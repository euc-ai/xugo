package emit

import (
	"context"
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
)

// CollectCNFCache reads, for the recorded sections of one member, every
// CNF certificate (and conditioning plan) the member's replay will
// consult, and returns them as a CNFCache.
//
// Its reader is the author, not the replay: the family CNF recorder
// records a landed member's keys live, so this blob is never installed.
// What it answers is the question a session cannot answer by closing —
// whether a leaf reached the refuter (and so will cost a recorded key)
// or closed by simplification or the apply rung. An empty cache is the
// keyless case.
//
// The walk re-runs each refute site through the SAME closer replay runs,
// against the store the session recorded into, on an env of its own
// (ProverEnv.CNFCaptureEnv) in strict capture-only mode:
// RequireCNFCacheHit (a MISS panics — the session closed a refute whose
// certificate is not under the key replay computes, a signal to
// diagnose rather than repair here) and CNFCacheCaptureOnly (a HIT
// closes with a reconstruct-at-force promise left unforced — no
// reconstruction runs; verifying a certificate reconstructs is the
// replay's job). A panic is recovered into an error naming the section.
// The env handed in is read and never written: the sessions sharing it
// keep their store and their live refuter while the collection runs.
//
// The capture is a proof.CapturingCNFStore in front of env's store,
// installed on the derived env alone. Both tables ride the one capture:
// a By target whose strict re-run reads a conditioning plan needs that
// plan, or the same By would find certificates it cannot reach (the
// plan is what reproduces the conditioned sequent). Strictness for
// plans is implicit: a By that NEEDS a missing plan diverges to a
// certificate MISS, which the strict mode reports.
func CollectCNFCache(env *proof.ProverEnv, sections []*proof.DetailedProofProto) (*proof.CNFCache, error) {
	capture := proof.NewCapturingCNFStore(env.ProofService.CNFStore)
	walk := env.CNFCaptureEnv(capture)
	for i, sec := range sections {
		if err := collectSectionCNF(walk, sec); err != nil {
			return nil, fmt.Errorf("section %d: %w", i, err)
		}
	}
	return capture.Captured().Cache(), nil
}

// collectSectionCNF runs every refute site of one section through the
// closer replay runs for its recorded step, recovering a strict-mode
// MISS panic into an error. A CnfRefute target runs the BARE refute
// (CloseByCNFRefute — replay runs `CnfRefute()`, i.e. tryCNFRefute
// directly; CloseByAuto would prepend AutoExpand preprocessing replay
// never does, diverging the refute goal and thus the key); a SetTac or
// By composite runs its own whole-step executor.
func collectSectionCNF(env *proof.ProverEnv, sec *proof.DetailedProofProto) (err error) {
	defer func() {
		if rec := recover(); rec != nil {
			err = fmt.Errorf("%v", rec)
		}
	}()
	dr := ext.NewPoolReader(sec.Pool, env.ProofService.LoadConstMeta)
	for _, g := range cnfRefuteTargetGoals(dr, sec.Steps) {
		if !proof.CloseByCNFRefute(proof.CreateGoalStack(g), env) {
			return fmt.Errorf("bare CNF refute failed on a recorded CnfRefute target — " +
				"the member's replay would fail at this step too")
		}
	}
	// SetTac ministeps: the refute targets live INSIDE the step (the
	// leaves after its rewrite fixpoint), so the walk runs the SAME
	// whole-step closer replay runs — ApplySetTacMode with the step's
	// recorded const list AND recorded mode.
	for _, st := range setTacTargetsFromDetailedSteps(dr, sec.Steps) {
		if !proof.ApplySetTacMode(proof.CreateGoalStack(st.goal), env, context.Background(), st.consts, st.mode, nil) {
			return fmt.Errorf("set_tac failed on a recorded SetTac target — " +
				"the member's replay would fail at this step too")
		}
	}
	// By ministeps: like SetTac, the refute target lives INSIDE the
	// composite (the working leaf after premise installs + shaping), so
	// its key is NOT the recorded step.Goal — only running the SAME
	// whole-step executor replay runs (ApplyByStep) reaches the refuter
	// with the right sequent. by{arith} is skipped (the omega path
	// never consults the CNF store).
	byTargets, bErr := byTargetsFromDetailedSteps(env, dr, sec.Steps)
	if bErr != nil {
		return bErr
	}
	for _, bt := range byTargets {
		if !proof.ApplyByStep(proof.CreateGoalStack(bt.goal), env, context.Background(), bt.spec) {
			return fmt.Errorf("by composite failed on a recorded By target — " +
				"the member's replay would fail at this step too")
		}
	}
	return nil
}

// setTacTarget pairs a recorded SetTac ministep's goal with its recorded
// const list and mode, for collectSectionCNF's whole-step verification.
type setTacTarget struct {
	goal   core.Prop
	consts []core.TermName
	mode   proof.SetTacMode
}

// setTacTargetsFromDetailedSteps scans a step list for SetTac ministeps.
// Mirrors cnfRefuteTargetGoals: step.Goal is replay-stable.
func setTacTargetsFromDetailedSteps(r *ext.PoolReader, steps []*proof.StepProto) []setTacTarget {
	var out []setTacTarget
	for _, step := range steps {
		st, ok := step.Step.(*proof.StepProto_SetTac)
		if !ok {
			continue
		}
		g, _ := r.Prop(step.Goal)
		if g == nil {
			continue
		}
		consts := make([]core.TermName, len(st.SetTac.GetConsts()))
		for i, c := range st.SetTac.GetConsts() {
			consts[i] = core.TermName(c)
		}
		out = append(out, setTacTarget{goal: g, consts: consts, mode: st.SetTac.GetMode()})
	}
	return out
}

// cnfRefuteTargetGoals scans a step list for CnfRefute ministeps and
// returns each's recorded step.Goal (set live at record time, so
// replay-stable).
func cnfRefuteTargetGoals(r *ext.PoolReader, steps []*proof.StepProto) []core.Prop {
	var out []core.Prop
	for _, step := range steps {
		if _, ok := step.Step.(*proof.StepProto_CnfRefute); !ok {
			continue
		}
		g, _ := r.Prop(step.Goal)
		if g != nil {
			out = append(out, g)
		}
	}
	return out
}

// byTarget pairs a recorded By ministep's goal with its decoded BySpec,
// for collectSectionCNF's whole-step verification. Mirrors setTacTarget.
type byTarget struct {
	goal core.Prop
	spec proof.BySpec
}

// byTargetsFromDetailedSteps scans a DetailedProofProto step list for By
// ministeps whose closer is the CNF refuter (arith:false) and decodes each
// payload back into the BySpec ApplyByStep takes — the inverse of
// _ByStep.proto, mirroring how emit_by.go renders the same payload as the
// By(...) source expression. step.Goal is the full recorded sequent, so
// resident premises resolve against its hyps exactly as at record time.
//
// A premise that is a law read under a resident hypothesis is handed
// back as the session handed it over (ByPremiseSpec.ReadingUnder): a
// witnessed one is the recorded sequent, and a bare one — the derived
// flavor — needs the sequent as a THEOREM, re-derived here from the
// recorded reading (readingTheorem). A loose cite (readingCitedLoose)
// is the law as a named premise beside its hypothesis, the reading on
// it a record for emit alone. Any other Derived premise (a kit's
// self-proving fact) is unreachable from session records, so hitting
// one here means a schema drift; fail loudly rather than replay it
// wrong.
func byTargetsFromDetailedSteps(env *proof.ProverEnv, r *ext.PoolReader, steps []*proof.StepProto) ([]byTarget, error) {
	var out []byTarget
	for i, step := range steps {
		st, ok := step.Step.(*proof.StepProto_By)
		if !ok {
			continue
		}
		if st.By.GetArith() {
			// by{arith} closes via _Arith{} + _TrivialSimplify{}; neither
			// consults the CNF store, so there is nothing to capture.
			// by{settac} is NOT skipped: the set driver's internal refutes
			// hit the CNF store exactly as a bare set_tac step's do, so its
			// keys must be collected through the same whole-step re-run.
			continue
		}
		g, _ := r.Prop(step.Goal)
		if g == nil {
			continue
		}
		var premises []proof.ByPremiseSpec
		for j, pr := range authoredByPremises(r, st.By) {
			reading := proof.ReadingRecordFromProto(r, pr.GetReading())
			if pr.GetDerived() && reading.Hypothesis() == nil {
				return nil, fmt.Errorf(
					"step %d: By premise %d is Derived (kit self-proving) — "+
						"unreachable from session records; cannot re-run for CNF collection", i, j)
			}
			install, _ := r.Prop(pr.GetInstall())
			if install == nil {
				return nil, fmt.Errorf("step %d: By premise %d has no install prop", i, j)
			}
			if pr.GetDerived() {
				theorem, err := readingTheorem(env, reading)
				if err != nil {
					return nil, fmt.Errorf("step %d: By premise %d: re-deriving the recorded reading: %w", i, j, err)
				}
				install = theorem
			}
			var reference core.Prop
			if pr.GetReference() != nil {
				reference, _ = r.Prop(pr.GetReference())
			}
			witnesses := make([]core.Term, 0, len(pr.GetWitnesses()))
			for _, w := range pr.GetWitnesses() {
				witnesses = append(witnesses, r.Term(w))
			}
			var named []proof.NamedWitness
			for _, nw := range pr.GetNamed() {
				named = append(named, proof.NamedWitness{Binder: nw.GetBinder(), Witness: r.Term(nw.GetTerm())})
			}
			// An exact premise's recorded clause form installs as the
			// session's executor installed it (ByPremiseSpec.Clause).
			var clause core.Prop
			if pr.GetClause() != nil {
				clause, _ = r.Prop(pr.GetClause())
			}
			premises = append(premises, proof.ByPremiseSpec{
				Install:      install,
				Reference:    reference,
				Witnesses:    witnesses,
				Named:        named,
				Resident:     pr.GetResident(),
				Exact:        pr.GetExact(),
				Clause:       clause,
				ReadingUnder: reading.Hypothesis() != nil && !readingCitedLoose(r, pr),
				Reading:      reading,
				Describe:     fmt.Sprintf("recorded premise %d", j),
			})
		}
		out = append(out, byTarget{goal: g, spec: proof.BySpec{
			Premises:   premises,
			Shapes:     byShapesFromProto(r, st.By.GetShape()),
			Settac:     st.By.GetSettac(),
			Chase:      st.By.GetChase(),
			ChaseDepth: int(st.By.GetChaseDepth()),
			Broadcast:  st.By.GetBroadcast(),
		}})
	}
	return out, nil
}

// readingTheorem re-derives a recorded reading as the theorem the
// session derived (proof.ReadLawAt): the law at the instance — an
// entry, the hypothesis assumed, or a reading re-derived the same way.
func readingTheorem(env *proof.ProverEnv, reading *proof.ReadingRecord) (core.Prop, error) {
	var instance core.Prop
	switch {
	case reading.Inner != nil:
		inner, err := readingTheorem(env, reading.Inner)
		if err != nil {
			return nil, err
		}
		instance = inner
	case reading.Under != nil:
		instance = core.Assume(reading.Under)
	default:
		instance = entryPromise(env, reading.Instance)
	}
	return proof.ReadLawAt(entryPromise(env, reading.Law), instance)
}

// entryPromise is the theorem an entry stating `stated` is served as:
// the entry's own promise, where env serves a builder under the
// statement's key, and otherwise a promise that fails when forced. The
// capture walk forces nothing — it reads which certificates a close
// consults — so the second is as good as the first here, and a
// statement no entry backs is reported where a proof would need it.
func entryPromise(env *proof.ProverEnv, stated core.Prop) core.Prop {
	normalized, _ := proof.Normalize(stated)
	if promise := env.PromiseByKey(normalized.AlphaKey(), stated); promise != nil {
		return promise
	}
	return core.Promise(stated, func(core.Forcer) core.ThmCert {
		panic(fmt.Sprintf("emit: no registered builder serves %s — the capture walk declared it and never forces it",
			stated.AlphaKey()))
	})
}

// byShapesFromProto decodes a recorded ByShapeProto into the shaping
// VALUES BySpec carries (MergeByShapes re-merges them — the same merge
// that produced the record, so the round trip is lossless). A
// present-but-empty shape is the macro's Normalized value, exactly as
// emit_by.go renders it.
func byShapesFromProto(r *ext.PoolReader, sh *proof.ByShapeProto) []proof.ByShape {
	if sh == nil {
		return nil
	}
	var out []proof.ByShape
	if sh.GetPre() {
		out = append(out, proof.PreNormalized)
	}
	if n := sh.GetDenoteSize(); n > 0 {
		out = append(out, proof.Denoted(int(n)))
	}
	if t := sh.GetDenoteTerm(); t != 0 {
		term := r.Term(t)
		if sh.GetDenoteHilbert() {
			out = append(out, proof.HilbertDenotedAs(sh.GetDenoteName(), term))
		} else {
			out = append(out, proof.DenotedAs(sh.GetDenoteName(), term))
		}
	}
	if sh.GetHilbert() {
		out = append(out, proof.HilbertDenoted)
	}
	if sh.GetRaw() {
		out = append(out, proof.Raw)
	}
	if len(out) == 0 {
		out = append(out, proof.Normalized)
	}
	return out
}
