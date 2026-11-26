// step_by.go — the math layer's premise-disciplined close (`By` /
// `ByArith` / `BySets`, fact.go) as a first-class recorded composite
// ministep.
//
// ONE proto tag (StepProto_By, tag 55) whose payload is the CALL — the
// premise list (resolved install forms + stated-order witnesses), the
// merged shaping, the closer choice, Broadcast — and whose apply IS the
// shared executor: locate the resident premises, clear every other
// ambient hyp (lexical scope), materialize the named premises in order
// (preserving install + content-located grounding), run the declared
// shaping, one refutation. Live agent dispatch (the engine `by`
// tactic), the By macro in hand-written proofs, and emitted
// members all execute this same apply — the record/emit/replay
// code-reuse principle (step_composite.go): record the COMPOSITE step,
// never an expansion snapshot. Before this tag, a By recorded its
// expansion (clear_hyps + lemma_preserve + specialize + basic +
// cnf_refute chain), which emit could only render back as an Action
// staircase; the tag records what the author SAID.
//
// Named premises surface as CLAIM CHILDREN (the resolved install form,
// premise order), closed OUTSIDE the composite — by the By macro's
// certs in corpus replay, by auto-match against the entry each premise
// names in a live session — the SimpWith rule-children convention,
// which keeps emit's
// leaf resolution and the trust regime exactly where they were. The closing
// refutation runs INSIDE apply, close-or-fail (the SetTac convention),
// so a recorded step's refute is a guaranteed strict-mode cache hit
// under the same key the record-time run wrote.
//
// The executor drives the SAME node-level machinery the pre-composite
// By macro drove (ApplyClearHyps / ApplyLemmaPreserve / Specialize /
// Basic / Denote / CnfRefute / Arith), on a PRIVATE goal stack.
// Behavior parity — install absorption, type adaptation, witness
// reorder, the By-MISS decision tree — is inherited by construction,
// not re-implemented.

package proof

import (
	"context"
	"fmt"
	"slices"
	"strings"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/euc-ai/xugo/utils"
)

// byPremise is one resolved premise of a _ByStep. See ByPremiseProto
// for the wire semantics of the two flavors.
type byPremise struct {
	// install: NAMED flavor — the resolved install form (what
	// ApplyLemmaPreserve materializes); RESIDENT flavor — a hyp-free
	// Prop whose conclusion is the resident hypothesis' statement
	// (located by α-match at apply, index-free).
	install Prop
	// reference is the STATED form whose binder order the witnesses
	// follow (citeReferenceProp of the author's target). nil = install.
	reference Prop
	// witnesses ground the premise, in reference's stated binder order.
	witnesses []Term
	// named pins binders of the STATED form by name (Fact.Where —
	// Lean's `apply law (R := r)`): the premise installs nothing in
	// phase 3 and enters the apply rung as a seeded head that MUST
	// fire (applyHeads / applyClose). Exclusive with witnesses.
	named    []NamedWitness
	resident bool
	// kept marks a resident premise the ENGINE added beside an authored
	// one — the hypothesis a reading is under — rather than one the
	// author listed: it is never reported unused.
	kept bool
	// exact marks an install form that is an EXPLICIT type instantiation
	// (an AtTypes target, or a session premise with an agent-supplied
	// type_specialize σ): the executor installs it exactly instead of
	// letting chooseTypeAdaptedStep's speculative σ override it.
	exact bool
	// clause is a NAMED premise's closer form — the normalized dep
	// (registered, so its obligation certifies by key), a typed
	// instance's install half; a session key premise's Normalize. A
	// bare named premise installs it (the closer alone consumes it, and
	// the closers were built and recorded on clause form) with the
	// stated form (install / reference) as the apply rung's head; a
	// witnessed one is a plain add of the stated form. nil marks an
	// explicit premise (a Prop, a cert, a section): it installs verbatim
	// — bare through the chain, witnessed as a plain add.
	clause Prop
	// derivedCert — the DERIVED flavor (a solver kit's self-proving
	// premise): the executor asserts `install` at this premise's list
	// position and closes the claim branch from this certificate.
	// RUNTIME-ONLY (like env); the wire carries the `derived` flag.
	derivedCert Prop
	// coefficient — the SCALED flavor (fact.go Scaled): after the
	// premise, an equation l = r, is installed and grounded — or, a
	// derived premise, asserted and resident — its congruence c·l = c·r
	// under the carrier's multiplication is added as a hypothesis,
	// proved from the equation (phase 3b). On the wire as `scaled` +
	// `coefficient`.
	coefficient Term
	// readingUnder marks the derived flavor's other tenant: a law read
	// under a RESIDENT hypothesis (proof.Read at a resident fact). It is
	// a fact of the context, so the list is reordered at construction
	// to materialize it before every install (withReadingsFirst) — the
	// Have it replaces was resident before the By began. RUNTIME-ONLY;
	// the wire sees a derived premise already in front.
	readingUnder bool
	// reading says what a session's premise was read from when it is a
	// law read at an instance (ReadingRecord): the wire's `reading`,
	// from which emit spells `law.Read(instance)`. The executor never
	// consults it.
	reading *ReadingRecord
	// describe is a RUNTIME-ONLY diagnostic label (the author's spelling
	// of the premise — dep name, hyp label). Never serialized; empty
	// falls back to a prop-derived description.
	describe string
	// sourceKey is the entry a session's key premise was loaded from
	// (ByPremiseSpec.SourceKey). RUNTIME-ONLY: the wire does not carry
	// it, GoalStackNode.ByPremiseSourceKeys reads it for emit.
	sourceKey core.PropKey
}

func (p byPremise) description() string {
	if p.describe != "" {
		return p.describe
	}
	base := clipRunes(ext.PrintTerm(p.install.AsProp().Conclusion()), 80)
	if p.resident {
		base = "hyp " + base
	}
	if len(p.witnesses) > 0 {
		ws := make([]string, len(p.witnesses))
		for i, w := range p.witnesses {
			ws[i] = ext.PrintTerm(w)
		}
		base += " at " + strings.Join(ws, ", ")
	}
	if len(p.named) > 0 {
		base += " where " + describeNamedWitnesses(p.named)
	}
	return base
}

// clipRunes shortens s to at most max runes, appending "…". Rune-safe
// by requirement, not politeness: these descriptions travel into panic
// messages the session relays as RPC diagnostics, and that marshal is
// strict-UTF-8 — a byte-indexed cut that splits a math glyph (∀, ∈, 𝕌)
// fails the WHOLE response, which callers then misread as a close.
func clipRunes(s string, max int) string {
	r := []rune(s)
	if len(r) <= max {
		return s
	}
	return string(r[:max-1]) + "…"
}

// unmaterializedAfter is what the over-specification check reports:
// the premises listed after the one that closed the goal which never
// entered the leaf — an install never run, a witnessed premise whose
// instance was never grounded, a kit premise never asserted. A bare
// resident premise is not among them: By keeps every listed resident
// in the leaf before the first install (phase 2), so it stood there
// while the closing install's simplification ran, and whether that
// read it is the economy audit's question, not this check's — which
// is why `By(law, h)` and `By(h, law)` are one close. A resident the
// engine added beside an authored premise (kept) is never reported.
func unmaterializedAfter(premises []byPremise, closedAt int) []int {
	var unused []int
	for i := closedAt + 1; i < len(premises); i++ {
		pr := premises[i]
		if pr.kept || (pr.resident && len(pr.witnesses) == 0 && len(pr.named) == 0) {
			continue
		}
		unused = append(unused, i)
	}
	return unused
}

// arithCloseFixpointBound caps the Arith firings the arith closer runs
// after its first, each a further hypothesis rewrite or the decision.
const arithCloseFixpointBound = 8

// _ByStep is the composite ministep. premises/shape/arith/broadcast are
// the recorded payload; env/ctx/scope are runtime-only (env injected by
// Script.Do for macro-constructed steps, passed explicitly by the
// engine dispatch; scope threads via applyScoped so the gated Arith
// closer honors the omega circularity gate exactly as the replay
// harness does).
type _ByStep struct {
	premises []byPremise
	shape    *ByShape
	arith    bool
	settac   bool
	// chase selects the diagram-chase closer, chaseDepth its number of
	// pull-back rounds (fact.go's ByChase and Depth).
	chase      bool
	chaseDepth int
	broadcast  bool

	// condition arms the conditioning stage for THIS attempt. Set by
	// the ladder (applyLadder), never serialized: the recorded By
	// replays through the same ladder, which re-derives it.
	condition bool

	// s4 is the grounding stage's per-attempt runtime state (set by
	// applyLadder alongside condition, never serialized): the plan
	// entries a successful conditioned close persists, and the
	// action descriptions a failing close reports.
	s4 *byS4State

	// audit is the economy audit's per-attempt capture (see
	// byAuditState) — runtime-only, armed by applyLadder only when the
	// env carries a report hook or the call its own (leafReport).
	audit *byAuditState
	// leafReport is one call's sink for the audit's FIRST probe
	// (BySpec.Report, the session's `by`) — runtime-only. With it the
	// ladder captures the leaves that reach resolution as it does
	// under the recorder and, after the close, runs that probe over
	// them (reportAvoidableRefutes): a leaf a plain Basic() closes,
	// and the By respelled with Normalized closing on fewer rows than
	// this close's. The probes for an inert element stay the
	// recorder's.
	leafReport  func(finding string)
	closeReport func(string)
	// recordsReport delivers the rows the recorder would write for the
	// close — the certificate keys its refutes wrote or read and the
	// conditioning plans it persisted or read — to the session `by`/`probe`
	// (BySpec.Records). Runtime-only; nil everywhere else.
	recordsReport func(keys, plans []core.PropKey)
	closeTrace    *byCloseTrace
	// whistleReport delivers the divergence-whistle cuts a replay of a
	// recording of the close meets (BySpec.Whistle, the session's `by`).
	// Runtime-only; nil everywhere else.
	whistleReport func(cuts []skeleton.WhistleEvent)
	// ladder is the ladder's per-call state, shared by every rung's
	// copy of the step: the cut-off a rung's terminal close measured,
	// read once a later rung closes (reportBudgetPick).
	ladder *byLadderState
	// keyless marks the rung-0 probe (probeKeyless): the conditioning
	// stage runs without grounding (the manual's S4), so the attempt
	// applies no plan and records none.
	keyless bool
	// failureUnread marks an attempt whose caller reads a failure as "did
	// not close" and nothing more (probeBare, probeKeyless, the audit's
	// probes): terminalClose raises the close's cause as it is and
	// renders no message. A cache-only context does not say this: a
	// session's resume runs under one and reads the failure as its
	// divergence. Set by those callers, never serialized.
	failureUnread bool
	// prune marks the run of the ladder's conditioned rung on the pruned
	// leaf (applyLadder): the grounding stage replaces, by its instances,
	// each source a match pinned in full.
	prune bool
	// numerals marks an attempt of the ladder's that reads numerals at
	// the apply rung (apply_close.go, rungReader): a guard that is a
	// comparison of numerals asks for no supplier, `X(2 + 1)` is `X(3)`.
	// Set by the ladder's numeral rungs alone (applyLadder), never
	// serialized: every other attempt is the By as its facts state it.
	numerals bool

	// site is the author's file:line for a Go-built By (_ByAction.site),
	// empty for a session-built one; runtime only — the audit names it.
	site string
	// engineShape: the shape is the prover's, not the author's
	// (_ByAction.engineShape) — Probe B has nothing to advise.
	engineShape bool

	env   *ProverEnv
	ctx   context.Context
	scope *ProofScope
	// spine is the leaf of the proof the By runs on — runtime-only, set
	// where the step is applied — read by a failure for the history of
	// a guard the leaf does not supply (rewrittenAwayNote): the private
	// stack the executor runs on has no ancestry of its own.
	spine *GoalStackNode
	// clauseInstalled marks, by premise index, the witnessed premises
	// this attempt installed in their clause form (applyInner), whose
	// stated form at the tuple is then the apply rung's head.
	clauseInstalled []bool
	// clauseGuards holds, by premise index, the guard a witnessed
	// premise fell to its clause form for — the one its line of a
	// failure names — set before the terminal close: what a failure
	// reads to say which of them the arithmetic closer decides
	// (withGuardAdvice).
	clauseGuards map[int]core.Term
	// goal is the goal this attempt was applied to, as applyInner
	// received it, set before the terminal close: what a failure re-runs
	// the installs on to read the list's order (listOrderNote).
	goal Prop
	// installs, when non-nil, makes applyInner an install probe: it
	// clears and installs the premises, reports here what the installs
	// left, and returns nil before any shaping or close.
	installs *byInstallProbe
	// bareInstalls lists the bare polymorphic premises this attempt
	// installed at one type instance (applyInner), set before the
	// terminal close: what a failure reads to name an install that
	// misses constants the leaf holds (installReadingNote).
	bareInstalls []byBareInstall
}

// byInstallProbe is what an install probe reports (_ByStep.installs).
type byInstallProbe struct {
	// closedAtLast: the leaf was open before the last premise's install
	// and that install closed it.
	closedAtLast bool
	// clause marks, by premise index, the witnessed premises that took
	// their clause form.
	clause []bool
}

// byS4State threads the S4 grounding stage's outcome through one
// ladder attempt.
type byS4State struct {
	// pending holds one plan entry per working leaf S4 conditioned by
	// LIVE search this attempt; a successful close persists them to
	// the CNF store's plan table. Plans applied FROM the store are
	// never re-pended.
	pending []byPendingPlan
	// describe lists the stage's actions for the failure diagnostics
	// (the error text is the repair prompt).
	describe []string
}

// byPendingPlan is one to-be-persisted plan entry: the live e-match
// search's output for one bare working leaf, as data.
type byPendingPlan struct {
	bareKey    core.PropKey
	bareGoal   Prop // the bare leaf, for the recorder's report (CNFGoalNoter)
	groundings []ematch.Plan
	replaced   []core.Term
	// canon takes the conditioned leaf's free variables to their
	// canonical names (prop.CanonicalFreeRenaming): the entry stores
	// its terms under those, so a renamed member reads them back.
	canon          []core.TermSubst
	conditionedKey core.PropKey
}

// cond builds the shared conditioning stage (step_condition.go) over
// this attempt's environment and S4 state. The stage code is one
// implementation for every door; the By executor threads its own
// ladder/audit state around it.
func (step _ByStep) cond() *conditioner {
	return &conditioner{env: step.env, ctx: step.ctx, s4: step.s4, arith: step.arith, scope: step.scope, numerals: step.numerals}
}

// door is how this attempt reads a guard outside the conditioning
// stage — where a witnessed premise is installed and grounded: in the
// proof's scope, with the numeral reading in an attempt the ladder runs
// with it and without in every other.
func (step _ByStep) door() rungOpts {
	return rungOpts{scope: step.scope, plain: !step.numerals}
}

// readsNumerals reports whether the ladder has numeral rungs for this
// By: the refuter's By, in a proof whose policy admits the arithmetic
// bundle the numerals are evaluated by. The arithmetic closer evaluates
// them itself and its By is run as it always was; the set driver's and
// the chase's read none.
func (step _ByStep) readsNumerals() bool {
	if step.arith || step.settac || step.chase || (step.shape != nil && step.shape.raw) {
		return false
	}
	return readerOf(step.scope).readsNumerals()
}

// applyHeads lists the named premises' STATED forms for the apply rung
// (apply_close.go): a premise whose canonical install is the normalized
// form carries the form the author actually named as its reference,
// and that is the form with a telescope to apply. A premise pinned by
// name (byPremise.named) is a SEEDED head — nothing of it is resident,
// and it must be the apply that closes the leaf. A premise installed as
// it is stated is read in the context, unless the install is one type
// instance of it (installsAtOneInstance): its stated form is then a
// head, tried at every instance the goal offers.
func (step _ByStep) applyHeads() []applyHead {
	var heads []applyHead
	for i, pr := range step.premises {
		if pr.resident {
			continue
		}
		stated := pr.reference
		if stated == nil {
			stated = pr.install
		}
		head := applyHead{stated: stated, describe: pr.description(), exact: pr.exact}
		if len(pr.named) > 0 {
			head.named = pr.named
			heads = append(heads, head)
			continue
		}
		if len(pr.witnesses) > 0 && pr.clause != nil && (statedMatrixIsIff(stated) || step.installedClause(i)) {
			// A witnessed ⇔ law installs in its clause form (materialize,
			// useClause), and so does a witnessed law whose stated guards
			// the leaf does not supply (statedGuardsSupplied), so the
			// instance the author named is not in the context for the
			// rung to read; the stated form, pinned at the tuple, is its
			// head — its guards then closed as any antecedent is.
			head.tuple = pr.witnesses
			heads = append(heads, head)
			continue
		}
		if stated.AlphaEquals(pr.installedForm()) && !pr.installsAtOneInstance() {
			continue // resident as stated: the rung reads it in the context
		}
		heads = append(heads, head)
	}
	return heads
}

// installedClause reports whether this attempt installed premise i, a
// witnessed premise, in its clause form.
func (step _ByStep) installedClause(i int) bool {
	return i < len(step.clauseInstalled) && step.clauseInstalled[i]
}

// installsAtOneInstance reports whether a bare named premise is resident
// at ONE type instance of its stated form: a polymorphic premise the
// install adapts to the goal (typematch.TryAdaptLemmaTypes, a single
// guess) — or leaves at its own letters where that guess finds no
// instance. The goal may offer instances beside the one resident; the
// head's enumeration (headCandidates) reaches each.
func (pr byPremise) installsAtOneInstance() bool {
	return pr.derivedCert == nil && len(pr.witnesses) == 0 && !pr.exact && ext.PropHasTypeVars(pr.installedForm())
}

// statedMatrixIsIff reports whether a stated form is an ⇔ under its
// guarded ∀-prefix — the shape a witnessed premise installs in clause
// form for.
func statedMatrixIsIff(stated Prop) bool {
	if stated.NumHyps() > 0 {
		return false
	}
	_, matrix := ematch.StripGuardedForalls(stated.Conclusion())
	_, _, iff := ext.MatchesIFF(matrix)
	return iff
}

// namedPremises lists the premises pinned by name (Where) — the
// ones the apply rung must fire.
func (step _ByStep) namedPremises() []byPremise {
	var out []byPremise
	for _, pr := range step.premises {
		if len(pr.named) > 0 {
			out = append(out, pr)
		}
	}
	return out
}

// installedForm is what the executor installs for a named premise: the
// closer's clause form for a bare one, the stated install otherwise.
func (pr byPremise) installedForm() Prop {
	if pr.clause != nil && len(pr.witnesses) == 0 {
		return pr.clause
	}
	return pr.install
}

// byAuditState captures what the economy audit needs from one
// ladder attempt: the leaf(s) the CNF closer actually received
// (recorded by closeOne just before the refute). Armed per attempt by
// applyLadder only when env.ByAuditReport is wired or the step carries
// a leafReport — nil everywhere else, at zero cost.
type byAuditState struct {
	preClose []Prop
}

func (step _ByStep) String() string {
	var parts []string
	if step.shape != nil {
		parts = append(parts, "shaped")
	}
	if step.broadcast {
		parts = append(parts, "broadcast")
	}
	closer := "cnf"
	switch {
	case step.arith:
		closer = "arith"
	case step.settac:
		closer = "settac"
	case step.chase:
		closer = fmt.Sprintf("chase depth %d", step.chaseDepth)
	}
	parts = append(parts, closer)
	scaled := 0
	for _, p := range step.premises {
		if p.coefficient != nil {
			scaled++
		}
	}
	if scaled > 0 {
		parts = append(parts, fmt.Sprintf("%d scaled", scaled))
	}
	return fmt.Sprintf("By(%d premises; %s)", len(step.premises), strings.Join(parts, ", "))
}

func (step _ByStep) proto(b *ext.PoolBuilder) isStepProto_Step {
	premises := make([]*ByPremiseProto, len(step.premises))
	for i, p := range step.premises {
		pp := &ByPremiseProto{
			Install:  b.PropRef(p.install),
			Resident: p.resident,
			Derived:  p.derivedCert != nil,
			Exact:    p.exact,
		}
		// An exact premise's clause form is not derivable from its
		// install (Normalize and type instantiation do not commute), so
		// the record carries it for a consumer that re-runs the step.
		if p.exact && p.clause != nil {
			pp.Clause = b.PropRef(p.clause)
		}
		// Named pins need their stated binder spelling on the wire,
		// even when the reference is alpha-equal to the install.
		if p.reference != nil && (!p.reference.AlphaEquals(p.install) ||
			len(p.named) > 0 && !p.reference.Conclusion().Equals(p.install.Conclusion())) {
			pp.Reference = b.PropRef(p.reference)
		}
		for _, w := range p.witnesses {
			pp.Witnesses = append(pp.Witnesses, b.TermRef(w))
		}
		for _, nw := range p.named {
			pp.Named = append(pp.Named, &NamedWitnessProto{Binder: nw.Binder, Term: b.TermRef(nw.Witness)})
		}
		if p.coefficient != nil {
			pp.Scaled = true
			pp.Coefficient = b.TermRef(p.coefficient)
		}
		pp.Reading = p.reading.proto(b)
		premises[i] = pp
	}
	var shape *ByShapeProto
	if s := step.shape; s != nil {
		shape = &ByShapeProto{
			Pre:           s.pre,
			Raw:           s.raw,
			DenoteSize:    int32(s.denote),
			Hilbert:       s.hilbert,
			DenoteName:    s.denoteName,
			DenoteHilbert: s.denoteHilbert,
		}
		if s.denoteTerm != nil {
			shape.DenoteTerm = b.TermRef(s.denoteTerm)
		}
	}
	return &StepProto_By{By: &ByProto{
		Premises:   premises,
		Shape:      shape,
		Arith:      step.arith,
		Settac:     step.settac,
		Chase:      step.chase,
		ChaseDepth: uint32(step.chaseDepth),
		Broadcast:  step.broadcast,
	}}
}

func (step _ByStep) applyScoped(p Prop, scope *ProofScope) *SubGoals {
	step.scope = scope
	return step.applyLadder(p)
}

func (step _ByStep) apply(p Prop) *SubGoals { return step.applyLadder(p) }

// applyLadder is the conditioning ladder; what is recorded replays
// untouched. Rung 0, the CNF closer's, is the conditioned attempt with the
// refuter barred and nothing grounded (probeKeyless): a leaf the strips,
// the apply rung and the shaping close is closed with no certificate
// asked for, before the key it would be asked under is computed. Rung 1
// attempts the BARE spelling in probe mode: CNF refutes are cache-only —
// a shallow env copy under RequireCNFCacheHit, whose MISS panic is the
// graceful probe failure — so every row recorded before the conditioning
// stage existed keeps closing on its recorded keys, with zero re-records
// and no live search spent; a strict replay passes over it for a leaf
// the store holds a plan for, whose recorded close is rung 2's. Rung 2
// runs the conditioned attempt with the caller's full semantics; new
// recordings therefore mint conditioned keys exactly where conditioning
// was needed. A plan the store holds for the leaf is applied as
// recorded, whatever it replaces.
// With none the rung grounds to the WHOLE leaf: the instances are added
// and every source stays, so the closer is handed each premise as the
// author named it. Where that fails and a match pinned a source in full,
// the rung is run once more (live mode only) on the PRUNED leaf, each
// such source replaced by its instances — fewer clauses for a search the
// wide forms were lost in, and a ground leaf for a shaping's Basic(),
// which discards an instance that stands beside its source. Whether a
// close needs a source at a point the stage did not ground it at, or is
// lost in the wide form, is known only once a search has run, so the
// leaf that loses no premise is searched first. A close made on the
// pruned leaf records the plan of that run, which replaces, and its
// replay is rung 2 applying the plan. The arithmetic closer reads its
// facts wide and is handed the whole leaf alone. Rung 3 (live mode only —
// a strict replay must not live-refute) retries the bare spelling with
// full semantics: conditioning must never LOSE a goal the bare spelling
// closes (the no-lost-search-power boundary); if rung 3 fails too, rung
// 2's failure on the whole leaf is the one reported — the conditioned
// spelling is the primary path — with a line saying so where the pruned
// leaf was run as well. Raw is single-attempt bare with full semantics.
//
// The refuter's By has rungs that read numerals at the apply rung
// (_ByStep.numerals; apply_close.go, rungReader), placed so that the By
// as its facts state it comes first wherever a recording of it can
// exist: live, the conditioned attempt with the refuter barred, after
// rung 1 — what the reading alone closes costs no search and no key —
// and the conditioned attempt whole, after rung 3; under a strict
// replay, the conditioned attempt once more where rung 2 failed. Every
// other attempt reads no numeral, so a By recorded before the reading,
// or one whose listed facts supply its numeral guards, replays by the
// steps and on the rows it recorded.
//
// The rungs run under a whistle watch (skeleton.WatchWhistle): a
// divergence-whistle cut reported while they run names this By — its
// premises, and its file:line where it is written in Go — to every
// reader of the event, and the cuts a replay of a recording of the
// close meets go to the call's own sink: every cut of the rungs, less
// what cutsAPrunedRunReplaySkips takes off when rung 2's run on the pruned
// leaf is what closed, and what cutsARetryReplaySkips takes off when the
// bare retry is. The watch ends before the economy audit, whose probes
// are not the close.
func (step _ByStep) applyLadder(p Prop) *SubGoals {
	if byAuditProbe(step.ctx) {
		step.closeReport, step.recordsReport, step.closeTrace = nil, nil, nil
		step.whistleReport = nil
	}
	watch := skeleton.WatchWhistle(step.auditLabel)
	defer watch.Close()
	defer step.cutOffInside()
	// skipFrom and skipTo bound the cuts a replay of a recording of the
	// close does not meet (cutsAPrunedRunReplaySkips, cutsARetryReplaySkips).
	skipFrom, skipTo := 0, 0
	// A step copied from one that closed on the pruned leaf (the audit's
	// probes) starts the ladder on the whole one.
	step.prune = false
	step.ladder = &byLadderState{}
	step.ctx = context.WithValue(step.ctx, byLadderStateKey{}, step.ladder)
	// The economy audit is armed per attempt when the env carries a
	// report hook (the recorder harness — never a replay) and this
	// apply is not itself an audit probe. Whichever rung closes, the
	// audit runs over that attempt's capture. A call with a sink of its
	// own (a session's `by`) arms the capture alone and runs the first
	// probe over it. The rungs are the same either way.
	auditArmed := step.env.ByAuditReport != nil && !byAuditProbe(step.ctx)
	leafProbe := !auditArmed && step.leafReport != nil && !byAuditProbe(step.ctx)
	// The audit reads the rows this close touches: they are what its
	// replay probes are held to (runEconomyAudit, reportAvoidableRefutes).
	if step.closeReport != nil || step.recordsReport != nil || auditArmed || leafProbe {
		step.closeTrace = &byCloseTrace{}
		step.ctx = context.WithValue(step.ctx, byCloseTraceKey{}, step.closeTrace)
	}
	// The audit's replay probe is the recorder's ladder held to the
	// audited close's rows (auditReplayProbeKey): the keyless rung first,
	// as the recorder runs it, the bare rung on those rows, and the
	// conditioned rung once. There is no bare retry: it runs the leaves
	// the bare rung did, and what that rung could not close on the rows
	// the retry closes only by a refute it writes.
	replay := auditReplayOf(step.ctx)
	arm := func() {
		if auditArmed || leafProbe {
			step.audit = &byAuditState{}
		}
	}
	closed := func(sg *SubGoals) *SubGoals {
		fired := watch.Close()
		if cuts := slices.Concat(fired[:skipFrom], fired[skipTo:]); step.whistleReport != nil && len(cuts) > 0 {
			step.whistleReport(cuts)
		}
		if step.closeReport != nil {
			step.closeReport(strings.Join(step.closeTrace.routes, ", "))
		}
		if step.recordsReport != nil {
			step.recordsReport(step.closeTrace.keys, step.closeTrace.plans)
		}
		switch {
		case auditArmed:
			step.runEconomyAudit(p)
		case leafProbe:
			step.reportAvoidableRefutes(p, step.closeTrace, step.leafReport)
		}
		return sg
	}
	if step.shape != nil && step.shape.raw {
		arm()
		return closed(step.applyInner(p))
	}
	// A leaf the conditioned rung closes with NO refuter and NO grounding
	// — the strips, the apply rung, the fat-atom denotation and the
	// declared shaping alone — is closed that way before rung 1 is asked:
	// in a session, under the recorder and under a strict replay alike.
	//
	// Rung 1 comes second for what its MISS costs. The store answers it
	// only under the key of the bare leaf's whole refute prop, so a miss
	// is paid in full before it is known: the bare leaf's CNF is built and
	// the refute prop is normalized, tens of seconds on a wide leaf, for a
	// key a leaf this probe closes has no row under. A session's new leaf
	// has no row at all, so there every ask is a miss (measured live on
	// product_topology.IndexedFiniteModificationsDense: 13 of its 46 Bys
	// missed, 125 seconds of a run of 128, and 12 of the 13 close at this
	// probe, in 0.07 seconds), and a strict replay misses wherever the
	// recording closed with no key (zariski_cotangent.
	// PairDependentModuloRelations: 31 of 82 Bys, 114 seconds of 129).
	//
	// And for what its HIT touches. A recorded key closes the bare leaf
	// before the conditioned rung ever runs, the recorder counts the read
	// as a touch, and a GC then keeps a key the apply rung or a shaping
	// (`Normalized`'s Basic on the conditioned leaf) has made unnecessary
	// — a re-record after adding the shaping read the token as inert. The
	// keyless probe reads no certificate, so what it closes leaves its key
	// and its plan untouched and the GC retires them; what it cannot close
	// runs the ladder below, so no key and no plan is ever ADDED by it.
	// (Skipping rung 1 outright was measured and withdrawn: every GC then
	// re-records every By leaf through the conditioned rung — the corpus
	// went 1217 keys + 626 plans → 1295 + 928 and four families' fresh
	// blobs did not replay.)
	//
	// The probe first for every caller is what makes a replay read the
	// rows the recording wrote, and a session's `by` close a leaf, and
	// report its rows, as the recorder does for the same spelling. Its
	// price is the conditioning stage run on a leaf the bare spelling's
	// own shaping closes outright: `a.Conjuncts`' `By(Normalized, fact)`
	// on a wide fact, where the apply rung reads the context for tenths
	// of a second and Basic() on the bare leaf takes none.
	arm()
	if !step.arith && !step.settac && !step.chase {
		if sg := step.probeKeyless(p); sg != nil {
			return closed(sg)
		}
	}
	// A plan under a leaf's plan key is written by a close of the
	// conditioned rung, whose certificate is filed under the conditioned
	// leaf's key: the recording of this By missed the bare key and closed
	// there. A strict replay that the keyless probe told of such a plan
	// goes to that rung with the bare key uncomputed, and asks the bare
	// probe after it where the plan's rung does not close.
	plannedReplay := step.ladder.planned
	// A strict replay asks its two certificate rungs on exact keys first:
	// the bare probe, then the conditioned rung as written, each ending
	// where the store's exact-key table does not close its leaf, before
	// any refute prop is normalized (exactKeysOnlyKey). A recording that
	// closed at either rung wrote its certificate with the row that names
	// it, so the replay of the same leaf closes here: the bare probe's
	// miss, whose key was the normal form of the bare leaf's whole refute
	// prop, is answered by the table instead (measured over the corpus:
	// 2,164 such misses, 108 seconds of key, 1,654 of them followed by a
	// certificate the conditioned rung reads under its exact key). Where
	// neither rung closes, the ladder below runs as it does without the
	// pass, on the keys: a certificate another spelling of the leaf
	// recorded has no row for this one. The pass is the CNF closer's, as
	// the keyless probe is; a leaf with a stored plan goes to its rung
	// below, whose lookup asks the exact key itself.
	if step.env.RequireCNFCacheHit && replay == nil && !plannedReplay && !step.arith && !step.settac && !step.chase {
		exact := step
		exact.ctx = withExactKeysOnly(step.ctx)
		if sg := exact.probeBare(p); sg != nil {
			return closed(sg)
		}
		exact.condition = true
		exact.s4 = &byS4State{}
		exact.failureUnread = true
		sg, failure := exact.attempt(p)
		if sg != nil {
			return closed(sg)
		}
		if cut, isCut := failure.(byCutOff); isCut {
			panic(cut)
		}
	}
	if !plannedReplay {
		if sg := step.probeBare(p); sg != nil {
			return closed(sg)
		}
	}
	if replay != nil && replay.offRows {
		panic("By[auditReplayProbe]: the bare rung reads a row the audited close does not touch")
	}
	// The numeral reading has rungs of its own, and the By as its facts
	// state it is run before them wherever a recording of it can exist:
	// what closed before a numeral was a value to the rung closes by the
	// steps it closed by, on the rows it recorded, and records no use of
	// the arithmetic bundles. A strict replay runs the conditioned rung
	// as written and, where that fails, once more reading numerals. A
	// live By runs the numeral reading first with the refuter barred —
	// a close that needs only the reading costs no search and no key —
	// and last with it, after every rung of the By as written. The first
	// of the two is for what the By as written does not close with the
	// refuter barred, which the keyless probe above has asked.
	numerals := step.readsNumerals()
	strict := step.env.RequireCNFCacheHit || replay != nil
	if numerals && !strict {
		arm()
		reading := step
		reading.numerals = true
		if sg := reading.probeKeyless(p); sg != nil {
			noteByClose(step.ctx, byNumeralRoute)
			return closed(sg)
		}
	}
	step.stopIfCut("before the conditioned rung")
	step.condition = true
	step.s4 = &byS4State{}
	arm()
	if strict {
		if !numerals && !plannedReplay {
			return closed(step.applyInner(p))
		}
		sg, failure := step.attempt(p)
		if sg != nil || failure == nil {
			return closed(sg)
		}
		if cut, isCut := failure.(byCutOff); isCut {
			panic(cut)
		}
		if plannedReplay {
			// The plan's rung did not close: the bare probe, passed over
			// for it, is asked now.
			arm()
			bare := step
			bare.s4 = nil
			if sg := bare.probeBare(p); sg != nil {
				return closed(sg)
			}
		}
		if !numerals {
			panic(failure)
		}
		arm()
		reading := step
		reading.numerals, reading.s4 = true, &byS4State{}
		if sg, _ := reading.attempt(p); sg != nil {
			noteByClose(step.ctx, byNumeralRoute)
			return closed(sg)
		}
		panic(failure)
	}
	beforeConditioned := watch.Fired()
	sg, conditionedFailure := step.attempt(p)
	if sg != nil {
		return closed(sg)
	}
	// The conditioned rung's cut-off, if a refutation of it ran to
	// budget: the probes above run no live search, and each later
	// rung's refutations are its own.
	conditionedCutOff := step.ladder.cutOff
	step.ladder.cutOff = ""
	// The grounding kept a source a match pinned in full, and the leaf did
	// not close: the search may be lost in the wide form where the
	// instances are all it needs, or a shaping's Basic() has discarded the
	// instances beside it. The rung is run on the pruned leaf, each such
	// source replaced by its instances. What it closes records the plan of
	// this run, which replaces, so a replay applies that plan in its one
	// conditioned rung and never comes here.
	prunedRun := step.ladder.prunable && !step.arith
	if prunedRun {
		step.stopIfCut("before the conditioned rung on the pruned leaf")
		skipFrom, skipTo = cutsAPrunedRunReplaySkips(beforeConditioned, watch.Fired(), conditionedCutOff)
		step.prune = true
		step.s4 = &byS4State{}
		arm()
		if pruned, _ := step.attempt(p); pruned != nil {
			noteByClose(step.ctx, byPrunedRoute)
			step.reportBudgetPick(conditionedCutOff, byPrunedRunPick)
			return closed(pruned)
		}
		step.prune = false
		// A cut-off of either run of the conditioned rung is one a
		// recording run with the time closes at.
		if conditionedCutOff == "" {
			conditionedCutOff = step.ladder.cutOff
		}
		step.ladder.cutOff = ""
	}
	step.stopIfCut("before the bare retry rung")
	step.condition = false
	step.s4 = nil
	arm()
	skipFrom, skipTo = 0, cutsARetryReplaySkips(watch.Fired(), conditionedCutOff)
	if bare, _ := step.attempt(p); bare != nil {
		step.reportBudgetPick(conditionedCutOff, byRetryPick)
		return closed(bare)
	}
	if numerals {
		step.stopIfCut("before the conditioned rung reading numerals")
		arm()
		reading := step
		reading.numerals, reading.condition, reading.s4 = true, true, &byS4State{}
		if sg, _ := reading.attempt(p); sg != nil {
			noteByClose(step.ctx, byNumeralRoute)
			return closed(sg)
		}
	}
	if conditionedFailure != nil {
		if text, isText := conditionedFailure.(string); isText && prunedRun {
			conditionedFailure = text + "\n" + byPrunedNote
		}
		panic(conditionedFailure)
	}
	return nil
}

// byNumeralRoute is the route a close adds where the rung that closed
// is one of the ladder's that read numerals (applyLadder).
const byNumeralRoute = "reading numerals at the apply rung"

// byPrunedRoute is the route a close adds where the run that closed is
// the conditioned rung's on the pruned leaf (applyLadder).
const byPrunedRoute = "conditioned on the pruned leaf"

// byPrunedNote is what the conditioned rung's failure says where the
// ladder ran it again on the pruned leaf and that did not close.
const byPrunedNote = "The conditioned rung was run again on the pruned leaf, each premise a match pinned in " +
	"full replaced by its instances, and did not close either: the wide premises are not what the search is lost in."

// cutsAPrunedRunReplaySkips bounds the whistle cuts a replay does not meet
// when the run that closes is the conditioned rung's on the pruned leaf:
// before is how many cuts the probes reported, after how many had been
// reported when the run on the whole leaf failed, and wholeCutOff that
// run's cut-off, empty when no refutation of it ran to budget.
//
// A run on the whole leaf that failed on its own fails in every recording
// run too, so the recording holds the pruned run's plan and its replay
// runs the probes and that plan: the whole run's cuts are skipped, the
// probes' are met. A whole run cut off at the refuter's budget closes in
// a recording given the time, whose replay meets its cuts: either
// recording can be the one written, so none is skipped.
func cutsAPrunedRunReplaySkips(before, after int, wholeCutOff string) (from, to int) {
	if wholeCutOff != "" {
		return 0, 0
	}
	return before, after
}

// cutsARetryReplaySkips is how many of the whistle cuts reported before
// the bare retry a replay does not meet when the retry is the rung that
// closes. conditionedCutOff is the cut-off of the conditioned rung, in
// either of its runs, empty when no refutation of it ran to budget.
//
// A conditioned rung that failed on its own, in each run of it, fails
// in every recording run too, so the recording holds the retry's rows and
// its replay closes at the bare probe on them: the retry's path, which
// repeats the probe's cuts and runs no conditioned rung. All the earlier
// cuts are skipped.
// A conditioned rung cut off at the refuter's budget is another matter:
// given the time a recording closes there (reportBudgetPick), and its
// replay runs the probe and that rung. Either recording can be the one
// written, so none of the earlier cuts is skipped.
func cutsARetryReplaySkips(before int, conditionedCutOff string) int {
	if conditionedCutOff != "" {
		return 0
	}
	return before
}

// attempt runs applyInner converting its close-or-fail panic into a
// captured value, so the ladder can try another rung.
func (step _ByStep) attempt(p Prop) (sg *SubGoals, failure any) {
	defer func() { failure = rungFailure(recover()) }()
	return step.applyInner(p), nil
}

// rungFailure is a rung's recovered panic as the ladder reads it
// (utils.Failure). A fault — a refutation one of whose goroutines
// panicked (refuter.SearchFault), any panic carried off another
// goroutine (utils.Fault), a failed assertion (utils.Assert: an
// invariant breach, which panics by contract), an error of the Go
// runtime (a nil dereference, an index out of range, a failed type
// assertion) — is no rung failure: it is raised again as it is, since
// a later rung that closed the leaf would hide the break. Every other
// value is the rung's failure. Every recover of the By reads its panic
// through this: the rungs and probes, the cache-only ones included, the
// recovers inside a rung that attribute a failure or tolerate one, and
// the member check's typing (typedForMembers).
func rungFailure(r any) any {
	return utils.Failure(r)
}

// probeFailure reads the recovered panic of a probe rung (probeBare,
// probeKeyless). A rung's failure is dropped: the ladder goes on to the
// next rung. A cut-off is raised again: the rung's context is the
// ladder's, so the next poll of the ladder would raise one, naming its
// own stage and not the one the time went to.
func probeFailure(r any) {
	if cut, ok := rungFailure(r).(byCutOff); ok {
		panic(cut)
	}
}

// probeBare is rung 1: the bare attempt with CNF refutes cache-only.
// The probe rides a context mark (withCNFCacheOnlyProbe) rather than an
// env flip — ProverEnv holds shared caches and cannot be copied — and
// tryCNFRefute treats a marked context exactly as strict replay: a MISS
// panics, which is the graceful probe failure recovered here.
func (step _ByStep) probeBare(p Prop) (sg *SubGoals) {
	defer func() { probeFailure(recover()) }()
	step.ctx = withCNFCacheOnlyProbe(step.ctx)
	step.condition = false
	step.failureUnread = true
	return step.applyInner(p)
}

// probeKeyless is rung 0: the conditioned attempt with the refuter
// barred (withNoRefuteProbe — reaching resolution is failure, before any
// cache is consulted) and S4's grounding off, so it reads no key and
// applies no plan; a strict replay's ends at a leaf the store holds a
// plan for, and tells the ladder (byLadderState.planned). The audit
// state stays the ladder's: a leaf this probe carried to resolution is
// captured for Probe A, which then says so when the conditioned leaf
// closes under Basic() — the advice a warm run could not give while rung
// 1 answered first.
func (step _ByStep) probeKeyless(p Prop) (sg *SubGoals) {
	defer func() { probeFailure(recover()) }()
	step.ctx = withNoRefuteProbe(step.ctx)
	step.condition = true
	step.keyless = true
	step.s4 = &byS4State{}
	step.failureUnread = true
	return step.applyInner(p)
}

// cnfCacheOnlyProbeKey marks a context as By's rung-1 probe: CNF
// refutes behave as strict replay (cache-only, MISS panics) regardless
// of env.RequireCNFCacheHit. Read by cnfRefuteContexts / tryCNFRefute.
type cnfCacheOnlyProbeKey struct{}

func withCNFCacheOnlyProbe(ctx context.Context) context.Context {
	return context.WithValue(ctx, cnfCacheOnlyProbeKey{}, true)
}

// exactKeysOnlyKey marks a context as a rung of a strict replay's exact
// pass: tryCNFRefute asks the store's exact-key table for the leaf's
// certificate and fails the rung where that does not close the leaf,
// before it computes the key a certificate is stored under. A rung
// under the mark normalizes no refute prop.
type exactKeysOnlyKey struct{}

func withExactKeysOnly(ctx context.Context) context.Context {
	return context.WithValue(ctx, exactKeysOnlyKey{}, true)
}

func exactKeysOnly(ctx context.Context) bool {
	v, _ := ctx.Value(exactKeysOnlyKey{}).(bool)
	return v
}

// noRefuteProbeKey marks a context under which reaching the CNF stage
// AT ALL is failure: tryCNFRefute panics before consulting any cache,
// and the probe's recover reads that as "did not close". It is the
// keyless rung's mark (probeKeyless).
type noRefuteProbeKey struct{}

func withNoRefuteProbe(ctx context.Context) context.Context {
	return context.WithValue(ctx, noRefuteProbeKey{}, true)
}

// auditReplayProbeKey marks a context as the economy audit's replay
// probe and carries its state (byAuditReplay). Under the mark the By
// without one element runs the recorder's ladder held to the rows the
// audited close touched, and whatever a recording of that spelling
// would add to the member's rows fails it:
//
//   - a refute at a key among those rows is served from the store and
//     never searched (the context is cache-only too); one at any other
//     key fails before the store serves it (tryCNFRefute) — the
//     recorder would read a row the close does not touch, or search
//     and write one;
//   - the grounding stage applies a plan among those rows; a plan the
//     store holds besides, and a grounding the stage would search out
//     and record, fail (groundStage).
//
// So a probe that closes names a spelling whose recording touches no
// row the audited close does not. The bound is that close's rows and
// not the store: a store being recorded into holds the rows of
// spellings since abandoned, and a probe served from those calls a
// marker inert whose removal brings its key into the member's rows
// (measured on `Normalized`: 11 of 17 such verdicts in one family were
// wrong against a cold recording). Whether the store holds a row off
// the close's is asked without serving it (cnfStoreHoldsProof), so a
// capturing store's record of the member stays what the member reads.
type auditReplayProbeKey struct{}

// byAuditReplay is one replay probe's state.
type byAuditReplay struct {
	// rows is what the audited close touched: the bound.
	rows *byCloseTrace
	// read is the rows among them the probe was served: what a recording
	// of the probe's spelling touches.
	read byCloseTrace
	// offRows records that the ladder met a row the store holds and the
	// audited close does not touch. The recorder's bare rung would have
	// been served it, so no later rung can make the element inert: the
	// ladder stops at the rung's end (applyLadder).
	offRows bool
}

func withAuditReplayProbe(ctx context.Context, rows *byCloseTrace) context.Context {
	return withCNFCacheOnlyProbe(context.WithValue(withByAuditProbe(ctx), auditReplayProbeKey{}, &byAuditReplay{rows: rows}))
}

// auditReplayOf is the replay probe a context runs under, nil outside one.
func auditReplayOf(ctx context.Context) *byAuditReplay {
	replay, _ := ctx.Value(auditReplayProbeKey{}).(*byAuditReplay)
	return replay
}

// byCloseTrace observes one successful attempt without changing its proof:
// the closing routes (by_closer) and the rows the recorder would write for
// the close — the certificate keys its refutes wrote or read and the
// conditioning plans it persisted (the session `by`'s Records sink).
type byCloseTraceKey struct{}
type byCloseTrace struct {
	routes []string
	keys   []core.PropKey
	plans  []core.PropKey
}

// addKey / addPlan record one row the close touched, de-duplicated: a key
// reached twice (read then the same leaf again) is one row.
func (t *byCloseTrace) addKey(key core.PropKey)  { t.keys = appendUniquePropKey(t.keys, key) }
func (t *byCloseTrace) addPlan(key core.PropKey) { t.plans = appendUniquePropKey(t.plans, key) }

func appendUniquePropKey(keys []core.PropKey, key core.PropKey) []core.PropKey {
	if slices.Contains(keys, key) {
		return keys
	}
	return append(keys, key)
}

// holdsKey / holdsPlan report whether the close touched the row.
func (t *byCloseTrace) holdsKey(key core.PropKey) bool  { return slices.Contains(t.keys, key) }
func (t *byCloseTrace) holdsPlan(key core.PropKey) bool { return slices.Contains(t.plans, key) }

// anyClosedDescendant reports a branch closed below a previously open leaf.
// Counting leaves alone loses a close when shaping also creates a new fan.
func anyClosedDescendant(nodes []*GoalStackNode) bool {
	for _, node := range nodes {
		if node.Proved() || anyClosedDescendant(node.Children()) {
			return true
		}
	}
	return false
}

func noteByClose(ctx context.Context, route string) {
	trace, _ := ctx.Value(byCloseTraceKey{}).(*byCloseTrace)
	if trace == nil || byAuditProbe(ctx) {
		return
	}
	for _, previous := range trace.routes {
		if previous == route {
			return
		}
	}
	trace.routes = append(trace.routes, route)
}

// noteRecordKey records a certificate key the close wrote (a live refute)
// or read (a cached certificate), for the recorder-rows report. Guarded
// as noteByClose is: an economy-audit probe's downward re-run records
// nothing, and the no-refute probe never reaches a key — neither pollutes
// the report. A rung-1 cache-only hit is NOT excluded: the row it read is
// one the recorder writes.
func noteRecordKey(ctx context.Context, key core.PropKey) {
	trace, _ := ctx.Value(byCloseTraceKey{}).(*byCloseTrace)
	if trace == nil || byAuditProbe(ctx) || noRefuteProbe(ctx) {
		return
	}
	trace.addKey(key)
}

// noteRecordPlan records a conditioning plan the close persisted
// (persistConditionPlans) or applied from the store (groundStage), for
// the recorder-rows report.
func noteRecordPlan(ctx context.Context, key core.PropKey) {
	trace, _ := ctx.Value(byCloseTraceKey{}).(*byCloseTrace)
	if trace == nil || byAuditProbe(ctx) || noRefuteProbe(ctx) {
		return
	}
	trace.addPlan(key)
}

// byAuditStateKey carries the armed audit's state down to tryCNFRefute,
// which appends the leaf at the point resolution is reached (step.go).
type byAuditStateKey struct{}

func withByAuditState(ctx context.Context, st *byAuditState) context.Context {
	return context.WithValue(ctx, byAuditStateKey{}, st)
}

func byAuditStateOf(ctx context.Context) *byAuditState {
	st, _ := ctx.Value(byAuditStateKey{}).(*byAuditState)
	return st
}

func noRefuteProbe(ctx context.Context) bool {
	v, _ := ctx.Value(noRefuteProbeKey{}).(bool)
	return v
}

// CNFCacheOnlyContext marks a context so every CNF refute under it
// replays from the store and never searches — a MISS panics as in
// strict replay. The engine's session resume runs a recorded
// transcript under it: a refute the record does not cover is a
// divergence, not a live search.
func CNFCacheOnlyContext(ctx context.Context) context.Context { return withCNFCacheOnlyProbe(ctx) }

func cnfCacheOnlyProbe(ctx context.Context) bool {
	v, _ := ctx.Value(cnfCacheOnlyProbeKey{}).(bool)
	return v
}

// byAuditProbeKey marks a context as an economy-audit probe (a
// downward re-run of a By that already closed). Under the mark the
// executor records NOTHING — tryCNFRefute withholds its certificate
// write, persistConditionPlans is a no-op, and applyLadder never arms
// a nested audit — because a probe exists to ANSWER a question, and a
// probe that persisted would turn the report-only stage into a
// behaviour.
type byAuditProbeKey struct{}

func withByAuditProbe(ctx context.Context) context.Context {
	return context.WithValue(ctx, byAuditProbeKey{}, true)
}

func byAuditProbe(ctx context.Context) bool {
	v, _ := ctx.Value(byAuditProbeKey{}).(bool)
	return v
}

// byAuditProbeBudget caps probe A's Basic() search on one leaf (the
// replay probes search nothing and read no clock). The
// audit asks whether a CHEAPER spelling closes the leaf, so a probe
// slower than the close it questions has answered "no" by
// construction — and an unbounded Basic() is minutes, not
// milliseconds, on a leaf that carries several ⇔ or ∃-conjunction
// hypotheses (the quotient bridges' closing split), which is where an
// unbounded probe makes a family GC spend its time.
const byAuditProbeBudget = 250 * time.Millisecond

// byBroadcastRoundBudget caps the Broadcast loop's rounds: one round
// conditions one working leaf, shapes it and closes it, so a fan that
// converges spends one round per leaf it produced. A shaping that
// re-fans each leaf it conditions produces leaves faster than the
// closer takes them, and the loop would run until the process is
// killed (measured at eleven CPU-minutes before it was). Sixty-four
// is far above any fan a recorded member has needed (the widest
// measured is single digits) and far below what a non-converging fan
// reaches in its first second.
const byBroadcastRoundBudget = 64

// byCutOff is the refusal a By raises when its context is done — a
// session request's deadline or budget, a probe's budget, a caller that
// went away. The executor polls the context BETWEEN units of work and
// never before the first: before each round over the working leaves
// after the first, each Arith firing after the first on a leaf, each
// step of the shaping stage's Basic() after the first, and the
// ladder's conditioned rung and bare retry. So a unit in flight
// finishes, a close the first unit makes is never refused, and the
// overrun past the deadline is at most one unit. Inside a unit five
// things read the same context: the CNF refuter's search; the
// normalization that keys a refute (tryCNFRefute), seconds on a wide
// leaf, which polls before each of its stages and inside the two that
// are slow on a wide disjunction; the install of a premise through the
// preserving chain (installPremise), whose unifications each run to a
// work budget of seconds where the premise is an equation read as a
// rule with a variable for its head; an Arith firing, whose decision
// polls before each leaf of the decider (arithFiring), since one
// decision can outlast any budget; and the arithmetic decision the
// apply rung tries on an antecedent (closeByArith), the same decider,
// which a rung asks of every antecedent of every head it weighs. A
// context done when a premise installs, during an Arith firing or an
// antecedent's decision, or while a key is normalized therefore cuts
// the By off there, first unit or not (cutOffInside): a close is
// refused where its budget is shorter than the close. Nothing else
// reads a clock; an Arith close whose firings rewrite its leaf without
// closing it would otherwise run the round bound out on every rung
// with the session locked (measured: minutes under a 5 s probe
// budget). A replay's By carries context.Background() and is never cut
// off.
type byCutOff struct {
	closer string
	stage  string
	cause  error
}

func (c byCutOff) Error() string {
	return fmt.Sprintf("By: the %s close was cut off %s — its context is done (%v): the request's deadline "+
		"or budget passed, or its caller went away. The close did not run to its end, so this is no "+
		"evidence about the premises or the shape. Make the step smaller — fewer premises, or the "+
		"intermediate fact the closer needs asserted first, as its own step — before raising the budget.",
		c.closer, c.stage, c.cause)
}

// stopIfCut raises byCutOff when the step's context is done; stage
// names the unit of work it stops before.
func (step _ByStep) stopIfCut(stage string) {
	if err := step.ctx.Err(); err != nil {
		panic(byCutOff{closer: step.closerName(), stage: stage, cause: err})
	}
}

// cutOffInside, deferred by the ladder, turns a utils.Cut raised inside
// one of its units into the By's cut-off, the unit its stage: the key
// normalization of a refute (tryCNFRefute), which the refuter's By, the
// set driver's and every cache-only probe of the ladder reach. Any other
// panic goes up as it is.
func (step _ByStep) cutOffInside() {
	if r := recover(); r != nil {
		if cut, ok := utils.AsCut(r); ok {
			panic(byCutOff{closer: step.closerName(), stage: cut.Where, cause: cut.Cause})
		}
		panic(r)
	}
}

// arithFiring runs one Arith firing of the closer on leaf under the
// step's context. A firing the context cut off inside the decision is
// the By's cut-off.
func (step _ByStep) arithFiring(leaf *GoalStackNode, rounds *_ArithRounds) bool {
	defer func() {
		if r := recover(); r != nil {
			if cut, ok := utils.AsCut(r); ok {
				panic(byCutOff{closer: step.closerName(), stage: cut.Where, cause: cut.Cause})
			}
			panic(r)
		}
	}()
	return leaf.runStep(_Arith{rounds: rounds, ctx: step.ctx})
}

// installPremise installs claim on the leaf l through the preserving
// chain — ApplyLemmaPreserve, or with exact its form that adapts no type
// — under the step's context. The chain reads an equation as a rewrite
// rule and unifies its pattern against the terms of the leaf, each
// unification under a work budget of its own and no clock; a chain the
// context ends is cut off rather than read as a premise that does not
// install.
func (step _ByStep) installPremise(l *GoalStackNode, claim Prop, exact bool, desc string) bool {
	installed, cut := l.installLemmaPreserveUntil(step.ctx, claim, exact)
	if cut {
		panic(byCutOff{closer: step.closerName(), stage: "inside the install of premise " + desc, cause: step.ctx.Err()})
	}
	return installed
}

func (step _ByStep) applyAction(s *Script, root *GoalStackNode) {
	step.spine = root.unsolvedLeaf(0)
	s.Do(root, step)
}

// byWorkingLeaf returns the first unsolved leaf of the private tree
// that is NOT a pending claim obligation — the leaf the next premise
// installs into / the terminal closer refutes. Claim obligations stay
// open by design (they become the composite's SubGoals children).
func byWorkingLeaf(root *GoalStackNode, claims []*GoalStackNode) *GoalStackNode {
	if open := byWorkingLeaves(root, claims); len(open) > 0 {
		return open[0]
	}
	return nil
}

// byWorkingLeaves is byWorkingLeaf's plural: every unsolved non-claim
// leaf, in tree order. The still-open diagnostic prints what remained.
func byWorkingLeaves(root *GoalStackNode, claims []*GoalStackNode) []*GoalStackNode {
	var out []*GoalStackNode
	for _, leaf := range root.UnsolvedLeaves() {
		isClaim := false
		for _, c := range claims {
			if leaf == c {
				isClaim = true
				break
			}
		}
		if !isClaim {
			out = append(out, leaf)
		}
	}
	return out
}

// collectClaimObligations gathers the open claim children a preserving
// install just produced under n: children whose goal α-equals the
// ADAPTED lemma the install recorded (LemmaTactic's contract: "the
// first subgoal is always the lemma itself"). The adapted form is read
// off the committed ministep, so type adaptation cannot desynchronize
// the test.
func collectClaimObligations(n *GoalStackNode) []*GoalStackNode {
	lp, ok := n.miniStep.(_LemmaPreserveTactic)
	if !ok {
		return nil
	}
	adapted := lp.lemma.AsProp()
	var claims []*GoalStackNode
	for _, c := range n.Children() {
		if c.Proved() {
			continue
		}
		if c.Goal.AlphaEquals(adapted) {
			claims = append(claims, c)
		}
	}
	return claims
}

// applyInner is the shared executor. Panics carry the premise-economy
// diagnostics the By macro is chartered to produce (the By-MISS
// decision tree included); the engine dispatch recovers them into
// errors. Returns the composite SubGoals: children = the claim
// obligations in premise order, reconstruct = certify those claims and
// read the private tree's root certificate.
func (step _ByStep) applyInner(p Prop) *SubGoals {
	if step.closeTrace != nil {
		step.closeTrace.routes = nil
	}
	Assert(step.env != nil)
	if len(step.premises) == 0 && !step.arith && !step.settac {
		// A premise-free BySets or ByArith is a legal bare form
		// (fact.go): the closer's own procedure is its content.
		panic("By: empty premise list (a bare refutation is CnfRefute())")
	}

	described := make([]string, len(step.premises))
	for i, pr := range step.premises {
		described[i] = pr.description()
	}

	// A ⊥-form leaf carries its obligation in the HYPS, so clear-first
	// would delete the thing to be refuted — the premise list must name
	// them. (Same guard as the macro layer; kept here so the session
	// dispatch inherits it.)
	if p.Conclusion().Equals(F) {
		named := false
		for _, pr := range step.premises {
			if pr.resident {
				named = true
				break
			}
		}
		if !named {
			panic(fmt.Sprintf("By: this leaf is a ⊥-refutation obligation — its content is in the "+
				"hypotheses, and By clears every hyp the premise list does not name.\n"+
				"  Name the hyps that carry the goal (a.Hyp(...)) as premises, or close this leaf "+
				"with a bare CnfRefute.\n  premises: %s\n  leaf: %s",
				strings.Join(described, ", "), prop.PrintProp(p)))
		}
	}

	root := CreateGoalStack(p)
	if step.scope != nil {
		root.SetProofScope(step.scope)
	}

	// Phase 1 — locate the resident premises: their source hyps are the
	// keep set. Also count uses per source (α-keyed) so grounding keeps
	// the ∀-source until its last use.
	var keep []core.Term
	addKeep := func(t core.Term) {
		for _, k := range keep {
			if k.AlphaEquals(t) {
				return
			}
		}
		keep = append(keep, t)
	}
	remaining := map[core.TermKey]int{}
	for i, pr := range step.premises {
		if !pr.resident {
			continue
		}
		src := pr.install.AsProp().Conclusion()
		idx, err := findHypIndex(p, src)
		if err != nil {
			panic(fmt.Sprintf("By: premise %s names no resident hypothesis of this leaf\n  premises: %s\n  on leaf goal: %s",
				described[i], strings.Join(described, ", "), prop.PrintProp(p)))
		}
		remaining[src.AlphaKey()]++
		addKeep(p.Hyp(idx))
	}

	// Phase 2 — lexical scope: clear every ambient hyp that is not a
	// listed resident premise.
	var drop []int
	var droppedText []string
	for i := 0; i < p.NumHyps(); i++ {
		h := p.Hyp(i)
		kept := false
		for _, k := range keep {
			if k.AlphaEquals(h) {
				kept = true
				break
			}
		}
		if !kept {
			drop = append(drop, i)
			droppedText = append(droppedText, ext.PrintTerm(h))
		}
	}
	if len(drop) > 0 {
		if !ApplyClearHyps(root, drop) {
			panic(fmt.Sprintf("By: clearing the unnamed ambient hyps had no effect (engine invariant break)\n  premises: %s",
				strings.Join(described, ", ")))
		}
	}

	// Phase 3 — materialize the named premises in order; ground the
	// witnessed ones (resident and named alike).
	var claims []*GoalStackNode
	closedAt := -1
	// A premise whose ∀-form install absorbs the goal never has its
	// witness tuple applied — the tuple is then unchecked text, and a
	// wrong instance replays green. Cite refuses this ("witnesses are
	// unused — cite bare instead", goal_stack.go); By enforces the same
	// contract, and the panic carries which premise so the fix is one
	// edit.
	unappliedWitnesses := ""
	// installedStatement[i] is premise i's resident statement once
	// materialized and grounded — what a scaled premise's congruence
	// reads (phase 3b).
	installedStatement := make([]Term, len(step.premises))
	// clauseInstalled[i]: premise i, witnessed, took its clause form
	// (useClause below) — its stated form is then the rung's head.
	clauseInstalled := make([]bool, len(step.premises))
	clauseGuards := map[int]core.Term{}
	var bareInstalls []byBareInstall
	for i, pr := range step.premises {
		l := byWorkingLeaf(root, claims)
		if l == nil {
			closedAt = i - 1
			break
		}
		desc := described[i]
		func() {
			defer func() {
				if r := rungFailure(recover()); r != nil {
					if cut, ok := r.(byCutOff); ok {
						// An install cut off failed for want of time, and
						// says nothing of whether the premise materializes.
						panic(cut)
					}
					panic(fmt.Sprintf("By: premise %s failed to materialize\n  premises: %s\n  on leaf goal: %s\ncause: %v",
						desc, strings.Join(described, ", "), prop.PrintProp(l.Goal), r))
				}
			}()
			switch {
			case pr.derivedCert != nil:
				// The kit premise: assert its claim, close the claim
				// branch from the kit's certificate, continue with the
				// fact resident — at THIS list position. A claim that IS
				// the goal is no assertion (the assert makes no progress):
				// its certificate closes the leaf outright — a reading
				// whose conclusion is the goal, `By(law.Read(fact))`; a
				// claim already resident needs nothing.
				claim := pr.install.Conclusion()
				// Resident once materialized, whichever way: what a
				// coefficient on the premise scales (phase 3b).
				installedStatement[i] = claim
				// The certificate stands on the hypotheses its reading
				// located; a leaf without one of them — the economy
				// audit's probe dropped the located premise — cannot take
				// it, and the premise fails to materialize, which the
				// probe reads as the drop not being inert.
				for h := range pr.derivedCert.HypIter() {
					if !l.Goal.HasHyp(h) {
						panic(fmt.Sprintf("its certificate stands on the hypothesis %s, which the leaf does not hold", ext.PrintTerm(h)))
					}
				}
				if l.Goal.Conclusion().AlphaEquals(claim) {
					if !l.runStep(_KnownThmStep{strongerGoal: pr.derivedCert}) {
						panic("its own certificate does not close the goal it states")
					}
					return
				}
				if l.Goal.HasHyp(claim) {
					return
				}
				if !l.runStep(_AssertStep{claim: pr.install}) {
					panic("asserting the self-proving premise's claim failed")
				}
				Assert(len(l.Children()) == 2)
				if !l.Children()[0].runStep(_KnownThmStep{strongerGoal: pr.derivedCert}) {
					panic("its own certificate does not close the asserted claim")
				}

			case pr.resident && len(pr.witnesses) == 0:
				// Located and kept in phase 1; nothing to materialize.
				installedStatement[i] = pr.install.AsProp().Conclusion()

			case len(pr.named) > 0:
				// Pinned by name: the apply rung installs the stated form
				// on the fire that closes the leaf (applyClose) — a plain
				// install here could only absorb the goal or feed the
				// closer a law the author meant to APPLY.

			case pr.resident:
				// Ground the resident source at the witnesses. Consumed
				// inside this leaf unless a later premise grounds the same
				// source again.
				src := pr.install.AsProp().Conclusion()
				idx, err := findHypIndex(l.Goal, src)
				if err != nil {
					panic(fmt.Sprintf("resident premise vanished before grounding: %v", err))
				}
				remaining[src.AlphaKey()]--
				var ok bool
				preGround := l.Goal
				if remaining[src.AlphaKey()] > 0 {
					ok = l.runStep(SpecializeKeep(InstHyp(idx, pr.witnesses...)))
				} else {
					ok = l.runStep(Specialize(InstHyp(idx, pr.witnesses...)))
				}
				if !ok {
					panic("grounding the resident premise failed")
				}
				if gl := byWorkingLeaf(root, claims); gl != nil {
					if gi, gerr := newHypIndex(preGround, gl.Goal); gerr == nil {
						installedStatement[i] = gl.Goal.Hyp(gi)
					}
				}

			default:
				// Named fact: preserving install; the claim obligation is
				// LEFT OPEN — it becomes a SubGoals child the caller
				// certifies (macro: the Fact's cert; session: auto-match).
				// A BARE premise installs in the closer's clause form
				// (byPremise.clause); its stated form is the apply rung's
				// head. A witnessed one grounds the stated form.
				L := pr.installedForm()
				// clauseInstall marks a witnessed premise taking its CLAUSE
				// form (below): it then installs through the preserving
				// chain exactly as before the migration — the chain's own
				// type adaptation, its own strategies — not the stated
				// path's plain add.
				clauseInstall := false
				// Replay-form divergence guard (witnessed CONJ-headed
				// premises only): the Fact a premise resolves to can
				// state the dep file's ORIGINAL form — a conjunction of
				// ∀-clauses, e.g. LibraryThm("nat_pow") / LibraryThm("LT") —
				// while the recorded witness tuple grounds the
				// NORMALIZED ∀∀-headed form the session actually
				// installed. Specialize cannot take a tuple at an ∧ head
				// (pre-guard this was a guaranteed materialize panic, so
				// the swap cannot regress a passing proof), and leaving
				// the premise ungrounded diverges the leaf from the
				// session's (a strict-replay CNF cache MISS). Installing
				// the fact's NORMALIZATION reproduces the session hyp —
				// same grounding, same leaf, same cache key — and its
				// claim obligation certifies through the normalized-key
				// cache tier exactly like any normalize-equivalent cite.
				// Non-conj stated forms (∀-headed, ∃-headed) keep the
				// verbatim install: they ground today (pairs.PairEq's
				// ∃-form premise is the live counterexample to a looser
				// ∀-prefix-count predicate).
				if n := len(pr.witnesses); n > 0 {
					// Which form the tuple grounds. A ∧-headed matrix (the
					// clause-pack shape, any target) grounds its prenex form,
					// where the binders stand. A NAMED premise takes its
					// STATED form exactly where the grounding leaves an
					// unguarded fact — every guarded binder grounded, every
					// leading guard of the instance supplied by the context
					// by assumption (statedGuardsSupplied; Lean's `f x₀ ‹A›`)
					// — and otherwise the clause form the closer was built
					// and recorded on: a partial tuple, a ⇔ matrix (whose
					// stated instance the Normalized stage case-splits into
					// leaves a single-leaf close never reaches), a guard the
					// context would have to prove. An explicit premise (no
					// clause form) stays verbatim beyond the ∧ case. The
					// reference (below) stays the stated form the tuple was
					// written against.
					concl := L.AsProp().Conclusion()
					_, matrix := ematch.StripGuardedForalls(concl)
					_, _, packAnd := ext.MatchesAND(matrix)
					// A sequent — a law read under a resident hypothesis —
					// grounds its stated form whatever its matrix: its free
					// variables are the leaf's own terms and its hypothesis
					// the leaf's, and the closed clause form would ∀-close
					// those terms and fold the hypothesis back in as an
					// antecedent, which is the law the reading was taken
					// from, its instance lost.
					useClause := packAnd && L.AsProp().NumHyps() == 0
					// A stated form in the standard form, `∀xs. H₁ ∧ … ⇒ C`,
					// is read at the tuple as the telescope at its prefix
					// (prop.PrefixTelescope): the hypotheses about the
					// grounded binders alone stand ahead, as the guards the
					// grounding leaves, the rest behind the binders left —
					// where a curried spelling put them.
					stated := L.AsProp()
					at := func(k int) Prop { return prop.PrefixTelescope(stated, k) }
					if pr.clause != nil && !useClause {
						typed := at(n)
						if !pr.exact && ext.PropHasTypeVars(L) {
							typed = witnessTypedForm(typed, pr.witnesses, l.Goal)
						}
						// A tuple naming a stated PREFIX that stops short of
						// the guarded binders — a principle cited at its
						// predicate alone — is completed from the goal: the
						// remaining binders are read off the stated
						// conclusion matched against the goal (the apply
						// rung's head matcher, seeded with the author's
						// witnesses), and the premise takes its stated form
						// as the terminal grounds it — exactly where that
						// form's guards are supplied, so a tuple the context
						// cannot serve keeps the clause lane and its recorded
						// key. The recorded tuple stays the author's; replay
						// completes it the same way against the same goal.
						if completed := completeStatedTuple(l.Goal, typed, pr.witnesses, step.door()); completed != nil {
							ctyped := at(len(completed))
							if !pr.exact && ext.PropHasTypeVars(L) {
								ctyped = witnessTypedForm(ctyped, completed, l.Goal)
							}
							if statedGuardsSupplied(l.Goal, ctyped, completed, step.door()) {
								pr.witnesses = completed
								n = len(completed)
								typed = ctyped
							}
						}
						_, _, packIff := ext.MatchesIFF(matrix)
						useClause = packIff || !statedGuardsSupplied(l.Goal, typed, pr.witnesses, step.door())
						if useClause && !packIff {
							if g := unsuppliedStatedGuard(l.Goal, typed, pr.witnesses, step.door()); g != nil {
								// Read only where a failure prints the premise list.
								clauseGuards[i] = g
								described[i] += fmt.Sprintf("\n      (installed in its clause form, for the closer: the context does "+
									"not supply this instance's guard %s as written, conjunct by conjunct or one apply deep; "+
									"name the fact that supplies it)",
									clipRunes(ext.PrintTerm(g), 120))
							}
						}
					}
					if useClause {
						// The clause form is the REGISTERED one where there is
						// one (byPremise.clause: a typed instance's install
						// half, the normalized dep) — Normalize and type
						// instantiation do not commute, and the tuple was
						// authored against the registered prefix.
						nl := pr.clause
						if nl == nil {
							nl = InstallForm(L.AsProp())
						}
						if nl != nil {
							if names, _ := forallPrefixNames(nl.Conclusion()); len(names) >= n {
								L = nl
								clauseInstall = true
								clauseInstalled[i] = true
								// A partial tuple is still read in the STATED
								// order: where the clause's canonical labeling put
								// the stated binders behind others, they are moved
								// to the front of the ∀-block (leadStatedBinders).
								if n < len(names) {
									ref := pr.reference
									if ref == nil {
										ref = pr.install
									}
									if led := leadStatedBinders(L, ref, n); led != nil {
										L = led
									}
								}
							}
						}
					}
					if !useClause {
						L = at(n)
					}
					// ⇒-headed stated forms are the other head Specialize
					// cannot take a tuple at — the spec-parametric statement
					// style (proofs/cartesian/carrier), where a lemma reads
					// `defs ⇒ ∀n. … vsp(n, y) ⇒ ∀x. …` and every ∀ the tuple
					// must reach sits behind an antecedent. Full Normalize is
					// the WRONG swap here (it ∀-closes the statement's free
					// spec variables and Skolemizes the negated antecedents —
					// the prefix stops matching the stated binders); the
					// targeted lift below commutes leading antecedents under
					// the ∀-chain (`P ⇒ ∀x. Q ↦ ∀x. (P ⇒ Q)`, binder and
					// antecedent order both preserved), which keeps the
					// witness tuple aligned with the STATED binder order and
					// leaves everything else verbatim. The claim obligation
					// certifies through the same normalize-equivalence tiers
					// as the ∧-headed swap above.
					if _, _, isImp := matchesImply(L.AsProp().Conclusion()); isImp {
						if lifted := prenexForallChain(L.AsProp().Conclusion()); lifted != nil {
							if names, _ := forallPrefixNames(lifted); len(names) >= n {
								L = prop.MakeProp(lifted)
							}
						}
					}
				}
				// A witnessed premise is typed by its tuple
				// (witness_order.go); a bare one adapts to the goal as the
				// preserving chain adapts it; an explicit instance installs
				// as it is.
				claim := L
				if !pr.exact && ext.PropHasTypeVars(L) {
					switch {
					case len(pr.witnesses) > 0 && !clauseInstall:
						claim = witnessTypedForm(L, pr.witnesses, l.Goal)
					case len(pr.witnesses) > 0:
						// The clause form at the goal's types: of every
						// adaptation the goal offers, the first whose binder
						// types the tuple fits — the tuple read in the stated
						// order and mapped onto the clause prefix by name.
						ref := pr.reference
						if ref == nil {
							ref = pr.install
						}
						claim = clauseTypedForWitnesses(L, pr.witnesses, l.Goal, ref)
					default:
						if adapted := typematch.TryAdaptLemmaTypes(L.AsProp(), l.Goal); adapted != nil {
							claim = adapted
						}
						bareInstalls = append(bareInstalls, byBareInstall{premise: desc, law: L, installed: claim, leaf: l.Goal})
					}
				}
				stated := claim.AsProp().Conclusion()
				before := l.Goal
				switch {
				case l.Goal.AnyHyp(stated.AlphaEquals):
					// Already in the context — a sibling premise, or the
					// goal's own hypothesis. Nothing to install.
				case l.Goal.Conclusion().AlphaEquals(stated):
					// The premise IS the goal — Lean's `exact foo`. A proved
					// certificate closes it outright; an unproved one (a
					// session premise, certified later by auto-match) closes
					// on its own claim obligation.
					switch {
					case claim.Proved():
						if !l.runStep(CiteKnown(claim).(_KnownThmStep)) {
							panic(fmt.Sprintf("premise %s is the goal but its certificate does not close it", desc))
						}
					case !l.Goal.AlphaEquals(claim.AsProp()):
						// The leaf keeps hypotheses beside the statement:
						// the install's claim child is the obligation.
						if !step.installPremise(l, claim, true, desc) {
							panic(fmt.Sprintf("premise %s is the goal but does not close it", desc))
						}
						claims = append(claims, collectClaimObligations(l)...)
					case l != root:
						// The clear pass left exactly the premise's statement
						// — the usual session leaf, its context unnamed. An
						// install has nothing to add (its claim child would
						// be this leaf again), so the leaf IS the obligation.
						claims = append(claims, l)
					default:
						// The By's own goal is the premise's statement, with
						// nothing cleared: a composite cannot hand its goal
						// back as its obligation, and there is nothing else
						// for it to do.
						panic(fmt.Sprintf("premise %s is this goal's whole statement, so a By has nothing to add — "+
							"close the leaf by the cite of the entry that states it: Cite(%s), in a session the `lemma` "+
							"tactic at that key", desc, desc))
					}
				case len(pr.witnesses) == 0:
					// A BARE premise installs as the closer expects it: the
					// clause form (byPremise.clause) through the preserving
					// chain — whose strategies instantiate a law against the
					// goal, rewrite with an equation, or close outright — the
					// install every recorded key was minted on. The stated
					// form is the apply rung's head, not the resident. (A
					// witnessed premise taking its clause form is a plain
					// add below: the chain's rewrite strategy would fire on
					// a sibling's stated instance and leave nothing to
					// ground.)
					if !step.installPremise(l, claim, pr.exact, desc) {
						panic(fmt.Sprintf("premise %s neither is resident nor installs", desc))
					}
					claims = append(claims, collectClaimObligations(l)...)
				default:
					// A WITNESSED premise is a PLAIN ADD of its stated form —
					// the hyp-match strategy alone (tactic.LemmaAddHypTactic),
					// committed as the preserving step so the claim child is
					// the hyp-free `⊢ premise` the macro certifies — grounded
					// below at the tuple, its guards discharged from the
					// context. Nothing about it is decided by its shape.
					sg := tactic.LemmaAddHypTactic(claim)(l.Goal)
					if sg == nil || !l.commitStep(_LemmaPreserveTactic{lemma: claim}, sg) {
						panic(fmt.Sprintf("premise %s neither is resident nor installs", desc))
					}
					claims = append(claims, collectClaimObligations(l)...)
				}
				nl := byWorkingLeaf(root, claims)
				if nl == nil {
					// The premise was the goal. A witness tuple on it was
					// never applied: flag for the post-loop panic.
					if len(pr.witnesses) > 0 {
						unappliedWitnesses = desc
					}
					return
				}
				installedStatement[i] = stated
				if len(pr.witnesses) > 0 {
					// The resident may be the statement's ∀-closure over
					// its free variables (the general form the plain add
					// installs), so locate it as the hyp the install added.
					ni, err := locateInstalled(before, nl.Goal, claim)
					if err != nil {
						panic(fmt.Sprintf("cannot locate the installed premise %s to ground it: %v", desc, err))
					}
					// The witness tuple follows the STATED binder order
					// (witness_order.go) — the form the author named, never
					// the pack form a witnessed conjunction installs as.
					ref := pr.reference
					if ref == nil {
						ref = pr.install
					}
					wits := reorderWitnessesToInstall(ref, nl.Goal.Hyp(ni), pr.witnesses)
					// A SPEC-PARAMETRIC premise (stated over its family's
					// free variables — the reference form carries term
					// frees) is ∀-closed over those frees at injection, so
					// the installed prefix runs `∀jk.∀vsp.` ahead of the
					// stated binders the tuple grounds. Those closure
					// binders are schematic exactly because the cert's
					// frees are — and the consumer means them AT the
					// context's own same-named frees, so they are completed
					// by identity, loudly checked against the leaf. Gated
					// to explicit instances with a frees-carrying reference:
					// partial-tuple semantics on closed statements is
					// untouched. A reading under hypotheses keeps its free
					// components rigid and adds no closure prefix.
					if pr.exact && ref != nil && ref.NumHyps() == 0 && len(ref.AsProp().Conclusion().Frees(nil)) > 0 {
						wits = completeClosureWitnesses(nl.Goal, ni, wits, desc)
					}
					pre := nl.Goal
					if !nl.runStep(Specialize(InstHyp(ni, wits...))) {
						ws := make([]string, len(wits))
						for i, w := range wits {
							ws[i] = ext.PrintTerm(w)
						}
						panic(fmt.Sprintf("grounding the installed premise %s failed\n  installed hyp: %s\n  witness tuple: (%s)%s",
							desc, ext.PrintTerm(nl.Goal.Hyp(ni)), strings.Join(ws, ", "),
							witnessOrderNote(ref, nl.Goal.Hyp(ni), wits)))
					}
					// The instance's guards are discharged from the context
					// where it supplies them — Lean's `f x₀ ‹A›`.
					if gl := byWorkingLeaf(root, claims); gl != nil {
						if gi, gerr := newHypIndex(pre, gl.Goal); gerr == nil {
							dischargeGuards(gl, gl.Goal.Hyp(gi), true, step.door(), nil)
						}
					}
					if gl := byWorkingLeaf(root, claims); gl != nil {
						if gi, gerr := newHypIndex(pre, gl.Goal); gerr == nil {
							installedStatement[i] = gl.Goal.Hyp(gi)
						}
					}
				}
			}
		}()
	}
	if step.installs != nil {
		step.installs.closedAtLast = closedAt < 0 && byWorkingLeaf(root, claims) == nil
		step.installs.clause = clauseInstalled
		return nil
	}
	// Phase 3b — scaled premises (fact.go Scaled): beside each premise
	// that carries a coefficient, now installed and grounded, the
	// congruence of its equation under the carrier's multiplication is
	// added as a hypothesis, proved from the equation. Keyless: the
	// assertion's obligation closes from the kernel congruence. A
	// scaled equation already resident needs nothing.
	for i, pr := range step.premises {
		if pr.coefficient == nil {
			continue
		}
		l := byWorkingLeaf(root, claims)
		if l == nil {
			break
		}
		eq := installedStatement[i]
		if eq == nil {
			panic(fmt.Sprintf("By: premise %s is scaled but no installed equation was located for it\n  premises: %s",
				described[i], strings.Join(described, ", ")))
		}
		scaled, cert, ok := omega.ScaleEquation(l.Goal.Hyps(), pr.coefficient, eq, libraryReader(step.scope))
		if !ok {
			panic(fmt.Sprintf("By: premise %s is scaled by %s, but it is not an equation at a carrier the "+
				"arithmetic layers own (num, real, int, or a ring by a comm_ring / field fact resident or "+
				"installed) with a coefficient of that carrier's type\n  installed: %s",
				described[i], ext.PrintTerm(pr.coefficient), ext.PrintTerm(eq)))
		}
		if l.Goal.AnyHyp(scaled.AlphaEquals) {
			continue
		}
		if l.Goal.Conclusion().AlphaEquals(scaled) {
			// The scaled equation IS the goal: the congruence closes the
			// leaf outright, as an assertion of the goal is no progress.
			if !l.runStep(_KnownThmStep{strongerGoal: cert}) {
				panic(fmt.Sprintf("By: the congruence does not close the goal the scaled premise %s states", described[i]))
			}
			continue
		}
		if !l.runStep(_AssertStep{claim: prop.MakeProp(scaled)}) {
			panic(fmt.Sprintf("By: asserting the scaled premise %s failed", described[i]))
		}
		Assert(len(l.Children()) == 2)
		if !l.Children()[0].runStep(_KnownThmStep{strongerGoal: cert}) {
			panic(fmt.Sprintf("By: the congruence does not close the scaled premise %s", described[i]))
		}
	}
	// The unapplied-witnesses contract is unconditional: a witnessed
	// premise whose ∀-form install absorbs the goal is a mistake, not a
	// mode — the tuple would otherwise be unchecked text.
	if unappliedWitnesses != "" {
		panic(fmt.Sprintf("By: premise %s closed the goal at its ∀-form install, so its witness tuple was never applied — "+
			"unapplied witnesses are unchecked text (a wrong tuple would replay green). Cite the premise bare, "+
			"the same contract Cite enforces.", unappliedWitnesses))
	}
	if closedAt < 0 && byWorkingLeaf(root, claims) == nil {
		closedAt = len(step.premises) - 1
	}
	if closedAt >= 0 && closedAt < len(step.premises)-1 {
		var unused []string
		for _, i := range unmaterializedAfter(step.premises, closedAt) {
			unused = append(unused, described[i])
		}
		if len(unused) > 0 {
			panic(fmt.Sprintf("By: the goal closed at premise %s — the remaining premise(s) are unused, drop them:\n  %s",
				described[closedAt], strings.Join(unused, "\n  ")))
		}
	}

	if closedAt >= 0 {
		noteByClose(step.ctx, "premise")
	}
	// S5 at the refuter's own instantiations: the parts of the record
	// values the installed leaf spells join the premises (_RecordParts;
	// prover/tactic, RecordPartsTactic), so every rung of the ladder —
	// the bare probe and the bare retry included — closes with them in
	// hand; the conditioned rung adds the parts a strip exposes. Raw
	// keeps the leaf as the author spelled it.
	if closedAt < 0 && !step.arith && !step.settac && !step.chase && !(step.shape != nil && step.shape.raw) {
		if l := byWorkingLeaf(root, claims); l != nil {
			l.runStep(_RecordParts{})
		}
	}
	fanned := false
	if closedAt < 0 {
		// Phase 4 — declared shaping + terminal close, failure annotated
		// with the premise economy: the missing premise is usually among
		// the cleared hyps. p.NumHyps() is the clear pass's denominator —
		// with none cleared it is what separates "every hyp was named"
		// from "there was nothing to clear" (byNothingClearedAdvice).
		step.clauseInstalled = clauseInstalled
		step.clauseGuards = clauseGuards
		step.bareInstalls = bareInstalls
		step.goal = p
		fanned = step.terminalClose(root, &claims, described, droppedText, p.NumHyps())
	}

	if open := byWorkingLeaves(root, claims); len(open) > 0 {
		lines := make([]string, len(open))
		for i, lf := range open {
			lines[i] = prop.PrintProp(lf.Goal)
		}
		var hint string
		switch {
		case fanned:
			// The shaping fanned the residual and the single-leaf close
			// took one of them — the count at panic time can be back to
			// one, so the discriminator is the fan itself, observed at
			// close time.
			hint = "the shaping fanned the leaf into several — if each closes under the same " +
				"closer, add Broadcast to the premise list"
		case step.arith:
			hint = "the premises are down but the residual is outside the arith closer's " +
				"fragment (linear combinations of the premises over the monomials, a monomial's " +
				"sign from its factors' resident signs or from its being a square, numeral " +
				"evaluation): a product whose factors' signs are not resident needs its sign fact " +
				"as a premise (a product INSIDE a premise also needs its factors' signs at one " +
				"strictness — the sign rows fold `&0 < a` with `&0 < b` or `&0 ≤ a` with `&0 ≤ b`, " +
				"not one of each; the goal's own product reads either); dividing by a variable " +
				"needs a premise too, whether that is cancelling a positive factor (P·a ≤ P·b, " +
				"0 < P ⊢ a ≤ b) or reading a factor's sign off the product's; a residual that is " +
				"propositional over the premises' spelling is the CNF closer's, or By(Normalized, …)"
		default:
			hint = "the premises are down but the leaf did not close — the facts are present " +
				"in a different shape than the refuter meets them in: try By(Normalized, …)"
		}
		// The premise list beside the residual, as terminalClose's own
		// failure prints it: the residual alone cannot say whether a
		// premise was installed and went unused or was never installed,
		// and a witnessed law that took its clause form for want of a
		// guard says so on its line of the list.
		step.clauseGuards = clauseGuards
		described = step.withGuardAdvice(described, open[0], step.guardAdviser())
		panic(fmt.Sprintf("By: %s returned but %d leaf(s) are still open:\n  %s\nwith premises:\n  %s\n%s",
			step.closerName(), len(open), strings.Join(lines, "\n  "), strings.Join(described, "\n  "), hint))
	}

	// The composite closed: persist the attempt's live-searched
	// conditioning plans (no-op on replay, probes, and plan-applied
	// runs — see persistConditionPlans).
	step.cond().persistConditionPlans()

	// Assemble the composite SubGoals.
	if len(claims) == 0 {
		Assert(root.Proved())
		return tactic.MakeEmptySubGoals(p, root.provedThm)
	}
	childGoals := make([]Prop, len(claims))
	claimIndex := make(map[*GoalStackNode]int, len(claims))
	for i, c := range claims {
		childGoals[i] = c.Goal
		claimIndex[c] = i
	}
	rootFn := buildByReconstruct(root, claimIndex)
	rec := func(certs ...Prop) Prop { return rootFn(certs) }
	return tactic.MakeSubGoals(p, rec, childGoals...)
}

// buildByReconstruct composes the private tree's per-node tactic
// reconstructs into ONE pure statement-level function from the claim
// certificates to the root certificate. Purity is a framework contract,
// not a nicety: MakeSubGoals dry-runs the reconstruct at construction
// time with the BARE child goals (tactic.makeSubGoalsAt's IsStronger
// sanity assert), so the function must be re-invocable and must never
// mutate the tree it was derived from. Nodes the executor already
// closed contribute their certificate as a constant; claim leaves
// select their certificate by position; internal nodes chain their own
// SubGoals.Reconstruct — the same functions that certified every
// pre-composite By.
func buildByReconstruct(n *GoalStackNode, claimIndex map[*GoalStackNode]int) func([]Prop) Prop {
	if n.provedThm != nil {
		thm := n.provedThm
		return func([]Prop) Prop { return thm }
	}
	if idx, isClaim := claimIndex[n]; isClaim {
		return func(certs []Prop) Prop { return certs[idx] }
	}
	Assert(n.miniStep != nil) // an open non-claim leaf survived close-or-fail — engine invariant break
	childFns := make([]func([]Prop) Prop, len(n.children))
	for i, c := range n.children {
		childFns[i] = buildByReconstruct(c, claimIndex)
	}
	sub := n.subGoals
	return func(certs []Prop) Prop {
		thms := make([]Prop, len(childFns))
		for i, f := range childFns {
			thms[i] = f(certs)
		}
		return sub.Reconstruct(thms...)
	}
}

func (step _ByStep) closerName() string {
	switch {
	case step.arith:
		return "Arith"
	case step.settac:
		return "SetTacMembership"
	case step.chase:
		return "Chase"
	}
	return "CnfRefute"
}

// byLadderState is what the rungs of one applyLadder call tell each
// other, carried on the rung's context (byLadderStateKey): a refutation
// the rung ran — the closer's own, or one of the set driver's leaves —
// that ended at the refuter's budget records itself here (tryCNFRefute,
// noteCutOff), and the ladder reads it once a later rung closes.
type byLadderState struct {
	// cutOff describes the first refutation of the rung that ran to its
	// budget ("a refutation ran to its 5s budget"), empty when none did.
	cutOff string
	// prunable records that the rung's grounding kept a source a pruning
	// stage replaces (groundStage): the ladder then has the conditioned
	// rung to run once more, on the pruned leaf.
	prunable bool
	// planned records that a strict replay's keyless probe ended at a
	// leaf the store holds a plan for (conditionLeaf): the leaf's recorded
	// close is the conditioned rung's, and the ladder goes to that rung
	// without asking the bare probe first.
	planned bool
}

type byLadderStateKey struct{}

// ladderStateOf is the ladder state the context carries, nil outside a
// By ladder's rung.
func ladderStateOf(ctx context.Context) *byLadderState {
	st, _ := ctx.Value(byLadderStateKey{}).(*byLadderState)
	return st
}

// noteCutOff records that a refutation of the rung ran to budget and
// was cut off; the first one is kept.
func (s *byLadderState) noteCutOff(budget time.Duration) {
	if s.cutOff == "" {
		s.cutOff = fmt.Sprintf("a refutation ran to its %s budget", budget.Round(time.Millisecond))
	}
}

// noteRefuteCutOff is tryCNFRefute's report of a failed live search to
// the By ladder running it, whose next rung may close the leaf another
// way: the search ended at the refuter's budget — its context expired
// while the caller's is alive — not at the caller's deadline and not by
// exhausting its space. A budget of 0 is the replay sentinel, under
// which no live search ran.
func noteRefuteCutOff(parentCtx, proveCtx context.Context, budget time.Duration) {
	if budget <= 0 || proveCtx.Err() == nil || parentCtx.Err() != nil {
		return
	}
	if st := ladderStateOf(parentCtx); st != nil {
		st.noteCutOff(budget)
	}
}

// ranToBudget says whether a CNF terminal close that took elapsed spent
// its budget: a close that got within a tenth of the ceiling did not
// exhaust the space either, and the deadline check only lands between
// search steps — the observed overshoots (5084ms, 5236ms, 5006ms
// against 5s) sit on both sides of the budget. A budget <= 0 is the
// replay sentinel (no live search ran at all); a closer other than the
// refuter has no budget to compare against.
func ranToBudget(cnfCloser bool, budget, elapsed time.Duration) bool {
	return cnfCloser && budget > 0 && elapsed*10 >= budget*9
}

// reportBudgetPick says, where a refutation of the conditioned rung ran
// to its budget (cutOff, as noteCutOff describes it) and a later rung
// then closed the leaf, that the rows this close records are the
// budget's pick. After the bare retry they are a bare key and no plan,
// where the conditioned rung, given the time, records a conditioned key
// and a plan row. After the rung's run on the pruned leaf they are a plan
// that replaces, where the run on the whole leaf, given the time, records
// one that replaces nothing. Either way: two valid recordings of one
// step, both replaying, told apart by the machine's load alone.
// Reported through the recorder's audit sink and the call's own, so a
// reader comparing two recordings of the step, or two spellings by
// their rows, knows which difference is the load's.
func (step _ByStep) reportBudgetPick(cutOff string, pick byBudgetPick) {
	if cutOff == "" {
		return
	}
	finding := byBudgetPickFinding(step.auditLabel(), cutOff, pick)
	if step.env.ByAuditReport != nil {
		step.env.ByAuditReport(finding)
	}
	if step.leafReport != nil {
		step.leafReport(finding)
	}
}

// byBudgetPick is the rung that closed the leaf after a refutation of
// the conditioned rung was cut off (reportBudgetPick).
type byBudgetPick int

const (
	// byRetryPick is the bare retry.
	byRetryPick byBudgetPick = iota
	// byPrunedRunPick is the conditioned rung run on the pruned leaf.
	byPrunedRunPick
)

// byBudgetPickFinding is reportBudgetPick's text for the By labelled
// label whose conditioned rung's cut-off is described by cutOff and
// whose leaf the rung pick closed.
func byBudgetPickFinding(label, cutOff string, pick byBudgetPick) string {
	recorded := "the bare retry closed the leaf, so the rows recorded here are a bare key and no plan. " +
		"Given the time, the conditioned rung closes first and records a conditioned key and a plan row"
	if pick == byPrunedRunPick {
		recorded = "run again on the pruned leaf, the rung closed it, so the plan recorded here replaces. " +
			"Given the time, the rung closes on the whole leaf and records a plan that replaces nothing"
	}
	return fmt.Sprintf("%s: in the conditioned rung %s and was cut off; %s: both recordings replay, and which "+
		"one a run writes is the machine's load, not the spelling. A row difference at this step "+
		"between two recordings, or between two spellings measured by their rows, is the budget's "+
		"pick unless the step was measured on an unloaded machine.", label, cutOff, recorded)
}

// byBudgetAdvice reports a terminal close that spent its whole search
// budget, which dominates every other reading of the failure: a search
// that was CUT OFF establishes nothing about the premise list and
// nothing about the shape. Empty string = not a budget case, fall
// through to the premise/shape advice.
//
// The recovered panic carries no timeout signal to key on —
// _CNFRefute.apply returns nil identically for "deadline expired" and
// "search space exhausted" (tryCNFRefute's r.Prove just stops when
// ctx.Err() != nil), and the close then panics with a bare "ministep
// failed". So this is a MEASUREMENT, not an inference: wall clock
// around the failing close, against the budget that call ran under.
// The wording says what was measured rather than asserting a timeout,
// because at the threshold the two are not separable.
//
// CNF closer only: the budget is the CNF refuter's, so comparing an
// arith/settac close against it would be meaningless. A
// budget <= 0 is the replay sentinel (no live search ran at all).
func byBudgetAdvice(cnfCloser bool, budget, elapsed time.Duration) string {
	if !ranToBudget(cnfCloser, budget, elapsed) {
		return ""
	}
	return "\nthe close " + byBudgetRun(budget, elapsed) + " — at or over the ceiling, so the " +
		fmt.Sprintf(
			"refuter was CUT OFF rather than run to exhaustion. That is no evidence about the premise "+
				"list AND no evidence about the shape: an unfinished search establishes neither, so do not "+
				"reshape on the strength of this failure. Make the search smaller instead — cut the premise "+
				"list to what the step actually needs (every extra premise widens the clause set), or split "+
				"the step so the refuter gets two small searches instead of one big one (an intermediate "+
				"a.Have/assert). Raising the budget only confirms the proof exists; a step that needs the "+
				"whole ceiling pays it again on every replay.")
}

// byBudgetRun is the measurement a cut-off is described by: "ran 5s
// against a 5s search budget".
func byBudgetRun(budget, elapsed time.Duration) string {
	return fmt.Sprintf("ran %s against a %s search budget", elapsed.Round(time.Millisecond), budget.Round(time.Millisecond))
}

// byNothingClearedAdvice is the advice for a terminal-close failure
// where the clear pass dropped NOTHING (phase 2 found no unnamed
// ambient hyp). leafHyps is the ambient hyp count of the leaf the clear
// pass ran on — the only thing that decides whether "nothing cleared"
// is evidence at all.
//
// The clear pass sees RESIDENT hyps and nothing else, so it can never
// speak for a lemma premise: a lemma was never resident, so dropping
// one from the list clears nothing and fails here identically. On a
// hyp-free leaf that is total — phase 1 rejects a resident premise that
// names no hyp, so leafHyps == 0 means EVERY premise is a lemma and the
// clear pass is vacuous. The message therefore does not claim the
// premise list is complete there, where it has no evidence, and offers
// the missing premise first.
func byNothingClearedAdvice(leafHyps int) string {
	const shapeTail = "Shaping fixes the shape-only cases: By(Normalized, …), or — when one " +
		"compound term stands in several of the premises at once — By(DenotedAs(name, term), …). " +
		"Under the refuter a GROUND equation premise between two spellings of one term (x*z " +
		"vs z*x) is consumed by its congruence demodulation and needs no hand-Rw; only a ∀-quantified " +
		"equation still meets it as clauses — ground it (or let the conditioning stage ground " +
		"it) before expecting it to identify spellings. Under arith two applications of one " +
		"head meet where their arguments decide equal under the premises (f(n - 1 - i) and " +
		"f(q + 1) beside i + 1 < n and q = n - 1 - (i + 1)), an equation, a predicate and a " +
		"membership alike; a comparison of two such atoms at a number carrier (g(n + 1 + 1) ≤ " +
		"g(n + 2)) is the layers' formula and is not read by its arguments — rewrite it first."
	if leafHyps == 0 {
		return "\nthis leaf has no ambient hyps, so the clear pass had nothing to work on: it is no " +
			"evidence either way, and nothing here says the premise list is complete. Every premise " +
			"of a hyp-free leaf is a LEMMA, and a lemma missing from the list clears nothing — it " +
			"fails exactly like this. Check the list for a MISSING premise first; a wrong shape is " +
			"the other cause. " + shapeTail
	}
	return "\nevery ambient hyp of this leaf is named in the premise list, so no RESIDENT fact is " +
		"missing. That says nothing about LEMMA premises — those were never resident, so a missing " +
		"one clears nothing and fails exactly like this. If the list is complete, the facts are all " +
		"present but not in the shape the closer meets them in. " + shapeTail
}

// bySetVocabularyNote is the note a failed CNF close carries when the
// leaf it failed on spells set vocabulary by name. The refuter unfolds
// no definition, so `s ⊆ t` or `x ∈ s ∪ t` reaches it as an atom over
// opaque sets and a leaf true by those definitions alone does not
// close; the set driver unfolds its vocabulary to memberships first.
// The two names it does not count are the ones every set leaf spells
// and the refuter reads as they stand: membership itself, and the
// comprehension's inner marker. Empty for a leaf that spells none.
func bySetVocabularyNote(leaf *GoalStackNode) string {
	if leaf == nil {
		return ""
	}
	var spelled []string
	for _, name := range StandardSetVocabulary() {
		if name == "set_member" || name == "comprehension_spec" {
			continue
		}
		if prop.ContainsConstName(leaf.Goal, core.TermName(name)) {
			spelled = append(spelled, name)
		}
	}
	if len(spelled) == 0 {
		return ""
	}
	return fmt.Sprintf("\nthis leaf spells set vocabulary by name (%s), and the refuter unfolds no definition: it meets "+
		"those sets as opaque atoms. The set driver unfolds its vocabulary to memberships before it closes — "+
		"BySets(…) over the same premises (in a session, the same `by` with settac:true).",
		strings.Join(spelled, ", "))
}

// bySetEquationNote is the note a failed set-driver close carries when
// the leaf it failed on holds an equation between sets. The driver reads
// every such equation pointwise, as memberships (prover/tactic,
// set_tac_membership.go, phase 0), and what it read is no longer an
// equation: one set does not replace the other under a constant the
// driver keeps opaque (`card(s)`), and an equation inside a set-builder's
// predicate becomes a quantified formula under the builder's own. The
// refuter keeps an equation an equation, so the same premises may close
// under By. Empty for a leaf that holds none.
func bySetEquationNote(leaf *GoalStackNode) string {
	if leaf == nil {
		return ""
	}
	isSet := func(t core.Term) bool {
		flat := ext.MatchesFun(t.Type())
		return len(flat) >= 2 && flat[len(flat)-1].Equals(core.TypeBool())
	}
	var holds func(t core.Term) bool
	holds = func(t core.Term) bool {
		if l, _, ok := ext.MatchesEQ(t); ok && isSet(l) {
			return true
		}
		if app, ok := t.AsAppliedTerm(); ok {
			return holds(app.Fun()) || holds(app.Arg())
		}
		if abs, ok := t.AsAbsTerm(); ok {
			return holds(abs.Body())
		}
		return false
	}
	found := holds(leaf.Goal.Conclusion())
	for i := 0; !found && i < leaf.Goal.NumHyps(); i++ {
		found = holds(leaf.Goal.Hyp(i))
	}
	if !found {
		return ""
	}
	return "\nthis leaf holds an equation between sets, and the set driver reads every one pointwise, as " +
		"memberships: what it read is no longer an equation, so one set does not replace the other under a " +
		"constant the driver keeps opaque (card(s)), and an equation inside a set-builder's predicate becomes " +
		"a quantified formula under the builder's own. The refuter keeps an equation an equation — By(…) over " +
		"the same premises (in a session, the same `by` without settac)."
}

// terminalClose runs the declared shaping and the terminal closer over
// the private tree, reproducing the macro's phase-4 semantics verbatim:
// every shaping step is optional, Broadcast fans the {shape, close}
// pair per leaf, and the failure panic decides the CNF-MISS split
// (record the key vs spell By(Normalized, …)) for the author.
//
// Returns whether the shaping FANNED the residual (more than one
// working leaf at close time) — the still-open panic's discriminator
// for its Broadcast hint. Observed at close time rather than at panic
// time because the single-leaf close may take one fanned leaf, leaving
// a count of one behind.
func (step _ByStep) terminalClose(root *GoalStackNode, claims *[]*GoalStackNode, described, droppedText []string, leafHyps int) (fanned bool) {
	shape := step.shape
	closerName := step.closerName()
	// Wall clock of the FAILING close (closeOne re-times per call, so a
	// broadcast loop reports the leaf that actually panicked). Read by
	// byBudgetAdvice — see there for why the panic itself cannot say.
	var closeElapsed time.Duration
	// The set driver's residual leaves — what its membership rewrite left
	// that did not close — read by the failure below: a closer's failure
	// prints the goal it stopped on, as the refuter's does.
	var setResiduals []Prop
	defer func() {
		// A fault goes up as it is (rungFailure): folded into the message
		// below it would read as this rung's failure, and a later rung
		// would close over it.
		if r := rungFailure(recover()); r != nil {
			if cut, ok := r.(byCutOff); ok {
				// A cut-off close failed for want of time: the premise
				// and shape readings below would misattribute it.
				panic(cut)
			}
			if step.failureUnread {
				// No one reads the message below, and its notes walk the
				// proof tree. The cause goes up as it is, so rungFailure
				// still sees a breach raised inside the close.
				panic(r)
			}
			advice := step.guardAdviser()
			described = step.withGuardAdvice(described, byWorkingLeaf(root, *claims), advice)
			msg := fmt.Sprintf("By: %s failed with premises:\n  %s",
				closerName, strings.Join(described, "\n  "))
			if len(setResiduals) > 0 {
				msg += "\nthe set driver's residual leaves, after its membership rewrite, that did not close:"
				for _, res := range setResiduals {
					msg += "\n  " + prop.PrintProp(res)
				}
			}
			msg += byUnsuppliedGuardsNote(step.spine, byWorkingLeaf(root, *claims), advice)
			msg += step.listOrderNote(described)
			msg += step.installReadingNote()
			// Read off the leaf before the MISS branch below runs its
			// Basic() check on it.
			setNote := ""
			switch {
			case closerName == "CnfRefute":
				setNote = bySetVocabularyNote(byWorkingLeaf(root, *claims))
			case step.settac:
				setNote = bySetEquationNote(byWorkingLeaf(root, *claims))
			}
			// The stage names what it tried: the failing close ran
			// on the CONDITIONED sequent, so the reader must see the
			// grounding actions to interpret the failure.
			if step.s4 != nil && len(step.s4.describe) > 0 {
				msg += "\nconditioning applied first:\n  " + strings.Join(step.s4.describe, "\n  ") +
					"\n  (a grounding is the stage's own guess at a witness, not a fact the argument supplied: one at a " +
					"witness the argument does not want is the guess missing — pin the lemma's binders with " +
					"term_specialize / At(…) rather than leaving the ∀-premise to the stage)"
			}
			if strings.Contains(fmt.Sprint(r), "CNF cache MISS") {
				// The Basic() oracle runs on the OUTER working leaf. For the
				// CNF closer that IS the refuted sequent; the settac closer
				// refutes residuals it manufactures internally, so there the
				// oracle's answer and the goal printed in the MISS refer to
				// DIFFERENT sequents — say so, or the reader pairs them.
				basicNote := ""
				if step.settac {
					basicNote = "\n(settac closer: the Basic() check ran on the By leaf as the set " +
						"driver received it; the goal printed in the MISS above is the driver's " +
						"INTERNAL residual — a different sequent.)"
				}
				if byClosesUnderBasic(step.ctx, root, *claims) {
					msg += "\nthis leaf closes under Basic(), so the refuter was never wanted and " +
						"NO key should be recorded: the premise list is already complete and the " +
						"facts simply do not meet the closer in clause form. Spell it " +
						"By(Normalized, …) — that runs Basic() between the installs and the close." +
						basicNote
				} else {
					msg += "\nthe cause is a CNF cache MISS: the refuter reached this leaf and found no " +
						"recorded key. Two causes produce exactly this — the key is genuinely unrecorded " +
						"(normal for a member's first record), OR a premise is a WRONG GROUND INSTANCE " +
						"(a swapped witness tuple builds a different fact and misses the same way). " +
						"Compare the installed instances in the premise list above against what you " +
						"intended BEFORE recording — recording a wrong instance mints a key for a proof " +
						"the member does not claim, and the panic then stops. If the instances are right, " +
						"record the key (XUGO_RECORD_FAMILY_CNF=<family>.<Member> go test -count=1 " +
						"-run TestRecordFamilyCNF ./library/integrity/gates/), then re-run the replay. " +
						"(Checked: this leaf does NOT close under Basic(), so By(Normalized, …) is " +
						"not the fix.) The two causes are not the only readings. Between them sits the SHAPE: " +
						"a compound term standing in several of the premises at once wants " +
						"By(DenotedAs(name, term), …), and a ∀-quantified equation premise meets the closer " +
						"as clauses until it is grounded (At(…)). A shaping can RELOCATE the key instead of " +
						"removing it: after adding one, replay again — a MISS at a different key is the same " +
						"refutation moved. To see which keys a spelling would add without writing any, run " +
						"the recorder with XUGO_RECORD_CNF_DRY_RUN=1." + basicNote
				}
			} else if adv := byBudgetAdvice(closerName == "CnfRefute",
				step.env.effectiveCnfTimeout(step.ctx), closeElapsed); adv != "" {
				// FIRST among the non-cache-MISS readings: a cut-off
				// search dominates both the premise and the shape story.
				// (Disjoint from the MISS branch above, which is strict
				// replay — that pre-cancels the prove ctx, so no live
				// search runs and no budget is spent.)
				msg += adv
			} else if len(droppedText) > 0 {
				msg += "\ncleared ambient hyps (a missing premise is usually in here):\n  " +
					strings.Join(droppedText, "\n  ")
			} else if shape == nil {
				msg += byNothingClearedAdvice(leafHyps)
			}
			msg += setNote
			panic(fmt.Sprintf("%s\ncause: %v", msg, r))
		}
	}()
	// Every shaping step is OPTIONAL by design: the install path may
	// already have produced the shape, and a shaping step that panics
	// for lack of work would read as a premise error. A fault inside
	// one is no lack of work, and is raised (rungFailure).
	try := func(st _Step) {
		leaf := byWorkingLeaf(root, *claims)
		if leaf == nil {
			return
		}
		defer func() { rungFailure(recover()) }()
		leaf.runStep(st)
	}
	// shapeBasic is the shaping stage's Basic(), optional as every shaping
	// step is, under the step's context: its fixpoint is a search over the
	// leaf's case splits and equations, and one the deadline ends is cut
	// off rather than read as a Basic() that had nothing to do.
	shapeBasic := func() {
		leaf := byWorkingLeaf(root, *claims)
		if leaf == nil {
			return
		}
		cut := false
		func() {
			defer func() { rungFailure(recover()) }()
			_, cut = leaf.runBasicUntil(step.ctx)
		}()
		if cut {
			panic(byCutOff{closer: closerName, stage: "inside the shaping stage's Basic()", cause: step.ctx.Err()})
		}
	}
	if step.chase {
		try(_ChaseRecordsStep{})
	}
	if shape != nil && shape.pre {
		before := len(byWorkingLeaves(root, *claims))
		shapeBasic()
		if len(byWorkingLeaves(root, *claims)) < before {
			noteByClose(step.ctx, "shaping")
		}
	}
	explicitDenoted := false
	denoteSawLeaf := false
	denoteStage := func() {
		if shape == nil {
			return
		}
		if shape.denoteTerm != nil {
			leaf := byWorkingLeaf(root, *claims)
			if leaf != nil {
				denoteSawLeaf = true
			}
			if leaf != nil && leaf.runStep(denoteTermOptional(
				shape.denoteName, shape.denoteTerm, shape.denoteHilbert)) {
				explicitDenoted = true
			}
		}
		if shape.denote > 0 {
			try(Denote(shape.denote))
		}
		if shape.hilbert {
			try(_AutoDenote{hilbert: true})
		}
		shapeBasic()
	}
	// mustRun is the terminal closer, close-or-fail: a closer that leaves
	// its leaf open fails naming the leaf it was handed, the conditioned
	// sequent the recover above cannot otherwise show.
	mustRun := func(leaf *GoalStackNode, st _Step) {
		if !leaf.runStep(st) {
			panic(fmt.Sprintf("the closer %v did not close the leaf\n  on leaf goal: %s", st, prop.PrintProp(leaf.Goal)))
		}
	}
	// The conditioning stage: the author names the facts; the executor puts
	// them in the form the closer digests. The goal strip fixes the
	// residual goal's ∀-binders and moves antecedents into hypotheses; the
	// premise split breaks conjunctive hyps into their conjuncts (∀-prefix
	// distributed), the antecedents the strip just installed included; S4
	// grounds the wide ∀-hyps at the leaf's own ground terms (the one
	// searchy stage — its search output persists as PLANS in the CNF store,
	// so every replay path applies the recorded plans with zero search).
	// The strip, the split and the denotation are pure functions of the
	// leaf, recorded nowhere: replay re-runs them inside the same
	// composite. Raw suppresses the stage (the author's hand wins).
	// condition reports whether the stage closed the leaf it conditioned
	// (the apply rung did): the next working leaf is then another conjunct,
	// which has not been conditioned.
	condition := func() (closed bool) {
		if named := step.namedPremises(); len(named) > 0 {
			// A premise pinned by name (Where) exists only for the apply
			// rung, which the conditioning stage runs: a bare attempt
			// (the ladder's probe and retry rungs, the author's Raw) or
			// the arith closer would run the closer on a leaf that never
			// saw the premise — and might close it by search around the
			// author's instruction. Refuse instead; the ladder's
			// conditioned rung is where a named premise fires.
			switch {
			case step.arith:
				panic(fmt.Sprintf("By: premise %s is pinned by name (Where), which the apply rung serves — "+
					"the arith closer does not run the rung; use the CNF closer (plain By)", named[0].description()))
			case step.shape != nil && step.shape.raw:
				panic(fmt.Sprintf("By: premise %s is pinned by name (Where), which the apply rung serves — "+
					"Raw suppresses the conditioning stage the rung runs in", named[0].description()))
			case !step.condition:
				panic(fmt.Sprintf("By: premise %s is pinned by name (Where) — a bare attempt runs no apply rung",
					named[0].description()))
			}
		}
		if !step.condition {
			return false
		}
		// The closer applicability matrix: S4 and the apply
		// rung serve every closer — a wide law grounded at the leaf's
		// terms, or applied to the goal with its antecedents resident,
		// is what the arithmetic decider cannot do for itself (it
		// instantiates nothing). A grounding adds the instances and
		// removes nothing; the ladder's run on the pruned leaf is the one
		// that replaces. Denotation serves CnfRefute only, and an explicit
		// denote in the shape suppresses it (the author's hand wins). The
		// stage itself is the door-shared conditioner (step_condition.go).
		c := step.cond()
		c.claims = claims
		c.heads = step.applyHeads()
		c.conditionLeaf(root, conditionOpts{
			// The keyless probe (probeKeyless) runs the stage without
			// S4, so it applies no plan and records none.
			// The chase reads its ∀-facts itself — a square, an
			// injectivity — and instantiates them at the elements it
			// introduces, so no grounding stage runs ahead of it.
			ground: !step.keyless && !step.chase,
			// The arithmetic closer reads its facts wide: it is never
			// handed the pruned leaf, and takes no plan that replaces.
			prune: step.prune,
			wide:  step.arith,
			denote: !(step.arith || step.settac || step.chase ||
				(shape != nil && (shape.denote > 0 || shape.denoteTerm != nil || shape.hilbert))),
			recordParts:     !(step.arith || step.settac || step.chase),
			readMemberships: !(step.settac || step.chase),
			readRecords:     !step.chase,
			applyClose:      true,
			// A premise pinned by name is applied to ONE goal, the one
			// the author wrote: its target is not split.
			splitConj: len(step.namedPremises()) == 0,
		})
		if c.cut != "" {
			panic(byCutOff{closer: closerName, stage: c.cut, cause: step.ctx.Err()})
		}
		// A premise pinned by name is an instruction to APPLY it; a
		// leaf the rung did not close with it fails here, with the
		// rung's nearest miss, rather than reaching a closer that never
		// saw the premise.
		if named := step.namedPremises(); len(named) > 0 && !c.closed {
			if leaf := byWorkingLeaf(root, *claims); leaf != nil {
				descs := make([]string, len(named))
				for i, pr := range named {
					descs[i] = pr.description()
				}
				miss := c.namedMiss
				if miss == "" {
					miss = "the conclusion of the stated form does not match the goal"
				}
				panic(fmt.Sprintf("By: the premise pinned by name did not apply — %s\n  premise: %s\n  leaf: %s",
					miss, strings.Join(descs, "\n  premise: "), prop.PrintProp(leaf.Goal)))
			}
		}
		if c.closed {
			noteByClose(step.ctx, "apply/conditioning")
		}
		return c.closed
	}
	closeOne := func(leaf *GoalStackNode) {
		// Deferred so the panicking path records too — the recover above
		// reads this to tell a cut-off search from an exhausted one.
		t0 := time.Now()
		defer func() { closeElapsed = time.Since(t0) }()
		switch {
		case step.arith:
			// Arith, then TrivialSimplify on what it leaves — the
			// scoped Arith first (the private nodes carry the proof
			// scope, so the omega gate applies), then the trivial mop-up
			// on its residual. The mop-up stages are OPTIONAL: a residual
			// they decline falls through to the still-open diagnostic,
			// which prints the leaf — a better failure than a bare
			// "ministep failed" with no goal on it.
			mopUp := func() {
				if res := byWorkingLeaf(root, *claims); res != nil {
					res.runStep(_TrivialSimplify{})
				}
				// Keyless propositional finisher: a residual that is true
				// by connective order alone (∀-prefix or ∧/∨ commutation
				// between an installed premise and the goal's spelling)
				// has no arithmetic left and normalizes to ⊤ — exactly
				// what TrivialNormalized closes, cleanly declining on
				// anything contentful. Only reachable on paths that
				// otherwise panic, so no recorded member's replay passes
				// through it.
				if res := byWorkingLeaf(root, *claims); res != nil {
					res.runStep(_TrivialNormalizedStep{})
				}
			}
			// A rewrite the mop-up undoes — the leaf after it is the leaf
			// the firing was handed — made no progress, and fired again
			// it would take every round from the firings behind it. The
			// decider reads a resident `n = 2 * m` variable to term and
			// the mop-up reads it term to variable, so `2 ∣ n` goes to
			// `2 ∣ (2 * m)` and back; and a law that grows a term, an
			// absolute value pushed through a product, rewrites the
			// conclusion, which the mop-up folds back by the bridge
			// equation the firing left beside it. The rounds pass such a
			// rewrite over, a hypothesis's or the conclusion's, and the
			// firing goes to the next hypothesis or to a deferred drop.
			// The conclusion is still decided every round: a decision is
			// another rewrite than the one passed over.
			rounds := &_ArithRounds{}
			settle := func(handed Prop) (more bool) {
				mopUp()
				after := byWorkingLeaf(root, *claims)
				if after == nil || !after.Goal.AlphaEquals(handed) {
					return true
				}
				rounds.passOver = append(rounds.passOver, rounds.fired)
				return true
			}
			if !step.arithFiring(leaf, rounds) {
				panic(fmt.Sprintf("the closer %v did not close the leaf\n  on leaf goal: %s", _Arith{}, prop.PrintProp(leaf.Goal)))
			}
			more := settle(leaf.Goal)
			// A leaf still open here gets further Arith rounds, to a
			// bounded fixpoint: one Arith firing is either the conclusion's
			// decision or ONE hypothesis rewrite (a ground guard folded out
			// of a Horn premise, an implication resolved against the other
			// facts), and a firing spent on a hypothesis leaves a residual
			// the next firing decides. Without the rounds the closer
			// stopped after the hypothesis rewrite with the residual open —
			// the "guard vanished, leaf still open" report. The rounds
			// start only after the single-firing path has failed, so a
			// leaf that closed before closes the same way at the same
			// cost; the bound caps the spend on a leaf that will not
			// close, and the rounds end before it when no firing is left.
			for i := 0; more && i < arithCloseFixpointBound; i++ {
				res := byWorkingLeaf(root, *claims)
				if res == nil {
					break
				}
				step.stopIfCut(fmt.Sprintf("before Arith firing %d on one leaf", i+2))
				if !step.arithFiring(res, rounds) {
					break
				}
				more = settle(res.Goal)
			}
			noteByClose(step.ctx, "arith")
		case step.chase:
			// The diagram chase at the author's depth, close-or-fail: a
			// leaf it does not close panics with the chase's own report.
			mustRun(leaf, _ChaseStep{depth: step.chaseDepth})
			noteByClose(step.ctx, "chase")
		case step.settac:
			// The membership-mode set driver, close-or-fail, with the
			// standard vocabulary (not a per-call choice — see BySets).
			// Its internal refutes hit the same CNF cache a bare set_tac
			// step's would, under keys the record-time run wrote.
			st := newSetTacStep(StandardSetVocabulary(), SetTacMode_SET_TAC_MEMBERSHIP).(_SetTacStep)
			st.env, st.ctx = step.env, step.ctx
			// The By ladder already owns conditioning and rung
			// structure for this attempt; the driver must run bare or
			// the raw door's own ladder would double both.
			st.bare = true
			st.residuals = &setResiduals
			mustRun(leaf, st)
			noteByClose(step.ctx, "settac")
		default:
			// The audit's capture happens INSIDE the closer, at the point
			// resolution is reached (tryCNFRefute) — not here, where a
			// leaf the prelude closes keylessly would be captured too
			// and Probe A would prescribe a marker that saves nothing.
			ctx := step.ctx
			if step.audit != nil {
				ctx = withByAuditState(ctx, step.audit)
			}
			mustRun(leaf, _CNFRefute{env: step.env, ctx: ctx, missReadByCaller: true})
		}
	}
	// handed is the leaf each round handed the closer. The rounds are a
	// function of that leaf — the conditioning, the closer and the mop-up
	// read nothing else — so a round handing over a leaf an earlier round
	// handed over is an orbit, not progress: measured on a leaf whose
	// conditioning grounded the instances the mop-up stripped again, round
	// after round to the budget, at seconds a round. The refusal is the
	// budget's, with the leaf still open for the report that follows.
	var handed []Prop
	hand := func(name string, round int, leaf *GoalStackNode) {
		if earlier := slices.IndexFunc(handed, leaf.Goal.AlphaEquals); earlier >= 0 {
			panic(fmt.Sprintf("By: %s's round %d hands its closer the leaf round %d did — "+
				"the rounds cycle and no further round would make progress — %d leaf(s) still open",
				name, round, earlier+1, len(byWorkingLeaves(root, *claims))))
		}
		handed = append(handed, leaf.Goal)
	}
	if step.broadcast {
		// The fan has no bound by construction: every round conditions
		// the next working leaf, and the shaping may fan THAT leaf
		// again. A shaping that re-fans what it conditions never
		// converges — measured on an induction base leaf carrying a
		// definition's ∀-clause under Normalized + arith, where the
		// loop ran for eleven CPU-minutes with the goal tree deepening
		// under it and the session locked. So the rounds are counted,
		// and a fan still open past the budget is refused with the
		// leaf it was on, the way a cut-off refuter is.
		rounds := 0
		for {
			leaf := byWorkingLeaf(root, *claims)
			if leaf == nil {
				break
			}
			rounds++
			if rounds > 1 {
				step.stopIfCut(fmt.Sprintf("before round %d over the fan (%d leaf(s) still open)",
					rounds, len(byWorkingLeaves(root, *claims))))
			}
			if rounds > byBroadcastRoundBudget {
				panic(fmt.Sprintf("By: Broadcast %s ran %d rounds and the fan has not converged — "+
					"%d leaf(s) still open. The shaping re-fans each leaf it conditions (a resident "+
					"∀-clause under Normalized is the measured cause), so more rounds would not finish: "+
					"drop Broadcast, or Simp the goal down to what the closer decides before the close. "+
					"The round it stopped on:\n  %s",
					closerName, rounds-1, len(byWorkingLeaves(root, *claims)), prop.PrintProp(leaf.Goal)))
			}
			if condition() {
				continue // closed on the rung: the next leaf has its own round
			}
			beforeShape := byWorkingLeaves(root, *claims)
			denoteStage()
			if anyClosedDescendant(beforeShape) {
				noteByClose(step.ctx, "shaping")
			}
			leaf = byWorkingLeaf(root, *claims)
			if leaf == nil {
				noteByClose(step.ctx, "shaping")
				break // the preamble itself discharged the last leaf
			}
			hand("Broadcast "+closerName, rounds, leaf)
			closeOne(leaf)
			if byWorkingLeaf(root, *claims) == leaf {
				panic(fmt.Sprintf("By: Broadcast %s left its leaf open:\n  %s",
					closerName, prop.PrintProp(leaf.Goal)))
			}
		}
	} else {
		// The conditioning stage splits a conjunctive goal into its
		// conjuncts, and each is conditioned, shaped and closed in its
		// turn — a round a leaf, the rounds the conjuncts alone. A fan
		// the SHAPING makes is the author's to declare (Broadcast): the
		// close takes one of its leaves and the rest stay open for the
		// still-open panic to name.
		rounds := 0
		for {
			if byWorkingLeaf(root, *claims) == nil {
				break
			}
			rounds++
			if rounds > 1 {
				step.stopIfCut(fmt.Sprintf("before round %d over the conjuncts of its goal (%d leaf(s) still open)",
					rounds, len(byWorkingLeaves(root, *claims))))
			}
			if rounds > byBroadcastRoundBudget {
				panic(fmt.Sprintf("By: %s ran %d rounds over the conjuncts of its goal and has not finished — "+
					"%d leaf(s) still open", closerName, rounds-1, len(byWorkingLeaves(root, *claims))))
			}
			if condition() {
				continue // closed on the rung: the next leaf is the next conjunct
			}
			conditioned := len(byWorkingLeaves(root, *claims))
			denoteStage()
			switch shaped := len(byWorkingLeaves(root, *claims)); {
			case shaped < conditioned:
				noteByClose(step.ctx, "shaping")
				continue // the shaping closed it
			case shaped > conditioned:
				fanned = true
			}
			leaf := byWorkingLeaf(root, *claims)
			if leaf == nil {
				break
			}
			hand(closerName, rounds, leaf)
			closeOne(leaf)
			after := byWorkingLeaf(root, *claims)
			// The closer left its leaf, or a leaf spelled as its leaf
			// was: no round made progress, and the still-open report
			// below names the leaf.
			if fanned || after == leaf || (after != nil && after.Goal.AlphaEquals(leaf.Goal)) {
				break
			}
		}
	}
	// A leaf closed before the shaping could run (the apply rung, or a
	// guard discharge that left the goal resident) made the shaping
	// unnecessary, not stale: only a leaf it was tried on can report it.
	if shape != nil && shape.denoteTerm != nil && !explicitDenoted && denoteSawLeaf {
		panic(fmt.Sprintf("By: the explicit denote shaping applied to no leaf — either "+
			"the term is not in this argument (it drifted, or the shaping is stale), "+
			"or %q was already free in every leaf:\n  %s",
			shape.denoteName, ext.PrintTerm(shape.denoteTerm)))
	}
	return fanned
}

// listOrderNote is a failing close's reading of the order of its
// premise list. A premise is installed into the leaf as the premises
// listed before it have built it, and two installs read that leaf: a
// bare law goes through the preserving chain, which rewrites the goal by
// the law, or closes where its rewrite meets a hypothesis; a witnessed
// premise takes its stated form where the leaf supplies its guards and
// the closer's clause form where it does not. So a law listed ahead of
// the instance its rewrite meets, or an instance listed ahead of the
// fact that supplies its guard, installs as a clause the closer may not
// bring together with the rest.
//
// The note re-runs the installs with one premise moved to the end of the
// list (an install probe, _ByStep.installs: no shaping, no close) and
// names the first premise for which that changes the outcome: a bare law
// whose install then closes the goal, or a witnessed premise that took
// its clause form and then takes its stated form. Each is a fact about
// the installs, checked; the second does not say the close then
// succeeds.
func (step _ByStep) listOrderNote(described []string) string {
	if step.goal == nil {
		return ""
	}
	// The last premise an install materializes: a premise at or behind it
	// has nothing listed after it to read.
	last := -1
	for i, pr := range step.premises {
		if !pr.kept && !(pr.resident && len(pr.witnesses) == 0 && len(pr.named) == 0) {
			last = i
		}
	}
	for i, pr := range step.premises {
		if i >= last || pr.derivedCert != nil || pr.resident || len(pr.named) > 0 {
			continue
		}
		bare := len(pr.witnesses) == 0
		if !bare && !(i < len(step.clauseInstalled) && step.clauseInstalled[i]) {
			continue
		}
		moved := make([]byPremise, 0, len(step.premises))
		moved = append(moved, step.premises[:i]...)
		moved = append(moved, step.premises[i+1:]...)
		moved = append(moved, pr)
		probe := step
		probe.premises = moved
		probe.installs = &byInstallProbe{}
		probe.failureUnread = true
		probe.closeTrace = nil
		func() {
			defer func() { rungFailure(recover()) }()
			probe.applyInner(step.goal)
		}()
		at := len(moved) - 1
		switch {
		case bare && probe.installs.closedAtLast:
			return fmt.Sprintf("\nthe order of the premise list (checked): premise %s, a bare law, closes this goal at its install "+
				"when it is listed last. A bare law acts on the leaf as the premises listed before it have built it — it "+
				"rewrites the goal by the law, or closes where its rewrite meets a hypothesis — and here it is listed ahead "+
				"of the premise that states what its rewrite meets. Move it to the end of the list.",
				clipRunes(described[i], 120))
		case !bare && at < len(probe.installs.clause) && !probe.installs.clause[at]:
			return fmt.Sprintf("\nthe order of the premise list (checked): premise %s took its clause form because the leaf did "+
				"not supply its guard where it is listed; listed last, the premises before it supply the guard and it "+
				"installs in its stated form. A premise reads the leaf as the premises listed before it have built it: "+
				"list it after the fact that supplies its guard.",
				clipRunes(firstLine(described[i]), 120))
		}
	}
	return ""
}

// firstLine is s up to its first line break.
func firstLine(s string) string {
	if i := strings.IndexByte(s, '\n'); i >= 0 {
		return s[:i]
	}
	return s
}

// byUnsuppliedGuardsNote lists, for a failing close, the guards the
// leaf's premise instances still carry — an implication among the
// hypotheses whose antecedent the context supplies neither as written
// nor as a conjunct of one resident fact — and, for each clause an
// earlier step of the proof rewrote out of the context, that step
// (rewrittenAwayNote on the spine the By runs on).
//
// advice is what the step says of a guard under the leaf's goal
// (_ByStep.guardAdviser).
func byUnsuppliedGuardsNote(spine, leaf *GoalStackNode, advice func(Prop, core.Term) string) string {
	if leaf == nil {
		return ""
	}
	note := ""
	for i := range leaf.Goal.NumHyps() {
		h := leaf.Goal.Hyp(i)
		guard, _, ok := ext.MatchesIMPLY(h)
		if !ok {
			continue
		}
		for _, piece := range unsuppliedPieces(leaf.Goal, guard, true, rungOpts{depth: byAssumption, scope: leaf.proofScope}) {
			note += fmt.Sprintf("\n  the premise %s is still guarded: the context does not supply %s%s%s",
				clipRunes(ext.PrintTerm(h), 80), clipRunes(ext.PrintTerm(piece), 80), rewrittenAwayNote(spine, piece),
				advice(leaf.Goal, piece))
		}
	}
	if note == "" {
		return ""
	}
	return "\nguards the close could not discharge:" + note
}

// withGuardAdvice is described with, on the line of each premise that
// fell to its clause form for a guard (clauseGuards), what advice says
// of that guard under leaf — the working leaf of the failing close,
// which holds every premise the By installed. A copy: described is the
// caller's. The same list where no leaf is at hand.
func (step _ByStep) withGuardAdvice(described []string, leaf *GoalStackNode, advice func(Prop, core.Term) string) []string {
	if leaf == nil || len(step.clauseGuards) == 0 {
		return described
	}
	out := slices.Clone(described)
	for i, guard := range step.clauseGuards {
		if said := advice(leaf.Goal, guard); said != "" {
			out[i] += "\n      (" + strings.TrimPrefix(said, " — ") + ")"
		}
	}
	return out
}

// guardAdviser is what the step's failure says of a guard the context
// does not supply and the arithmetic closer decides under a goal's
// hypotheses: a By whose closer is another reads a guard at its numerals
// and does no other arithmetic on it, so the guard is stated by that
// closer or the step closed by it; a reflexive bound is also what its
// order's reflexivity law, listed, supplies. It says nothing of a guard the closer does not decide there, and
// nothing in a step whose closer it is — there the rung asked it
// already. The decision is the first reading ByArith gives a leaf, by
// the policy an Arith step of the step's scope runs under (the
// unscoped one where the step has none); it builds no step and notes
// no use of the closer, being read for a failure's message alone. One
// failure asks about one leaf, whose hypotheses are read once.
func (step _ByStep) guardAdviser() func(goal Prop, guard core.Term) string {
	if step.arith {
		return func(Prop, core.Term) string { return "" }
	}
	var read Prop
	var ctx *omega.ArithCtx
	return func(goal Prop, guard core.Term) string {
		if ctx == nil || read != goal {
			policy, reader := omega.UnscopedArithPolicy(), (*omega.LibraryReader)(nil)
			if step.scope != nil {
				policy, reader = step.scope.ArithPolicy(), libraryReader(step.scope)
			}
			read, ctx = goal, omega.NewArithCtxWithPolicy(goal.Hyps(), policy, reader)
		}
		if w := ctx.Decide(guard); w == nil || !prop.Rhs(w).Equals(prop.T) {
			return ""
		}
		advice := " — arithmetic decides this guard from the leaf, and a By that is not ByArith reads a guard at its " +
			"numerals and does no other arithmetic on it: state it first as a Have closed by ByArith and list that, or " +
			"close the step with ByArith"
		if _, sides := ext.MatchesApply(guard); len(sides) == 2 && sides[0].AlphaEquals(sides[1]) {
			advice += ", or list the order's reflexivity law, which the rung applies to a reflexive bound"
		}
		return advice
	}
}

// describeGroundings renders the stage's actions for the failure
// diagnostics (the panic names what was tried): each grounding, and, for
// a stage that prunes, what became of its source — replaced, or kept
// because the plan was a guess (guessedInstance), with the antecedent the
// leaf did not hold. A stage that keeps passes neither list: every source
// stands beside its instances.
func describeGroundings(applied []ematch.Plan, replaced []core.Term, guessed map[core.TermKey]core.Term) []string {
	out := make([]string, 0, len(applied))
	for _, pl := range applied {
		ws := make([]string, len(pl.Witnesses))
		for i, w := range pl.Witnesses {
			ws[i] = ext.PrintTerm(w)
		}
		tag := ""
		for _, r := range replaced {
			if r.AlphaEquals(pl.Hyp) {
				tag = " [wide form replaced]"
				break
			}
		}
		if unheld, ok := guessed[pl.Hyp.AlphaKey()]; ok && tag == "" {
			tag = fmt.Sprintf(" [wide form kept: matched through its conclusion alone, and the instance's antecedent %s is not in the context]",
				clipRunes(ext.PrintTerm(unheld), 60))
		}
		out = append(out, fmt.Sprintf("grounded %s at (%s) — an ematch guess%s",
			clipRunes(ext.PrintTerm(pl.Hyp), 60), strings.Join(ws, ", "), tag))
	}
	return out
}

// verifyPlanEntryRoundTrip decodes the freshly built plan entry and
// asserts it reproduces the applied groundings term-for-term. A
// mismatch is a recorder fault (the silent-tuple-binding class) and
// panics — a plan that decodes to different mathematics would replay a
// conditioning the session never ran.
func verifyPlanEntryRoundTrip(entry *ByConditionPlanProto, pend byPendingPlan, env *ProverEnv) {
	var loadMeta func(core.TermName) (core.ConstTermMeta, bool)
	if env.ProofService != nil {
		loadMeta = env.ProofService.LoadConstMeta
	}
	reader := ext.NewPoolReader(entry.Pool, loadMeta)
	broken := func(what string) {
		panic(fmt.Sprintf("By[S4]: plan entry for %s does not round-trip (%s) — "+
			"recorder fault, refusing to persist a plan that replays different mathematics",
			pend.bareKey, what))
	}
	if len(entry.Groundings) != len(pend.groundings) || len(entry.Replaced) != len(pend.replaced) {
		broken("entry counts diverge")
	}
	// The entry's terms are under the canonical free names; so are the
	// expected ones here.
	for i, g := range entry.Groundings {
		hypTerm := reader.Term(g.Hyp)
		if hypTerm == nil || !hypTerm.AlphaEquals(pend.groundings[i].Hyp.Substitute(pend.canon...)) {
			broken(fmt.Sprintf("grounding %d hyp diverges", i))
		}
		if len(g.Witnesses) != len(pend.groundings[i].Witnesses) {
			broken(fmt.Sprintf("grounding %d witness count diverges", i))
		}
		for j, w := range g.Witnesses {
			wt := reader.Term(w)
			if wt == nil || !wt.AlphaEquals(pend.groundings[i].Witnesses[j].Substitute(pend.canon...)) {
				broken(fmt.Sprintf("grounding %d witness %d diverges", i, j))
			}
		}
	}
	for i, r := range entry.Replaced {
		rt := reader.Term(r)
		if rt == nil || !rt.AlphaEquals(pend.replaced[i].Substitute(pend.canon...)) {
			broken(fmt.Sprintf("replaced entry %d diverges", i))
		}
	}
}

// runEconomyAudit is the economy audit — recorder-side and REPORT-only,
// run after a By closed successfully. Two downward probes,
// both on throwaway state (the composite's own tree is never
// touched — its reconstructs are pure closures over it):
//
//   - refute → Basic(): each sequent the CNF closer received is
//     re-tried under a plain Basic() on a fresh stack. A close names a
//     candidate, and the By respelled with Normalized is then run as
//     the inert probes run theirs: where it closes on fewer rows than
//     this close touched, the honest spelling is By(Normalized, …).
//   - inert → each shape element, the Broadcast flag and each premise
//     of the set driver taken out one at a time: the WHOLE composite
//     re-runs without it through the recorder's ladder, held to the rows
//     this close touched (auditProbeReplays). A close means the element
//     is inert — a recording of the By without it touches no row this
//     one does not, so the drop costs no key and no plan.
//
// A finding is reported and never applied: findings are MESSAGES through
// env.ByAuditReport; the recording and the member text stay untouched, and
// applying a finding is an authored edit. The FAILURE path reports the same
// discovery as a message too (byClosesUnderBasic's MISS diagnostic).
//
// The probes write nothing, and the replay probes are served no row but
// the ones this close touched, so an audited run leaves the store, and
// a capturing store's record of the member, as an unaudited run does.
func (step _ByStep) runEconomyAudit(p Prop) {
	report := step.env.ByAuditReport
	if report == nil {
		return
	}
	label := step.auditLabel()
	rows := step.closeTrace
	Assert(rows != nil)

	// Probe B′ — an inert Broadcast. Broadcast is a premise-list option
	// outside ByShape, so the per-element loop below never sees it, and
	// nothing else reports it: a By that fans WITHOUT the flag fails
	// loudly, one that carries it over a close that does not fan says
	// nothing — a marker left behind by a shaping that went. Author's
	// only — no engine-built By carries it.
	if step.broadcast {
		probe := step
		probe.broadcast = false
		if auditProbeReplays(probe, p, rows) {
			report(fmt.Sprintf("%s: shape element Broadcast is inert — %s; drop it.", label, auditInertReason))
		}
	}

	// The arithmetic closer is audited for that one element only: it
	// records no key, so the probes below have nothing to read on it.
	if step.arith {
		return
	}

	// Probe C — an inert premise of the set driver. The driver unfolds
	// its standard vocabulary itself, so a cited membership law
	// (`set_basic.InInter` beside a set built with ∩) dissolves into a
	// tautology and the close succeeds just as well without it — and
	// nothing on the success path says so. Each premise is dropped in
	// turn; a premise whose removal leaves the driver a refute this
	// close did not make is not named, since the drop would cost that
	// refute's key.
	if step.settac {
		for i, pr := range step.premises {
			probe := step
			probe.premises = append(append([]byPremise(nil), step.premises[:i]...), step.premises[i+1:]...)
			// The leaf the ladder reads is already cleared to the named
			// residents (phase 2 above ran on the real tree), so a
			// resident premise dropped from the list must leave the
			// sequent too — "without it" for a resident means the
			// hypothesis is gone, exactly as an unnamed one would be.
			without := p
			if pr.resident {
				if idx, err := findHypIndex(p, pr.install.AsProp().Conclusion()); err == nil {
					hyps := make([]Term, 0, p.NumHyps()-1)
					for j := 0; j < p.NumHyps(); j++ {
						if j != idx {
							hyps = append(hyps, p.Hyp(j))
						}
					}
					without = core.MakeProp(p.Conclusion(), hyps...)
				}
			}
			if auditProbeReplays(probe, without, rows) {
				report(fmt.Sprintf("%s: premise %s is inert — %s; drop it.",
					label, pr.description(), auditInertReason))
			}
		}
		return
	}

	// Probe A — the refuter was never needed.
	step.reportAvoidableRefutes(p, rows, report)

	// Probe B — inert shape elements. A shape the prover inserted is
	// not the author's to drop, so there is nothing to advise.
	if step.shape == nil || step.engineShape {
		return
	}
	for _, variant := range shapeRemovals(*step.shape) {
		probe := step
		probe.shape = variant.shape
		if auditProbeReplays(probe, p, rows) {
			report(fmt.Sprintf("%s: shape element %s is inert — %s; drop it.",
				label, variant.desc, auditInertReason))
		}
	}
}

// auditInertReason is what every "inert" finding says of the By without
// the element it names (auditProbeReplays).
const auditInertReason = "the close succeeds without it on the rows it already records, no new key and no new plan"

// auditProbeReplays is the audit's one test of "inert": the By the
// caller built — the audited step with a shape element, the Broadcast
// flag or a premise taken out — run through the recorder's ladder, held
// to the rows the audited close touched (auditReplayProbeKey). It closes
// at the keyless rung, at the bare rung on certificates among those
// rows, or at the conditioned rung on a plan and certificates among
// them; every failure is "not inert" (rungFailure).
//
// The test is what a recording of that By would touch, so it searches
// for no refutation and reads no clock. A live refute is not the test:
// a leaf the refuter closes without the element closes at a key the
// recording of that spelling writes, so "the ladder still closes" says
// nothing of what the drop costs. A plan is held to the same bound: one
// the grounding stage would record in a marker's place is blob state
// where the marker was one token of text.
func auditProbeReplays(probe _ByStep, p Prop, rows *byCloseTrace) (closed bool) {
	_, closed = auditProbeRows(probe, p, rows)
	return closed
}

// auditProbeRows is auditProbeReplays with the count of the rows the
// probe was served, keys and plans together: what a recording of the
// probe's spelling touches, never more than the audited close's rows.
func auditProbeRows(probe _ByStep, p Prop, rows *byCloseTrace) (read int, closed bool) {
	probe.ctx = withAuditReplayProbe(probe.ctx, rows)
	replay := auditReplayOf(probe.ctx)
	probe.condition, probe.keyless = false, false
	probe.s4, probe.audit = nil, nil
	probe.failureUnread = true
	defer func() {
		if rungFailure(recover()) != nil {
			closed = false
		}
	}()
	closed = probe.applyLadder(p) != nil
	return len(replay.read.keys) + len(replay.read.plans), closed
}

// auditBasicCloses is probe A's oracle, and the MISS diagnostics'
// (byClosesUnderBasic, cnfMissWithBasicCheck), on a FRESH search, never
// the live tree: does the Basic() fixpoint, given byAuditProbeBudget of
// wall clock, close g outright? A search abandoned at the deadline
// answers no, and so does one that panicked, unless the panic is a
// fault (rungFailure).
func auditBasicCloses(ctx context.Context, g Prop) (closed bool) {
	defer func() {
		if rungFailure(recover()) != nil {
			closed = false
		}
	}()
	ctx, cancel := context.WithTimeout(ctx, byAuditProbeBudget)
	defer cancel()
	sg := tactic.BasicTacticsUnder(ctx)(g)
	return sg != nil && sg.Size() == 0
}

// auditLabel names the By in a finding: its premise list, and the
// source line where the step carries one.
func (step _ByStep) auditLabel() string {
	described := make([]string, len(step.premises))
	for i, pr := range step.premises {
		described[i] = pr.description()
	}
	label := fmt.Sprintf("By(%s)", strings.Join(described, "; "))
	if step.site != "" {
		label += " at " + step.site
	}
	return label
}

// reportAvoidableRefutes is the audit's first probe (Probe A): the
// refuter was never needed. Each sequent the CNF closer received in the
// closing attempt is re-tried under a plain Basic() on a fresh stack;
// one that closes names a candidate and proves nothing about the By,
// whose other leaves and whose conditioned rung the marker changes too.
// So the respelling is run: the By with Normalized, through the
// recorder's ladder, held to the rows this close touched
// (auditProbeRows). The finding is printed where that By closes on
// FEWER rows — a respelling that leaves leaves open, or closes on the
// same certificates and plans, saves nothing and is not advised.
//
// A By that carries a shape runs Basic() before its close already, and
// Normalized adds nothing to it. The arithmetic closer and the set
// driver capture nothing, so there is nothing to report on them.
func (step _ByStep) reportAvoidableRefutes(p Prop, rows *byCloseTrace, report func(finding string)) {
	if step.audit == nil || step.shape != nil {
		return
	}
	Assert(rows != nil)
	i := slices.IndexFunc(step.audit.preClose, func(g Prop) bool { return auditBasicCloses(step.ctx, g) })
	if i < 0 {
		return
	}
	probe := step
	probe.shape = &ByShape{}
	touched := len(rows.keys) + len(rows.plans)
	read, closed := auditProbeRows(probe, p, rows)
	if !closed || read >= touched {
		return
	}
	report(fmt.Sprintf("%s: the refuted leaf closes under Basic(), and By(Normalized, …) closes on %d row(s) "+
		"where this close touches %d — the refuter (and its recorded key) is avoidable; spell By(Normalized, …).\n  leaf: %s",
		step.auditLabel(), read, touched, clipRunes(prop.PrintProp(step.audit.preClose[i]), 160)))
}

// shapeRemoval is one probe-B variant: the shape with one element
// dropped (nil = the element was the whole shape).
type shapeRemoval struct {
	desc  string
	shape *ByShape
}

// shapeRemovals enumerates the author-visible shape elements one
// removal at a time, in a fixed order.
//
// The empty_set shape is an element too. `Normalized` is `ByShape{}` — no
// flag set, its whole effect being that the step carries a shape at
// all, so Basic() runs before the close — and a per-flag loop finds
// nothing in it to remove. That left the audit structurally blind on
// the one marker the corpus writes 1141 times against 19 for all the
// others combined: Probe A could tell an author to ADD `Normalized`,
// and nothing could ever tell them to take one out. Its removal is
// the whole shape, i.e. nil.
func shapeRemovals(s ByShape) []shapeRemoval {
	if !s.pre && !s.raw && !s.hilbert && s.denote == 0 && s.denoteTerm == nil {
		return []shapeRemoval{{desc: "Normalized", shape: nil}}
	}
	norm := func(cp ByShape) *ByShape {
		if !cp.pre && !cp.raw && !cp.hilbert && cp.denote == 0 && cp.denoteTerm == nil {
			return nil
		}
		return &cp
	}
	var out []shapeRemoval
	if s.pre {
		cp := s
		cp.pre = false
		out = append(out, shapeRemoval{desc: "PreNormalized", shape: norm(cp)})
	}
	if s.raw {
		cp := s
		cp.raw = false
		out = append(out, shapeRemoval{desc: "Raw", shape: norm(cp)})
	}
	if s.denote > 0 {
		cp := s
		cp.denote = 0
		out = append(out, shapeRemoval{desc: fmt.Sprintf("Denoted(%d)", s.denote), shape: norm(cp)})
	}
	if s.denoteTerm != nil {
		cp := s
		cp.denoteTerm, cp.denoteName, cp.denoteHilbert = nil, "", false
		out = append(out, shapeRemoval{
			desc:  fmt.Sprintf("DenotedAs(%s, %s)", s.denoteName, clipRunes(ext.PrintTerm(s.denoteTerm), 60)),
			shape: norm(cp)})
	}
	if s.hilbert {
		cp := s
		cp.hilbert = false
		out = append(out, shapeRemoval{desc: "HilbertDenoted", shape: norm(cp)})
	}
	return out
}

// byClosesUnderBasic reports whether the still-open working leaf is
// closed by a plain Basic(). It exists for ONE caller: the CNF-cache-MISS
// branch of By's failure message, which has to tell a genuine recording
// gap ("this leaf wants the refuter, record its key") apart from a shape
// problem ("this leaf never wanted the refuter — spell By(Normalized,…)").
// Those two readings of a MISS point in opposite directions, and a family
// practising zero recorded keys gets the wrong one from the record-first
// advice every time.
//
// The check is auditBasicCloses on the leaf's goal: a fresh search off
// the By's tree, under byAuditProbeBudget, so a Basic() that does not
// reach its fixpoint inside the budget answers no. With more than one
// leaf open no single Basic() closes the By, and the answer is no.
//
// Why this is a MESSAGE and not a behaviour — why By does NOT insert
// the Basic() itself, or auto-rewrite equation premises, once it knows
// the leaf would close:
//
//   - It would invert the authoring incentive. The explicit spellings
//     (a named `Have` for the equation, then `f.Rw`) put the step in the
//     checked layer — real_order_ring's four *MulRight members read
//     "turn the smaller product round" that way. A By that rewrote for
//     the author would make the flat form the path of least resistance,
//     the intermediate fact would disappear from the proof, and review
//     would have to push authors back uphill.
//   - It would blur the premise/shaping boundary that ByShape's own doc
//     draws ("carry no premise and state nothing about the argument").
//     An auto-prewrite CONSUMES a premise, silently reclassifying it
//     from fact to rewrite rule.
//   - Direction and termination would have to be guessed. A permutation
//     equation (x*z = z*x) oscillates under unguarded rewriting — the
//     reason eqSimplify carries a size guard at all. The author
//     carries the direction in Rw(flip); an engine guess fails in a way
//     that reads worse than this panic.
//
// One layer down, a ground equation between two nonlinear products
// does serve as a premise, though the closer meets the products as
// distinct opaque atoms: ground congruence closure runs IN-SEARCH, as
// the order-gated same-size demodulation case of the clause layer's
// Simplifies rule (ext/clause/deduce.go), so the premise identifies
// its two spellings by demodulation and the clause set and every
// recorded CNF key are untouched. A Have+Rw spelling of such a site is
// valid authored text and is not forced.
func byClosesUnderBasic(ctx context.Context, root *GoalStackNode, claims []*GoalStackNode) bool {
	leaves := byWorkingLeaves(root, claims)
	if len(leaves) != 1 {
		return false
	}
	return auditBasicCloses(ctx, leaves[0].Goal)
}

// MergeByShapes folds a premise list's shaping values into the ONE
// merged ByShape a By records (shaping values merge; only a denote-size
// or explicit-denote conflict is an error). nil for an empty list. The
// macro's premise-list parse and the engine's `by` dispatch share this
// so the two surfaces reject exactly the same conflicts.
func MergeByShapes(shapes []ByShape) *ByShape {
	var shape *ByShape
	for _, sh := range shapes {
		if shape == nil {
			cp := sh
			shape = &cp
			continue
		}
		if sh.denote > 0 {
			if shape.denote > 0 && shape.denote != sh.denote {
				panic(fmt.Sprintf("By: two Denoted sizes in one premise list (%d and %d) — pick one",
					shape.denote, sh.denote))
			}
			shape.denote = sh.denote
		}
		if sh.denoteTerm != nil {
			if shape.denoteTerm != nil {
				panic(fmt.Sprintf("By: two explicit denote shapings in one premise "+
					"list (%s and %s) — a By names at most one term",
					ext.PrintTerm(shape.denoteTerm), ext.PrintTerm(sh.denoteTerm)))
			}
			shape.denoteTerm, shape.denoteName = sh.denoteTerm, sh.denoteName
			shape.denoteHilbert = sh.denoteHilbert
		}
		shape.hilbert = shape.hilbert || sh.hilbert
		shape.pre = shape.pre || sh.pre
		shape.raw = shape.raw || sh.raw
	}
	return shape
}

// ByPremiseSpec is the engine-facing premise descriptor for ApplyByStep
// — the session `by` tactic's resolved premise (the engine resolves
// keys/text/hyp references before this layer).
type ByPremiseSpec struct {
	// Install: named flavor — the resolved install form; resident flavor
	// — a hyp-free Prop whose conclusion is the resident hyp's statement.
	Install Prop
	// Reference is the stated form whose binder order Witnesses follow.
	// nil = Install.
	Reference Prop
	Witnesses []Term
	// Named pins binders of the stated form by name (the session's
	// sparse term_specialize, the macro's Where): the premise is the
	// apply rung's seeded head and must fire. Exclusive with Witnesses;
	// a resident premise takes none.
	Named    []NamedWitness
	Resident bool
	// Exact marks Install as an EXPLICIT type instantiation (an
	// agent-supplied type_specialize σ): the executor installs it
	// exactly instead of letting the speculative goal-side adaptation
	// override it.
	Exact bool
	// Clause is an Exact key premise's clause form, the one Go's typed
	// instance of the same entry carries (ExplicitInstanceClause):
	// bare, it installs; witnessed, a ⇔ law installs it and its stated
	// form grounds as the apply rung's head. nil leaves the clause form
	// to ApplyByStep: InstallForm(Install) for a premise neither resident
	// nor exact, none for the rest.
	Clause Prop
	// Coefficient scales the premise (fact.go Scaled; the session's
	// `coefficient`): the equation's congruence under multiplication by
	// it is added beside the premise once installed and grounded.
	Coefficient Term
	// ReadingUnder marks a structure law read under a RESIDENT
	// hypothesis of the goal — proof.Read at a resident fact, as a
	// session premise. Install is then the kernel-derived SEQUENT
	// `S(c) ⊢ body[comps := c]` (ReadLawAt against the hypothesis
	// assumed), and the premise materializes as the macro's does: bare,
	// asserted ahead of every install with its claim branch closed from
	// that sequent; witnessed or pinned by name, the sequent installed
	// exactly and grounded. Either way the hypothesis is kept resident
	// beside it. A reading at an instance ENTRY is an ordinary named
	// premise whose Install is the derived theorem, and sets only
	// Reading.
	ReadingUnder bool
	// Reading says what Install was read from, for the record
	// (ReadingRecord). The executor never consults it.
	Reading *ReadingRecord
	// Describe labels the premise in failure diagnostics (the agent's
	// own spelling — key, name, hyp index).
	Describe string
	// SourceKey names the entry a key premise was loaded from, by the
	// key or registered name the session resolved it through: emit
	// cites Install by that entry where Install, a type instance of the
	// entry's statement, has no entry of its own. In memory only (the
	// record does not carry it); empty for a premise no entry names.
	SourceKey core.PropKey
}

// BySpec bundles ApplyByStep's inputs. Shapes carries the shaping
// VALUES (Normalized / PreNormalized / Denoted(n) / HilbertDenoted…);
// ApplyByStep merges them via MergeByShapes — same rules, same
// conflicts as the macro's premise-list parse.
type BySpec struct {
	Premises []ByPremiseSpec
	Shapes   []ByShape
	Arith    bool
	// Settac selects the membership-mode set driver as the terminal
	// closer (the math layer's BySets). Mutually exclusive with Arith.
	Settac bool
	// Chase selects the diagram-chase closer (the math layer's ByChase)
	// and ChaseDepth its number of pull-back rounds (Depth(k)). Mutually
	// exclusive with Arith and Settac.
	Chase      bool
	ChaseDepth int
	Broadcast  bool
	// Report, when non-nil, receives the economy audit's first finding
	// for this one call: a leaf the close sent to the refuter that a
	// plain Basic() closes ("spell By(Normalized, …)"). The session's
	// `by` passes it, so an author reads that before any blob is
	// written; the rest of the audit is the recorder's
	// (ProverEnv.ByAuditReport). Nothing is applied and nothing recorded
	// changes.
	Report func(finding string)
	// Closed reports the routes used by the successful attempt only.
	// It is observational and is not serialized into the proof.
	Closed func(string)
	// Records reports the rows the recorder would write for the close:
	// the certificate keys the refutes wrote (a live refute) or read (a
	// cached certificate), and the conditioning plan keys the stage
	// persisted or applied from the store. The session's `by` and `probe` pass it, so an author
	// sees "records: 1 key (prop_…), 1 plan" or "records nothing" before
	// any blob is written — the question only the recorder's dry run
	// answered before. Observational; nothing recorded changes.
	Records func(keys []core.PropKey, plans []core.PropKey)
	// Whistle, when non-nil, receives the divergence-whistle cuts a
	// replay of a recording of the close meets, when there are any
	// (applyLadder says which; tactic.DescribeWhistleCut renders one).
	// The close stands — a cut costs the search a simplification, never
	// soundness — but a cut is a function of the goal it is made at, the
	// member's replay meets it again, and the recorder refuses a member
	// whose replay does. The session's `by` and `probe` pass it.
	// Observational; nothing recorded changes.
	Whistle func(cuts []skeleton.WhistleEvent)
}

// ApplyByStep runs the `by` composite on n's goal, recording ONE
// _ByStep ministep. The claim obligations of named premises surface as
// n's open children afterwards — the caller certifies them (session:
// auto-match against the named entries; programmatic callers:
// CiteKnown). Panics carry the By diagnostics; the engine dispatch
// recovers them into errors.
func ApplyByStep(n *GoalStackNode, env *ProverEnv, ctx context.Context, spec BySpec) bool {
	premises := make([]byPremise, len(spec.Premises))
	hypotheses := make([][]Term, len(spec.Premises))
	described := make([]string, len(spec.Premises))
	for i, p := range spec.Premises {
		described[i] = p.Describe
		if p.ReadingUnder {
			var h Term
			premises[i], h = readingUnderPremise(p)
			if h != nil {
				hypotheses[i] = []Term{h}
			}
			continue
		}
		if len(p.Named) > 0 {
			if p.Resident {
				panic(fmt.Sprintf("By: premise %s pins a binder by name, which reads a NAMED fact's stated "+
					"form — a resident hypothesis is grounded positionally", p.Describe))
			}
			if len(p.Witnesses) > 0 {
				panic(fmt.Sprintf("By: premise %s carries both a positional tuple and a named table — "+
					"a fact takes one or the other", p.Describe))
			}
		}
		if p.Coefficient != nil && len(p.Named) > 0 {
			panic(fmt.Sprintf("By: premise %s is pinned by name and scaled — the apply rung's head is not scaled; "+
				"ground it positionally and scale the instance", p.Describe))
		}
		premises[i] = byPremise{
			install:     p.Install,
			reference:   p.Reference,
			witnesses:   p.Witnesses,
			named:       p.Named,
			resident:    p.Resident,
			exact:       p.Exact,
			coefficient: p.Coefficient,
			reading:     p.Reading,
			describe:    p.Describe,
			sourceKey:   p.SourceKey,
		}
		// A session's key-resolved premise carries its Normalize as the
		// clause form, as the Go macro's named dep does (byPremise.
		// clause): bare, that is what installs; witnessed, the stated
		// form is plain-added and grounded. An explicit type instance
		// carries the clause form its caller derived the way Go's typed
		// instance does (ByPremiseSpec.Clause), Normalize and type
		// instantiation not commuting.
		if p.Clause != nil {
			premises[i].clause = p.Clause
		} else if !p.Resident && !p.Exact && p.Install != nil {
			premises[i].clause = p.Install
			if nl := InstallForm(p.Install.AsProp()); nl != nil {
				premises[i].clause = nl
			}
		}
	}
	if spec.Arith && spec.Settac {
		panic("By: Arith and Settac are mutually exclusive closers — pick one")
	}
	if spec.Chase && (spec.Arith || spec.Settac) {
		panic("By: Chase is mutually exclusive with Arith and Settac — pick one closer")
	}
	if spec.Chase && spec.ChaseDepth < 0 {
		panic("By: a negative chase depth")
	}
	// A premise reading a law under a resident hypothesis brings the
	// premise locating that hypothesis with it, and a bare one goes
	// ahead of every install — as in the macro's premise list (fact.go).
	premises = withReadingsFirst(withHypothesisPremises(n.Goal, premises, hypotheses, described))
	return n.runStep(_ByStep{
		premises:      premises,
		shape:         MergeByShapes(spec.Shapes),
		arith:         spec.Arith,
		settac:        spec.Settac,
		chase:         spec.Chase,
		chaseDepth:    spec.ChaseDepth,
		broadcast:     spec.Broadcast,
		env:           env,
		ctx:           ctx,
		spine:         n,
		leafReport:    spec.Report,
		closeReport:   spec.Closed,
		recordsReport: spec.Records,
		whistleReport: spec.Whistle,
	})
}

// readingUnderPremise is a session premise reading a law under a
// resident hypothesis (ByPremiseSpec.ReadingUnder), as the composite's
// premise, with the hypothesis it is read under — the two shapes the
// macro gives proof.Read at a resident fact (fact.go): bare, the
// derived flavor, a Have moved inside the leaf; witnessed or pinned by
// name, the sequent itself, an explicit instance with no clause form.
func readingUnderPremise(p ByPremiseSpec) (byPremise, Term) {
	if p.Install == nil || p.Install.NumHyps() != 1 {
		panic(fmt.Sprintf("By: premise %s is marked as a law read under a resident hypothesis, which is a "+
			"sequent with that one hypothesis", p.Describe))
	}
	if p.Resident {
		panic(fmt.Sprintf("By: premise %s is both a resident hypothesis and a law read under one", p.Describe))
	}
	hypothesis := p.Install.Hyp(0)
	if len(p.Witnesses) == 0 && len(p.Named) == 0 {
		if !(p.Install.Proved() || core.IsPromised(p.Install)) {
			panic(fmt.Sprintf("By: premise %s is a bare reading under a resident hypothesis, whose claim branch "+
				"closes from the derived sequent — it must be that theorem, not its statement", p.Describe))
		}
		return byPremise{
			install:      core.MakeProp(p.Install.Conclusion()),
			derivedCert:  p.Install,
			readingUnder: true,
			coefficient:  p.Coefficient,
			reading:      p.Reading,
			describe:     p.Describe,
		}, hypothesis
	}
	return byPremise{
		install:     p.Install,
		witnesses:   p.Witnesses,
		named:       p.Named,
		exact:       true,
		coefficient: p.Coefficient,
		reading:     p.Reading,
		describe:    p.Describe,
	}, hypothesis
}

// prenexForallChain lifts every ∀ of a statement's leading ∀/⇒ spine
// to the front, preserving both the binder order and the antecedent
// order as stated: `P ⇒ ∀x. Q` becomes `∀x. (P ⇒ Q)`, applied
// recursively down the spine. This is the install shaping for the
// ⇒-headed guard in the _ByStep executor (see the call site): a
// witness tuple reads in the STATED binder order, and this lift is the
// one transform that exposes those binders without renaming, reordering
// or otherwise re-spelling anything. Sound term-for-term because each
// commuted binder is the lemma's own bound variable; a binder that IS
// free in the antecedent it would cross (a capture) stops the lift at
// that point rather than renaming — the caller's prefix-length check
// then decides the shaping simply does not apply.
func prenexForallChain(t core.Term) core.Term {
	if abs := ext.MatchesFORALL(t); !abs.IsZero() {
		return ext.ForAll(abs.Var())(prenexForallChain(abs.Body())).Core()
	}
	if ante, concl, ok := matchesImply(t); ok {
		return liftAntecedent(ante, prenexForallChain(concl))
	}
	return t
}

// liftAntecedent pushes one antecedent under a leading ∀-chain, up to
// the first binder that would capture.
func liftAntecedent(ante, t core.Term) core.Term {
	if abs := ext.MatchesFORALL(t); !abs.IsZero() && !hasVar(ante.Frees(nil), abs.Var()) {
		return ext.ForAll(abs.Var())(liftAntecedent(ante, abs.Body())).Core()
	}
	return ext.Apply(ext.IMPLY, ante, t).Core()
}

// completeStatedTuple reads the binders a prefix tuple leaves open off
// the goal: the stated form's guarded ∀-chain is longer than the tuple,
// the given witnesses are seeded onto its leading binders, and the
// stated conclusion is matched against the goal's (matchHead — the
// apply rung's reading, seeds βη-applied) to pin the rest. The full
// tuple in stated order, or nil when the tuple is already full or the
// goal pins some binder nothing names. The form is the typed one the
// tuple forces (the caller's witnessTypedForm); door is the reading the
// match takes, the attempt's own.
func completeStatedTuple(goal Prop, stated Prop, witnesses []core.Term, door rungOpts) []core.Term {
	if stated.NumHyps() > 0 {
		return nil
	}
	form := stated
	// A statement with free term variables — a spec-parametric law, a
	// test fixture's — installs ∀-closed over them ahead of its stated
	// binders, a prefix the stated tuple does not address; such a
	// premise keeps the clause lane (leadStatedBinders reads its tuple
	// there) and the exact-instance closure completion it has.
	if len(form.Conclusion().Frees(nil)) > 0 {
		return nil
	}
	binders, _ := ematch.StripGuardedForalls(form.Conclusion())
	n := len(witnesses)
	if n >= len(binders) {
		return nil
	}
	for i := range n {
		if !binders[i].Type().Equals(witnesses[i].Type()) {
			return nil
		}
	}
	named := make([]NamedWitness, n)
	for i := range n {
		named[i] = NamedWitness{Binder: string(binders[i].Name()), Witness: witnesses[i]}
	}
	plan, _ := matchHead(door.reader(), goal, form.Conclusion(), "the premise", named)
	if plan == nil || plan.unpinned() {
		return nil
	}
	if m := plan.pinWitnesses("the premise"); m != "" {
		return nil
	}
	if len(plan.witnesses) != len(binders) {
		return nil
	}
	return plan.witnesses
}

// completeClosureWitnesses prepends identity witnesses for the
// closure-added ∀-prefix of a spec-parametric premise: injection
// ∀-closes the cert's free spec variables ahead of the stated binders,
// and the consumer means each of those AT the context's own free
// variable of the same name and type — vsp at vsp, jk at jk. Any
// closure binder the leaf does not actually hold free is a mismatch
// between the premise's spec vocabulary and the consuming statement's,
// reported by name.
func completeClosureWitnesses(goal Prop, hypIdx int, wits []Term, desc string) []Term {
	var prefix []core.VarTerm
	t := goal.Hyp(hypIdx)
	for {
		abs := ext.MatchesFORALL(t)
		if abs.IsZero() {
			break
		}
		prefix = append(prefix, abs.Var())
		t = abs.Body()
	}
	k := len(prefix) - len(wits)
	if k <= 0 {
		return wits
	}
	leafFrees := goalFreeNames(goal)
	completed := make([]Term, 0, len(prefix))
	for _, v := range prefix[:k] {
		if !hasVar(leafFrees, v) {
			panic(fmt.Sprintf("grounding %s: closure binder %s:%s is not a free variable of the "+
				"consuming context — the premise's spec vocabulary does not match the statement's",
				desc, v.Name(), ext.FormatType(v.Type())))
		}
		completed = append(completed, v)
	}
	return append(completed, wits...)
}
