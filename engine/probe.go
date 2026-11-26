package engine

import (
	"context"
	"errors"
	"fmt"
	"runtime/debug"
	"strings"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

const (
	// ProbeDefaultBudgetMs is the default per-call probe budget: long
	// enough that a close the session's apply finishes in under a second
	// answers instead of being cut off, short beside an agent's own turn.
	// A structural step answers in milliseconds whatever the budget; a
	// search that finds nothing waits it out. A request's budget_ms
	// replaces it, never past the request context's deadline.
	ProbeDefaultBudgetMs = 1000
)

// Probe runs a single tactic against a clone of the named goal and reports
// the outcome without touching the session. The agent uses this as a
// non-destructive lookahead: "if I tried apply X, what subgoals would I
// see?".
//
// Outcome contract:
//
//   - success     — tactic applied; subgoals returned. effect ∈ close /
//     simplify / branch.
//   - fail        — strong negative for structural / unification tactics
//     (the tactic genuinely doesn't apply on this shape).
//   - unknown     — soft negative; reason is one of the ProbeReason*
//     constants. Never combine fail + a reason — fail means
//     "this is definitively not applicable," unknown means
//     "we couldn't decide cheaply."
func (e *Engine) Probe(ctx context.Context, sessionID string, req *ProbeRequest) (result *ProbeResult, err error) {
	if req == nil {
		return nil, fmt.Errorf("probe request is required")
	}
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if err := s.faultRefusal(); err != nil {
		return nil, err
	}
	entry, goalID, err := e.resolveFocusedGoal(s, req.GoalID)
	if err != nil {
		return nil, err
	}
	if entry == nil {
		return nil, fmt.Errorf("session has no open goals to probe")
	}

	start := time.Now()

	// Determine effective deadline: min(ctx-deadline, start + budget). The
	// budget can shorten but never lengthen past the request context.
	budgetMs := req.BudgetMs
	if budgetMs <= 0 {
		budgetMs = ProbeDefaultBudgetMs
	}
	probeDeadline := start.Add(time.Duration(budgetMs) * time.Millisecond)
	if cd, ok := ctx.Deadline(); ok && cd.Before(probeDeadline) {
		probeDeadline = cd
	}

	// Wrap ctx with the probe's tighter deadline so any cooperative
	// cancellation inside the tactic (e.g. AutoExpand's CNF refutation)
	// fires at the probe budget, not the outer RPC timeout. This is what
	// makes probe feel cheap.
	//
	// Also stamp the ctx with a CNF-refuter timeout override equal to
	// the probe budget — otherwise the inner CNF refuter falls back to
	// env.CnfRefuterTimeout (~2s) and an agent-supplied budget larger
	// than that is silently capped, with the diagnostic misleadingly
	// reporting the request value.	// @ ~2s" for the original symptom.
	probeBudget := time.Until(probeDeadline)
	probeCtx := context.WithValue(ctx, proof.CnfRefuterTimeoutCtxKey, probeBudget)
	probeCtx, cancel := context.WithDeadline(probeCtx, probeDeadline)
	defer cancel()

	res := &ProbeResult{}
	result = res
	defer func() {
		res.ElapsedMs = int(time.Since(start).Milliseconds())
	}()

	// A panic is an engine fault (fault.go): recorded, and answered as
	// unknown(panic_recovered) with the record's mark. The tactic's own
	// is read by runTactic; the recover here reads one raised while the
	// probe predicts what an apply would then do.
	scope := faultScope(ctx, s, "probe").onGoal(goalID, entry, req.Tactic, budgetMs)
	faulted := func(fault *EngineFault) {
		res.Outcome = ProbeUnknown
		res.Reason = ProbeReasonPanicRecovered
		res.EngineFault = fault
		res.Diagnostic = fault.message(fmt.Sprintf("probing tactic %s on goal %s", req.Tactic.Type, goalID))
	}
	defer func() {
		if r := recover(); r != nil {
			faulted(e.fileFault(s, scope.record(r, string(debug.Stack()))))
			result = res
			err = nil
		}
	}()

	clone, fault, runErr := e.runTactic(probeCtx, scope)
	// A run that ended well past the probe's deadline is written down,
	// whatever it answered (overrun.go).
	e.noteOverrun(scope, fmt.Sprintf("the probe of %s", req.Tactic.Type), probeDeadline, cutStackOf(runErr))
	if fault != nil {
		faulted(fault)
		return res, nil
	}
	var cutOff _CutOffError
	if errors.As(runErr, &cutOff) {
		// The run's context ended it inside a unit of work: no answer,
		// whatever the tactic.
		res.Outcome = ProbeUnknown
		res.Reason = ProbeReasonTimeout
		res.Diagnostic = fmt.Sprintf("%v (probe budget %dms)", runErr, budgetMs)
		return res, nil
	}
	if runErr != nil {
		// We can't easily distinguish "definitively not applicable" from
		// "ran out of time" inside runTacticOnClone — the structural
		// tactics return a clean error on shape mismatch (= fail) but
		// auto / refute / lemma can fail because of a budget. Map by
		// tactic class:
		switch req.Tactic.Type {
		case "auto", "expand":
			// These are search-y: a timeout maps to unknown(timeout), not
			// fail, so the agent can tell "no proof at this depth" from
			// "out of time". The CNF refuter inside auto honors the probe budget via
			// the proof.CnfRefuterTimeoutCtxKey override (set above), so
			// a CNF timeout propagates to probeCtx.Err() instead of
			// being masked as a "fail" with elapsed << budget.
			// (The agent surface has no bare `refute` —
			// runTacticOnClone rejects it upstream with a typed error.)
			if probeCtx.Err() == context.DeadlineExceeded || time.Now().After(probeDeadline) {
				res.Outcome = ProbeUnknown
				res.Reason = ProbeReasonTimeout
				// Attach the tactic-aware "switch strategy" advice. Without
				// it a probe timeout returned bare unknown(timeout) with no
				// guidance, so the agent re-probed with a larger budget
				// instead of reaching for congr/funext/lemma — the exact
				// loop the prod-foundation HO function-equality leaf hit
				//.
				res.Diagnostic = probeTimeoutDiagnostic(req.Tactic.Type, budgetMs)
				return res, nil
			}
			// Search exhausted within the budget without timing out =
			// strong negative. The elapsed_ms field tells the agent how
			// much of the budget was actually consumed, which is the
			// signal for "retrying with a larger budget won't help".
			//
			// Use the tactic-aware diagnostic from engine.go so the agent
			// gets the same "switch tactic, don't retry" guidance whether
			// it sees the failure via apply or probe. Budget/elapsed are
			// appended as quantitative context (and also surfaced via the
			// elapsed_ms field) but the leading sentence names the right
			// next move.
			res.Outcome = ProbeFail
			if msg := tacticNoProgressDiagnostic(req.Tactic.Type); msg != "" {
				res.Diagnostic = fmt.Sprintf("%s (probe budget %dms, elapsed %dms)",
					msg, budgetMs, int(time.Since(start).Milliseconds()))
			} else {
				res.Diagnostic = fmt.Sprintf(
					"%s exhausted without closing the goal (budget %dms, elapsed %dms; %v)",
					req.Tactic.Type, budgetMs, int(time.Since(start).Milliseconds()), runErr)
			}
			return res, nil
		case "by", "by_induction":
			// The composite polls the context between its rounds and
			// rungs and stops with a cut-off once the budget is spent
			// (proof.byCutOff): that is unknown(timeout), with the
			// cut-off's own text. A close that failed inside the budget
			// is a fail with the composite's diagnostics.
			if probeCtx.Err() != nil {
				res.Outcome = ProbeUnknown
				res.Reason = ProbeReasonTimeout
				res.Diagnostic = byProbeTimeoutDiagnostic(req.Tactic.Type, budgetMs, s.env.CnfRefuterTimeout, runErr)
				return res, nil
			}
			res.Outcome = ProbeFail
			res.Diagnostic = runErr.Error()
			return res, nil
		default:
			// Structural / unification tactics: clean error = applicability
			// just doesn't hold (or, for lemma_key, the key names no entry,
			// or the session's own target). Strong fail with the specific
			// reason.
			res.Outcome = ProbeFail
			res.Diagnostic = runErr.Error()
			return res, nil
		}
	}

	// Success. Run the same auto-match pipeline that ApplyStep runs
	// post-tactic, but against the clone — so probe's predicted Subgoals /
	// Effect match what apply would commit. Without this step probe and
	// apply diverge whenever a cited entry's reproduction subgoal closes
	// by type-instance match, leaving the agent to reverse-engineer
	// "where did the second branch go" across multiple RPCs.
	//
	// We use a scratch ThmCache so that probe stays non-destructive against
	// session state (s.autoMatchCache).
	res.Outcome = ProbeSuccess

	// A `by` / `by_induction` close pushes its closer and recorder-rows
	// diagnostics onto the session's carry buffer (applyByOnClone). Probe
	// never commits the clone, but it surfaces those reports so an author
	// reads the closer and what a recording would write WITHOUT an apply +
	// restore — the gap that made comparing three spellings' key cost take
	// an apply and a restore each. Drain the buffer so a probe leaves no
	// diagnostic behind for a later apply (runTacticOnClone resets it on
	// entry too).
	for _, d := range s.pendingApplyDiagnostics {
		switch d.Type {
		case DiagByCloser:
			res.ByCloser = strings.TrimPrefix(d.Message, "Closed by: ")
		case DiagByRecords:
			res.Records = d.Message
		case DiagByWhistle:
			res.Whistle = d.Message
		}
	}
	s.pendingApplyDiagnostics = nil
	if !clone.Proved() {
		roots := []*proof.GoalStackNode{clone}
		scratchCache := &proof.ThmCache{}
		if req.Tactic.LemmaKey != "" && (req.Tactic.Type == "lemma" || req.Tactic.Type == "lean_rw") {
			if lemmaEntry, ok := registryEntry(req.Tactic.LemmaKey); ok {
				res.AutoMatched = append(res.AutoMatched,
					s.applyAutoMatchTypeInstanceOnRoots(roots, core.PropKey(req.Tactic.LemmaKey),
						lemmaEntry.Statement().Prop, []string{lemmaEntry.Name}, scratchCache)...)
			}
		}
		res.AutoMatched = append(res.AutoMatched, s.applyAutoMatchOnRoots(roots, scratchCache)...)
	}

	if clone.Proved() {
		res.Effect = "close"
	} else {
		leaves := clone.UnsolvedLeaves()
		for _, leaf := range leaves {
			res.Subgoals = append(res.Subgoals, ProbeSubgoal{
				Statement: prop.PrintProp(leaf.Goal),
				Changes:   computeGoalChanges(entry.node.Goal, leaf.Goal),
			})
		}
		// Share the apply-side classifier so the boundary cases (notably
		// "noop" vs "simplify" when the sole subgoal is α-equivalent to
		// the input) report the same value. classifyEffect operates on
		// ProducedSubgoal, but it only reads .Changes, so a trivial
		// re-shape is sufficient — see engine.go.
		shaped := make([]ProducedSubgoal, len(res.Subgoals))
		for i, sg := range res.Subgoals {
			shaped[i] = ProducedSubgoal{Changes: sg.Changes}
		}
		res.Effect = classifyEffect(shaped)
	}
	return res, nil
}

// computeGoalChanges returns the structural diff from `before` to `after`,
// comparing hyps and conclusion by α-equivalence. Hyps are stored in
// canonical sort order (see core.makeStatementFromOrderedHyps) so set-difference
// is well-defined: a hyp appears in `dropped` iff no `after` hyp is α-equal
// to it, symmetrically for `added`. Conclusion comparison is direct
// `Term.AlphaEquals`.
func computeGoalChanges(before, after core.Prop) GoalChanges {
	beforeHyps := before.Hyps()
	afterHyps := after.Hyps()
	dropped := 0
	for _, h := range beforeHyps {
		found := false
		for _, a := range afterHyps {
			if a.AlphaEquals(h) {
				found = true
				break
			}
		}
		if !found {
			dropped++
		}
	}
	added := 0
	for _, h := range afterHyps {
		found := false
		for _, b := range beforeHyps {
			if b.AlphaEquals(h) {
				found = true
				break
			}
		}
		if !found {
			added++
		}
	}
	return GoalChanges{
		HypsAdded:         added,
		HypsDropped:       dropped,
		ConclusionChanged: !before.Conclusion().AlphaEquals(after.Conclusion()),
	}
}

// byProbeTimeoutDiagnostic is a `by` / `by_induction` probe's timeout
// text: it names the probe budget the close ran under AND the session
// refuter budget an apply of the same move would run under, so a close
// cut off at the shorter probe budget is not read as a failed close. A
// probe runs the CNF refuter at its own (small) budget; apply runs it at
// the session's env.CnfRefuterTimeout.
func byProbeTimeoutDiagnostic(tacticType string, budgetMs int, applyBudget time.Duration, cause error) string {
	return fmt.Sprintf("%s did not finish within the %dms probe budget: %v\n  "+
		"unknown(timeout) at %dms; apply runs the CNF refuter under the session budget (%s), not the "+
		"probe budget — a close cut off here can still close under apply (raise budget_ms, or apply it).",
		tacticType, budgetMs, cause, budgetMs, applyBudget)
}
