package tactic

import (
	"context"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// SetTacExpand is the deterministic fixpoint def-expand half of the
// `set_tac` ministep (its rewrite phase): unfold every
// occurrence of the named definitional constants across the goal's
// conclusion AND hypotheses, repeated to fixpoint. The other half — the
// closing CNF refute on the residual — lives in prover._SetTacStep.apply,
// which composes it over this result (env access keeps it out of this
// package).
//
// SHARED EXECUTOR: this one function runs at record time (engine `set_tac`
// dispatch), at emit's CNF collection (cnf_cache collector), and at a
// member's replay (emitted `Do(SetTac(...))`). There is no expansion
// snapshot to drift against — the record/emit/replay-reuse principle.
//
// Determinism contract (replay re-runs this cold and the resulting leaf
// goals key the closing refutes' CNF cache entries — any divergence is a
// strict-mode replay MISS):
//   - consts are processed in SLICE ORDER; the recorder sorts them, replay
//     receives the recorded order verbatim (SetTacProto doc).
//   - per pass, the FIRST const (in slice order) with a firing TryDefExpand
//     wins; the walker inside TryDefExpand is a deterministic structural
//     recursion, and per-occurrence type instantiation (constT.DefThm())
//     is a pure function of the occurrence.
//   - the pass budget is the goal's total term size — same hard bound
//     rwFixpoint uses. Def-expansion of the set vocabulary strictly
//     eliminates occurrences (the def bodies don't reintroduce their own
//     const), so the budget is never the binding constraint; it exists to
//     make non-termination structurally impossible.
//   - ctx is a LIVE-ONLY abort signal (the agent's budget_ms), polled at
//     the fixpoint loop head: on cancellation the expansion stops and the
//     partial SubGoals is returned, so the closing refutes fail fast under
//     the same cancelled ctx and the whole close-or-fail step fails —
//     nothing is recorded, so determinism is unaffected. Replay passes
//     context.Background() and never aborts.
//
// Each TryDefExpand result has children [defEqClaim, rewrittenGoal]; the
// def-eq claim is closed inline with the kernel-issued def thm (an
// AxiomDef — deps-free), so every open child of the returned SubGoals is
// a rewritten goal. Returns nil when no unfold fires at all.
func SetTacExpand(ctx context.Context, goal Prop, consts []core.TermName) *SubGoals {
	oneStep := func(p Prop) *SubGoals {
		for _, name := range consts {
			c := firstConstOccurrence(p, name)
			if c.IsZero() {
				continue
			}
			defThm := c.DefThm()
			if defThm.IsZero() {
				// Not a Type-1 NewConstDef const — nothing to unfold.
				continue
			}
			if prop.IsHilbertConstDef(c) {
				// ε-shaped definition (nat_mod/nat_div class): unfolding to the ε
				// equation is a dead-end rewrite, and the set vocabulary
				// has no such consts anyway. Defensive skip.
				continue
			}
			sg := TryDefExpand(defThm, p)
			if sg == nil {
				continue
			}
			// Close the def-eq claim child with the kernel thm itself. The
			// claim is the statement of defThm verbatim (TryDefExpand's
			// child(0) is lemma.AsProp()), so IsStronger holds exactly.
			closer := Tactic(func(q Prop) *SubGoals {
				if IsStronger(defThm, q) {
					return MakeEmptySubGoals(q, defThm)
				}
				return nil
			})
			return closer.expand(sg)
		}
		return nil
	}

	s := oneStep(goal)
	if s == nil {
		return nil
	}
	budget := goal.Conclusion().Size()
	for h := range goal.HypIter() {
		budget += h.Size()
	}
	for range budget {
		if ctx.Err() != nil {
			// Live budget exhausted mid-expansion: stop here and let the
			// closing refutes fail fast on the same cancelled ctx.
			return s
		}
		next := Tactic(oneStep).expand(s)
		if next == s {
			break
		}
		s = next
	}
	return s
}

// Expand is the exported form of Tactic.expand for composition from the
// prover package (e.g. _SetTacStep composing the closing CNF refute over
// SetTacExpand's residual leaves). Identical semantics: apply t to every
// open child of s, flatten, keep unexpanded children as-is; returns s
// itself when nothing expanded.
func (t Tactic) Expand(s *SubGoals) *SubGoals { return t.expand(s) }

// firstConstOccurrence returns the first (deterministic pre-order,
// conclusion before hyps) ConstTerm occurrence with the given name, or
// nil. The specific occurrence only pins the def thm used as TryDefExpand's
// shape-gate lemma; the walker inside re-instantiates per occurrence, so
// WHICH occurrence we return does not affect the rewrite result — but the
// walk order is still fixed (pre-order) so the recorded lemma child is
// deterministic.
func firstConstOccurrence(p Prop, name core.TermName) core.ConstTerm {
	if c := firstConstIn(p.Conclusion(), name); !c.IsZero() {
		return c
	}
	for h := range p.HypIter() {
		if c := firstConstIn(h, name); !c.IsZero() {
			return c
		}
	}
	return core.ConstTerm{}
}

func firstConstIn(t core.Term, name core.TermName) core.ConstTerm {
	// Structural walk: a term caches no has-constant predicate, and
	// def_expand's own walker likewise recurses unconditionally. Early
	// return on first hit.
	switch t := t.Core().(type) {
	case core.VarTerm:
		return core.ConstTerm{}
	case core.ConstTerm:
		if t.Name() == name {
			return t
		}
		return core.ConstTerm{}
	case core.AppliedTerm:
		if c := firstConstIn(t.Fun(), name); !c.IsZero() {
			return c
		}
		return firstConstIn(t.Arg(), name)
	case core.AbsTerm:
		return firstConstIn(t.Body(), name)
	}
	return core.ConstTerm{}
}

// SortTermNames returns a name-sorted copy — the recorder-side helper that
// pins SetTacProto's const order (see the proto doc: recorded order IS the
// deterministic processing order).
func SortTermNames(names []core.TermName) []core.TermName {
	out := slices.Clone(names)
	slices.Sort(out)
	return out
}
