// File: lean_tactics.go
//
// LEAN-style ministep tactics. Each is a thin wrapper around existing
// kernel primitives (Refl/EqSym/EqTrans/PropApply/Contradict/FunEq/...)
// packaged as a single SubGoals-returning tactic so it can be a
// first-class agent move via the engine `apply`/`probe` RPCs.
//
// Naming follows the LEAN cheat-sheet (assumption / refl / left / right /
// funext / by_contra / symm / subst / trans / congr); semantics are
// scoped to what a LEAN-fluent agent expects from the same name.

package tactic

import (
	"context"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// AssumptionTactic closes the goal when the conclusion is a hypothesis:
// α-equal to one, or βη-equal to one — the normal form identifies
// `g(λx. f(x))` with `g(f)`, and so does this move, through the kernel's
// own conversion (prop.BetaEtaRefl) rather than a search. This is the
// "h ⊢ h" branch of simplestTrivialTactic repackaged as a standalone
// tactic so the agent can name the move directly without invoking the
// broader trivial cleanup pipeline.
func AssumptionTactic(goal Prop) *SubGoals {
	concl := goal.Conclusion()
	for i := range goal.NumHyps() {
		if goal.Hyp(i).AlphaEquals(concl) {
			return MakeEmptySubGoals(goal, prop.Assume(concl).AsThmCert())
		}
	}
	for i := range goal.NumHyps() {
		h := goal.Hyp(i)
		if eq := prop.BetaEtaRefl(concl, h); eq != nil {
			// concl = h, so h ⊢ h carries over to h ⊢ concl.
			return MakeEmptySubGoals(goal, eq.EqSym().EqMP(prop.Assume(h)).AsThmCert())
		}
	}
	return nil
}

// ReflTactic closes the goal when the conclusion is `t = t` for some
// term t (after α-equivalence on the two sides).
func ReflTactic(goal Prop) *SubGoals {
	l, r, ok := MatchesEQ(goal.Conclusion())
	if !ok || !l.AlphaEquals(r) {
		return nil
	}
	return MakeEmptySubGoals(goal, core.Refl(l).AsThmCert())
}

// LeftTactic peels the right disjunct: ⊢ A∨B → ⊢ A. Preserves all hyps.
// The reconstruct uses prop.ConclOR0(A,B): `A ⊢ A∨B`.
func LeftTactic(goal Prop) *SubGoals {
	a, b, ok := ext.MatchesOR(goal.Conclusion())
	if !ok {
		return nil
	}
	goal0 := MakeProp(a, goal.Hyps()...)
	reconstruct := func(thms ...Prop) Prop {
		if thms[0].Conclusion().Equals(F) {
			return thms[0]
		}
		return prop.ConclOR0(a, b).DeriveHypFrom(thms[0])
	}
	return MakeSubGoals(goal, reconstruct, goal0)
}

// RightTactic peels the left disjunct: ⊢ A∨B → ⊢ B. Preserves all hyps.
func RightTactic(goal Prop) *SubGoals {
	a, b, ok := ext.MatchesOR(goal.Conclusion())
	if !ok {
		return nil
	}
	goal0 := MakeProp(b, goal.Hyps()...)
	reconstruct := func(thms ...Prop) Prop {
		if thms[0].Conclusion().Equals(F) {
			return thms[0]
		}
		return prop.ConclOR1(a, b).DeriveHypFrom(thms[0])
	}
	return MakeSubGoals(goal, reconstruct, goal0)
}

// FunextTactic transforms `⊢ f = g` (with function-typed sides) into the
// fully pointwise form `⊢ ∀x.∀y…. f(x,y,…) = g(x,y,…)` via
// DeepFunEqRewrite Conclusion-only — does not rewrite hypotheses.
//
// Returns nil when the conclusion is not an equality, when the sides are not
// function-typed, or when the rewrite has nothing to do (e.g. both sides are
// already lambdas with α-identical bodies).
func FunextTactic(goal Prop) *SubGoals {
	w := prop.DeepFunEqRewrite(goal.Conclusion())
	if w == nil {
		return nil
	}
	goal0 := MakeProp(Rhs(w), goal.Hyps()...)
	reconstruct := func(thms ...Prop) Prop {
		if thms[0].Conclusion().Equals(F) {
			return thms[0]
		}
		return w.EqSym().EqMP(thms[0])
	}
	return MakeSubGoals(goal, reconstruct, goal0)
}

// ByContraTactic transforms `⊢ G` (G ≠ ⊥) into `¬G ⊢ ⊥`. Reconstruct
// re-derives `⊢ G` from the contradiction-of-negation via NegHyp +
// double-negation elimination. Returns nil when the conclusion is
// already ⊥ (no progress) or when the negation is α-equal to an
// existing hyp (also no progress).
func ByContraTactic(goal Prop) *SubGoals {
	concl := goal.Conclusion()
	if concl.Equals(F) {
		return nil
	}
	negConcl := Not(concl)
	if goal.HasHyp(negConcl) {
		return nil
	}
	goal0 := MakeProp(F, append(goal.Hyps(), negConcl)...)
	reconstruct := func(thms ...Prop) Prop {
		// thms[0]: Γ, ¬G ⊢ ⊥. Re-derive Γ ⊢ G.
		p := WrapProp(thms[0])
		if !p.HasHyp(negConcl) {
			// Subgoal closed without using the negated hyp — already
			// stronger than what we need (its hyps ⊆ goal.Hyps).
			return p
		}
		// p.NegHyp(negConcl) : Γ ⊢ ¬¬G; rewrite ¬¬G → G.
		return prop.DoubleNeg(concl).EqMP(p.NegHyp(negConcl))
	}
	return MakeSubGoals(goal, reconstruct, goal0)
}

// SymmTactic transforms `⊢ a = b` into `⊢ b = a`. Reconstruct flips
// the proven equality back via core.EqSym. Returns nil when the
// conclusion is not an equality, or when both sides are α-equal
// (no progress — refl already closes the goal).
func SymmTactic(goal Prop) *SubGoals {
	a, b, ok := MatchesEQ(goal.Conclusion())
	if !ok || a.AlphaEquals(b) {
		return nil
	}
	goal0 := MakeProp(Eq(b, a), goal.Hyps()...)
	reconstruct := func(thms ...Prop) Prop {
		if thms[0].Conclusion().Equals(F) {
			return thms[0]
		}
		return WrapProp(thms[0]).EqSym()
	}
	return MakeSubGoals(goal, reconstruct, goal0)
}

// SubstTactic substitutes using hypothesis at index `hypIndex`. The
// hypothesis must be an equality whose LHS or RHS is a free variable
// (the precondition for eqSimplify to make progress). Returns nil
// when hypIndex is out of range, when the hyp isn't an equality, or
// when eqSimplify produces no useful simplification.
func SubstTactic(hypIndex int) Tactic {
	return func(goal Prop) *SubGoals {
		if hypIndex < 0 || hypIndex >= goal.NumHyps() {
			return nil
		}
		eq := goal.Hyp(hypIndex)
		if _, _, ok := MatchesEQ(eq); !ok {
			return nil
		}
		return eqSimplify(fullSearch, new(prop.PreCNFCache), goal, eq, false, false)
	}
}

// RwHypTactic is the directed rewrite-to-fixpoint tactic — the engine
// counterpart of Lean's `rw [h] at *`
// (session tactic `rw`, ministep `_RwStep`, proto tag 47). Given the
// equality hyp `a = b` at hypIndex, it rewrites a→b (b→a when flip)
// across the goal's conclusion AND all other hyps, descending into every
// subterm position — relation-atom arguments and opaque function
// arguments included — repeated until no occurrence of the oriented LHS
// remains. One subgoal, in which the equality hyp stands as it stood,
// in either direction.
//
// Contrast with the adjacent moves:
//   - subst (SubstTactic) rewrites exactly ONE target (the first hyp or
//     the conclusion the rewrite touches), auto-orients the equality
//     bigger→smaller, and rejects non-shrinking rewrites; the agent
//     cannot pick the direction and must re-invoke per target with
//     shifting hyp indices.
//   - congr_arg pushes the equality under ONE function layer per call.
//   - rw is the direction-controlled fixpoint closure of both: one
//     ministep replaces the manual congr_arg-per-layer / subst-per-target
//     loop.
//
// v1 scope decisions (deliberate):
//   - Structural matching only (eqSimplify with unifyEq=false). A
//     ∀-quantified equation hyp is rejected at the MatchesEQ gate:
//     unify-based matching routes through ext/unify's wall-clock default
//     budget (DefaultUnifyTimeout), which would make replay
//     timing-sensitive (the cnf-replay unify-timeout flake). Structural
//     matching keeps the step a deterministic pure function of
//     (goal, hypIndex, flip).
//   - allowExpand=true: the chosen direction is preserved verbatim — no
//     bigger-side swap, no size guard — so expansion-style rewrites
//     (`d → nat_dist(m,n)`) work.
//
// Termination: a self-expanding rule (oriented LHS occurs in the
// oriented RHS, e.g. `x = f(x)`) is refused outright by EqRewrite's
// ext.IsSub guard, so every successful pass strictly decreases the
// number of LHS occurrences outside the equality hyp itself and the
// fixpoint completes; the driver additionally caps passes at the goal's
// total term size (occurrences can never exceed it).
//
// Returns nil when hypIndex is out of range, the hyp is not a top-level
// equality, both sides are α-equal, the rule is self-expanding, or no
// occurrence of the oriented LHS rewrites anywhere.
func RwHypTactic(hypIndex int, flip bool) Tactic {
	return RwHypTacticUntil(context.Background(), hypIndex, flip)
}

// RwHypTacticUntil is RwHypTactic cut off by ctx: the context is polled
// before each pass of the fixpoint after the first, and a done context
// raises a utils.Cut there. One pass is the unit a cut waits for.
func RwHypTacticUntil(ctx context.Context, hypIndex int, flip bool) Tactic {
	stop := utils.Stopper(ctx)
	return func(goal Prop) *SubGoals {
		if hypIndex < 0 || hypIndex >= goal.NumHyps() {
			return nil
		}
		eq := goal.Hyp(hypIndex)
		l, r, ok := MatchesEQ(eq)
		if !ok || l.AlphaEquals(r) {
			return nil
		}
		if !flip {
			return rwFixpoint(stop, goal, eq)
		}
		// The driver keeps the equality it rewrites with and rewrites
		// every other hypothesis, so it runs on a cut goal in which the
		// flipped equality STANDS IN for the original: left beside it,
		// the original would be one more target, rewritten to `a = a`.
		// The child gets the original back in the flipped one's place
		// (beside it, where the goal held both).
		flipped := Eq(r, l)
		hadFlipped := goal.HasHyp(flipped)
		cut := MakeProp(goal.Conclusion(), append(hypsExcept(goal, eq, flipped), flipped)...)
		inner := rwFixpoint(stop, cut, flipped)
		if inner == nil {
			return nil
		}
		children := make([]Prop, inner.Size())
		restored := make([]bool, inner.Size())
		successors := make([][]int, inner.Size())
		for i := range children {
			child := inner.ChildGoal(i)
			if !child.HasHyp(flipped) {
				children[i] = child
			} else {
				hyps := append(hypsExcept(child, eq, flipped), eq)
				if hadFlipped {
					hyps = append(hyps, flipped)
				}
				children[i] = MakeProp(child.Conclusion(), hyps...)
				restored[i] = true
			}
			successors[i] = rwFlipSuccessors(goal, cut, child, children[i], inner.HypSuccessors(i))
		}
		// The two orientations prove each other by EqSym, and DeriveTrans
		// swaps one for the other as a hypothesis.
		reconstruct := func(thms ...Prop) Prop {
			innerThms := make([]Prop, len(thms))
			for i, thm := range thms {
				if restored[i] && thm.HasHyp(eq) {
					// flipped ⊢ eq discharges the child's original
					// equality against the driver's own.
					thm = prop.Assume(flipped).EqSym().DeriveTrans(thm)
				}
				innerThms[i] = thm
			}
			p := inner.Reconstruct(innerThms...)
			if hadFlipped || !p.HasHyp(flipped) {
				// Either the goal holds the flipped equality itself, or
				// the proof closed without it (e.g. via ⊥) — already at
				// least as strong as the parent needs.
				return p
			}
			// eq ⊢ flipped discharges the cut goal's stand-in.
			return prop.Assume(eq).EqSym().DeriveTrans(p)
		}
		return MakeTrackedSubGoals(goal, reconstruct, successors, children...)
	}
}

// rwFlipSuccessors is the flipped rewrite's provenance for one child:
// goal's hypotheses through the cut goal, the driver's own provenance
// into its child, and the restoration into restored. The equality the
// step rewrites with is not in the cut (its flipped form stands in for
// it) and is located in restored directly, where the restoration put it
// back; every other hypothesis follows its cut slot. Nil when the
// driver recorded none.
func rwFlipSuccessors(goal, cut, innerChild, restored Prop, innerSucc []int) []int {
	if innerSucc == nil {
		return nil
	}
	succ := make([]int, goal.NumHyps())
	for i := range goal.NumHyps() {
		h := goal.Hyp(i)
		c := hypIndexOf(cut, h)
		switch {
		case c == NoSuccessor:
			succ[i] = hypIndexOf(restored, h)
		case innerSucc[c] == NoSuccessor:
			succ[i] = NoSuccessor
		default:
			succ[i] = hypIndexOf(restored, innerChild.Hyp(innerSucc[c]))
		}
	}
	return succ
}

// hypsExcept is p's hypotheses without the ones α-equal to a dropped
// term, in p's order.
func hypsExcept(p Prop, dropped ...Term) []Term {
	kept := make([]Term, 0, p.NumHyps())
hyps:
	for h := range p.HypIter() {
		for _, d := range dropped {
			if h.AlphaEquals(d) {
				continue hyps
			}
		}
		kept = append(kept, h)
	}
	return kept
}

// rwFixpoint drives eqSimplify (structural, direction-preserving,
// expansion-allowed) to fixpoint. Each eqSimplify call rewrites the
// first target (hyp or conclusion) the rule touches; expanding the
// single child with the same step reaches the next target. The pass
// budget is the goal's total term size — a hard upper bound on LHS
// occurrences — making non-termination impossible even if a cleanup
// rewrite were to manufacture a fresh occurrence. (Self-expanding rules
// never get this far: EqRewrite's ext.IsSub guard refuses them, so the
// first oneStep already returns nil.) stop, when not nil, is polled
// before each pass after the first.
//
// The passes are one run (_SearchMode.asRun): a pass rewrites one target
// and leaves the others as they stood, so the next pass reads their
// normal forms and computes only the rewritten one's.
func rwFixpoint(stop func(string), goal Prop, eq Term) *SubGoals {
	run := fullSearch.asRun()
	oneStep := func(p Prop) *SubGoals {
		if !p.HasHyp(eq) {
			return nil
		}
		return eqSimplify(run, run.ruleCache(), p, eq, false, true)
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
		if stop != nil {
			stop("inside rw, before a pass of its fixpoint")
		}
		next := Tactic(oneStep).expand(s)
		if next == s {
			break
		}
		s = next
	}
	return s
}

// TransTactic transforms `⊢ a = c` into two subgoals `⊢ a = b` and
// `⊢ b = c` using the agent-supplied middle term `b`. Reconstruct
// chains them via core.EqTrans. Returns nil when the conclusion is
// not an equality, when `b` doesn't share the LHS's type, or when
// `b` α-equals one of the sides (no progress — symm or refl applies
// directly instead).
func TransTactic(middle Term) Tactic {
	return func(goal Prop) *SubGoals {
		a, c, ok := MatchesEQ(goal.Conclusion())
		if !ok {
			return nil
		}
		if !a.Type().Equals(middle.Type()) {
			return nil
		}
		if middle.AlphaEquals(a) || middle.AlphaEquals(c) {
			return nil
		}
		goal0 := MakeProp(Eq(a, middle), goal.Hyps()...)
		goal1 := MakeProp(Eq(middle, c), goal.Hyps()...)
		reconstruct := func(thms ...Prop) Prop {
			if thms[0].Conclusion().Equals(F) {
				return thms[0]
			}
			if thms[1].Conclusion().Equals(F) {
				return thms[1]
			}
			return WrapProp(thms[0]).EqTrans(thms[1])
		}
		return MakeSubGoals(goal, reconstruct, goal0, goal1)
	}
}

// CongrTactic decomposes an equality goal `⊢ s = t` structurally.
// Two phases:
//
//	Phase 1 (TermDiff):  if prop.TermDiff finds a non-trivial single-
//	    point replacement, produce one subgoal `⊢ l = r` and
//	    reconstruct via the EqRewrite candidate.
//
//	Phase 2 (application spine): when phase 1 returns the trivial
//	    whole-term fallback, check whether s and t are both AppliedTerm
//	    chains with the same head. If so, decompose into one subgoal
//	    per differing argument; α-equal args drop out and reconstruct
//	    via core.Refl.
//
// Returns nil when neither phase fires (heads differ AND no single-
// point replacement found).
func CongrTactic(goal Prop) *SubGoals {
	s, t, ok := MatchesEQ(goal.Conclusion())
	if !ok || s.AlphaEquals(t) {
		return nil
	}

	// Phase 1: TermDiff single-point candidate. TermDiff(s, t) returns
	// (left, right) where exactly one is non-nil (the validated rewrite
	// from one side). When it falls back to whole-term replacement, the
	// returned PropWrapper has hyps `s = t` or `t = s`; we detect that
	// and skip to phase 2.
	if subGoals := congrPhase1(goal, s, t); subGoals != nil {
		return subGoals
	}

	// Phase 2: spine decomposition for same-headed AppliedTerms.
	if subGoals := congrPhase2(goal, s, t); subGoals != nil {
		return subGoals
	}

	return nil
}

// congrPhase1 tries TermDiff for a fine-grained single-subterm
// replacement. The returned PropWrapper rewrites `s` (or `t`) to the
// other; reconstruct lifts a proof of the candidate equality back to
// `⊢ s = t` via EqRewrite + EqMP.
func congrPhase1(goal Prop, s, t Term) *SubGoals {
	left, right := prop.TermDiff(s, t)
	var w *prop.PropWrapper
	var leftDir bool
	if left != nil {
		w = left
		leftDir = true
	} else if right != nil {
		w = right
	} else {
		return nil
	}
	// w has the form `cand ⊢ s = t` (leftDir) or `cand ⊢ t = s`.
	// `cand` is the equality the agent must prove. If cand is just
	// `s = t` (or `t = s`), TermDiff fell back to whole-term — phase 2
	// (or nothing) handles that case better.
	if w.NumHyps() != 1 {
		return nil
	}
	cand := w.Hyp(0)
	candL, candR, ok := MatchesEQ(cand)
	if !ok {
		return nil
	}
	// Whole-term fallback: candidate equates s and t directly. Bail
	// to phase 2.
	if (candL.AlphaEquals(s) && candR.AlphaEquals(t)) ||
		(candL.AlphaEquals(t) && candR.AlphaEquals(s)) {
		return nil
	}
	goal0 := MakeProp(cand, goal.Hyps()...)
	reconstruct := func(thms ...Prop) Prop {
		if thms[0].Conclusion().Equals(F) {
			return thms[0]
		}
		// thms[0] : Γ ⊢ cand. w : cand ⊢ (s = t) or (t = s).
		// DeriveTrans yields Γ ⊢ s = t (or t = s); flip if needed.
		derived := WrapProp(thms[0]).DeriveTrans(w)
		if !leftDir {
			// w produced `t = s`; symmetrize to `s = t`.
			derived = derived.EqSym()
		}
		return derived
	}
	return MakeSubGoals(goal, reconstruct, goal0)
}

// congrPhase2 decomposes `⊢ s = t` along the application spine. Both s and
// t must be AppliedTerm chains rooted at the same head. Each differing
// argument becomes its own subgoal `⊢ aᵢ = bᵢ`; α-equal args don't
// produce a subgoal — they get reconstructed from Refl.
func congrPhase2(goal Prop, s, t Term) *SubGoals {
	headS, argsS := unfoldApp(s)
	headT, argsT := unfoldApp(t)
	if headS == nil || headT == nil {
		return nil
	}
	if !headS.AlphaEquals(headT) {
		return nil
	}
	if len(argsS) != len(argsT) || len(argsS) == 0 {
		return nil
	}

	// Determine which arg positions actually differ.
	type slot struct {
		needsSubgoal bool
		// For diff slots, holds the subgoal index after dedup.
		subgoalIdx int
	}
	slots := make([]slot, len(argsS))
	var subgoals []Prop
	for i := range argsS {
		if argsS[i].AlphaEquals(argsT[i]) {
			slots[i] = slot{needsSubgoal: false}
			continue
		}
		if !argsS[i].Type().Equals(argsT[i].Type()) {
			// Same head + same arity should imply matching arg types,
			// but be defensive — heads can be polymorphic.
			return nil
		}
		eq := Eq(argsS[i], argsT[i])
		slots[i] = slot{needsSubgoal: true, subgoalIdx: len(subgoals)}
		subgoals = append(subgoals, MakeProp(eq, goal.Hyps()...))
	}
	if len(subgoals) == 0 {
		// All args α-equal — the goal is already refl. Bail; refl
		// handles it directly.
		return nil
	}

	reconstruct := func(thms ...Prop) Prop {
		// Walk the spine left-to-right, building an equality chain via
		// PropApply (congruence on equalities):
		//   ⊢ head = head                         (Refl)
		//   ⊢ head(a₁) = head(b₁)                  (Apply prev arg-eq)
		//   ⊢ head(a₁,a₂) = head(b₁,b₂)            (Apply prev arg-eq)
		//   ...
		var cur Prop = core.Refl(headS)
		for i := range argsS {
			var argEq Prop
			if slots[i].needsSubgoal {
				p := thms[slots[i].subgoalIdx]
				if p.Conclusion().Equals(F) {
					return p
				}
				argEq = p
			} else {
				argEq = core.Refl(argsS[i])
			}
			cur = core.PropApply(cur, argEq)
		}
		return cur
	}
	return MakeSubGoals(goal, reconstruct, subgoals...)
}

// CongrArgTactic is forward congruence on an equality hypothesis: given
// hyps[hypIndex] of the form `a = b` and an agent-supplied function term
// `fn`, it adds the hypothesis `fn(a) = fn(b)` while keeping the original
// equality available (Lean `congrArg`, kernel
// core.PropLeftApply). One subgoal, reconstructed by a DeriveTrans cut —
// structurally identical to instantiateAt (add a derived fact as a hyp,
// discharge it on the way back up).
//
// Returns nil when:
//   - hypIndex is out of range,
//   - hyps[hypIndex] is not an equality,
//   - `fn` is not a function whose domain matches the equality's type, or
//   - the resulting subgoal would alpha-equal the original (fn(a)=fn(b)
//     already in scope — no progress).
//
// Range / shape / type validation also produces typed errors at the
// engine dispatch layer; returning nil here keeps `probe` (which skips
// that pre-validation) behaving like `apply` on bad inputs.
func CongrArgTactic(fn Term, hypIndex int) Tactic {
	return func(goal Prop) *SubGoals {
		if hypIndex < 0 || hypIndex >= goal.NumHyps() {
			return nil
		}
		eq := goal.Hyp(hypIndex)
		a, _, ok := MatchesEQ(eq)
		if !ok {
			return nil
		}
		if !ext.IsFunType(fn.Type()) {
			return nil
		}
		if !ext.MatchesFun(fn.Type())[0].Equals(a.Type()) {
			return nil
		}
		// applied: (a = b) ⊢ fn(a) = fn(b).
		applied := core.PropLeftApply(fn, core.Assume(eq))
		newFact := applied.Conclusion()
		newHyps := append(goal.Hyps(), newFact)
		subgoal := MakeProp(goal.Conclusion(), newHyps...)
		if subgoal.AlphaEquals(goal) {
			// fn(a)=fn(b) already a hyp (or normalized away) — no progress.
			return nil
		}
		reconstruct := func(thms ...Prop) Prop {
			// Subgoal closed without using the added fact — already at
			// least as strong (its hyps ⊆ goal's). Pass through.
			if !thms[0].HasHyp(newFact) {
				return thms[0]
			}
			// applied:  (a=b) ⊢ fn(a)=fn(b)
			// thms[0]:  Γ, (a=b), fn(a)=fn(b) ⊢ C
			// DeriveTrans discharges fn(a)=fn(b); (a=b) is already in Γ.
			return WrapProp(applied).DeriveTrans(thms[0])
		}
		return MakeSubGoals(goal, reconstruct, subgoal)
	}
}

// CongrFunTactic is the dual of CongrArgTactic: given a function-equality
// hypothesis `f = g` at hyps[hypIndex] and an agent-supplied argument
// term `arg`, it adds the hypothesis `f(arg) = g(arg)` (Lean
// `congrFun`, kernel core.PropRightApply). Same one-subgoal DeriveTrans
// cut as CongrArgTactic.
//
// Returns nil under the dual conditions: hypIndex out of range, hyp not
// an equality, the equated sides not functions whose domain matches
// `arg`'s type, or no progress.
func CongrFunTactic(arg Term, hypIndex int) Tactic {
	return func(goal Prop) *SubGoals {
		if hypIndex < 0 || hypIndex >= goal.NumHyps() {
			return nil
		}
		eq := goal.Hyp(hypIndex)
		f, _, ok := MatchesEQ(eq)
		if !ok {
			return nil
		}
		if !ext.IsFunType(f.Type()) {
			return nil
		}
		if !ext.MatchesFun(f.Type())[0].Equals(arg.Type()) {
			return nil
		}
		// applied: (f = g) ⊢ f(arg) = g(arg).
		applied := core.PropRightApply(core.Assume(eq), arg)
		newFact := applied.Conclusion()
		newHyps := append(goal.Hyps(), newFact)
		subgoal := MakeProp(goal.Conclusion(), newHyps...)
		if subgoal.AlphaEquals(goal) {
			return nil
		}
		reconstruct := func(thms ...Prop) Prop {
			if !thms[0].HasHyp(newFact) {
				return thms[0]
			}
			return WrapProp(applied).DeriveTrans(thms[0])
		}
		return MakeSubGoals(goal, reconstruct, subgoal)
	}
}

// unfoldApp peels off all applied-term arg layers, returning the head
// term and the list of args in argument order. Returns (nil, nil) when
// `t` is not an AppliedTerm at all.
func unfoldApp(t Term) (Term, []Term) {
	at, ok := t.AsAppliedTerm()
	if !ok || at.IsZero() {
		return nil, nil
	}
	var args []Term
	cur := t
	for {
		app, ok := cur.AsAppliedTerm()
		if !ok || app.IsZero() {
			break
		}
		args = append([]Term{app.Arg()}, args...)
		cur = app.Fun()
	}
	return cur, args
}
