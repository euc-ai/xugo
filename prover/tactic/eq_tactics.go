/**
 * File: eq_tactics.go
 *
 * Implements equality-based tactics that simplify goals using equational reasoning:
 *
 * - eqSimplify: Applies equality-based simplification to a goal using a hypothesis
 * - eqSimplifyUnder: Automatically identifies and applies equality-based simplifications
 * - eqLemmaTactic: Creates tactics that use equational lemmas to simplify goals
 *
 * The tactics handle equalities in a generalized sense, such as:
 * - Direct equalities, e.g. ∀x.(P(x) = Q(x))
 * - Positive assertions, e.g. ∀x.P(x) (treated as ∀x.(P(x) = ⊤))
 * - Negative assertions, e.g. ∀x.¬P(x) (treated as ∀x.(P(x) = ⊥))
 */

package tactic

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// eqSimplify rewrites the goal using the provided equality term (eq).
// The equality term must satisfy one of these conditions:
//  1. It must be a hypothesis of the goal, OR
//  2. It must be the negated conclusion of the goal, OR
//  3. If the negated conclusion can be simplified by basic rewriting,
//     then eq should be the result of that rewriting.
//
// This function attempts to use the equality to simplify either the
// conclusion or one of the hypotheses of the goal, potentially reducing
// the complexity of the proof obligation.
// When unifyEq is false, it uses contextEq + EqRewrite (structural matching).
// When unifyEq is true, it uses ContextAbsEq + unifyEqRewrite (unification-based matching),
// which enables β-matching through ∀-quantified variables.
// The equality is interpreted in a general sense, such as:
// ∀x.(P(x) = Q(x)),
// ∀x.P(x) which is equivalent to ∀x.(P(x) = ⊤),
// ∀x.¬P(x) which is equivalent to ∀x.(P(x) = ⊥).
//
// allowExpand controls the size-monotonicity guard. When false (the
// default for fixpoint contexts like BasicTactics / TrivialSimplify),
// rewrites whose RHS is not strictly smaller are rejected — this
// prevents nontermination on hyps shaped like `f(x) = ... f(x) ...`
// when the merged tactic re-enters. When true (one-shot agent-driven
// callers like the explicit-rewrite path), the guard is bypassed,
// admitting expansion-style equational lemmas (extensionality,
// definitional unfolding, COND distribution).
//
// preCNF is the pre-CNF normalization cache the eq's rewrite reads for
// its pre-CNF fallback (see prop.ContextEqRewriteOpt). A caller
// that runs eqSimplify over several equalities of ONE goal passes one
// cache for all of them: the targets — the goal's other hypotheses and
// its conclusion — are the same at each call, so their normal forms are
// computed once per goal, not once per equality. A caller that is a step
// of a fixpoint passes the mode's (_SearchMode.ruleCache), which stands
// in front of the run's: the next goal of the run keeps most of this
// one's hypotheses, and their normal forms are read, not computed again.
//
// mode is the search eqSimplify is a step of. The equality's rewrite
// runs under the mode's deadline (prop.ContextEqRewriteOptUnder), and
// what it answers once the deadline is done is read by no one: the
// search is abandoned (abandonIfDone) where a call of the rewrite
// returns.
func eqSimplify(mode _SearchMode, preCNF *prop.PreCNFCache, goal Prop, eq Term, unifyEq, allowExpand bool) *SubGoals {
	renamedEq := eq
	if u := prop.AdjustUnivVars(goal.HasFreeName)(eq); u != nil {
		renamedEq = Rhs(u)
	}

	nConcl := Not(goal.Conclusion())
	nConclProp := prop.BasicRewrite(nConcl)

	Assert(goal.HasHyp(eq) ||
		(nConclProp == nil && eq.Equals(nConcl)) ||
		(nConclProp != nil && eq.Equals(Rhs(nConclProp))))

	rewrite := prop.ContextEqRewriteOptUnder(mode.deadline, preCNF, renamedEq, unifyEq, allowExpand)

	// Try to simplify a hyp or the conclusion of the goal using eq.
	for j, tj := range append(goal.Hyps(), goal.Conclusion()) {
		if tj.Equals(F) || tj.Equals(eq) {
			continue
		}
		if tj.Equals(goal.Conclusion()) && !goal.HasHyp(eq) {
			// eq comes from the conclusion itself.
			// no need to simplify the conlusion by itself.
			continue
		}

		w := rewrite(tj)
		mode.abandonIfDone()
		if w == nil {
			continue
		}

		w = w.RewriteConclRhs(prop.BasicRewrite)
		if !allowExpand && Rhs(w).Size() >= tj.Size() && !settlesAgainstContext(goal, tj, Rhs(w)) {
			continue
		}
		v := prop.ReduceSizeRewriteRecur(prop.ChainRewrites(
			rewrite,
			prop.BasicRewrite), Rhs(w))
		mode.abandonIfDone()
		if v != nil {
			w = w.EqTrans(v)
		}

		// The one target is rewritten; every other hypothesis, the
		// equality included, stands as it stood.
		var goal0 Prop
		var successors []int
		if tj.Equals(goal.Conclusion()) {
			goal0 = MakeProp(Rhs(w), goal.Hyps()...)
			successors = keptSuccessors(goal, goal0)
		} else {
			images := hypImages(goal, j, Rhs(w))
			goal0 = makeImageProp(goal.Conclusion(), images)
			successors = hypSuccessorsOf(goal0, images)
		}
		reconstruct := func(thms ...Prop) Prop {
			if IsStronger(thms[0], goal) {
				return thms[0]
			}
			if !thms[0].Conclusion().AlphaEquals(goal.Conclusion()) &&
				!thms[0].Conclusion().Equals(F) {
				return w.EqSym().EqMP(thms[0])
			}
			Assert(thms[0].HasHyp(Rhs(w)))
			// replace the new hyp by the original one.
			p := w.LeftAssume().DeriveTrans(thms[0])

			if p.Conclusion().Equals(F) {
				if nConclProp != nil &&
					p.HasHyp(Rhs(nConclProp)) &&
					!goal.HasHyp(Rhs(nConclProp)) {
					p = nConclProp.
						LeftAssume().
						DeriveTrans(p).
						NegHyp(nConcl).
						RewriteConcl(prop.DoubleNegRewrite)
				} else if p.HasHyp(nConcl) {
					p = p.NegHyp(nConcl).RewriteConcl(prop.DoubleNegRewrite)
				}
				return p
			}

			Assert(p.Conclusion().AlphaEquals(goal.Conclusion()))
			if nConclProp != nil && p.HasHyp(Rhs(nConclProp)) {
				p = nConclProp.LeftAssume().DeriveTrans(p)
			}
			if p.HasHyp(nConcl) {
				p = p.
					Contraposition(nConcl).
					RewriteConcl(prop.DoubleNegRewrite)
			}
			return p
		}
		return MakeTrackedSubGoals(goal, reconstruct, [][]int{successors}, goal0)
	}
	return nil
}

// settlesAgainstContext reports whether rewriting target, a hypothesis
// or the conclusion of goal, to result closes the leaf: the conclusion
// rewritten into a hypothesis the goal holds, or its symmetric, and a
// hypothesis rewritten into the conclusion or its symmetric, close by
// assumption or by the next rewrite, `a = a`. The size-monotone guard
// admits such a rewrite although it does not shrink its target: an
// equation between two sides of one size could otherwise rewrite in
// neither direction, and two spellings of one value would never meet.
// It admits no other: a hypothesis rewritten into the symmetric of
// another leaves both standing, and a later rewrite could orient it
// back.
func settlesAgainstContext(goal Prop, target, result Term) bool {
	var symmetric Term
	if l, r, ok := MatchesEQ(result); ok {
		symmetric = core.Eq(r, l)
	}
	matches := func(t Term) bool {
		return t.AlphaEquals(result) || (symmetric != nil && t.AlphaEquals(symmetric))
	}
	if target.Equals(goal.Conclusion()) {
		return goal.AnyHyp(matches)
	}
	return matches(goal.Conclusion())
}

// eqSimplifyUnder simplifies the goal by using one hypothesis (or the negated conclusion) to simplify
// the goal if it contains an equality, as a component of a search in
// mode (eqSimplify).
// The equality is interpreted in a strict sense. No unification is used in rewriting.
// The tactic works by:
// 1. Converting the goal to negation normal form if the conclusion is not ⊥
// 2. Iterating through all hypotheses to find potential equalities
// 3. Applying the equality to simplify other parts of the goal if possible
// 4. Returning a simplified subgoal if successful, or nil if no simplification is possible
func eqSimplifyUnder(mode _SearchMode) Tactic {
	return func(goal Prop) *SubGoals {
		_goal := WrapProp(goal)
		if !goal.Conclusion().Equals(F) {
			_goal = _goal.NegConcl()
			if u := prop.BasicRewrite(Not(goal.Conclusion())); u != nil {
				_goal = u.RightAssume().DeriveTrans(_goal)
			}
		}

		preCNF := mode.ruleCache()
		for h := range _goal.HypIter() {
			if subGoal := eqSimplify(mode, preCNF, goal, h, false, false); subGoal != nil &&
				!subGoal.ChildGoal(0).AlphaEquals(goal) {
				return subGoal
			}
		}
		return nil
	}
}

// unifyEqSimplifyTactic is unifyEqSimplifyUnder in the unbounded search,
// as a tactic on its own: no run stands behind it, and each call reads
// the normal forms it needs for itself.
var unifyEqSimplifyTactic = unifyEqSimplifyUnder(fullSearch)

// unifyEqSimplifyUnder simplifies the goal by using one hypothesis (or the negated conclusion) to simplify
// the goal if it contains an equality, as a component of a search in
// mode: its unifications end with the mode's deadline, and the search is
// then abandoned (eqSimplify).
// The equality is interpreted in a general sense, using unification for rewriting.
// The tactic works by:
// 1. Converting the goal to negation normal form if the conclusion is not ⊥
// 2. Iterating through all hypotheses to find potential equalities
// 3. Applying the equality to simplify other parts of the goal if possible
// 4. Returning a simplified subgoal if successful, or nil if no simplification is possible
func unifyEqSimplifyUnder(mode _SearchMode) Tactic {
	return func(goal Prop) *SubGoals {
		_goal := WrapProp(goal)
		if !goal.Conclusion().Equals(F) {
			_goal = _goal.NegConcl()
			if u := prop.BasicRewrite(Not(goal.Conclusion())); u != nil {
				_goal = u.RightAssume().DeriveTrans(_goal)
			}
		}

		preCNF := mode.ruleCache()
		for h := range _goal.HypIter() {
			if subGoal := eqSimplify(mode, preCNF, goal, h, true, false); subGoal != nil &&
				!subGoal.ChildGoal(0).AlphaEquals(goal) {
				return subGoal
			}
		}
		return nil
	}
}

// Transforms a prop to the form of ..., ¬c ⊢ ⊥
// Also returns PropFunc to reconstruct the original prop.
func negConcl(p Prop) (*PropWrapper, utils.EndoFunc[Prop]) {
	if p.Conclusion().Equals(F) {
		return WrapProp(p), utils.IdentityFunc
	}

	reconstruct := func(w Prop) Prop {
		Assert(w.Conclusion().Equals(F))
		nConcl := Not(p.Conclusion())
		if w.HasHyp(nConcl) {
			w = prop.DoubleNeg(p.Conclusion()).EqMP(WrapProp(w).NegHyp(nConcl))
		}
		return w
	}

	return WrapProp(p).NegConcl(), reconstruct
}

// eqLemmaTactic creates a tactic that uses a lemma containing an equality to simplify a goal.
// The function takes a lemma as input and returns a tactic function that:
// 1. Converts both the lemma and goal to negation normal form
// 2. Checks if the lemma directly implies the goal or is equivalent to it
// 3. Identifies the equality hypothesis in the lemma (which may be in general forms as in eqSimplify)
// 4. Applies this equality to rewrite and simplify the goal
// 5. Removes the equality hypothesis from the resulting goal if possible
//
// allowExpand is forwarded to eqSimplify. The default-false form
// (eqLemmaTactic) preserves the size-monotone semantics that internal
// fixpoint chains rely on. The expansion-allowed form
// (eqLemmaTacticExpand) is the entry point for explicit one-shot
// agent-driven rewrites (lean_rw / def_expand), where expansion-style
// equational lemmas (extensionality, definitional unfolding, COND
// distribution) are routine.
func eqLemmaTactic(lemma Prop) Tactic {
	return eqLemmaTacticOpt(fullSearch, lemma, false)
}

// eqLemmaTacticExpand is eqLemmaTactic with the size-decrease guard
// disabled. Use only from one-shot, agent-driven callers — never from
// inside a fixpoint chain (the eq witness would be re-applied to its
// own RHS and could expand without bound).
func eqLemmaTacticExpand(lemma Prop) Tactic {
	return eqLemmaTacticOpt(fullSearch, lemma, true)
}

// eqLemmaTacticOpt is the tactic of eqLemmaTactic and eqLemmaTacticExpand
// as a step of a search in mode (eqSimplify, mergeTacticsWithin).
func eqLemmaTacticOpt(mode _SearchMode, lemma Prop, allowExpand bool) Tactic {
	lemma0, _ := negConcl(lemma)
	tactic := func(goal Prop) *SubGoals {
		goal0, goalReconstruct := negConcl(goal)

		if lemma0.AlphaEquals(goal0) {
			return nil
		}
		if IsStronger(lemma0, goal0) {
			reconstruct := func(thms ...Prop) Prop {
				provedLemma, _ := negConcl(thms[0])
				return goalReconstruct(provedLemma)
			}
			return MakeSubGoals(goal, reconstruct, lemma)
		}

		// Identify the lemma's missing equality/iff witness. For each
		// lemma hyp:
		//   - raw α-match in goal0: skip (matched cheaply).
		//   - else, try a pre-CNF bridge ⊢ h_lemma = h_goal (when both
		//     sides share the same pre-CNF normal form): record the bridge
		//     and skip — the reconstruction substitutes h_lemma for h_goal
		//     so the final proof's hyps stay inside goal0.Hyps() raw.
		//   - else: candidate eq witness. There must be exactly one.
		//
		// The bridge path is what makes normalized matching sound here:
		// without it, widening to normalized matching produces
		// reconstructions whose hyps are only normalized-equal to goal
		// hyps, failing IsStronger on the parent's MakeSubGoals assertion. With the explicit ⊢ h = g
		// witness threaded through, every matched-but-not-raw hyp gets
		// rewritten to its raw goal counterpart in the proved lemma.
		var negEqTerm Term
		var hypBridges []*PropWrapper
		var goalPreCNFHyps map[core.TermKey]Term
		// Local cache: each hyp from lemma0 and goal0 is keyed at most
		// once across this matching pass. Scope is the per-call match
		// loop; released on return.
		preCNFCache := &prop.PreCNFCache{}
		for h := range lemma0.HypIter() {
			if goal0.HasHyp(h) {
				continue
			}
			if goalPreCNFHyps == nil {
				goalPreCNFHyps = make(map[core.TermKey]Term, goal0.NumHyps())
				for g := range goal0.HypIter() {
					goalPreCNFHyps[preCNFCache.NormalizeTermKey(g)] = g
				}
			}
			if g, ok := goalPreCNFHyps[preCNFCache.NormalizeTermKey(h)]; ok {
				if bridge := prop.PreCNFEqBridge(h, g); bridge != nil {
					hypBridges = append(hypBridges, bridge)
					continue
				}
			}
			if negEqTerm != nil {
				// more than one hyp of lemma0 is not a hyp of goal0
				return nil
			}
			negEqTerm = h
		}
		if negEqTerm == nil {
			// All lemma hyps matched raw or via bridge. The IsStronger
			// raw check above did not fire (otherwise we'd have already
			// returned via that path), so this case only arises when at
			// least one match is bridge-only. Reconstructing here would
			// require applying every bridge to provedLemma without the
			// usual eq-rewrite step; the result is a normalized-equal
			// IsStronger but the existing eqLemmaTactic shape doesn't
			// have a slot for that. Skip — LemmaTactic's other tactics
			// (lemmaHypMatchTactic with its widened gate, the goal-
			// denormalize path) can pick this case up.
			return nil
		}
		eqTerm := Term(Not(negEqTerm))
		if u := prop.DeepNegRewrite(Not(negEqTerm)); u != nil {
			eqTerm = Rhs(u)
		}

		subGoal := eqSimplify(mode, mode.ruleCache(), MakeProp(F, append(goal0.Hyps(), eqTerm)...), eqTerm, true, allowExpand)
		if subGoal == nil {
			return nil
		}

		Assert(subGoal.Size() == 1)
		// goal1 is a simplified version of goal0 with eqTerm as an extra hyp.
		goal1 := subGoal.ChildGoal(0)
		// remove eqTerm from goal1 if it exists.
		if goal1.HasHyp(eqTerm) {
			goal1 = MakeProp(eqTerm).DeriveTrans(goal1)
		}
		// make goal1 look more like the original goal.
		goal1 = goalReconstruct(goal1)

		if IsStronger(goal1, goal) {
			// in this case the sub goal is actually harder to prove.
			return nil
		}

		subGoals := []Prop{lemma, goal1}
		reconstruct := func(thms ...Prop) Prop {
			Assert(len(thms) == 2)
			provedLemma, _ := negConcl(thms[0])
			// Apply each hyp bridge: rewrite a lemma-side hyp h to its
			// raw goal-side counterpart g via ⊢ h = g. This keeps the
			// reconstructed prop's hyps inside goal0.Hyps() so the
			// parent's IsStronger assertion holds.
			//
			// Mechanically: bridge.EqSym() is ⊢ g = h, Assume(g) is g ⊢ g,
			// EqMP gives g ⊢ h. DeriveTrans then discharges h from
			// provedLemma's hyps and adds g, yielding the same conclusion
			// with hyps {... h ...} → {... g ...}.
			for _, bridge := range hypBridges {
				h, g := prop.Lhs(bridge), prop.Rhs(bridge)
				if !provedLemma.HasHyp(h) {
					// h was already discharged upstream — bridge unused.
					continue
				}
				gToH := bridge.EqSym().EqMP(prop.Assume(g))
				provedLemma = gToH.DeriveTrans(provedLemma)
			}
			if !provedLemma.HasHyp(negEqTerm) {
				return goalReconstruct(prop.WeakenTo(provedLemma, goal0))
			}
			negConclGoal, _ := negConcl(thms[1])
			provedGoal := subGoal.reconstruct(negConclGoal)
			if provedGoal.HasHyp(eqTerm) {
				provedGoal = provedLemma.
					NegHyp(negEqTerm).
					RewriteConcl(prop.DeepNegRewrite).
					DeriveTrans(provedGoal)
			}
			return goalReconstruct(provedGoal)
		}
		return MakeSubGoals(goal, reconstruct, subGoals...)
	}
	return mergeTacticsWithin(mode, tactic)
}
