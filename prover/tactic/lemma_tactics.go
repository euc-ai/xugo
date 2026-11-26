package tactic

import (
	"context"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/utils"
)

// instantiateLemma instantiates a lemma with the given substitutions.
// It returns a function that takes a lemma and returns a specialized version of the lemma.
// It considers the following cases:
// 1. the substituted var is free in the conclusion or in any hypothesis.
// 2. the substituted var is among the universal quantifier variables in the conclusion.
func instantiateLemma(substs TermSubstsGroup) func(Prop) *PropWrapper {
	return func(lemma Prop) *PropWrapper {
		conclUnivVars, _ := ext.DecomposesFORALL(lemma.Conclusion())
		instantiatedLemma := WrapProp(lemma)
		for _, subst := range substs {
			_, substIsAbs := subst.Term.AsAbsTerm()
			if lemma.Conclusion().HasFree(subst.VarTerm) ||
				lemma.AnyHyp(utils.Curry(Term.HasFree, subst.VarTerm)) {
				instantiatedLemma = instantiatedLemma.TermInst(subst)
				if substIsAbs {
					// Free var could be applied anywhere in concl or hyps.
					instantiatedLemma = instantiatedLemma.Rewrite(prop.DeepBeta)
				}
			} else if conclUnivVars.Has(subst.VarTerm) {
				// subst.VarTerm was a ∀-bound var in the original lemma's
				// conclusion. Reorder must use the CURRENT instantiatedLemma
				// (which may have been partially instantiated by previous
				// iterations), not the original lemma — otherwise EqMP(lemma)
				// would discard prior instantiations.
				currentUnivVars, currentBody := ext.DecomposesFORALL(
					instantiatedLemma.Conclusion())
				// Move the matched variable to the front.
				if !currentUnivVars.Ind(0).Equals(subst.VarTerm) {
					newConcl := currentBody
					for _, v := range currentUnivVars.Backward() {
						if !v.Equals(subst.VarTerm) {
							newConcl = ForAll(v)(newConcl)
						}
					}
					newConcl = ForAll(subst.VarTerm)(newConcl)
					// Reorder the quantifiers in the conclusion such that the first one
					// is the matched variable.
					instantiatedLemma = prop.ReorderForAll(
						instantiatedLemma.Conclusion(), newConcl).
						EqMP(instantiatedLemma)
				}
				abs := ext.MatchesFORALL(instantiatedLemma.Conclusion())
				Assert(!abs.IsZero() && abs.Var().Equals(subst.VarTerm))
				instantiatedLemma = instantiatedLemma.ConclForAllInst(subst.Term)
				if substIsAbs {
					// Bound var only appears in concl, so hyps stay untouched.
					instantiatedLemma = instantiatedLemma.RewriteConcl(prop.DeepBeta)
				}
			}
		}
		return instantiatedLemma
	}
}

// Given a proved theorem that is stronger than the lemma,
// proves the lemma exactly (not α-invariant).
func provedLemmaExactly(lemma Prop, thm Prop) *PropWrapper {
	Assert(IsStronger(thm, lemma))
	provedLemma := WrapProp(thm)

	// Adjust conclusion if needed
	if !lemma.Conclusion().Equals(F) && provedLemma.Conclusion().Equals(F) {
		provedLemma = weakenConcl(provedLemma, lemma.Conclusion())
	} else {
		provedLemma = provedLemma.DeriveTrans(prop.Assume(lemma.Conclusion()))
	}

	// Adjust hypotheses to match exactly
	for h := range lemma.HypIter() {
		_h := prop.Assume(h)
		if provedLemma.HasHyp(h) {
			provedLemma = _h.DeriveTrans(provedLemma)
		} else {
			provedLemma = _h.Deduct(provedLemma).EqMP(_h)
		}
	}

	Assert(provedLemma.Conclusion().Equals(lemma.Conclusion()) &&
		slices.EqualFunc(provedLemma.Hyps(), lemma.Hyps(), Term.Equals))
	return provedLemma
}

// lemmaAsStated is the theorem of a lemma's child read as the lemma
// states it. A lemma that carries hypotheses may have its child closed
// by contradiction; that theorem concludes ⊥ over the lemma's
// hypotheses and proves the lemma ex falso. Any other theorem of the
// child is returned as it is.
func lemmaAsStated(lemma, thm Prop) Prop {
	if thm.Conclusion().Equals(F) && !lemma.Conclusion().Equals(F) {
		return provedLemmaExactly(lemma, thm)
	}
	return thm
}

// lemmaInstTactic instantiates a lemma with the given substitutions and applies it to a goal.
// It returns a tactic that attempts to apply the instantiated lemma to prove or simplify goals.
// It considers the following cases:
// 1. the substituted var is free in the conclusion or in any hypothesis of the lemma.
// 2. the substituted var is among the universal quantifier variables in the conclusion of the lemma.
// Instantiated Lemma: L_H1, L_H2, ... ⊢ L_C
// Goal: G_H1, G_H2, ... ⊢ G_C
// The result of the tactic:
// The original goal G_H1, ... ⊢ G_C is replaced by N+2 new subgoals:
// The first subgoal is the original lemma itself.
// The second subgoal: G_H1, ..., G_Hn, **L_C** ⊢ G_C (prove the original conclusion with the new hypothesis)
// The remaining N subgoals: G_H1, ... ⊢ L_H1, G_H1, ... ⊢ L_H2, ... (prove the lemma's hypotheses)
func lemmaInstTactic(lemma Prop, substs TermSubstsGroup) Tactic {
	instantiate := instantiateLemma(substs)
	instantiatedLemma := instantiate(lemma)

	return func(goal Prop) *SubGoals {
		// Create subgoals for each hypothesis of the lemma.
		lemmaHypsGoals := make([]Prop, instantiatedLemma.NumHyps())
		for i, h := range instantiatedLemma.Hyps() {
			lemmaHypsGoals[i] = MakeProp(h, goal.Hyps()...)
		}

		// Create the main subgoal with the lemma's conclusion added as a new hypothesis.
		mainGoal := MakeProp(
			goal.Conclusion(),
			append(goal.Hyps(), instantiatedLemma.Conclusion())...)

		allSubGoals := append([]Prop{lemma, mainGoal}, lemmaHypsGoals...)

		// The reconstruct function combines the proofs of the subgoals
		// to construct a proof for the original goal.
		reconstruct := func(thms ...Prop) Prop {
			// thms[0] is the proved version of the lemma or a stronger version.
			// thms[1] is the proof for mainGoal: G_H, L_C ⊢ G_C
			// thms[2:] are proofs for the lemma's hyps: G_H ⊢ L_H_i
			Assert(len(thms) == lemma.NumHyps()+2 && IsStronger(thms[0], lemma))

			provedLemma := instantiatedLemma
			if !instantiatedLemma.Proved() {
				// Re-derive from the child's certificate thms[0] (always a genuine
				// Thm — realized cert or unforced promise) whenever instantiatedLemma
				// is a bare statement, so a promise-backed lemma close threads a
				// promise up instead of a bare Prop. Gating on thms[0].Proved() left
				// the promise case returning the bare instantiatedLemma, which panics
				// in Commit's updateUpwards (PromisedThm→AsThm). See the matching fix
				// and rationale in lemmaConclMatchTactic below.
				provedLemma = instantiate(provedLemmaExactly(lemma, thms[0]))
			}

			// Sequentially prove each hypothesis of the lemma.
			for i := range lemma.NumHyps() {
				if thms[i+2].Conclusion().Equals(F) {
					// thms[i+2] is stronger than the original goal.
					Assert(IsStronger(thms[i+2], goal))
					return thms[i+2]
				}
				// Each thms[i+2] proves a hypothesis of the lemma.
				// DeriveHypFrom uses this proof to discharge the hypothesis from the lemma.
				provedLemma = provedLemma.DeriveHypFrom(thms[i+2])
			}
			// After the loop, provedLemma is a theorem: G_H ⊢ L_C

			// thms[1] is a proof of G_H, L_C ⊢ G_C.
			// By deriving it from the now-proven lemma (G_H ⊢ L_C),
			// we get the final proof for the original goal: G_H ⊢ G_C.
			return provedLemma.MaybeDeriveTrans(thms[1])
		}

		return MakeSubGoals(goal, reconstruct, allSubGoals...)
	}
}

// lemmaConclMatchTactic creates a backward-chaining tactic that attempts to apply a lemma
// by unifying the lemma's conclusion with the goal's conclusion.
//
// The tactic works as follows:
//  1. It strips any top-level universal quantifiers from the lemma's conclusion.
//  2. It attempts to unify the resulting lemma conclusion with the goal's conclusion.
//  3. The tactic only succeeds if there is exactly one unique set of substitutions found.
//     If unification fails or is ambiguous (multiple results), the tactic returns nil.
//  4. If successful, it instantiates the lemma with the found substitutions.
//  5. It then generates 2 subgoals:
//     - The first subgoal is the original lemma itself (to be proven).
//     - The second subgoal is to prove the instantiated lemma's conclusion with the original goal's hypotheses.
func lemmaConclMatchTactic(lemma Prop) Tactic { return lemmaConclMatchUnder(fullSearch, lemma) }

// lemmaConclMatchUnder is lemmaConclMatchTactic as a step of a search in
// mode: its unifications run under the mode's deadline beside their own
// work budget, and one the deadline ends abandons the search.
func lemmaConclMatchUnder(mode _SearchMode, lemma Prop) Tactic {
	unifyConcl := func(pattern, target Term) []TermSubstsGroup {
		bounded, cancel := unify.WithWorkBudget(mode.deadline)
		defer cancel()
		substs := unify.UnifyTerms(bounded, pattern, target, target.HasFreeName)
		mode.abandonIfDone()
		return substs
	}
	return func(goal Prop) *SubGoals {
		conclUnivVars, conclBody := ext.DecomposesFORALL(lemma.Conclusion())
		if !conclUnivVars.Empty() {
			nameCollision := false
			for v := range conclUnivVars.Iter() {
				if goal.HasFreeName(v.Name()) ||
					lemma.AnyHyp(utils.Curry(Term.HasFreeName, v.Name())) {
					// E.g. P(x) ⊢ ∀x.∀y.Q(x, y)
					nameCollision = true
					break
				}
			}
			if nameCollision {
				rewriteConcl := prop.AdjustUnivVars(
					utils.Disjunct(lemma.HasFreeName, goal.HasFreeName))(
					lemma.Conclusion())
				Assert(rewriteConcl != nil && Rhs(rewriteConcl).AlphaEquals(lemma.Conclusion()))
				// We directly replace lemma here, which is α-equal to the original lemma.
				lemma = rewriteConcl.EqMP(lemma)
				_, conclBody = ext.DecomposesFORALL(lemma.Conclusion())
			}
		}
		substs := unifyConcl(conclBody, goal.Conclusion())
		if substs == nil {
			// No instantiation found.
			return nil
		}
		if len(substs) > 1 {
			// Multiple instantiations found.
			// Need user's input to choose the best one.
			return nil
		}
		instantiate := instantiateLemma(substs[0])
		instantiatedLemma := instantiate(lemma)

		// Post-instantiation validation: the instantiated lemma's conclusion
		// must reproduce the goal's conclusion, or the downstream soundness
		// Asserts (IsStronger in makeSubGoalsAt / the no-hyps branch below)
		// panic. The proxy mirrors exactly what those asserts need: the
		// reconstructed prop has conclusion instantiatedLemma.Conclusion()
		// and hyps drawn from goal.Hyps().
		//
		// The stripped-∀ unification above can produce a spurious HO
		// imitation solution when the lemma carries a FREE (sequent-level)
		// predicate variable: e.g. binary induction's sequent form
		// `P(0), ∀n.(P(n) ⇒ …) ⊢ ∀n.P(n)` against a goal concl `∀m.Q(m)`
		// unifies the stripped body `P(n)` as `P ↦ λx.∀m.Q(m)` — the free
		// predicate absorbs the goal's entire ∀-conclusion and the stripped
		// binder `n` gets no binding, leaving a vacuous `∀n.` on the
		// instantiated conclusion (`∀n.∀m.Q(m)` ≠ `∀m.Q(m)`).
		reproducesGoal := func(il *PropWrapper) bool {
			return IsStronger(MakeProp(il.Conclusion(), goal.Hyps()...), goal)
		}
		if !reproducesGoal(instantiatedLemma) {
			// Retry with a WHOLE-conclusion unification (∀-prefix kept):
			// pattern-unifying under the shared binder yields the intended
			// first-order-ish solution (P ↦ Q above) instead of the
			// absorbing imitation. Replay stability: every stored
			// decomposition passed the first-attempt validation live
			// (otherwise it would have panicked at store time), so this
			// branch only fires where the old code panicked.
			substs = unifyConcl(lemma.Conclusion(), goal.Conclusion())
			if substs == nil || len(substs) > 1 {
				// No unique whole-conclusion instantiation either: the
				// lemma does not apply. Soft failure, not a panic.
				return nil
			}
			instantiate = instantiateLemma(substs[0])
			instantiatedLemma = instantiate(lemma)
			if !reproducesGoal(instantiatedLemma) {
				return nil
			}
		}

		if instantiatedLemma.NumHyps() == 0 {
			Assert(IsStronger(instantiatedLemma, goal))
			return MakeSubGoals(goal, func(thms ...Prop) Prop {
				Assert(IsStronger(thms[0], lemma))
				provedLemma := instantiatedLemma
				if !instantiatedLemma.Proved() {
					// instantiatedLemma is not a realized certificate: the lemma
					// reached `instantiate` as a bare statement (a lemma can
					// arrive unproven), so ConclForAllInst's DeriveTrans hit
					// deriveProp's unprovable-dep escape and `instantiatedLemma` is a
					// bare proposition. Re-derive from the child's actual
					// certificate thms[0] — always a genuine Thm (a realized ThmCert
					// OR an unforced ThmPromise, by the closed-child PromisedThm
					// contract) — so the result threads a promise instead of staying a
					// bare Prop. Gating on thms[0].Proved() (the old condition) left
					// the promise-backed case returning the bare instantiatedLemma,
					// which then poisons Commit's updateUpwards (PromisedThm→AsThm
					// panic).
					provedLemma = instantiate(provedLemmaExactly(lemma, thms[0]))
				}
				return provedLemma
			}, lemma.AsProp())
		}

		instantiatedLemmaHyps := instantiatedLemma.Hyps()
		newGoal := MakeProp(And(instantiatedLemmaHyps...), goal.Hyps()...)

		// The reconstruct function combines the proofs of the subgoals
		// to construct a proof for the original goal.
		reconstruct := func(thms ...Prop) Prop {
			Assert(len(thms) == 2 && IsStronger(thms[0], lemma))
			provedLemma := instantiatedLemma
			if !instantiatedLemma.Proved() {
				// See the no-hyps branch above: re-derive from thms[0] (always a
				// genuine Thm — realized cert or unforced promise) whenever
				// instantiatedLemma is a bare statement, so a promise-backed lemma
				// close threads a promise up instead of a bare Prop that would
				// panic in Commit's updateUpwards.
				provedLemma = instantiate(provedLemmaExactly(lemma, thms[0]))
			}

			// Sequentially prove each hypothesis of the lemma.
			if thms[1].Conclusion().Equals(F) {
				// thms[1] is stronger than the original goal.
				Assert(IsStronger(thms[1], goal))
				return thms[1]
			}
			for _, t := range prop.HypANDRecursive(instantiatedLemmaHyps...) {
				// Each t proves a hypothesis of the lemma.
				provedLemma = provedLemma.DeriveHypFrom(t)
			}
			provedLemma = provedLemma.DeriveHypFrom(thms[1])
			return provedLemma
		}

		return MakeSubGoals(goal, reconstruct, lemma.AsProp(), newGoal)
	}
}

func hypMatching(goal Prop) func(Prop) *PropWrapper {
	return func(lemma Prop) *PropWrapper {
		matchedLemma := WrapProp(lemma)
		for h := range lemma.HypIter() {
			if goal.HasHyp(h) {
				continue
			}
			// Put hypothesis that is not in the goal to conclusion side
			if matchedLemma.Conclusion().Equals(F) {
				matchedLemma = matchedLemma.NegHyp(h)
			} else {
				matchedLemma = matchedLemma.PromoteHyp(h)
			}
		}
		// Add universal quantifiers so the lemma is in the general form
		for _, v := range matchedLemma.Conclusion().Frees(func(v VarTerm) bool {
			return prop.NotFreeInHyps(matchedLemma, v)
		}) {
			matchedLemma = matchedLemma.ConclForAll(v)
		}
		return matchedLemma
	}
}

// lemmaHypMatchTactic creates a forward-chaining tactic that attempts to apply a lemma
// by matching the lemma's hypotheses with the goal's hypotheses.
//
// The tactic works as follows:
//  1. The tactic works if the lemma has no hypotheses or some of its hypotheses are in the goal.
//  2. It processes the lemma by moving any of its hypotheses that are *not* in the goal's
//     hypotheses to the conclusion side of the lemma (e.g., H, h ⊢ c becomes H ⊢ h => c).
//     This results in a `matchedLemma`.
//  3. If the `matchedLemma`'s conclusion is `F` (false), it means all of the original lemma's
//     hypotheses were present in the goal, and the lemma proves a contradiction from a subset
//     of the goal's hypotheses. Thus, the lemma directly proves the goal. A single subgoal,
//     the lemma itself, is generated.
//  4. Otherwise, it creates a new goal by adding the `matchedLemma`'s conclusion as a new
//     hypothesis to the original goal. The free variables in the conclusion that are not in the
//     goal's hypotheses are universally quantified to make it general.
//  5. It then generates two subgoals:
//     - The first subgoal is to prove the original lemma itself.
//     - The second subgoal is the new goal (original goal + new hypothesis).
//
// Example:
// Lemma: P, Q ⊢ R
// Goal:  P, S ⊢ T
//
// 1. Lemma hypothesis `P` is in the goal's hypotheses.
// 2. Lemma hypothesis `Q` is not, so it's moved to the conclusion: `matchedLemma` is `P ⊢ (Q => R)`.
// 3. A new goal is created: `P, S, (Q => R) ⊢ T`.
// 4. Two subgoals are generated:
//   - Prove `P, Q ⊢ R` (the original lemma).
//   - Prove `P, S, (Q => R) ⊢ T`.
//
// LemmaAddHypTactic is the PLAIN ADD of a lemma: the hyp-match strategy
// alone — the lemma's statement joins the context (free variables
// ∀-closed into the general form), with the lemma itself as the first
// subgoal (the claim obligation) and the goal-with-the-fact as the
// second. No conclusion match, no rewrite: nothing about the fact is
// decided by its shape at install. The By executor installs every named
// premise this way (a premise reaches the closer as the fact the author
// named), and its apply rung does at the leaf what a conclusion-match
// strategy would do at install.
func LemmaAddHypTactic(lemma Prop) Tactic { return lemmaHypMatchTactic(lemma) }

func lemmaHypMatchTactic(lemma Prop) Tactic {
	return func(goal Prop) *SubGoals {
		var goalNormalizedHypKeys map[PropKey]struct{}
		hasGoalHyp := func(h Term) bool {
			if goal.HasHyp(h) {
				return true
			}
			if goalNormalizedHypKeys == nil {
				goalNormalizedHypKeys = normalizedHypKeys(goal)
			}
			return hasNormalizedHypKey(goalNormalizedHypKeys, h)
		}

		if lemma.NumHyps() > 0 &&
			!lemma.AnyHyp(hasGoalHyp) {
			return nil
		}
		// There is at least one hypothesis of the lemma that matches a goal
		// hyp under normalized comparison. The applicability gate uses
		// normalized matching to admit lemmas whose hyps differ from goal
		// hyps only in representation (⇒/¬∨, scope, ordering); hypMatching
		// itself stays raw and pushes any non-raw-matched lemma hyp to the
		// conclusion side, so the reconstruction never carries a hyp that's
		// only normalized-equal to a goal hyp.

		// push the unmatched hypotheses to conclusion side
		matchedLemma := hypMatching(goal)(lemma)

		// If the conclusion is ⊥, the lemma directly proves the goal.
		if matchedLemma.Conclusion().Equals(F) {
			Assert(IsStronger(lemma, goal))
			return MakeSubGoals(goal, trivialReconstruct, lemma)
		}

		if goal.HasHyp(matchedLemma.Conclusion()) {
			return nil
		}

		newGoal := MakeProp(goal.Conclusion(), append(
			goal.Hyps(), matchedLemma.Conclusion())...)

		reconstruct := func(thms ...Prop) Prop {
			Assert(len(thms) == 2)
			provedLemma := provedLemmaExactly(lemma, thms[0])
			provedLemma = hypMatching(goal)(provedLemma)
			if !thms[1].HasHyp(provedLemma.Conclusion()) {
				Assert(IsStronger(thms[1], goal))
				return thms[1]
			}
			return provedLemma.DeriveTrans(thms[1])
		}

		return MakeSubGoals(goal, reconstruct, lemma.AsProp(), newGoal)

	}
}

// Trivially simplify the new goal if possible. mode is the search the
// simplification is a step of.
func simplifyNewGoal(mode _SearchMode, lemma Prop, subGoals *SubGoals) *SubGoals {
	if subGoals.Size() == 1 {
		Assert(subGoals.ChildGoal(0).AlphaEquals(lemma))
		return subGoals
	}

	Assert(subGoals.Size() == 2 &&
		subGoals.ChildGoal(0).AlphaEquals(lemma))

	newGoal := subGoals.ChildGoal(1)

	// The simplification is a fixpoint: a run of its own, or a step of
	// the run mode already is.
	mode = mode.asRun()
	simplify := mergeTacticsWithin(mode,
		simplestTrivialTactic,
		rewriteTactic(prop.BasicRewrite),
		boolOpSimplifyNestedUnder(mode),
		unifyEqSimplifyUnder(mode),
		trivialTactic,
	)

	simplifiedSubGoal := simplify(newGoal)

	if simplifiedSubGoal == nil {
		// No simplification occurred by TrivialSimplifyTactic.
		// Return the new goal (with the added hypothesis) as is.
		return subGoals
	}

	// simplified new goal can be trivially proved.
	if simplifiedSubGoal.Size() == 0 {
		return MakeSubGoals(
			subGoals.goal,
			func(thms ...Prop) Prop {
				return subGoals.reconstruct(thms[0], simplifiedSubGoal.Reconstruct())
			},
			lemma)
	}

	Assert(simplifiedSubGoal.Size() == 1)
	if IsStronger(simplifiedSubGoal.ChildGoal(0), subGoals.goal) {
		// Simplified sub goal is stronger than the original goal.
		// In this case the lemma application is not useful.
		return nil
	}
	return MakeSubGoals(
		subGoals.goal,
		func(thms ...Prop) Prop {
			return subGoals.reconstruct(
				thms[0], simplifiedSubGoal.Reconstruct(thms[1]))
		},
		lemma,
		simplifiedSubGoal.ChildGoal(0))
}

// _DenormStep records one forward denormalize move on a proposition's
// conclusion. Exactly one of `vars` or `hyp` is populated.
//
//   - vars != nil: ∀-strip step. The bound vars in outer-first order. If
//     renameEq is non-nil, it's an equation `pre_concl = post_rename_concl`
//     that must be applied (via EqMP) before instantiating with vars — the
//     renamed form is what DecomposesFORALL was run on.
//   - hyp != nil: ⇒-peel step. The hypothesis that was peeled out of the
//     concl into the hyp-side.
//
// postConcl is the conclusion AFTER this step fires (= t1 for peel, = body
// for strip). It lets the backward reconstruct pre-weaken a ⊥-collapsed
// proof to the right intermediate shape before applying the inverse move.
type _DenormStep struct {
	vars      []VarTerm
	hyp       Term
	postConcl Term
	renameEq  Prop
}

// denormalizeProp reverses prop.Normalize on a proposition's conclusion:
// strip top-level ∀ (with AdjustUnivVars fresh-renaming only on collision)
// and peel top-level ⇒ into hyps, iterating until neither applies. Returns
// the denormalized prop and the list of forward steps (empty iff no change).
//
// The returned steps can drive either direction:
//   - Backward (proved denorm → proved original): weakenConcl + ConclForAll
//     / PromoteHyp for each step in reverse order. Used by the goal-side
//
// denormalizeConclTactic's emit.
//   - Forward (proved original → proved denorm): EqMP(renameEq) +
//     ConclForAllInst / DemoteHyp for each step in forward order. Used by
//     the lemma-side wrapLemmaWithDenorm.
func denormalizeProp(p Prop) (Prop, []_DenormStep) {
	var steps []_DenormStep
	current := p
	hyps := p.Hyps() // Hyps() clones — we own this slice.
	for {
		concl := current.Conclusion()
		if t0, t1, ok := MatchesIMPLY(concl); ok && !t0.AlphaEquals(t1) {
			hyps = append(hyps, t0)
			current = MakeProp(t1, hyps...)
			steps = append(steps, _DenormStep{hyp: t0, postConcl: t1})
			continue
		}
		if !ext.MatchesFORALL(concl).IsZero() {
			// AdjustUnivVars renames ∀-bound vars only when they'd clash
			// with any free name in the current prop (hyps + concl).
			// Same minimum-rename helper lemmaConclMatchTactic uses.
			var renameEq Prop
			if w := prop.AdjustUnivVars(current.HasFreeName)(concl); w != nil {
				renameEq = w
				concl = Rhs(w)
			}
			vars, body := ext.DecomposesFORALL(concl)
			vs := make([]VarTerm, 0, vars.Size())
			for v := range vars.Iter() {
				vs = append(vs, v)
			}
			current = MakeProp(body, hyps...)
			steps = append(steps, _DenormStep{
				vars: vs, postConcl: body, renameEq: renameEq,
			})
			continue
		}
		break
	}
	return current, steps
}

// forwardDenorm converts a proved exact form of the ORIGINAL prop into a
// proved exact form of the DENORMALIZED prop, by applying each step's
// forward inverse:
//
//   - ⇒-peel:   DemoteHyp turns `hyps ⊢ h ⇒ c` into `hyps, h ⊢ c`.
//   - ∀-strip:  EqMP(renameEq) renames bound vars if needed, then
//     ConclForAllInst(v) per stripped var turns `⊢ ∀v. body(v)` into
//     `⊢ body(v)` with v free.
func forwardDenorm(p *PropWrapper, steps []_DenormStep) *PropWrapper {
	for _, s := range steps {
		if s.vars != nil {
			if s.renameEq != nil {
				p = WrapProp(s.renameEq).EqMP(p)
			}
			for _, v := range s.vars {
				p = p.ConclForAllInst(v)
			}
		} else {
			p = p.DemoteHyp()
		}
	}
	return p
}

// backwardDenorm converts a proved form of the DENORMALIZED prop into a
// proved form of the ORIGINAL prop by applying each step's inverse in
// reverse order. weakenConcl handles a ⊥-concl child before each inverse
// move so ConclForAll / PromoteHyp produce the right structural wrapper.
func backwardDenorm(p *PropWrapper, steps []_DenormStep) *PropWrapper {
	for i := len(steps) - 1; i >= 0; i-- {
		s := steps[i]
		p = weakenConcl(p, s.postConcl)
		if s.vars != nil {
			for j := len(s.vars) - 1; j >= 0; j-- {
				p = p.ConclForAll(s.vars[j])
			}
		} else {
			p = p.PromoteHyp(s.hyp)
		}
	}
	return p
}

// denormalizeConclTactic reverses prop.Normalize on the goal's conclusion:
// it strips top-level ∀ from the conclusion (with fresh-renaming to avoid
// free-name collisions) and peels top-level ⇒ from the conclusion into the
// hyp side, iterating until neither applies.
//
// Motivation: Normalize moves everything into the conclusion as a ⇒-chain
// under outer ∀s. In that shape, lemmaHypMatchTactic is dead code (no hyps
// to α-match) and lemmaConclMatchTactic's unify is blocked by outer ∀ on
// the goal side (the tactic strips ∀ from the lemma's concl but not from
// the goal's — see lemmaConclMatchTactic). Denormalizing the goal restores
// the maximum-hyp form where both backward-chain paths are effective.
//
// Every forward move has a kernel-level inverse (ConclForAll / PromoteHyp);
// α-equivalence absorbs the fresh-renaming so the reconstructed thm α-equals
// the original goal.
func denormalizeConclTactic(goal Prop) *SubGoals {
	current, steps := denormalizeProp(goal)
	if len(steps) == 0 {
		return nil
	}
	reconstruct := func(thms ...Prop) Prop {
		// Short-circuit: if the child proof is already stronger than the
		// original goal (typically ⊥ with a hyp subset), no reverse moves
		// are needed — it already proves the goal by weakening.
		if IsStronger(thms[0], goal) {
			return thms[0]
		}
		return backwardDenorm(WrapProp(thms[0]), steps)
	}
	return MakeSubGoals(goal, reconstruct, current)
}

// lemmaTacticCore is the original LemmaTactic body: try IsStronger shortcuts,
// then eq / conclMatch / hypMatch variants. Kept as its own tactic so that
// LemmaTactic can run it against multiple forms of the lemma without
// modifying these well-tested sub-tactics. mode is the search the chain
// is a step of: the rewrites and unifications of its strategies run
// under the mode's deadline.
func lemmaTacticCore(mode _SearchMode, lemma Prop) Tactic {
	return func(goal Prop) *SubGoals {
		if IsStronger(goal, lemma) {
			return nil
		}

		if IsStronger(lemma, goal) {
			return MakeSubGoals(goal, trivialReconstruct, lemma)
		}

		if subGoals := eqLemmaTacticOpt(mode, lemma, false)(goal); subGoals != nil {
			return simplifyNewGoal(mode, lemma, subGoals)
		}

		if subGoals := lemmaConclMatchUnder(mode, lemma)(goal); subGoals != nil {
			return simplifyNewGoal(mode, lemma, subGoals)
		}

		if subGoals := lemmaHypMatchTactic(lemma)(goal); subGoals != nil {
			return simplifyNewGoal(mode, lemma, subGoals)
		}

		return nil
	}
}

// rewriteOnlyTacticCore is the rewrite-only counterpart of
// lemmaTacticCore, used by LeanRwTactic and the def_expand path. It
// keeps the IsStronger shortcuts (a successful direct match is a
// degenerate rewrite, equivalent to the rewrite trivially producing
// the goal as RHS) and the equational rewrite step, but bypasses the
// size-decrease guard via eqLemmaTacticExpand and DOES NOT fall back
// to lemmaConclMatchTactic / lemmaHypMatchTactic. Failure returns nil
// — agents see a clean miss instead of the silent "lemma added as a
// hyp" outcome that hypMatch produces for non-equational shapes.
func rewriteOnlyTacticCore(lemma Prop) Tactic {
	return func(goal Prop) *SubGoals {
		if IsStronger(goal, lemma) {
			return nil
		}

		if IsStronger(lemma, goal) {
			return MakeSubGoals(goal, trivialReconstruct, lemma)
		}

		if subGoals := eqLemmaTacticExpand(lemma)(goal); subGoals != nil {
			if simplified := simplifyNewGoal(fullSearch, lemma, subGoals); simplified != nil {
				return simplified
			}
		}

		if subGoals := directConclusionRewriteTactic(lemma)(goal); subGoals != nil {
			if simplified := simplifyNewGoal(fullSearch, lemma, subGoals); simplified != nil {
				return simplified
			}
			return subGoals
		}

		return nil
	}
}

func directConclusionRewriteTactic(lemma Prop) Tactic {
	return func(goal Prop) *SubGoals {
		if lemma.NumHyps() != 0 {
			return nil
		}
		// The refutation-shaped eqLemmaTactic path can reject a useful
		// expansion under negation as "not useful". For explicit rw/def_expand,
		// a direct conclusion rewrite is still valid progress.
		bridge := prop.ContextEqRewriteOpt(new(prop.PreCNFCache), lemma.Conclusion(), true, true)(goal.Conclusion())
		if bridge == nil || Rhs(bridge).AlphaEquals(goal.Conclusion()) {
			return nil
		}
		if bridge.NumHyps() != 0 &&
			!(bridge.NumHyps() == 1 && bridge.HasHyp(lemma.Conclusion())) {
			return nil
		}

		child := MakeProp(Rhs(bridge), goal.Hyps()...)
		reconstruct := func(thms ...Prop) Prop {
			// child(1) carries goal.Hyps(); if it was closed via ⊥
			// (contradictory hyps — e.g. a case-split branch), it proves
			// the parent directly. Without this guard, EqMP below asserts
			// on `⊢ ⊥` and panics. Mirrors SymmTactic / TransTactic /
			// FunextTactic / ByContraTactic.
			if thms[1].Conclusion().Equals(F) {
				return thms[1]
			}
			rewrite := bridge
			if rewrite.HasHyp(lemma.Conclusion()) {
				rewrite = rewrite.DeriveHypFrom(thms[0])
			}
			Assert(rewrite.NumHyps() == 0)
			return rewrite.EqSym().EqMP(thms[1])
		}
		return MakeSubGoals(goal, reconstruct, lemma.AsProp(), child)
	}
}

// wrapLemmaWithDenorm takes inner SubGoals produced by running
// lemmaTacticCore with the DENORMALIZED lemma (so inner.ChildGoal(0) α-equals
// denormLemma) and re-exposes origLemma as child[0] so that the recorded
// dep is the correct one (keyed by origLemma's normalized AlphaKey — the
// key its registry entry carries).
//
// In reconstruct, thms[0] is a proof (or stronger form) of origLemma. We
// bridge via provedLemmaExactly (normalize to exact origLemma) then
// forwardDenorm (apply the denormalize steps forward) to produce a proof
// of denormLemma, which is what the inner reconstruct expects.
func wrapLemmaWithDenorm(inner *SubGoals, origLemma Prop, steps []_DenormStep) *SubGoals {
	newChildren := make([]Prop, inner.Size())
	newChildren[0] = origLemma
	for i := 1; i < inner.Size(); i++ {
		newChildren[i] = inner.ChildGoal(i)
	}
	reconstruct := func(thms ...Prop) Prop {
		exact := provedLemmaExactly(origLemma, thms[0])
		denormThm := forwardDenorm(exact, steps)
		innerThms := make([]Prop, len(thms))
		innerThms[0] = denormThm
		copy(innerThms[1:], thms[1:])
		return inner.Reconstruct(innerThms...)
	}
	return MakeSubGoals(inner.goal, reconstruct, newChildren...)
}

// LemmaTactic creates a tactic that applies a given lemma to simplify a proof goal.
// This is a higher-order function that takes a lemma proposition and returns a tactic
// function that attempts to apply that lemma to prove or simplify goals.
//
// Two internal strategies combine to recover matches that a purely
// normalized lemma + goal would miss:
//
//  1. Lemma-side denormalization: if the input lemma's conclusion has outer
//     ∀/⇒, compute its max-hyp form (denormLemma) once at construction. Run
//     lemmaTacticCore against BOTH origLemma and denormLemma; prefer the
//     result with fewer subgoals. This unblocks α-aware hyp matching and
//     conclusion unification that would fail on the ⇒-chain-under-∀ form.
//     wrapLemmaWithDenorm re-exposes origLemma as child[0] so dep
//     tracking stays keyed on the lemma's own key.
//
//  2. Goal-side denormalization: if neither form matches the goal as-is,
//     denormalize the goal's concl (denormalizeConclTactic) and retry with
//     the same dual-form core. The denormalize wrapper's reconstruct
//     undoes the goal-side transformation via backwardDenorm.
//
// Both denormalizations are semantics-preserving (kernel-level inverses)
// and visible only inside the tactic — search, engine and store see only
// the original normalized forms.
func LemmaTactic(lemma Prop) Tactic { return lemmaTacticUnder(fullSearch, lemma) }

// lemmaTacticUnder is LemmaTactic as a step of a search in mode
// (lemmaTacticCore).
func lemmaTacticUnder(mode _SearchMode, lemma Prop) Tactic {
	// If the lemma is a proved theorem, use its proposition form to ensure
	// the first subgoal is always the lemma itself. This is important for
	// the reconstruct function as the prover need the lemma child node to
	// be recorded in the proof.
	lemma = lemma.AsProp()
	coreOrig := lemmaTacticCore(mode, lemma)

	// Compute the denormalized form of the lemma ONCE. If it differs from
	// the original (i.e., the lemma's concl had outer ∀/⇒), coreAlt runs
	// matching on the denormalized form and re-wraps child[0] back to
	// origLemma. If the lemma has no denorm steps, coreAlt stays nil and
	// the dual-form comparison degenerates to coreOrig alone.
	denormLemma, lemmaSteps := denormalizeProp(lemma)
	var coreAlt Tactic
	if len(lemmaSteps) > 0 {
		coreInner := lemmaTacticCore(mode, denormLemma)
		coreAlt = func(goal Prop) *SubGoals {
			inner := coreInner(goal)
			if inner == nil {
				return nil
			}
			return wrapLemmaWithDenorm(inner, lemma, lemmaSteps)
		}
	}

	// try runs the lemma against `goal` using both forms and prefers the
	// one with fewer subgoals. Tie goes to coreOrig for stability (and
	// because coreOrig's result typically has simpler provenance: the
	// lemma child is the real lemma, not an α-adjusted variant).
	try := func(goal Prop) *SubGoals {
		sOrig := coreOrig(goal)
		if coreAlt == nil {
			return sOrig
		}
		sAlt := coreAlt(goal)
		switch {
		case sOrig == nil:
			return sAlt
		case sAlt == nil:
			return sOrig
		case sAlt.Size() < sOrig.Size():
			return sAlt
		default:
			return sOrig
		}
	}

	return func(goal Prop) *SubGoals {
		// Corner case: goal α-equals lemma. Using the lemma to "prove" a
		// goal that IS the lemma is circular; Search should handle this
		// via tryKnownThm (AlphaKey lookup) before invoking LemmaTactic.
		// Without this guard, the goal-denormalize path below would
		// produce subgoals whose lemma child α-equals the original goal,
		// tripping MakeSubGoals' "None(childrenGoals, goal.AlphaEquals)"
		// assertion — the tactic framework forbids a child goal that's
		// α-equal to the parent goal (no progress).
		if goal.AlphaEquals(lemma) {
			return nil
		}
		if s := try(goal); s != nil {
			return s
		}
		// Neither form of the lemma matched the goal as-is. Denormalize
		// the goal's concl and retry; bail if the goal doesn't denormalize
		// (nothing else to try) or if try still fails on the denormalized
		// form (bare denormalization without a lemma child is not a valid
		// LemmaTactic result — it would corrupt Search's dep tracking).
		denormSG := denormalizeConclTactic(goal)
		if denormSG == nil {
			return nil
		}
		expanded := Tactic(try).expand(denormSG)
		if expanded == denormSG {
			return nil
		}
		return expanded
	}
}

// lemmaResultPreservesGoalHyps reports whether every hypothesis of the
// original goal survives (α-equal) into every residual child of the
// SubGoals. Children α-equal to the lemma itself are exempt — they
// reproduce the lemma, not the goal, so the goal's hyp context doesn't
// apply to them. A closing result (lemma-only children) passes
// trivially, as does any goal with no hyps.
//
// This is the acceptance gate of LemmaPreserveTactic: it distinguishes
// the benign LemmaTactic outcomes (close, backward-chain on the
// conclusion, conclusion eq-rewrite — all of which carry goal.Hyps()
// through unchanged) from the destructive ones (eqSimplify retargeting
// a pre-existing hyp; simplifyNewGoal's whole-context pass letting a
// resident ∀-hyp absorb its own ground instances).
func lemmaResultPreservesGoalHyps(goal, lemma Prop, subGoals *SubGoals) bool {
	for i := range subGoals.Size() {
		child := subGoals.ChildGoal(i)
		if child.AlphaEquals(lemma) {
			continue
		}
		for h := range goal.HypIter() {
			if !child.HasHyp(h) && !child.AnyHyp(h.AlphaEquals) {
				return false
			}
		}
	}
	return true
}

// LemmaPreserveTactic is the hypothesis-preserving variant of
// LemmaTactic, used by the agent-facing session `lemma` dispatch
// (`_LemmaPreserveTactic` / proto tag `lemma_preserve`).
//
// Motivation (`lemma` re-normalizing the hyp context): LemmaTactic's
// hypMatch/conclMatch results pass through simplifyNewGoal, whose
// merged simplify chain includes unifyEqSimplifyUnder — which lets
// any resident ∀-hyp rewrite its own ground instance to ⊤ (then
// dropped). So loading ANY lemma after a manual `instantiate`
// silently reverted the ground-specialized hyps to their ∀-forms,
// forcing re-instantiation. The eqLemma path can likewise retarget a
// pre-existing hyp instead of the conclusion.
//
// Strategy: run the full LemmaTactic chain; accept its result only if
// every pre-existing goal hyp survives into every residual child
// (lemmaResultPreservesGoalHyps). Otherwise — including when the chain
// declines outright — fall back to the plain forward-load: add the
// lemma's conclusion as a new hypothesis via lemmaHypMatchTactic with
// NO post-simplify. Closing results and conclusion-side rewrites are
// unaffected (they preserve hyps by construction); only the
// hyp-destroying outcomes are downgraded to the benign load.
//
// When the forward-load itself is unavailable (lemmaHypMatchTactic
// declines — e.g. a hyps-carrying ORIGINAL form none of whose hyps
// match a goal hyp, the binary-induction shape), the non-preserving inner
// result is returned rather than failing outright: a sound
// backward-chain that restructures a hyp (∧-split by simplifyNewGoal)
// beats "lemma did not apply". Replay-stable: this branch is only
// reachable where the old code returned nil, and failed applies are
// never stored.
//
// Replay note: this is intentionally a SEPARATE tactic from
// LemmaTactic. Steps recorded under the `lemma` tag replay through
// LemmaTactic and must keep reproducing its SubGoals (including the
// destructive simplify) — only steps recorded under `lemma_preserve`
// replay through this tactic.
func LemmaPreserveTactic(lemma Prop) Tactic { return lemmaPreserveTacticUnder(fullSearch, lemma) }

// LemmaPreserveTacticUntil runs LemmaPreserveTactic(lemma) on goal until
// ctx is done. A chain that ends before the deadline returns what
// LemmaPreserveTactic returns. abandoned reports that the deadline ended
// it first: sg is then nil and stands for nothing — the caller does not
// read it as a lemma that does not apply. The deadline bounds the
// chain's rewrites and unifications (eqSimplify, lemmaConclMatchUnder)
// and the fixpoints around them; each still runs under its own work
// budget, so a chain the deadline does not end is the one a replay runs
// with no deadline.
func LemmaPreserveTacticUntil(ctx context.Context, lemma, goal Prop) (sg *SubGoals, abandoned bool) {
	chain := lemmaPreserveTacticUnder(boundedSearch(ctx), lemma)
	defer func() {
		if r := recover(); r != nil {
			if _, cut := r.(searchAbandoned); !cut {
				panic(r)
			}
			sg, abandoned = nil, true
		}
	}()
	return chain(goal), false
}

// lemmaPreserveTacticUnder is LemmaPreserveTactic as a search in mode.
func lemmaPreserveTacticUnder(mode _SearchMode, lemma Prop) Tactic {
	lemma = lemma.AsProp()
	inner := lemmaTacticUnder(mode, lemma)
	addHyp := lemmaHypMatchTactic(lemma)
	return func(goal Prop) *SubGoals {
		s := inner(goal)
		if s != nil && lemmaResultPreservesGoalHyps(goal, lemma, s) {
			return s
		}
		// Inner chain declined, or its result would rewrite/drop a
		// pre-existing hyp. Plain forward-load instead. The two guards
		// mirror LemmaTactic's own top-level corner cases: a lemma
		// α-equal to (or derivable from) the goal is circular — adding
		// it as a hyp would either trip MakeSubGoals' no-progress
		// assertion or smuggle the goal in as its own justification.
		if goal.AlphaEquals(lemma) || IsStronger(goal, lemma) {
			return nil
		}
		if forward := addHyp(goal); forward != nil {
			return forward
		}
		// No benign load possible; prefer the (sound, non-preserving)
		// inner result over hard failure. nil when inner declined too.
		return s
	}
}

// LeanRwTactic is the explicit equational-rewrite tactic — the engine
// counterpart of LEAN's `rw [h]`. Unlike LemmaTactic, it does not fall
// back to `lemmaConclMatchTactic` / `lemmaHypMatchTactic` when the
// equational rewrite path doesn't fire: a clean nil is more useful to
// the agent than the "lemma silently added as a hyp" outcome those
// fallbacks produce for non-equational shapes.
//
// It also bypasses the size-decrease guard inside eqSimplify, so
// expansion-style equational lemmas (extensionality, COND
// distribution, definitional unfolding — anything where the RHS is
// bigger than the LHS) apply normally.
//
// Direction handling: tries the lemma's natural direction first
// (LHS → RHS), then falls back to the flipped direction (RHS → LHS)
// if no match was found: the rule is oriented by what
// fires — lemmas are sometimes stated
// as `body = const(...)` (so the agent's intended `const → body`
// rewrite needs the flipped direction), or as `(big iff) ⇔ (small)`
// (where the agent anchors on the small side and expands). Without
// the bidirectional retry, the agent would have to know each lemma's
// stored orientation up front; with it, the agent can just call
// lean_rw and the engine picks whichever direction actually matches.
//
// Mirrors LemmaTactic's dual-form / goal-side denorm structure so
// type adaptation and α-aware matching still work.
func LeanRwTactic(lemma Prop) Tactic {
	lemma = lemma.AsProp()

	// Conjunction-splitting: a
	// recursive definition bundles a list type's nil and
	// cons clauses into a single ∀-quantified conjunction (ALL, list_member,
	// PAIRWISE, list_map, ...). Each clause is independently a rewrite rule.
	// When the lemma is such a conjunction, dispatch to the multi-clause
	// path: build a per-clause Rewrite, compose via DeepRewrite, run a
	// single fixed-point rewrite pass over the goal's conclusion. The
	// single-clause case (the common one) falls through to the existing
	// single-equation logic below — zero behavior change.
	if clauses := splitConjunctiveClauses(lemma); len(clauses) > 1 {
		return leanRwTacticMultiClause(lemma, clauses)
	}

	coreOrig := rewriteOnlyTacticCore(lemma)

	denormLemma, lemmaSteps := denormalizeProp(lemma)
	var coreAlt Tactic
	if len(lemmaSteps) > 0 {
		coreInner := rewriteOnlyTacticCore(denormLemma)
		coreAlt = func(goal Prop) *SubGoals {
			inner := coreInner(goal)
			if inner == nil {
				return nil
			}
			return wrapLemmaWithDenorm(inner, lemma, lemmaSteps)
		}
	}

	// Bidirectional retry: when neither natural form (orig / denorm)
	// matches, try the lemma with its conclusion's equation flipped.
	// Reconstruction bridges via Spec + EqSym + Gen so child[0] still
	// α-equals the original lemma (dep tracking unaffected).
	flippedLemma := flipEqLemma(lemma)
	var coreFlipped Tactic
	if flippedLemma != nil {
		coreInner := rewriteOnlyTacticCore(flippedLemma)
		coreFlipped = func(goal Prop) *SubGoals {
			inner := coreInner(goal)
			if inner == nil {
				return nil
			}
			return wrapLemmaWithFlip(inner, lemma, flippedLemma)
		}
	}

	try := func(goal Prop) *SubGoals {
		sOrig := coreOrig(goal)
		if coreAlt == nil {
			if sOrig != nil {
				return sOrig
			}
			if coreFlipped != nil {
				return coreFlipped(goal)
			}
			return nil
		}
		sAlt := coreAlt(goal)
		switch {
		case sOrig == nil && sAlt == nil:
			if coreFlipped != nil {
				return coreFlipped(goal)
			}
			return nil
		case sOrig == nil:
			return sAlt
		case sAlt == nil:
			return sOrig
		case sAlt.Size() < sOrig.Size():
			return sAlt
		default:
			return sOrig
		}
	}

	return func(goal Prop) *SubGoals {
		if goal.AlphaEquals(lemma) {
			return nil
		}
		if s := try(goal); s != nil {
			return s
		}
		denormSG := denormalizeConclTactic(goal)
		if denormSG == nil {
			return nil
		}
		expanded := Tactic(try).expand(denormSG)
		if expanded == denormSG {
			return nil
		}
		return expanded
	}
}

// leanRwTacticMultiClause is the rewrite path for a conjunctive lemma
// (already split into per-clause thms by prop.SplitConjunctiveClauses).
// It builds a unification-based Rewrite per clause via
// prop.ContextEqRewriteOpt (which handles ∀-quantified equations and
// orients propositional facts to ⇔T/⇔F), composes them with DeepRewrite
// so a fired clause's RHS is immediately re-scanned by every other
// clause (a top-down fixed point), and applies
// the combined rewrite to the goal's conclusion.
//
// The per-clause Rewrites introduce each clause's term as a hyp (the
// ContextEqRewrite contract); those hyps are discharged against the
// proved split clauses, leaving a clean ⊢ goal_concl = new_concl
// bridge. child[0] is the ORIGINAL conjunctive lemma (so dep tracking
// records the lemma's key exactly as the single-equation path does);
// child[1] is the rewritten goal.
//
// Returns nil when no clause fires (goal conclusion unchanged), when the
// divergence whistle cut the rewrite, or when
// a clause hyp can't be discharged cleanly (defensive — keeps the
// rewrite sound by never emitting a bridge that still depends on an
// undischarged assumption).
func leanRwTacticMultiClause(lemma Prop, clauses []Prop) Tactic {
	// Each clause becomes a unification rewriter; DeepBeta is folded in
	// as a final member so the (λx.RHS)(arg) redexes that unifyEqRewrite
	// leaves behind get β-reduced inline — and, via DeepRewrite's
	// RewriteConclRhsRecur fixed-point, a β-exposed subterm is re-scanned
	// by every clause (rewriting and β interleaved).
	rewrites := make([]prop.Rewrite, 0, len(clauses)+1)
	// Ordered: permutative clauses self-feed inside this fixpoint
	// composition — same simp-set discipline as simp_with's clause
	// rules (see ContextEqRewriteOrdered); an ASSOC-class rotation
	// paired with a same-operator variants clause is AC-group ordered
	// (see prop.SimpSetACGates).
	clauseConcls := make([]Term, len(clauses))
	for i, c := range clauses {
		clauseConcls[i] = c.Conclusion()
	}
	acGates := prop.SimpSetACGates(clauseConcls)
	// One pre-CNF cache for the clause set: a node's normal form is
	// computed once per set, not once per clause.
	preCNF := new(prop.PreCNFCache)
	for i := range clauses {
		if acGates[i] {
			rewrites = append(rewrites, prop.ContextEqRewriteOrderedAC(preCNF, clauseConcls[i], true, true))
		} else {
			rewrites = append(rewrites, prop.ContextEqRewriteOrdered(preCNF, clauseConcls[i], true, true))
		}
	}
	rewrites = append(rewrites, prop.DeepBeta)
	// Whistled: the clause rewrites are lemma-fed unification rules
	// with allowExpand — termination is unproven, and a self-feeding
	// clause diverges inside this one tactic step where the
	// mergeTactics goal-level whistle cannot see it. A rewrite the
	// whistle cut does not apply: what it leaves is no normal form.
	// Each rewrite carries its clause term as a hyp.
	anyClause := func(pred func(Term) bool) bool { return utils.Any(clauseConcls, pred) }
	deepRw := prop.DeepRewriteWhistled(anyClause, rewrites...)

	return func(goal Prop) *SubGoals {
		if goal.AlphaEquals(lemma) {
			return nil
		}
		u, cut := deepRw(goal.Conclusion())
		if cut != nil || u == nil || Rhs(u).AlphaEquals(goal.Conclusion()) {
			return nil
		}
		// u : (clause terms as hyps) ⊢ goal_concl = new_concl.
		// Discharge each clause-term hyp using its proved split clause.
		for _, c := range clauses {
			if u.HasHyp(c.Conclusion()) {
				u = u.DeriveHypFrom(c)
			}
		}
		if u.NumHyps() != 0 {
			// A clause hyp survived (e.g. ContextEqRewrite normalized it
			// to a form that doesn't match c.Conclusion() syntactically).
			// Bail rather than emit an assumption-dependent bridge.
			return nil
		}

		newConcl := Rhs(u)
		child := MakeProp(newConcl, goal.Hyps()...)
		reconstruct := func(thms ...Prop) Prop {
			// thms[0] = lemma reproduction (closes via auto-match against
			// the cited entry; records the dep — a Thm or Promise).
			// thms[1] = proof of child (⊢ new_concl under goal hyps).
			//
			// A child closed by contradiction concludes ⊥ where it states
			// new_concl. It keeps the goal's hypotheses, so that theorem is
			// stronger than the goal as it stands, and the bridge has no
			// conclusion to carry back.
			if thms[1].Conclusion().Equals(F) && !newConcl.Equals(F) {
				return thms[1]
			}
			// Re-derive the rewrite bridge using the Thm-backed lemma from
			// thms[0] so the resulting Prop is Thm-backed too. Reusing the
			// `u` captured at setup time would propagate bare clauses (built
			// from `lemma.AsProp()`, which is a bare proposition whenever
			// the lemma arrived as a bare statement). The structural
			// rewrite chain (deepRw + DeriveHypFrom) is sound for bare Props
			// but the resulting bridge is a bare proposition, not
			// Thm/Promise, and AsThm panics downstream when goal_stack tries
			// to narrow it for the parent's PromisedThm().
			thmClauses := splitConjunctiveClauses(thms[0])
			ub, cut := deepRw(goal.Conclusion())
			if ub == nil || cut != nil {
				// deepRw must succeed here — it succeeded at setup with
				// statement-level clauses, uncut, and re-running with the
				// same goal is purely structural. A nil or a cut here
				// indicates an invariant breach worth surfacing rather than
				// silently producing a bare result.
				panic("leanRwTacticMultiClause: deepRw failed at reconstruct time")
			}
			for _, c := range thmClauses {
				if ub.HasHyp(c.Conclusion()) {
					ub = ub.DeriveHypFrom(c)
				}
			}
			return ub.EqSym().EqMP(thms[1])
		}
		return MakeSubGoals(goal, reconstruct, lemma.AsProp(), child)
	}
}

// flipEqLemma returns a structurally-flipped variant of the lemma:
// if its conclusion is `∀x1...xn. L = R` (or just `L = R`), returns a
// Prop whose conclusion is `∀x1...xn. R = L` (with the same hyps).
// Returns nil when:
//
//   - The conclusion is not an equation under ∀-binders.
//   - L α-equals R (flipping is a no-op).
//   - Any of x1...xn appears free in a hyp (the kernel-level Gen
//     used by wrapLemmaWithFlip's reconstruction would fail).
//
// The returned Prop is structural — not proved. wrapLemmaWithFlip
// derives the proved form on demand from the original lemma's proof.
func flipEqLemma(lemma Prop) Prop {
	vars, body := ext.DecomposesFORALL(lemma.Conclusion())
	l, r, ok := MatchesEQ(body)
	if !ok || l.AlphaEquals(r) {
		return nil
	}
	hyps := lemma.Hyps()
	for v := range vars.Iter() {
		for _, h := range hyps {
			if h.HasFree(v) {
				return nil
			}
		}
	}
	var flipped Term = Eq(r, l)
	for _, v := range vars.Backward() {
		flipped = ext.ForAll(v)(flipped).Core()
	}
	if flipped.AlphaEquals(lemma.Conclusion()) {
		return nil
	}
	return MakeProp(flipped, hyps...)
}

// wrapLemmaWithFlip takes inner SubGoals produced by running
// rewriteOnlyTacticCore against the FLIPPED lemma (so
// inner.ChildGoal(0) α-equals flippedLemma) and re-exposes origLemma
// as child[0]. The reconstruct function bridges from a proof of
// origLemma to a proof of flippedLemma via specialize + EqSym +
// generalize.
//
// Re-exposing origLemma keeps dep tracking keyed on the lemma's own
// key — agents and emit never see the internal flipped form.
func wrapLemmaWithFlip(inner *SubGoals, origLemma, flippedLemma Prop) *SubGoals {
	newChildren := make([]Prop, inner.Size())
	newChildren[0] = origLemma
	for i := 1; i < inner.Size(); i++ {
		newChildren[i] = inner.ChildGoal(i)
	}
	reconstruct := func(thms ...Prop) Prop {
		flippedThm := propFlipEqUnderForall(lemmaAsStated(origLemma, thms[0]))
		innerThms := make([]Prop, len(thms))
		innerThms[0] = flippedThm
		copy(innerThms[1:], thms[1:])
		return inner.Reconstruct(innerThms...)
	}
	return MakeSubGoals(inner.goal, reconstruct, newChildren...)
}

// propFlipEqUnderForall takes a proved Prop with conclusion
// `∀x1...xn. L = R` and produces a proved Prop with conclusion
// `∀x1...xn. R = L` via specialize + EqSym + generalize. The hyps
// come along unchanged. flipEqLemma's "no binder is free in any hyp"
// precondition guarantees the generalize step succeeds.
func propFlipEqUnderForall(thm Prop) Prop {
	vars, _ := ext.DecomposesFORALL(thm.Conclusion())
	p := WrapProp(thm)
	for v := range vars.Iter() {
		p = p.ConclForAllInst(v)
	}
	p = p.EqSym()
	for _, v := range vars.Backward() {
		p = p.ConclForAll(v)
	}
	return p
}

// splitConjunctiveClauses takes a thm of shape
//
//	⊢ ∀x₁...xₙ. c₁ ∧ c₂ ∧ ... ∧ cₖ
//
// and returns the per-clause thms with the ∀-prefix distributed onto
// each conjunct:
//
//	[⊢ ∀x₁...xₙ. c₁, ⊢ ∀x₁...xₙ. c₂, ..., ⊢ ∀x₁...xₙ. cₖ]
//
// This is conjunction-splitting: a recursive definition bundles a list
// type's nil clause and cons clause into a single ∀-quantified
// conjunction (e.g. ALL/list_member/PAIRWISE), but each clause is independently
// useful as a rewrite rule. Splitting lets a caller feed each clause to
// the rewrite engine separately.
//
// Mechanism:
//  1. DeepRewrite(ForAllANDRewrite) distributes the outer ∀ through the
//     ∧ to a fixed point: ⊢ ∀x.(a ∧ b) becomes ⊢ (∀x.a) ∧ (∀x.b).
//     A binder that doesn't occur in a given conjunct becomes a vacuous
//     ∀ over that clause — harmless, since the clause's rewrite LHS
//     simply doesn't mention that variable.
//  2. The top-level conjunction is peeled recursively via HypAND0 /
//     HypAND1 (each projects one conjunct, discharged against the proved
//     parent), flattening nested ∧ associativity.
//
// When the body (after the distribution pass) is not a top-level
// conjunction, returns [thm] unchanged. Idempotent on already-split
// (single-clause) inputs.
//
// Each returned clause is a fully proved Prop derived from the input —
// no new hypotheses, no trust injection.
func splitConjunctiveClauses(thm Prop) []Prop {
	distributed := WrapProp(thm).RewriteConcl(prop.DeepRewrite(prop.ForAllANDRewrite))
	return splitTopAND(distributed)
}

// splitTopAND recursively peels a top-level conjunction `⊢ l ∧ r` into
// `[⊢ l, ⊢ r]`, recursing into each side to flatten nested ∧. A
// non-conjunction prop returns `[thm]`.
func splitTopAND(thm *PropWrapper) []Prop {
	l, r, ok := ext.MatchesAND(thm.Conclusion())
	if !ok {
		return []Prop{thm}
	}
	left := HypAND0(l, r).DeriveHypFrom(thm)  // ⊢ l
	right := HypAND1(l, r).DeriveHypFrom(thm) // ⊢ r
	return append(splitTopAND(left), splitTopAND(right)...)
}
