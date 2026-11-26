/**
 * File: basic_tactics.go
 *
 * Implements core tactical functions and proof transformation algorithms for the tactic system.
 * This file contains the implementation of various tactics that transform proof goals into simpler
 * subgoals, following the goal-directed proof methodology.
 *
 * Key components:
 * - Basic propositional tactics: Handle boolean operations (AND, OR, IMPLY, IFF)
 * - Rewriting tactics: Transform expressions using equivalence rules
 * - Quantifier tactics: Handle universal and existential quantifiers
 * - Case analysis tactics: Split proofs into multiple cases for different assumptions
 *
 * The tactics implemented here are the building blocks of the proof automation system,
 * allowing for systematic decomposition of complex mathematical goals into simpler subgoals
 * that can be directly proven or further decomposed.
 */

package tactic

import (
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

var (
	MatchesNOT    = ext.MatchesNOT
	MatchesAND    = ext.MatchesAND
	MatchesOR     = ext.MatchesOR
	MatchesIFF    = ext.MatchesIFF
	MatchesIMPLY  = ext.MatchesIMPLY
	HypAND0       = prop.HypAND0
	HypAND1       = prop.HypAND1
	ByCases       = prop.ByCases
	RewriteOrRefl = prop.RewriteOrRefl
	NegRefl       = prop.NegRefl
)

/**
 * trivialTactic attempts to prove a goal through direct application of basic logical principles.
 * It applies rewriting to all hypotheses and the conclusion, then checks for several common
 * patterns that allow for immediate proof or simplification:
 *
 * Cases where goal is directly provable:
 * 1. ⊢ ⊤: Goal conclusion is true
 * 2. ⊥ ⊢ c: One hypothesis is false
 * 3. h ⊢ h: Conclusion matches a hypothesis
 * 4. h, ¬h ⊢ c: Contradictory hypotheses
 *
 * Cases where goal can be simplified:
 * 1. ..., ⊤ ⊢ c: Remove trivial true hypothesis
 * 2. ..., ¬c ⊢ c: Remove hypothesis that is negation of conclusion
 * 3. ..., x = _ ⊢ c: Remove variable binding hypothesis if x not free elsewhere
 *
 * The function applies these reductions concurrently for efficiency, using goroutines
 * to rewrite hypotheses and their negations in parallel.
 *
 * Parameters:
 *   - goal: The proposition to prove or simplify
 *
 * Returns:
 *   - A SubGoals structure with simplified subgoals if applicable
 *   - nil if no simplification is possible
 */
func trivialTactic(goal Prop) *SubGoals {
	if s := simplestTrivialTactic(goal); s != nil {
		return s
	}

	trivialRewrite := prop.TrivialNormalize

	wg := utils.Tasks{}
	negHyps := make([]Term, goal.NumHyps())
	rewriteHyps := make([]*PropWrapper, goal.NumHyps())
	rewriteNegHyps := make([]*PropWrapper, goal.NumHyps())
	for i := range goal.NumHyps() {
		h := goal.Hyp(i)
		wg.Go(func() {
			rewriteHyps[i] = trivialRewrite(h)
		})
		wg.Go(func() {
			negHyps[i] = ext.Eq(h, F)
			rewriteNegHyps[i] = trivialRewrite(negHyps[i])
		})
	}
	rewriteConcl := RewriteOrRefl(trivialRewrite, goal.Conclusion())
	wg.Wait()

	// ⊢ ⊤
	if Rhs(rewriteConcl).Equals(T) {
		thm := rewriteConcl.EqSym().EqMP(prop.DerivesTrue).AsThmCert()
		return MakeEmptySubGoals(goal, thm)
	}

	for i := range goal.NumHyps() {
		hi := goal.Hyp(i)
		if rewriteHyps[i] != nil {
			hi = Rhs(rewriteHyps[i])
		}
		// ⊥ ⊢ c
		if hi.Equals(F) {
			if rewriteHyps[i] == nil {
				return MakeEmptySubGoals(goal, prop.Assume(F).AsThmCert())
			}
			thm := rewriteHyps[i].LeftAssume().AsThmCert()
			return MakeEmptySubGoals(goal, thm)
		}
		// h ⊢ h
		if hi.AlphaEquals(Rhs(rewriteConcl)) {
			if rewriteHyps[i] == nil {
				return MakeEmptySubGoals(goal, rewriteConcl.RightAssume().AsThmCert())
			}
			thm := rewriteHyps[i].
				EqTrans(rewriteConcl.EqSym()).
				LeftAssume().AsThmCert()
			return MakeEmptySubGoals(goal, thm)

		}
		// h, ¬h ⊢ c
		for j := range goal.NumHyps() {
			if j == i {
				continue
			}
			nj := negHyps[j]
			if rewriteNegHyps[j] != nil {
				nj = Rhs(rewriteNegHyps[j])
			}
			if nj.AlphaEquals(hi) {
				var thm *PropWrapper
				if rewriteHyps[i] == nil && rewriteNegHyps[j] == nil {
					thm = prop.Assume(nj)
				} else if rewriteHyps[i] == nil {
					thm = rewriteNegHyps[j].RightAssume()
				} else if rewriteNegHyps[j] == nil {
					thm = rewriteHyps[i].LeftAssume()
				} else {
					thm = rewriteHyps[i].
						EqTrans(rewriteNegHyps[j].EqSym()).
						LeftAssume()
				}
				return MakeEmptySubGoals(goal, thm.LeftAssume().AsThmCert())
			}
		}
	}

	for i := range goal.NumHyps() {
		hi := goal.Hyp(i)
		if rewriteHyps[i] != nil {
			hi = Rhs(rewriteHyps[i])
		}
		// goal: ..., ⊤ ⊢ c
		// subgoal:
		//		... ⊢ c
		if hi.Equals(T) {
			return dropHypSubGoals(goal, i)
		}

		// goal: ..., ¬c ⊢ c
		// subgoal:
		//		... ⊢ c
		ni := negHyps[i]
		if rewriteNegHyps[i] != nil {
			ni = Rhs(rewriteNegHyps[i])
		}
		if ni.AlphaEquals(Rhs(rewriteConcl)) {
			return dropHypSubGoals(goal, i)
		}
	}
	return nil
}

// The simplest version of trivial tactic. No rewrites, just essential checks.
func simplestTrivialTactic(goal Prop) *SubGoals {
	// ⊢ ⊤
	if goal.Conclusion().Equals(T) {
		return MakeEmptySubGoals(goal, prop.DerivesTrue.AsThmCert())
	}
	// ⊥ ⊢ c
	if goal.HasHyp(F) {
		return MakeEmptySubGoals(goal, prop.Assume(F).AsThmCert())
	}
	// h ⊢ h
	if goal.HasHyp(goal.Conclusion()) {
		return MakeEmptySubGoals(goal, prop.Assume(goal.Conclusion()).AsThmCert())
	}
	for i := range goal.NumHyps() {
		hi := goal.Hyp(i)
		// goal: ..., ⊤ ⊢ c
		// subgoal:
		//		... ⊢ c
		if hi.Equals(T) {
			return dropHypSubGoals(goal, i)
		}
		// goal: ..., x = _ ⊢ c
		// subgoal:
		//		... ⊢ c
		if l, r, ok := MatchesEQ(goal.Hyp(i)); ok {
			varHypRemovable := false
			if x, ok := l.AsVar(); ok {
				varHypRemovable = !r.HasFree(x) &&
					!goal.Conclusion().HasFree(x) &&
					prop.NotFreeInHyps(goal, x, goal.Hyp(i))
			}
			if x, ok := r.AsVar(); ok && !varHypRemovable {
				varHypRemovable = !l.HasFree(x) &&
					!goal.Conclusion().HasFree(x) &&
					prop.NotFreeInHyps(goal, x, goal.Hyp(i))
			}
			if varHypRemovable {
				return dropHypSubGoals(goal, i)
			}
		}
		// h, ¬h ⊢ c
		for j := range goal.NumHyps() {
			hj := goal.Hyp(j)
			if j == i {
				continue
			}

			if nj := MatchesNOT(hj); nj != nil && nj.AlphaEquals(hi) {
				return MakeEmptySubGoals(goal, prop.Contradict(hi).AsThmCert())
			}
		}
	}
	return nil
}

// goal: ... ⊢ A ∧ B
// subgoal:
//
//	... ⊢ A
//	... ⊢ B
func ConclConjTactic(goal Prop) *SubGoals {
	if t0, t1, ok := MatchesAND(goal.Conclusion()); ok {
		// Degenerate A∧A: agent-natural answer is "to prove A∧A, prove A
		// (once)". Produce one subgoal and reuse the same proof for both
		// AND-intro branches in the emit. Chain callers route
		// through trivial cleanup first and never hit this case, but
		// agent-direct callers do — and a single ⊢A subgoal is what they
		// expect from a "split conjunction" tactic on an idempotent input.
		if t0.AlphaEquals(t1) {
			goal0 := MakeProp(t0, goal.Hyps()...)
			reconstruct := func(thms ...Prop) Prop {
				if thms[0].Conclusion().Equals(F) {
					return thms[0]
				}
				// ConclAND(A,A) is `p,q ⊢ p∧q` whose hyps dedup to `A ⊢ A∧A`.
				// One DeriveHypFrom consumes that single A hyp via thms[0].
				return prop.ConclAND(t0, t1).DeriveHypFrom(thms[0])
			}
			return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, goal0)}, goal0)
		}
		goal0 := MakeProp(t0, goal.Hyps()...)
		goal1 := MakeProp(t1, goal.Hyps()...)
		reconstruct := func(thms ...Prop) Prop {
			if thms[0].Conclusion().Equals(F) {
				return thms[0]
			}
			if thms[1].Conclusion().Equals(F) {
				return thms[1]
			}
			return prop.ConclAND(t0, t1).
				DeriveHypFrom(thms[0]).
				DeriveHypFrom(thms[1])
		}
		return MakeTrackedSubGoals(goal, reconstruct,
			[][]int{keptSuccessors(goal, goal0), keptSuccessors(goal, goal1)}, goal0, goal1)
	}
	return nil
}

// goal: ... ⊢ A ∧ B ∧ … ∧ Z   (any association)
// subgoals (flat — one per leaf conjunct):
//
//	... ⊢ A
//	... ⊢ B
//	  …
//	... ⊢ Z
//
// Unlike ConclConjTactic (strictly binary), this flattens the ENTIRE
// ∧-spine in a single step, so a wide flat conjunction becomes N sibling
// subgoals at once instead of an (N-1)-deep binary peel. The reconstruct
// re-nests the N proofs into the goal's ORIGINAL association tree
// (rebuildConj mirrors MatchesAND's split), so it is sound regardless of
// how the conjunction was parenthesized. Returns nil when the conclusion
// is not a conjunction (so callers/enumeration treat it as inapplicable).
func ConclConjAllTactic(goal Prop) *SubGoals {
	concl := goal.Conclusion()
	if _, _, ok := MatchesAND(concl); !ok {
		return nil
	}
	clauses := ext.DecomposesAND(concl)
	childGoals := make([]Prop, len(clauses))
	successors := make([][]int, len(clauses))
	for i, c := range clauses {
		childGoals[i] = MakeProp(c, goal.Hyps()...)
		successors[i] = keptSuccessors(goal, childGoals[i])
	}
	reconstruct := func(thms ...Prop) Prop {
		// ⊥ short-circuit: a child closed by refutation proves the
		// whole goal outright (mirrors ConclConjTactic's per-branch
		// F check). Must precede rebuildConj, whose DeriveHypFrom
		// expects each thm's conclusion to be the matching conjunct.
		for _, t := range thms {
			if t.Conclusion().Equals(F) {
				return t
			}
		}
		thm, rest := rebuildConj(concl, thms)
		Assert(len(rest) == 0)
		return thm
	}
	return MakeTrackedSubGoals(goal, reconstruct, successors, childGoals...)
}

// rebuildConj reassembles a proof of `... ⊢ t` from per-leaf-conjunct
// proofs, consuming thms left-to-right and mirroring t's association
// tree so the rebuilt conclusion is α-identical to t. Returns the
// assembled proof plus the unconsumed tail of thms. The leaf order it
// consumes matches ext.DecomposesAND (both recurse via MatchesAND
// left-then-right), so ConclConjAllTactic's childGoals line up.
func rebuildConj(t Term, thms []Prop) (Prop, []Prop) {
	l, r, ok := MatchesAND(t)
	if !ok {
		return thms[0], thms[1:]
	}
	lThm, rest := rebuildConj(l, thms)
	rThm, rest := rebuildConj(r, rest)
	// ConclAND(l, r) is `l, r ⊢ l∧r`. When l and r are α-equal (e.g.
	// the A∧A spine of A∧A∧A) its two hyps collapse to one, so a blind
	// DeriveHypFrom for each side would fail on the second (no such
	// hyp left). MaybeDeriveTrans discharges a side only when the hyp
	// is actually present, no-op otherwise — sound for both cases.
	out := WrapProp(lThm).MaybeDeriveTrans(prop.ConclAND(l, r))
	return WrapProp(rThm).MaybeDeriveTrans(out), rest
}

// goal: ... ⊢ A ∨ B
// subgoal:
//
//	..., ¬A ⊢ B if B is larger or A itself contains ¬.
//	..., ¬B ⊢ A if A is larger or B itself contains ¬.
//	..., ¬A, ¬B ⊢ ⊥ if A and B both contain ¬.
func ConclDisjTactic(goal Prop) *SubGoals {
	if t0, t1, ok := MatchesOR(goal.Conclusion()); ok {
		// Degenerate A∨A: same shape-collapses-to-A logic as conclConj.
		// One subgoal ⊢A; reconstruct via OR-intro on either side.
		if t0.AlphaEquals(t1) {
			goal0 := MakeProp(t0, goal.Hyps()...)
			reconstruct := func(thms ...Prop) Prop {
				if thms[0].Conclusion().Equals(F) {
					return thms[0]
				}
				return prop.ConclOR0(t0, t1).DeriveHypFrom(thms[0])
			}
			return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, goal0)}, goal0)
		}
		nt0, nt1 := MatchesNOT(t0), MatchesNOT(t1)
		if nt0 != nil && nt1 != nil {
			goal0 := MakeProp(F, append(goal.Hyps(), nt0, nt1)...)
			reconstruct := func(thms ...Prop) Prop {
				if !thms[0].HasHyp(nt0) && !thms[0].HasHyp(nt1) {
					return thms[0]
				}
				p := Prop(thms[0])
				p = HypAND0(nt0, nt1).MaybeDeriveTrans(p)
				p = HypAND1(nt0, nt1).MaybeDeriveTrans(p)
				nt0Andnt1 := And(nt0, nt1)
				return NegRefl(
					Not(nt0Andnt1), goal.Conclusion()).
					EqMP(WrapProp(p).NegHyp(nt0Andnt1))
			}
			return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, goal0)}, goal0)
		}
		if nt0 != nil ||
			(nt0 == nil && nt1 == nil && t1.Size() >= t0.Size()) {
			if nt0 == nil {
				nt0 = Not(t0)
			}
			goal0 := MakeProp(t1, append(goal.Hyps(), nt0)...)
			reconstruct := func(thms ...Prop) Prop {
				if IsStronger(thms[0], goal) {
					return thms[0]
				}
				p := weakenConcl(thms[0], t1)
				if p.HasHyp(nt0) {
					p = p.MoveHypsToConcl(nt0.AlphaEquals)
					p = prop.CommuteOR(t1, Not(nt0)).EqMP(p)
					if !p.Conclusion().AlphaEquals(goal.Conclusion()) {
						// This happens when they differ by double negation.
						p = NegRefl(
							p.Conclusion(), goal.Conclusion()).
							EqMP(p)
					}
					return p
				}
				return prop.ConclOR1(t0, p.Conclusion()).
					DeriveHypFrom(p)
			}
			return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, goal0)}, goal0)
		}
		if nt1 != nil ||
			(nt0 == nil && nt1 == nil && t1.Size() < t0.Size()) {
			if nt1 == nil {
				nt1 = Not(t1)
			}
			goal0 := MakeProp(t0, append(goal.Hyps(), nt1)...)
			reconstruct := func(thms ...Prop) Prop {
				if IsStronger(thms[0], goal) {
					return thms[0]
				}
				p := weakenConcl(thms[0], t0)
				if p.HasHyp(nt1) {
					p = p.MoveHypsToConcl(nt1.AlphaEquals)
					if !p.Conclusion().AlphaEquals(goal.Conclusion()) {
						// This happens when they differ by double negation.
						p = NegRefl(
							p.Conclusion(), goal.Conclusion()).
							EqMP(p)
					}
					return p
				}
				return prop.ConclOR0(p.Conclusion(), t1).
					DeriveHypFrom(p)
			}
			return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, goal0)}, goal0)
		}
		panic("Should not reach here")
	}
	return nil
}

// goal: ... ⊢ A ⇔ B
// subgoal:
//
//	..., B ⊢ A
//	..., A ⊢ B
func ConclIffTactic(goal Prop) *SubGoals {
	if t0, t1, ok := MatchesIFF(goal.Conclusion()); ok {
		if t0.AlphaEquals(t1) { // see ConclConjTactic
			return nil
		}
		goal0 := MakeProp(t0, append(goal.Hyps(), t1)...)
		goal1 := MakeProp(t1, append(goal.Hyps(), t0)...)
		reconstruct := func(thms ...Prop) Prop {
			if thms[0].Conclusion().Equals(F) && !thms[0].HasHyp(t1) {
				return thms[0]
			}
			if thms[1].Conclusion().Equals(F) && !thms[1].HasHyp(t0) {
				return thms[1]
			}
			return weakenConcl(thms[0], t0).Deduct(weakenConcl(thms[1], t1))
		}
		return MakeTrackedSubGoals(goal, reconstruct,
			[][]int{keptSuccessors(goal, goal0), keptSuccessors(goal, goal1)}, goal0, goal1)
	}
	return nil
}

// goal: ... ⊢ A ⇒ B
// subgoal:
//
//	..., A ⊢ B
func ConclImplyTactic(goal Prop) *SubGoals {
	if t0, t1, ok := MatchesIMPLY(goal.Conclusion()); ok {
		if t0.AlphaEquals(t1) { // see ConclConjTactic
			return nil
		}
		goal0 := MakeProp(t1, append(goal.Hyps(), t0)...)
		reconstruct := func(thms ...Prop) Prop {
			if !thms[0].HasHyp(t0) && thms[0].Conclusion().Equals(F) {
				return thms[0]
			}
			return weakenConcl(thms[0], t1).PromoteHyp(t0)
		}
		return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, goal0)}, goal0)
	}
	return nil
}

// goal: ..., A ∧ B ⊢ C
// subgoal:
//
//	..., A, B ⊢ C
func HypConjTactic(goal Prop) *SubGoals {
	for i := range goal.NumHyps() {
		if t0, t1, ok := MatchesAND(goal.Hyp(i)); ok {
			// Degenerate A∧A in hyp: dedup to single A hyp. Single subgoal
			// with reconstruct that re-introduces A∧A from A via HypAND0.
			// (see ConclConjTactic for the agent-rationale)
			if t0.AlphaEquals(t1) {
				goal0 := MakeProp(goal.Conclusion(), append(restHyps(goal, i), t0)...)
				reconstruct := func(thms ...Prop) Prop {
					if !thms[0].HasHyp(t0) {
						return thms[0]
					}
					return HypAND0(t0, t1).MaybeDeriveTrans(thms[0])
				}
				return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, hypImages(goal, i, t0))}, goal0)
			}
			goal0 := MakeProp(goal.Conclusion(), append(restHyps(goal, i), t0, t1)...)
			reconstruct := func(thms ...Prop) Prop {
				if !thms[0].HasHyp(t0) && !thms[0].HasHyp(t1) {
					return thms[0]
				}
				p := HypAND0(t0, t1).MaybeDeriveTrans(thms[0])
				p = HypAND1(t0, t1).MaybeDeriveTrans(p)
				return p
			}
			// The conjunction becomes two hypotheses: no single successor.
			return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, hypImages(goal, i, nil))}, goal0)
		}
	}
	return nil
}

// goal: ..., ∀x⃗.(A ∧ B) ⊢ C
// subgoal:
//
//	..., ∀x⃗.A, ∀x⃗.B ⊢ C
//
// The ∀-prefixed sibling of HypConjTactic: the prefix distributes over
// the conjuncts. One distribution level per call — a conjunct that is
// itself a (∀-prefixed) conjunction splits on the caller's next pass;
// By's conditioning stage runs both tactics to fixpoint. Picks the
// first hyp with a non-empty ∀-prefix over a conjunctive matrix
// (bare A ∧ B hyps are HypConjTactic's).
func HypForallConjTactic(goal Prop) *SubGoals {
	for i := range goal.NumHyps() {
		h := goal.Hyp(i)
		vars, matrix := ext.DecomposesFORALL(h)
		if vars.Empty() {
			continue
		}
		t0, t1, ok := MatchesAND(matrix)
		if !ok {
			continue
		}
		// bridge(project) : h ⊢ ∀x⃗.side — instantiate the prefix at
		// its own binders, project the conjunct, re-∀-close.
		bridge := func(project Prop) Prop {
			w := prop.WrapProp(prop.Assume(h))
			for v := range vars.Iter() {
				w = w.ConclForAllInst(v)
			}
			w = w.DeriveTrans(project)
			for _, v := range vars.Backward() {
				w = w.ConclForAll(v)
			}
			return w
		}
		bridge0 := bridge(HypAND0(t0, t1))
		bridge1 := bridge(HypAND1(t0, t1))
		c0, c1 := bridge0.Conclusion(), bridge1.Conclusion()
		goal0 := MakeProp(goal.Conclusion(), append(restHyps(goal, i), c0, c1)...)
		if goal0.AlphaEquals(goal) {
			return nil
		}
		reconstruct := func(thms ...Prop) Prop {
			out := thms[0]
			if out.HasHyp(c0) {
				out = WrapProp(bridge0).DeriveTrans(out)
			}
			if out.HasHyp(c1) {
				out = WrapProp(bridge1).DeriveTrans(out)
			}
			return out
		}
		// The conjunction becomes two hypotheses: no single successor.
		return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, hypImages(goal, i, nil))}, goal0)
	}
	return nil
}

// goal: ..., A ∨ B ⊢ C
// subgoal:
//
//	..., A ⊢ C
//	..., B ⊢ C
//
// Picks the first ∨-shaped hyp. HypDisjTacticAt targets a specific
// index (both call the same body — hypDisjTacticAt).
func HypDisjTactic(goal Prop) *SubGoals {
	for i := range goal.NumHyps() {
		if sg := hypDisjTacticAt(goal, i); sg != nil {
			return sg
		}
	}
	return nil
}

// HypDisjTacticAt is the index-targeted variant: split the ∨-hyp at
// hypIdx (or return nil if that hyp is out of range or not A∨B).
// Same "did not apply" contract as HypDisjTactic — the caller gets
// nil and a clean failure from the wire layer instead of a wrong hyp
// being split (the recurring "split_disj ignored my hyp_index" defeat).
// A membership in a set-builder that reads as A∨B is split through its
// reading (throughMembershipAt), as are the ∃, ⇔ and ⇒ the other
// index-targeted splits open; the pick-first forms do not read it.
func HypDisjTacticAt(goal Prop, hypIdx int) *SubGoals {
	if hypIdx < 0 || hypIdx >= goal.NumHyps() {
		return nil
	}
	return throughMembershipAt(goal, hypIdx, hypDisjTacticAt)
}

// hypDisjTacticAt is the shared per-hyp body. Callers guarantee the
// index is in range; the shape check + degenerate A∨A collapse both
// live here so both entry points (loop + at-index) share exactly one
// implementation of the split logic.
func hypDisjTacticAt(goal Prop, i int) *SubGoals {
	t0, t1, ok := MatchesOR(goal.Hyp(i))
	if !ok {
		return nil
	}
	// Degenerate A∨A in hyp: case-analysis collapses (both branches
	// give the same A ⊢ C). Single subgoal; reconstruct still uses
	// ByCases but feeds the same proof into both branches.
	// (see ConclConjTactic for the agent-rationale)
	if t0.AlphaEquals(t1) {
		goal0 := MakeProp(goal.Conclusion(), append(restHyps(goal, i), t0)...)
		reconstruct := func(thms ...Prop) Prop {
			if !thms[0].HasHyp(t0) {
				return thms[0]
			}
			concl := goal.Conclusion()
			if thms[0].Conclusion().Equals(F) {
				concl = F
			}
			// ByCases hyps `[t0∨t1, t0⇒c, t1⇒c]` dedup with t0=t1
			// to `[A∨A, A⇒c]`. One DeriveHypFrom consumes A⇒c; a
			// second would panic because that hyp is gone.
			return ByCases(concl, t0, t1).
				DeriveHypFrom(weakenConcl(thms[0], concl).PromoteHyp(t0))
		}
		return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, hypImages(goal, i, t0))}, goal0)
	}
	hyps := restHyps(goal, i)
	goal0 := MakeProp(goal.Conclusion(), append(hyps, t0)...)
	goal1 := MakeProp(goal.Conclusion(), append(hyps, t1)...)
	reconstruct := func(thms ...Prop) Prop {
		if !thms[0].HasHyp(t0) {
			return thms[0]
		}
		if !thms[1].HasHyp(t1) {
			return thms[1]
		}
		concl := goal.Conclusion()
		if thms[0].Conclusion().Equals(F) && thms[1].Conclusion().Equals(F) {
			concl = F
		}
		return ByCases(concl, t0, t1).
			DeriveHypFrom(weakenConcl(thms[0], concl).PromoteHyp(t0)).
			DeriveHypFrom(weakenConcl(thms[1], concl).PromoteHyp(t1))
	}
	// In each branch the disjunction descends into the disjunct assumed there.
	return MakeTrackedSubGoals(goal, reconstruct,
		[][]int{hypSuccessorsOf(goal0, hypImages(goal, i, t0)), hypSuccessorsOf(goal1, hypImages(goal, i, t1))},
		goal0, goal1)
}

// goal: ..., A ⇔ B ⊢ C
// subgoal:
//
//	..., A, B ⊢ C
//	..., ¬A, ¬B ⊢ C
//
// Picks the first ⇔-shaped hyp. HypIffTacticAt targets a specific
// index (both call the same body — hypIffTacticAt).
func HypIffTactic(goal Prop) *SubGoals {
	for i := range goal.NumHyps() {
		if sg := hypIffTacticAt(goal, i); sg != nil {
			return sg
		}
	}
	return nil
}

// HypIffTacticAt is the index-targeted variant: split the ⇔-hyp at
// hypIdx (or return nil if that hyp is out of range or not A⇔B).
// See HypDisjTacticAt for the rationale.
func HypIffTacticAt(goal Prop, hypIdx int) *SubGoals {
	if hypIdx < 0 || hypIdx >= goal.NumHyps() {
		return nil
	}
	return throughMembershipAt(goal, hypIdx, hypIffTacticAt)
}

func hypIffTacticAt(goal Prop, i int) *SubGoals {
	t0, t1, ok := MatchesIFF(goal.Hyp(i))
	if !ok {
		return nil
	}
	if t0.AlphaEquals(t1) { // see ConclConjTactic
		return nil
	}
	nt0, nt1 := MatchesNOT(t0), MatchesNOT(t1)
	if nt0 == nil {
		nt0 = Not(t0)
	}
	if nt1 == nil {
		nt1 = Not(t1)
	}
	goal0 := MakeProp(goal.Conclusion(), append(restHyps(goal, i), t0, t1)...)
	goal1 := MakeProp(goal.Conclusion(), append(restHyps(goal, i), nt0, nt1)...)
	reconstruct := func(thms ...Prop) Prop {
		if !thms[0].HasHyp(t0) && !thms[0].HasHyp(t1) {
			return thms[0]
		}
		if !thms[1].HasHyp(nt0) && !thms[1].HasHyp(nt1) {
			return thms[1]
		}
		concl := goal.Conclusion()
		if thms[0].Conclusion().Equals(F) && thms[1].Conclusion().Equals(F) {
			concl = F
		}
		s, ns := And(t0, t1), And(nt0, nt1)
		p0 := HypAND0(t0, t1).MaybeDeriveTrans(thms[0])
		p0 = HypAND1(t0, t1).MaybeDeriveTrans(p0)
		p0 = weakenConcl(p0, concl).PromoteHyp(s)
		p1 := HypAND0(nt0, nt1).MaybeDeriveTrans(thms[1])
		p1 = HypAND1(nt0, nt1).MaybeDeriveTrans(p1)
		p1 = weakenConcl(p1, concl).PromoteHyp(ns)
		p := ByCases(concl, s, ns).
			DeriveHypFrom(p0).
			DeriveHypFrom(p1)
		// Rewrite only the RHS (the (p∧q)∨(¬p∧¬q) side) so it lines up
		// with the unreduced Or(s, ns) rebuilt below. Rewriting the WHOLE
		// conclusion would deep-beta-reduce the iff's LHS too — when t0/t1
		// carry an unreduced redex (e.g. from instantiate-ing a higher-order
		// ∀P lemma), LeftAssume would then assume the *reduced* (t0'⇔t1'),
		// which is not a hyp of `goal` (it has the unreduced (t0⇔t1)),
		// tripping the IsStronger assert in MakeSubGoals.
		return prop.BinaryThms["(p ⇔ q) ⇔ ((p ∧ q) ∨ (¬p ∧ ¬q))"](t0, t1).
			RewriteConclRhs(prop.BasicRewrite).
			EqTrans(RewriteOrRefl(prop.BasicRewrite, Or(s, ns)).
				EqSym()).
			LeftAssume().
			DeriveTrans(p)
	}
	// Each branch holds two hypotheses for the ⇔: no single successor.
	dropped := hypImages(goal, i, nil)
	return MakeTrackedSubGoals(goal, reconstruct,
		[][]int{hypSuccessorsOf(goal0, dropped), hypSuccessorsOf(goal1, dropped)}, goal0, goal1)
}

// goal: ..., A ⇒ B ⊢ C
// subgoal:
//
//	..., ¬A ⊢ C
//	..., B ⊢ C
//
// Picks the first ⇒-shaped hyp. HypImplyTacticAt targets a specific
// index (both call the same body — hypImplyTacticAt).
func HypImplyTactic(goal Prop) *SubGoals {
	for i := range goal.NumHyps() {
		if sg := hypImplyTacticAt(goal, i); sg != nil {
			return sg
		}
	}
	return nil
}

// HypImplyTacticAt is the index-targeted variant: split the ⇒-hyp at
// hypIdx (or return nil if that hyp is out of range or not A⇒B).
// See HypDisjTacticAt for the rationale.
func HypImplyTacticAt(goal Prop, hypIdx int) *SubGoals {
	if hypIdx < 0 || hypIdx >= goal.NumHyps() {
		return nil
	}
	return throughMembershipAt(goal, hypIdx, hypImplyTacticAt)
}

func hypImplyTacticAt(goal Prop, i int) *SubGoals {
	t0, t1, ok := MatchesIMPLY(goal.Hyp(i))
	if !ok {
		return nil
	}
	if t0.AlphaEquals(t1) { // see ConclConjTactic
		return nil
	}
	hyps, nt0 := restHyps(goal, i), Not(t0)
	goal0 := MakeProp(goal.Conclusion(), append(hyps, nt0)...)
	// A ⇒ ¬A says ¬A, and both cases of the split assume it: one subgoal.
	// ByCases hyps `[¬A∨¬A, ¬A⇒c, ¬A⇒c]` dedup to `[¬A∨¬A, ¬A⇒c]`, so the
	// one case's proof discharges the implication and a second
	// DeriveHypFrom would find it gone (as hypDisjTacticAt's A∨A).
	if nt0.AlphaEquals(t1) {
		reconstruct := func(thms ...Prop) Prop {
			if !thms[0].HasHyp(nt0) {
				return thms[0]
			}
			concl := goal.Conclusion()
			if thms[0].Conclusion().Equals(F) {
				concl = F
			}
			return ByCases(concl, nt0, t1).
				DeriveHypFrom(weakenConcl(thms[0], concl).PromoteHyp(nt0)).
				DeriveHypFrom(prop.BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](t0, t1).
					LeftAssume())
		}
		return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, hypImages(goal, i, nt0))}, goal0)
	}
	goal1 := MakeProp(goal.Conclusion(), append(hyps, t1)...)
	reconstruct := func(thms ...Prop) Prop {
		if !thms[0].HasHyp(nt0) {
			return thms[0]
		}
		if !thms[1].HasHyp(t1) {
			return thms[1]
		}

		var prop0, prop1, p *PropWrapper
		if thms[0].Conclusion().Equals(F) && thms[1].Conclusion().Equals(F) {
			prop0, prop1 = WrapProp(thms[0]), WrapProp(thms[1])
			p = ByCases(F, nt0, t1)
		} else {
			prop0 = weakenConcl(thms[0], goal.Conclusion())
			prop1 = weakenConcl(thms[1], goal.Conclusion())
			p = ByCases(goal0.Conclusion(), nt0, t1)
		}
		return p.
			DeriveHypFrom(prop0.PromoteHyp(nt0)).
			DeriveHypFrom(prop1.PromoteHyp(t1)).
			DeriveHypFrom(prop.BinaryThms["(p ⇒ q) ⇔ (¬p ∨ q)"](t0, t1).
				LeftAssume())
	}
	// The implication descends into the negated antecedent in one
	// branch and the consequent in the other.
	return MakeTrackedSubGoals(goal, reconstruct,
		[][]int{hypSuccessorsOf(goal0, hypImages(goal, i, nt0)), hypSuccessorsOf(goal1, hypImages(goal, i, t1))},
		goal0, goal1)
}

// goal: ..., ¬A ⊢ ¬C if A is the largest negated hypothesis.
// subgoal:
//
//	..., C ⊢ A
func ContrapositionTactic(goal Prop) *SubGoals {
	nc := MatchesNOT(goal.Conclusion())
	if goal.Conclusion().Equals(F) || nc != nil {
		largestNegHyp := -1
		for i := range goal.NumHyps() {
			if MatchesNOT(goal.Hyp(i)) != nil {
				if largestNegHyp == -1 ||
					goal.Hyp(i).Size() > goal.Hyp(largestNegHyp).Size() {
					largestNegHyp = i
				}
			}
		}
		if largestNegHyp != -1 {
			nt := MatchesNOT(goal.Hyp(largestNegHyp))
			// The negated hypothesis becomes the conclusion: dropped from
			// the hypotheses, with no successor there.
			dropped := hypImages(goal, largestNegHyp, nil)
			if goal.Conclusion().Equals(F) {
				goal0 := MakeProp(nt, restHyps(goal, largestNegHyp)...)
				reconstruct := func(thms ...Prop) Prop {
					if thms[0].Conclusion().Equals(F) {
						return thms[0]
					}
					return WrapProp(thms[0]).NegConcl()
				}
				return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, dropped)}, goal0)
			}
			goal0 := MakeProp(nt, append([]Term{nc}, restHyps(goal, largestNegHyp)...)...)
			reconstruct := func(thms ...Prop) Prop {
				if IsStronger(thms[0], goal) {
					return thms[0]
				}
				p := WrapProp(thms[0])
				if p.Conclusion().AlphaEquals(nt) && !p.HasHyp(nc) {
					return p.NegConcl()
				}
				if p.Conclusion().Equals(F) {
					return p.NegHyp(nc)
				}
				return p.Contraposition(nc)
			}
			return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, dropped)}, goal0)
		}
	}
	return nil
}

/**
 * boolOpSimplifyTactic transforms goals containing boolean operations into simpler forms.
 * It recognizes specific patterns in the conclusion or hypotheses and applies appropriate
 * transformations to simplify the goal structure. Each transformation produces at most
 * one subgoal.
 *
 * Transformations for conclusions:
 * 1. ⊢ A ∨ B: Transforms to "..., ¬A, ¬B ⊢ ⊥" (proof by contradiction)
 * 2. ⊢ A ⇒ B: Transforms to "..., A ⊢ B" (moves antecedent to hypotheses)
 *
 * Transformations for hypotheses:
 * 1. A ∧ B ⊢ C: Transforms to "..., A, B ⊢ C" (splits conjunction into separate hypotheses)
 * 2. ..., ¬A ⊢ ¬C: Transforms to "..., C ⊢ A"  if A is the largest negated hypothesis.
 *
 * For each transformation, the function provides a reconstruction function that creates
 * a proof of the original goal from proofs of the subgoals. This allows for compositional
 * proof construction where complex proofs are built from simpler ones.
 *
 * Parameters:
 *   - goal: The proposition to simplify
 *
 * Returns:
 *   - A SubGoals structure with simplified subgoals if applicable
 *   - nil if no simplification is possible
 */
var boolOpSimplifyTactic = recoveringNested(boolOpSimplifyNestedUnder(fullSearch))

// recoveringNested gives a nested-form fixpoint the entry recover the
// standalone forms carry, for the callers that run one on its own.
func recoveringNested(inner Tactic) Tactic {
	return func(p Prop) (result *SubGoals) {
		defer func() {
			if r := recover(); r != nil {
				switch r.(type) {
				case searchAbandoned, breadthExceeded:
					result = nil
				default:
					panic(r)
				}
			}
		}()
		return inner(p)
	}
}

// boolOpSimplifyNestedUnder is the form Basic and TrivialSimplify
// compose: no entry recover, so a refusal inside propagates to the
// outer driver (see mergeTacticsNestedUnder).
func boolOpSimplifyNestedUnder(mode _SearchMode) Tactic {
	return mergeTacticsNestedUnder(mode,
		simplestTrivialTactic,
		ConclDisjTactic,
		HypConjTactic,
		ConclImplyTactic,
		ContrapositionTactic,
	)
}

// RewriteTactic normalizes terms via basic rewrites.
var RewriteTactic = rewriteTactic(prop.BasicRewrite)

// RewriteTactic normalizes terms via basic rewrites.
var CondRewriteTactic = rewriteTactic(
	prop.BasicRewritesWith(prop.CondElimRewrite, prop.CondSwapRewrite))

/**
 * boolOpDivideTactic decomposes goals containing boolean operations into multiple subgoals.
 * Unlike boolOpSimplifyTactic which produces at most one subgoal, this tactic can create
 * multiple subgoals that must all be proved to establish the original goal.
 *
 * Transformations for conclusions:
 * 1. A ∧ B: Transforms to two subgoals "... ⊢ A" and "... ⊢ B"
 *    (to prove a conjunction, prove each conjunct separately)
 * 2. A ⇔ B: Transforms to two subgoals "..., B ⊢ A" and "..., A ⊢ B"
 *    (to prove an equivalence, prove both directions)
 *
 * Transformations for hypotheses:
 * 1. A ∨ B: Transforms to two subgoals "..., A ⊢ C" and "..., B ⊢ C"
 *    (case analysis - prove goal assuming each disjunct)
 * 2. A ⇔ B: Transforms to two subgoals "..., A, B ⊢ C" and "..., ¬A, ¬B ⊢ C"
 *    (case analysis using both sides of equivalence)
 * 3. A ⇒ B: Transforms to two subgoals "..., ¬A ⊢ C" and "..., B ⊢ C"
 *    (case analysis - either antecedent is false or consequent is true)
 *
 * Each transformation includes a reconstruct function that combines proofs of subgoals
 * to produce a proof of the original goal, handling various special cases like when
 * some subgoals prove contradiction (F).
 *
 * Parameters:
 *   - goal: The proposition to decompose
 *
 * Returns:
 *   - A SubGoals structure with decomposed subgoals if applicable
 *   - nil if no decomposition is possible
 */
var boolOpDivideTactic = recoveringNested(boolOpDivideNestedUnder(fullSearch))

// boolOpDivideNestedUnder is the form Basic composes: no entry recover,
// so a refusal inside propagates to the outer driver (see
// mergeTacticsNestedUnder). The case splits live here, so a bounded
// Basic() must bound this fixpoint too — a deadline on the outer driver
// alone never reaches a split in progress.
func boolOpDivideNestedUnder(mode _SearchMode) Tactic {
	return mergeTacticsNestedUnder(mode,
		simplestTrivialTactic,
		ConclConjTactic,
		ConclIffTactic,
		HypDisjTactic,
		HypIffTactic,
		HypImplyTactic,
	)
}

// quantifierTactic / ConclExistsWitnessTactic / HypForallInstantiateTactic
// have moved to quantifier.go.

/**
 * rewriteTactic creates a tactic that simplifies goals by applying term rewriting to
 * hypotheses and conclusions. This higher-order function takes a rewrite function and
 * returns a tactic that applies that rewriting strategy to transform the goal.
 *
 * The tactic works by:
 * 1. Attempting to rewrite the conclusion using the provided rewrite function
 *    - If successful, creates a subgoal with the rewritten conclusion
 *    - The reconstruction function applies the equation MP rule to restore the original conclusion
 *
 * 2. If conclusion rewriting fails, attempts to rewrite each hypothesis
 *    - If successful, creates a subgoal with the rewritten hypothesis
 *    - The reconstruction function applies the appropriate derivation to maintain proof validity
 *
 * This function is particularly useful for applying different rewriting strategies by
 * simply providing different rewrite functions. Common rewriting strategies include:
 * - Basic logical simplifications (e.g., A ∧ A → A, A ∨ ¬A → ⊤)
 * - Beta reduction for lambda expressions
 * - Definitional expansions or simplifications
 * - Specialized domain-specific rewriting rules
 *
 * Parameters:
 *   - rewrite: A function that rewrites terms, returning an equality wrapper or nil
 *
 * Returns:
 *   - A Tactic function that applies the rewriting strategy to goals
 */
func rewriteTactic(rewrite prop.Rewrite) Tactic {
	return func(goal Prop) *SubGoals {
		if w := rewrite(goal.Conclusion()); w != nil {
			goal0 := MakeProp(Rhs(w), goal.Hyps()...)
			reconstruct := func(thms ...Prop) Prop {
				if thms[0].Conclusion().Equals(F) {
					return thms[0]
				}
				return w.EqSym().EqMP(thms[0])
			}
			return MakeTrackedSubGoals(goal, reconstruct, [][]int{keptSuccessors(goal, goal0)}, goal0)
		}
		for i := range goal.NumHyps() {
			if w := rewrite(goal.Hyp(i)); w != nil {
				w = w.LeftAssume()
				images := hypImages(goal, i, w.Conclusion())
				goal0 := makeImageProp(goal.Conclusion(), images)
				reconstruct := func(thms ...Prop) Prop {
					return w.MaybeDeriveTrans(thms[0])
				}
				return MakeTrackedSubGoals(goal, reconstruct, [][]int{hypSuccessorsOf(goal0, images)}, goal0)
			}
		}
		return nil
	}
}

/**
 * ByCaseTactic creates a tactic that performs case analysis on a specified boolean term.
 * This tactic splits the proof into two branches: one where the term is true, and one
 * where the term is false, allowing for proof by cases.
 *
 * The function works as follows:
 * 1. Takes a boolean term as input and validates it is of boolean type
 * 2. Handles negated terms appropriately, ensuring proper case splitting
 * 3. Returns a tactic function that performs the actual case analysis when applied to a goal
 * 4. The returned tactic creates two subgoals, on the term under one
 *    leading ¬ (ByCaseSides) — p for the case term ¬p:
 *    - child 0: the original goal with p added as a hypothesis
 *    - child 1: the original goal with ¬p added as a hypothesis
 * 5. Provides a reconstruction function that combines the proofs using the law of excluded middle
 *
 * The tactic avoids redundant case analysis by checking if:
 * - The case term or its negation is already the goal conclusion
 * - The case term or its negation is already present in the hypotheses
 *
 * Case analysis is a fundamental proof technique that allows breaking complex proofs
 * into simpler cases that can be handled separately. This tactic provides an automated
 * way to apply this technique within the goal-directed proof framework.
 *
 * Parameters:
 *   - caseTerm: The boolean term to split cases on
 *
 * Returns:
 *   - A Tactic function that performs case analysis when applied to a goal
 */
func ByCaseTactic(caseTerm Term) Tactic {
	Assert(IsBool(caseTerm))
	tactic := func(goal Prop) *SubGoals {
		kind, pos, neg := AnalyzeByCase(goal, caseTerm)
		if kind != ByCaseApplies {
			return nil
		}
		goal0 := MakeProp(goal.Conclusion(), append(goal.Hyps(), pos)...)
		goal1 := MakeProp(goal.Conclusion(), append(goal.Hyps(), neg)...)
		reconstruct := func(thms ...Prop) Prop {
			if !thms[0].HasHyp(pos) {
				return thms[0]
			}
			if !thms[1].HasHyp(neg) {
				return thms[1]
			}
			concl := goal.Conclusion()
			if thms[0].Conclusion().Equals(F) && thms[1].Conclusion().Equals(F) {
				concl = F
			}
			return ByCases(concl, pos, neg).
				DeriveHypFrom(prop.ExcludedMiddle(pos)).
				DeriveHypFrom(weakenConcl(thms[0], concl).PromoteHyp(pos)).
				DeriveHypFrom(weakenConcl(thms[1], concl).PromoteHyp(neg))
		}
		return MakeTrackedSubGoals(goal, reconstruct,
			[][]int{keptSuccessors(goal, goal0), keptSuccessors(goal, goal1)}, goal0, goal1)
	}
	return tactic
}

// ByCaseNoOpKind classifies why ByCaseTactic refuses to split a given
// goal on a given term — or reports that it will split (ByCaseApplies).
type ByCaseNoOpKind int

const (
	// ByCaseApplies: the split introduces new information; ByCaseTactic will
	// produce a non-trivial 2-child split.
	ByCaseApplies ByCaseNoOpKind = iota
	// ByCaseConclIsPositive: goal's conclusion α-equals the positive form φ
	// (so branch 0 becomes Γ,φ ⊢ φ which closes trivially, and branch 1
	// becomes Γ,¬φ ⊢ φ, reproducing the original goal shape).
	ByCaseConclIsPositive
	// ByCaseConclIsNegative: goal's conclusion α-equals ¬φ; symmetric no-op.
	ByCaseConclIsNegative
	// ByCaseHypIsPositive: φ is already a hypothesis — the true-branch just
	// restates it.
	ByCaseHypIsPositive
	// ByCaseHypIsNegative: ¬φ is already a hypothesis — the false-branch just
	// restates it.
	ByCaseHypIsNegative
)

// ByCaseSides is the pair of hypotheses a case split on caseTerm adds,
// one per child: pos the term under one leading ¬ — caseTerm itself
// where it has none — and neg its negation. A ¬-headed case term is
// therefore neg, and the child that receives it is child 1. ByCaseTactic
// and AnalyzeByCase read the pair here, and so does every surface that
// names a branch (proof.ByCaseBranch); no other site normalizes a case
// term.
func ByCaseSides(caseTerm Term) (pos, neg Term) {
	if inner := MatchesNOT(caseTerm); inner != nil {
		return inner, caseTerm
	}
	return caseTerm, Not(caseTerm)
}

// AnalyzeByCase is the SINGLE SOURCE OF TRUTH for ByCaseTactic's
// idempotence guards. It reads the split's two hypotheses (ByCaseSides)
// and reports whether — and if so which — of the four no-op conditions
// fires on `goal`. Returns the pos/neg pair so callers reuse the same
// terms the tactic itself consumes (goal0 hyp, reconstruct's
// PromoteHyp, ExcludedMiddle, etc.).
//
// ByCaseTactic itself calls this to decide whether to return nil;
// external diagnostics (engine's per-tactic error message for
// `case_split`) call the same function so agent-facing "why it failed"
// and kernel-facing "why we refused" can never disagree. If you add a
// fifth guard, add it here — both sites pick it up automatically.
func AnalyzeByCase(goal Prop, caseTerm Term) (kind ByCaseNoOpKind, pos, neg Term) {
	pos, neg = ByCaseSides(caseTerm)
	switch {
	case goal.Conclusion().AlphaEquals(pos):
		return ByCaseConclIsPositive, pos, neg
	case goal.Conclusion().AlphaEquals(neg):
		return ByCaseConclIsNegative, pos, neg
	case goal.HasHyp(pos):
		return ByCaseHypIsPositive, pos, neg
	case goal.HasHyp(neg):
		return ByCaseHypIsNegative, pos, neg
	}
	return ByCaseApplies, pos, neg
}

// AssertTactic creates a tactic that introduces claim as a sub-claim.
//
// The claim must be a hyp-free Prop with a boolean conclusion (any Prop
// produced by MakeProp is already boolean-concluded; the hyp-free
// requirement is the load-bearing precondition). The conclusion term of
// claim becomes both the goal of child(0) and the new hypothesis added
// to child(1).
//
// Returns nil when applying the tactic would be a no-op or
// self-referential:
//   - the claim's conclusion is already a hyp of goal (no point asserting
//     what is already in context)
//   - the claim's conclusion is α-equal to the goal's conclusion
//     (assert reduces to "prove what we wanted to prove")
//
// Semantics: given current goal Γ ⊢ G and a hyp-free boolean claim φ,
// produce
//
//	child(0) = Γ ⊢ φ
//	child(1) = Γ, φ ⊢ G
//
// Reconstruction discharges φ in child(1)'s hyps using child(0):
//
//	thm0 : Γ ⊢ φ
//	thm1 : Γ, φ ⊢ G
//	-----------------
//	thm  : Γ ⊢ G
//
// If thm1 turns out not to use φ as a hyp (e.g. the residual was closed
// without it), thm1 is returned directly — mirroring ByCaseTactic's
// "unused branch" handling.
//
// Distinct from ByCaseTactic: assert does NOT add ¬φ on a second branch.
// It is the Coq `assert φ` / Lean `have h : φ := …` shape — a single
// directional sub-claim that the residual goal may then use as a hyp.
// Free variables in the claim that are not in scope at goal are not
// rejected at this level — the kernel allows them as new free vars in
// the resulting subgoals. The engine RPC layer performs the scope check
// before calling this tactic and surfaces a typed diagnostic.
func AssertTactic(claim Prop) Tactic {
	Assert(claim != nil)
	Assert(claim.NumHyps() == 0)
	claimTerm := claim.Conclusion()
	Assert(IsBool(claimTerm))
	return func(goal Prop) *SubGoals {
		if goal.Conclusion().AlphaEquals(claimTerm) {
			return nil
		}
		if goal.HasHyp(claimTerm) {
			return nil
		}
		claimGoal := MakeProp(claimTerm, goal.Hyps()...)
		residualGoal := MakeProp(goal.Conclusion(), append(goal.Hyps(), claimTerm)...)
		reconstruct := func(thms ...Prop) Prop {
			// If the residual didn't actually use φ as a hyp, return it
			// directly — the short-circuit keeps the kernel chain shorter
			// and avoids a needless DeriveTrans for the unused-claim case.
			if !thms[1].HasHyp(claimTerm) {
				return thms[1]
			}
			// thms[0] proves Γ ⊢ φ — or, in the F-branch test path,
			// Γ' ⊆ Γ ⊢ ⊥. weakenConcl matches the conclusion to claimTerm
			// (via FalseDerives) when thms[0] arrived as ⊥, so DeriveTrans's
			// "t0.Conclusion is a hyp of t1" precondition holds in both
			// branches.
			return weakenConcl(thms[0], claimTerm).DeriveTrans(thms[1])
		}
		return MakeTrackedSubGoals(goal, reconstruct,
			[][]int{keptSuccessors(goal, claimGoal), keptSuccessors(goal, residualGoal)}, claimGoal, residualGoal)
	}
}

// ClearHypsTactic drops the SET of hyps at hypIndices in one step,
// producing the single subgoal `Γ\{dropped} ⊢ G`. All indices refer to
// the same input goal's hyp list (the set is removed atomically — no
// sequential index shifting). Sound by weakening: the child carries a
// subset of the parent's hyps with the same conclusion, so
// reconstruction is the identity.
//
// Motivation: a wide multi-quantifier ∀-lemma resident in the hyp
// context drives the CNF refuter inside `auto`/`refute` to its ceiling
// on irrelevant resolutions, even when the actual refutation is trivial
// and ground; dropping it before the refute collapses that cost.
// Returns nil (no-op) when the index list is empty, contains a
// duplicate, or any index is out of range — callers surface a clean
// "did not apply".
func ClearHypsTactic(hypIndices []int) Tactic {
	return func(goal Prop) *SubGoals {
		if len(hypIndices) == 0 {
			return nil
		}
		drop := make(map[int]bool, len(hypIndices))
		for _, idx := range hypIndices {
			if idx < 0 || idx >= goal.NumHyps() || drop[idx] {
				return nil
			}
			drop[idx] = true
		}
		hyps := make([]Term, 0, goal.NumHyps()-len(drop))
		images := goal.Hyps()
		for j := range goal.NumHyps() {
			if drop[j] {
				images[j] = nil
			} else {
				hyps = append(hyps, goal.Hyp(j))
			}
		}
		child := MakeProp(goal.Conclusion(), hyps...)
		return MakeTrackedSubGoals(goal, trivialReconstruct, [][]int{hypSuccessorsOf(child, images)}, child)
	}
}

// ExistentialConstDefTactic reads a const `c` whose definition is a
// choice, `⊢ c = εx.P(x)` (the shape a recursive definition and a
// specification produce), by its two obligations. Returns nil for a
// const whose definition is not such a choice.
//
// Semantics: given current goal Γ ⊢ G,
//
//	child(0) = Γ ⊢ ∃x.P(x)         (existence claim)
//	child(1) = Γ, P(c) ⊢ G          (residual with P(c) as a free hyp)
//
// The agent / search reasons over child(1) by splitting/using P(c) as
// a lemma — e.g. for `+`, P(c) is the conjunctive recursive body
// `∀m n. (0+m = m) ∧ (suc(m)+n = suc(m+n))`, which can be split into
// oriented rewriters.
//
// Reconstruction uses prop.ExistentialConstDef(c) = `∃x.P(x) ⊢ P(c)`
// as the bridge axiom: discharge its ∃ hyp with thm0, then cut
// the resulting P(c) into thm1. If thm1 didn't use P(c), short-circuit
// to thm1 directly (mirrors AssertTactic's unused-claim optimization).
//
// Distinct from the rewrite of c to its ε-term (the def-expand
// composite): c stays folded, and P(c) is a hypothesis of the residual
// instead of an ε-term in the goal — the reading an author wants where
// the goal is not P(c) itself.
func ExistentialConstDefTactic(c ConstTerm) Tactic {
	Assert(!c.IsZero())
	return func(goal Prop) *SubGoals {
		return ExistentialConstDefTacticFromBridge(prop.ExistentialConstDef(c))(goal)
	}
}

// ExistentialConstDefTacticFromBridge is ExistentialConstDefTactic with
// the bridge thm `∃x.P(x) ⊢ P(c)` supplied directly instead of rebuilt
// from c via prop.ExistentialConstDef — _ExistentialConstDefStep.apply
// builds the bridge itself and hands it here. Returns a nil-result
// tactic when pcThm is nil.
func ExistentialConstDefTacticFromBridge(pcThm Thm) Tactic {
	return func(goal Prop) *SubGoals {
		if pcThm.IsZero() {
			return nil
		}
		// pcThm : ∃x.P(x) ⊢ P(c)
		Assert(pcThm.NumHyps() == 1)
		existsTerm := pcThm.Hyps()[0]
		pcTerm := pcThm.Conclusion()
		// No-op gates: nothing to do if either output is already in scope.
		if goal.HasHyp(pcTerm) {
			return nil
		}
		if goal.Conclusion().AlphaEquals(existsTerm) {
			return nil
		}
		existsGoal := MakeProp(existsTerm, goal.Hyps()...)
		residualGoal := MakeProp(goal.Conclusion(), append(goal.Hyps(), pcTerm)...)
		reconstruct := func(thms ...Prop) Prop {
			// Short-circuit when the residual didn't actually use P(c) —
			// no need to drag the existence proof through reconstruction.
			if !thms[1].HasHyp(pcTerm) {
				return thms[1]
			}
			// thms[0] : Γ ⊢ ∃x.P(x)         — or Γ' ⊆ Γ ⊢ ⊥ in the
			//                                  test-grid F-branch. weakenConcl
			//                                  lifts ⊥ to existsTerm so
			//                                  pcThm.DeriveHypFrom's
			//                                  "t1.Concl is a hyp of t0"
			//                                  precondition holds.
			// pcThm   : ∃x.P(x) ⊢ P(c)
			// pcThm.DeriveHypFrom(thms[0]) : Γ ⊢ P(c)
			// thms[1] : Γ, P(c) ⊢ G
			// thms[1].DeriveHypFrom(...)   : Γ ⊢ G
			weakened := weakenConcl(thms[0], existsTerm)
			pcDerived := WrapProp(pcThm).DeriveHypFrom(weakened)
			return WrapProp(thms[1]).DeriveHypFrom(pcDerived)
		}
		return MakeSubGoals(goal, reconstruct, existsGoal, residualGoal)
	}
}
