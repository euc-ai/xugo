package tactic

import (
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// Regression test for the engine panic applying a ∀-closed-with-hyps
// lemma whose free predicate vars are not generalized.
//
// Mirrors the sequent shape of binary induction:
//
//	lemma:  P(z), ∀n.(P(n) ⇒ P(f(n)) ∧ P(g(n)))  ⊢  ∀n.P(n)     (P a FREE var)
//	goal:   (∀m.Q(f(m))) ∧ (∀m.Q(g(m)))          ⊢  ∀m.Q(m)     (Q rigid)
//
// The old code stripped the lemma concl's ∀-prefix and unified the body
// `P(n)` against the whole goal concl `∀m.Q(m)`; Huet imitation returned
// `P ↦ λx.∀m.Q(m)` (the free predicate absorbed the goal's entire
// ∀-conclusion, the stripped binder `n` got no binding), so after
// TermInst+DeepBeta the instantiated conclusion was `∀n.∀m.Q(m)` — not
// α-equal to the goal's `∀m.Q(m)` — and makeSubGoalsAt's IsStronger Assert
// panicked ("Should not happen.").
//
// The fix validates the instantiation against the goal conclusion and, on
// mismatch, retries with a WHOLE-conclusion unification (∀-prefix kept),
// which pattern-unifies under the shared binder and yields the intended
// `P ↦ Q`. If that also fails, the tactic returns nil (soft failure).
func TestLemmaConclMatch_FreePredicateWholeConclRetry(t *testing.T) {
	n := Var("n", TypeA)
	m := Var("m", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool)) // free predicate VARIABLE (flexible)
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))
	f := ext.TestConst("f", MakeFun(TypeA, TypeA))
	g := ext.TestConst("g", MakeFun(TypeA, TypeA))
	z := ext.TestConst("z", TypeA)

	lemma := MakeProp(
		ForAll(n)(P.Apply(n)), // concl ∀n.P(n)
		P.Apply(z),            // hyp base
		ForAll(n)(P.Apply(n).Imply(P.Apply(f.Apply(n)).And(P.Apply(g.Apply(n))))), // hyp step
	)
	goal := MakeProp(
		ForAll(m)(Q.Apply(m)), // concl ∀m.Q(m)
		ForAll(m)(Q.Apply(f.Apply(m))).And(ForAll(m)(Q.Apply(g.Apply(m)))), // hyp
	)

	subGoals := lemmaConclMatchTactic(lemma)(goal) // must NOT panic
	require.NotNil(t, subGoals)
	require.Equal(t, 2, subGoals.Size())

	// Child 0 is the lemma itself (dep tracking).
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), lemma)

	// Child 1's conclusion is the conjunction of the two instantiated
	// lemma hyps: Q(z) ∧ ∀n.(Q(n) ⇒ Q(f(n)) ∧ Q(g(n))) — i.e. P ↦ Q, the
	// whole-conclusion pattern unification, NOT the absorbing imitation.
	wantConcl := Q.Apply(z).And(
		ForAll(n)(Q.Apply(n).Imply(Q.Apply(f.Apply(n)).And(Q.Apply(g.Apply(n))))))
	assert.True(t, subGoals.ChildGoal(1).Conclusion().AlphaEquals(wantConcl.Core()),
		"child 1 conclusion = %s, want %s",
		ext.PrintTerm(subGoals.ChildGoal(1).Conclusion()), ext.PrintTerm(wantConcl.Core()))
	// Child 1 carries the goal's hyps through unchanged.
	for h := range goal.HypIter() {
		assert.True(t, subGoals.ChildGoal(1).HasHyp(h))
	}

	// Reconstruction soundness (real proofs, ⊥-collapse, hyp-drop fuzz).
	assertSubGoals(t, subGoals, goal)
}

// Graceful-nil path: when even the whole-conclusion unification cannot
// match (rigid head mismatch: lemma concl is ∀-headed, goal concl is
// ∃-headed), the tactic must return nil — "lemma did not apply" — rather
// than panic on the spurious first-attempt imitation solution.
func TestLemmaConclMatch_FreePredicateNoMatchReturnsNil(t *testing.T) {
	n := Var("n", TypeA)
	m := Var("m", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))
	f := ext.TestConst("f", MakeFun(TypeA, TypeA))
	g := ext.TestConst("g", MakeFun(TypeA, TypeA))
	z := ext.TestConst("z", TypeA)

	lemma := MakeProp(
		ForAll(n)(P.Apply(n)),
		P.Apply(z),
		ForAll(n)(P.Apply(n).Imply(P.Apply(f.Apply(n)).And(P.Apply(g.Apply(n))))),
	)
	goal := MakeProp(
		Exists(m)(Q.Apply(m)), // ∃-headed: whole-concl unify can't match ∀n.P(n)
		ForAll(m)(Q.Apply(f.Apply(m))).And(ForAll(m)(Q.Apply(g.Apply(m)))),
	)

	subGoals := lemmaConclMatchTactic(lemma)(goal) // must NOT panic
	assert.Nil(t, subGoals)
}
