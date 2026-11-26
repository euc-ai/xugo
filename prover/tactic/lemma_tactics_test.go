package tactic

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

func TestEqLemmaTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)

	P := ext.TestConst("P", MakeFun(TypeA, TypeBool))
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeA, TypeBool))

	s := testProp(ForAll(y)(Q.Apply(x, y)))
	subGoals := eqLemmaTactic(s)(s)
	assert.Nil(t, subGoals)

	s = testProp(Unique(y)(Q.Apply(x, y)))
	goal := testProp(Exists(y)(Not(Q.Apply(x, y).Eq(P.Apply(y)))), Unique(y)(Q.Apply(x, y)))
	subGoals = eqLemmaTactic(s)(goal)
	assert.Nil(t, subGoals)

	s = testProp(Unique(y)(Q.Apply(x, y)), ForAll(y)(Q.Apply(x, y)), ForAll(y)(P.Apply(y)))
	goal = testProp(Exists(y)(Not(Q.Apply(x, y).Eq(P.Apply(y)))), ForAll(y)(Q.Apply(x, y)))
	subGoals = eqLemmaTactic(s)(goal)
	assert.Nil(t, subGoals)

	s = testProp(Exists(y)(Q.Apply(y, y)))
	goal = testProp(F, Unique(y)(P.Apply(y)), Exists(y)(Q.Apply(y, y)).Imply(Unique(y)(P.Apply(y))))
	subGoals = eqLemmaTactic(s)(goal)
	assert.Nil(t, subGoals)

	s = testProp(ForAll(y)(Q.Apply(x, y).Eq(P.Apply(y))))
	goal = testProp(ForAll(y)(Q.Apply(x, y).Eq(P.Apply(y))), Unique(y)(Q.Apply(x, y)))
	subGoals = eqLemmaTactic(s)(goal)
	assertSubGoals(t, subGoals, goal)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), s)

	s = testProp(ForAll(y)(Q.Apply(x, y).Eq(P.Apply(y))))
	goal = testProp(Exists(y)(Not(Q.Apply(x, y).Eq(P.Apply(y)))), Unique(y)(Q.Apply(x, y)))
	subGoals = eqLemmaTactic(s)(goal)
	assertSubGoals(t, subGoals, goal)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), s)
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		testProp(F, Unique(y)(P.Apply(y)), T))

	s = testProp(Q.Apply(x, x).Imply(P.Apply(x)))
	goal = testProp(Unique(y)(Q.Apply(x, y)),
		Q.Apply(x, x).Imply(P.Apply(x)).Imply(P.Apply(x)),
		Not(Q.Apply(x, x)).Or(P.Apply(x)).Imply(P.Apply(x)))
	subGoals = eqLemmaTactic(s)(goal)
	assertSubGoals(t, subGoals, goal)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), s)
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		testProp(
			Unique(y)(Q.Apply(x, y)),
			Not(Q.Apply(x, x)).Or(P.Apply(x)).Imply(P.Apply(x)),
			P.Apply(x)))

	s = testProp(ForAll(y)(Q.Apply(x, y).Eq(P.Apply(y))))
	goal = testProp(Unique(y)(Q.Apply(x, y)), Q.Apply(x, x))
	subGoals = eqLemmaTactic(s)(goal)
	assertSubGoals(t, subGoals, goal)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), s)
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		testProp(F, Not(Unique(y)(P.Apply(y))), P.Apply(x)))

	s = testProp(ForAll(y)(Q.Apply(x, y).Eq(P.Apply(y))))
	goal = testProp(Exists(y)(Not(Q.Apply(x, y))), Q.Apply(x, x))
	subGoals = eqLemmaTactic(s)(goal)
	assertSubGoals(t, subGoals, goal)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), s)
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		testProp(F, ForAll(y)(P.Apply(y)), P.Apply(x)))

	s = testProp(ForAll(y)(Q.Apply(x, y).Eq(P.Apply(y))))
	goal = testProp(ForAll(x)(Not(Q.Apply(x, x))), Exists(y)(Not(Q.Apply(x, y))))
	subGoals = eqLemmaTactic(s)(goal)
	assertSubGoals(t, subGoals, goal)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), s)
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		testProp(ForAll(x)(Not(Q.Apply(x, x))), Exists(x)(Not(P.Apply(x)))))
}

func TestEqLemmaTacticPreCNFFallbackHits(t *testing.T) {
	defer goleak.VerifyNone(t)

	p := Var("p", TypeBool)
	q := Var("q", TypeBool)
	done := Var("done", TypeBool)

	// The equality witness is written against ¬p ∨ q, while the goal hyp uses
	// the equivalent p ⇒ q. eqSimplify is the matcher used by eqLemmaTactic;
	// it should hit through ContextEqRewrite's pre-CNF fallback.
	eq := WrapTerm(Rhs(prop.PreCNFNormalizeTerm(p.Imply(q)))).Eq(done)
	goal := testProp(F, p.Imply(q), Not(done), eq)
	subGoals := eqSimplify(fullSearch, new(prop.PreCNFCache), goal, eq, true, false)
	assertSubGoals(t, subGoals, goal)
	assert.Equal(t, 1, subGoals.Size())
	lemmaSubGoals := eqLemmaTactic(testProp(eq))(testProp(done, p.Imply(q)))
	assertSubGoals(t, lemmaSubGoals, testProp(done, p.Imply(q)))

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))

	// Same logical content, different quantifier scope:
	//   ∀x. P(x) ⇒ ∀y. R(x,y)
	// versus
	//   ∀x y. P(x) ⇒ R(x,y)
	// The fallback should normalize the target hyp before applying the lemma
	// witness.
	scopedLemma := ForAll(x)(P.Apply(x).Imply(ForAll(y)(R.Apply(x, y))))
	flatTarget := ForAll(x, y)(P.Apply(x).Imply(R.Apply(x, y)))
	eq = WrapTerm(Rhs(prop.PreCNFNormalizeTerm(scopedLemma))).Eq(done)
	goal = testProp(F, flatTarget, Not(done), eq)
	subGoals = eqSimplify(fullSearch, new(prop.PreCNFCache), goal, eq, true, false)
	assertSubGoals(t, subGoals, goal)
	assert.Equal(t, 1, subGoals.Size())
	lemmaSubGoals = eqLemmaTactic(testProp(eq))(testProp(done, flatTarget))
	assertSubGoals(t, lemmaSubGoals, testProp(done, flatTarget))
}

// TestEqLemmaTacticExpand_DriversLeanRw verifies that
// eqLemmaTacticExpand (the entry point LeanRwTactic builds on)
// successfully rewrites an expansion-style equational lemma —
// specifically the case the agent reported (an iff lemma whose r2l
// direction expands a small constant-shaped LHS into a larger RHS in
// the goal).
//
// Default eqLemmaTactic returns nil for the same input because its
// internal eqSimplify call passes allowExpand=false; the bypass is the
// load-bearing change.
func TestEqLemmaTacticExpand_DriversLeanRw(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	done := Var("done", TypeBool)

	// Lemma: ⊢ done = (a ∧ b). Conclusion is an equality whose RHS is
	// strictly bigger than the LHS — the size-guard-rejected case.
	lemma := testProp(done.Eq(a.And(b)))
	// Goal: ⊢ done. LeanRw should rewrite `done` to `a ∧ b`, leaving
	// the residual ⊢ a ∧ b.
	goal := testProp(done.Core())

	// Size-guarded path returns nil — the eq-rewrite path can't fire,
	// and eqLemmaTactic has no fallback inside (the hypMatch / conclMatch
	// fallbacks live one layer up in lemmaTacticCore).
	guarded := eqLemmaTactic(lemma)(goal)
	assert.Nil(t, guarded,
		"eqLemmaTactic (size-guarded) must return nil on the expansion case")

	// Expansion-allowed path produces subgoals: child(0) = lemma,
	// child(1) = residual whose conclusion is the rewritten goal. The
	// rewrite happens inside the negConcl form (¬done ⊢ ⊥ → ¬(a∧b) ⊢ ⊥
	// → ¬a ∨ ¬b ⊢ ⊥ after BasicRewrite), so the residual after
	// goalReconstruct may surface in either polarity. The invariant we
	// pin: the residual's conclusion is NOT α-equal to the original
	// `done` — that is, the rewrite actually transformed the goal.
	expanded := eqLemmaTacticExpand(lemma)(goal)
	require.NotNil(t, expanded,
		"eqLemmaTacticExpand must succeed on the expansion case")
	assertSubGoals(t, expanded, goal)
	assert.GreaterOrEqual(t, expanded.Size(), 1)
	assertPropAlphaEqual(t, expanded.ChildGoal(0), lemma)
	if expanded.Size() == 2 {
		residual := expanded.ChildGoal(1)
		assert.False(t,
			residual.AlphaEquals(goal),
			"residual must differ from original goal (rewrite must have fired); got %s",
			prop.PrintProp(residual))
	}
}

func TestEqLemmaTacticPreCNFHypBridgeKeepsRawGoalHyps(t *testing.T) {
	defer goleak.VerifyNone(t)

	p := Var("p", TypeBool)
	q := Var("q", TypeBool)
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)

	lemmaHyp := p.Imply(q)
	goalHyp := Not(p).Or(q)
	big := a.And(b)
	lemma := testProp(big.Eq(b), lemmaHyp)
	goal := testProp(b, goalHyp, big)

	subGoals := eqLemmaTactic(lemma)(goal)
	assertSubGoals(t, subGoals, goal)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), lemma)

	thms := make([]Prop, subGoals.Size())
	for i, g := range subGoals.childrenGoals {
		thms[i] = testThm(g.Conclusion(), g.Hyps()...)
	}
	reconstructed := subGoals.Reconstruct(thms...)
	assert.True(t, reconstructed.AllHyp(goal.HasHyp),
		"bridge-only lemma hyp must be rewritten back to a raw goal hyp")
	assert.False(t, reconstructed.HasHyp(lemmaHyp),
		"reconstructed proof must not leak the normalized-only lemma hyp")
}

func TestLemmaInstTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := ext.TestConst("P", MakeFun(TypeA, TypeBool))
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))
	R := ext.TestConst("R", MakeFun(TypeA, TypeA, TypeBool))

	var lemma, goal Prop
	var expectedGoal0, expectedGoal1 *PropWrapper
	var tactic Tactic
	var subGoals *SubGoals

	// Test Case 1: Simple application with one hypothesis
	lemma = testProp(Q.Apply(x), P.Apply(x)) // P(x) ⊢ Q(x)
	goal = testProp(F, R.Apply(x, y))        // R(x, y) ⊢ F
	tactic = lemmaInstTactic(lemma, nil)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 3, subGoals.Size())
	assertSubGoals(t, subGoals, goal)

	// Expected subgoal 1: main goal with lemma conclusion as new hypothesis
	expectedGoal0 = testProp(F, R.Apply(x, y), Q.Apply(x))
	assertPropAlphaEqual(t, expectedGoal0, subGoals.ChildGoal(1))

	// Expected subgoal 2: prove lemma hypothesis
	expectedGoal1 = testProp(P.Apply(x), R.Apply(x, y))
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(2))

	// Test Case 2: Lemma with no hypotheses

	lemma = testProp(P.Apply(x)) // ⊢ P(x)
	goal = testProp(R.Apply(x, y), Q.Apply(x))
	tactic = lemmaInstTactic(lemma, nil)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)

	// Expected subgoal: main goal with lemma conclusion as new hypothesis
	expectedGoal0 = testProp(R.Apply(x, y), Q.Apply(x), P.Apply(x))
	assertPropAlphaEqual(t, expectedGoal0, subGoals.ChildGoal(1))

	// Test Case 3: Lemma with multiple hypotheses

	lemma = testProp(R.Apply(x, y), P.Apply(x), Q.Apply(y)) // P(x), Q(y) ⊢ R(x, y)
	goal = testProp(F, z.Eq(z))
	tactic = lemmaInstTactic(lemma, nil)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 4, subGoals.Size())
	assertSubGoals(t, subGoals, goal)

	// Expected subgoal 1: main goal with new hypothesis
	expectedGoal0 = testProp(F, z.Eq(z), R.Apply(x, y))
	assertPropAlphaEqual(t, expectedGoal0, subGoals.ChildGoal(1))

	// Expected subgoals for lemma's hypotheses
	expectedGoal1 = testProp(P.Apply(x), z.Eq(z))
	expectedGoal2 := testProp(Q.Apply(y), z.Eq(z))
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(2))
	assertPropAlphaEqual(t, expectedGoal2, subGoals.ChildGoal(3))

	// Test Case 4: Application with free variable substitution
	lemma = testProp(Q.Apply(x), P.Apply(x)) // P(x) ⊢ Q(x)
	goal = testProp(F, R.Apply(y, y))
	substs := []core.TermSubst{ext.MakeTermSubst(x, y)}
	tactic = lemmaInstTactic(lemma, substs)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 3, subGoals.Size())
	assertSubGoals(t, subGoals, goal)

	// Expected subgoal 1: main goal with instantiated lemma conclusion
	expectedGoal0 = testProp(F, R.Apply(y, y), Q.Apply(y))
	assertPropAlphaEqual(t, expectedGoal0, subGoals.ChildGoal(1))

	// Expected subgoal 2: prove instantiated lemma hypothesis
	expectedGoal1 = testProp(P.Apply(y), R.Apply(y, y))
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(2))

	// Test Case 5: Application with universally quantified variable substitution

	lemma = testProp(ForAll(x)(Q.Apply(x)), P.Apply(y)) // P(y) ⊢ ∀x. Q(x)
	goal = testProp(F, R.Apply(z, z))
	substs = []core.TermSubst{ext.MakeTermSubst(x, z)}
	tactic = lemmaInstTactic(lemma, substs)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 3, subGoals.Size())
	assertSubGoals(t, subGoals, goal)

	// Instantiated lemma conclusion is Q(z)
	expectedGoal0 = testProp(F, R.Apply(z, z), Q.Apply(z))
	assertPropAlphaEqual(t, expectedGoal0, subGoals.ChildGoal(1))

	// Lemma hypothesis remains P(y)
	expectedGoal1 = testProp(P.Apply(y), R.Apply(z, z))
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(2))

}

func TestLemmaConclMatchTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := ext.TestConst("P", MakeFun(TypeA, TypeBool))
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))
	R := ext.TestConst("R", MakeFun(TypeA, TypeA, TypeBool))

	var lemma, goal Prop
	var tactic Tactic
	var subGoals *SubGoals

	// Test Case 1: Simple successful match with one hypothesis
	lemma = testProp(Q.Apply(x), P.Apply(x))   // P(x) ⊢ Q(x)
	goal = testProp(Q.Apply(y), R.Apply(z, z)) // R(z, z) ⊢ Q(y)
	tactic = lemmaConclMatchTactic(lemma)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	// Expected subgoal: prove instantiated lemma hypothesis P(y)
	expectedGoal1 := testProp(P.Apply(y), R.Apply(z, z))
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(1))

	// Test Case 2: Match with a universally quantified conclusion
	lemma = testProp(ForAll(y)(R.Apply(x, y)), P.Apply(x)) // P(x) ⊢ ∀y. R(x, y)
	goal = testProp(R.Apply(z, z), Q.Apply(z))             // Q(z) ⊢ R(z, z)
	tactic = lemmaConclMatchTactic(lemma)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	// Expected subgoal: prove instantiated lemma hypothesis P(z)
	expectedGoal1 = testProp(P.Apply(z), Q.Apply(z))
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(1))

	// Test Case 3: Match with a universally quantified conclusion
	lemma = testProp(ForAll(y)(R.Apply(x, y)), P.Apply(x)) // P(x) ⊢ ∀y. R(x, y)
	goal = testProp(R.Apply(y, y), Q.Apply(y))             // Q(y) ⊢ R(y, y)
	tactic = lemmaConclMatchTactic(lemma)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	// Expected subgoal: prove instantiated lemma hypothesis P(y)
	expectedGoal1 = testProp(P.Apply(y), Q.Apply(y))
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(1))

	// Test Case 4: Lemma with no hypotheses
	lemma = testProp(ForAll(x)(P.Apply(x))) // ⊢ ∀x. P(x)
	goal = testProp(P.Apply(y), Q.Apply(z)) // Q(z) ⊢ P(y)
	tactic = lemmaConclMatchTactic(lemma)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))

	// Test Case 5: No match, unification fails
	lemma = testProp(P.Apply(x))
	goal = testProp(Q.Apply(y))
	tactic = lemmaConclMatchTactic(lemma)
	subGoals = tactic(goal)
	assert.Nil(t, subGoals)

	// Test Case 6: Match fails because goal conclusion is more general
	lemma = testProp(P.Apply(y))
	goal = testProp(ForAll(x)(P.Apply(x)))
	tactic = lemmaConclMatchTactic(lemma)
	subGoals = tactic(goal)
	assert.Nil(t, subGoals)

	// Test Case 7: Name collision (in this case y is free in the lemma's hyps)
	lemma = testProp(ForAll(y)(R.Apply(x, y)), P.Apply(y)) // P(y) ⊢ ∀y. R(x, y)
	goal = testProp(R.Apply(z, z), Q.Apply(z))             // Q(z) ⊢ R(z, z)
	tactic = lemmaConclMatchTactic(lemma)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	// Expected subgoal: prove instantiated lemma hypothesis P(y)
	expectedGoal1 = testProp(P.Apply(y), Q.Apply(z))
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(1))
}

// TestLemmaConclMatchTactic_PromiseBackedReconstructsToThm is the regression
// for the `AsThm: not a theorem (proven-or-provable)` panic that
// `trans + auto` reaches in a session proof of a mod-equality law.
//
// A lemma can reach the tactic as a BARE statement, so
// `instantiate(lemma)` hits deriveProp's unprovable-dep escape and the
// instantiated lemma is a bare proposition. When the lemma's own subgoal is
// then discharged by an UNFORCED promise (the ◐ auto-match case), the
// reconstruct must STILL yield a genuine Thm. The old code gated the
// re-derivation on `thms[0].Proved()` — true for a realized cert, FALSE for an
// unforced promise — and so returned the bare instantiatedLemma. That bare Prop
// became the node's provedThm; a later sibling close walked Commit's
// updateUpwards, which called core.AsThm on it and panicked, poisoning the
// session. The fix re-derives whenever instantiatedLemma is not itself a
// realized cert, threading the promise through instead.
func TestLemmaConclMatchTactic_PromiseBackedReconstructsToThm(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := ext.TestConst("P", MakeFun(TypeA, TypeBool))

	// Bare lemma statement ⊢ ∀x. P(x) (unproven) plus a goal
	// it closes by instantiation. The single subgoal is the lemma itself — the
	// no-hyp branch whose reconstruct carried the bug.
	lemma := testProp(ForAll(x)(P.Apply(x)))
	goal := testProp(P.Apply(y))
	subGoals := lemmaConclMatchTactic(lemma)(goal)
	require.NotNil(t, subGoals)
	require.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))

	// Discharge the lemma subgoal with an UNFORCED promise (root builder; the
	// readiness check does not run it, so Proved() stays false).
	built := 0
	promise := core.Promise(lemma, func(core.Forcer) core.ThmCert {
		built++
		return core.TestThm(lemma.Conclusion())
	})
	require.False(t, promise.Proved(), "raw promise is unforced")

	var result Prop
	require.NotPanics(t, func() { result = subGoals.Reconstruct(promise) },
		"reconstruct from a promise-backed lemma close must not panic")
	if _, isThm := result.Core().(core.Thm); !isThm {
		t.Fatalf("reconstruct must return a Thm (realized cert or promise), got bare %T", result.Core())
	}
	require.NotPanics(t, func() { _ = core.AsThm(result) },
		"core.AsThm must accept the reconstruct result — this is the exact call that panicked in Commit")
	assert.True(t, core.IsPromised(result), "result threads the unforced lemma promise")
	assert.True(t, result.Conclusion().AlphaEquals(goal.Conclusion()), "result proves the goal P(y)")
	assert.Equal(t, 0, built, "builder must not run until the promise is forced")

	// Forcing realizes the whole graph and proves the goal exactly once.
	thm := core.Force(context.Background(), core.AsThm(result))
	assert.True(t, thm.Conclusion().AlphaEquals(goal.Conclusion()), "forced result proves P(y)")
	assert.Equal(t, 1, built, "builder runs exactly once on force")
}

func TestLemmaConclMatchTactic_HOFBetaReduction(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	u := Var("u", TypeA)
	v := Var("v", TypeA)
	// Stand-in for the original nil constant — any rigid constant of type A works.
	c := ext.TestConst("c", TypeA)

	// Lemma: ⊢ ∀P. ∃x. ∃y. P(x, y)
	// Stripping the outer ∀P leaves ∃x.∃y.P(x, y), which the unifier matches
	// against the goal by setting P ↦ λa.λb.(b = c).
	lemma := testProp(ForAll(P)(Exists(x)(Exists(y)(P.Apply(x, y)))))
	goal := testProp(Exists(u)(Exists(v)(v.Eq(c))))

	// instantiateLemma collapses the (λa.λb.(b = c))(x, y) β-redex in the
	// conclusion — left in place it trips the IsStronger(instantiatedLemma,
	// goal) assert — and the lemma applies cleanly with a single child
	// subgoal (the lemma itself — no hyps to discharge).
	subGoals := lemmaConclMatchTactic(lemma)(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
}

func TestLemmaHypMatchTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := ext.TestConst("P", MakeFun(TypeA, TypeBool))
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))
	R := ext.TestConst("R", MakeFun(TypeA, TypeBool))
	S := ext.TestConst("S", MakeFun(TypeA, TypeBool))

	var lemma, goal Prop
	var tactic Tactic
	var subGoals *SubGoals
	var expectedGoal1 Prop

	// Test Case 1: Simple match, one hypothesis
	// Lemma: P(x) ⊢ Q(x)
	// Goal: P(x) ⊢ R(x)
	// New hypothesis: Q(x)
	lemma = testProp(Q.Apply(x), P.Apply(x))
	goal = testProp(R.Apply(x), P.Apply(x))
	tactic = lemmaHypMatchTactic(lemma)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	expectedGoal1 = testProp(R.Apply(x), P.Apply(x), Q.Apply(x))
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(1))

	// Test Case 2: Partial match of hypotheses
	// Lemma: P(x), Q(y) ⊢ R(x)
	// Goal: P(x), S(y) ⊢ F
	// New hypothesis: Q(y) => R(x)
	lemma = testProp(R.Apply(x), P.Apply(x), Q.Apply(y))
	goal = testProp(F, P.Apply(x), S.Apply(y))
	tactic = lemmaHypMatchTactic(lemma)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	newHyp := ForAll(y)(Q.Apply(y).Imply(R.Apply(x)))
	expectedGoal1 = testProp(F, P.Apply(x), S.Apply(y), newHyp)
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(1))

	// Test Case 3: No matching hypotheses
	// Tactic should fail
	lemma = testProp(Q.Apply(x), P.Apply(x))
	goal = testProp(R.Apply(x), S.Apply(y))
	tactic = lemmaHypMatchTactic(lemma)
	subGoals = tactic(goal)
	assert.Nil(t, subGoals)

	// Test Case 4: Full match, lemma proves contradiction
	// Tactic should produce one subgoal: the lemma itself
	lemma = testProp(F, P.Apply(x), Q.Apply(y))
	goal = testProp(R.Apply(z), P.Apply(x), Q.Apply(y), S.Apply(z))
	tactic = lemmaHypMatchTactic(lemma)
	subGoals = tactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))

	// Test Case 5: Trivial application, new hypothesis already in goal
	// Tactic should fail
	lemma = testProp(Q.Apply(x), P.Apply(x))
	goal = testProp(R.Apply(y), P.Apply(x), Q.Apply(x))
	tactic = lemmaHypMatchTactic(lemma)
	subGoals = tactic(goal)
	assert.Nil(t, subGoals)

	// Test Case 6: Lemma with no hypotheses
	// New hypothesis is the conclusion of the lemma
	lemma = testProp(P.Apply(x))
	goal = testProp(R.Apply(y), Q.Apply(z))
	tactic = lemmaHypMatchTactic(lemma)
	subGoals = tactic(goal)

	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	newHyp = ForAll(x)(P.Apply(x))
	expectedGoal1 = testProp(R.Apply(y), Q.Apply(z), newHyp)
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(1))

	// Test Case 7: Lemma proves contradiction with new hypothesis
	// Tactic should produce one subgoal: the lemma itself
	lemma = testProp(F, P.Apply(x), S.Apply(z))
	goal = testProp(R.Apply(z), P.Apply(x), Q.Apply(y))
	tactic = lemmaHypMatchTactic(lemma)
	subGoals = tactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	newHyp = ForAll(z)(Not(S.Apply(z)))
	expectedGoal1 = testProp(R.Apply(z), P.Apply(x), Q.Apply(y), newHyp)
	assertPropAlphaEqual(t, expectedGoal1, subGoals.ChildGoal(1))
}

// TestLemmaTacticDenormalize covers the two-pass behavior of LemmaTactic:
// when core matching fails on the as-is goal but succeeds after denormalizing
// the conclusion, we return the chained result; when core still fails after
// denormalization, we return nil (bare denormalization is not a valid lemma
// application — the lemma must actually appear as a child).
func TestLemmaTacticDenormalize(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := ext.TestConst("P", MakeFun(TypeA, TypeBool))
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))
	R := ext.TestConst("R", MakeFun(TypeA, TypeBool))

	// Case A: goal is in "normalized" form (⊢ P ⇒ Q), lemma concludes Q(x)
	// with different free var. Direct core fails (can't unify `Q(x)` against
	// `P(x) ⇒ Q(y)`), but after peeling the ⇒ into a hyp, lemmaConclMatchTactic
	// can unify Q(x) against Q(y) with subst {x → y}. Verifies the chain fires.
	lemma := testProp(Q.Apply(x), P.Apply(x)) // P(x) ⊢ Q(x)
	goal := testProp(P.Apply(x).Imply(Q.Apply(y)))
	subGoals := LemmaTactic(lemma)(goal)
	assert.NotNil(t, subGoals, "denormalize should expose Q(y) for unify against lemma's Q(x)")
	assertSubGoals(t, subGoals, goal)
	// LemmaTactic invariant: child[0] is the lemma itself.
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))

	// Case B: denormalization runs but core still fails — lemma's hyp S(·)
	// doesn't overlap with the goal's peeled hyp P(·), so lemmaHypMatchTactic
	// bails; lemma's concl R(·) can't unify with Q(·), so lemmaConclMatchTactic
	// bails. LemmaTactic must return nil (NOT a bare denormalization subgoal,
	// which would corrupt Search's candidate-use tracking since no lemma
	// appears as a child).
	S := ext.TestConst("S", MakeFun(TypeA, TypeBool))
	lemma = testProp(R.Apply(x), S.Apply(x)) // S(x) ⊢ R(x)
	goal = testProp(P.Apply(x).Imply(Q.Apply(y)))
	subGoals = LemmaTactic(lemma)(goal)
	assert.Nil(t, subGoals,
		"denormalize-only progress without core firing must not be reported as a lemma application")

	// Case C: goal already has hyps exposed so core fires directly — verify
	// we preserve the original behavior (no denormalization when unnecessary).
	// Goal: P(x) ⊢ Q(y). Lemma: P(x) ⊢ Q(x). lemmaConclMatchTactic unifies on
	// concl Q(x) vs Q(y).
	lemma = testProp(Q.Apply(x), P.Apply(x))
	goal = testProp(Q.Apply(y), P.Apply(x))
	subGoals = LemmaTactic(lemma)(goal)
	assert.NotNil(t, subGoals)
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))

	// Case D: goal has outer ∀ on concl — exactly the asymmetry in
	// lemmaConclMatchTactic (strips lemma's ∀ but not goal's). Direct core
	// fails: conclMatch can't unify lemma's body Q(x) against `∀y. Q(y)`
	// (constructor mismatch), hypMatch bails because lemma has a hyp P(·)
	// that doesn't appear in the hyp-less goal. After denormalize strips the
	// goal's ∀, goal becomes `⊢ Q(y)` with y free, and conclMatch unifies
	// Q(x) against Q(y). This is the motivating case for the tactic.
	lemma = testProp(Q.Apply(x), P.Apply(x))
	goal = testProp(ForAll(y)(Q.Apply(y)))
	subGoals = LemmaTactic(lemma)(goal)
	assert.NotNil(t, subGoals,
		"denormalize should strip goal's outer ∀ so conclMatch can unify Q(x) vs Q(y)")
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
}

// TestLemmaTacticLemmaDenormalize covers the lemma-side (symmetric)
// denormalization: when the INPUT lemma's conclusion has outer ∀/⇒
// (i.e. the lemma arrived in Normalize'd form), LemmaTactic internally
// runs matching against the denormalized lemma too, and picks the
// tighter of the two results. Child[0] is still the ORIGINAL lemma —
// the inner reconstruct bridges via forwardDenorm + provedLemmaExactly.
func TestLemmaTacticLemmaDenormalize(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := ext.TestConst("P", MakeFun(TypeA, TypeBool))
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))
	S := ext.TestConst("S", MakeFun(TypeA, TypeBool))

	var lemma, goal Prop
	var subGoals *SubGoals

	// Case A: normalized lemma `⊢ P(x) ⇒ Q(x)` against max-hyp goal
	// `P(y), S(y) ⊢ Q(y)`. Core on the ORIGINAL lemma can't conclMatch
	// (body P(x)⇒Q(x) vs Q(y) — constructor mismatch) so it falls through
	// to a hypMatch WEAKENING — subgoal residual gets `∀x.(P(x)⇒Q(x))` as a
	// hyp, which Search would then have to instantiate+MP to discharge.
	//
	// With lemma-side denormalization, coreAlt's denormLemma is `P(x) ⊢ Q(x)`.
	// conclMatch unifies Q(x) vs Q(y) giving subst {x → y}, instantiates to
	// `P(y) ⊢ Q(y)`, and produces a residual `P(y), S(y) ⊢ P(y)` which is
	// trivially closeable by simplifyNewGoal's hyp-matches-concl check.
	// Result: 1-subgoal vs coreOrig's 2-subgoal — prefer coreAlt.
	//
	// Child[0] must still be the normalized `⊢ P(x) ⇒ Q(x)` so Search
	// records the right dep.
	lemma = testProp(P.Apply(x).Imply(Q.Apply(x)))
	goal = testProp(Q.Apply(y), P.Apply(y), S.Apply(y))
	subGoals = LemmaTactic(lemma)(goal)
	assert.NotNil(t, subGoals, "coreAlt with denormLemma should fire via conclMatch")
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	assert.Equal(t, 1, subGoals.Size(),
		"lemma-denormalize path should collapse to a single subgoal (the lemma)")

	// Case B: normalized lemma `⊢ ∀x. P(x) ⇒ Q(x)` — outer ∀ + inner ⇒.
	// Goal: `P(y), S(y) ⊢ Q(y)`. Same improvement pattern as A.
	//
	// denormLemma strips ∀ then peels ⇒: `P(x) ⊢ Q(x)` (x free).
	// conclMatch unifies Q(x) vs Q(y); instantiated lemma `P(y) ⊢ Q(y)`;
	// residual `P(y), S(y) ⊢ P(y)` trivially closes. Single subgoal out.
	lemma = testProp(ForAll(x)(P.Apply(x).Imply(Q.Apply(x))))
	goal = testProp(Q.Apply(y), P.Apply(y), S.Apply(y))
	subGoals = LemmaTactic(lemma)(goal)
	assert.NotNil(t, subGoals)
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
	assert.Equal(t, 1, subGoals.Size())

	// Case C: α-equal guard. When goal α-equals lemma, LemmaTactic must
	// return nil — the caller should use a known-thm (AlphaKey) lookup
	// instead, not a circular lemma application. Without this guard the
	// goal-denormalize path would produce subgoals whose lemma child
	// α-equals the original goal, tripping MakeSubGoals' assertion that
	// forbids a child goal α-equal to its parent.
	lemma = testProp(P.Apply(x).Imply(Q.Apply(x)))
	goal = testProp(P.Apply(x).Imply(Q.Apply(x))) // α-equal to lemma
	subGoals = LemmaTactic(lemma)(goal)
	assert.Nil(t, subGoals, "α-equal goal/lemma must short-circuit to nil")

	// Case D: α-equal guard under ∀-bound-var renaming. The same corner
	// via ∀x vs ∀y — α-equivalence covers bound-variable renaming.
	lemma = testProp(ForAll(x)(P.Apply(x).Imply(Q.Apply(x))))
	goal = testProp(ForAll(y)(P.Apply(y).Imply(Q.Apply(y)))) // α-equal
	subGoals = LemmaTactic(lemma)(goal)
	assert.Nil(t, subGoals, "α-equal under bound-var rename must short-circuit to nil")

	// Case E: lemma with nothing to denormalize — coreAlt is nil, try
	// degenerates to coreOrig alone. Verify we don't crash and behavior
	// matches the pre-lemma-denormalize path.
	lemma = testProp(Q.Apply(x), P.Apply(x)) // P(x) ⊢ Q(x) — already max-hyp
	goal = testProp(Q.Apply(y), P.Apply(y))
	subGoals = LemmaTactic(lemma)(goal)
	assert.NotNil(t, subGoals)
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, lemma, subGoals.ChildGoal(0))
}

func TestSplitConjunctiveClauses(t *testing.T) {
	t.Run("TwoClauses", func(t *testing.T) {
		// TestSplitConjunctiveClauses_TwoClauses verifies the basic split of a
		// ∀-quantified two-way conjunction, with the ∀ distributed onto each
		// clause.
		a := Var("a", TypeA)
		f := Var("f", MakeFun(TypeA, TypeA))
		g := Var("g", MakeFun(TypeA, TypeA))
		h := Var("h", MakeFun(TypeA, TypeA))

		// ⊢ ∀a. (f(a) = g(a)) ∧ (g(a) = h(a))   (trusted)
		eq1 := f.Apply(a).Eq(g.Apply(a))
		eq2 := g.Apply(a).Eq(h.Apply(a))
		thm := testThm(ForAll(a)(eq1.And(eq2)))

		clauses := splitConjunctiveClauses(thm)
		require.Len(t, clauses, 2)
		assertPropAlphaEqual(t, clauses[0], testThm(ForAll(a)(f.Apply(a).Eq(g.Apply(a)))))
		assertPropAlphaEqual(t, clauses[1], testThm(ForAll(a)(g.Apply(a).Eq(h.Apply(a)))))
	})

	// TestSplitConjunctiveClauses_ThreeClausesNested verifies flattening of
	// a nested conjunction (right-associated `a ∧ (b ∧ c)`) into three
	// separate clauses.
	t.Run("ThreeClausesNested", func(t *testing.T) {
		a := Var("a", TypeA)
		f := Var("f", MakeFun(TypeA, TypeA))
		g := Var("g", MakeFun(TypeA, TypeA))
		h := Var("h", MakeFun(TypeA, TypeA))
		k := Var("k", MakeFun(TypeA, TypeA))

		c1 := f.Apply(a).Eq(g.Apply(a))
		c2 := g.Apply(a).Eq(h.Apply(a))
		c3 := h.Apply(a).Eq(k.Apply(a))
		// ⊢ ∀a. c1 ∧ (c2 ∧ c3)   (And folds right by default)
		thm := testThm(ForAll(a)(c1.And(c2.And(c3))))

		clauses := splitConjunctiveClauses(thm)
		require.Len(t, clauses, 3)
		assertPropAlphaEqual(t, clauses[0], testThm(ForAll(a)(f.Apply(a).Eq(g.Apply(a)))))
		assertPropAlphaEqual(t, clauses[1], testThm(ForAll(a)(g.Apply(a).Eq(h.Apply(a)))))
		assertPropAlphaEqual(t, clauses[2], testThm(ForAll(a)(h.Apply(a).Eq(k.Apply(a)))))
	})

	// TestSplitConjunctiveClauses_NonConjunction verifies that a thm whose
	// body isn't a conjunction passes through unchanged (single-element
	// slice).
	t.Run("NonConjunction", func(t *testing.T) {
		a := Var("a", TypeA)
		f := Var("f", MakeFun(TypeA, TypeA))
		g := Var("g", MakeFun(TypeA, TypeA))

		thm := testThm(ForAll(a)(f.Apply(a).Eq(g.Apply(a))))
		clauses := splitConjunctiveClauses(thm)
		require.Len(t, clauses, 1)
		assertPropAlphaEqual(t, clauses[0], thm)
	})

	// TestSplitConjunctiveClauses_VacuousBinder verifies the recursive-def
	// shape: one clause uses all the ∀-vars, the other uses a subset (the
	// nil clause). After distribution the unused binders become vacuous ∀
	// over that clause — still a valid thm.
	t.Run("VacuousBinder", func(t *testing.T) {
		// Mirror ALL's shape: ∀t P h. (cons-clause uses t,P,h) ∧ (nil-clause uses P)
		tv := Var("t", TypeA)
		P := Var("P", MakeFun(TypeA, TypeBool))
		h := Var("h", TypeA)

		// cons-clause uses P,h,t; nil-clause uses only P,h (subset).
		consClause := P.Apply(h).Eq(P.Apply(tv))
		nilClause := P.Apply(h).Eq(P.Apply(h))

		thm := testThm(ForAll(tv)(ForAll(P)(ForAll(h)(consClause.And(nilClause)))))
		clauses := splitConjunctiveClauses(thm)
		require.Len(t, clauses, 2)
		// Both clauses keep the full ∀-prefix (vacuous binders allowed) and
		// each is a single (non-conjunctive) ∀-statement — i.e. re-splitting
		// is idempotent.
		for i, c := range clauses {
			assert.Len(t, splitConjunctiveClauses(c), 1,
				"clause %d should be a single ∀-statement, not further splittable", i)
		}
	})
}

// directConclusionRewriteTactic is the def_expand / lean_rw fallback that
// rewrites a const occurrence sitting under `⇔` or `¬` (positions the
// refutation-shaped eqLemmaTactic path rejects). Its reconstruct chains
// `bridge.EqSym().EqMP(thms[1])` (plus an optional `DeriveHypFrom(thms[0])`
// when the bridge carries the lemma conclusion as a hyp). This test fuzzes
// that reconstruct via assertSubGoals — the 100-iteration adversarial pass
// that feeds each child arbitrary / weaker theorems and requires the
// reconstructed parent to stay kernel-Proved. Guards against the reconstruct
// silently depending on more than the children it is handed.
func TestDirectConclusionRewriteTactic_ReconstructSound(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := ext.TestConst("P", MakeFun(TypeA, TypeBool))
	S := ext.TestConst("S", MakeFun(TypeA, TypeBool))
	R := ext.TestConst("R", MakeFun(TypeA, TypeBool))
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))

	// Hyp-free rewrite lemma `P(x) ⇔ S(x)`.
	lemma := testProp(P.Apply(x).Eq(S.Apply(x)))

	cases := []struct {
		name string
		goal Prop
	}{
		// P(x) under ¬, with a spurious hyp so the hyp-removal fuzz bites.
		{"under_not", testProp(Not(P.Apply(x)), Q.Apply(x))},
		// P(x) under ⇔ (boolean equality at the top connective).
		{"under_iff", testProp(P.Apply(x).Eq(R.Apply(x)), Q.Apply(x))},
	}

	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			sg := directConclusionRewriteTactic(lemma)(tc.goal)
			require.NotNil(t, sg, "directConclusionRewriteTactic should fire on %s", tc.name)
			require.Equal(t, 2, sg.Size(), "expected [lemma, rewritten-goal]")
			// child(0) is the lemma reproduction obligation.
			assertPropAlphaEqual(t, sg.ChildGoal(0), lemma)
			// Soundness: adversarial reconstruct fuzz.
			assertSubGoals(t, sg, tc.goal)
		})
	}
}

// TestLemmaTactic_DropsInstantiatedHyp_RootCausePin pins the root cause
// of `lemma` re-normalizing the hyp context and dropping previously-built
// ground instantiations:
// LemmaTactic's hypMatch result passes through simplifyNewGoal, whose
// unifyEqSimplifyTactic pass lets the resident ∀-equation hyp rewrite
// its own ground instance to ⊤ (then dropped by the trivial cleanup).
// The agent-visible symptom: after a manual `instantiate`, loading ANY
// unrelated lemma reverts the ground-specialized hyp to its ∀-form.
//
// This test documents the OLD tactic's behavior (kept for replay of
// recorded proofs — do NOT "fix" LemmaTactic itself); the
// companion test below asserts LemmaPreserveTactic keeps the hyp.
func TestLemmaTactic_DropsInstantiatedHyp_RootCausePin(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	c := Var("c", TypeA) // the agent's ground witness
	f := ext.TestConst("f", MakeFun(TypeA, TypeA))
	g := ext.TestConst("g", MakeFun(TypeA, TypeA))
	R := ext.TestConst("R", MakeFun(TypeA, TypeBool))
	C := ext.TestConst("C", TypeBool)

	forallEq := ForAll(x)(f.Apply(x).Eq(g.Apply(x))) // ∀x. f(x) = g(x)
	ground := f.Apply(c).Eq(g.Apply(c))              // f(c) = g(c)  (manual instantiate)
	unrelated := testProp(ForAll(x)(R.Apply(x)))     // the lemma being loaded

	goal := testProp(C.Core(), forallEq.Core(), ground.Core())

	subGoals := LemmaTactic(unrelated)(goal)
	require.NotNil(t, subGoals)
	require.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), unrelated)

	residual := subGoals.ChildGoal(1)
	// The ∀-form and the loaded lemma survive…
	assert.True(t, residual.HasHyp(forallEq.Core()))
	assert.True(t, residual.AnyHyp(unrelated.Conclusion().AlphaEquals))
	// …but the ground instance is absorbed (THE defect being pinned).
	// If this assertion ever flips, LemmaTactic's replay behavior
	// changed — that would break recorded proofs; investigate.
	assert.False(t, residual.HasHyp(ground.Core()),
		"LemmaTactic no longer absorbs the ground instance — replay-affecting change!")
}

// TestLemmaPreserveTactic_KeepsInstantiatedHyp is the fix-side
// counterpart of the root-cause pin above: loading an unrelated lemma
// via LemmaPreserveTactic must keep BOTH the ∀-form and its ground
// instance, adding only the new hypothesis.
func TestLemmaPreserveTactic_KeepsInstantiatedHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	c := Var("c", TypeA)
	f := ext.TestConst("f", MakeFun(TypeA, TypeA))
	g := ext.TestConst("g", MakeFun(TypeA, TypeA))
	R := ext.TestConst("R", MakeFun(TypeA, TypeBool))
	C := ext.TestConst("C", TypeBool)

	forallEq := ForAll(x)(f.Apply(x).Eq(g.Apply(x)))
	ground := f.Apply(c).Eq(g.Apply(c))
	unrelated := testProp(ForAll(x)(R.Apply(x)))

	goal := testProp(C.Core(), forallEq.Core(), ground.Core())

	subGoals := LemmaPreserveTactic(unrelated)(goal)
	require.NotNil(t, subGoals)
	require.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), unrelated)

	residual := subGoals.ChildGoal(1)
	// Every pre-existing hyp survives — including the ground instance.
	assert.True(t, residual.HasHyp(forallEq.Core()))
	assert.True(t, residual.HasHyp(ground.Core()),
		"ground instantiation must survive the lemma load")
	// The lemma landed as a new hyp.
	assert.True(t, residual.AnyHyp(unrelated.Conclusion().AlphaEquals))
	// Conclusion untouched.
	assert.True(t, residual.Conclusion().AlphaEquals(goal.Conclusion()))
	// Reconstruct soundness (adversarial fuzz).
	assertSubGoals(t, subGoals, goal)
}

// TestLemmaPreserveTactic_KeepsBenignOutcomes asserts the preserve
// variant does NOT degrade LemmaTactic's hyp-safe strategies: a lemma
// that directly closes the goal still closes it, and a conclusion-side
// equational rewrite (hyps untouched) is still applied rather than
// downgraded to a hyp load.
func TestLemmaPreserveTactic_KeepsBenignOutcomes(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := ext.TestConst("P", MakeFun(TypeA, TypeBool))
	f := ext.TestConst("f", MakeFun(TypeA, TypeA))
	e := ext.TestConst("e", TypeA)
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))

	// Direct close: goal IS an instance of the lemma.
	lemma := testProp(ForAll(x)(P.Apply(x)))
	goal := testProp(P.Apply(Var("a", TypeA)).Core())
	subGoals := LemmaPreserveTactic(lemma)(goal)
	require.NotNil(t, subGoals)
	require.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), lemma)
	assertSubGoals(t, subGoals, goal)

	// Conclusion eq-rewrite: ∀x. f(x) = e rewrites Q(f(a)) → Q(e) — a
	// strictly size-decreasing rewrite, so LemmaTactic's size-monotone
	// eq path fires. Hyps (one spurious resident) are untouched, so the
	// preserve gate accepts the rewrite as-is instead of downgrading it
	// to a hyp load.
	a := Var("a", TypeA)
	spurious := Q.Apply(Var("s", TypeA))
	eqLemma := testProp(ForAll(x)(f.Apply(x).Eq(e.Core())))
	goal = testProp(Q.Apply(f.Apply(a)).Core(), spurious.Core())
	old := LemmaTactic(eqLemma)(goal)
	require.NotNil(t, old)
	subGoals = LemmaPreserveTactic(eqLemma)(goal)
	require.NotNil(t, subGoals)
	require.Equal(t, old.Size(), subGoals.Size(),
		"preserve variant must not change the hyp-safe rewrite outcome")
	require.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), eqLemma)
	residual := subGoals.ChildGoal(1)
	assert.True(t, residual.Conclusion().AlphaEquals(Q.Apply(e.Core()).Core()),
		"conclusion rewrite should still fire (it preserves hyps)")
	assert.True(t, residual.HasHyp(spurious.Core()))
	assertSubGoals(t, subGoals, goal)
}

// LemmaPreserveTacticUntil tells a chain its deadline ended from a lemma
// that does not apply, and under a context that never ends it is
// LemmaPreserveTactic.
func TestLemmaPreserveTacticUntilReportsTheAbandon(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	a := Var("a", TypeA)
	f := ext.TestConst("f", MakeFun(TypeA, TypeA))
	e := ext.TestConst("e", TypeA)
	Q := ext.TestConst("Q", MakeFun(TypeA, TypeBool))

	// ∀x. f(x) = e rewrites the conclusion Q(f(a)) to Q(e).
	lemma := testProp(ForAll(x)(f.Apply(x).Eq(e.Core())))
	goal := testProp(Q.Apply(f.Apply(a)).Core(), Q.Apply(Var("s", TypeA)).Core())
	unbounded := LemmaPreserveTactic(lemma)(goal)
	require.NotNil(t, unbounded)
	require.Equal(t, 2, unbounded.Size())

	sg, abandoned := LemmaPreserveTacticUntil(context.Background(), lemma, goal)
	require.False(t, abandoned)
	require.NotNil(t, sg)
	require.Equal(t, unbounded.Size(), sg.Size())
	for i := range sg.Size() {
		assertPropAlphaEqual(t, sg.ChildGoal(i), unbounded.ChildGoal(i))
	}
	assertSubGoals(t, sg, goal)

	done, cancel := context.WithCancel(context.Background())
	cancel()
	sg, abandoned = LemmaPreserveTacticUntil(done, lemma, goal)
	assert.True(t, abandoned, "past the deadline the chain is abandoned, and says so")
	assert.Nil(t, sg)
}
