package tactic

import (
	"context"
	"fmt"
	"math/rand"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

var (
	testProp = MakeProp
	testThm  = core.TestThm
)

func assertPropAlphaEqual(t *testing.T, p0, p1 Prop) {
	assert.True(t, p0.AlphaEquals(p1))
}

func assertSubGoals(t *testing.T, subGoals *SubGoals, goal Prop) {
	Assert(subGoals.goal.AlphaEquals(goal))
	thms := make([]Prop, subGoals.Size())
	for i, g := range subGoals.childrenGoals {
		thms[i] = testThm(g.Conclusion(), g.Hyps()...)
	}
	assert.True(t, subGoals.Reconstruct(thms...).AsThmCert().Proved())
	for i, g := range subGoals.childrenGoals {
		if g.NumHyps() > 0 {
			thms[i] = testThm(F, g.Hyps()...)
		}
	}
	assert.True(t, subGoals.Reconstruct(thms...).AsThmCert().Proved())
	for range 100 {
		for i, g := range subGoals.childrenGoals {
			if g.NumHyps() == 0 {
				thms[i] = testThm(g.Conclusion())
			} else {
				// randomly remove one.
				hyps := g.Hyps()
				hyps[rand.Intn(g.NumHyps())] = hyps[g.NumHyps()-1]
				if subGoals.Size() > 1 && i == rand.Intn(subGoals.Size()+1) {
					thms[i] = testThm(F, hyps[:g.NumHyps()-1]...)
				} else {
					thms[i] = testThm(g.Conclusion(), hyps[:g.NumHyps()-1]...)
				}
			}
		}
		assert.True(t, subGoals.Reconstruct(thms...).AsThmCert().Proved())
	}
}

// TestConclConjAllTactic exercises the n-ary flatten + shape-mirroring
// reconstruct of ConclConjAllTactic across associations and arities.
// assertSubGoals validates the reconstruct three ways: from real proofs,
// from ⊥-conclusion proofs (the short-circuit branch), and a 100-round
// fuzz that randomly drops hyps / injects ⊥ — so the right-association
// rebuildConj path is checked, not just the count.
func TestConclConjAllTactic(t *testing.T) {
	defer goleak.VerifyNone(t)
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	w := Var("w", TypeA)
	q := Var("q", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))
	a := P.Apply(x)
	b := P.Apply(y)
	c := P.Apply(z)
	d := P.Apply(w)

	// Non-conjunction conclusion → inapplicable (nil), even with hyps.
	require.Nil(t, ConclConjAllTactic(testProp(a)))
	require.Nil(t, ConclConjAllTactic(testProp(a, b, c)))

	// Binary A∧B → 2 flat children (degenerates to ConclConjTactic).
	bin := testProp(a.And(b))
	sg := ConclConjAllTactic(bin)
	require.NotNil(t, sg)
	assert.Equal(t, 2, sg.Size())
	assertSubGoals(t, sg, bin)

	// Right-nested A∧(B∧C) with a hyp → 3 flat children; the hyp makes
	// assertSubGoals exercise the ⊥-conclusion reconstruct branch.
	rn := testProp(a.And(b.And(c)), q)
	sg = ConclConjAllTactic(rn)
	require.NotNil(t, sg)
	assert.Equal(t, 3, sg.Size())
	assertSubGoals(t, sg, rn)

	// Left-nested (A∧B)∧C → 3 flat children (any association flattens).
	ln := testProp(a.And(b).And(c))
	sg = ConclConjAllTactic(ln)
	require.NotNil(t, sg)
	assert.Equal(t, 3, sg.Size())
	assertSubGoals(t, sg, ln)

	// Wide right-nested A∧B∧C∧D with a hyp → 4 flat children.
	wide := testProp(a.And(b.And(c.And(d))), q)
	sg = ConclConjAllTactic(wide)
	require.NotNil(t, sg)
	assert.Equal(t, 4, sg.Size())
	assertSubGoals(t, sg, wide)

	// Degenerate A∧A∧A → MakeSubGoals dedups to 1 compact child, but
	// reconstruct still rebuilds the full 3-leaf conjunction.
	dgn := testProp(a.And(a.And(a)))
	sg = ConclConjAllTactic(dgn)
	require.NotNil(t, sg)
	assert.Equal(t, 1, sg.Size())
	assertSubGoals(t, sg, dgn)
}

func TestBasicTactics(t *testing.T) {
	defer goleak.VerifyNone(t)

	var prop Prop
	var subGoals *SubGoals

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	q := Var("q", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeA))

	prop = testProp(P.Apply(x), P.Apply(z))
	subGoals = BasicTactics(prop)
	assert.Nil(t, subGoals)

	prop = testProp(P.Apply(y), Not(P.Apply(y)), P.Apply(x))
	subGoals = trivialTactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(y), P.Apply(x)))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Not(P.Apply(y)), P.Apply(y), P.Apply(x))
	subGoals = trivialTactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(Not(P.Apply(y)), P.Apply(x)))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x), P.Apply(y), Not(P.Apply(y)))
	subGoals = trivialTactic(prop)
	assert.Equal(t, subGoals.Size(), 0)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(F, Not(R.Apply(x.Eq(y)).Eq(z)), Not(P.Apply(x)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(R.Apply(x.Eq(y)).Eq(z), Not(P.Apply(x))))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Not(P.Apply(x)), Not(R.Apply(x.Eq(y)).Eq(z)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(R.Apply(x.Eq(y)).Eq(z), P.Apply(x)))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x), P.Apply(y).Or(Not(P.Apply(y))), P.Apply(z))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(y), x.Eq(y))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(y), x.Eq(R.Apply(P.Apply(y))))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(y), R.Apply(P.Apply(y)).Eq(x))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x).Or(Not(P.Apply(x))), P.Apply(y))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 0)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x), P.Apply(x).And(P.Apply(x)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 0)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(y), P.Apply(x).And(Not(P.Apply(x))))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 0)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(F, P.Apply(x).And(P.Apply(z)).And(P.Apply(y)).Or(P.Apply(z).And(P.Apply(x))))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(F, P.Apply(z).And(P.Apply(x)).Or(P.Apply(x).And(P.Apply(z)).And(P.Apply(y))))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x).Eq(P.Apply(x).And(P.Apply(x))))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 0)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(F, P.Apply(x).Eq(P.Apply(y).And(P.Apply(z))))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 3)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x), P.Apply(y), P.Apply(z), F)
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 0)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x), P.Apply(y), P.Apply(z), Not(P.Apply(y)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 0)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x), P.Apply(y), P.Apply(z), Not(P.Apply(x)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x).And(P.Apply(x)).Eq(P.Apply(y).And(P.Apply(z))))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 3)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x).And(P.Apply(y)), P.Apply(y).Or(P.Apply(z)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 3)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(q.And(P.Apply(z)), P.Apply(x).And(P.Apply(y)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 2)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x).Or(Not(P.Apply(y))), q.And(P.Apply(z)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(x), P.Apply(y), q, (P.Apply(z))))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Not(P.Apply(x)).Or(P.Apply(y)), q.And(P.Apply(z)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(y), P.Apply(x), q, (P.Apply(z))))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Not(P.Apply(x)).Or(Not(P.Apply(y))), q.And(P.Apply(z)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(F, P.Apply(x), P.Apply(y), q, (P.Apply(z))))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x).Or(P.Apply(R.Apply(q))))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(R.Apply(q)), Not(P.Apply(x))))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(R.Apply(q)).Or(P.Apply(x)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(R.Apply(q)), Not(P.Apply(x))))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(F, Not(P.Apply(y).Or(P.Apply(z))), Not(P.Apply(x)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(x), Not(P.Apply(y)), Not(P.Apply(z))))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Not(P.Apply(x)), Not(R.Apply(y.Eq(z)).Eq(x)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(R.Apply(y.Eq(z)).Eq(x), P.Apply(x)))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(R.Apply(q)), z.Eq(R.Apply(q)), Q.Apply(z))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(z), z.Eq(R.Apply(q)), Q.Apply(z)))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x).Imply(P.Apply(R.Apply(q))), Q.Apply(z))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(R.Apply(q)), P.Apply(x), Q.Apply(z)))
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x), P.Apply(y), z.Eq(R.Apply(q)).Imply(P.Apply(R.Apply(q))))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 2)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(ForAll(x)(P.Apply(x)), q.And(P.Apply(x)))
	subGoals = BasicTactics(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(ForAll(q)(q.And(P.Apply(x))), Exists(q)(P.Apply(R.Apply(q))))
	subGoals = BasicTactics(prop)
	assert.Nil(t, subGoals)

	prop = testProp(Exists(q)(q.And(P.Apply(x))), ForAll(q)(P.Apply(R.Apply(q))))
	subGoals = BasicTactics(prop)
	assert.Nil(t, subGoals)
}

// TestStructuralTactics_DegenerateInputs covers the agent-callable
// structural sub-tactics on idempotent inputs (A∧A, A∨A, A⇒A, A⇔A) and on
// the implication whose two cases are one (A⇒¬A).
//
// Two regimes after the basic_tactics.go change:
//
//   - Dedup (∧/∨ in concl or hyp): produces a single subgoal ⊢A (concl)
//     or A in hyp (hyp). The reconstruct path uses one DeriveHypFrom
//     because MakeProp dedups the duplicate hyp internally; calling
//     DeriveHypFrom twice would consume a hyp that's already gone.
//
//   - Trivial-collapse (⇒/⇔ in concl or hyp): returns nil. The result
//     is "trivially T" rather than "single subgoal" — that's auto/refute's
//     job, not a structural decomposition. Returning nil makes the
//     structural-moves enumerator correctly omit these from its options.
//
//   - One case (A⇒¬A in hyp): the hypothesis says ¬A, and both cases of
//     the split assume it. A single subgoal with ¬A in hyp; the
//     reconstruct discharges the one implication ByCases holds.
//
// No regime may panic. An Assert(!t0.AlphaEquals(t1)) there would
// assume the upstream BasicTactic chain ran trivial cleanup first, and
// direct-from-agent callers (apply RPC, structural enumerator) have no
// such upstream cleanup.
func TestStructuralTactics_DegenerateInputs(t *testing.T) {
	defer goleak.VerifyNone(t)

	var prop Prop
	var subGoals *SubGoals

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	A := P.Apply(x) // some atomic-ish bool prop
	B := P.Apply(y) // a different one (used as preserved hyp)

	// --- Dedup: ∧/∨ produce a single subgoal ----------------------------

	// conclConj: ⊢ A∧A → ⊢ A   (preserve unrelated hyp B)
	prop = testProp(A.And(A).Core(), B.Core())
	subGoals = ConclConjTactic(prop)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(A.Core(), B.Core()))
	assertSubGoals(t, subGoals, prop)

	// conclDisj: ⊢ A∨A → ⊢ A
	prop = testProp(A.Or(A).Core(), B.Core())
	subGoals = ConclDisjTactic(prop)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(A.Core(), B.Core()))
	assertSubGoals(t, subGoals, prop)

	// hypConj: A∧A ⊢ B → A ⊢ B
	prop = testProp(B.Core(), A.And(A).Core())
	subGoals = HypConjTactic(prop)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(B.Core(), A.Core()))
	assertSubGoals(t, subGoals, prop)

	// hypDisj: A∨A ⊢ B → A ⊢ B
	prop = testProp(B.Core(), A.Or(A).Core())
	subGoals = HypDisjTactic(prop)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(B.Core(), A.Core()))
	assertSubGoals(t, subGoals, prop)

	// --- Trivial-collapse: ⇒/⇔ return nil (not the structural tactic's job) -

	// conclImply: ⊢ A⇒A is trivially T → use auto/refute
	prop = testProp(A.Imply(A).Core(), B.Core())
	subGoals = ConclImplyTactic(prop)
	assert.Nil(t, subGoals)

	// conclIff: ⊢ A⇔A is trivially T → use auto/refute
	prop = testProp(A.Eq(A).Core(), B.Core())
	subGoals = ConclIffTactic(prop)
	assert.Nil(t, subGoals)

	// hypImply: A⇒A in hyp is a useless T-hyp → no structural decomposition
	prop = testProp(B.Core(), A.Imply(A).Core())
	subGoals = HypImplyTactic(prop)
	assert.Nil(t, subGoals)

	// hypIff: A⇔A in hyp is a useless T-hyp → no structural decomposition
	prop = testProp(B.Core(), A.Eq(A).Core())
	subGoals = HypIffTactic(prop)
	assert.Nil(t, subGoals)

	// --- One case: A⇒¬A in hyp is ¬A ------------------------------------

	// hypImply: A⇒¬A ⊢ B → ¬A ⊢ B
	notA := Not(A)
	prop = testProp(B.Core(), A.Imply(notA).Core())
	subGoals = HypImplyTactic(prop)
	require.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(B.Core(), notA.Core()))
	assertSubGoals(t, subGoals, prop)
}

// TestHypSplitTacticsAt_TargetSpecificHyp is the tactic-layer
// regression for `[feature-gap] split_disj ignores hyp_index —
// always picks first ∨-hyp`.
// Each `HypXTacticAt(goal, idx)` must split the hyp AT idx, not the
// first matching one — the mis-splits observed in the coordinator's
// iterated-product session (hyp 15 asked for, hyp 13 split)
// arose because the tactic ignored the index and re-scanned from 0.
//
// MakeProp sorts hyps by Term.Compare, so the test discovers which
// index each shape landed at instead of hard-coding positions — that
// keeps the check semantic ("At(k) splits the hyp AT position k"),
// not brittle against MakeProp's ordering.
func TestHypSplitTacticsAt_TargetSpecificHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	// A / B / C are distinct atoms usable as ∨ / ⇔ / ⇒ operands.
	A := P.Apply(x)
	B := Q.Apply(y)
	C := R.Apply(z)
	Cgoal := Var("g", TypeBool).Core()

	// findHyp returns the goal's 0-based index of a hyp α-equal to
	// target, or -1 if not present. Used to translate "the A∨B hyp"
	// into the sort-order index MakeProp gave it.
	findHyp := func(g Prop, target Term) int {
		for i := range g.NumHyps() {
			if g.Hyp(i).AlphaEquals(target) {
				return i
			}
		}
		return -1
	}

	// --- split_disj: two ∨-hyps + a non-∨ atom, ensure `At` targets
	// the requested one AND that the wrong index / wrong shape decline.
	{
		D := Var("D", TypeBool).Core()
		AorB := A.Or(B).Core()
		AorC := A.Or(C).Core()
		g := testProp(Cgoal, AorB, AorC, D)

		iAB := findHyp(g, AorB)
		iAC := findHyp(g, AorC)
		iD := findHyp(g, D)
		require.NotEqual(t, -1, iAB)
		require.NotEqual(t, -1, iAC)
		require.NotEqual(t, -1, iD)

		// Pick-first path — legacy semantics: splits the FIRST ∨-hyp
		// (min of iAB/iAC in the sort-order).
		sg := HypDisjTactic(g)
		require.NotNil(t, sg)
		require.Equal(t, 2, sg.Size())

		// At-index=iAB: splits A∨B. Distinguishes by looking for A
		// on one child and B on the other — the discriminator that
		// tells an honored index from "asked for iAC, got iAB anyway".
		sg = HypDisjTacticAt(g, iAB)
		require.NotNil(t, sg)
		require.Equal(t, 2, sg.Size())
		gotABranch := sg.ChildGoal(0).HasHyp(A.Core()) && sg.ChildGoal(1).HasHyp(B.Core())
		require.True(t, gotABranch,
			"HypDisjTacticAt(iAB) must split A∨B into {A, B} children; got %s / %s",
			prop.PrintProp(sg.ChildGoal(0)), prop.PrintProp(sg.ChildGoal(1)))
		assertSubGoals(t, sg, g)

		// At-index=iAC: splits A∨C — the second child MUST carry C
		// (not B, which would prove the wrong-index bug is back).
		sg = HypDisjTacticAt(g, iAC)
		require.NotNil(t, sg)
		require.Equal(t, 2, sg.Size())
		assert.True(t, sg.ChildGoal(0).HasHyp(A.Core()))
		assert.True(t, sg.ChildGoal(1).HasHyp(C.Core()),
			"HypDisjTacticAt(iAC) must land on A∨C, so branch 1 has C — got: %s",
			prop.PrintProp(sg.ChildGoal(1)))
		// Cross-check: neither child carries B (the A∨B branch's marker).
		assert.False(t, sg.ChildGoal(0).HasHyp(B.Core()))
		assert.False(t, sg.ChildGoal(1).HasHyp(B.Core()))
		assertSubGoals(t, sg, g)

		// Wrong shape at the index → nil (declines, no wrong split).
		assert.Nil(t, HypDisjTacticAt(g, iD),
			"non-∨ hyp at the index must decline instead of silently picking a different hyp")

		// Out-of-range → nil.
		assert.Nil(t, HypDisjTacticAt(g, -1))
		assert.Nil(t, HypDisjTacticAt(g, g.NumHyps()))
	}

	// --- split_hyp_iff: two ⇔-hyps.
	{
		AiffB := A.Eq(B).Core()
		AiffC := A.Eq(C).Core()
		g := testProp(Cgoal, AiffB, AiffC)
		iAB := findHyp(g, AiffB)
		iAC := findHyp(g, AiffC)
		require.NotEqual(t, -1, iAB)
		require.NotEqual(t, -1, iAC)
		require.NotEqual(t, iAB, iAC)

		// At-index=iAC: first child carries C (the A⇔C branch adds A, C
		// as hyps). B must NOT appear on either child.
		sg := HypIffTacticAt(g, iAC)
		require.NotNil(t, sg)
		require.Equal(t, 2, sg.Size())
		assert.True(t, sg.ChildGoal(0).HasHyp(C.Core()),
			"HypIffTacticAt(iAC) must split A⇔C, so branch 0 has C")
		assert.False(t, sg.ChildGoal(0).HasHyp(B.Core()),
			"HypIffTacticAt(iAC) must NOT split A⇔B (that's the bug this test guards against)")
		assertSubGoals(t, sg, g)

		// At-index=iAB: first child carries B.
		sg = HypIffTacticAt(g, iAB)
		require.NotNil(t, sg)
		require.Equal(t, 2, sg.Size())
		assert.True(t, sg.ChildGoal(0).HasHyp(B.Core()))
		assertSubGoals(t, sg, g)

		// Wrong-shape / out-of-range → nil.
		assert.Nil(t, HypIffTacticAt(g, -1))
		assert.Nil(t, HypIffTacticAt(testProp(Cgoal, A.Core()), 0),
			"non-⇔ hyp at the index must decline")
	}

	// --- split_hyp_imply: two ⇒-hyps.
	{
		AimpB := A.Imply(B).Core()
		AimpC := A.Imply(C).Core()
		g := testProp(Cgoal, AimpB, AimpC)
		iAB := findHyp(g, AimpB)
		iAC := findHyp(g, AimpC)
		require.NotEqual(t, -1, iAB)
		require.NotEqual(t, -1, iAC)
		require.NotEqual(t, iAB, iAC)

		// HypImplyTactic splits A⇒P into two branches:
		//   [0] ¬A added
		//   [1] P (the consequent) added
		// At-index=iAC: branch 1 carries C, not B.
		sg := HypImplyTacticAt(g, iAC)
		require.NotNil(t, sg)
		require.Equal(t, 2, sg.Size())
		assert.True(t, sg.ChildGoal(1).HasHyp(C.Core()),
			"HypImplyTacticAt(iAC) must split A⇒C, so branch 1 carries C")
		assert.False(t, sg.ChildGoal(1).HasHyp(B.Core()),
			"HypImplyTacticAt(iAC) must NOT split A⇒B")
		assertSubGoals(t, sg, g)

		// At-index=iAB: branch 1 carries B.
		sg = HypImplyTacticAt(g, iAB)
		require.NotNil(t, sg)
		require.Equal(t, 2, sg.Size())
		assert.True(t, sg.ChildGoal(1).HasHyp(B.Core()))
		assertSubGoals(t, sg, g)

		assert.Nil(t, HypImplyTacticAt(g, -1))
		assert.Nil(t, HypImplyTacticAt(testProp(Cgoal, A.Core()), 0),
			"non-⇒ hyp at the index must decline")
	}
}

func TestCondRewriteTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Block 1: trivial COND with literal ⊤/⊥ case term — handled by
	// trivialCondRewrite (also part of BasicRewrite). Same behavior as before.
	{
		b := Var("b", TypeBool)
		p := Var("p", TypeB)
		q := Var("q", TypeB)
		R := Var("R", MakeFun(TypeB, TypeBool))

		goal := core.MakeProp(ForAll(p, q)(R.Apply(ext.Cond(T, p, q))))

		subGoals := CondRewriteTactic(goal)
		assert.NotNil(t, subGoals)
		assert.Equal(t, 1, subGoals.Size())
		assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(ForAll(p)(R.Apply(p))))
		assertSubGoals(t, subGoals, goal)

		goal = core.MakeProp(ForAll(p, q)(R.Apply(ext.Cond(F, p, q))))
		subGoals = CondRewriteTactic(goal)
		assert.NotNil(t, subGoals)
		assert.Equal(t, 1, subGoals.Size())
		assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(ForAll(q)(R.Apply(q))))
		assertSubGoals(t, subGoals, goal)

		goal = core.MakeProp(
			ForAll(p, q)(R.Apply(ext.Cond(T, p, q))),
			Exists(p, q)(R.Apply(ext.Cond(F, p, q))),
			b)
		subGoals = CondRewriteTactic(goal)
		assert.NotNil(t, subGoals)
		assert.Equal(t, 1, subGoals.Size())
		// rewriteTactic stops at the first matching site (conclusion here);
		// the hypothesis Cond is left for a subsequent rewrite pass.
		assertPropAlphaEqual(t, subGoals.ChildGoal(0),
			MakeProp(ForAll(p)(R.Apply(p)),
				Exists(p, q)(R.Apply(ext.Cond(F, p, q))), b))
		assertSubGoals(t, subGoals, goal)
	}

	// Block 2: f(COND b p q) where everything is bool.
	// CondElim picks the smallest bool subterm containing the COND.
	// Cond(b, p, q) is itself bool here, so P = identity, and the COND
	// is rewritten in place: Cond(b, p, q) → (b ⇒ p) ∧ (¬b ⇒ q).
	// Output: f((b ⇒ p) ∧ (¬b ⇒ q))
	{
		b := Var("b", TypeBool)
		p := Var("p", TypeBool)
		q := Var("q", TypeBool)
		f := Var("f", MakeFun(TypeBool, TypeBool))
		condApp := ext.Cond(b, p, q)
		goal := core.MakeProp(core.Apply(f, condApp))

		subGoals := CondRewriteTactic(goal)
		assert.NotNil(t, subGoals)
		assert.Equal(t, 1, subGoals.Size())
		assertSubGoals(t, subGoals, goal)
		assertPropAlphaEqual(t, subGoals.ChildGoal(0),
			MakeProp(f.Apply(b.Imply(p).And(Not(b).Imply(q)))))
	}

	// Block 3: f(COND b x y) = g(COND b z w), x/y:A, z/w:B.
	// Two CONDs share the same case term b. Deep CondElim at the equation
	// (the smallest bool ancestor for either COND) eliminates both.
	{
		b := Var("b", TypeBool)
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		z := Var("z", TypeB)
		w := Var("w", TypeB)
		f := Var("f", MakeFun(TypeA, TypeA))
		g := Var("g", MakeFun(TypeB, TypeA))

		condBXY := ext.Cond(b, x, y)
		condBZW := ext.Cond(b, z, w)
		goal := core.MakeProp(core.Eq(core.Apply(f, condBXY), core.Apply(g, condBZW)))

		subGoals := CondRewriteTactic(goal)
		assert.NotNil(t, subGoals)
		assert.Equal(t, 1, subGoals.Size())
		assertSubGoals(t, subGoals, goal)
		// Both CONDs eliminated; same case term b unifies the two splits.
		// Output: (b ⇒ f(x) = g(z)) ∧ (¬b ⇒ f(y) = g(w))
		assertPropAlphaEqual(t, subGoals.ChildGoal(0),
			MakeProp(b.Imply(f.Apply(x).Eq(g.Apply(z))).
				And(Not(b).Imply(f.Apply(y).Eq(g.Apply(w))))))
	}

	// Block 4: f(COND b x y) = g(COND c z w), distinct case terms.
	{
		b := Var("b", TypeBool)
		c := Var("c", TypeBool)
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		z := Var("z", TypeA)
		w := Var("w", TypeA)
		f := Var("f", MakeFun(TypeA, TypeA))
		g := Var("g", MakeFun(TypeA, TypeA))

		condBXY := ext.Cond(b, x, y)
		condCZW := ext.Cond(c, z, w)
		goal := core.MakeProp(f.Apply(condBXY).Eq(g.Apply(condCZW)))

		subGoals := CondRewriteTactic(goal)
		assert.NotNil(t, subGoals)
		assert.Equal(t, 1, subGoals.Size())
		assertSubGoals(t, subGoals, goal)
		// Both CONDs eliminated; nested splits on b (outer) and c (inner).
		// Output: (b ⇒ ((c ⇒ f(x) = g(z)) ∧ (¬c ⇒ f(x) = g(w))))
		//      ∧ (¬b ⇒ ((c ⇒ f(y) = g(z)) ∧ (¬c ⇒ f(y) = g(w))))
		fxgz := f.Apply(x).Eq(g.Apply(z))
		fxgw := f.Apply(x).Eq(g.Apply(w))
		fygz := f.Apply(y).Eq(g.Apply(z))
		fygw := f.Apply(y).Eq(g.Apply(w))
		assertPropAlphaEqual(t, subGoals.ChildGoal(0),
			MakeProp(b.Imply(c.Imply(fxgz).And(Not(c).Imply(fxgw))).
				And(Not(b).Imply(c.Imply(fygz).And(Not(c).Imply(fygw))))))
	}

	// Block 5: COND under lambda. Two sub-cases:
	//   (a) case term `b` is FREE (not captured by the lambdas λy/λa).
	//       CondSwap pushes COND outward through f/g until it reaches the
	//       lambda boundary; then CondElim at the equation eliminates it.
	//   (b) case term IS the lambda's bound variable (b is captured by λb).
	//       CondSwap can still push COND outward inside the lambda body;
	//       CondElim cannot fire because the case term is captured. Result:
	//       COND survives at the outermost position inside each lambda.
	{
		a := Var("a", TypeA)
		b := Var("b", TypeBool)
		y := Var("y", TypeA)
		f := Var("f", MakeFun(TypeA, TypeA))
		g := Var("g", MakeFun(TypeA, TypeA))

		condBAY := ext.Cond(b, a, y)
		fCond := f.Apply(condBAY)
		gCond := g.Apply(condBAY)

		// (a) b is free. CondElim at the equation: P = λh. (λy.λa.f(h)) =
		//     (λy.λa.g(h)). After beta, the lambdas survive on each side —
		//     except that λa.f(a) is an η-redex under λy, which the basic
		//     rewrite reduces to f (the λ under ¬b binds a variable f does
		//     not take, so it stays).
		// Output: (b ⇒ (λy.f) = (λy.g))
		//       ∧ (¬b ⇒ (λy.λa.f(y)) = (λy.λa.g(y)))
		goal := MakeProp(y.To(a.To(fCond)).Eq(y.To(a.To(gCond))))
		subGoals := CondRewriteTactic(goal)
		assert.NotNil(t, subGoals)
		assert.Equal(t, 1, subGoals.Size())
		assertSubGoals(t, subGoals, goal)
		assertPropAlphaEqual(t, subGoals.ChildGoal(0),
			MakeProp(b.Imply(y.To(f).Eq(y.To(g))).
				And(Not(b).Imply(y.To(a.To(f.Apply(y))).Eq(y.To(a.To(g.Apply(y))))))))

		// (b) b is captured by λb. CondElim cannot fire (captured case term);
		// CondSwap pushes COND outward inside each lambda body.
		// Output: (λb. COND(b, f(a), f(y))) = (λb. COND(b, g(a), g(y)))
		goal = MakeProp(b.To(fCond).Eq(b.To(gCond)))
		subGoals = CondRewriteTactic(goal)
		assert.NotNil(t, subGoals)
		assert.Equal(t, 1, subGoals.Size())
		assertSubGoals(t, subGoals, goal)
		assertPropAlphaEqual(t, subGoals.ChildGoal(0),
			MakeProp(b.To(ext.Cond(b, f.Apply(a), f.Apply(y))).
				Eq(b.To(ext.Cond(b, g.Apply(a), g.Apply(y))))))
	}

	// Block 6: COND in both hypothesis and conclusion. CondRewriteTactic
	// rewrites the conclusion first (rewriteTactic stops after first match).
	{
		b := Var("b", TypeBool)
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		f := Var("f", MakeFun(TypeA, TypeBool))
		g := Var("g", MakeFun(TypeA, TypeBool))
		s := Var("s", TypeBool)

		condBXY := ext.Cond(b, x, y)
		// s, f(COND b x y) ⊢ g(COND b x y)
		goal := core.MakeProp(g.Apply(condBXY), f.Apply(condBXY), s)

		subGoals := CondRewriteTactic(goal)
		assert.NotNil(t, subGoals)
		assert.Equal(t, 1, subGoals.Size())
		assertSubGoals(t, subGoals, goal)
		// rewriteTactic stops at the first matching site (conclusion);
		// the COND in the hypothesis is left for a subsequent pass.
		assertPropAlphaEqual(t, subGoals.ChildGoal(0),
			MakeProp(b.Imply(g.Apply(x)).And(Not(b).Imply(g.Apply(y))),
				f.Apply(condBXY), s))
	}
}

func TestByCaseTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	var prop Prop

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	prop = testProp(Q.Apply(x), Q.Apply(z))

	s0 := ByCaseTactic(ForAll(y)(P.Apply(y)))(prop)
	assert.Equal(t, s0.Size(), 2)
	assertSubGoals(t, s0, prop)

	s1 := ByCaseTactic(Not(ForAll(y)(P.Apply(y))))(prop)
	assert.Equal(t, s1.Size(), 2)
	assertSubGoals(t, s1, prop)

	assertPropAlphaEqual(t, s0.ChildGoal(0), s1.ChildGoal(0))
	assertPropAlphaEqual(t, s0.ChildGoal(1), s1.ChildGoal(1))

	prop = testProp(Not(P.Apply(x)), P.Apply(z))
	s := ByCaseTactic(ForAll(y)(P.Apply(y)))(prop)
	assert.Equal(t, s.Size(), 2)
	assertSubGoals(t, s, prop)

	subGoals := ByCaseTactic(P.Apply(z))(prop)
	assert.Nil(t, subGoals)

	subGoals = ByCaseTactic(P.Apply(x))(prop)
	assert.Nil(t, subGoals)
}

func TestHilbertDenoteTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeB, TypeBool))
	f := Var("f", MakeFun(TypeA, TypeB))
	a := Var("a", TypeB)
	x0 := Var("x_0", TypeA)
	y0 := Var("y_0", TypeB)
	z0 := Var("z_0", TypeB)
	alpha := Var("α_0", MakeFun(TypeA, MakeFun(TypeA, TypeB), TypeB))

	s0 := x.Eq(x0).Imply(a.Eq(y0)).And(Not(x.Eq(x0)).Imply(a.Eq(f.Apply(x))))
	s1 := ForAll(x, f)(P.Apply(x, a.SuchThat(s0)))
	s2 := s0.Substitute(ext.MakeTermSubst(a, alpha.Apply(x, f)))
	p := testProp(y0.Eq(z0), s1)
	subGoals := HilbertDenoteTactic(p)
	assert.Equal(t, 1, subGoals.Size())
	assertSubGoals(t, subGoals, p)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(y0.Eq(z0),
			ForAll(x, f)(Exists(a)(s0).Imply(s2)),
			ForAll(x, f)(P.Apply(x, alpha.Apply(x, f)))))

	p = testProp(s1, y0.Eq(z0))
	subGoals = HilbertDenoteTactic(p)
	assert.Equal(t, 1, subGoals.Size())
	assertSubGoals(t, subGoals, p)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(ForAll(x, f)(P.Apply(x, alpha.Apply(x, f))),
			ForAll(x, f)(Exists(a)(s0).Imply(s2)),
			y0.Eq(z0)))

}

func TestDenoteTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	var prop Prop
	var subGoals *SubGoals
	tactic := DenoteTactic(3)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeA))
	R := Var("R", MakeFun(TypeA, TypeBool))

	prop = testProp(F, P.Apply(Q.Apply(x), y), P.Apply(Q.Apply(x), z), P.Apply(Q.Apply(x)).Eq(R))
	subGoals = tactic(prop)
	assert.Nil(t, subGoals)

	// The repeated P(Q(x)) occurs only as the head of an application — a
	// spine prefix — and Q(x) is below the threshold: nothing to name.
	prop = testProp(F, P.Apply(Q.Apply(x), y), P.Apply(Q.Apply(x), z))
	assert.Nil(t, tactic(prop))

	// Q(Q(x)) is a repeated VALUE above the threshold; the prefix
	// P(Q(Q(x))) that would outweigh it by one node is not a candidate.
	QQ := func(v Term) Term { return Q.Apply(Q.Apply(v)) }
	prop = testProp(F, P.Apply(QQ(x), y), P.Apply(QQ(x), z))
	subGoals = tactic(prop)
	assertSubGoals(t, subGoals, prop)
	assert.Equal(t, 1, subGoals.Size())
	assert.Nil(t, tactic(subGoals.childrenGoals[0]))

	prop = testProp(P.Apply(QQ(x), y), P.Apply(QQ(x), z))
	subGoals = tactic(prop)
	assertSubGoals(t, subGoals, prop)
	assert.Equal(t, 1, subGoals.Size())
	assert.Nil(t, tactic(subGoals.childrenGoals[0]))

	prop = testProp(ForAll(x)(P.Apply(z, x)),
		ForAll(y)(P.Apply(QQ(y), x)),
		ForAll(z)(P.Apply(QQ(z), z)))
	subGoals = tactic(prop)
	assertSubGoals(t, subGoals, prop)
	assert.Equal(t, 1, subGoals.Size())
	assert.Nil(t, tactic(subGoals.childrenGoals[0]))

	prop = testProp(ForAll(z)(P.Apply(QQ(z), z)).Eq(Exists(y)(P.Apply(QQ(y), x))))
	subGoals = tactic(prop)
	assertSubGoals(t, subGoals, prop)
	assert.Equal(t, 1, subGoals.Size())
	assert.Nil(t, tactic(subGoals.childrenGoals[0]))

	prop = testProp(
		y.To(ForAll(z)(P.Apply(QQ(z), y))).Apply(y),
		x.To(Exists(z)(P.Apply(QQ(z), x))).Apply(x))
	subGoals = tactic(prop)
	assertSubGoals(t, subGoals, prop)
	assert.Equal(t, 1, subGoals.Size())
	assert.Nil(t, tactic(subGoals.childrenGoals[0]))
}

// Regression test: DenoteRewrite operates bottom-up and may rewrite inside
// lambda bodies, producing eta-expanded forms. When a function-typed subterm
// like f(x,y) : A→A→bool appears both bare (as argument to g) and applied
// under quantifiers (as f(x,y,a,b)), the reconstruction must handle the
// eta-expansion mismatch via BetaEtaRefl.
func TestDenoteTacticEtaExpansion(t *testing.T) {
	defer goleak.VerifyNone(t)

	// f : A → A → A → A → bool (4-ary), so f(x,y) : A → A → bool
	f := ext.TestConst("f", MakeFun(TypeA, TypeA, TypeA, TypeA, TypeBool))
	// g : (A → A → bool) → bool (takes a binary predicate)
	g := ext.TestConst("g", MakeFun(MakeFun(TypeA, TypeA, TypeBool), TypeBool))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)

	fxy := f.Apply(x).Apply(y) // f(x,y) : A → A → bool — the frequent subterm

	// Conclusion: g(f(x,y)) — contains f(x,y) as a bare function-typed arg.
	// Since conclusion ≠ ⊥, negConcl = ¬g(f(x,y)) is added as a hyp.
	concl := g.Apply(fxy)

	// Hypothesis: ∀a.∀b.(f(x,y,a,b) ⇔ f(x,y,a,b)) — contains f(x,y)
	// applied under quantifier binders. The bottom-up DenoteRewrite rewrites
	// f(x,y,a,b) → α₀(a,b) inside λa.λb, producing λa.λb.α₀(a,b) instead
	// of the bare α₀. On reconstruction (α₀→f(x,y)), this becomes
	// λa.λb.f(x,y,a,b) which is eta-expanded compared to f(x,y).
	hyp := ForAll(a)(ForAll(b)(
		fxy.Apply(a).Apply(b).Eq(fxy.Apply(a).Apply(b))))

	tactic := DenoteTactic(3)
	prop := testProp(concl, hyp)
	subGoals := tactic(prop)
	assertSubGoals(t, subGoals, prop)
	assert.Equal(t, 1, subGoals.Size())
}

// Regression test: same eta-expansion issue as above, but the
// partial application f(x,y) lives in a regular hypothesis (not negConcl).
// Conclusion is ⊥ so no negConcl is created. The hypothesis g(f(x,y)) gets
// rewritten to g(α₀) where α₀ = λa.λb.f(x,y,a,b), and after reconstruction
// becomes g(λa.λb.f(x,y,a,b)) — eta-expanded compared to g(f(x,y)).
// Without the BetaEtaRefl bridging for goal hypotheses, makeSubGoals panics.
func TestDenoteTacticHypEtaExpansion(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := ext.TestConst("f", MakeFun(TypeA, TypeA, TypeA, TypeA, TypeBool))
	g := ext.TestConst("g", MakeFun(MakeFun(TypeA, TypeA, TypeBool), TypeBool))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)

	fxy := f.Apply(x).Apply(y)

	// hyp1: ∀a.∀b.(f(x,y,a,b) ⇔ f(x,y,a,b)) — makes λa.λb.f(x,y,a,b) the
	// frequent subterm (count=2 from both sides of the Eq).
	hyp1 := ForAll(a)(ForAll(b)(
		fxy.Apply(a).Apply(b).Eq(fxy.Apply(a).Apply(b))))

	// hyp2: g(f(x,y)) — contains f(x,y) as a bare partial application.
	// DenoteRewrite matches this via eta-equivalence (f(x,y) ≈ λa.λb.f(x,y,a,b))
	// and rewrites to g(α₀). After substituting back, g(α₀) becomes
	// g(λa.λb.f(x,y,a,b)) which needs BetaEtaRefl to match g(f(x,y)).
	hyp2 := g.Apply(fxy)

	tactic := DenoteTactic(3)
	prop := testProp(F, hyp1, hyp2)
	subGoals := tactic(prop)
	assert.NotNil(t, subGoals)
	assertSubGoals(t, subGoals, prop)
	assert.Equal(t, 1, subGoals.Size())
}

func TestUnifyEqSimplifyTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	tactic := unifyEqSimplifyTactic
	var prop Prop
	var subGoals *SubGoals

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeA))
	R := Var("R", MakeFun(TypeA, TypeBool))

	prop = testProp(Not(Q.Apply(x).Eq(x)), P.Apply(x, x), Q.Apply(x).Eq(x))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Q.Apply(x).Eq(x), P.Apply(x, x), Not(Q.Apply(x).Eq(x)))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(F, P.Apply(Q.Apply(x), y), Q.Apply(x).Eq(x))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(F, P.Apply(Q.Apply(x), y), ForAll(x)(Q.Apply(x).Eq(x)))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(R.Apply(x), ForAll(y)(P.Apply(y, x).Eq(R.Apply(x))), ForAll(x)(Q.Apply(x).Eq(x)))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Not(P.Apply(Q.Apply(x), y)), ForAll(x)(Q.Apply(x).Eq(x)))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Not(P.Apply(Q.Apply(x), y)), ForAll(x)(x.Eq(Q.Apply(x))))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Not(Q.Apply(x).Eq(x)), P.Apply(Q.Apply(x), y))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Not(x.Eq(Q.Apply(x))), x.Eq(Q.Apply(x)), P.Apply(Q.Apply(x), y))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(P.Apply(x, y).Eq(Q.Apply(y).Eq(x)), x.Eq(Q.Apply(x)), P.Apply(Q.Apply(x), y))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(F, P.Apply(Q.Apply(x), Q.Apply(y)), ForAll(x, y)(Q.Apply(x).Eq(y)))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Exists(x)(Not(Q.Apply(x).Eq(x))), ForAll(y)(P.Apply(Q.Apply(x), y)))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Exists(x)(Not(Q.Apply(x).Eq(x))), ForAll(x)(P.Apply(Q.Apply(x), y)))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(F, ForAll(x)(R.Apply(Q.Apply(x))),
		y.SuchThat(R.Apply(Q.Apply(y)).Imply(P.Apply(y, y))).Eq(z))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Exists(x)(R.Apply(Q.Apply(x))),
		y.SuchThat(R.Apply(Q.Apply(y)).Imply(P.Apply(y, y))).Eq(z))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)

	prop = testProp(Exists(y)(Not(P.Apply(x, y))),
		P.Apply(x, x), ForAll(y)(P.Apply(x, y).Eq(R.Apply(y))))
	subGoals = mergeTactics(unifyEqSimplifyTactic)(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)
	assert.True(t, subGoals.ChildGoal(0).HasHyp(T))

	prop = testProp(R.Apply(y), Exists(x)(R.Apply(x)), ForAll(x)(Not(R.Apply(x))))
	subGoals = mergeTactics(BasicTactics, unifyEqSimplifyTactic)(prop)
	assert.Equal(t, subGoals.Size(), 0)
	assertSubGoals(t, subGoals, prop)

	plus := ext.TestConst("+", MakeFun(TypeA, TypeA, TypeA))

	prop = testProp(
		plus.Apply(plus.Apply(y, z), x).Eq(plus.Apply(x, plus.Apply(y, z))).
			And(plus.Apply(plus.Apply(y, z), x).Eq(plus.Apply(y, plus.Apply(x, z)))),
		ForAll(x, y)(plus.Apply(x, y).Eq(plus.Apply(y, x))),
		ForAll(x, y, z)(plus.Apply(x, plus.Apply(y, z)).Eq(plus.Apply(plus.Apply(x, y), z))))
	subGoals = tactic(prop)
	assert.Equal(t, subGoals.Size(), 1)
	assertSubGoals(t, subGoals, prop)
}

// TestEqSimplify_SizeGuardSplit pins down the agent-driven vs internal
// dispatch split: with allowExpand=false (the default for fixpoint
// callers in BasicTactics), an expansion-style rewrite is rejected to
// keep the merged-tactic loop terminating. With allowExpand=true (the
// one-shot path used by eqLemmaTacticExpand → LeanRwTactic →
// def_expand), the rewrite goes through, transforming the matched hyp
// into the larger RHS.
//
// The fixture: hyp `done = (a ∧ b)` is the rewrite witness, applied to
// hyp `done`. Default-false rejects (size doesn't decrease); expand-true
// accepts and rewrites `done` to `a ∧ b` in the resulting subgoal hyps.
func TestEqSimplify_SizeGuardSplit(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	done := Var("done", TypeBool)

	// eq: done = (a ∧ b). Rewriting `done` via this eq is an expansion.
	eq := done.Eq(a.And(b))
	// Goal: done, eq ⊢ ⊥. eqSimplify should try to use eq to rewrite the
	// `done` hyp.
	goal := testProp(F, done, eq)

	// allowExpand=false: existing default for fixpoint contexts. The
	// rewrite finds a match but the size guard rejects it, so the
	// candidate hyp loops don't advance and eqSimplify returns nil.
	guarded := eqSimplify(fullSearch, new(prop.PreCNFCache), goal, eq, true, false)
	assert.Nil(t, guarded,
		"eqSimplify with allowExpand=false must reject the expansion rewrite")

	// allowExpand=true: agent-driven one-shot path. The size guard is
	// bypassed and the rewrite produces a subgoal whose hyps include
	// the expanded form `a ∧ b` (instead of the original `done`).
	expand := eqSimplify(fullSearch, new(prop.PreCNFCache), goal, eq, true, true)
	require.NotNil(t, expand,
		"eqSimplify with allowExpand=true must accept the expansion rewrite")
	assertSubGoals(t, expand, goal)
	assert.Equal(t, 1, expand.Size())
	child := expand.ChildGoal(0)
	hasExpanded := false
	for h := range child.HypIter() {
		if h.AlphaEquals(a.And(b).Core()) {
			hasExpanded = true
			break
		}
	}
	assert.True(t, hasExpanded,
		"expansion subgoal must contain the rewritten hyp `a ∧ b`; got %v",
		child.Hyps())
}

// TestDenormalizeConclTactic exercises the tactic that reverses prop.Normalize
// on the goal's conclusion — stripping outer ∀ and peeling outer ⇒ into hyps
// until the conclusion is a bare proposition. Each case checks (a) the shape
// of the resulting subgoal and (b) reconstruction correctness via assertSubGoals.
func TestDenormalizeConclTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))

	var goal Prop
	var subGoals *SubGoals

	// No-op: bare atom, no outer ⇒/∀.
	goal = testProp(P.Apply(x))
	assert.Nil(t, denormalizeConclTactic(goal))

	// No-op: concl is atomic even with pre-existing hyps.
	goal = testProp(Q.Apply(x), P.Apply(x))
	assert.Nil(t, denormalizeConclTactic(goal))

	// No-op: t0 α-equals t1 in `t0 ⇒ t1` — matches the guard so we don't
	// peel a trivial ⇒. (Mirrors ConclImplyTactic's same guard.)
	goal = testProp(P.Apply(x).Imply(P.Apply(x)))
	assert.Nil(t, denormalizeConclTactic(goal))

	// ⇒-peel, one level. ⊢ P(x) ⇒ Q(x)  →  P(x) ⊢ Q(x)
	goal = testProp(P.Apply(x).Imply(Q.Apply(x)))
	subGoals = denormalizeConclTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(Q.Apply(x), P.Apply(x)))
	assertSubGoals(t, subGoals, goal)

	// ⇒-peel, chained.  ⊢ P(x) ⇒ Q(x) ⇒ R(x,y)  →  P(x), Q(x) ⊢ R(x,y)
	goal = testProp(P.Apply(x).Imply(Q.Apply(x).Imply(R.Apply(x, y))))
	subGoals = denormalizeConclTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(R.Apply(x, y), P.Apply(x), Q.Apply(x)))
	assertSubGoals(t, subGoals, goal)

	// ∀-strip, one var.  ⊢ ∀x. P(x)  →  ⊢ P(x)  (x becomes free)
	goal = testProp(ForAll(x)(P.Apply(x)))
	subGoals = denormalizeConclTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(P.Apply(x)))
	assertSubGoals(t, subGoals, goal)

	// ∀-strip, multiple vars from one ForAll chain.
	//   ⊢ ∀x.∀y. R(x,y)  →  ⊢ R(x,y)
	goal = testProp(ForAll(x, y)(R.Apply(x, y)))
	subGoals = denormalizeConclTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(R.Apply(x, y)))
	assertSubGoals(t, subGoals, goal)

	// ∀ then ⇒ alternation, single iteration.
	//   ⊢ ∀x. P(x) ⇒ Q(x)  →  P(x) ⊢ Q(x)
	goal = testProp(ForAll(x)(P.Apply(x).Imply(Q.Apply(x))))
	subGoals = denormalizeConclTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(Q.Apply(x), P.Apply(x)))
	assertSubGoals(t, subGoals, goal)

	// Nested alternation ∀ ⇒ ∀ — exercises the iterative loop across step kinds.
	//   ⊢ ∀x. P(x) ⇒ ∀y. R(x,y)  →  P(x) ⊢ R(x,y)
	goal = testProp(ForAll(x)(P.Apply(x).Imply(ForAll(y)(R.Apply(x, y)))))
	subGoals = denormalizeConclTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(R.Apply(x, y), P.Apply(x)))
	assertSubGoals(t, subGoals, goal)

	// Pre-existing hyp + ⇒-peel: hyp is preserved, new hyp appended.
	//   R(x,y) ⊢ P(x) ⇒ Q(x)  →  R(x,y), P(x) ⊢ Q(x)
	goal = testProp(P.Apply(x).Imply(Q.Apply(x)), R.Apply(x, y))
	subGoals = denormalizeConclTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(Q.Apply(x), R.Apply(x, y), P.Apply(x)))
	assertSubGoals(t, subGoals, goal)

	// Name collision between a goal-free var and the ∀-bound var: the tactic
	// must fresh-rename the bound var to avoid capture. The specific rename
	// is an implementation detail — α-equivalence handles it. We verify
	// (i) assertSubGoals passes (round-trip proof reconstruction), and
	// (ii) the hyp set is preserved literally (only concl was transformed).
	//   P(x) ⊢ ∀x. Q(x)  →  P(x) ⊢ Q(x')  for some fresh x'
	goal = testProp(ForAll(x)(Q.Apply(x)), P.Apply(x))
	subGoals = denormalizeConclTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assert.Equal(t, 1, subGoals.ChildGoal(0).NumHyps())
	assert.True(t, subGoals.ChildGoal(0).Hyps()[0].AlphaEquals(P.Apply(x)))
	assertSubGoals(t, subGoals, goal)

	// ⇒-peel where t0 is a complex term (∀ inside a hyp is allowed — we only
	// peel top-level ⇒ on concl side; ∀ inside the peeled hyp stays put).
	//   ⊢ (∀x.P(x)) ⇒ Q(y)  →  ∀x.P(x) ⊢ Q(y)
	goal = testProp(ForAll(x)(P.Apply(x)).Imply(Q.Apply(y)))
	subGoals = denormalizeConclTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(Q.Apply(y), ForAll(x)(P.Apply(x))))
	assertSubGoals(t, subGoals, goal)
}

func TestAssertTactic_BasicSplit(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", TypeBool)
	Q := Var("Q", TypeBool)
	R := Var("R", TypeBool)

	// goal: R ⊢ Q (Q is the conclusion; R is a hyp)
	goal := MakeProp(Q, R)

	// assert P
	subGoals := AssertTactic(MakeProp(P))(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	// child(0) = R ⊢ P
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(P, R))
	// child(1) = R, P ⊢ Q
	assertPropAlphaEqual(t, subGoals.ChildGoal(1), MakeProp(Q, R, P))
	// reconstruct from trivial Thms is well-formed.
	assertSubGoals(t, subGoals, goal)
}

func TestAssertTactic_NoHypsOnGoal(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", TypeBool)
	Q := Var("Q", TypeBool)

	// goal: ⊢ Q (no hyps)
	goal := MakeProp(Q)

	subGoals := AssertTactic(MakeProp(P))(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(P))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1), MakeProp(Q, P))
	assertSubGoals(t, subGoals, goal)
}

func TestAssertTactic_NoOpWhenAlreadyHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", TypeBool)
	Q := Var("Q", TypeBool)

	goal := MakeProp(Q, P) // P already in hyps

	// Asserting P would be useless — return nil.
	assert.Nil(t, AssertTactic(MakeProp(P))(goal))
}

func TestAssertTactic_NoOpWhenSameAsConcl(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", TypeBool)

	goal := MakeProp(P)

	// Asserting the goal's conclusion is trivially circular — return nil.
	assert.Nil(t, AssertTactic(MakeProp(P))(goal))
}

func TestAssertTactic_Reconstruction_AlphaEqualsLemmaOnlyProof(t *testing.T) {
	defer goleak.VerifyNone(t)

	// goal: ⊢ Q, asserting P and then closing both with trivial test-thms.
	// The reconstructed prop should be α-equal to ⊢ Q.
	P := Var("P", TypeBool)
	Q := Var("Q", TypeBool)
	goal := MakeProp(Q)

	subGoals := AssertTactic(MakeProp(P))(goal)
	thm0 := testThm(P)    // proves ⊢ P
	thm1 := testThm(Q, P) // proves P ⊢ Q

	reconstructed := subGoals.Reconstruct(thm0, thm1)
	assert.True(t, reconstructed.Proved())
	assert.Equal(t, 0, reconstructed.NumHyps())
	assert.True(t, reconstructed.Conclusion().AlphaEquals(Q))
}

func TestAssertTactic_ResidualNotUsingClaim(t *testing.T) {
	defer goleak.VerifyNone(t)

	// If the residual was closed without using the asserted hyp,
	// reconstruct should return the residual thm unchanged.
	P := Var("P", TypeBool)
	Q := Var("Q", TypeBool)
	goal := MakeProp(Q)

	subGoals := AssertTactic(MakeProp(P))(goal)
	thm0 := testThm(P) // proves ⊢ P
	thm1 := testThm(Q) // proves ⊢ Q WITHOUT P as a hyp

	reconstructed := subGoals.Reconstruct(thm0, thm1)
	assert.True(t, reconstructed.Proved())
	assert.True(t, reconstructed.Conclusion().AlphaEquals(Q))
}

// makeHilbertTestConst builds a const whose def has the direct Hilbert
// shape `⊢ c = εx:A.(x = x)` — a basic definition's shape.
func makeHilbertTestConst(name string) ConstTerm {
	x := Var("x", TypeA)
	body := x.SuchThat(x.Eq(x).Core()) // εx:A.(x = x)
	return ext.ConstDef(body.Core(), ext.TermName(name)).AssertConst()
}

// makeAppliedHilbertTestConst builds a const whose def has the applied
// Hilbert shape `⊢ c = (εF.∀_idx. F(_idx) = _idx)(T)` — analog of the
// shape produced by a recursive definition (the shape +, list_member,
// * etc. are defined in).
func makeAppliedHilbertTestConst(name string) ConstTerm {
	boolToBool := MakeFun(TypeBool, TypeBool)
	F := Var("F", boolToBool)
	idx := Var("_idx", TypeBool)
	body := ForAll(idx)(F.Apply(idx).Eq(idx).Core())
	hilbert := F.SuchThat(body.Core())
	// Witness must be closed; use T (the bool constant true).
	rhs := ext.WrapTerm(hilbert.Core()).Apply(T)
	return ext.ConstDef(rhs.Core(), ext.TermName(name)).AssertConst()
}

func TestExistentialConstDefTactic_BasicSplit(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := makeHilbertTestConst("TestExistentialConstDefTactic_BasicSplit_C")
	R := Var("R", TypeBool)
	Q := Var("Q", TypeBool)

	// goal: R ⊢ Q  — note c doesn't occur; the tactic doesn't gate on
	// "c appears in goal" because the unfold is useful purely for
	// surfacing the existence claim + P(c) into context.
	goal := MakeProp(Q, R)

	subGoals := ExistentialConstDefTactic(c)(goal)
	require.NotNil(t, subGoals)
	require.Equal(t, 2, subGoals.Size())

	// child(0): R ⊢ ∃x.(x = x)  (existence claim, original hyps retained)
	child0 := subGoals.ChildGoal(0)
	assert.Equal(t, 1, child0.NumHyps())
	assert.True(t, child0.HasHyp(R))
	vars, _ := ext.DecomposesEXISTS(child0.Conclusion())
	assert.False(t, vars.Empty(),
		"existence subgoal conclusion must be ∃-headed")

	// child(1): R, (c = c) ⊢ Q  (residual gains P(c) as a free hyp)
	child1 := subGoals.ChildGoal(1)
	assert.Equal(t, 2, child1.NumHyps())
	assert.True(t, child1.HasHyp(R))
	assert.True(t, child1.Conclusion().AlphaEquals(Q),
		"residual conclusion must equal original goal conclusion")

	// Reconstruction is well-formed across the standard testThm grid
	// (full proofs, ⊥-proofs, random hyp drops). Catches DeriveHypFrom
	// chain bugs and the "residual didn't use P(c)" short-circuit.
	assertSubGoals(t, subGoals, goal)
}

func TestExistentialConstDefTactic_NoHypsOnGoal(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := makeHilbertTestConst("TestExistentialConstDefTactic_NoHyps_C")
	Q := Var("Q", TypeBool)
	goal := MakeProp(Q)

	subGoals := ExistentialConstDefTactic(c)(goal)
	require.NotNil(t, subGoals)
	require.Equal(t, 2, subGoals.Size())
	assert.Equal(t, 0, subGoals.ChildGoal(0).NumHyps())
	// child(1) carries only P(c) as a hyp.
	assert.Equal(t, 1, subGoals.ChildGoal(1).NumHyps())
	assertSubGoals(t, subGoals, goal)
}

func TestExistentialConstDefTactic_NonHilbertReturnsNil(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Plain ConstDef (λa.body), not Hilbert.
	a := Var("a", TypeA)
	c := ext.ConstDef(a.To(a.Eq(a).Core()).Core(),
		"TestExistentialConstDefTactic_NonHilbert_C").AssertConst()
	Q := Var("Q", TypeBool)
	goal := MakeProp(Q)

	// Tactic gates on prop.ExistentialConstDef returning non-nil;
	// non-Hilbert const → nil result.
	assert.Nil(t, ExistentialConstDefTactic(c)(goal),
		"ExistentialConstDefTactic must return nil for non-Hilbert const defs")
}

func TestExistentialConstDefTactic_NoOpWhenPcAlreadyHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := makeHilbertTestConst("TestExistentialConstDefTactic_PcInHyp_C")
	// P(c) for this fixture is (c = c). If the goal already has it as
	// a hyp, the tactic should no-op — there's nothing to add.
	pcTerm := WrapTerm(c).Eq(c).Core() // (c = c)
	Q := Var("Q", TypeBool)
	goal := MakeProp(Q, pcTerm)

	assert.Nil(t, ExistentialConstDefTactic(c)(goal),
		"ExistentialConstDefTactic must no-op when P(c) is already a hyp")
}

func TestExistentialConstDefTactic_NoOpWhenExistsAlreadyConcl(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := makeHilbertTestConst("TestExistentialConstDefTactic_ExistsAsConcl_C")
	// Build a goal whose conclusion IS ∃x.(x = x) — same as the
	// existence subgoal the tactic would produce. The tactic should
	// no-op: producing the same conclusion as child(0) would be
	// circular.
	existsThm := prop.ExistentialConstDef(c)
	require.False(t, existsThm.IsZero())
	existsTerm := existsThm.Hyps()[0] // ∃x.(x = x)

	goal := MakeProp(existsTerm)
	assert.Nil(t, ExistentialConstDefTactic(c)(goal),
		"ExistentialConstDefTactic must no-op when ∃x.P(x) is the goal conclusion")
}

func TestExistentialConstDefTactic_Reconstruction_ResidualUsesPc(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := makeHilbertTestConst("TestExistentialConstDefTactic_Reconstruct_C")
	Q := Var("Q", TypeBool)
	goal := MakeProp(Q)

	subGoals := ExistentialConstDefTactic(c)(goal)
	require.NotNil(t, subGoals)

	// thm0 proves ⊢ ∃x.(x = x); thm1 proves (c = c) ⊢ Q.
	// Reconstruct must produce ⊢ Q with no leftover hyps — i.e. P(c)
	// was discharged via the pcThm + thm0 chain.
	thm0 := testThm(subGoals.ChildGoal(0).Conclusion(),
		subGoals.ChildGoal(0).Hyps()...)
	thm1 := testThm(subGoals.ChildGoal(1).Conclusion(),
		subGoals.ChildGoal(1).Hyps()...)
	reconstructed := subGoals.Reconstruct(thm0, thm1)
	assert.True(t, reconstructed.Proved())
	assert.Equal(t, 0, reconstructed.NumHyps(),
		"reconstruct must discharge both ∃-hyp (via thm0) and P(c)-hyp (via pcThm)")
	assert.True(t, reconstructed.Conclusion().AlphaEquals(Q))
}

// TestExistentialConstDefTactic_AppliedHilbert: end-to-end for the
// real-world shape — c = (εF.P(F))(args). Pre-extension this case
// would fall through (IsHilbertConstDef returned false), missing the
// exact pattern motivating this whole path.
func TestExistentialConstDefTactic_AppliedHilbert(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := makeAppliedHilbertTestConst("TestExistentialConstDefTactic_AppliedHilbert_C")
	Q := Var("Q", TypeBool)
	goal := MakeProp(Q)

	subGoals := ExistentialConstDefTactic(c)(goal)
	require.NotNil(t, subGoals,
		"tactic must fire on applied-Hilbert shape")
	require.Equal(t, 2, subGoals.Size())

	// child(0) is the existence claim — ∃-headed.
	vars, _ := ext.DecomposesEXISTS(subGoals.ChildGoal(0).Conclusion())
	assert.False(t, vars.Empty(),
		"applied-Hilbert child(0) must still be ∃-headed")

	// Reconstruction via the standard test grid (catches DeriveHypFrom
	// chain bugs introduced by the applied-shape changes).
	assertSubGoals(t, subGoals, goal)
}

func TestExistentialConstDefTactic_Reconstruction_ResidualSkipsPc(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Mirrors AssertTactic's "residual not using claim" optimization:
	// if thm1 doesn't actually use P(c), reconstruct returns thm1
	// directly without dragging the existence proof through.
	c := makeHilbertTestConst("TestExistentialConstDefTactic_SkipsPc_C")
	Q := Var("Q", TypeBool)
	goal := MakeProp(Q)

	subGoals := ExistentialConstDefTactic(c)(goal)
	require.NotNil(t, subGoals)

	thm0 := testThm(subGoals.ChildGoal(0).Conclusion()) // ⊢ ∃x.(x = x)
	thm1 := testThm(Q)                                  // ⊢ Q (no P(c) hyp)

	reconstructed := subGoals.Reconstruct(thm0, thm1)
	assert.True(t, reconstructed.Proved())
	assert.True(t, reconstructed.Conclusion().AlphaEquals(Q))
	assert.Equal(t, 0, reconstructed.NumHyps())
}

// withWhistleDepth temporarily lowers the backstop so tests can reach
// the whistle without thousands of steps.
func withWhistleDepth(t *testing.T, depth int) {
	t.Helper()
	saved := whistleBackstopDepth
	whistleBackstopDepth = depth
	t.Cleanup(func() { whistleBackstopDepth = saved })
}

// keepGoalReconstruct builds a reconstruct callback that satisfies
// makeSubGoals' IsStronger assert without modeling a real proof step —
// these tests only exercise the driver, never Reconstruct.
func keepGoalReconstruct(goal Prop) _TacticReconstruct {
	return func(...Prop) Prop { return goal }
}

// A tactic that always wraps the conclusion in one more ¬ diverges by
// pure growth. Without the whistle, mergeTactics recurses forever; with
// it, the branch must stop right past the backstop: the ancestor path
// sets (all suffixes of the ¬-chain) embed into every later goal.
func TestWhistleStopsGrowthDivergence(t *testing.T) {
	const depth = 8
	withWhistleDepth(t, depth)

	grow := func(goal Prop) *SubGoals {
		child := MakeProp(Not(goal.Conclusion()).Core())
		return MakeSubGoals(goal, keepGoalReconstruct(goal), child)
	}

	// Tripwire observability: the cut must bump the process counter and
	// deliver a WhistleEvent naming this driver and the cut goal.
	var events []skeleton.WhistleEvent
	skeleton.OnWhistleFire = func(ev skeleton.WhistleEvent) { events = append(events, ev) }
	t.Cleanup(func() { skeleton.OnWhistleFire = nil })
	firesBefore := skeleton.WhistleFires()

	p := MakeProp(Var("p", TypeBool).Core())
	s := mergeTactics(grow)(p)
	require.NotNil(t, s)
	require.Equal(t, 1, s.Size())
	// Trajectory: depth 1 = p, depth k = ¬^(k-1) p. The first node past
	// the backstop (depth+1) embeds its ancestors and is kept
	// unexpanded, so the surviving child is ¬^depth p — size depth+1.
	assert.Equal(t, depth+1, s.ChildGoal(0).Conclusion().Size())

	assert.Equal(t, int64(1), skeleton.WhistleFires()-firesBefore)
	require.Len(t, events, 1)
	assert.Equal(t, "mergeTactics", events[0].Driver)
	assert.Equal(t, depth+1, events[0].Depth)
	assert.Equal(t, depth, events[0].Budget)
	require.NotNil(t, events[0].Goal)
	assert.True(t, events[0].Goal.AlphaEquals(s.ChildGoal(0)))
	require.NotNil(t, events[0].Entry)
	assert.True(t, events[0].Entry.AlphaEquals(p), "the event carries the goal the fixpoint was entered with")
}

// A loop that renames free variables at every step (the unifier's
// fresh-variable churn) never trips expand's α-repeat assert in
// makeSubGoals — each state is a distinct prop — so the old driver
// spins forever. (An EXACT α-repeat 2-cycle is different: flattening
// folds the grandchild back onto the grandparent and the driver panics
// on makeSubGoals' AlphaEquals assert — loud, not divergent.) The
// wildcard alphabet erases free-var identity, so every renamed state
// embeds its ancestors and the whistle cuts the loop.
func TestWhistleStopsFreshVarLoop(t *testing.T) {
	withWhistleDepth(t, 8)

	k := 0
	rename := func(goal Prop) *SubGoals {
		if _, _, ok := MatchesEQ(goal.Conclusion()); !ok {
			return nil
		}
		k++
		child := MakeProp(Eq(
			Var(TermName(fmt.Sprintf("a%d", k)), TypeA).Core(),
			Var(TermName(fmt.Sprintf("b%d", k)), TypeA).Core()))
		return MakeSubGoals(goal, keepGoalReconstruct(goal), child)
	}

	a := Var("a", TypeA).Core()
	b := Var("b", TypeA).Core()
	s := mergeTactics(rename)(MakeProp(Eq(a, b)))
	require.NotNil(t, s)
	require.Equal(t, 1, s.Size())
}

// A strictly shrinking trajectory must NEVER be cut, no matter how far
// past the backstop it runs: the size gate keeps every larger ancestor
// out of the embedding check. This pins the bit-identical-replay
// guarantee for terminating (shrinking) fixpoints of any length.
func TestWhistleDoesNotCutShrinkingTrajectory(t *testing.T) {
	const depth = 8
	withWhistleDepth(t, depth)

	strip := func(goal Prop) *SubGoals {
		body := ext.MatchesNOT(goal.Conclusion())
		if body == nil {
			return nil
		}
		return MakeSubGoals(goal, keepGoalReconstruct(goal), MakeProp(body))
	}

	// Start 5× past the backstop.
	concl := Var("p", TypeBool).Core()
	p := MakeProp(concl)
	deep := concl
	for range depth * 5 {
		deep = Not(deep).Core()
	}

	s := mergeTactics(strip)(MakeProp(deep))
	require.NotNil(t, s)
	require.Equal(t, 1, s.Size())
	// Fully stripped: the fixpoint reached the bare variable.
	assert.True(t, s.ChildGoal(0).AlphaEquals(p))
}

// Trajectory semantics at the skeleton level, over real Props with
// hypotheses.
func TestTrajectoryEmbedsAncestor(t *testing.T) {
	x := Var("x", TypeBool).Core()
	h := Var("h", TypeBool).Core()

	var root *skeleton.Trajectory
	n1 := root.Extend(MakeProp(x, h))
	assert.Equal(t, 1, n1.Depth())
	assert.False(t, n1.EmbedsAncestor())

	// Growth over the same structure: embeds the ancestor.
	n2 := n1.Extend(MakeProp(Not(x).Core(), h))
	assert.Equal(t, 2, n2.Depth())
	assert.True(t, n2.EmbedsAncestor())

	// Shrink below the ancestor's size: size gate keeps it silent.
	n3 := n2.Extend(MakeProp(x))
	assert.False(t, n3.EmbedsAncestor())

	// Exact repeat of a distant ancestor (loop): caught.
	n4 := n3.Extend(MakeProp(x, h))
	assert.True(t, n4.EmbedsAncestor())
}

// BasicTacticsUnder abandons the search at the deadline: a cancelled
// context yields nil for a goal the unbounded search closes outright —
// the recorder's economy audit runs probe A on this contract.
func TestBasicTacticsUnderAbandonsAtTheDeadline(t *testing.T) {
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	// a ∧ b ⊢ b ∧ a: the conclusion splits, then each half closes.
	goal := MakeProp(b.And(a).Core(), a.And(b).Core())

	open := BasicTacticsUnder(context.Background())(goal)
	require.NotNil(t, open)
	assert.Equal(t, 0, open.Size(), "the unbounded search closes the goal")

	done, cancel := context.WithCancel(context.Background())
	cancel()
	assert.Nil(t, BasicTacticsUnder(done)(goal), "past the deadline the search is abandoned")
}

// BasicTacticsUntil tells an abandoned search from one that had nothing
// to do, and under a context that never ends it is BasicTactics.
func TestBasicTacticsUntilReportsTheAbandon(t *testing.T) {
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	// a ∧ b ⊢ b ∧ a: the conclusion splits, then each half closes.
	goal := MakeProp(b.And(a).Core(), a.And(b).Core())

	closed, abandoned := BasicTacticsUntil(context.Background(), goal)
	require.False(t, abandoned)
	require.NotNil(t, closed)
	assert.Equal(t, 0, closed.Size(), "the search runs to its fixpoint")

	done, cancel := context.WithCancel(context.Background())
	cancel()
	sg, abandoned := BasicTacticsUntil(done, goal)
	assert.True(t, abandoned, "past the deadline the search is abandoned, and says so")
	assert.Nil(t, sg)

	// Nothing applies to a ⊢ b: no step is taken, so no poll is reached
	// and the answer is "nothing applied" under a done context as well.
	inert := MakeProp(b.Core(), a.Core())
	sg, abandoned = BasicTacticsUntil(done, inert)
	assert.False(t, abandoned)
	assert.Nil(t, sg)
}

// withOpenLeafBackstop temporarily lowers the breadth backstop so tests
// can reach it with a handful of hypotheses.
func withOpenLeafBackstop(t *testing.T, n int) {
	t.Helper()
	saved := openLeafBackstop
	openLeafBackstop = n
	t.Cleanup(func() { openLeafBackstop = saved })
}

// iffHypGoal is r under k hypotheses Pᵢ(x) ⇔ Qᵢ(x) over distinct
// predicate variables (plus extra): k independent case splits whose
// sides no rule decides and no equation substitutes away (a ⇔ between
// bare Boolean variables is an equation Basic eliminates instead), so
// 2^k open leaves under HypIffTactic alone.
func iffHypGoal(k int, extra ...Term) Prop {
	hyps := make([]Term, 0, k+len(extra))
	x := Var("x", TypeA)
	pred := core.MakeFun(TypeA, TypeBool)
	for i := range k {
		p := Var(TermName(fmt.Sprintf("P%d", i)), pred).Apply(x).Core()
		q := Var(TermName(fmt.Sprintf("Q%d", i)), pred).Apply(x).Core()
		hyps = append(hyps, ext.Apply(core.IFF(), p, q))
	}
	hyps = append(hyps, extra...)
	return MakeProp(Var("r", TypeBool).Core(), hyps...)
}

// recordWhistleFires installs the tripwire hook for one test and
// returns the events it collected plus the fire count at install.
func recordWhistleFires(t *testing.T) (*[]skeleton.WhistleEvent, int64) {
	t.Helper()
	var events []skeleton.WhistleEvent
	skeleton.OnWhistleFire = func(ev skeleton.WhistleEvent) { events = append(events, ev) }
	t.Cleanup(func() { skeleton.OnWhistleFire = nil })
	return &events, skeleton.WhistleFires()
}

// Below the backstop a case analysis is complete and untouched: three
// independent equivalences fan into their eight open leaves, no fire.
func TestBreadthBackstopKeepsCompleteCaseAnalysis(t *testing.T) {
	withOpenLeafBackstop(t, 16)
	events, firesBefore := recordWhistleFires(t)

	s := mergeTactics(HypIffTactic)(iffHypGoal(3))
	require.NotNil(t, s)
	assert.Equal(t, 8, s.Size())
	assert.Equal(t, int64(0), skeleton.WhistleFires()-firesBefore)
	assert.Empty(t, *events)
}

// At the backstop the WHOLE expansion is refused — nil, not a partial
// fan — and the cut is reported through the whistle tripwire with the
// open-leaf count that reached the budget.
func TestBreadthBackstopRefusesTheWholeFan(t *testing.T) {
	const backstop = 16
	withOpenLeafBackstop(t, backstop)
	events, firesBefore := recordWhistleFires(t)

	s := mergeTactics(HypIffTactic)(iffHypGoal(5)) // 32 open leaves
	assert.Nil(t, s)
	assert.Equal(t, int64(1), skeleton.WhistleFires()-firesBefore)
	require.Len(t, *events, 1)
	ev := (*events)[0]
	assert.Equal(t, "mergeTactics", ev.Driver)
	assert.Equal(t, backstop, ev.Budget)
	assert.Equal(t, backstop, ev.Open)
	require.NotNil(t, ev.Goal)
}

// The refusal is local to the invocation that fanned: Basic's case-split
// component declines on a goal with too many equivalences, and Basic
// itself goes on with its non-branching simplifications — the ∧
// hypothesis is split into its conjuncts, the equivalences stay as
// spelled, one leaf comes back.
func TestBreadthBackstopIsLocalToTheInvocation(t *testing.T) {
	withOpenLeafBackstop(t, 16)
	_, firesBefore := recordWhistleFires(t)

	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	goal := iffHypGoal(5, a.And(b).Core())
	s := BasicTactics(goal)
	require.NotNil(t, s)
	require.Equal(t, 1, s.Size())
	leaf := s.ChildGoal(0)
	assert.True(t, leaf.HasHyp(a.Core()))
	assert.True(t, leaf.HasHyp(b.Core()))
	for i := range goal.NumHyps() {
		if _, _, ok := MatchesIFF(goal.Hyp(i)); ok {
			assert.True(t, leaf.HasHyp(goal.Hyp(i)), "equivalence %d must stay as spelled", i)
		}
	}
	assert.GreaterOrEqual(t, skeleton.WhistleFires()-firesBefore, int64(1))
}

// An inner refusal is not repeated within the outer invocation. The
// five equivalences make Basic's case-split component refuse at a
// backstop of 16; the chain of conjunction hypotheses gives Basic's
// non-branching simplifications several steps to take AFTER that, each
// yielding a child the split would be tried on again from the top.
// Before the driver remembered the refusal that was one whole fan per
// step — the serve-side `by` measured eight of them at open=512 in one
// attempt; now the component is skipped for the rest of the invocation
// and the fan is paid once. The leaf the outer hands back is the same
// either way: the refusals contributed nothing to it.
func TestBreadthBackstopRefusalIsNotRepeatedWithinTheInvocation(t *testing.T) {
	withOpenLeafBackstop(t, 16)
	events, firesBefore := recordWhistleFires(t)

	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	c := Var("c", TypeBool)
	d := Var("d", TypeBool)
	// a ∧ (b ∧ (c ∧ d)): three ∧-peelings, each a fresh child of the outer.
	goal := iffHypGoal(5, a.And(b.And(c.And(d))).Core())
	s := BasicTactics(goal)
	require.NotNil(t, s)
	require.Equal(t, 1, s.Size())
	leaf := s.ChildGoal(0)
	for _, h := range []Term{a.Core(), b.Core(), c.Core(), d.Core()} {
		assert.True(t, leaf.HasHyp(h), "the conjunction is fully peeled")
	}
	for i := range goal.NumHyps() {
		if _, _, ok := MatchesIFF(goal.Hyp(i)); ok {
			assert.True(t, leaf.HasHyp(goal.Hyp(i)), "equivalence %d stays as spelled", i)
		}
	}
	assert.Equal(t, int64(1), skeleton.WhistleFires()-firesBefore,
		"one refusal for the whole invocation, not one per simplification step")
	require.Len(t, *events, 1)
	assert.Equal(t, "mergeTactics", (*events)[0].Driver)
}

// TestStripQuantAtTactic pins the hyp-targeted ∃-elimination: the index
// names the hypothesis; the conclusion is left alone even when it is
// ∀-headed (the pick-first StripQuantTactic strips it before it looks
// at any hyp); the other ∃-hyp stands; a wrong-shape index and an
// out-of-range one decline with nil instead of opening some other hyp.
func TestStripQuantAtTactic(t *testing.T) {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	w := Var("w", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	H := Var("H", MakeFun(TypeA, TypeBool))
	D := Var("D", TypeBool).Core()
	exP := Exists(x)(P.Apply(x)).Core()
	exQ := Exists(y)(Q.Apply(y)).Core()
	concl := ForAll(w)(H.Apply(w)).Core()
	g := testProp(concl, exP, exQ, D)

	findHyp := func(g Prop, target Term) int {
		for i := range g.NumHyps() {
			if g.Hyp(i).AlphaEquals(target) {
				return i
			}
		}
		return -1
	}
	iP, iQ, iD := findHyp(g, exP), findHyp(g, exQ), findHyp(g, D)
	require.NotEqual(t, -1, iP)
	require.NotEqual(t, -1, iQ)
	require.NotEqual(t, -1, iD)

	// Pick-first: the ∀-conclusion goes and no hyp moves.
	sg := StripQuantTactic(g)
	require.NotNil(t, sg)
	require.Equal(t, 1, sg.Size())
	assert.True(t, ext.MatchesFORALL(sg.ChildGoal(0).Conclusion()).IsZero())
	assert.True(t, sg.ChildGoal(0).HasHyp(exP))
	assert.True(t, sg.ChildGoal(0).HasHyp(exQ))
	assertSubGoals(t, sg, g)

	// At iQ: ∃y. Q(y) is opened; ∃x. P(x) and the ∀-conclusion stand.
	sg = StripQuantAtTactic(g, iQ)
	require.NotNil(t, sg)
	require.Equal(t, 1, sg.Size())
	child := sg.ChildGoal(0)
	assert.True(t, child.Conclusion().AlphaEquals(concl),
		"a named ∃-hyp must not strip the conclusion; got %s", prop.PrintProp(child))
	assert.True(t, child.HasHyp(exP), "the other ∃-hyp must stand")
	assert.False(t, child.HasHyp(exQ), "the named ∃-hyp must be opened")
	assert.True(t, child.HasHyp(D))
	require.Equal(t, g.NumHyps(), child.NumHyps(), "one hyp replaced by its instance, nothing added or dropped")
	opened := 0
	for i := range child.NumHyps() {
		if h := child.Hyp(i); ext.MatchesEXISTS(h).IsZero() && !h.AlphaEquals(D) {
			opened++
		}
	}
	assert.Equal(t, 1, opened, "exactly one ∃-free instance hyp: %s", prop.PrintProp(child))
	assertSubGoals(t, sg, g)

	// Wrong shape at the index, and out of range → nil.
	assert.Nil(t, StripQuantAtTactic(g, iD),
		"a non-∃ hyp at the index must decline instead of opening a different hyp")
	assert.Nil(t, StripQuantAtTactic(g, -1))
	assert.Nil(t, StripQuantAtTactic(g, g.NumHyps()))
}

// A run's rule sets read one cache of normal forms: a second rule set of
// the run reads what the first computed. The unbounded mode is no run,
// and each of its rule sets reads for itself.
func TestSearchMode_ARunsRuleSetsShareItsNormalForms(t *testing.T) {
	defer goleak.VerifyNone(t)
	a := Var("a", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	target := ForAll(a)(ext.WrapTerm(P).Apply(a).Imply(ext.WrapTerm(Q).Apply(a))).Core()

	assert.Nil(t, fullSearch.normalForms)
	assert.NotSame(t, fullSearch.ruleCache().NormalizeTerm(target), fullSearch.ruleCache().NormalizeTerm(target))

	run := fullSearch.asRun()
	require.NotNil(t, run.normalForms)
	assert.Nil(t, fullSearch.normalForms, "the unbounded mode itself holds nothing")
	assert.Same(t, run.normalForms, run.asRun().normalForms, "a step of a run is that run")
	assert.Same(t, run.normalForms, run.unbounded().normalForms)
	assert.Same(t, run.ruleCache().NormalizeTerm(target), run.ruleCache().NormalizeTerm(target))

	bounded := boundedSearch(context.Background())
	probe := probeSearch(context.Background())
	require.NotNil(t, bounded.normalForms)
	require.NotNil(t, probe.normalForms)
	assert.NotSame(t, bounded.normalForms, probe.normalForms, "each search is a run of its own")
}

// An equality tactic of a run leaves the normal forms it read with the
// run, where the run's next call of it finds them.
func TestUnifyEqSimplifyUnder_KeepsItsNormalFormsWithTheRun(t *testing.T) {
	defer goleak.VerifyNone(t)
	a := ext.WrapTerm(Var("a", TypeA))
	b := ext.WrapTerm(Var("b", TypeA))
	c := ext.WrapTerm(Var("c", TypeA))
	f := ext.WrapTerm(Var("f", MakeFun(TypeA, TypeA)))
	P := ext.WrapTerm(Var("P", MakeFun(TypeA, TypeBool)))
	Q := ext.WrapTerm(Var("Q", MakeFun(TypeA, TypeBool)))

	// f(a) = b rewrites nothing in P(c) ⇒ Q(c), which is read in its
	// normal form for the retry.
	goal := testProp(F, f.Apply(a).Eq(b).Core(), P.Apply(c).Imply(Q.Apply(c)).Core())

	run := fullSearch.asRun()
	assert.Nil(t, unifyEqSimplifyUnder(run)(goal))
	held := run.normalForms.TermCacheSize()
	require.Positive(t, held)
	assert.Nil(t, unifyEqSimplifyUnder(run)(goal))
	assert.Equal(t, held, run.normalForms.TermCacheSize())
}
