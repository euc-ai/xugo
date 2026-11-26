package tactic

import (
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// specializeHypIdx locates the hyp α-equal to h in goal, failing the
// test if absent — hyp lists are canonically sorted by MakeProp, so
// tests must discover indices instead of hardcoding them.
func specializeHypIdx(t *testing.T, goal Prop, h Term) int {
	t.Helper()
	for i := range goal.NumHyps() {
		if goal.Hyp(i).AlphaEquals(h) {
			return i
		}
	}
	t.Fatalf("hyp not found in goal: %s", h)
	return -1
}

// TestSpecialize_BasicDrop pins the core shape: a 2-binder ∀-hyp
// grounded at [a, b] in ONE step — the subgoal carries the final
// instance R(a,b), NOT the intermediate partial ∀y.R(a,y), and the
// source ∀-hyp is consumed (default Lean `specialize` semantics).
func TestSpecialize_BasicDrop(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	q := Var("q", TypeBool)

	all := ForAll(x, y)(R.Apply(x, y)).Core()
	goal := testProp(q.Core(), all)
	idx := specializeHypIdx(t, goal, all)

	sg := SpecializeTactic([]SpecializeSpec{{HypIndex: idx, Witnesses: []Term{a.Core(), b.Core()}}}, false)(goal)
	require.NotNil(t, sg, "specialize must apply on a ∀∀-hyp")
	require.Equal(t, 1, sg.Size())

	child := sg.ChildGoal(0)
	assertPropAlphaEqual(t, child, testProp(q.Core(), R.Apply(a, b).Core()))
	assertSubGoals(t, sg, goal)
}

// TestSpecialize_KeepSources verifies keepSources=true leaves the
// grounded ∀-hyp in place alongside the new instance (the ematch
// contract: only ADD hyps).
func TestSpecialize_KeepSources(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	q := Var("q", TypeBool)

	all := ForAll(x, y)(R.Apply(x, y)).Core()
	goal := testProp(q.Core(), all)
	idx := specializeHypIdx(t, goal, all)

	sg := SpecializeTactic([]SpecializeSpec{{HypIndex: idx, Witnesses: []Term{a.Core(), b.Core()}}}, true)(goal)
	require.NotNil(t, sg)
	assertPropAlphaEqual(t, sg.ChildGoal(0), testProp(q.Core(), all, R.Apply(a, b).Core()))
	assertSubGoals(t, sg, goal)
}

// TestSpecialize_BatchSameSnapshot pins the atomic-set index
// convention: two entries ground two different ∀-hyps, both indices
// referring to the SAME input hyp list (no sequential shifting between
// entries).
func TestSpecialize_BatchSameSnapshot(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	q := Var("q", TypeBool)

	allP := ForAll(x)(P.Apply(x)).Core()
	allR := ForAll(x, y)(R.Apply(x, y)).Core()
	goal := testProp(q.Core(), allP, allR)

	sg := SpecializeTactic([]SpecializeSpec{
		{HypIndex: specializeHypIdx(t, goal, allP), Witnesses: []Term{a.Core()}},
		{HypIndex: specializeHypIdx(t, goal, allR), Witnesses: []Term{a.Core(), b.Core()}},
	}, false)(goal)
	require.NotNil(t, sg)
	assertPropAlphaEqual(t, sg.ChildGoal(0),
		testProp(q.Core(), P.Apply(a).Core(), R.Apply(a, b).Core()))
	assertSubGoals(t, sg, goal)
}

// TestSpecialize_SameHypMultipleTuples covers the ematch shape: one
// wide ∀-hyp grounded at TWO witness tuples in the same batch, source
// kept. Also exercises duplicate hyp indices with keepSources=false —
// the source must be dropped exactly once.
func TestSpecialize_SameHypMultipleTuples(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	q := Var("q", TypeBool)

	all := ForAll(x, y)(R.Apply(x, y)).Core()
	goal := testProp(q.Core(), all)
	idx := specializeHypIdx(t, goal, all)
	specs := []SpecializeSpec{
		{HypIndex: idx, Witnesses: []Term{a.Core(), b.Core()}},
		{HypIndex: idx, Witnesses: []Term{b.Core(), a.Core()}},
	}

	// keep: source + both instances.
	sgKeep := SpecializeTactic(specs, true)(goal)
	require.NotNil(t, sgKeep)
	assertPropAlphaEqual(t, sgKeep.ChildGoal(0),
		testProp(q.Core(), all, R.Apply(a, b).Core(), R.Apply(b, a).Core()))
	assertSubGoals(t, sgKeep, goal)

	// drop: both instances, source dropped once (duplicate index OK).
	sgDrop := SpecializeTactic(specs, false)(goal)
	require.NotNil(t, sgDrop)
	assertPropAlphaEqual(t, sgDrop.ChildGoal(0),
		testProp(q.Core(), R.Apply(a, b).Core(), R.Apply(b, a).Core()))
	assertSubGoals(t, sgDrop, goal)
}

// TestSpecialize_Inapplicable pins every nil-return guard: empty batch,
// empty witness list, index out of range, non-∀ hyp, binder-type
// mismatch, witness list deeper than the ∀-prefix, and the no-progress
// case (instance already resident, source kept).
func TestSpecialize_Inapplicable(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	z := Var("z", TypeB)
	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	q := Var("q", TypeBool)

	all := ForAll(x, y)(R.Apply(x, y)).Core()
	ground := R.Apply(a, a).Core()
	goal := testProp(q.Core(), all, ground)
	idx := specializeHypIdx(t, goal, all)
	groundIdx := specializeHypIdx(t, goal, ground)

	assert.Nil(t, SpecializeTactic(nil, false)(goal), "empty batch")
	assert.Nil(t, SpecializeTactic([]SpecializeSpec{{HypIndex: idx}}, false)(goal),
		"empty witness list")
	assert.Nil(t, SpecializeTactic([]SpecializeSpec{{HypIndex: goal.NumHyps(), Witnesses: []Term{a.Core()}}}, false)(goal),
		"index out of range")
	assert.Nil(t, SpecializeTactic([]SpecializeSpec{{HypIndex: groundIdx, Witnesses: []Term{a.Core()}}}, false)(goal),
		"non-∀ hyp")
	assert.Nil(t, SpecializeTactic([]SpecializeSpec{{HypIndex: idx, Witnesses: []Term{z.Core()}}}, false)(goal),
		"binder-type mismatch")
	assert.Nil(t, SpecializeTactic([]SpecializeSpec{{HypIndex: idx, Witnesses: []Term{a.Core(), b.Core(), a.Core()}}}, false)(goal),
		"witness list deeper than the ∀-prefix")

	// No progress: R(a,b) already resident, source kept → subgoal
	// α-equals the input.
	resident := testProp(q.Core(), all, R.Apply(a, b).Core())
	rIdx := specializeHypIdx(t, resident, all)
	assert.Nil(t, SpecializeTactic([]SpecializeSpec{{HypIndex: rIdx, Witnesses: []Term{a.Core(), b.Core()}}}, true)(resident),
		"instance already resident with keep → no progress")
}

// TestSpecialize_MatchesInstantiateAtChain verifies the composite's
// net effect equals the primitive chain it replaces: InstantiateAt per
// binder + ClearHyps of the source and intermediates.
func TestSpecialize_MatchesInstantiateAtChain(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	q := Var("q", TypeBool)

	all := ForAll(x, y)(R.Apply(x, y)).Core()
	goal := testProp(q.Core(), all)
	idx := specializeHypIdx(t, goal, all)

	// Composite.
	sg := SpecializeTactic([]SpecializeSpec{{HypIndex: idx, Witnesses: []Term{a.Core(), b.Core()}}}, false)(goal)
	require.NotNil(t, sg)

	// Primitive chain: instantiate at a, then at b (on the appended
	// partial), then clear source + partial.
	var cur Prop = goal
	sg1 := instantiateAt(cur, specializeHypIdx(t, cur, all), a.Core())
	require.NotNil(t, sg1)
	cur = sg1.ChildGoal(0)
	partial := ForAll(y)(R.Apply(a, y)).Core()
	sg2 := instantiateAt(cur, specializeHypIdx(t, cur, partial), b.Core())
	require.NotNil(t, sg2)
	cur = sg2.ChildGoal(0)
	sg3 := ClearHypsTactic([]int{
		specializeHypIdx(t, cur, all),
		specializeHypIdx(t, cur, partial),
	})(cur)
	require.NotNil(t, sg3)

	assertPropAlphaEqual(t, sg.ChildGoal(0), sg3.ChildGoal(0))
}

// TestSpecialize_ThroughGuard pins the guarded-lemma shape: a hyp that
// states its content behind an antecedent, `∀x. P(x) ⇒ ∀y. R(x, y)`,
// grounds at [a, b] in ONE step to the guarded instance
// `P(a) ⇒ R(a, b)` — the guard travels with the instance, the source is
// consumed, and the bridge is a kernel derivation (assume / demote /
// instantiate / promote), so reconstruction closes back to the input.
// A hyp whose implication has no ∀ below it stays inapplicable.
func TestSpecialize_ThroughGuard(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool)))
	q := Var("q", TypeBool)

	guarded := ForAll(x)(P.Apply(x).Imply(ForAll(y)(R.Apply(x, y)))).Core()
	goal := testProp(q.Core(), guarded)
	idx := specializeHypIdx(t, goal, guarded)

	sg := SpecializeTactic([]SpecializeSpec{{HypIndex: idx, Witnesses: []Term{a.Core(), b.Core()}}}, false)(goal)
	require.NotNil(t, sg, "specialize must reach the ∀ behind the guard")
	require.Equal(t, 1, sg.Size())
	want := P.Apply(a).Imply(R.Apply(a, b)).Core()
	assertPropAlphaEqual(t, sg.ChildGoal(0), testProp(q.Core(), want))
	assertSubGoals(t, sg, goal)

	// Two guards in a row, and a witness list that stops at the first
	// binder: the partial instance keeps the inner guard and ∀.
	inner := ForAll(y)(R.Apply(x, y))
	twoGuards := ForAll(x)(P.Apply(x).Imply(P.Apply(a).Imply(inner))).Core()
	goal2 := testProp(q.Core(), twoGuards)
	idx2 := specializeHypIdx(t, goal2, twoGuards)
	sg2 := SpecializeTactic([]SpecializeSpec{{HypIndex: idx2, Witnesses: []Term{a.Core(), b.Core()}}}, true)(goal2)
	require.NotNil(t, sg2)
	want2 := P.Apply(a).Imply(P.Apply(a).Imply(R.Apply(a, b))).Core()
	assertPropAlphaEqual(t, sg2.ChildGoal(0), testProp(q.Core(), twoGuards, want2))
	assertSubGoals(t, sg2, goal2)

	// A guard with nothing quantified below it is not a binder.
	flat := ForAll(x)(P.Apply(x).Imply(R.Apply(x, x))).Core()
	goal3 := testProp(q.Core(), flat)
	idx3 := specializeHypIdx(t, goal3, flat)
	assert.Nil(t, SpecializeTactic([]SpecializeSpec{{HypIndex: idx3, Witnesses: []Term{a.Core(), b.Core()}}}, false)(goal3),
		"the second witness has no ∀ to reach")
}
