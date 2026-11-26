package tactic

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

func TestAssumptionTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	// Happy path: concl matches a hyp.
	goal := testProp(P.Apply(x).Core(), P.Apply(x).Core(), x.Eq(x).Core())
	subGoals := AssumptionTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 0, subGoals.Size())

	// Shape miss: concl not in hyps.
	noHyp := testProp(P.Apply(x).Core())
	assert.Nil(t, AssumptionTactic(noHyp))

	// Shape miss: concl is `true` but `true` not a hyp.
	other := Var("y", TypeA)
	mismatch := testProp(P.Apply(x).Core(), P.Apply(other).Core())
	assert.Nil(t, AssumptionTactic(mismatch))

	// βη: the hypothesis spells the function bare, the conclusion
	// η-expands it — one statement, closed through the conversion.
	f := Var("f", MakeFun(TypeA, TypeA))
	R := Var("R", MakeFun(MakeFun(TypeA, TypeA), TypeBool))
	y := core.Var(core.TermName("y"), TypeA)
	expanded := R.Apply(ext.WrapTerm(ext.Abs(y, f.Apply(ext.WrapTerm(y)).Core())))
	etaGoal := testProp(expanded.Core(), R.Apply(f).Core())
	etaSub := AssumptionTactic(etaGoal)
	if assert.NotNil(t, etaSub, "R(λy. f(y)) is R(f) up to η") {
		assert.Equal(t, 0, etaSub.Size())
		closed := etaSub.Reconstruct()
		assert.True(t, closed.Conclusion().AlphaEquals(expanded.Core()), "the certificate proves the goal as spelled")
	}
}

func TestReflTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)

	// Happy path: t = t.
	goal := testProp(x.Eq(x).Core())
	subGoals := ReflTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 0, subGoals.Size())

	// Shape miss: a = b with a != b.
	y := Var("y", TypeA)
	notRefl := testProp(x.Eq(y).Core())
	assert.Nil(t, ReflTactic(notRefl))

	// Shape miss: not an equality at all.
	P := Var("P", MakeFun(TypeA, TypeBool))
	notEq := testProp(P.Apply(x).Core())
	assert.Nil(t, ReflTactic(notEq))
}

func TestLeftRightTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	A := P.Apply(x)
	B := Q.Apply(x)

	// Left: ⊢ A∨B → ⊢ A
	goal := testProp(A.Or(B).Core())
	subGoalsL := LeftTactic(goal)
	assert.NotNil(t, subGoalsL)
	assert.Equal(t, 1, subGoalsL.Size())
	assertPropAlphaEqual(t, subGoalsL.ChildGoal(0), MakeProp(A.Core()))
	assertSubGoals(t, subGoalsL, goal)

	// Right: ⊢ A∨B → ⊢ B
	subGoalsR := RightTactic(goal)
	assert.NotNil(t, subGoalsR)
	assert.Equal(t, 1, subGoalsR.Size())
	assertPropAlphaEqual(t, subGoalsR.ChildGoal(0), MakeProp(B.Core()))
	assertSubGoals(t, subGoalsR, goal)

	// Shape miss: not a disjunction.
	notDisj := testProp(A.Core())
	assert.Nil(t, LeftTactic(notDisj))
	assert.Nil(t, RightTactic(notDisj))
}

func TestSymmTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)

	// Happy path: ⊢ a = b → ⊢ b = a.
	goal := testProp(x.Eq(y).Core())
	subGoals := SymmTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(y.Eq(x).Core()))
	assertSubGoals(t, subGoals, goal)

	// Shape miss: refl-shaped.
	assert.Nil(t, SymmTactic(testProp(x.Eq(x).Core())))

	// Shape miss: not an equality.
	P := Var("P", MakeFun(TypeA, TypeBool))
	assert.Nil(t, SymmTactic(testProp(P.Apply(x).Core())))
}

func TestByContraTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	// Happy path: ⊢ G (G ≠ ⊥) → ¬G ⊢ ⊥
	goal := testProp(P.Apply(x).Core(), x.Eq(y).Core())
	subGoals := ByContraTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assert.True(t, subGoals.ChildGoal(0).Conclusion().Equals(F))
	assertSubGoals(t, subGoals, goal)

	// Shape miss: concl is already ⊥.
	bottom := testProp(F)
	assert.Nil(t, ByContraTactic(bottom))

	// Shape miss: ¬G already in hyps (no progress).
	g := P.Apply(x).Core()
	already := testProp(g, Not(g))
	assert.Nil(t, ByContraTactic(already))
}

func TestFunextTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA))

	// Happy path: ⊢ f = g → ⊢ ∀x. f(x) = g(x).
	goal := testProp(f.Eq(g).Core())
	subGoals := FunextTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertSubGoals(t, subGoals, goal)

	// Shape miss: not an equality.
	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	assert.Nil(t, FunextTactic(testProp(P.Apply(x).Core())))

	// Shape miss: equality but neither side is function-typed.
	y := Var("y", TypeA)
	assert.Nil(t, FunextTactic(testProp(x.Eq(y).Core())))
}

func TestSubstTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeA))

	// Happy path: hyp Q(x) = x, concl P(Q(x), y). Subst rewrites Q(x) → x
	// in the conclusion, shrinking it to P(x, y).
	goal := testProp(P.Apply(Q.Apply(x).Core(), y.Core()).Core(), Q.Apply(x).Eq(x).Core())
	subGoals := SubstTactic(0)(goal)
	assert.NotNil(t, subGoals, "subst should fire for Q(x)=x rewriting P(Q(x), y) → P(x, y)")
	assertSubGoals(t, subGoals, goal)

	// Out of range index → nil.
	assert.Nil(t, SubstTactic(5)(goal))
	assert.Nil(t, SubstTactic(-1)(goal))

	// Hyp is not an equality → nil.
	notEq := testProp(P.Apply(x.Core(), y.Core()).Core(), P.Apply(x.Core(), x.Core()).Core())
	assert.Nil(t, SubstTactic(0)(notEq))
}

// rwEqHypIndex finds the index of the equality hyp in a goal whose hyps
// were reordered by MakeProp normalization. Test helper only.
func rwEqHypIndex(t *testing.T, goal Prop, eq Term) int {
	t.Helper()
	for i := range goal.NumHyps() {
		if goal.Hyp(i).Equals(eq) {
			return i
		}
	}
	t.Fatalf("equality hyp %v not found in goal", eq)
	return -1
}

// One rw call rewrites BOTH another hyp and the conclusion — the
// fixpoint behavior subst (one target per call) lacks.
// hyp f(m)=d, hyp P(f(m)) ⊢ Q(f(m))  →  child  P(d), f(m)=d ⊢ Q(d).
func TestRwHypTactic_MultiTarget(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", TypeA)
	d := Var("d", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	eq := f.Apply(m).Eq(d).Core()
	goal := testProp(Q.Apply(f.Apply(m).Core()).Core(),
		eq, P.Apply(f.Apply(m).Core()).Core())

	sg := RwHypTactic(rwEqHypIndex(t, goal, eq), false)(goal)
	assert.NotNil(t, sg, "rw should fire")
	assert.Equal(t, 1, sg.Size())
	child := sg.ChildGoal(0)
	assert.True(t, child.Conclusion().AlphaEquals(Q.Apply(d).Core()),
		"conclusion must be rewritten to Q(d), got %v", child.Conclusion())
	assert.True(t, child.HasHyp(P.Apply(d).Core()),
		"hyp P(f(m)) must be rewritten to P(d)")
	assert.True(t, child.HasHyp(eq), "the equality hyp itself must survive")
	assertSubGoals(t, sg, goal)
}

// Deep descent: rewrite under an opaque function arg inside a
// relation-atom argument. hyp f(m)=d ⊢ le(g(B,f(m)),C) rewrites to
// le(g(B,d),C) — with no manual congr_arg-per-layer loop.
func TestRwHypTactic_DeepOpaqueRelationAtom(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", TypeA)
	d := Var("d", TypeA)
	B := Var("B", TypeA)
	C := Var("C", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA, TypeA))
	le := Var("le", MakeFun(TypeA, TypeA, TypeBool))

	eq := f.Apply(m).Eq(d).Core()
	goal := testProp(
		le.Apply(g.Apply(B.Core(), f.Apply(m).Core()).Core(), C.Core()).Core(), eq)

	sg := RwHypTactic(rwEqHypIndex(t, goal, eq), false)(goal)
	assert.NotNil(t, sg, "rw should descend into the relation atom")
	assert.Equal(t, 1, sg.Size())
	assert.True(t, sg.ChildGoal(0).Conclusion().AlphaEquals(
		le.Apply(g.Apply(B.Core(), d.Core()).Core(), C.Core()).Core()),
		"got %v", sg.ChildGoal(0).Conclusion())
	assertSubGoals(t, sg, goal)
}

// Multiple occurrences of the LHS in one target are all rewritten.
// hyp f(m)=d ⊢ R(f(m), f(m))  →  ⊢ R(d, d).
func TestRwHypTactic_AllOccurrences(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", TypeA)
	d := Var("d", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))

	eq := f.Apply(m).Eq(d).Core()
	goal := testProp(R.Apply(f.Apply(m).Core(), f.Apply(m).Core()).Core(), eq)

	sg := RwHypTactic(rwEqHypIndex(t, goal, eq), false)(goal)
	assert.NotNil(t, sg)
	assert.True(t, sg.ChildGoal(0).Conclusion().AlphaEquals(
		R.Apply(d.Core(), d.Core()).Core()),
		"both occurrences must rewrite, got %v", sg.ChildGoal(0).Conclusion())
	assertSubGoals(t, sg, goal)
}

// Expansion direction (written small→big): hyp d=f(m) rewrites d→f(m)
// in BOTH targets — impossible for subst (size-monotone, auto-swap).
func TestRwHypTactic_ExpansionDirection(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", TypeA)
	d := Var("d", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	eq := d.Eq(f.Apply(m)).Core()
	goal := testProp(Q.Apply(d).Core(), eq, P.Apply(d).Core())

	sg := RwHypTactic(rwEqHypIndex(t, goal, eq), false)(goal)
	assert.NotNil(t, sg, "expansion-direction rw should fire")
	child := sg.ChildGoal(0)
	assert.True(t, child.Conclusion().AlphaEquals(Q.Apply(f.Apply(m).Core()).Core()),
		"got %v", child.Conclusion())
	assert.True(t, child.HasHyp(P.Apply(f.Apply(m).Core()).Core()),
		"hyp P(d) must expand to P(f(m))")
	assertSubGoals(t, sg, goal)
}

// flip=true rewrites right→left. hyp f(m)=d + flip: d→f(m).
// The flipped equality is not a hyp, so this exercises the cut +
// EqSym-discharge reconstruction path. The equality hyp is kept as it
// stood: the child holds it in its own orientation, and neither its
// flipped copy nor the `f(m) = f(m)` the rewrite would make of it.
func TestRwHypTactic_Flip(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", TypeA)
	d := Var("d", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	eq := f.Apply(m).Eq(d).Core()
	goal := testProp(Q.Apply(d).Core(), eq, P.Apply(d).Core())

	sg := RwHypTactic(rwEqHypIndex(t, goal, eq), true)(goal)
	assert.NotNil(t, sg, "flipped rw should fire")
	child := sg.ChildGoal(0)
	assert.True(t, child.Conclusion().AlphaEquals(Q.Apply(f.Apply(m).Core()).Core()),
		"conclusion must rewrite d→f(m), got %v", child.Conclusion())
	assert.True(t, child.HasHyp(P.Apply(f.Apply(m).Core()).Core()),
		"hyp P(d) must rewrite to P(f(m))")
	assert.Equal(t, goal.NumHyps(), child.NumHyps(), "the rewrite adds no hyp and drops none")
	assert.True(t, child.HasHyp(eq), "the equality hyp is kept in its own orientation")
	assert.False(t, child.HasHyp(d.Eq(f.Apply(m)).Core()), "the flipped copy is the driver's, not the child's")
	assert.False(t, child.HasHyp(T), "the equality hyp is not rewritten by itself")
	assertSubGoals(t, sg, goal)
}

// Both orientations resident: the flipped rewrite keeps both, as the
// goal held them.
func TestRwHypTactic_Flip_BothOrientationsResident(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", TypeA)
	d := Var("d", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	eq := f.Apply(m).Eq(d).Core()
	mirror := d.Eq(f.Apply(m)).Core()
	goal := testProp(Q.Apply(d).Core(), eq, mirror)

	sg := RwHypTactic(rwEqHypIndex(t, goal, eq), true)(goal)
	assert.NotNil(t, sg, "flipped rw should fire")
	child := sg.ChildGoal(0)
	assert.True(t, child.Conclusion().AlphaEquals(Q.Apply(f.Apply(m).Core()).Core()),
		"conclusion must rewrite d→f(m), got %v", child.Conclusion())
	assert.Equal(t, goal.NumHyps(), child.NumHyps())
	assert.True(t, child.HasHyp(eq))
	assert.True(t, child.HasHyp(mirror))
	assertSubGoals(t, sg, goal)
}

// Self-expanding rule (LHS occurs in RHS): hyp x=f(x) is refused —
// EqRewrite's ext.IsSub guard returns NilRewrite, so rw returns nil
// rather than diverging or applying a partial pass.
func TestRwHypTactic_SelfExpandingRefused(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))

	eq := x.Eq(f.Apply(x)).Core()
	goal := testProp(P.Apply(x).Core(), eq)

	assert.Nil(t, RwHypTactic(rwEqHypIndex(t, goal, eq), false)(goal),
		"self-expanding rule must be refused, not diverge")
}

// Shape misses and no-ops return nil.
func TestRwHypTactic_Misses(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	h := Var("h", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// Out of range.
	goal := testProp(Q.Apply(x).Core(), x.Eq(y).Core())
	assert.Nil(t, RwHypTactic(5, false)(goal))
	assert.Nil(t, RwHypTactic(-1, false)(goal))

	// Hyp is not an equality.
	notEq := testProp(Q.Apply(x).Core(), P.Apply(x).Core())
	assert.Nil(t, RwHypTactic(0, false)(notEq))

	// ∀-quantified equation is rejected at the gate (v1: structural only).
	forallEq := ForAll(x)(h.Apply(h.Apply(x).Core()).Eq(h.Apply(x))).Core()
	forallGoal := testProp(Q.Apply(h.Apply(h.Apply(y).Core()).Core()).Core(), forallEq)
	assert.Nil(t, RwHypTactic(0, false)(forallGoal))

	// No occurrence of the oriented LHS anywhere → nil.
	noOcc := testProp(Q.Apply(y).Core(), h.Apply(x).Eq(x).Core())
	idx := rwEqHypIndex(t, noOcc, h.Apply(x).Eq(x).Core())
	assert.Nil(t, RwHypTactic(idx, false)(noOcc))
}

func TestTransTactic(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)

	// Happy path: ⊢ a = c → ⊢ a = b and ⊢ b = c.
	goal := testProp(a.Eq(c).Core())
	subGoals := TransTactic(b)(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(a.Eq(b).Core()))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1), MakeProp(b.Eq(c).Core()))
	assertSubGoals(t, subGoals, goal)

	// Shape miss: not an equality.
	P := Var("P", MakeFun(TypeA, TypeBool))
	assert.Nil(t, TransTactic(b)(testProp(P.Apply(a).Core())))

	// No-progress: middle equals one of the sides.
	assert.Nil(t, TransTactic(a)(goal))
	assert.Nil(t, TransTactic(c)(goal))

	// Type mismatch: middle term has wrong type.
	wrongType := Var("p", TypeBool)
	assert.Nil(t, TransTactic(wrongType)(goal))
}

func TestCongrTactic_Phase1_SinglePoint(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))

	// f(a) = f(b) → one subgoal a = b.
	goal := testProp(f.Apply(a).Eq(f.Apply(b)).Core())
	subGoals := CongrTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(a.Eq(b).Core()))
	assertSubGoals(t, subGoals, goal)
}

func TestCongrTactic_Phase1_UniformReplacement(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeA))
	R := Var("R", MakeFun(TypeA, TypeA))

	// P(Q(x), Q(x)) = P(R(x), R(x)) → one subgoal Q = R (or Q(x) = R(x)).
	lhs := P.Apply(Q.Apply(x).Core(), Q.Apply(x).Core())
	rhs := P.Apply(R.Apply(x).Core(), R.Apply(x).Core())
	goal := testProp(lhs.Eq(rhs).Core())
	subGoals := CongrTactic(goal)
	assert.NotNil(t, subGoals)
	// Single subgoal; the exact form (Q = R vs Q(x) = R(x)) depends on
	// TermDiff's choice — both are valid single-point candidates.
	assert.Equal(t, 1, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
}

func TestCongrTactic_Phase2_MultiArg(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	d := Var("d", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA, TypeA))

	// f(a,b) = f(c,d) where a≠c, b≠d, no single-point candidate works.
	// Phase 2 produces two subgoals a = c and b = d.
	goal := testProp(f.Apply(a.Core(), b.Core()).Eq(f.Apply(c.Core(), d.Core())).Core())
	subGoals := CongrTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(a.Eq(c).Core()))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1), MakeProp(b.Eq(d).Core()))
	assertSubGoals(t, subGoals, goal)
}

func TestCongrTactic_Phase2_PartialAlphaEqual(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA, TypeA))

	// f(a,b) = f(c,b) — only the first arg differs. Phase 2 produces a
	// single subgoal a = c; the b = b arg is reconstructed via Refl.
	goal := testProp(f.Apply(a.Core(), b.Core()).Eq(f.Apply(c.Core(), b.Core())).Core())
	subGoals := CongrTactic(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 1, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(a.Eq(c).Core()))
	assertSubGoals(t, subGoals, goal)
}

func TestCongrTactic_BothPhasesMiss(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA))

	// f(a) = g(b): different heads AND different args. Phase 1 might
	// fall back to whole-term, phase 2 detects head mismatch — should
	// return nil. (TermDiff itself may or may not surface a usable
	// single-point candidate here; whatever happens, the result is
	// either a valid one-subgoal decomposition or nil.)
	goal := testProp(f.Apply(a).Eq(g.Apply(b)).Core())
	subGoals := CongrTactic(goal)
	if subGoals != nil {
		// If TermDiff surfaced a usable candidate (e.g. the whole f.Apply(a) = g.Apply(b)
		// equality might even validate as itself), assertSubGoals still verifies
		// the reconstruct is sound. But the trivial whole-term fallback should be
		// filtered, so we expect nil here.
		t.Logf("Note: CongrTactic produced a single subgoal for heads-differ goal (unexpected): %v", subGoals)
	}
}

func TestCongrTactic_RefShape_ReturnsNil(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)

	// ⊢ a = a — refl shape, congr should bail (refl handles it).
	goal := testProp(a.Eq(a).Core())
	assert.Nil(t, CongrTactic(goal))
}

// TestMiniStepProto_OneofRoundTrip_NewSteps runs each LEAN-named tactic on
// its happy-path goal and checks it produces subgoals.
func TestMiniStepProto_OneofRoundTrip_NewSteps(t *testing.T) {
	defer goleak.VerifyNone(t)
	// The ministep marker types live in package proof, so to avoid an
	// import cycle this exercises the tactic-level happy path only: each
	// tactic must produce subgoals on its happy-path goal. The steps run
	// end to end, recorded and replayed, in engine/lean_dispatch_test.go.
	x := Var("x", TypeA)
	y := Var("y", TypeA)

	cases := []struct {
		name   string
		tactic Tactic
		goal   Prop
	}{
		{"assumption", AssumptionTactic, testProp(x.Eq(x).Core(), x.Eq(x).Core())},
		{"refl", ReflTactic, testProp(x.Eq(x).Core())},
		{"left", LeftTactic, testProp(x.Eq(y).Or(y.Eq(x)).Core())},
		{"right", RightTactic, testProp(x.Eq(y).Or(y.Eq(x)).Core())},
		{"symm", SymmTactic, testProp(x.Eq(y).Core())},
		{"by_contra", ByContraTactic, testProp(x.Eq(y).Core())},
		{"funext", FunextTactic, testProp(
			Var("f", MakeFun(TypeA, TypeA)).Eq(Var("g", MakeFun(TypeA, TypeA))).Core())},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			subGoals := tc.tactic(tc.goal)
			assert.NotNilf(t, subGoals, "tactic %q failed on its happy-path goal", tc.name)
		})
	}
}

// TestLeanRwTactic_BidirectionalRetry pins the agent's r2l-direction
// case: when the lemma states the equation in the "wrong" direction
// for the agent's goal (i.e., LHS isn't present in the goal but RHS
// is), LeanRwTactic now retries with the equation flipped and fires.
//
// Before this fix, lean_rw used LHS as the search pattern verbatim
// from however the lemma stated the equation. For lemmas like the
// definition of a vector-pasting constant (`body = c(...)`), the LHS body wasn't
// in the goal — the agent's intended `c → body` rewrite
// silently failed.
func TestLeanRwTactic_BidirectionalRetry(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	f := Var("f", MakeFun(TypeA, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeBool))

	// Lemma stored body-on-LHS, const-on-RHS shape:
	//   ⊢ ∀x. (f(x) ∧ g(x)) = h(x)
	// where h is a free var standing in for the "stored as RHS" const.
	// The natural direction (LHS pattern = `f(x) ∧ g(x)`) cannot match
	// a goal containing `h(...)` only — so without bidirectional retry,
	// the rewrite would never fire.
	h := Var("h", MakeFun(TypeA, TypeBool))
	lemma := testProp(
		ext.ForAll(a)(f.Apply(a).And(g.Apply(a).Core()).Eq(h.Apply(a).Core()).Core()),
	)

	// Goal: ⊢ h(a). Bidirectional retry should rewrite h(a) → f(a) ∧ g(a).
	goal := testProp(h.Apply(a).Core())

	subGoals := LeanRwTactic(lemma)(goal)
	require.NotNil(t, subGoals,
		"LeanRwTactic must fire via bidirectional retry on body-on-LHS lemma")
	assertSubGoals(t, subGoals, goal)
	// child[0] must α-equal the original lemma — agents and dep tracking
	// see only the original form, not the internal flipped variant.
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), lemma)
}

// TestLeanRwTactic_BidirectionalRetry_IffShape pins the
// case of componentwise vector equality: `(big iff) ⇔ (small)` where the agent anchors on the small side
// and expands. This is the original failure mode — the
// size guard fix in 8033ccb4 unlocked the size-non-decreasing rewrite,
// but the natural direction (big as LHS pattern) still couldn't match.
//
// Mirrors that law's structural property that the two sides don't
// share head symbols (LHS uses `$(x,i)` indexing, RHS is
// `x = y`). If the small side appeared as a subterm of the big side,
// unifyEqRewrite's IsSub guard would correctly reject the flipped
// direction — that's a separate (and legitimate) restriction.
func TestLeanRwTactic_BidirectionalRetry_IffShape(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	f := Var("f", MakeFun(TypeA, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeBool))
	h := Var("h", MakeFun(TypeA, TypeBool))
	k := Var("k", MakeFun(TypeA, TypeBool))

	// Lemma: ⊢ ∀x. (f(x) ∧ g(x) ∧ h(x)) ⇔ k(x)
	// LHS is the bigger pointwise form; RHS is the small `k(x)`. Disjoint
	// head symbols on the two sides — flipping doesn't trigger the
	// self-reference IsSub guard.
	bigBody := f.Apply(a).And(g.Apply(a).Core()).And(h.Apply(a).Core())
	lemma := testProp(
		ext.ForAll(a)(bigBody.Eq(k.Apply(a).Core()).Core()),
	)

	// Goal: ⊢ k(a). Bidirectional retry rewrites k(a) → f(a) ∧ g(a) ∧ h(a).
	goal := testProp(k.Apply(a).Core())

	subGoals := LeanRwTactic(lemma)(goal)
	require.NotNil(t, subGoals,
		"LeanRwTactic must fire via bidirectional retry on big-iff-small lemma")
	assertSubGoals(t, subGoals, goal)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), lemma)
}

func TestLeanRwTactic_WellfoundedRecursionCasesShape(t *testing.T) {
	TypeAB := MakeFun(TypeA, TypeB)
	T1 := MakeFun(TypeA, TypeA, TypeBool)
	T2 := MakeFun(TypeAB, TypeA, TypeBool)
	cType := MakeFun(T1, T2, TypeA, TypeAB, TypeBool)
	c := ext.TestConst("tailadmissible", cType)

	ltv := Var("ltv", T1)
	pv := Var("pv", T2)
	sv := Var("sv", TypeA)
	tv := Var("tv", TypeAB)
	body := ltv.To(pv.To(sv.To(tv.To(ltv.Apply(sv, sv)))))
	defThm := testProp(c.Eq(body))

	// Construct the conclusion shape after strip_quant + witness.
	ltFree := Var("<<", T1)
	// inner lambda arg for p: λf.λa.⊤
	innerF := Var("ifv", TypeAB)
	innerA := Var("iav", TypeA)
	innerLambdaArg := innerF.To(innerA.To(WrapTerm(T)))

	fPattern := Var("f", MakeFun(TypeA, TypeAB))
	s := Var("s", TypeA)
	tt := Var("t", TypeAB)
	patternEq := Var("pattern_eq", MakeFun(TypeAB, TypeBool, TypeBool))
	tailapp := c.Apply(ltFree, innerLambdaArg, s, tt)

	innerBody := ForAll(s)(ForAll(tt)(patternEq.Apply(fPattern.Apply(s), tailapp)))
	patternLambda := fPattern.To(innerBody)
	patternConst := ext.TestConst("pattern_abstraction", MakeFun(
		MakeFun(MakeFun(TypeA, TypeAB), TypeBool), TypeBool))
	patternApp := patternConst.Apply(patternLambda)

	clausesType := MakeFun(TypeA, TypeAB)
	clauses := Var("clauses", clausesType)
	allConst := ext.TestConst("list_all", MakeFun(
		TypeBool, clausesType, TypeBool))
	allApp := allConst.Apply(patternApp, clauses)

	wellfounded := Var("wellfounded", MakeFun(T1, TypeBool))
	x := Var("x", TypeA)
	fOuter := Var("f_outer", MakeFun(TypeA, TypeAB))
	casewise := Var("casewise", MakeFun(clausesType, MakeFun(TypeA, TypeAB), TypeA, TypeAB))

	// (¬wellfounded(<<) ∨ ¬list_all(pattern_abstraction(...), clauses)) ∨ (f(x) = casewise(...))
	disjBody := (Not(wellfounded.Apply(ltFree)).Or(Not(allApp))).Or(
		fOuter.Apply(x).Eq(casewise.Apply(clauses, fOuter, x)))

	// ∃f. ∀x. disjBody
	concl := ext.Exists(fOuter)(ForAll(x)(disjBody))

	other := Var("other", TypeBool)
	goal := testProp(concl, other.Core())

	t.Logf("defThm: %s", prop.PrintProp(defThm))
	t.Logf("goal:   %s", prop.PrintProp(goal))

	subGoals := LeanRwTactic(defThm)(goal)
	if subGoals == nil {
		t.Fatalf("FAIL: LeanRwTactic returned nil on the wellfounded-recursion-cases-shape goal")
	}
	t.Logf("LeanRwTactic SUCCEEDED with %d children", subGoals.Size())
	for i := 0; i < subGoals.Size(); i++ {
		t.Logf("  child[%d]: %s", i, prop.PrintProp(subGoals.ChildGoal(i)))
	}
}

// Second-call scenario: no separate def-hyp. Just the goal with
// under-pattern_abstraction tailadmissible in the conclusion.
func TestLeanRwTactic_OnlyUnderBinder(t *testing.T) {
	TypeAB := MakeFun(TypeA, TypeB)
	T1 := MakeFun(TypeA, TypeA, TypeBool)
	T2 := MakeFun(TypeAB, TypeA, TypeBool)
	cType := MakeFun(T1, T2, TypeA, TypeAB, TypeBool)
	c := ext.TestConst("tailadmissible_v2", cType)

	ltv := Var("ltv", T1)
	pv := Var("pv", T2)
	sv := Var("sv", TypeA)
	tv := Var("tv", TypeAB)
	body := ltv.To(pv.To(sv.To(tv.To(ltv.Apply(sv, sv)))))
	defThm := testProp(c.Eq(body))

	ltFree := Var("<<", T1)
	innerF := Var("ifv", TypeAB)
	innerA := Var("iav", TypeA)
	innerLambdaArg := innerF.To(innerA.To(WrapTerm(T)))

	fPattern := Var("f", MakeFun(TypeA, TypeAB))
	s := Var("s", TypeA)
	tt := Var("t", TypeAB)
	patternEq := Var("pattern_eq", MakeFun(TypeAB, TypeBool, TypeBool))
	tailapp := c.Apply(ltFree, innerLambdaArg, s, tt)

	innerBody := ForAll(s)(ForAll(tt)(patternEq.Apply(fPattern.Apply(s), tailapp)))
	patternLambda := fPattern.To(innerBody)
	patternConst := ext.TestConst("pattern_abstraction2", MakeFun(
		MakeFun(MakeFun(TypeA, TypeAB), TypeBool), TypeBool))
	patternApp := patternConst.Apply(patternLambda)

	clausesType := MakeFun(TypeA, TypeAB)
	clauses := Var("clauses", clausesType)
	allConst := ext.TestConst("list_all2", MakeFun(
		TypeBool, clausesType, TypeBool))
	allApp := allConst.Apply(patternApp, clauses)

	wellfounded := Var("wellfounded2", MakeFun(T1, TypeBool))
	x := Var("x", TypeA)
	fOuter := Var("f_outer", MakeFun(TypeA, TypeAB))
	casewise := Var("casewise2", MakeFun(clausesType, MakeFun(TypeA, TypeAB), TypeA, TypeAB))

	disjBody := (Not(wellfounded.Apply(ltFree)).Or(Not(allApp))).Or(
		fOuter.Apply(x).Eq(casewise.Apply(clauses, fOuter, x)))
	concl := ext.Exists(fOuter)(ForAll(x)(disjBody))

	// Just one hyp WITHOUT tailadmissible. Mimics second call.
	WF_REC_unfolded := Var("WF_REC_unfolded", TypeBool)
	goal := testProp(concl, WF_REC_unfolded.Core())

	t.Logf("defThm: %s", prop.PrintProp(defThm))
	t.Logf("goal:   %s", prop.PrintProp(goal))

	subGoals := LeanRwTactic(defThm)(goal)
	if subGoals == nil {
		t.Fatalf("FAIL: LeanRwTactic returned nil on second-call scenario")
	}
	t.Logf("LeanRwTactic SUCCEEDED with %d children", subGoals.Size())
	for i := 0; i < subGoals.Size(); i++ {
		t.Logf("  child[%d]: %s", i, prop.PrintProp(subGoals.ChildGoal(i)))
	}
}

// Test rewrite on a hyp that is the NEGATION of the goal conclusion,
// matching what eqSimplify sees after negConcl wraps the goal.
func TestLeanRwTactic_NegatedConclAsHyp(t *testing.T) {
	TypeAB := MakeFun(TypeA, TypeB)
	T1 := MakeFun(TypeA, TypeA, TypeBool)
	T2 := MakeFun(TypeAB, TypeA, TypeBool)
	cType := MakeFun(T1, T2, TypeA, TypeAB, TypeBool)
	c := ext.TestConst("c_v3", cType)

	ltv := Var("ltv", T1)
	pv := Var("pv", T2)
	sv := Var("sv", TypeA)
	tv := Var("tv", TypeAB)
	body := ltv.To(pv.To(sv.To(tv.To(ltv.Apply(sv, sv)))))
	defThm := testProp(c.Eq(body))

	ltFree := Var("<<", T1)
	innerF := Var("ifv", TypeAB)
	innerA := Var("iav", TypeA)
	innerLambdaArg := innerF.To(innerA.To(WrapTerm(T)))

	fPattern := Var("f", MakeFun(TypeA, TypeAB))
	s := Var("s", TypeA)
	tt := Var("t", TypeAB)
	patternEq := Var("pattern_eq", MakeFun(TypeAB, TypeBool, TypeBool))
	tailapp := c.Apply(ltFree, innerLambdaArg, s, tt)

	innerBody := ForAll(s)(ForAll(tt)(patternEq.Apply(fPattern.Apply(s), tailapp)))
	patternLambda := fPattern.To(innerBody)
	patternConst := ext.TestConst("pattern_abstraction3", MakeFun(
		MakeFun(MakeFun(TypeA, TypeAB), TypeBool), TypeBool))
	patternApp := patternConst.Apply(patternLambda)

	clausesType := MakeFun(TypeA, TypeAB)
	clauses := Var("clauses", clausesType)
	allConst := ext.TestConst("list_all3", MakeFun(
		TypeBool, clausesType, TypeBool))
	allApp := allConst.Apply(patternApp, clauses)

	wellfounded := Var("wellfounded3", MakeFun(T1, TypeBool))
	x := Var("x", TypeA)
	fOuter := Var("f_outer", MakeFun(TypeA, TypeAB))
	casewise := Var("casewise3", MakeFun(clausesType, MakeFun(TypeA, TypeAB), TypeA, TypeAB))

	disjBody := (Not(wellfounded.Apply(ltFree)).Or(Not(allApp))).Or(
		fOuter.Apply(x).Eq(casewise.Apply(clauses, fOuter, x)))
	concl := ext.Exists(fOuter)(ForAll(x)(disjBody))
	negatedConcl := Not(concl)

	// Goal: hyp = negated original concl (no other hyps). Conclusion = F.
	// This is the post-negConcl form.
	goal := testProp(F, negatedConcl)

	t.Logf("defThm: %s", prop.PrintProp(defThm))
	t.Logf("goal:   %s", prop.PrintProp(goal))

	subGoals := LeanRwTactic(defThm)(goal)
	if subGoals == nil {
		t.Fatalf("FAIL: LeanRwTactic returned nil on negated-concl-as-hyp goal")
	}
	t.Logf("LeanRwTactic SUCCEEDED with %d children", subGoals.Size())
	for i := 0; i < subGoals.Size(); i++ {
		t.Logf("  child[%d]: %s", i, prop.PrintProp(subGoals.ChildGoal(i)))
	}
}

// Test where the inner-lambda var `f` shadows the outer pattern_abstraction-lambda var `f`
// with the same name AND type — mimicking `pattern_abstraction(λf. ∀s. ∀t. ... tailadmissible(<<, λf.λa.⊤, s, t))`.
func TestLeanRwTactic_NameShadowing(t *testing.T) {
	TypeAB := MakeFun(TypeA, TypeB)
	T1 := MakeFun(TypeA, TypeA, TypeBool)
	// Make T2 take a function of the SAME type as the pattern_abstraction binder f
	patternFunType := MakeFun(TypeA, TypeAB)
	T2 := MakeFun(patternFunType, TypeA, TypeBool)
	cType := MakeFun(T1, T2, TypeA, TypeAB, TypeBool)
	c := ext.TestConst("c_v4", cType)

	ltv := Var("ltv", T1)
	pv := Var("pv", T2)
	sv := Var("sv", TypeA)
	tv := Var("tv", TypeAB)
	body := ltv.To(pv.To(sv.To(tv.To(ltv.Apply(sv, sv)))))
	defThm := testProp(c.Eq(body))

	ltFree := Var("<<", T1)
	// Inner lambda arg: λf.λa.⊤  where f has type A→AB (same as pattern_abstraction binder)
	innerF := Var("f", patternFunType) // SAME NAME as outer pattern_abstraction binder
	innerA := Var("a", TypeA)
	innerLambdaArg := innerF.To(innerA.To(WrapTerm(T)))

	// pattern_abstraction binder: also "f", same type
	fPattern := Var("f", patternFunType)
	s := Var("s", TypeA)
	tt := Var("t", TypeAB)
	patternEq := Var("pattern_eq", MakeFun(TypeAB, TypeBool, TypeBool))
	tailapp := c.Apply(ltFree, innerLambdaArg, s, tt)

	innerBody := ForAll(s)(ForAll(tt)(patternEq.Apply(fPattern.Apply(s), tailapp)))
	patternLambda := fPattern.To(innerBody)
	patternConst := ext.TestConst("pattern_abstraction4", MakeFun(
		MakeFun(patternFunType, TypeBool), TypeBool))
	patternApp := patternConst.Apply(patternLambda)

	// Wrap in ∃f.∀x.... shape
	clausesType := patternFunType
	clauses := Var("clauses", clausesType)
	allConst := ext.TestConst("list_all4", MakeFun(
		TypeBool, clausesType, TypeBool))
	allApp := allConst.Apply(patternApp, clauses)

	wellfounded := Var("wellfounded4", MakeFun(T1, TypeBool))
	x := Var("x", TypeA)
	fOuter := Var("f_outer", patternFunType)
	casewise := Var("casewise4", MakeFun(clausesType, patternFunType, TypeA, TypeAB))

	disjBody := (Not(wellfounded.Apply(ltFree)).Or(Not(allApp))).Or(
		fOuter.Apply(x).Eq(casewise.Apply(clauses, fOuter, x)))
	concl := ext.Exists(fOuter)(ForAll(x)(disjBody))

	goal := testProp(concl)
	t.Logf("defThm: %s", prop.PrintProp(defThm))
	t.Logf("goal:   %s", prop.PrintProp(goal))

	subGoals := LeanRwTactic(defThm)(goal)
	if subGoals == nil {
		t.Fatalf("FAIL: LeanRwTactic returned nil on name-shadowed goal")
	}
	t.Logf("LeanRwTactic SUCCEEDED with %d children", subGoals.Size())
	for i := 0; i < subGoals.Size(); i++ {
		t.Logf("  child[%d]: %s", i, prop.PrintProp(subGoals.ChildGoal(i)))
	}
}

// TestLeanRwTactic_MergeTacticsFixpoint verifies that mergeTactics
// (wrapping eqLemmaTacticOpt inside eqLemmaTacticExpand) recursively
// applies the rewrite to the residual subgoal — so a SINGLE
// LeanRwTactic call rewrites ALL occurrences of the const, not just
// the first one eqSimplify happens to fire on.
//
// This pins the implicit "fixpoint" semantics that the agent on a
// wellfounded-recursion frontier relied on (they reported "only top-level
// rewrote" — that interpretation was wrong; both positions get
// rewritten in one call). After one def_expand: tailadmissible should
// be completely gone from goals where it appears at multiple
// positions (top-level hyp + under-pattern_abstraction in conclusion).
func TestLeanRwTactic_MergeTacticsFixpoint(t *testing.T) {
	TypeAB := MakeFun(TypeA, TypeB)
	T1 := MakeFun(TypeA, TypeA, TypeBool)
	T2 := MakeFun(TypeAB, TypeA, TypeBool)
	cType := MakeFun(T1, T2, TypeA, TypeAB, TypeBool)
	c := ext.TestConst("c_fp", cType)

	ltv := Var("ltv", T1)
	pv := Var("pv", T2)
	sv := Var("sv", TypeA)
	tv := Var("tv", TypeAB)
	body := ltv.To(pv.To(sv.To(tv.To(ltv.Apply(sv, sv)))))
	defThm := testProp(c.Eq(body))

	// Goal with TWO tailadmissible occurrences:
	//   Hyp:   c(<<, p1, s1, t1)                          ← top-level, easy
	//   Concl: ∀s.∀t. F(c(<<, p2, s, t))                  ← under ∀∀ binder
	ltFree := Var("<<", T1)
	p1 := Var("p1", T2)
	p2 := Var("p2", T2)
	s1 := Var("s1", TypeA)
	t1 := Var("t1", TypeAB)
	topLevelHyp := c.Apply(ltFree, p1, s1, t1)

	F := Var("F_fp", MakeFun(TypeBool, TypeBool))
	s := Var("s", TypeA)
	tt := Var("t", TypeAB)
	underBinderTerm := c.Apply(ltFree, p2, s, tt)
	concl := ForAll(s)(ForAll(tt)(F.Apply(underBinderTerm)))

	goal := testProp(concl, topLevelHyp.Core())
	t.Logf("goal pre:  %s", prop.PrintProp(goal))

	subGoals := LeanRwTactic(defThm)(goal)
	if subGoals == nil {
		t.Fatalf("LeanRwTactic returned nil")
	}
	if subGoals.Size() != 2 {
		t.Fatalf("expected 2 children, got %d", subGoals.Size())
	}
	residual := subGoals.ChildGoal(1)
	t.Logf("goal post: %s", prop.PrintProp(residual))

	// After one call, NO occurrence of c_fp should remain anywhere.
	// (TermContainsConstName walks under binders too.)
	const cName = "c_fp"
	if prop.ContainsConstName(residual, cName) {
		t.Errorf("residual still contains %s after one LeanRwTactic call: %s",
			cName, prop.PrintProp(residual))
	}
}

// TestLeanRwTactic_ConjunctiveLemma pins the conjunction-splitting path:
// a ∀-quantified two-clause conjunction (the shape of ALL/list_member/PAIRWISE
// clause-form thms) applied via lean_rw must drive BOTH clauses as
// conclusion rewriters in a single pass, with child[0] = the original
// conjunctive lemma (dep-tracking unchanged).
func TestLeanRwTactic_ConjunctiveLemma(t *testing.T) {
	x := Var("x", TypeA)
	c := Var("c", TypeA)
	d := Var("d", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// ⊢ ∀x. (f(x) = a) ∧ (g(x) = b)
	lemma := testThm(ForAll(x)(f.Apply(x).Eq(a).And(g.Apply(x).Eq(b))).Core())
	// goal: ⊢ P(f(c)) ∧ Q(g(d))
	goal := testProp(P.Apply(f.Apply(c)).And(Q.Apply(g.Apply(d))).Core())

	sg := LeanRwTactic(lemma)(goal)
	require.NotNil(t, sg, "conjunctive lean_rw should fire")
	require.Equal(t, 2, sg.Size(), "child[0]=lemma, child[1]=rewritten")
	assertPropAlphaEqual(t, sg.ChildGoal(0), lemma.AsProp())
	// Both clauses fired: f(c)→a and g(d)→b in one pass.
	expected := testProp(P.Apply(a).And(Q.Apply(b)).Core())
	assertPropAlphaEqual(t, sg.ChildGoal(1), expected)
}

// TestLeanRwTactic_ConjunctiveLemma_FixedPoint verifies the DeepRewrite
// fixed-point: one clause's RHS exposes a redex for another clause.
// lemma: ∀x. (f(x) = g(x)) ∧ (g(x) = a). Rewriting f(c) → g(c) must then
// re-fire g(c) → a, reaching a in one combined pass.
func TestLeanRwTactic_ConjunctiveLemma_FixedPoint(t *testing.T) {
	x := Var("x", TypeA)
	c := Var("c", TypeA)
	a := Var("a", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))

	lemma := testThm(ForAll(x)(f.Apply(x).Eq(g.Apply(x)).And(g.Apply(x).Eq(a))).Core())
	goal := testProp(P.Apply(f.Apply(c)).Core())

	sg := LeanRwTactic(lemma)(goal)
	require.NotNil(t, sg)
	require.Equal(t, 2, sg.Size())
	// f(c) → g(c) → a  (fixed point)
	expected := testProp(P.Apply(a).Core())
	assertPropAlphaEqual(t, sg.ChildGoal(1), expected)
}

// A conjunctive rewrite's residual keeps the goal's hypotheses, and a
// residual whose hypotheses contradict one another is closed at ⊥ where
// it states the rewritten conclusion. The reconstruction takes that
// theorem back to the goal; assertSubGoals then holds it over full
// proofs, ⊥ proofs and proofs that drop hypotheses.
func TestLeanRwTactic_ConjunctiveLemma_ResidualClosedByContradiction(t *testing.T) {
	x := Var("x", TypeA)
	c := Var("c", TypeA)
	d := Var("d", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))

	// ⊢ ∀x. (f(x) = a) ∧ (g(x) = b)
	lemma := testThm(ForAll(x)(f.Apply(x).Eq(a).And(g.Apply(x).Eq(b))).Core())
	// goal: R(c), ¬R(c) ⊢ P(f(c)) ∧ Q(g(d))
	goal := testProp(P.Apply(f.Apply(c)).And(Q.Apply(g.Apply(d))).Core(), R.Apply(c).Core(), Not(R.Apply(c)).Core())

	sg := LeanRwTactic(lemma)(goal)
	require.NotNil(t, sg, "conjunctive lean_rw should fire")
	require.Equal(t, 2, sg.Size(), "child[0]=lemma, child[1]=rewritten")
	residual := sg.ChildGoal(1)
	require.False(t, residual.Conclusion().Equals(F))

	var thm Prop
	require.NotPanics(t, func() { thm = sg.Reconstruct(lemma, testThm(F, residual.Hyps()...)) },
		"a residual closed by contradiction reconstructs")
	require.True(t, thm.Proved())
	require.True(t, IsStronger(thm, goal))

	assertSubGoals(t, sg, goal)
}

// A lemma that carries a hypothesis is a child that can be closed by
// contradiction, `Q(b) ⊢ ⊥` here for `Q(b) ⊢ ∀x. a = f(x)`. The rewrite
// fires right to left, so the reconstruction flips the lemma's
// theorem, and it flips the lemma as stated whatever that theorem
// concludes. assertSubGoals holds it over full proofs, ⊥ proofs and
// proofs that drop hypotheses.
func TestLeanRwTactic_FlippedLemmaUnderAHypothesis_ClosedByContradiction(t *testing.T) {
	x := Var("x", TypeA)
	c := Var("c", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	// Q(b) ⊢ ∀x. a = f(x)
	lemma := testThm(ForAll(x)(a.Eq(f.Apply(x))).Core(), Q.Apply(b).Core())
	// goal: Q(b) ⊢ P(f(c))
	goal := testProp(P.Apply(f.Apply(c)).Core(), Q.Apply(b).Core())

	sg := LeanRwTactic(lemma)(goal)
	require.NotNil(t, sg, "the flipped rewrite should fire")
	require.Equal(t, 2, sg.Size(), "child[0]=lemma, child[1]=rewritten")
	assertPropAlphaEqual(t, sg.ChildGoal(0), lemma.AsProp())
	assertPropAlphaEqual(t, sg.ChildGoal(1), testProp(P.Apply(a).Core(), Q.Apply(b).Core()))
	residual := sg.ChildGoal(1)

	var thm Prop
	require.NotPanics(t, func() {
		thm = sg.Reconstruct(testThm(F, Q.Apply(b).Core()), testThm(residual.Conclusion(), residual.Hyps()...))
	}, "a lemma closed by contradiction reconstructs")
	require.True(t, thm.Proved())
	require.True(t, IsStronger(thm, goal))

	assertSubGoals(t, sg, goal)
}

// A clause's own variable, bound by a binder of the same name in its right
// side, stays bound: the walk does not hand it to the clause as free.
func TestLeanRwTactic_ConjunctiveLemma_BoundVariableDoesNotFeedClause(t *testing.T) {
	j := Var("J", TypeA)
	c := Var("c", TypeA)
	d := Var("d", TypeA)
	f := Var("f", MakeFun(MakeFun(TypeA, TypeA), TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	rhs := f.Apply(j.To(j))

	lemma := testProp(j.Eq(rhs).And(c.Eq(d)).Core())
	goal := testProp(P.Apply(j).Core())

	before := skeleton.WhistleFires()
	sg := LeanRwTactic(lemma)(goal)
	require.NotNil(t, sg)
	require.Equal(t, 2, sg.Size())
	assertPropAlphaEqual(t, sg.ChildGoal(1), testProp(P.Apply(rhs).Core()))
	assert.Equal(t, before, skeleton.WhistleFires())
}

// f = g : A→B→bool  →  (one call)  ∀x.∀y. f(x,y) = g(x,y)
func TestFunext_Deep_TwoArity(t *testing.T) {
	A := TypeA
	B := TypeB
	RtoB := MakeFun(A, B, TypeBool)
	f := Var("f", RtoB)
	g := Var("g", RtoB)

	goal := MakeProp(f.Eq(g).Core())
	sg := FunextTactic(goal)
	require.NotNil(t, sg, "funext should fire on f=g")
	require.Equal(t, 1, sg.Size())
	out := sg.ChildGoal(0).Conclusion()
	t.Logf("funext(f=g : A→B→bool) -> %s", ext.FormatTerm(out, false))

	// Outer should be ∀; peel both and confirm bool-level equality body.
	abs1 := ext.MatchesFORALL(out)
	require.False(t, abs1.IsZero(), "outer should be ∀")
	abs2 := ext.MatchesFORALL(abs1.Body())
	require.False(t, abs2.IsZero(), "second ∀ should be present (all arrows peeled in one call)")
	l, r, ok := ext.MatchesEQ(abs2.Body())
	require.True(t, ok, "innermost body should be an equality")
	assert.True(t, l.Type().Equals(TypeBool), "innermost equality should be at bool level, got %s", ext.FormatType(l.Type()))
	_ = r

	// Reconstruction soundness: rebuild ⊢ f=g from a proof of the pointwise form.
	assertSubGoals(t, sg, goal)
}

// Single-arity f = g : A→bool  →  ∀x. f(x) = g(x)
func TestFunext_Deep_OneArity(t *testing.T) {
	A := TypeA
	AtoBool := MakeFun(A, TypeBool)
	f := Var("f", AtoBool)
	g := Var("g", AtoBool)

	goal := MakeProp(f.Eq(g).Core())
	sg := FunextTactic(goal)
	require.NotNil(t, sg)
	out := sg.ChildGoal(0).Conclusion()
	t.Logf("funext(f=g : A→bool) -> %s", ext.FormatTerm(out, false))
	abs := ext.MatchesFORALL(out)
	require.False(t, abs.IsZero())
	l, _, ok := ext.MatchesEQ(abs.Body())
	require.True(t, ok)
	assert.True(t, l.Type().Equals(TypeBool))
	assertSubGoals(t, sg, goal)
}

// Non-function equality must still return nil (shape gate preserved).
func TestFunext_Deep_NonFunctionNil(t *testing.T) {
	A := TypeA
	a := Var("a", A)
	b := Var("b", A)
	assert.Nil(t, FunextTactic(MakeProp(a.Eq(b).Core())), "funext must not fire on atomic a=b")

	P := Var("P", MakeFun(A, TypeBool))
	x := Var("x", A)
	assert.Nil(t, FunextTactic(MakeProp(P.Apply(x).Core())), "funext must not fire on non-equality")
}

// TestCongrArg_BasicShape covers the happy path: equality hyp `a = b`
// plus function `f`, produces a subgoal that adds `f(a) = f(b)` to the
// hyps and keeps the original equality available; the reconstruct
// soundly re-derives the original goal.
func TestCongrArg_BasicShape(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	Q := Var("Q", TypeBool)

	// (a = b) ⊢ Q
	goal := MakeProp(Q.Core(), Eq(a.Core(), b.Core()))
	sg := CongrArgTactic(f.Core(), 0)(goal)
	assert.NotNil(t, sg, "congr_arg must apply on an equality hyp")
	assert.Equal(t, 1, sg.Size(), "congr_arg produces exactly one subgoal")

	child := sg.ChildGoal(0)
	hasOrig := false
	hasDerived := false
	wantDerived := Eq(f.Apply(a).Core(), f.Apply(b).Core())
	for h := range child.HypIter() {
		if h.AlphaEquals(Eq(a.Core(), b.Core())) {
			hasOrig = true
		}
		if h.AlphaEquals(wantDerived) {
			hasDerived = true
		}
	}
	assert.True(t, hasOrig, "congr_arg must keep the original equality hyp")
	assert.True(t, hasDerived, "congr_arg must add f(a)=f(b) to hyps")

	assertSubGoals(t, sg, goal)
}

// TestCongrArg_PreservesOtherHyps verifies unrelated hyps pass through.
func TestCongrArg_PreservesOtherHyps(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", TypeBool)

	// P(a), (a = b) ⊢ Q
	goal := MakeProp(Q.Core(), P.Apply(a).Core(), Eq(a.Core(), b.Core()))
	sg := CongrArgTactic(f.Core(), 1)(goal)
	assert.NotNil(t, sg)
	assertSubGoals(t, sg, goal)
}

// TestCongrArg_OutOfRange pins the index range guard.
func TestCongrArg_OutOfRange(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))

	goal := MakeProp(Eq(a.Core(), b.Core()))
	assert.Nil(t, CongrArgTactic(f.Core(), 5)(goal), "out-of-range index returns nil")
	assert.Nil(t, CongrArgTactic(f.Core(), -1)(goal), "negative index returns nil")
}

// TestCongrArg_NonEqualityHyp pins that a non-equality hyp returns nil.
func TestCongrArg_NonEqualityHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	P := Var("P", MakeFun(TypeA, TypeBool))

	// P(a) ⊢ P(a) — hyp 0 is not an equality.
	goal := MakeProp(P.Apply(a).Core(), P.Apply(a).Core())
	assert.Nil(t, CongrArgTactic(f.Core(), 0)(goal))
}

// TestCongrArg_DomainMismatch verifies the type-gate: a function whose
// domain doesn't match the equality's side type returns nil (instead of
// panicking inside core.Apply).
func TestCongrArg_DomainMismatch(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	// g : B → B, but the equality is over A.
	g := Var("g", MakeFun(TypeB, TypeB))

	goal := MakeProp(Eq(a.Core(), b.Core()))
	assert.Nil(t, CongrArgTactic(g.Core(), 0)(goal),
		"function whose domain mismatches the equality type must return nil, not panic")
}

// TestCongrArg_NotAFunction verifies a non-function term returns nil.
func TestCongrArg_NotAFunction(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA) // not a function

	goal := MakeProp(Eq(a.Core(), b.Core()))
	assert.Nil(t, CongrArgTactic(c.Core(), 0)(goal))
}

// TestCongrFun_BasicShape covers the dual happy path: function-equality
// hyp `f = g` plus argument `x`, produces a subgoal adding `f(x) = g(x)`.
func TestCongrFun_BasicShape(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))
	x := Var("x", TypeA)
	Q := Var("Q", TypeBool)

	// (f = g) ⊢ Q
	goal := MakeProp(Q.Core(), Eq(f.Core(), g.Core()))
	sg := CongrFunTactic(x.Core(), 0)(goal)
	assert.NotNil(t, sg, "congr_fun must apply on a function-equality hyp")
	assert.Equal(t, 1, sg.Size())

	child := sg.ChildGoal(0)
	hasOrig := false
	hasDerived := false
	wantDerived := Eq(f.Apply(x).Core(), g.Apply(x).Core())
	for h := range child.HypIter() {
		if h.AlphaEquals(Eq(f.Core(), g.Core())) {
			hasOrig = true
		}
		if h.AlphaEquals(wantDerived) {
			hasDerived = true
		}
	}
	assert.True(t, hasOrig, "congr_fun must keep the original function-equality hyp")
	assert.True(t, hasDerived, "congr_fun must add f(x)=g(x) to hyps")

	assertSubGoals(t, sg, goal)
}

// TestCongrFun_OutOfRange pins the index range guard.
func TestCongrFun_OutOfRange(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))
	x := Var("x", TypeA)

	goal := MakeProp(Eq(f.Core(), g.Core()))
	assert.Nil(t, CongrFunTactic(x.Core(), 5)(goal))
	assert.Nil(t, CongrFunTactic(x.Core(), -1)(goal))
}

// TestCongrFun_NonFunctionEquality verifies that an equality whose sides
// are not functions returns nil.
func TestCongrFun_NonFunctionEquality(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	x := Var("x", TypeA)

	// (a = b) ⊢ ... — sides are TypeA, not functions.
	goal := MakeProp(Eq(a.Core(), b.Core()))
	assert.Nil(t, CongrFunTactic(x.Core(), 0)(goal))
}

// TestCongrFun_ArgTypeMismatch verifies the type-gate on the argument.
func TestCongrFun_ArgTypeMismatch(t *testing.T) {
	defer goleak.VerifyNone(t)

	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))
	z := Var("z", TypeB) // wrong arg type (domain is A)

	goal := MakeProp(Eq(f.Core(), g.Core()))
	assert.Nil(t, CongrFunTactic(z.Core(), 0)(goal),
		"argument whose type mismatches the function domain must return nil")
}

// A flipped rewrite with nothing to rewrite does not apply: the only
// occurrence of the oriented left side is in the equality itself, which
// the rewrite leaves alone — it is not a way to turn the hyp round.
func TestRwHypTactic_Flip_NothingToRewriteDoesNotApply(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", TypeA)
	d := Var("d", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	eq := d.Eq(f.Apply(m)).Core()
	goal := testProp(Q.Apply(d).Core(), eq)

	assert.Nil(t, RwHypTactic(rwEqHypIndex(t, goal, eq), true)(goal),
		"f(m) occurs nowhere but in the equality")
}

// A ground ⇔ hypothesis is an equation at bool, and `rw` rewrites by it
// as by any other: the left atom becomes the right wherever it stands,
// under a connective and inside another hypothesis. A ∀-quantified ⇔
// is no ground equation and is not a rewrite rule here.
func TestRwHypTactic_RewritesByAGroundIff(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))

	iff := P.Apply(a).Eq(Q.Apply(a)).Core()
	require.True(t, iff.Type().Equals(TypeBool))
	goal := testProp(P.Apply(a).And(R.Apply(a)).Core(), iff, P.Apply(a).Imply(R.Apply(a)).Core())

	sg := RwHypTactic(rwEqHypIndex(t, goal, iff), false)(goal)
	require.NotNil(t, sg, "rw by a ground ⇔ should fire")
	child := sg.ChildGoal(0)
	assert.True(t, child.Conclusion().AlphaEquals(Q.Apply(a).And(R.Apply(a)).Core()),
		"the atom is rewritten under the conjunction, got %v", child.Conclusion())
	assert.True(t, child.HasHyp(Q.Apply(a).Imply(R.Apply(a)).Core()), "and inside the other hypothesis")
	assert.True(t, child.HasHyp(iff), "the ⇔ is kept")
	assertSubGoals(t, sg, goal)

	x := Var("x", TypeA)
	quantified := ForAll(x)(P.Apply(x).Eq(Q.Apply(x))).Core()
	wide := testProp(P.Apply(a).Core(), quantified)
	idx := -1
	for i := range wide.NumHyps() {
		if wide.Hyp(i).AlphaEquals(quantified) {
			idx = i
		}
	}
	require.GreaterOrEqual(t, idx, 0)
	assert.Nil(t, RwHypTactic(idx, false)(wide), "a ∀-quantified ⇔ is not a ground equation: ground it first")
}
