package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

func TestStrongerGoals(t *testing.T) {
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	z := Var("z", TypeBool)
	w := Var("w", TypeBool)

	assert.Equal(t, _STRONGER_GOALS_HYP_DIFF_THRES, 2)

	goal := MakeProp(x)
	assert.Equal(t, len(StrongerGoals(goal)), 1)
	goal = MakeProp(x, y, z)
	assert.Equal(t, len(StrongerGoals(goal)), 7)
	goal = MakeProp(x, y, z, w)
	assert.Equal(t, len(StrongerGoals(goal)), 14)
	goal = MakeProp(F, x, y, z)
	assert.Equal(t, len(StrongerGoals(goal)), 7)
	goal = MakeProp(F, x, y, z, w)
	assert.Equal(t, len(StrongerGoals(goal)), 11)
}

func TestPropTypeMatch(t *testing.T) {
	defer goleak.VerifyNone(t)

	t.Run("basic type instantiation", func(t *testing.T) {
		// Pattern: ⊢ x:A = x:A
		xA := ext.Var("x", core.TypeA())
		pattern := core.MakeProp(core.Eq(xA, xA))

		// Target: ⊢ x:bool = x:bool
		xBool := ext.Var("x", core.TypeBool())
		target := core.MakeProp(core.Eq(xBool, xBool))

		substs, ok := NormalizedPropTypeMatch(pattern, target)
		assert.True(t, ok)
		assert.Len(t, substs, 1)
		assert.True(t, substs[0].VarType.Equals(core.TypeA()))
		assert.True(t, substs[0].HolType.Equals(core.TypeBool()))
	})

	t.Run("no match different structure", func(t *testing.T) {
		xA := ext.Var("x", core.TypeA())
		pattern := core.MakeProp(core.Eq(xA, xA))
		target := core.MakeProp(core.Eq(xA, ext.Var("y", core.TypeA())))

		_, ok := NormalizedPropTypeMatch(pattern, target)
		assert.False(t, ok)
	})

	t.Run("same theorem no match", func(t *testing.T) {
		// Same polymorphic theorem — should not match (no actual type substitution).
		xA := ext.Var("x", core.TypeA())
		pattern := core.MakeProp(core.Eq(xA, xA))
		target := core.MakeProp(core.Eq(xA, xA))

		_, ok := NormalizedPropTypeMatch(pattern, target)
		assert.False(t, ok)
	})

	t.Run("different size no match", func(t *testing.T) {
		xA := ext.Var("x", core.TypeA())
		pattern := core.MakeProp(core.Eq(xA, xA))
		target := core.MakeProp(ext.Var("x", core.TypeBool()).And(ext.Var("y", core.TypeBool())))

		_, ok := NormalizedPropTypeMatch(pattern, target)
		assert.False(t, ok)
	})

	t.Run("type instantiation A->ind", func(t *testing.T) {
		xA := ext.Var("x", core.TypeA())
		pattern := core.MakeProp(core.Eq(xA, xA))

		xInd := ext.Var("x", TypeInd)
		target := core.MakeProp(core.Eq(xInd, xInd))

		substs, ok := NormalizedPropTypeMatch(pattern, target)
		assert.True(t, ok)
		assert.Len(t, substs, 1)
		assert.True(t, substs[0].HolType.Equals(TypeInd))
	})
}

// TestThmCache_LoadMatchThm exercises the new TypeMatch tier in
// FindProvedThm: insert a polymorphic thm and look up:
//
//	(1) a variant goal (different type-var names) — should hit;
//	(2) a concrete-instantiation goal (type vars → concrete bool) — should hit;
//	(3) a structurally different goal — should miss.
//
// Note: source must not normalize to ⊤ (a tautology), since
// LoadMatchThm has a trivial-true guard to prevent a ⊢⊤ entry from
// matching everything. ∀x. P(x) → Q(x) is the simplest polymorphic
// non-tautology: it stays non-trivial after Normalize.
func TestThmCache_LoadMatchThm(t *testing.T) {
	defer goleak.VerifyNone(t)

	xA := Var("x", TypeA)
	PA := Var("P", MakeFun(TypeA, TypeBool))
	QA := Var("Q", MakeFun(TypeA, TypeBool))
	source := core.TestThm(ForAll(xA)(PA.Apply(xA).Imply(QA.Apply(xA))))
	require.False(t, source.IsZero())
	normalized, _ := Normalize(source)
	require.False(t, normalized.Conclusion().Equals(T),
		"source must not normalize to ⊤ — would hit trivial-true guard")

	var cache ThmCache
	cache.SaveThm(source, normalized.AsThmCert())

	// (1) Variant goal: same structure with B in place of A.
	TypeB := core.MakeVarType("B")
	xB := Var("x", TypeB)
	PB := Var("P", MakeFun(TypeB, TypeBool))
	QB := Var("Q", MakeFun(TypeB, TypeBool))
	goalVariant := MakeProp(ForAll(xB)(PB.Apply(xB).Imply(QB.Apply(xB))))
	stronger, equiv := cache.LoadMatchThm(goalVariant)
	require.NotNil(t, stronger, "variant goal should hit LoadMatchThm")
	assert.True(t, stronger.AlphaEquals(goalVariant),
		"reconstructed thm should match goal shape")
	require.NotNil(t, equiv)
	assert.True(t, equiv.AlphaEquals(source),
		"equivalentThm should be the cached source")

	// (2) Concrete-instantiation goal: same structure with bool in place of A.
	xBool := Var("x", TypeBool)
	Pbool := Var("P", MakeFun(TypeBool, TypeBool))
	Qbool := Var("Q", MakeFun(TypeBool, TypeBool))
	goalConcrete := MakeProp(ForAll(xBool)(Pbool.Apply(xBool).Imply(Qbool.Apply(xBool))))
	stronger, equiv = cache.LoadMatchThm(goalConcrete)
	require.NotNil(t, stronger, "concrete-instantiation goal should hit LoadMatchThm")
	assert.True(t, stronger.AlphaEquals(goalConcrete))
	require.NotNil(t, equiv)
	assert.True(t, equiv.AlphaEquals(source))

	// (3) Structurally different goal: ∀x:A. P(x) ∧ Q(x). Different shape.
	goalDifferent := MakeProp(
		ForAll(xA)(PA.Apply(xA).And(QA.Apply(xA))))
	stronger, _ = cache.LoadMatchThm(goalDifferent)
	assert.Nil(t, stronger, "structurally different goal should miss")

	// (4) FindProvedThm dispatches through the tier — confirm.
	stronger, _ = cache.FindProvedThm(goalConcrete)
	require.NotNil(t, stronger, "FindProvedThm should find via LoadMatchThm tier")
}

// TestTypeInstAction_Apply verifies that applying a polymorphic source Thm
// to a ground goal that is its type instantiation closes the goal via the
// kernel's PropTypeInst primitive.
func TestTypeInstAction_Apply(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Source: ⊢ ∀x:A. x = x  (polymorphic reflexivity)
	xA := Var("x", TypeA)
	sourceConcl := ForAll(xA)(xA.Eq(xA))
	source := core.TestThm(sourceConcl)
	require.False(t, source.IsZero())
	require.True(t, ext.PropHasTypeVars(source))

	// Goal: ⊢ ∀x:bool. x = x
	xBool := Var("x", TypeBool)
	goal := MakeProp(ForAll(xBool)(xBool.Eq(xBool)))
	require.False(t, ext.PropHasTypeVars(goal))

	node := CreateGoalStack(goal)
	require.True(t, ApplyTypeInst(node, source), "the type_inst step should succeed")
	assert.False(t, node.ProvedThm().IsZero(), "node should be proved after the type_inst step")
	assert.True(t, node.ProvedThm().AlphaEquals(goal))
}

// TestApplyDefExpand_FailsWhenRewriteDoesntApply pins the def_expand
// invariant: when the def thm's rewrite path doesn't fire (because
// the const doesn't appear in the goal, or because the def thm's shape
// makes rewriting a no-op as in TypeDef cases), ApplyDefExpand returns
// FALSE — no silent "def thm added as hypothesis" outcome.
func TestApplyDefExpand_FailsWhenRewriteDoesntApply(t *testing.T) {
	defer goleak.VerifyNone(t)

	// c : A → bool with def `λa.(a = a)` (closed body — the const
	// itself doesn't appear in the goal below, so the rewrite path
	// has nothing to match).
	a := Var("a", TypeA)
	c := ext.ConstDef(a.To(a.Eq(a)).Core(), "TestApplyDefExpandUnusedC")

	// Goal: ⊢ p — `c` is nowhere in it. The def thm's rewrite path
	// has nothing to match; ApplyDefExpand must return false.
	p := Var("p", TypeBool)
	goal := MakeProp(p.Core())

	rewriteOnlyNode := CreateGoalStack(goal)
	assert.False(t,
		ApplyDefExpand(rewriteOnlyNode, c.AssertConst()),
		"ApplyDefExpand must return false when the const isn't in the goal — "+
			"no silent hyp-match fallback")
}

// TestTypeInstAction_NoMatch verifies that the type_inst step returns
// false when the source is not a polymorphic parent of the goal.
func TestTypeInstAction_NoMatch(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Source: ⊢ ∀x:A. x = x
	xA := Var("x", TypeA)
	source := core.TestThm(ForAll(xA)(xA.Eq(xA)))

	// Goal: ⊢ ∀x:bool. ∀y:bool. x = y  (not a type instance)
	xBool := Var("x", TypeBool)
	yBool := Var("y", TypeBool)
	goal := MakeProp(ForAll(xBool)(ForAll(yBool)(xBool.Eq(yBool))))

	node := CreateGoalStack(goal)
	assert.False(t, ApplyTypeInst(node, source))
	assert.True(t, node.ProvedThm().IsZero())
}

// makeHilbertConst builds a const whose definition has the direct
// Hilbert shape `⊢ c = εx:A.(x = x)` — the simple shape produced by
// a basic definition. Used as the test fixture for the direct-case
// arm of the ExistentialConstDef path.
func makeHilbertConst(t *testing.T, name string) ConstTerm {
	t.Helper()
	x := Var("x", TypeA)
	body := x.SuchThat(x.Eq(x).Core()) // εx:A.(x = x)
	c := ext.ConstDef(body.Core(), ext.TermName(name))
	return c.AssertConst()
}

// makeAppliedHilbertConst builds a const whose definition has the
// applied Hilbert shape `⊢ c = (εF. ∀_idx. F(_idx) = _idx)(witness)`
// — the shape produced by a recursive definition's
// generic recursion combinator. Used to test that the
// IsHilbertConstDef + ExistentialConstDef path handles the
// applied-Hilbert case.
//
// The fixture's structure:
//   - F :: bool → bool (identity-like, one argument)
//   - body = ∀_idx. F(_idx) = _idx  (trivially-satisfied so ∃F.body holds)
//   - witness :: bool, a closed term
//   - c = (εF.body)(witness) :: bool
func makeAppliedHilbertConst(t *testing.T, name string) ConstTerm {
	t.Helper()
	numToNum := MakeFun(TypeBool, TypeBool) // simpler stand-in than num
	F := Var("F", numToNum)
	idx := Var("_idx", TypeBool)
	// body = ∀_idx:bool. F(_idx) = _idx
	body := ForAll(idx)(F.Apply(idx).Eq(idx).Core())
	// εF:(bool→bool). body
	hilbert := F.SuchThat(body.Core()) // εF. ∀_idx. F _idx = _idx
	// witness must be a closed term — NewConstDef rejects bodies with
	// free vars. Use the bool constant T.
	rhs := ext.WrapTerm(hilbert.Core()).Apply(T)
	c := ext.ConstDef(rhs.Core(), ext.TermName(name))
	return c.AssertConst()
}

// TestIsHilbertConstDef pins the predicate across all three relevant
// shapes:
//
//	(a) direct Hilbert    c = εF.P(F)              → true
//	(b) applied Hilbert   c = (εF.P(F))(args...)   → true (a recursive definition)
//	(c) plain λ-equation  c = λx.body              → false (regular ConstDef)
func TestIsHilbertConstDef(t *testing.T) {
	defer goleak.VerifyNone(t)

	// (a) direct Hilbert
	hilbert := makeHilbertConst(t, "TestIsHilbertConstDef_Direct")
	assert.True(t, prop.IsHilbertConstDef(hilbert),
		"IsHilbertConstDef must detect direct εx.P(x) shape")

	// (b) applied Hilbert — the case that motivates this whole path
	// (real consts: +, list_member, MULT, …)
	applied := makeAppliedHilbertConst(t, "TestIsHilbertConstDef_Applied")
	assert.True(t, prop.IsHilbertConstDef(applied),
		"IsHilbertConstDef must detect (εF.P(F))(args) applied shape — "+
			"the load-bearing case for recursively defined consts")

	// (c) negative: λa:A.(a = a) — function abstraction, not Hilbert
	a := Var("a", TypeA)
	lambda := ext.ConstDef(a.To(a.Eq(a).Core()).Core(), "TestIsHilbertConstDef_Lambda")
	assert.False(t, prop.IsHilbertConstDef(lambda.AssertConst()),
		"IsHilbertConstDef must reject λx.body shape")
}

// TestExistentialConstDef_AppliedShape pins the bridge thm produced
// for an applied-Hilbert const. Verifies:
//   - bridge thm is hypothesis-bearing (`∃F.P(F) ⊢ ...`)
//   - the bridge conclusion has c-occurrences (the partial-application
//     subterm `(εF.P(F))(args)` has been rewritten back to c via the
//     def thm)
func TestExistentialConstDef_AppliedShape(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := makeAppliedHilbertConst(t, "TestExistentialConstDef_AppliedShape_C")
	bridge := prop.ExistentialConstDef(c)
	require.False(t, bridge.IsZero(), "ExistentialConstDef must return non-nil for applied-Hilbert shape")
	require.Equal(t, 1, bridge.NumHyps(),
		"bridge thm must have exactly 1 hypothesis (the existence claim)")

	// Bridge conclusion mentions c — the (εF.P(F))(args) subterm got
	// folded back to c via EqSym(def). Inspect the conclusion term for
	// the const-name to confirm.
	assert.True(t, prop.ContainsConstName(core.MakeProp(bridge.Conclusion()), c.Name()),
		"bridge conclusion must mention %s (the (εF.P(F))(args) subterm "+
			"should have been rewritten back to c)", c.Name())
}

// TestExistentialConstDefAction_AppliedHilbert pins the step on the
// applied-Hilbert shape (ADD/MULT/list_member-style consts a recursive
// definition produces): 2 children, the existence subgoal child(0)
// hyp-free + ∃-headed.
func TestExistentialConstDefAction_AppliedHilbert(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := makeAppliedHilbertConst(t, "TestExistentialConstDefAction_Applied_C")
	p := Var("p", TypeBool)
	node := CreateGoalStack(MakeProp(p.Core()))

	require.True(t, node.runStep(_ExistentialConstDefStep{constTerm: c}),
		"the existential step must fire on the applied-Hilbert shape")
	require.Equal(t, 2, len(node.children))

	// child(0): hyp-free existence claim ∃F. ...
	existsGoal := node.child(0).Goal
	assert.Equal(t, 0, existsGoal.NumHyps())
	vars, _ := ext.DecomposesEXISTS(existsGoal.Conclusion())
	assert.False(t, vars.Empty(),
		"existence subgoal conclusion must be ∃-headed")
}

// TestExistentialConstDefAction_ProducesTwoChildren pins the step's
// output shape: child(0) = ⊢ ∃x.P(x), child(1) = Γ, P(c) ⊢ G — and
// that BOTH are handed over open: the residual is the caller's to
// close with its own move (the session's `simplify`, a chapter's
// Case), never simplified inside the step (macro.go's header).
func TestExistentialConstDefAction_ProducesTwoChildren(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := makeHilbertConst(t, "TestExistentialConstDefAction_C")

	p := Var("p", TypeBool)
	goal := MakeProp(p.Core())
	node := CreateGoalStack(goal)

	require.True(t, node.runStep(_ExistentialConstDefStep{constTerm: c}),
		"the existential step must fire on a Hilbert-shape const")

	require.Equal(t, 2, len(node.children),
		"the existential step must produce exactly 2 children")
	assert.Equal(t, 2, len(node.UnsolvedLeaves()),
		"both children stay open — the step records no simplification of the residual")

	// child(0): ⊢ ∃x.(x = x)  (the existence claim — same hyps as goal,
	// here the goal had none).
	existsGoal := node.child(0).Goal
	assert.Equal(t, 0, existsGoal.NumHyps(),
		"existence subgoal carries the original hyps (here: none)")
	// Conclusion should be an ∃-headed term.
	vars, _ := ext.DecomposesEXISTS(existsGoal.Conclusion())
	assert.False(t, vars.Empty(),
		"existence subgoal conclusion should be ∃-headed")

	// child(1): P(c) ⊢ p  (residual gains P(c) = (c=c) as a free hyp).
	residual := node.child(1).Goal
	assert.True(t, residual.Conclusion().AlphaEquals(p.Core()),
		"residual conclusion must equal original goal conclusion")
}
