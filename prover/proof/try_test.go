package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

var (
	numMetaType = core.MakeMetaType("num", 0)
	numType     = core.MakeCompositeType(numMetaType)

	zeroConstMeta = core.MakeConstMeta("_0", numType)
	sucConstMeta  = core.MakeConstMeta("suc", MakeFun(numType, numType))

	zeroTerm = core.MakeConstTerm(zeroConstMeta, numType)
	sucTerm  = core.MakeConstTerm(sucConstMeta, MakeFun(numType, numType))

	// ∀P n. P(_0) ∧ (∀n:num. P(n) ⇒ P(suc(n))) ⇒ P(n)
	numInductionThm = func() ThmCert {
		P := Var("P", MakeFun(numType, TypeBool))
		n := Var("n", numType)
		Pn := P.Apply(n)
		P0 := P.Apply(zeroTerm)
		Psuc := P.Apply(ext.Apply(sucTerm, n))
		return core.TestThm(ForAll(P)(ForAll(n)(P0.And(ForAll(n)(Pn.Imply(Psuc))).Imply(Pn))))
	}()

	numInductionTmpl = func() *tactic.InductionTemplate {
		t, err := tactic.AnalyzeInductionPrinciple(numInductionThm)
		if err != nil {
			panic(err)
		}
		return t
	}()
)

// --- ByCaseTactic tests ---

func TestTryByCaseTactic_Basic(t *testing.T) {
	defer goleak.VerifyNone(t)

	b := Var("b", TypeBool)
	p := Var("p", TypeBool)

	// Goal: p ∧ b (case split on b)
	goal := core.MakeProp(p.And(b))

	branchT, branchF, ok := TryByCaseTactic(goal, b)
	assert.True(t, ok, "TryByCaseTactic should succeed")
	assert.NotNil(t, branchT)
	assert.NotNil(t, branchF)
	assert.True(t, branchT.HasHyp(b), "T-branch should have b as hypothesis")
	assert.True(t, branchF.HasHyp(Not(b)), "F-branch should have ¬b as hypothesis")
}

func TestTryByCaseTactic_CaseTermIsConclusion(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Goal: b (caseTerm IS the conclusion → tactic not applicable)
	b := Var("b", TypeBool)
	goal := core.MakeProp(b)

	_, _, ok := TryByCaseTactic(goal, b)
	assert.False(t, ok)
}

func TestCollectInductionVars_ForAllBound(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, numType, TypeA, TypeBool))
	n := Var("n", numType)
	m := Var("m", numType)
	x := Var("x", TypeA)
	// Goal: ⊢ ∀x.∀m.∀n.P(m, n, x)
	goal := core.MakeProp(ForAll(x, m, n)(P.Apply(m, n, x)))

	vars := CollectInductionVars(goal, numType)
	assert.Len(t, vars, 2)
	assert.True(t, vars[0].Equals(m))
	assert.True(t, vars[1].Equals(n))
}

func TestCollectInductionVars_FreeVar(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	// Goal: ⊢ P(n) with n free
	goal := core.MakeProp(P.Apply(n))

	vars := CollectInductionVars(goal, numType)
	assert.Len(t, vars, 1)
	assert.True(t, vars[0].Equals(n))
}

func TestCollectInductionVars_NonNumVar(t *testing.T) {
	defer goleak.VerifyNone(t)

	p := Var("p", TypeBool)
	// Goal: ⊢ p (bool-typed, not num)
	goal := core.MakeProp(p)

	vars := CollectInductionVars(goal, numType)
	assert.Empty(t, vars)
}

func TestCollectInductionVars_NilMeta(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	goal := core.MakeProp(P.Apply(n))

	vars := CollectInductionVars(goal, nil)
	assert.Nil(t, vars)
}

func TestCollectInductionVars_MixedTypes(t *testing.T) {
	defer goleak.VerifyNone(t)

	n := Var("n", numType)
	x := Var("x", TypeBool)
	R := Var("R", MakeFun(numType, MakeFun(TypeBool, TypeBool)))
	// Goal: ⊢ ∀n:num. ∀x:bool. R(n, x) — only n is num-typed
	goal := core.MakeProp(ForAll(n)(ForAll(x)(R.Apply(n).Apply(x))))

	vars := CollectInductionVars(goal, numType)
	assert.Len(t, vars, 1)
	assert.True(t, vars[0].Equals(n))
}

func TestCollectInductionVars_ForAllInHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	Q := Var("Q", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	h := Var("h", TypeBool)
	c := Var("c", TypeBool)

	// Goal: ∀n.Q(n), h ⊢ c
	// The ∀n is in a hypothesis, not the conclusion.
	// n does not appear free in c, so no induction variable should be found.
	goal := core.MakeProp(c, ForAll(n)(Q.Apply(n)), h)

	vars := CollectInductionVars(goal, numType)
	assert.Empty(t, vars, "should not find induction vars — ∀n is in hyp, not conclusion")
}

func TestTryInductionTactic_ForAll(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	Pn := P.Apply(n)

	// Goal: ⊢ ∀n:num. P(n)
	goal := core.MakeProp(ForAll(n)(Pn))

	base, step, ok := TryInductionTactic(goal, n.AssertVar(), numInductionTmpl)
	assert.True(t, ok, "TryInductionTactic should succeed")
	assert.NotNil(t, base)
	assert.NotNil(t, step)

	// Base case: ⊢ P(_0)
	P0 := P.Apply(zeroTerm)
	assert.True(t, base.Conclusion().AlphaEquals(P0),
		"base conclusion should be P(_0), got: %s", prop.PrintProp(base))

	// Step case: P(n) ⊢ P(suc(n))
	Psuc := P.Apply(ext.Apply(sucTerm, n))
	assert.True(t, step.Conclusion().AlphaEquals(Psuc),
		"step conclusion should be P(suc(n)), got: %s", prop.PrintProp(step))
	assert.True(t, step.HasHyp(Pn),
		"step should have P(n) as hypothesis")
}

func TestTryInductionTactic_FreeVar(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	Pn := P.Apply(n)

	// Goal: ⊢ P(n) with n free
	goal := core.MakeProp(Pn)

	base, step, ok := TryInductionTactic(goal, n.AssertVar(), numInductionTmpl)
	assert.True(t, ok, "TryInductionTactic should succeed on free var")
	assert.NotNil(t, base)
	assert.NotNil(t, step)

	// Base case: ⊢ P(_0)
	P0 := P.Apply(zeroTerm)
	assert.True(t, base.Conclusion().AlphaEquals(P0),
		"base conclusion should be P(_0)")

	// Step case: P(n) ⊢ P(suc(n))
	Psuc := P.Apply(ext.Apply(sucTerm, n))
	assert.True(t, step.Conclusion().AlphaEquals(Psuc),
		"step conclusion should be P(suc(n))")
}

func TestTryInductionTactic_WithHyps(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	q := Var("q", TypeBool) // hypothesis that does NOT mention n

	// Goal: q ⊢ P(n)
	// n is free in conclusion but NOT in hypothesis — valid for induction.
	goal := core.MakeProp(P.Apply(n), q)

	base, step, ok := TryInductionTactic(goal, n.AssertVar(), numInductionTmpl)
	assert.True(t, ok)

	// Hypotheses should be preserved.
	// Base: q ⊢ P(_0)
	assert.True(t, base.HasHyp(q),
		"base should preserve original hypothesis q")

	// Step: q, P(n) ⊢ P(suc(n))
	assert.True(t, step.HasHyp(q),
		"step should preserve original hypothesis q")
	assert.True(t, step.HasHyp(P.Apply(n)),
		"step should have induction hypothesis P(n)")
}

func TestTryInductionTactic_NilTemplate(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	goal := core.MakeProp(ForAll(n)(P.Apply(n)))

	_, _, ok := TryInductionTactic(goal, n.AssertVar(), nil)
	assert.False(t, ok, "should fail with nil template")
}

// TestTryDefTacticRewrite_AgreesWithApplyDefExpand verifies the
// inspect/apply consistency invariant: TryDefTacticRewrite returns ok
// iff ApplyDefExpand on a fresh GoalStackNode returns true. This is
// the contract the agent relies on — `inspect` listing a `def_expand`
// fact must mean `apply def_expand` will succeed at commit time, not
// just that some lemma-style fallback would fire.
func TestTryDefTacticRewrite_AgreesWithApplyDefExpand(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Build a const with a closed lambda definition.
	// Body: λx:A. λy:A. T  (a closed bool-valued const, no free vars)
	x := ext.Var("x", ext.TypeA)
	y := ext.Var("y", ext.TypeA)
	body := x.To(y.To(ext.WrapTerm(prop.T)))
	c := core.NewConstDef(body.Core(), "test_const_under_binder_a")

	// Case 1: goal that contains the const at top-level (under no binder).
	cTermInGoal := ext.Const(c.Meta(), c.Meta().AbsType())
	a := ext.Var("a", ext.TypeA)
	b := ext.Var("b", ext.TypeA)
	goal1 := prop.MakeProp(cTermInGoal.Apply(a, b))

	_, predicted := TryDefTacticRewrite(goal1, cTermInGoal.AssertConst())
	applied := ApplyDefExpand(CreateGoalStack(goal1), cTermInGoal.AssertConst())
	assert.Equal(t, predicted, applied,
		"top-level: TryDefTacticRewrite=%v must equal ApplyDefExpand=%v", predicted, applied)

	// Case 2: goal that contains the const under a binder (∀z. const(a, z)).
	// The rewrite engine handles binder traversal, so both should succeed.
	z := ext.Var("z", ext.TypeA)
	goal2 := prop.MakeProp(ext.ForAll(z)(cTermInGoal.Apply(a, z)))

	_, predicted2 := TryDefTacticRewrite(goal2, cTermInGoal.AssertConst())
	applied2 := ApplyDefExpand(CreateGoalStack(goal2), cTermInGoal.AssertConst())
	assert.Equal(t, predicted2, applied2,
		"under-binder: TryDefTacticRewrite=%v must equal ApplyDefExpand=%v", predicted2, applied2)
	assert.True(t, predicted2, "under-binder: rewrite must succeed (binder traversal supported)")

	// Case 3: goal that does NOT contain the const — both predicates must reject.
	P := ext.Var("P", ext.MakeFun(ext.TypeA, ext.TypeBool))
	goal3 := prop.MakeProp(P.Apply(a))
	_, predicted3 := TryDefTacticRewrite(goal3, cTermInGoal.AssertConst())
	applied3 := ApplyDefExpand(CreateGoalStack(goal3), cTermInGoal.AssertConst())
	assert.False(t, predicted3, "absent: TryDefTacticRewrite must return false when const not in goal")
	assert.False(t, applied3, "absent: ApplyDefExpand must return false when const not in goal")
}

// TestApplyDefExpand_PolymorphicCrossTypeVarInstance reproduces a
// bug discovered by the prover agent on `tailadmissible`:
// the def thm carries the const at one set of type-var instances (those
// minted when the def was traced in), the goal carries the const at a
// DIFFERENT set of instances (minted when the goal's proposition was
// traced in), and the rewrite engine's type-prefilter in
// ext/prop/eq_rewrite.go's unifyEqRewrite uses strict HolType.Equals
// (= name match), so it rejects every goal-side occurrence.
//
// Commit 0f43a4ce wired tryAdaptLemmaTypes into the PUBLIC entry points
// prover.ApplyLemma / prover.ApplyLeanRw to fix exactly this for
// cited-lemma applications, and the def_expand composite
// (ApplyDefExpand → computeDefExpandSubGoals) had missed it. This test
// pins that the composite type-adapts too, plus that _AxiomDefStep.apply
// replays correctly when the lemma-child it's closing is the adapted
// (rather than raw meta.DefThm()) form.
//
// Cross-instance setup: build the def at a fresh VarType("?def_A") and
// the goal occurrence at a fresh VarType("?goal_A"). Both names parse
// as "A" colloquially, but VarType.equalsVar(t,s) = (t == s ||
// t.name == s.name) — different names AND different pointers → strict
// inequality. The under-binder shape (∀z. const(a, z)) is included so
// the rewrite must descend through the AbsTerm, mirroring the original
// tailadmissible-under-pattern_abstraction site.
func TestApplyDefExpand_PolymorphicCrossTypeVarInstance(t *testing.T) {
	defer goleak.VerifyNone(t)

	defA := core.MakeVarType("?def_A")
	goalA := core.MakeVarType("?goal_A")

	// Def body: λx:def_A. λy:def_A. T   (closed, returns Bool)
	x := ext.Var("x", defA)
	y := ext.Var("y", defA)
	body := x.To(y.To(ext.WrapTerm(prop.T)))
	c := core.NewConstDef(body.Core(), "poly_def_const")

	// Goal: ∀z:goal_A. poly_def_const(a, z)   with a, z at goal_A.
	// ext.Const(meta, goalConstType) triggers MakeConstTerm's
	// typeSubsts branch — the const is materialized at goal_A while
	// meta.AbsType() stays at def_A.
	goalConstType := core.MakeFun(goalA, core.MakeFun(goalA, core.TypeBool()))
	cAtGoal := ext.Const(c.Meta(), goalConstType)
	a := ext.Var("a", goalA)
	z := ext.Var("z", goalA)
	goal := prop.MakeProp(ext.ForAll(z)(cAtGoal.Apply(a, z)))

	// Unadapted, ApplyDefExpand would return false: applyLeanRw's
	// inner unifyEqRewrite type-prefilter (lTypes[restLen:] vs tTypes
	// via HolType.Equals) rejects every const occurrence — the def's
	// `?def_A` literally != the goal's `?goal_A`.
	//
	// applyLeanRw (lowercase) calls tryAdaptLemmaTypes upfront on a
	// polymorphic lemma, producing an adapted def thm at goal_A.
	// _AxiomDefStep.apply then re-adapts at replay time so IsStronger
	// passes inside MakeEmptySubGoals.
	node := CreateGoalStack(goal)
	require.True(t, ApplyDefExpand(node, c),
		"ApplyDefExpand must succeed across type-var instances "+
			"(the cross-instance bug — pre-fix returned false)")

	// Both TryDefTacticRewrite (used by inspect) and the apply path
	// should agree positively.
	_, predicted := TryDefTacticRewrite(goal, c)
	assert.True(t, predicted,
		"TryDefTacticRewrite must also accept the polymorphic-cross-instance case")
}

// list_all/pattern_abstraction/casewise work on the same goal because each appears at
// TOP-LEVEL (no λ wrapping over the const head itself), so descend
// reaches them.  `tailadmissible` is the only under-λ occurrence here.
func TestApplyDefExpand_PolymorphicCrossTypeVarInstance_GoalUnderLambda(t *testing.T) {
	defer goleak.VerifyNone(t)

	defA := core.MakeVarType("?def_A_under_lambda")
	goalA := core.MakeVarType("?goal_A_under_lambda")

	// Def: c : def_A → def_A → bool. Body: λx. λy. T. Same as the existing
	// PolymorphicCrossTypeVarInstance test — the def-side setup is fine.
	x := ext.Var("x", defA)
	y := ext.Var("y", defA)
	body := x.To(y.To(ext.WrapTerm(prop.T)))
	c := core.NewConstDef(body.Core(), "poly_const_under_lambda")

	// Goal-side instance at goal_A.
	goalConstType := core.MakeFun(goalA, core.MakeFun(goalA, core.TypeBool()))
	cAtGoal := ext.Const(c.Meta(), goalConstType)

	// Construct the GOAL: place `cAtGoal(a, b)` inside a Lambda body.
	// This mirrors the live `tailadmissible(<<, λf.λa.⊤, s, t)` inside
	// `pattern_abstraction(λf. ∀s. ∀t. f(s,t) = tailadm(...))` structurally.
	//
	// Build `λaIn:goal_A. cAtGoal(aIn, bFree)` (type `goal_A → bool`),
	// then apply `wrapBool : (goal_A → bool) → bool` to it.
	aIn := ext.Var("aIn", goalA)
	bFree := ext.Var("bFree", goalA)
	innerLambda := aIn.To(cAtGoal.Apply(aIn, bFree)) // λaIn:goal_A. c(aIn, bFree)

	// Outer wrapper: `(goal_A → bool) → bool` applied to innerLambda.
	wrapBoolMeta := core.MakeConstMeta(
		"wrapBool", core.MakeFun(core.MakeFun(goalA, core.TypeBool()), core.TypeBool()))
	wrapBool := core.MakeConstTerm(wrapBoolMeta, wrapBoolMeta.AbsType())
	goal := prop.MakeProp(ext.WrapTerm(wrapBool).Apply(innerLambda).Core())

	// Sanity check: the goal really does contain the const, but only
	// under the λaIn binder.
	require.True(t, prop.ContainsConstName(goal, c.Name()),
		"premise: goal must contain the const (otherwise the test trivializes)")

	node := CreateGoalStack(goal)
	require.True(t, ApplyDefExpand(node, c),
		"ApplyDefExpand must succeed when the goal-side const occurrence "+
			"sits under a λ-binder (mimicking the live `tailadmissible` "+
			"inside `pattern_abstraction(λf. ...)`)")

	_, predicted := TryDefTacticRewrite(goal, c)
	assert.True(t, predicted,
		"TryDefTacticRewrite must agree — so `inspect` surfaces "+
			"`def_expand` as a structural fact even when the goal "+
			"occurrence is under λ")
}
