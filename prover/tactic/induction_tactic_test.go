package tactic

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

// --- helpers ---

var (
	n    = Var("n", numType)
	nSuc = ext.Apply(suc, n)

	// ∀P n. P(_0) ∧ (∀n:num. P(n) ⇒ P(suc(n))) ⇒ P(n)
	numInductionThm = func() Thm {
		P := Var("P", MakeFun(numType, TypeBool))
		Pn := P.Apply(n)
		P0 := P.Apply(_0)
		Psuc := P.Apply(nSuc)
		return core.TestThm(ForAll(P)(ForAll(n)(P0.And(ForAll(n)(Pn.Imply(Psuc))).Imply(Pn))))
	}()

	numInductionTmpl = func() *InductionTemplate {
		t, err := AnalyzeInductionPrinciple(numInductionThm)
		if err != nil {
			panic(err)
		}
		return t
	}()
)

// numInductTactic is a test helper that wraps GeneralInductionTactic
// with the num template (a template carries all required state), so a
// test calls it per goal.
func numInductTactic(inductVar VarTerm) Tactic {
	return GeneralInductionTactic(inductVar, numInductionTmpl)
}

func TestInductionTactic_VarInHyp_Reconstruction(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	Q := Var("Q", MakeFun(numType, TypeBool))

	// Goal: Q(n) ⊢ P(n)
	goal := core.MakeProp(P.Apply(n), Q.Apply(n))

	tac := numInductTactic(n.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(_0).Or(Not(Q.Apply(_0)))))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(P.Apply(nSuc).Or(Not(Q.Apply(nSuc))), P.Apply(n).Or(Not(Q.Apply(n)))))
	assertSubGoals(t, subGoals, goal)
}

func TestInductionTactic_Reconstruction(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))

	// Goal: ⊢ ∀n:num. P(n)
	goal := core.MakeProp(ForAll(n)(P.Apply(n)))

	tac := numInductTactic(n.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(_0)))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(P.Apply(nSuc), P.Apply(n)))
	assertSubGoals(t, subGoals, goal)
}

func TestInductionTactic_Reconstruction_FreeVar(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))

	// Goal: ⊢ P(n) with n free
	goal := core.MakeProp(P.Apply(n))

	tac := numInductTactic(n.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(_0)))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(P.Apply(nSuc), P.Apply(n)))
	assertSubGoals(t, subGoals, goal)
}

func TestInductionTactic_Reconstruction_VarInHypWithIrrelevantHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	Q := Var("Q", MakeFun(numType, TypeBool))
	h := Var("h", TypeBool) // irrelevant hyp, does not mention n

	// Goal: Q(n), h ⊢ P(n)
	goal := core.MakeProp(P.Apply(n), Q.Apply(n), h)

	tac := numInductTactic(n.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(_0).Or(Not(Q.Apply(_0))), h))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(P.Apply(nSuc).Or(Not(Q.Apply(nSuc))), P.Apply(n).Or(Not(Q.Apply(n))), h))
	assertSubGoals(t, subGoals, goal)
}

func TestInductionTactic_Reconstruction_VarOnlyInHyp_FalseConclusion(t *testing.T) {
	defer goleak.VerifyNone(t)

	Q := Var("Q", MakeFun(numType, TypeBool))
	h := Var("h", TypeBool) // irrelevant hyp

	// Goal: Q(n), h ⊢ ⊥
	// n appears only in hypothesis Q(n), not in conclusion.
	// After moving Q(n) to concl side: h ⊢ ¬Q(n)
	// Induction on n in ¬Q(n).
	goal := core.MakeProp(F, Q.Apply(n), h)

	tac := numInductTactic(n.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals, "should succeed — n appears in moved hyp")
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(Not(Q.Apply(_0)), h))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(Not(Q.Apply(nSuc)), Not(Q.Apply(n)), h))
	assertSubGoals(t, subGoals, goal)
}

func TestInductionTactic_ForAllNonNumThenNum(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, MakeFun(TypeA, TypeBool)))
	x := Var("x", TypeA)

	// Goal: ⊢ ∀x:A. ∀n:num. P(n, x)
	// The outermost ∀ is over x (not num), so it should NOT be stripped.
	// Induction on n should produce:
	//   base: ⊢ ∀x:A. P(_0, x)
	//   step: ∀x:A. P(n, x) ⊢ ∀x:A. P(suc(n), x)
	goal := core.MakeProp(ForAll(x)(ForAll(n)(P.Apply(n).Apply(x))))

	tac := numInductTactic(n.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals, "should succeed — n is free in ∀x.∀n.P(n,x)")
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(ForAll(x)(P.Apply(_0, x))))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(ForAll(x)(P.Apply(nSuc, x)), ForAll(x)(P.Apply(n, x))))
	assertSubGoals(t, subGoals, goal)
}

func TestInductionTactic_Reconstruction_ForAllInConclWithFreeVarInHyp(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	Q := Var("Q", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	m := Var("m", numType)
	h := Var("h", TypeBool)

	// Goal: Q(n), h ⊢ ∀m.P(m)
	// Use distinct names n vs m to ensure the test is not accidentally
	// correct due to name collision. n is free in Q(n) (hyp); m is bound
	// in ∀m.P(m) (concl). Induction should be on n (the free var),
	// treating ∀m.P(m) as an opaque conclusion.
	goal := core.MakeProp(ForAll(m)(P.Apply(m)), Q.Apply(n), h)

	tac := numInductTactic(n.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals, "should succeed")
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(ForAll(m)(P.Apply(m)).Or(Not(Q.Apply(_0))), h))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(
			ForAll(m)(P.Apply(m)).Or(Not(Q.Apply(nSuc))),
			ForAll(m)(P.Apply(m)).Or(Not(Q.Apply(n))),
			h))
	assertSubGoals(t, subGoals, goal)
}

// Regression: when inductVar is an inner forall-bound variable whose name
// differs from num_induction's "n", ReorderForAll panicked because the
// result's outermost bound var was "n" instead of the original var name.
func TestInductionTactic_InnerForAllVar_DifferentName(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", numType)
	x := Var("x", numType) // inner var, name ≠ "n"
	P := Var("P", MakeFun(numType, MakeFun(numType, TypeBool)))

	// Goal: ⊢ ∀m:num. ∀x:num. P(m, x)
	// Induction on x (inner var). The result should be reordered to match
	// the original ∀m.∀x order.
	goal := core.MakeProp(ForAll(m)(ForAll(x)(P.Apply(m).Apply(x))))

	tac := numInductTactic(x.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals, "should succeed")
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(ForAll(m)(P.Apply(m).Apply(_0))))
	xSuc := ext.Apply(suc, x)
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(ForAll(m)(P.Apply(m).Apply(xSuc)), ForAll(m)(P.Apply(m).Apply(x))))
	assertSubGoals(t, subGoals, goal)
}

func TestInductionTactic_MultipleHypsWithVar(t *testing.T) {
	defer goleak.VerifyNone(t)

	P := Var("P", MakeFun(numType, TypeBool))
	Q := Var("Q", MakeFun(numType, TypeBool))
	R := Var("R", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	h := Var("h", TypeBool)

	// Goal: P(n), Q(n), h ⊢ R(n)
	// Both P(n) and Q(n) contain the induction var; h and c do not.
	goal := core.MakeProp(R.Apply(n), P.Apply(n), Q.Apply(n), h)

	tac := numInductTactic(n.AssertVar())

	// Full reconstruction
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(
			R.Apply(_0).Or(Not(P.Apply(_0))).Or(Not(Q.Apply(_0))),
			h))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(
			R.Apply(nSuc).Or(Not(P.Apply(nSuc))).Or(Not(Q.Apply(nSuc))),
			R.Apply(n).Or(Not(P.Apply(n))).Or(Not(Q.Apply(n))),
			h))
	assertSubGoals(t, subGoals, goal)
}

// Regression: if a non-induction quantified variable is named "n", the
// beta/rewrite path through num_induction can freshen it while reordering the
// quantifiers for a different induction variable. ReorderForAll must handle
// alpha-equivalent variable lists, not require exact binder names.
func TestInductionTactic_ReorderForAll_AllowsAlphaRenamedRestVars(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", numType)
	n := Var("n", numType)
	p := Var("p", numType)
	P := Var("P", MakeFun(numType, MakeFun(numType, MakeFun(numType, TypeBool))))

	goal := core.MakeProp(ForAll(m)(ForAll(n)(ForAll(p)(
		P.Apply(m).Apply(n).Apply(p)))))

	tac := numInductTactic(p.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals, "should succeed")
	assert.Equal(t, 2, subGoals.Size())

	pSuc := ext.Apply(suc, p)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(ForAll(m)(ForAll(n)(P.Apply(m).Apply(n).Apply(_0)))))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(
			ForAll(m)(ForAll(n)(P.Apply(m).Apply(n).Apply(pSuc))),
			ForAll(m)(ForAll(n)(P.Apply(m).Apply(n).Apply(p))),
		))
	assertSubGoals(t, subGoals, goal)
}

// Regression: induction on a middle forall-bound variable must preserve which
// occurrences belong to the induction variable versus later bound variables,
// even when both appear multiple times in asymmetric positions.
func TestInductionTactic_MiddleForAllVar_DoesNotSwapCapturedVars(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", numType)
	k := Var("k", numType)
	n := Var("n", numType)
	f := Var("f", MakeFun(numType, numType, numType))
	g := Var("g", MakeFun(numType, numType, numType))
	h := Var("h", MakeFun(numType, numType, numType))
	u := Var("u", MakeFun(numType, numType, numType))

	kSuc := ext.Apply(suc, k)
	nSuc := ext.Apply(suc, n)

	body := m.Eq(m).
		And(f.Apply(kSuc, n).Eq(g.Apply(k, n))).
		And(h.Apply(k, nSuc).Eq(u.Apply(k, n)))

	goal := core.MakeProp(ForAll(m)(ForAll(k)(ForAll(n)(body))))

	tac := numInductTactic(k.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals, "should succeed")
	assert.Equal(t, 2, subGoals.Size())

	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(ForAll(m)(ForAll(n)(
			m.Eq(m).
				And(f.Apply(ext.Apply(suc, _0), n).Eq(g.Apply(_0, n))).
				And(h.Apply(_0, ext.Apply(suc, n)).Eq(u.Apply(_0, n))),
		))))

	stepBody := m.Eq(m).
		And(f.Apply(ext.Apply(suc, ext.Apply(suc, k)), n).Eq(g.Apply(ext.Apply(suc, k), n))).
		And(h.Apply(ext.Apply(suc, k), ext.Apply(suc, n)).Eq(u.Apply(ext.Apply(suc, k), n)))
	indHypBody := m.Eq(m).
		And(f.Apply(kSuc, n).Eq(g.Apply(k, n))).
		And(h.Apply(k, nSuc).Eq(u.Apply(k, n)))

	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(
			ForAll(m)(ForAll(n)(stepBody)),
			ForAll(m)(ForAll(n)(indHypBody)),
		))
	assertSubGoals(t, subGoals, goal)
}

// Regression: the induction variable may come from serialized proof data, so
// it can be equal-by-name/type to the goal binder without being the same
// pointer. Reconstruction must rebind to the actual goal binder before
// building the induction theorem instantiation.
func TestInductionTactic_MiddleForAllVar_EquivalentExternalVar(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", numType)
	kGoal := Var("k", numType)
	n := Var("n", numType)
	kExternal := Var("k", numType) // same name/type, different instance
	f := Var("f", MakeFun(numType, numType, numType))
	g := Var("g", MakeFun(numType, numType, numType))
	h := Var("h", MakeFun(numType, numType, numType))
	u := Var("u", MakeFun(numType, numType, numType))

	body := m.Eq(m).
		And(f.Apply(ext.Apply(suc, kGoal), n).Eq(g.Apply(kGoal, n))).
		And(h.Apply(kGoal, ext.Apply(suc, n)).Eq(u.Apply(kGoal, n)))

	goal := core.MakeProp(ForAll(m)(ForAll(kGoal)(ForAll(n)(body))))

	tac := numInductTactic(kExternal.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals, "should succeed with an equivalent external var")
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
}

func TestInductionTactic_ReconstructFromEquivalentSubgoalTheorems(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", numType)
	k := Var("k", numType)
	n := Var("n", numType)
	f := Var("f", MakeFun(numType, numType, numType))
	g := Var("g", MakeFun(numType, numType, numType))
	h := Var("h", MakeFun(numType, numType, numType))
	u := Var("u", MakeFun(numType, numType, numType))

	body := m.Eq(m).
		And(f.Apply(ext.Apply(suc, k), n).Eq(g.Apply(k, n))).
		And(h.Apply(k, ext.Apply(suc, n)).Eq(u.Apply(k, n)))
	goal := core.MakeProp(ForAll(m)(ForAll(k)(ForAll(n)(body))))

	tac := numInductTactic(k.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())

	m1 := Var("m", numType)
	n1 := Var("n", numType)
	k1 := Var("k", numType)

	baseEquivalent := core.TestThm(
		ForAll(m1)(ForAll(n1)(
			m1.Eq(m1).
				And(f.Apply(ext.Apply(suc, _0), n1).Eq(g.Apply(_0, n1))).
				And(h.Apply(_0, ext.Apply(suc, n1)).Eq(u.Apply(_0, n1))),
		)))
	stepEquivalent := core.TestThm(
		ForAll(m1)(ForAll(n1)(
			m1.Eq(m1).
				And(f.Apply(ext.Apply(suc, ext.Apply(suc, k1)), n1).Eq(g.Apply(ext.Apply(suc, k1), n1))).
				And(h.Apply(ext.Apply(suc, k1), ext.Apply(suc, n1)).Eq(u.Apply(ext.Apply(suc, k1), n1))),
		)),
		ForAll(m1)(ForAll(n1)(
			m1.Eq(m1).
				And(f.Apply(ext.Apply(suc, k1), n1).Eq(g.Apply(k1, n1))).
				And(h.Apply(k1, ext.Apply(suc, n1)).Eq(u.Apply(k1, n1))),
		)),
	)

	reconstructed := subGoals.Reconstruct(baseEquivalent, stepEquivalent)
	assert.True(t, reconstructed.AlphaEquals(goal))
}

func TestInductionTactic_PrimedMiddleForAllVar_EquivalentSubgoalTheorems(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", numType)
	kPrime := Var("kʹ", numType)
	n := Var("n", numType)
	f := Var("f", MakeFun(numType, numType, numType))
	g := Var("g", MakeFun(numType, numType, numType))
	h := Var("h", MakeFun(numType, numType, numType))
	u := Var("u", MakeFun(numType, numType, numType))

	body := m.Eq(m).
		And(f.Apply(ext.Apply(suc, kPrime), n).Eq(g.Apply(kPrime, n))).
		And(h.Apply(kPrime, ext.Apply(suc, n)).Eq(u.Apply(kPrime, n)))
	goal := core.MakeProp(ForAll(m)(ForAll(kPrime)(ForAll(n)(body))))

	tac := numInductTactic(Var("kʹ", numType).AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())

	m1 := Var("m", numType)
	n1 := Var("n", numType)
	k1 := Var("kʹ", numType)

	baseEquivalent := core.TestThm(
		ForAll(m1)(ForAll(n1)(
			m1.Eq(m1).
				And(f.Apply(ext.Apply(suc, _0), n1).Eq(g.Apply(_0, n1))).
				And(h.Apply(_0, ext.Apply(suc, n1)).Eq(u.Apply(_0, n1))),
		)))
	stepEquivalent := core.TestThm(
		ForAll(m1)(ForAll(n1)(
			m1.Eq(m1).
				And(f.Apply(ext.Apply(suc, ext.Apply(suc, k1)), n1).Eq(g.Apply(ext.Apply(suc, k1), n1))).
				And(h.Apply(ext.Apply(suc, k1), ext.Apply(suc, n1)).Eq(u.Apply(ext.Apply(suc, k1), n1))),
		)),
		ForAll(m1)(ForAll(n1)(
			m1.Eq(m1).
				And(f.Apply(ext.Apply(suc, k1), n1).Eq(g.Apply(k1, n1))).
				And(h.Apply(k1, ext.Apply(suc, n1)).Eq(u.Apply(k1, n1))),
		)),
	)

	reconstructed := subGoals.Reconstruct(baseEquivalent, stepEquivalent)
	assert.True(t, reconstructed.AlphaEquals(goal))
}

func TestInductionTactic_PrimedMiddleForAllVar_Reconstruction(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := Var("m", numType)
	kPrime := Var("kʹ", numType)
	n := Var("n", numType)
	f := Var("f", MakeFun(numType, numType, numType))
	g := Var("g", MakeFun(numType, numType, numType))
	h := Var("h", MakeFun(numType, numType, numType))
	u := Var("u", MakeFun(numType, numType, numType))

	body := m.Eq(m).
		And(f.Apply(ext.Apply(suc, kPrime), n).Eq(g.Apply(kPrime, n))).
		And(h.Apply(kPrime, ext.Apply(suc, n)).Eq(u.Apply(kPrime, n)))
	goal := core.MakeProp(ForAll(m)(ForAll(kPrime)(ForAll(n)(body))))

	tac := numInductTactic(kPrime.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertSubGoals(t, subGoals, goal)
}

// When the goal's concl already contains ¬h as a literal disjunct,
// MoveHypsToConcl appends a second copy of ¬h to the right. The
// reconstruct closure must move the *appended* copy back, not the
// pre-existing one, to keep the reconstructed concl α-equal to the
// original goal's concl.
func TestInductionTactic_HypNegationAlreadyInConcl(t *testing.T) {
	defer goleak.VerifyNone(t)

	Q := Var("Q", MakeFun(numType, TypeBool))
	R := Var("R", MakeFun(numType, TypeBool))

	// Goal: Q(n) ⊢ ¬Q(n) ∨ R(n)
	// — concl already contains ¬Q(n) as a literal disjunct.
	goal := core.MakeProp(Not(Q.Apply(n)).Or(R.Apply(n)), Q.Apply(n))

	tac := numInductTactic(n.AssertVar())
	subGoals := tac(goal)
	assert.NotNil(t, subGoals, "should not panic on hyp-negation-in-concl shape")
	assert.Equal(t, 2, subGoals.Size())
	// Base case: substitute _0 for n in the moved concl
	// (¬Q(n) ∨ R(n)) ∨ ¬Q(n).
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(Not(Q.Apply(_0)).Or(R.Apply(_0)).Or(Not(Q.Apply(_0)))))
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(
			Not(Q.Apply(nSuc)).Or(R.Apply(nSuc)).Or(Not(Q.Apply(nSuc))),
			Not(Q.Apply(n)).Or(R.Apply(n)).Or(Not(Q.Apply(n)))))
	assertSubGoals(t, subGoals, goal)
}

// --- helpers: per-type principle scaffolding shared by tests ---

func listType(elem core.HolType) core.HolType {
	return core.MakeCompositeType(core.MakeMetaType("list", 1), elem)
}

func optionType(elem core.HolType) core.HolType {
	return core.MakeCompositeType(core.MakeMetaType("option", 1), elem)
}

// makeListInductionThm constructs `list_induction` for the element
// type A used by these tests:
//
//	∀P l. P([]) ∧ (∀h t. P(t) ⇒ P(cons h t)) ⇒ P(l)
func makeListInductionThm(elem core.HolType) (
	Thm, VarTerm, ConstTerm, ConstTerm,
) {
	lt := listType(elem)
	nilMeta := core.MakeConstMeta("nil", lt)
	consMeta := core.MakeConstMeta("cons", MakeFun(elem, MakeFun(lt, lt)))
	nilT := core.MakeConstTerm(nilMeta, lt)
	consT := core.MakeConstTerm(consMeta, MakeFun(elem, MakeFun(lt, lt)))
	P := Var("P", MakeFun(lt, TypeBool))
	l := Var("l", lt)
	h := Var("h", elem)
	t := Var("t", lt)
	Pl := P.Apply(l)
	Pnil := P.Apply(nilT)
	Pt := P.Apply(t)
	Pcons := P.Apply(ext.Apply(consT, h, t))
	step := ForAll(h)(ForAll(t)(Pt.Imply(Pcons)))
	thm := core.TestThm(ForAll(P)(ForAll(l)(Pnil.And(step).Imply(Pl))))
	return thm, l.AssertVar(), nilT, consT
}

// makeOptionInductionThm constructs `option_induction`:
//
//	∀P o. P(NONE) ∧ (∀a. P(SOME a)) ⇒ P(o)
//
// Note: no IH on the SOME case (a's type is the element type, not the
// inductive type).
func makeOptionInductionThm(elem core.HolType) (
	Thm, VarTerm, ConstTerm, ConstTerm,
) {
	ot := optionType(elem)
	noneMeta := core.MakeConstMeta("none", ot)
	someMeta := core.MakeConstMeta("some", MakeFun(elem, ot))
	noneT := core.MakeConstTerm(noneMeta, ot)
	someT := core.MakeConstTerm(someMeta, MakeFun(elem, ot))
	P := Var("P", MakeFun(ot, TypeBool))
	o := Var("o", ot)
	a := Var("a", elem)
	Po := P.Apply(o)
	Pnone := P.Apply(noneT)
	Psome := P.Apply(ext.Apply(someT, a))
	thm := core.TestThm(ForAll(P)(ForAll(o)(Pnone.And(ForAll(a)(Psome)).Imply(Po))))
	return thm, o.AssertVar(), noneT, someT
}

// --- analyzer tests ---

func TestAnalyzeInductionPrinciple_Num(t *testing.T) {
	defer goleak.VerifyNone(t)
	tmpl, err := AnalyzeInductionPrinciple(numInductionThm)
	assert.NoError(t, err)
	assert.NotNil(t, tmpl)
	assert.Equal(t, 2, len(tmpl.Cases))
	assert.True(t, tmpl.IndexType.Equals(numType))
	// Base: no args, no rec.
	assert.Empty(t, tmpl.Cases[0].Args)
	assert.Empty(t, tmpl.Cases[0].RecArgIndices)
	// Step: 1 arg, 1 rec, constructor = suc(arg).
	assert.Equal(t, 1, len(tmpl.Cases[1].Args))
	assert.Equal(t, []int{0}, tmpl.Cases[1].RecArgIndices)
}

func TestAnalyzeInductionPrinciple_List(t *testing.T) {
	defer goleak.VerifyNone(t)
	thm, _, _, _ := makeListInductionThm(core.TypeA())
	tmpl, err := AnalyzeInductionPrinciple(thm)
	assert.NoError(t, err)
	assert.NotNil(t, tmpl)
	assert.Equal(t, 2, len(tmpl.Cases))
	// nil: no args, no rec.
	assert.Empty(t, tmpl.Cases[0].Args)
	assert.Empty(t, tmpl.Cases[0].RecArgIndices)
	// cons: 2 args (h, t), 1 rec (t at index 1).
	assert.Equal(t, 2, len(tmpl.Cases[1].Args))
	assert.Equal(t, []int{1}, tmpl.Cases[1].RecArgIndices)
}

func TestAnalyzeInductionPrinciple_Option(t *testing.T) {
	defer goleak.VerifyNone(t)
	thm, _, _, _ := makeOptionInductionThm(core.TypeA())
	tmpl, err := AnalyzeInductionPrinciple(thm)
	assert.NoError(t, err)
	assert.NotNil(t, tmpl)
	assert.Equal(t, 2, len(tmpl.Cases))
	// NONE: no args, no rec.
	assert.Empty(t, tmpl.Cases[0].Args)
	assert.Empty(t, tmpl.Cases[0].RecArgIndices)
	// SOME: 1 arg, no rec (arg is element type, not option).
	assert.Equal(t, 1, len(tmpl.Cases[1].Args))
	assert.Empty(t, tmpl.Cases[1].RecArgIndices)
}

func TestAnalyzeInductionPrinciple_BadConclusion(t *testing.T) {
	defer goleak.VerifyNone(t)
	// `∀P n. P(_0) ⇒ ⊤` — the consequent isn't `P(x)`.
	P := Var("P", MakeFun(numType, TypeBool))
	thm := core.TestThm(ForAll(P)(ForAll(n)(P.Apply(_0).Imply(ext.T))))
	_, err := AnalyzeInductionPrinciple(thm)
	assert.Error(t, err)
}

// A principle is stated closed: the sequent spelling of the same
// theorem, its cases left of ⊢, is refused, naming the form.
func TestAnalyzeInductionPrinciple_RefusesSequent(t *testing.T) {
	defer goleak.VerifyNone(t)
	P := Var("P", MakeFun(numType, TypeBool))
	Pn := P.Apply(n)
	thm := core.TestThm(Pn, P.Apply(_0), ForAll(n)(Pn.Imply(P.Apply(nSuc))))
	_, err := AnalyzeInductionPrinciple(thm)
	if assert.Error(t, err) {
		assert.Contains(t, err.Error(), "states a sequent")
	}
}

// The prefix binds the predicate and the index and nothing else: a
// parameter bound before them is not an induction principle's.
func TestAnalyzeInductionPrinciple_PrefixBindsOnlyPredicateAndIndex(t *testing.T) {
	defer goleak.VerifyNone(t)
	P := Var("P", MakeFun(numType, TypeBool))
	m := Var("m", numType)
	Pn := P.Apply(n)
	body := P.Apply(_0).And(ForAll(n)(Pn.Imply(P.Apply(nSuc)))).Imply(Pn)
	thm := core.TestThm(ForAll(m)(ForAll(P)(ForAll(n)(body))))
	_, err := AnalyzeInductionPrinciple(thm)
	if assert.Error(t, err) {
		assert.Contains(t, err.Error(), "binds exactly its predicate")
	}
}

// --- tactic-via-template tests ---

func TestListInduction_Reconstruction_FreeVar(t *testing.T) {
	defer goleak.VerifyNone(t)
	thm, l, nilT, consT := makeListInductionThm(core.TypeA())
	tmpl, err := AnalyzeInductionPrinciple(thm)
	assert.NoError(t, err)

	lt := listType(core.TypeA())
	P := Var("P", MakeFun(lt, TypeBool))
	// Goal: ⊢ P(l)
	goal := core.MakeProp(P.Apply(l))

	tac := GeneralInductionTactic(l, tmpl)
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())

	// child 0: ⊢ P(nil)
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(P.Apply(nilT)))
	// child 1: P(l) ⊢ P(cons h l)   — primary rec arg renamed to inductVar l.
	h := Var("h", core.TypeA())
	consHL := ext.Apply(consT, h, l)
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(P.Apply(consHL), P.Apply(l)))
	assertSubGoals(t, subGoals, goal)
}

func TestListInduction_Reconstruction_UnivQuantified(t *testing.T) {
	defer goleak.VerifyNone(t)
	thm, l, nilT, consT := makeListInductionThm(core.TypeA())
	tmpl, err := AnalyzeInductionPrinciple(thm)
	assert.NoError(t, err)

	lt := listType(core.TypeA())
	P := Var("P", MakeFun(lt, TypeBool))
	// Goal: ⊢ ∀l:(A)list. P(l)
	goal := core.MakeProp(ForAll(l)(P.Apply(l)))

	tac := GeneralInductionTactic(l, tmpl)
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(P.Apply(nilT)))
	h := Var("h", core.TypeA())
	consHL := ext.Apply(consT, h, l)
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(P.Apply(consHL), P.Apply(l)))
	assertSubGoals(t, subGoals, goal)
}

func TestListInduction_VarInHyp_MovesToConcl(t *testing.T) {
	defer goleak.VerifyNone(t)
	thm, l, nilT, consT := makeListInductionThm(core.TypeA())
	tmpl, err := AnalyzeInductionPrinciple(thm)
	assert.NoError(t, err)

	lt := listType(core.TypeA())
	P := Var("P", MakeFun(lt, TypeBool))
	Q := Var("Q", MakeFun(lt, TypeBool))
	// Goal: Q(l) ⊢ P(l) — should move Q(l) to concl as disjunct.
	goal := core.MakeProp(P.Apply(l), Q.Apply(l))

	tac := GeneralInductionTactic(l, tmpl)
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0),
		MakeProp(P.Apply(nilT).Or(Not(Q.Apply(nilT)))))
	h := Var("h", core.TypeA())
	consHL := ext.Apply(consT, h, l)
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(
			P.Apply(consHL).Or(Not(Q.Apply(consHL))),
			P.Apply(l).Or(Not(Q.Apply(l)))))
	assertSubGoals(t, subGoals, goal)
}

func TestOptionInduction_Reconstruction(t *testing.T) {
	defer goleak.VerifyNone(t)
	thm, o, noneT, someT := makeOptionInductionThm(core.TypeA())
	tmpl, err := AnalyzeInductionPrinciple(thm)
	assert.NoError(t, err)

	ot := optionType(core.TypeA())
	P := Var("P", MakeFun(ot, TypeBool))
	// Goal: ⊢ P(o)
	goal := core.MakeProp(P.Apply(o))

	tac := GeneralInductionTactic(o, tmpl)
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())
	assertPropAlphaEqual(t, subGoals.ChildGoal(0), MakeProp(P.Apply(noneT)))
	a := Var("a", core.TypeA())
	assertPropAlphaEqual(t, subGoals.ChildGoal(1),
		MakeProp(P.Apply(ext.Apply(someT, a))))
	assertSubGoals(t, subGoals, goal)
}

// Regression: when the goal already contains a free variable named
// like the principle's non-rec arg (e.g. goal has a free `h` and
// list_induction's cons case has bound `h`), the case arg must be
// freshened to avoid collision.
func TestListInduction_NonRecArgFreshening(t *testing.T) {
	defer goleak.VerifyNone(t)
	thm, l, _, consT := makeListInductionThm(core.TypeA())
	tmpl, err := AnalyzeInductionPrinciple(thm)
	assert.NoError(t, err)

	lt := listType(core.TypeA())
	P := Var("P", MakeFun(lt, MakeFun(core.TypeA(), TypeBool)))
	h := Var("h", core.TypeA()) // already free in goal
	// Goal: ⊢ P(l, h)
	goal := core.MakeProp(P.Apply(l, h))

	tac := GeneralInductionTactic(l, tmpl)
	subGoals := tac(goal)
	assert.NotNil(t, subGoals)
	assert.Equal(t, 2, subGoals.Size())

	// child 1's cons-bound `h` must NOT alias the goal's `h`. So the
	// step's conclusion is P(cons hʹ l, h) with hʹ a fresh variant.
	// NextName cycles `h → aʹ` (alphabetic-neighbor
	// convention), so the actual fresh name is "aʹ".
	step := subGoals.ChildGoal(1)
	assert.True(t, step.HasFreeName("h"), "goal's h is still free in step")
	hFresh := Var("aʹ", core.TypeA())
	consApplied := ext.Apply(consT, hFresh, l)
	expectedStep := MakeProp(
		P.Apply(consApplied, h),
		P.Apply(l, h),
	)
	assertPropAlphaEqual(t, step, expectedStep)
	assertSubGoals(t, subGoals, goal)
}
