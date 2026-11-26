// witness_typing_test.go — the witness tuple's typing doors
// (witness_order.go header):
//
//  1. A polymorphic install form is typed by its tuple: each guarded
//     binder's type read against its witness's, the reading settled by
//     the one bijection that type-checks when the positional order does
//     not.
//  2. A tuple authored against the prenex habit (`∀m.∀P.` for a
//     principle stated `∀P.∀m.`) still grounds the STATED form: the
//     positional reading is ill-typed, the types settle the order, and
//     the instance's guard is discharged from the context — the whole
//     move keyless.
package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/ematch"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestWitnessTypeReading_TupleSettlesTheInstance reads
//
//	∀f:(A→B). ∀x:A. f(x) = f(x)   at   (x₀:ind, g:ind→bool)
//
// — the positional reading is ill-typed (x₀ is no function), the other
// bijection binds A ≔ ind, B ≔ bool consistently across both slots.
func TestWitnessTypeReading_TupleSettlesTheInstance(t *testing.T) {
	A, B := core.MakeVarType("A"), core.MakeVarType("B")
	f := ext.Var("f", core.MakeFun(A, B))
	x := ext.Var("x", A)
	law := prop.MakeProp(ext.ForAll(f)(ext.ForAll(x)(f.Apply(x).Eq(f.Apply(x)))).Core())

	x0 := ext.Var("x_0", TypeInd)
	g := ext.Var("g", core.MakeFun(TypeInd, core.TypeBool()))
	env, full, ok := witnessTypeReading(law, []Term{x0.Core(), g.Core()})
	require.True(t, ok, "one bijection type-checks")
	require.True(t, full)
	inst := core.PropTypeInst(law, env...)
	assert.False(t, ext.PropHasTypeVars(inst), "A and B are both read off the tuple")
	typed := witnessTypedForm(law, []Term{x0.Core(), g.Core()}, prop.MakeProp(x0.Eq(x0).Core()))
	assert.True(t, typed.AlphaEquals(inst), "the typed form is the tuple's instance, no anchor search")

	// Two witnesses of one type: the bijections disagree on nothing
	// but the order, and the reading is declined — the grounding
	// names the miss rather than the engine guessing.
	y0 := ext.Var("y_0", TypeInd)
	_, _, ok = witnessTypeReading(law, []Term{x0.Core(), y0.Core()})
	assert.False(t, ok, "no bijection type-checks: a function binder cannot take an individual")
}

// TestByWitness_PrenexOrderTupleGroundsStatedForm cites
//
//	∀g:(ind→ind). ∀P:(ind→bool). ∀c:ind. P(c) ⇒ zk(c) = g(c)
//
// at (a, g₀, P₀) — a scrambled order, as the prenex form presents
// it — on the leaf P₀(a) ⊢ zk(a) = g₀(a): the tuple is read
// (g ≔ g₀, P ≔ P₀, c ≔ a) by type, the guard P₀(a) is discharged from
// the context, and the instance closes the leaf keylessly.
func TestByWitness_PrenexOrderTupleGroundsStatedForm(t *testing.T) {
	pred := core.MakeFun(TypeInd, core.TypeBool())
	ind1 := core.MakeFun(TypeInd, TypeInd)
	g := ext.Var("g", ind1)
	P := ext.Var("P", pred)
	c := ext.Var("c", TypeInd)
	zk := ext.WrapTerm(zkConst)
	law := prop.MakeProp(ext.ForAll(g)(ext.ForAll(P)(ext.ForAll(c)(
		P.Apply(c).Imply(zk.Apply(c).Eq(g.Apply(c)))))).Core())

	g0 := ext.Var("g_0", ind1)
	P0 := ext.Var("P_0", pred)
	a := ext.Var("a", TypeInd)
	goal := prop.MakeProp(zk.Apply(a).Eq(g0.Apply(a)).Core(), P0.Apply(a).Core())

	// The guard is NAMED: By clears the ambient hyps it is not told
	// about, and the discharge reads the context the premises leave.
	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: prop.MakeProp(P0.Apply(a).Core()), Resident: true, Describe: "guard"},
		{Install: law, Witnesses: []Term{a.Core(), g0.Core(), P0.Core()}, Describe: "the law at (a, g₀, P₀) — scrambled"},
	}}
	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), spec), "the tuple grounds the stated form by type")
	assert.Empty(t, st.Proofs(), "keyless: the discharged instance is the goal")
	// What stays open is the unproved fixture law's claim obligation —
	// never the leaf.
	for _, c := range n.Children() {
		if !c.Proved() {
			assert.True(t, c.Goal.Conclusion().AlphaEquals(law.Conclusion()),
				"open child is the law's claim obligation, got %s", prop.PrintProp(c.Goal))
		}
	}
}

// TestByWitness_ConjunctiveGuardDischargedFromConjuncts: the guard of a
// grounded instance is discharged when the context SUPPLIES it — here
// conjunct by conjunct, one equation in the other orientation — which
// is decided by whether the ¬antecedent branch closes under Basic on a
// scratch copy (dischargeGuards), not by α-residency of the guard.
//
//	∀g P c. P(c) ∧ g(c) = c ⇒ zk(c) = g(c)   at (g, P, a),   P(a),  a = g(a)   ⊢  zk(a) = g(a)
//
// (g and P are bound in the law so that the fixture is closed: a free
// variable is ∀-closed at install and would take the tuple's slot.)
func TestByWitness_ConjunctiveGuardDischargedFromConjuncts(t *testing.T) {
	pred := core.MakeFun(TypeInd, core.TypeBool())
	ind1 := core.MakeFun(TypeInd, TypeInd)
	P := ext.Var("P", pred)
	g := ext.Var("g", ind1)
	c := ext.Var("c", TypeInd)
	a := ext.Var("a", TypeInd)
	zk := ext.WrapTerm(zkConst)
	law := prop.MakeProp(ext.ForAll(g)(ext.ForAll(P)(ext.ForAll(c)(
		P.Apply(c).And(g.Apply(c).Eq(c)).Imply(zk.Apply(c).Eq(g.Apply(c)))))).Core())
	goal := prop.MakeProp(zk.Apply(a).Eq(g.Apply(a)).Core(), P.Apply(a).Core(), a.Eq(g.Apply(a)).Core())

	spec := BySpec{Premises: []ByPremiseSpec{
		{Install: prop.MakeProp(P.Apply(a).Core()), Resident: true, Describe: "P(a)"},
		{Install: prop.MakeProp(a.Eq(g.Apply(a)).Core()), Resident: true, Describe: "a = g(a), the guard's equation flipped"},
		{Install: law, Witnesses: []Term{g.Core(), P.Core(), a.Core()}, Describe: "the guarded law at (g, P, a)"},
	}}
	st := newGroundByStore()
	live := groundTestEnv(t)
	st.wire(live, true)
	n := CreateGoalStack(goal)
	require.True(t, ApplyByStep(n, live, t.Context(), spec), "the guard is supplied conjunct-wise, so the instance is the goal")
	assert.Empty(t, st.Proofs(), "keyless: discharged instance closes by assumption")
	for _, ch := range n.Children() {
		if !ch.Proved() {
			assert.True(t, ch.Goal.Conclusion().AlphaEquals(law.Conclusion()),
				"open child is the law's claim obligation, got %s", prop.PrintProp(ch.Goal))
		}
	}
}

// TestClauseTypedForWitnesses_StatedOrderMappedOntoClausePrefix: a
// witnessed premise whose CLAUSE prefix orders the binders differently
// from its statement is typed by a tuple written in the STATED order —
// mapped onto the prefix by name, as the grounding reads it — even
// where two binders share a type, so that the by-type permutation
// alone would decline.
//
//	stated  ∀op:(B→B→B). M(op) ⇒ ∀R:(B→B→bool). ∀f g:(A→B). K(R, op, f, g)
//	clause  ∀R.∀op.∀f.∀g. ¬M(op) ∨ K(R, op, f, g)
//	at (op₀, R₀, f₀, g₀) on  M(op₀) ⊢ K(R₀, op₀, f₀, g₀)  over ind
//
// Measured on nat_sum.DigitSumSplit citing monoidal.Related after the
// structure door restated the law with `op` first: the tuple fit no
// adaptation positionally (f and g share a type, so no permutation),
// the premise installed at the law's own letters, and the grounding
// failed on the type mismatch.
func TestClauseTypedForWitnesses_StatedOrderMappedOntoClausePrefix(t *testing.T) {
	A, B := core.MakeVarType("A"), core.MakeVarType("B")
	opT := core.MakeFun(B, core.MakeFun(B, B))
	relT := core.MakeFun(B, core.MakeFun(B, core.TypeBool()))
	fnT := core.MakeFun(A, B)
	mMeta := core.MakeConstMeta("M_clause_typing", core.MakeFun(opT, core.TypeBool()))
	kMeta := core.MakeConstMeta("K_clause_typing",
		core.MakeFun(relT, core.MakeFun(opT, core.MakeFun(fnT, core.MakeFun(fnT, core.TypeBool())))))
	m := ext.WrapTerm(core.MakeConstTerm(mMeta, mMeta.AbsType()))
	k := ext.WrapTerm(core.MakeConstTerm(kMeta, kMeta.AbsType()))
	op, R := ext.Var("op", opT), ext.Var("R", relT)
	f, g := ext.Var("f", fnT), ext.Var("g", fnT)

	stated := prop.MakeProp(ext.ForAll(op)(m.Apply(op).Imply(
		ext.ForAll(R)(ext.ForAll(f)(ext.ForAll(g)(k.Apply(R, op, f, g)))))).Core())
	clause := prop.MakeProp(ext.ForAll(R)(ext.ForAll(op)(ext.ForAll(f)(ext.ForAll(g)(
		ext.Not(m.Apply(op).Core()).Or(k.Apply(R, op, f, g).Core()))))).Core())

	ind := TypeInd
	opI := core.MakeFun(ind, core.MakeFun(ind, ind))
	relI := core.MakeFun(ind, core.MakeFun(ind, core.TypeBool()))
	fnI := core.MakeFun(ind, ind)
	mI := ext.WrapTerm(core.MakeConstTerm(mMeta, core.MakeFun(opI, core.TypeBool())))
	kI := ext.WrapTerm(core.MakeConstTerm(kMeta,
		core.MakeFun(relI, core.MakeFun(opI, core.MakeFun(fnI, core.MakeFun(fnI, core.TypeBool()))))))
	op0, R0 := ext.Var("op_0", opI), ext.Var("R_0", relI)
	f0, g0 := ext.Var("f_0", fnI), ext.Var("g_0", fnI)
	goal := prop.MakeProp(kI.Apply(R0, op0, f0, g0).Core(), mI.Apply(op0).Core())

	// The tuple in the STATED order: op first, then R.
	wits := []Term{op0.Core(), R0.Core(), f0.Core(), g0.Core()}

	typed := clauseTypedForWitnesses(clause, wits, goal, stated)
	require.False(t, ext.PropHasTypeVars(typed), "the clause form is typed at ind: %s", prop.PrintProp(typed))
	binders, _ := ematch.StripGuardedForalls(typed.Conclusion())
	require.Len(t, binders, 4)
	assert.Equal(t, "R", string(binders[0].Name()), "the clause prefix keeps its own order")
	assert.True(t, binders[0].Type().Equals(relI))
	assert.True(t, binders[1].Type().Equals(opI))

	// Without the reference the positional reading is ill-typed, f and
	// g share a type so no permutation is attempted, and the form stays
	// at the law's own letters — the miss this test pins.
	untyped := clauseTypedForWitnesses(clause, wits, goal, nil)
	assert.True(t, ext.PropHasTypeVars(untyped), "no reference: the tuple fits no candidate")
}

// TestClauseTypedForWitnesses_StatedReadingPinsTheInstance: a witnessed
// premise's tuple fixes the instance — its witnesses' types, read
// against the stated binders — before the goal's adaptations are
// consulted.
//
//	stated = clause  ∀s:set(A). ∀t:set(B). ∀x:A. ∀y:B. K(s, t, x, y)
//	at (s₀:set(C), t₀:set(D))  on  K(t₀, s₀, y₀, x₀) ⊢ K(t₀, s₀, y₀, x₀)
//
// The goal holds K at (D, C) alone — the instance the tuple does not
// name (set_product.CrossSwap's leaf holds set_cross at (B, A) beside
// (A, B), and that adaptation is enumerated first). Before, the goal's
// adaptations alone decided the typing: the tuple fit the (B, A)
// instance permuted and the premise installed there — the instance the
// author did not write, silently (CrossSwap) — or fit nothing and the
// form stayed at the law's own letters; never the instance the tuple
// names. The tuple names (A := C, B := D), and that is the typed form,
// the tuple in place, whether or not the goal holds it — the grounding
// then names the miss.
func TestClauseTypedForWitnesses_StatedReadingPinsTheInstance(t *testing.T) {
	A, B := core.MakeVarType("A"), core.MakeVarType("B")
	set := func(elem core.HolType) core.HolType { return core.MakeFun(elem, core.TypeBool()) }
	kType := func(a, b core.HolType) core.HolType {
		return core.MakeFun(set(a), core.MakeFun(set(b), core.MakeFun(a, core.MakeFun(b, core.TypeBool()))))
	}
	kMeta := core.MakeConstMeta("K_stated_reading", kType(A, B))
	k := ext.WrapTerm(core.MakeConstTerm(kMeta, kMeta.AbsType()))
	s, tt := ext.Var("s", set(A)), ext.Var("t", set(B))
	x, y := ext.Var("x", A), ext.Var("y", B)
	stated := prop.MakeProp(ext.ForAll(s)(ext.ForAll(tt)(ext.ForAll(x)(ext.ForAll(y)(k.Apply(s, tt, x, y))))).Core())

	C, D := core.MakeVarType("C"), core.MakeVarType("D")
	s0, t0 := ext.Var("s_0", set(C)), ext.Var("t_0", set(D))
	x0, y0 := ext.Var("x_0", C), ext.Var("y_0", D)
	kSwapped := ext.WrapTerm(core.MakeConstTerm(kMeta, kType(D, C)))
	swapped := kSwapped.Apply(t0, s0, y0, x0).Core()
	goal := prop.MakeProp(swapped, swapped)

	typed := clauseTypedForWitnesses(stated, []Term{s0.Core(), t0.Core()}, goal, stated)
	binders, _ := ematch.StripGuardedForalls(typed.Conclusion())
	require.Len(t, binders, 4)
	assert.True(t, binders[0].Type().Equals(set(C)), "s is read at s₀'s type: %s", prop.PrintProp(typed))
	assert.True(t, binders[1].Type().Equals(set(D)), "t is read at t₀'s type: %s", prop.PrintProp(typed))
}
