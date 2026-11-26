// induction_test.go — ByInduction's obligation reader (induction.go).
//
// The unit under test is inductionObligations: given a principle's
// statement and the witnesses a cite grounds it at, what does each Case
// body have to prove? Everything else about ByInduction is the ordinary
// Have/By machinery covered elsewhere.

package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// obligationTexts runs the reader and prints what it produced, so a
// test states the obligations as a person reads them. The goal steers
// only a type variable the tuple leaves open; these tuples leave none,
// so the principle itself serves as the sequent.
func obligationTexts(t *testing.T, principle Prop, want int, witnesses ...TermLike) []string {
	t.Helper()
	got := inductionObligations(NewScript(makeStepTestEnv()), MakeFact(principle).At(witnesses...), want, principle)
	out := make([]string, len(got))
	for i, o := range got {
		out[i] = ext.PrintTerm(o.Conclusion())
	}
	return out
}

// numInductionImplForm is num_induction as a headline states it
// — the ⇒-form a proof CITES, as opposed to the sequent form the
// induction tactic analyzes:
//
//	∀P. P(0) ∧ (∀n. P(n) ⇒ P(suc n)) ⇒ ∀n. P(n)
//
// Note `n` is bound TWICE — once in the step, once in the conclusion.
// That is what denies the statement a name-addressable slot map and
// sends peano's cites through the positional path, where the grounding
// permutes an ill-typed tuple by type. See TestInductionObligations_
// WitnessOrderIrrelevant.
func numInductionImplForm() Prop {
	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	step := ForAll(n)(P.Apply(n).Imply(P.Apply(ext.Apply(sucTerm, n))))
	return core.MakeProp(ForAll(P)(P.Apply(zeroTerm).And(step).Imply(ForAll(n)(P.Apply(n)))))
}

// TestInductionObligations_ReadsCasesAtThePredicate: the base case and
// the step case come back as the principle's own cases with the
// predicate substituted and the resulting redex reduced — which is what
// spares the author the Sprintf that would otherwise state them.
func TestInductionObligations_ReadsCasesAtThePredicate(t *testing.T) {
	R := Var("R", MakeFun(numType, TypeBool))
	u := Var("u", numType)
	// λu. R(suc u) — a predicate with a body, so β-reduction is visible.
	pred := u.To(R.Apply(ext.Apply(sucTerm, u)))
	k := Var("k", numType)

	got := obligationTexts(t, numInductionImplForm(), 2, pred, k)
	require.Len(t, got, 2)
	require.Equal(t, ext.PrintTerm(R.Apply(ext.Apply(sucTerm, zeroTerm))), got[0],
		"the base case is the predicate at 0, β-reduced")
	require.Contains(t, got[1], "suc", "the step case is the principle's own ∀-quantified step")
	require.NotContains(t, got[1], "λ", "no un-reduced application survives into an obligation")
}

// TestInductionObligations_PremisesAreNoCases: a principle in the
// standard form states its cases and its premises in one antecedent —
// `∀P n. P(0) ∧ (∀n. P(n) ⇒ P(suc n)) ∧ n = n ⇒ P(n)`. The cases are the
// hypotheses that mention P; `n = n`, about the index alone, is a
// premise the terminal discharges, so a cite grounded at the predicate
// alone reads two obligations and never reaches the index.
func TestInductionObligations_PremisesAreNoCases(t *testing.T) {
	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	step := ForAll(n)(P.Apply(n).Imply(P.Apply(ext.Apply(sucTerm, n))))
	premise := ext.WrapTerm(n).Eq(n)
	principle := core.MakeProp(ForAll(P, n)(P.Apply(zeroTerm).And(step).And(premise).Imply(P.Apply(n))))
	R := Var("R", MakeFun(numType, TypeBool))

	got := obligationTexts(t, principle, 2, R)
	require.Len(t, got, 2)
	assert.Equal(t, ext.PrintTerm(R.Apply(zeroTerm)), got[0])
	assert.NotContains(t, got[1], "=", "the premise about the index is no obligation")
}

// TestInductionObligations_WitnessOrderIrrelevant is the regression
// test for the discovery that a cite's witness order is NOT a fixed
// convention. `sets/finite_set` writes `At(FiniteInduct, pred, point)`
// and `nat_num/peano` writes `At(Induction, point, pred)`, both
// correctly — the second statement binds one name twice, so its cite
// falls through to positional order against the install prefix, and
// the grounding permutes the ill-typed tuple by type. The reader makes
// the SAME reading the grounding makes, so the obligations do not
// depend on which spelling the citing proof used.
func TestInductionObligations_WitnessOrderIrrelevant(t *testing.T) {
	R := Var("R", MakeFun(numType, TypeBool))
	u := Var("u", numType)
	pred := u.To(R.Apply(u))
	k := Var("k", numType)
	principle := numInductionImplForm()

	predFirst := obligationTexts(t, principle, 2, pred, k)
	pointFirst := obligationTexts(t, principle, 2, k, pred)
	require.Equal(t, predFirst, pointFirst,
		"an ill-typed positional reading is permuted by type, so either witness order reads the same obligations")
}

// TestInductionObligations_GuardedConclusion: an inductive definition's
// rule induction guards its conclusion (`∀a. F(a) ⇒ P(a)`) and binds
// the index INSIDE it. The guard is the terminal By's business; it must
// not leak into the obligations.
func TestInductionObligations_GuardedConclusion(t *testing.T) {
	setType := MakeFun(TypeA, TypeBool)
	P := Var("P", MakeFun(setType, TypeBool))
	F := Var("F", MakeFun(setType, TypeBool))
	ins := Var("ins", MakeFun(TypeA, MakeFun(setType, setType)))
	e := Var("e", setType)
	x, s, a := Var("x", TypeA), Var("s", setType), Var("a", setType)

	step := ForAll(x)(ForAll(s)(P.Apply(s).Imply(P.Apply(ext.Apply(ins, x, s)))))
	concl := ForAll(a)(F.Apply(a).Imply(P.Apply(a)))
	principle := core.MakeProp(ForAll(P)(P.Apply(e).And(step).Imply(concl)))

	Q := Var("Q", MakeFun(setType, TypeBool))
	v := Var("v", setType)
	got := obligationTexts(t, principle, 2, v.To(Q.Apply(v)), Var("c", setType))
	require.Len(t, got, 2)
	for _, o := range got {
		require.NotContains(t, o, "F", "the conclusion's guard is not an obligation")
	}
}

// TestInductionObligations_CurriedPrinciple: a principle whose cases
// are curried rather than conjoined reads the same. Both spellings
// occur, and which one a principle uses is not the citing proof's
// business.
func TestInductionObligations_CurriedPrinciple(t *testing.T) {
	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	step := ForAll(n)(P.Apply(n).Imply(P.Apply(ext.Apply(sucTerm, n))))
	curried := core.MakeProp(ForAll(P)(P.Apply(zeroTerm).Imply(step.Imply(ForAll(n)(P.Apply(n))))))

	R := Var("R", MakeFun(numType, TypeBool))
	u := Var("u", numType)
	got := obligationTexts(t, curried, 2, u.To(R.Apply(u)), Var("k", numType))
	require.Len(t, got, 2)
	require.Equal(t, ext.PrintTerm(R.Apply(zeroTerm)), got[0])
}

// relationType is `A → A → bool`: the type a relation's closure gives
// both its parameter and its predicate.
func relationType() core.HolType { return MakeFun(TypeA, MakeFun(TypeA, TypeBool)) }

// closureInductionForm is the induction principle a parameterized
// inductive definition mints — transitive closure's, with the relation
// R a PARAMETER stated before the predicate and of the predicate's own
// type:
//
//	∀R P x0 x1. (∀x y. R(x, y) ⇒ P(x, y)) ∧ (∀x y z. P(x, y) ∧ P(y, z) ⇒ P(x, z))
//	     ∧ tc(R, x0, x1) ⇒ P(x0, x1)
//
// Its first rule APPLIES the parameter, so a reader that took "the
// binder the cases apply" for the predicate found two; and a reader
// that then chose the witness by type found two again.
func closureInductionForm() Prop {
	R := Var("R", relationType())
	P := Var("P", relationType())
	tc := Var("tc", MakeFun(relationType(), relationType()))
	x, y, z := Var("x", TypeA), Var("y", TypeA), Var("z", TypeA)
	x0, x1 := Var("x0", TypeA), Var("x1", TypeA)
	oneStep := ForAll(x)(ForAll(y)(R.Apply(x, y).Imply(P.Apply(x, y))))
	compose := ForAll(x)(ForAll(y)(ForAll(z)(
		P.Apply(x, y).And(P.Apply(y, z)).Imply(P.Apply(x, z)))))
	body := oneStep.And(compose).And(tc.Apply(R, x0, x1)).Imply(P.Apply(x0, x1))
	return core.MakeProp(ForAll(R)(ForAll(P)(ForAll(x0)(ForAll(x1)(body)))))
}

// TestInductionObligations_ParameterizedPrinciple: the predicate is the
// head of the principle's conclusion, and the obligations are read at
// the PARAMETER's witness as well as at the predicate's — a relation's
// rules mention the relation, so an obligation read at the predicate
// alone would carry the principle's own bound `R` as a free name.
func TestInductionObligations_ParameterizedPrinciple(t *testing.T) {
	S := Var("S", relationType())
	R0 := Var("R0", relationType())
	tc := Var("tc", MakeFun(relationType(), relationType()))
	u, v := Var("u", TypeA), Var("v", TypeA)
	// λu v. tc(S, u, v) — "the pair is related by S's closure".
	motive := u.To(v.To(tc.Apply(S, u, v)))
	a, b := Var("a", TypeA), Var("b", TypeA)

	got := obligationTexts(t, closureInductionForm(), 2, R0, motive, a, b)
	require.Len(t, got, 2)
	require.Equal(t, "∀x.∀y.(R0(x, y) ⇒ tc(S, x, y))", got[0],
		"the one-step case is read at the parameter's witness R0 and the predicate's motive, β-reduced")
	require.Equal(t, "∀x.∀y.∀z.((tc(S, x, y) ∧ tc(S, y, z)) ⇒ tc(S, x, z))", got[1],
		"the composing case mentions only the motive")
	for _, o := range got {
		require.NotContains(t, o, "R(", "the principle's own bound parameter never survives into an obligation")
	}
}

// TestInductionObligations_MotiveIsTheParameter: a motive that is the
// rule set's own parameter makes the one-step obligation `R0(x, y) ⇒
// R0(x, y)`. The reader states it as the principle does; what the
// terminal makes of an obligation that normalizes to ⊤ is the
// terminal's business, and the Case is still owed.
func TestInductionObligations_MotiveIsTheParameter(t *testing.T) {
	R0 := Var("R0", relationType())
	a, b := Var("a", TypeA), Var("b", TypeA)

	got := obligationTexts(t, closureInductionForm(), 2, R0, R0, a, b)
	require.Len(t, got, 2)
	require.Equal(t, "∀x.∀y.(R0(x, y) ⇒ R0(x, y))", got[0])
	require.Equal(t, "∀x.∀y.∀z.((R0(x, y) ∧ R0(y, z)) ⇒ R0(x, z))", got[1])
}

// TestInductionObligations_TupleStopsBeforeThePredicate: a cite that
// grounds the parameter alone leaves the predicate — which the cases
// mention — open, and the panic says which binder the tuple must
// reach and in what order, rather than reading obligations over a
// predicate nothing grounds.
func TestInductionObligations_TupleStopsBeforeThePredicate(t *testing.T) {
	R0 := Var("R0", relationType())
	msg := panicTextOf(t, func() {
		obligationTexts(t, closureInductionForm(), 2, R0)
	})
	require.Contains(t, msg, "stops before the principle's predicate P")
	require.Contains(t, msg, "At(principle, R, P…)")
}

// TestInductionObligations_WherePinnedRejected: ByInduction reads its
// tuple off a positional grounding, and its terminal grounds the same
// tuple; a fact pinned by name (Where) enters a By as the apply rung's
// head instead, so the verb refuses it and names the At spelling.
func TestInductionObligations_WherePinnedRejected(t *testing.T) {
	R0 := Var("R0", relationType())
	msg := panicTextOf(t, func() {
		inductionObligations(NewScript(makeStepTestEnv()),
			MakeFact(closureInductionForm()).Where("P", R0), 2, closureInductionForm())
	})
	require.Contains(t, msg, "pins a binder by name (Where)")
	require.Contains(t, msg, "At(principle, w…)")
}

// TestInductionObligations_ConclusionNotHeadedByAVariable: a statement
// whose final consequent is not a predicate applied to the index has
// no single predicate to read the cases at, and the panic names the
// conclusion rather than a downstream shape failure.
func TestInductionObligations_ConclusionNotHeadedByAVariable(t *testing.T) {
	P := Var("P", MakeFun(numType, TypeBool))
	Q := Var("Q", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	mutual := core.MakeProp(ForAll(P)(ForAll(Q)(
		P.Apply(zeroTerm).Imply(ForAll(n)(P.Apply(n).And(Q.Apply(n)))))))

	R := Var("R", MakeFun(numType, TypeBool))
	msg := panicTextOf(t, func() {
		obligationTexts(t, mutual, 1, R, R)
	})
	require.Contains(t, msg, "whose head is not a variable")
}

// TestInductionObligations_CaseCountMismatch: the count is the verb's
// one structural check, and its panic prints what the principle asked
// for — which is also the cheapest way to see the obligations of a
// principle being cited for the first time.
func TestInductionObligations_CaseCountMismatch(t *testing.T) {
	R := Var("R", MakeFun(numType, TypeBool))
	u := Var("u", numType)
	msg := panicTextOf(t, func() {
		obligationTexts(t, numInductionImplForm(), 3, u.To(R.Apply(u)), Var("k", numType))
	})
	require.Contains(t, msg, "3 Case body(ies) provided")
	require.Contains(t, msg, "asks for 2 obligation(s)")
	require.Contains(t, msg, "obligation 0:", "the panic prints what the principle asked for")
	require.Contains(t, msg, "obligation 1:")
}

// TestInductionObligations_BareCiteRejected: ByInduction reads the
// obligations at a predicate, so a principle cited bare has nothing to
// read them at. The panic says how to fix it rather than reporting a
// shape failure somewhere downstream.
func TestInductionObligations_BareCiteRejected(t *testing.T) {
	msg := panicTextOf(t, func() {
		inductionObligations(NewScript(makeStepTestEnv()), MakeFact(numInductionImplForm()), 2, numInductionImplForm())
	})
	require.Contains(t, msg, "cited bare")
	require.Contains(t, msg, "ground the cite")
}

// TestInductionObligations_NotAnInductionPrinciple: a statement with no
// antecedent has no cases, and saying so beats letting the Case bodies
// fail against goals that were never obligations.
func TestInductionObligations_NotAnInductionPrinciple(t *testing.T) {
	P := Var("P", MakeFun(numType, TypeBool))
	n := Var("n", numType)
	notAPrinciple := core.MakeProp(ForAll(P)(ForAll(n)(P.Apply(n))))

	R := Var("R", MakeFun(numType, TypeBool))
	u := Var("u", numType)
	msg := panicTextOf(t, func() {
		obligationTexts(t, notAPrinciple, 2, u.To(R.Apply(u)))
	})
	require.Contains(t, msg, "no antecedent to read cases off")
}

func panicTextOf(t *testing.T, f func()) string {
	t.Helper()
	var got any
	func() {
		defer func() { got = recover() }()
		f()
	}()
	require.NotNil(t, got, "expected a panic")
	s, ok := got.(string)
	require.True(t, ok, "expected a string panic, got %T", got)
	return s
}

// TestByInduction_NamedPrincipleInstallsStatedForm: a principle named by
// its dep installs in its STATED form under ByInduction, whatever By's
// own install would make of the tuple. The fixture is
// nat_order.StrongInduction's shape, `∀P. (∀n. (∀m. m < n ⇒ P(m)) ⇒
// P(n)) ⇒ ∀n. P(n)`, cited at the predicate alone — a partial tuple,
// which By installs as the closer's clause form; that form's prefix is
// `∀n.∀P.…`, so the one witness lands on n and the grounding fails
// (measured on the corpus site before statedPrinciple: "grounding the
// installed premise … failed — installed hyp: ∀n.∀P.∃kʹ.∀m.…"). Through
// ByInduction the stated form installs and the close is one modus
// ponens.
func TestByInduction_NamedPrincipleInstallsStatedForm(t *testing.T) {
	ltType := MakeFun(numType, MakeFun(numType, TypeBool))
	lt := WrapTerm(core.MakeConstTerm(core.MakeConstMeta("<", ltType), ltType))
	n := Var("n", numType)
	m := Var("m", numType)
	// ∀n. (∀m. m < n ⇒ P(m)) ⇒ P(n), the principle's one obligation at P.
	stepAt := func(P *ext.TermWrapper) *ext.TermWrapper {
		return ForAll(n)(ForAll(m)(lt.Apply(m, n).Imply(P.Apply(m))).Imply(P.Apply(n)))
	}
	P := Var("P", MakeFun(numType, TypeBool))
	principle := ForAll(P)(stepAt(P).Imply(ForAll(n)(P.Apply(n))))

	ctx := NewScript(makeStepTestEnv())
	serveThm(ctx, "zz_strong_induction", core.TestThm(principle.Core()))

	// The closure is assumed in its contrapositive shape — Q holds at n
	// or fails somewhere below — so the obligation ByInduction computes
	// is PROVED from it rather than being it (an Assert of a resident
	// hypothesis is refused).
	Q := Var("Q", MakeFun(numType, TypeBool))
	closureAt := ForAll(n)(Q.Apply(n).Or(Exists(m)(lt.Apply(m, n).And(Not(Q.Apply(m))))))
	sec := ctx.Section(core.MakeProp(closureAt.Imply(ForAll(n)(Q.Apply(n))).Core()))
	sec.Do(Derive(func(a *Argument) {
		closure := a.Assume()
		a.Show("the principle at Q concludes ∀n. Q(n), and its one obligation is the assumed closure",
			ByInduction(At(depName("zz_strong_induction"), Q), Normalized,
				MakeCase("Q holds at n once it holds everywhere below n", By(closure))))
	}))
	require.True(t, sec.Proved())
}

// TestBy_PrefixTupleAtAPrincipleIsCompletedFromTheGoal: a principle
// cited in a plain By at its predicate alone — `By(At(principle, Q))`
// on the goal `Q(n₀)` with the one obligation resident — takes its
// STATED form: the index the tuple left open is read off the goal
// (completeStatedTuple), the guard is supplied by the resident
// obligation, and the leaf closes by one modus ponens with no refuter
// (the store is empty and strict, so a refute would panic). Before the
// completion the partial tuple took the closer's clause form, whose
// dissolved ⇒ handed the close to the refuter — at a transparent
// predicate, a search that times out (measured on the free group's
// rule inductions: `{P}` alone failed, `{P, x0, x1}` closed bare).
func TestBy_PrefixTupleAtAPrincipleIsCompletedFromTheGoal(t *testing.T) {
	ltType := MakeFun(numType, MakeFun(numType, TypeBool))
	lt := WrapTerm(core.MakeConstTerm(core.MakeConstMeta("<", ltType), ltType))
	n := Var("n", numType)
	m := Var("m", numType)
	stepAt := func(P *ext.TermWrapper) *ext.TermWrapper {
		return ForAll(n)(ForAll(m)(lt.Apply(m, n).Imply(P.Apply(m))).Imply(P.Apply(n)))
	}
	P := Var("P", MakeFun(numType, TypeBool))
	principle := ForAll(P)(stepAt(P).Imply(ForAll(n)(P.Apply(n))))

	env := makeStepTestEnv()
	// Strict: a close that reaches the refuter panics on the empty
	// store, so a proved section is a keyless one.
	env.RequireCNFCacheHit = true
	ctx := NewScript(env)
	serveThm(ctx, "zz_strong_induction", core.TestThm(principle.Core()))

	Q := Var("Q", MakeFun(numType, TypeBool))
	k := Var("k", numType)
	sec := ctx.Section(core.MakeProp(stepAt(Q).Imply(Q.Apply(k)).Core()))
	sec.Do(Derive(func(a *Argument) {
		obligation := a.Assume()
		a.Show("the principle at Q, its index read off the goal, concludes Q(k) from the resident obligation",
			By(obligation, At(depName("zz_strong_induction"), Q)))
	}))
	require.True(t, sec.Proved())
}

// TestByInduction_BarePolymorphicPrincipleAtAFunctionTypeInstance: a
// polymorphic principle whose predicate ranges over a function type on
// the letter, cited BARE at an instance of the letter that is itself a
// function type. The fixture is finite_set.FiniteInductSupport's shape,
// `∀P:((A → num) → bool). ∀v:(A → num). P(λx. 0) ∧ (∀u a. P(λx. COND(x =
// a, 0, u(x))) ⇒ P(u)) ⇒ P(v)`, at A := (ind → bool): the step rule's `x
// = a` is then an equation between functions, which Normalize
// funext-expands at the instance and not at the letter, so the claim
// obligation's normal form is no type instance of the certificate's.
// The obligation is the certificate's tuple-length telescope at the
// instance, which the type-instance step matches raw (measured on
// ideal_factorization.IdealProductSubsetPrime: "By: no certificate
// covers the premise obligation ⊢ ∀P.((P(λx.0) ∧ …) ⇒ (∀v.(finite({x |
// v(x) ≠ 0}) ⇒ P(v))))" before, keyless after).
func TestByInduction_BarePolymorphicPrincipleAtAFunctionTypeInstance(t *testing.T) {
	elem := core.MakeVarType("A")
	vec := MakeFun(elem, numType)
	P := Var("P", MakeFun(vec, TypeBool))
	v := Var("v", vec)
	u := Var("u", vec)
	a := Var("a", elem)
	x := Var("x", elem)
	// ∀P v. P(λx. 0) ∧ (∀u a. P(λx. COND(x = a, 0, u(x))) ⇒ P(u)) ⇒ P(v)
	cleared := Lambda(x, ext.Cond(x.Eq(a).Core(), zeroTerm, u.Apply(x).Core()))
	step := ForAll(u)(ForAll(a)(P.Apply(cleared).Imply(P.Apply(u))))
	principle := ForAll(P)(ForAll(v)(P.Apply(Lambda(x, zeroTerm)).And(step).Imply(P.Apply(v))))

	ctx := NewScript(makeStepTestEnv())
	serveThm(ctx, "zz_support_induction", core.TestThm(principle.Core()))

	// The same rules at Q over (ind → bool) → num, assumed as one fact
	// so that each Case proves its obligation rather than restating a
	// resident hypothesis.
	point := MakeFun(TypeInd, TypeBool)
	vecAt := MakeFun(point, numType)
	Q := Var("Q", MakeFun(vecAt, TypeBool))
	vAt := Var("v", vecAt)
	uAt := Var("u", vecAt)
	aAt := Var("a", point)
	xAt := Var("x", point)
	clearedAt := Lambda(xAt, ext.Cond(xAt.Eq(aAt).Core(), zeroTerm, uAt.Apply(xAt).Core()))
	stepAt := ForAll(uAt)(ForAll(aAt)(Q.Apply(clearedAt).Imply(Q.Apply(uAt))))
	rulesAt := Q.Apply(Lambda(xAt, zeroTerm)).And(stepAt)
	sec := ctx.Section(core.MakeProp(rulesAt.Imply(ForAll(vAt)(Q.Apply(vAt))).Core()))
	sec.Do(Derive(func(b *Argument) {
		rules := b.Assume()
		b.Show("the principle at Q, cited bare at the function-type instance, concludes ∀v. Q(v) from its two cases",
			ByInduction(At(depName("zz_support_induction"), Q),
				MakeCase("at the zero vector", By(rules)),
				MakeCase("across a cleared coordinate", By(rules))))
	}))
	require.True(t, sec.Proved())
}

// TestInductionObligations_SessionReadingIsTheVerbs: the exported
// reading — a statement and a tuple, no Script — returns the
// obligations the verb reads for the same cite, and refuses what the
// verb refuses, in the verb's words.
func TestInductionObligations_SessionReadingIsTheVerbs(t *testing.T) {
	principle := numInductionImplForm()
	n := Var("n", numType)
	pred := n.To(ext.WrapTerm(n.Core()).Eq(n))
	fromVerb := obligationTexts(t, principle, 2, pred)
	got, err := InductionObligations(principle, []Term{pred}, "the principle")
	require.NoError(t, err)
	require.Len(t, got, 2)
	for i, o := range got {
		assert.Equal(t, fromVerb[i], ext.PrintTerm(o.Conclusion()))
	}

	_, err = InductionObligations(principle, nil, "the principle")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "is cited bare")
	notAPrinciple := core.MakeProp(ForAll(n)(ext.WrapTerm(n.Core()).Eq(n)))
	_, err = InductionObligations(notAPrinciple, []Term{n}, "the law")
	require.Error(t, err)
	assert.Contains(t, err.Error(), "has no antecedent to read cases off")
}
