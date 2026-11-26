package prop

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
)

var (
	testThm  = core.TestThm
	testProp = MakeProp
)

func assertTermEqual(t *testing.T, t0, t1 Term) {
	assert.True(t, t0.Equals(t1))
}

func assertTermAlphaEqual(t *testing.T, t0, t1 Term) {
	assert.True(t, t0.AlphaEquals(t1))
}

func assertPropAlphaEqual(t *testing.T, p0, p1 Prop) {
	assert.True(t, p0.AlphaEquals(p1))
}

func TestSubscriptVarsRewrite(t *testing.T) {
	emptyNamePredicate := utils.EmptyPredicate[TermName]
	a := Var("a", TypeA)
	a0 := Var("a_0", TypeA)
	a1 := Var("a_1", TypeA)
	ap := Var("a"+utils.PrimeStr, TypeA)
	ap0 := Var("a"+utils.PrimeStr+"_0", TypeA)
	b := Var("b", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA))
	f := Var("ƒ", TypeA)
	f0 := Var("ƒ_0", TypeA)
	f1 := Var("ƒ_1", TypeA)
	f2 := Var("ƒ_2", TypeA)
	f3 := Var("ƒ_3", TypeA)

	assert.True(t, Rhs(SubscriptUnivVars(emptyNamePredicate)(
		ForAll(a)(P.Apply(a).Eq(b)))).Equals(ForAll(a0)(P.Apply(a0).Eq(b))))

	assert.True(t, Rhs(SubscriptUnivVars(emptyNamePredicate)(
		ForAll(ap)(P.Apply(ap).Eq(b)))).Equals(ForAll(ap0)(P.Apply(ap0).Eq(b))))

	assert.True(t, Rhs(SubscriptUnivVars(a0.HasName)(
		ForAll(a)(P.Apply(a).Eq(b)))).Equals(ForAll(a1)(P.Apply(a1).Eq(b))))

	assert.True(t, Rhs(SubscriptExistsVars(emptyNamePredicate)(Exists(f0, f)(f0.Eq(f)))).
		Equals(Exists(f0, f1)(f0.Eq(f1))))

	assert.True(t, Rhs(SubscriptExistsVars(emptyNamePredicate)(Exists(f, f0)(f0.Eq(f)))).
		Equals(Exists(f1, f0)(f0.Eq(f1))))

	assert.True(t, Rhs(SubscriptExistsVars(f0.HasFreeName)(Exists(f0, f)(f0.Eq(f)))).
		Equals(Exists(f1, f2)(f1.Eq(f2))))

	assert.True(t, Rhs(SubscriptExistsVars(f0.HasFreeName)(Exists(f, f0)(f0.Eq(f)))).
		Equals(Exists(f1, f2)(f2.Eq(f1))))

	assert.True(t, Rhs(SubscriptExistsVars(f0.Eq(f1).HasFreeName)(Exists(f0, f1)(f0.Eq(f1)))).
		Equals(Exists(f2, f3)(f2.Eq(f3))))

	assert.True(t, Rhs(SubscriptExistsVars(f0.Eq(f1).HasFreeName)(Exists(f0, f1)(f1.Eq(f0)))).
		Equals(Exists(f2, f3)(f3.Eq(f2))))

	assert.True(t, Rhs(SubscriptExistsVars(f0.Eq(f2).HasFreeName)(Exists(f0, f1)(f0.Eq(f1)))).
		Equals(Exists(f3, f1)(f3.Eq(f1))))

	assert.True(t, Rhs(SubscriptExistsVars(f0.Eq(f2).HasFreeName)(Exists(f1, f0)(f0.Eq(f1)))).
		Equals(Exists(f1, f3)(f3.Eq(f1))))

	x1 := Var("x1", TypeA)
	x2 := Var("x2", TypeA)
	x_2 := Var("x_2", TypeA)
	x1_2 := Var("x1_2", TypeA)
	x_1_2 := Var("x_1_2", TypeA)
	xp1 := Var("x'1", TypeA)
	xp_1 := Var("x'_1", TypeA)
	x5y := Var("x5y", TypeA)
	x5y_0 := Var("x5y_0", TypeA)
	xa1 := Var("%1", TypeA)
	xa_1 := Var("%_1", TypeA)
	xa1_0 := Var("ˍ_1", TypeA)
	assert.True(t, Rhs(SubscriptExistsVars(x1.HasFreeName)(Exists(x2)(x1.Eq(x2)))).
		Equals(Exists(x_2)(x1.Eq(x_2))))
	assert.True(t, Rhs(SubscriptExistsVars(x1.HasFreeName)(Exists(xp1)(x1.Eq(xp1)))).
		Equals(Exists(xp_1)(x1.Eq(xp_1))))
	assert.True(t, Rhs(SubscriptExistsVars(emptyNamePredicate)(Exists(x5y)(x1.Eq(x5y)))).
		Equals(Exists(x5y_0)(x1.Eq(x5y_0))))
	assert.True(t, Rhs(SubscriptExistsVars(x1.HasFreeName)(Exists(xa1)(x1.Eq(xa1)))).
		Equals(Exists(xa1_0)(x1.Eq(xa1_0))))
	assert.Nil(t, SubscriptExistsVars(x1.HasFreeName)(Exists(x1_2)(x1.Eq(x1_2))))
	assert.Nil(t, SubscriptExistsVars(x1.HasFreeName)(Exists(x_1_2)(x1.Eq(x_1_2))))
	assert.Nil(t, SubscriptExistsVars(x1.HasFreeName)(Exists(xp_1)(x1.Eq(xp_1))))
	assert.Nil(t, SubscriptExistsVars(x1.HasFreeName)(Exists(xa_1)(x1.Eq(xa_1))))
}

func TestAdjustQuantifierVars(t *testing.T) {
	emptyNamePredicate := utils.EmptyPredicate[TermName]
	a := Var("a", TypeA)
	ap := Var("a"+utils.PrimeStr, TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	u := Var("u", TypeA)
	z := Var("z", TypeA)
	zp := Var("z"+utils.PrimeStr, TypeA)
	P := Var("P", MakeFun(TypeA, TypeA))
	f := Var("ƒ", TypeA)
	fp := Var("ƒ"+utils.PrimeStr, TypeA)
	fpp := Var("ƒ"+utils.PrimeStr+utils.PrimeStr, TypeA)
	f0 := Var("ƒ_0", TypeA)
	f1 := Var("ƒ_1", TypeA)
	f2 := Var("ƒ_2", TypeA)
	f3 := Var("ƒ_3", TypeA)

	assert.Nil(t, AdjustUnivVars(emptyNamePredicate)(ForAll(a)(P.Apply(a).Eq(b))))

	assert.True(t, Rhs(AdjustUnivVars(emptyNamePredicate)(
		ForAll(ap)(P.Apply(ap).Eq(b)))).Equals(ForAll(a)(P.Apply(a).Eq(b))))

	assert.True(t, Rhs(AdjustUnivVars(emptyNamePredicate)(
		ForAll(zp)(P.Apply(zp).Eq(b)))).Equals(ForAll(z)(P.Apply(z).Eq(b))))

	assert.True(t, Rhs(AdjustUnivVars(emptyNamePredicate)(
		ForAll(zp)(P.Apply(zp).Eq(z)))).Equals(ForAll(u)(P.Apply(u).Eq(z))))

	assert.True(t, Rhs(AdjustUnivVars(a.HasName)(
		ForAll(a)(P.Apply(a).Eq(b)))).Equals(ForAll(c)(P.Apply(c).Eq(b))))

	assert.True(t, Rhs(AdjustUnivVars(a.HasName)(
		ForAll(ap)(P.Apply(ap).Eq(b)))).Equals(ForAll(c)(P.Apply(c).Eq(b))))

	assert.True(t, Rhs(AdjustUnivVars(emptyNamePredicate)(
		ForAll(a, fp)(P.Apply(a).Eq(fp)))).Equals(ForAll(a, f)(P.Apply(a).Eq(f))))

	assert.Nil(t, AdjustUnivVars(emptyNamePredicate)(ForAll(a, fp)(P.Apply(f).Eq(fp))))

	assert.True(t, Rhs(AdjustUnivVars(emptyNamePredicate)(
		ForAll(a, fpp)(P.Apply(f).Eq(fpp)))).Equals(ForAll(a, fp)(P.Apply(f).Eq(fp))))

	assert.True(t, Rhs(AdjustExistsVars(f0.Eq(f1).HasFreeName)(Exists(f0, f1)(f0.Eq(f1)))).
		Equals(Exists(f2, f3)(f2.Eq(f3))))

	assert.True(t, Rhs(AdjustExistsVars(f0.Eq(f1).HasFreeName)(Exists(f0, f1)(f1.Eq(f0)))).
		Equals(Exists(f2, f3)(f3.Eq(f2))))

	assert.True(t, Rhs(AdjustExistsVars(f0.Eq(f2).HasFreeName)(Exists(f0, f1)(f0.Eq(f1)))).
		Equals(Exists(f3, f1)(f3.Eq(f1))))

	assert.True(t, Rhs(AdjustExistsVars(f0.Eq(f2).HasFreeName)(Exists(f1, f0)(f0.Eq(f1)))).
		Equals(Exists(f1, f3)(f3.Eq(f1))))
}

func TestBetaRefl(t *testing.T) {
	assertBetaRefl := func(t0, t1 Term) {
		thm := BetaEtaRefl(t0, t1).AsThmCert()
		assertTermEqual(t, Lhs(thm), t0)
		assertTermEqual(t, Rhs(thm), t1)
	}

	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	z := Var("z", TypeBool)
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	f := Var("f", MakeFun(TypeBool, TypeBool, TypeBool, TypeBool))

	assertPropAlphaEqual(t, BetaEtaRefl(x, x), Refl(x))
	assertPropAlphaEqual(t, BetaEtaRefl(x.To(f.Apply(x)), y.To(f.Apply(y))), Refl(x.To(f.Apply(x))))
	assertPropAlphaEqual(t, BetaEtaRefl(x.To(f.Apply(x)), f), testThm(Eq(x.To(f.Apply(x)), f)))
	assert.Nil(t, BetaEtaRefl(x, y))

	assertBetaRefl(
		x.To(y.To(f.Apply(x, y))).Apply(a, b),
		y.To(x.To(f.Apply(x, y))).Apply(b, a))

	P := Var("P", MakeFun(TypeBool, TypeBool))
	Q := Var("Q", MakeFun(TypeBool, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool, TypeBool))
	F := Var("F", MakeFun(MakeFun(TypeBool, TypeBool), TypeBool))
	H := Var("H", MakeFun(MakeFun(TypeBool, TypeBool), TypeBool, TypeBool))

	// (λz.P(Q(z)))(z) = (λx.P(x))((λy.Q(y))(z))
	assertBetaRefl(
		z.To(P.Apply(Q.Apply(z))).Apply(z),
		x.To(P.Apply(x)).Apply(y.To(Q.Apply(y)).Apply(z)))

	// (λx.λy.R(x, y))(y, z) = R(y, z)
	assertBetaRefl(
		x.To(y.To(R.Apply(x, y))).Apply(y, z),
		R.Apply(y, z))

	// (λQ.F(H(Q)))(P) = F(λx.H(P, x))
	assertBetaRefl(
		Q.To(F.Apply(H.Apply(Q))).Apply(P),
		F.Apply(x.To(H.Apply(P, x))))
}

func TestBetaEta(t *testing.T) {
	assertBetaEta := func(s0, s1 Term) {
		assertTermAlphaEqual(t, ext.BetaEtaNormalize(t.Context(), s0), s1)
		assertTermAlphaEqual(t,
			Rhs(RewriteOrRefl(DeepBetaEta, s0)),
			Rhs(RewriteOrRefl(DeepBetaEta, s1)))
		assertPropAlphaEqual(t,
			BetaEtaRefl(s0, s1),
			testThm(Eq(s0, s1)))
		assertPropAlphaEqual(t,
			BetaEtaRefl(s1, s0),
			testThm(Eq(s1, s0)))
	}

	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	z := Var("z", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	R := Var("R", MakeFun(TypeInd, TypeInd))
	S := Var("S", MakeFun(TypeInd, TypeInd, TypeBool))
	F := Var("F", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd))
	G := Var("G", MakeFun(MakeFun(TypeInd, TypeBool), TypeBool))
	H := Var("H", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd, TypeBool))

	assertTermEqual(t, F, Rhs(DeepBetaEta(ext.BetaEtaNormalize(t.Context(), F))))
	assertTermEqual(t, G, Rhs(DeepBetaEta(ext.BetaEtaNormalize(t.Context(), G))))
	assertTermEqual(t, H, Rhs(DeepBetaEta(ext.BetaEtaNormalize(t.Context(), H))))

	assertBetaEta(P, x.To(P.Apply(x)))
	assertBetaEta(S, x.To(y.To(S.Apply(x, y))))
	assertBetaEta(P.Apply(x), P.Apply(x))
	assertBetaEta(x.To(x.Eq(x)), x.To(x.Eq(x)))
	assertBetaEta(x.To(x.Eq(y)), x.To(x.Eq(y)))
	assertBetaEta(x.To(y.Eq(x)), x.To(y.Eq(x)))
	assertBetaEta(x.To(P.Apply(x)), x.To(P.Apply(x)))
	assertBetaEta(x.To(P.Apply(y)), x.To(P.Apply(y)))
	assertBetaEta(x.To(P.Apply(x)).Apply(y), P.Apply(y))
	assertBetaEta(y.To(P.Apply(y)).Apply(y), P.Apply(y))
	assertBetaEta(x.To(P.Apply(y)).Apply(y), P.Apply(y))
	assertBetaEta(x.To(y.To(z)).Apply(x, y), z)

	// P -> λx.P(x)
	assertBetaEta(
		P,
		x.To(P.Apply(x)))

	// P(y) -> P(y)
	assertBetaEta(
		P.Apply(y),
		P.Apply(y))

	// S -> λx.λy.S(x, y)
	assertBetaEta(
		S,
		x.To(y.To(S.Apply(x, y))))

	// S(y) -> λx.S(y, x)
	assertBetaEta(
		S.Apply(y),
		x.To(S.Apply(y, x)))

	// λx.S(x) -> λx.λy.S(x, y)
	assertBetaEta(
		x.To(S.Apply(x)),
		x.To(y.To(S.Apply(x, y))))

	// λx.S(x, y) -> λx.S(x, y)
	assertBetaEta(
		x.To(S.Apply(x, y)),
		x.To(S.Apply(x, y)))

	// (λy.λx.S(x, y))(x, y) -> S(y, x)
	assertBetaEta(
		y.To(x.To(S.Apply(x, y))).Apply(x, y),
		S.Apply(y, x))

	// (λx.P(x))(y) -> P(y)
	assertBetaEta(
		x.To(P.Apply(x)).Apply(y),
		P.Apply(y))

	// (λx.P(x))((λy.R(y))(z)) -> P(R(z))
	assertBetaEta(
		x.To(P.Apply(x)).Apply(y.To(R.Apply(y)).Apply(z)),
		P.Apply(R.Apply(z)))

	// (λx.λy.S(x, y))(y, z) -> S(y, z)
	assertBetaEta(
		x.To(y.To(S.Apply(x, y))).Apply(y, z),
		S.Apply(y, z))

	// (λz.R((λy.R((λx.x)(y))(z))))(R(x)) -> R(R(R(x)))
	assertBetaEta(
		z.To(R.Apply(y.To(R.Apply(x.To(x).Apply(y))).Apply(z))).Apply(R.Apply(x)),
		R.Apply(R.Apply(R.Apply(x))))

	// G -> λP.G(λx.P(x)))
	assertBetaEta(
		G,
		P.To(G.Apply(x.To(P.Apply(x)))))

	// G(P) -> G(λx.P(x))
	assertBetaEta(
		G.Apply(P),
		G.Apply(x.To(P.Apply(x))))

	// G(R(x)) -> G(λy.S(x, y))
	assertBetaEta(
		G.Apply(S.Apply(x)),
		G.Apply(y.To(S.Apply(x, y))))

	// H -> λP.λx.H(λy.P(y), x)
	assertBetaEta(
		H,
		P.To(x.To(H.Apply(y.To(P.Apply(y)), x))))

	// H(P) -> λx.H(λy.P(y), x)
	assertBetaEta(
		H.Apply(P),
		x.To(H.Apply(y.To(P.Apply(y)), x)))

	// (λQ.(λx.Q(x)))(P) -> λx.P(x)
	assertBetaEta(
		Q.To((x.To(Q.Apply(x)))).Apply(P),
		x.To(P.Apply(x)))

	// (λQ.P(F(λx.Q(x))))(P) -> P(F(λx.P(x)))
	assertBetaEta(
		Q.To(P.Apply(F.Apply(x.To(Q.Apply(x))))).Apply(P),
		P.Apply(F.Apply(x.To(P.Apply(x)))))

	// (λQ.F(H(λx.Q(x))))(P) -> F(λx.H(λy.P(y), x))
	assertBetaEta(
		Q.To(F.Apply(H.Apply(x.To(Q.Apply(x))))).Apply(P),
		F.Apply(x.To(H.Apply(y.To(P.Apply(y)), x))))

	{
		// ((((A, A) → bool), (Ind → A), Ind) → Ind)
		typeX := MakeFun(MakeFun(TypeA, TypeA, TypeBool), MakeFun(TypeInd, TypeA), TypeInd, TypeInd)
		x := Var("x", typeX)
		x0 := Var("x0", MakeFun(TypeA, TypeA, TypeBool))
		x1 := Var("x1", MakeFun(TypeInd, TypeA))
		x2 := Var("x2", TypeInd)
		x3 := Var("x3", TypeA)
		x4 := Var("x4", TypeA)
		x5 := Var("x5", TypeInd)
		assertBetaEta(
			x,
			x0.To(x1.To(x2.To(x.Apply(x3.To(x4.To(x0.Apply(x3, x4))), x5.To(x1.Apply(x5)), x2)))))
	}
}

func TestMatchesAbsToAvoid(t *testing.T) {
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeA, TypeBool))

	eq := (VarTerm).EqualsVar

	assert.Panics(t, func() { matchesAbsToAvoid(Q.Apply(a, b), P.Apply(a), 1) })
	assert.Panics(t, func() { matchesAbsToAvoid(a.To(Q.Apply(a, b)), P.Apply(a), 2) })

	vars, s := matchesAbsToAvoid(Q.Apply(a, b), P.Apply(a), 0)
	assert.Nil(t, vars)
	assert.True(t, s.Equals(Q.Apply(a, b)))

	vars, s = matchesAbsToAvoid(a.To(Q.Apply(a, b)), P.Apply(a), 1)
	assert.True(t, s.Equals(Q.Apply(c, b)))
	assert.True(t, slices.EqualFunc(vars, []VarTerm{c.AssertVar()}, eq))

	vars, s = matchesAbsToAvoid(a.To(b.To(Q.Apply(a, b))), P.Apply(c), 2)
	assert.True(t, s.Equals(Q.Apply(a, b)))
	assert.True(t, slices.EqualFunc(vars, []VarTerm{a.AssertVar(), b.AssertVar()}, eq))

	vars, s = matchesAbsToAvoid(a.To(b.To(Q.Apply(a, b))), P.Apply(c), 1)
	assert.True(t, s.Equals(b.To(Q.Apply(a, b))))
	assert.True(t, slices.EqualFunc(vars, []VarTerm{a.AssertVar()}, eq))

	vars, s = matchesAbsToAvoid(a.To(b.To(Q.Apply(a, b))), P.Apply(b), 2)
	assert.True(t, s.Equals(Q.Apply(a, c)))
	assert.True(t, slices.EqualFunc(vars, []VarTerm{a.AssertVar(), c.AssertVar()}, eq))

	vars, s = matchesAbsToAvoid(a.To(b.To(Q.Apply(a, b))), P.Apply(b), 1)
	assert.True(t, s.Equals(b.To(Q.Apply(a, b))))
	assert.True(t, slices.EqualFunc(vars, []VarTerm{a.AssertVar()}, eq))

	vars, s = matchesAbsToAvoid(a.To(b.To(Q.Apply(a, b))), P.Apply(a), 2)
	assert.True(t, s.Equals(Q.Apply(c, b)))
	assert.True(t, slices.EqualFunc(vars, []VarTerm{c.AssertVar(), b.AssertVar()}, eq))

	vars, s = matchesAbsToAvoid(a.To(b.To(Q.Apply(a, b))), P.Apply(a), 1)
	assert.True(t, s.Equals(b.To(Q.Apply(c, b))))
	assert.True(t, slices.EqualFunc(vars, []VarTerm{c.AssertVar()}, eq))
}

// TestWeakenTo_SyntacticConclusionPreserved exercises WeakenTo's contract that the
// returned Thm's conclusion is SYNTACTICALLY (not just α-) equal to the target's. The
// bound-var-rename case is the load-bearing one for emit/replay determinism: a downstream
// strip_quant produces a Skolem named after the bound var of whichever binder it peels,
// so syntactic divergence (kʹ vs n) yields different Skolem constants and a divergent
// leaf AlphaKey. See WeakenTo's docstring for the full rationale.
func TestWeakenTo_SyntacticConclusionPreserved(t *testing.T) {
	x := Var("x", TypeA).AssertVar()
	y := Var("y", TypeA).AssertVar()
	z := Var("z", TypeA).AssertVar()
	P := Var("P", MakeFun(TypeA, TypeBool))

	// Section A — fast path: conclusions already syntactically equal.
	t.Run("syntactic_identity_no_kernel_work", func(t *testing.T) {
		concl := ForAll(x)(P.Apply(x))
		s := testThm(concl)
		target := testProp(concl)
		got := WeakenTo(s, target)
		assert.True(t, got.Proved())
		assert.True(t, got.Conclusion().Equals(target.Conclusion()),
			"identity case must return the same syntactic concl")
		assert.Equal(t, 0, got.NumHyps())
	})

	// Section B — alpha-equivalent but renamed conclusion. Source has `∀x.P(x)`;
	// target asks for `∀y.P(y)`. Returned Thm must have target's bound-var name
	// syntactically — not the source's. This is the bug case.
	t.Run("alpha_equivalent_bound_var_renamed", func(t *testing.T) {
		sourceConcl := ForAll(x)(P.Apply(x))
		targetConcl := ForAll(y)(P.Apply(y))
		assert.True(t, sourceConcl.AlphaEquals(targetConcl))
		assert.False(t, sourceConcl.Equals(targetConcl),
			"setup: source and target conclusions must differ syntactically")

		s := testThm(sourceConcl)
		target := testProp(targetConcl)
		got := WeakenTo(s, target)

		assert.True(t, got.Proved(), "result must still be a *Thm")
		assert.True(t, got.Conclusion().Equals(targetConcl),
			"result's conclusion must syntactically equal target's, not source's")
		assert.False(t, got.Conclusion().Equals(sourceConcl),
			"result's conclusion must NOT remain in source's syntactic form")
	})

	// Section C — nested-binder rename, the shape of nat_parity.OddIffModTwoOne. Source uses
	// `∀x.∀y.…`; target requests `∀y.∀x.…` (the bound-var roles swap at both
	// binders). Both bound levels must be renamed in the output.
	t.Run("nested_binder_swap", func(t *testing.T) {
		R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
		sourceConcl := ForAll(x, y)(R.Apply(x, y))
		// Target with bound names y, x swapped: still ∀ ∀ but ∀y. then ∀x.
		// We pick fresh-named binders to force a syntactic mismatch on
		// every level.
		yT, xT := Var("y", TypeA).AssertVar(), Var("x", TypeA).AssertVar()
		targetConcl := ForAll(yT, xT)(R.Apply(yT, xT))
		assert.True(t, sourceConcl.AlphaEquals(targetConcl))

		// To force a real rename mismatch, swap the bound-var roles fully:
		swappedConcl := ForAll(y, x)(R.Apply(y, x))
		assert.True(t, sourceConcl.AlphaEquals(swappedConcl))
		assert.False(t, sourceConcl.Equals(swappedConcl),
			"setup: swapped form must differ syntactically from source")

		s := testThm(sourceConcl)
		target := testProp(swappedConcl)
		got := WeakenTo(s, target)
		assert.True(t, got.Proved())
		assert.True(t, got.Conclusion().Equals(swappedConcl),
			"result must adopt target's swapped bound-var syntactic form")
	})

	// Section D — alpha-equivalent payload (existential), simulates the
	// Skolem-bridge ∃-binder rename that member hit (cite returns ∀kʹ.∃n.… where
	// record loaded ∀n.∃kʹ.…). Strip_quant on the result's ∃ must Skolemize
	// from target's bound name, so the syntactic form must survive WeakenTo.
	t.Run("existential_bound_var_renamed", func(t *testing.T) {
		k := Var("k", TypeA).AssertVar()
		sourceConcl := Exists(x)(P.Apply(x))
		targetConcl := Exists(k)(P.Apply(k))
		assert.True(t, sourceConcl.AlphaEquals(targetConcl))
		assert.False(t, sourceConcl.Equals(targetConcl))

		s := testThm(sourceConcl)
		target := testProp(targetConcl)
		got := WeakenTo(s, target)
		assert.True(t, got.Conclusion().Equals(targetConcl),
			"∃-binder rename must be reflected in result")
	})

	// Section E — adds a hyp (existing weaken behavior preserved). Source proves
	// `⊢ P(x)`, target asks for `Q(z) ⊢ P(x)`. Result must carry Q(z) as hyp.
	t.Run("adds_missing_hyp", func(t *testing.T) {
		Q := Var("Q", MakeFun(TypeA, TypeBool))
		concl := P.Apply(x)
		extraHyp := Q.Apply(z)
		s := testThm(concl)
		target := testProp(concl, extraHyp)
		got := WeakenTo(s, target)
		assert.True(t, got.Proved())
		assert.True(t, got.Conclusion().Equals(concl))
		assert.True(t, got.HasHyp(extraHyp),
			"weaken must add target's extra hyp")
	})

	// Section F — combination: alpha-renamed concl AND a new hyp from target.
	// Both transformations must apply.
	t.Run("rename_and_add_hyp", func(t *testing.T) {
		Q := Var("Q", MakeFun(TypeA, TypeBool))
		sourceConcl := ForAll(x)(P.Apply(x))
		targetConcl := ForAll(y)(P.Apply(y))
		extraHyp := Q.Apply(z)

		s := testThm(sourceConcl)
		target := testProp(targetConcl, extraHyp)
		got := WeakenTo(s, target)

		assert.True(t, got.Proved())
		assert.True(t, got.Conclusion().Equals(targetConcl),
			"rename must apply alongside hyp addition")
		assert.True(t, got.HasHyp(extraHyp))
	})

	// Section G — IsStronger fails (s has a hyp t doesn't): WeakenTo returns nil.
	t.Run("not_stronger_returns_nil", func(t *testing.T) {
		Q := Var("Q", MakeFun(TypeA, TypeBool))
		s := testThm(P.Apply(x), Q.Apply(z)) // s has Q(z) hyp
		target := testProp(P.Apply(x))       // t has no hyp
		got := WeakenTo(s, target)
		assert.Nil(t, got, "WeakenTo should refuse when s isn't a weakening of t")
	})

	// Section H — F-conclusion broadcast: when s.Concl is ⊥, target.Concl can be
	// anything (FalseDerives handles it). Verify the result's concl is target's
	// syntactically.
	t.Run("false_conclusion_broadcasts_to_target", func(t *testing.T) {
		s := testThm(F)
		target := testProp(P.Apply(x))
		got := WeakenTo(s, target)
		assert.True(t, got.Proved())
		assert.True(t, got.Conclusion().Equals(target.Conclusion()),
			"F-derivation must land at target's syntactic conclusion")
	})
}

func TestIsTypeVariantOf(t *testing.T) {
	TypeB := core.MakeVarType("B")
	TypeC := core.MakeVarType("C")
	TypeD := core.MakeVarType("D")

	// Identical props with no type vars → trivially variant (empty rename).
	pBool := core.Var("p", core.TypeBool())
	p1 := core.MakeProp(core.Eq(pBool, pBool))
	q1 := core.MakeProp(core.Eq(pBool, pBool))
	substs, ok := IsTypeVariantOf(p1, q1)
	assert.True(t, ok)
	assert.Empty(t, substs)

	// ⊢ x:A = x:A  variant-of  ⊢ x:B = x:B  → true  (A↔B).
	xA := core.Var("x", core.TypeA())
	xB := core.Var("x", TypeB)
	substs, ok = IsTypeVariantOf(core.MakeProp(core.Eq(xA, xA)), core.MakeProp(core.Eq(xB, xB)))
	assert.True(t, ok, "⊢ x:A = x:A is a variant of ⊢ x:B = x:B")
	assert.Equal(t, 1, len(substs))
	assert.True(t, substs[0].VarType.Equals(core.TypeA()))
	assert.True(t, substs[0].HolType.Equals(TypeB))

	// Free var name differs → false (variant only renames type vars,
	// never free term vars; AlphaEquals also does not rename free vars).
	yA := core.Var("y", core.TypeA())
	_, ok = IsTypeVariantOf(core.MakeProp(core.Eq(xA, xA)), core.MakeProp(core.Eq(yA, yA)))
	assert.False(t, ok, "free vars with different names are not variants")

	// Polymorphic ↔ concrete → false (bool is not a var).
	_, ok = IsTypeVariantOf(core.MakeProp(core.Eq(xA, xA)), core.MakeProp(core.Eq(pBool, pBool)))
	assert.False(t, ok, "polymorphic prop is not a variant of a ground prop")

	// Bound-var α-renaming + type-var rename, using Abs directly:
	//   ⊢ (λx:A. x) = (λx:A. x)   variant-of   ⊢ (λy:B. y) = (λy:B. y)
	// The two sides differ in both the bound-var name AND the type var.
	yB := core.Var("y", TypeB)
	pAbs := core.MakeProp(core.Eq(core.Abs(xA, xA), core.Abs(xA, xA)))
	qAbs := core.MakeProp(core.Eq(core.Abs(yB, yB), core.Abs(yB, yB)))
	substs, ok = IsTypeVariantOf(pAbs, qAbs)
	assert.True(t, ok, "bound-var α-renaming composes with type renaming")
	assert.Equal(t, 1, len(substs))
	assert.True(t, substs[0].VarType.Equals(core.TypeA()))
	assert.True(t, substs[0].HolType.Equals(TypeB))

	// Two-type-var prop: free vars f:A→B, g:A→B; variant against C→D
	// version with same free-var names.
	fAB := core.Var("f", core.MakeFun(core.TypeA(), TypeB))
	gAB := core.Var("g", core.MakeFun(core.TypeA(), TypeB))
	fCD := core.Var("f", core.MakeFun(TypeC, TypeD))
	gCD := core.Var("g", core.MakeFun(TypeC, TypeD))
	substs, ok = IsTypeVariantOf(core.MakeProp(core.Eq(fAB, gAB)), core.MakeProp(core.Eq(fCD, gCD)))
	assert.True(t, ok, "two-type-var prop: bijection A↔C, B↔D")
	assert.Equal(t, 2, len(substs))
	// substs ordering is implementation-defined; check the pairs form
	// a valid {A→C, B→D} bijection.
	got := map[core.TypeName]HolType{}
	for _, s := range substs {
		got[s.VarType.Name()] = s.HolType
	}
	assert.True(t, got["A"].Equals(TypeC))
	assert.True(t, got["B"].Equals(TypeD))

	// Bijection violation: h:(A,B)→bool with args x:A, z:B versus
	// h:(C,C)→bool with args x:C, z:C — A and B both would map to C.
	hAB := core.Var("h", core.MakeFun(core.TypeA(), TypeB, core.TypeBool()))
	hCC := core.Var("h", core.MakeFun(TypeC, TypeC, core.TypeBool()))
	zB := core.Var("z", TypeB)
	xC := core.Var("x", TypeC)
	zC := core.Var("z", TypeC)
	p6 := core.MakeProp(core.Eq(core.Apply(core.Apply(hAB, xA), zB), pBool))
	q6 := core.MakeProp(core.Eq(core.Apply(core.Apply(hCC, xC), zC), pBool))
	_, ok = IsTypeVariantOf(p6, q6)
	assert.False(t, ok, "bijection broken: A and B both would map to C")

	// Forward-consistency violation: A used twice on the left, A and B
	// on the right — A would need to map to both A and B.
	hAA := core.Var("h", core.MakeFun(core.TypeA(), core.TypeA(), core.TypeBool()))
	hAB2 := core.Var("h", core.MakeFun(core.TypeA(), TypeB, core.TypeBool()))
	yB2 := core.Var("y", TypeB)
	p7 := core.MakeProp(core.Eq(core.Apply(core.Apply(hAA, xA), yA), pBool))
	q7 := core.MakeProp(core.Eq(core.Apply(core.Apply(hAB2, xA), yB2), pBool))
	_, ok = IsTypeVariantOf(p7, q7)
	assert.False(t, ok, "A would have to map to both A and B")

	// Different shape: conclusion is core.Eq(x, x) on one side, bare pBool
	// on the other (different size, different structure).
	_, ok = IsTypeVariantOf(core.MakeProp(core.Eq(xA, xA)), core.MakeProp(pBool))
	assert.False(t, ok, "different conclusion shape is not a variant")
}

// Matching proposes a substitution without forcing either proposition. The
// kernel's instantiation supplies the resulting theorem and statement.
func TestIsTypeMatchOfSharesBindingsWithoutForcing(t *testing.T) {
	a := core.MakeVarType("match_A")
	x, y := core.Var("x", a), core.Var("y", a)
	xb, yb := core.Var("x", core.TypeBool()), core.Var("y", core.TypeBool())
	source := core.MakeProp(core.Eq(x, x), core.Eq(y, y))
	target := core.MakeProp(core.Eq(xb, xb), core.Eq(yb, yb))
	promise := core.Promise(source, func(core.Forcer) core.ThmCert { panic("matching must not force") })
	substs, ok := IsTypeMatchOf(WrapProp(promise), target, utils.FullPredicate[VarType])
	if !assert.True(t, ok) {
		return
	}
	assert.Len(t, substs, 1)
	instantiated := core.PropTypeInst(promise, substs...)
	assert.True(t, instantiated.AlphaEquals(target))
	assert.False(t, promise.Proved())
	assert.True(t, core.IsPromised(instantiated))

	_, ok = IsTypeMatchOf(source, target, utils.EmptyPredicate[VarType])
	assert.False(t, ok, "a rigid type variable cannot instantiate to bool")
	_, ok = IsTypeMatchOf(source, source, utils.EmptyPredicate[VarType])
	assert.True(t, ok, "a rigid type variable matches itself")
	inconsistent := core.MakeProp(core.Eq(xb, xb), core.Eq(y, y))
	_, ok = IsTypeMatchOf(source, inconsistent, utils.FullPredicate[VarType])
	assert.False(t, ok, "hypotheses must respect the conclusion's type bindings")
	_, ok = IsTypeMatchOf(source, core.MakeProp(target.Conclusion()), utils.FullPredicate[VarType])
	assert.False(t, ok, "matching does not drop hypotheses")
}
