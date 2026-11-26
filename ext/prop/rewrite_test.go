package prop

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

func assertRewrite(t *testing.T, r Rewrite, s0 *ext.TermWrapper, s1 Term) {
	assertPropAlphaEqual(t,
		r(s0),
		testThm(s0.Eq(s1)))
}

func TestRewriteRhs(t *testing.T) {
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)

	w := testProp(x)
	assert.Panics(t, func() { WrapProp(w).RewriteConclRhs(BasicRewrite) })

	w = testProp(x.Eq(y))
	assertPropAlphaEqual(t, WrapProp(w).RewriteConclRhs(BoolRewrite), w)

	w = testProp(x.Eq(y.Eq(y)))
	assertPropAlphaEqual(t, WrapProp(w).RewriteConclRhs(BoolRewrite), testProp(x.Eq(T)))

	w = testProp(x.Eq(y.Eq(y)))
	assertPropAlphaEqual(t, WrapProp(w).RewriteConclRhs(DoubleNegRewrite), w)

	w = testProp(x.Eq(y.Eq(y.Eq(y))))
	assertPropAlphaEqual(t, WrapProp(w).RewriteConclRhs(BoolRewrite), w)
	assertPropAlphaEqual(t, WrapProp(w).RewriteConclRhs(DeepBoolRewrite), testProp(x.Eq(y)))
}

func TestBetaRewrite(t *testing.T) {
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	z := Var("z", TypeBool)
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	f := Var("f", MakeFun(TypeBool, TypeBool, TypeBool, TypeBool))

	// (λx.f(x))(a) = f(a)
	s := x.To(f.Apply(x))
	assert.Nil(t, DeepBeta(s))

	// (λx.f(x))(a) = f(a)
	s = x.To(f.Apply(x)).Apply(a)
	assertRewrite(t, DeepBeta, s, f.Apply(a))

	// (λx.f(x))(a = b) = f(a = b)
	s = x.To(f.Apply(x)).Apply(a.Eq(b))
	assertRewrite(t, DeepBeta, s, f.Apply(a.Eq(b)))

	// (λx.λy.f(x, y))(a, b) = f(a, b)
	s = x.To(y.To(f.Apply(x, y))).Apply(a, b)
	assertRewrite(t, DeepBeta, s, f.Apply(a, b))

	// (λx.λy.f(x, y))(b, a) = f(b, a)
	s = x.To(y.To(f.Apply(x, y))).Apply(b, a)
	assertRewrite(t, DeepBeta, s, f.Apply(b, a))

	// (λx.λy.f(x, y))(b) = λy.f(b, y)
	s = x.To(y.To(f.Apply(x, y))).Apply(b)
	assertRewrite(t, DeepBeta, s, y.To(f.Apply(b, y)))

	// (λx.λy.λz.f(x, y, z))(b, a) = λz.f(b, a, z)
	s = x.To(y.To(z.To(f.Apply(x, y, z)))).Apply(b, a)
	assertRewrite(t, DeepBeta, s, z.To(f.Apply(b, a, z)))

	// (λx.λy.f(x))(b) = λy.f(b)
	s = x.To(y.To(f.Apply(x))).Apply(b)
	assertRewrite(t, DeepBeta, s, y.To(f.Apply(b)))

	// λx.(λy.f(y))(b)) = λx.f(b)
	s = x.To(y.To(f.Apply(y)).Apply(b))
	assertRewrite(t, DeepBeta, s, x.To(f.Apply(b)))

	// (λx.(λy.f(y))(b))(a) = f(b)
	s = x.To(y.To(f.Apply(y)).Apply(b)).Apply(a)
	assertRewrite(t, DeepBeta, s, f.Apply(b))

	// λz.((λx.(λy.((f(x, y))(a, a))))(z))(a) = f(a, a, a)
	s = z.To(x.To(y.To(f.Apply(x, y))).Apply(a, a).Apply(z)).Apply(a)
	assertRewrite(t, DeepBeta, s, f.Apply(a, a, a))

	assertPropAlphaEqual(t,
		WrapProp(testProp(s, b)).Rewrite(DeepBeta),
		testProp(f.Apply(a, a, a), b))
	assertPropAlphaEqual(t,
		WrapProp(testThm(s, b)).Rewrite(DeepBeta),
		testThm(f.Apply(a, a, a), b))
	assert.NotPanics(t, func() { WrapProp(testThm(s, b)).Rewrite(DeepBeta).AsThmCert() })

	// (((λx.y)(x)) ∧ y) ⇒ y
	s = x.To(y).Apply(x).And(y).Imply(y)
	assertPropAlphaEqual(t,
		WrapProp(testThm(s)).Rewrite(DeepBeta),
		testThm(y.And(y).Imply(y)))
}

func TestEtaRewrite(t *testing.T) {
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	z := Var("z", TypeBool)
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	f := Var("f", MakeFun(TypeBool, TypeBool, TypeBool, TypeBool))
	deepEta := DeepRewrite(etaRewrite)

	// λx.f(x) = f
	s := x.To(f.Apply(x))
	assertRewrite(t, deepEta, s, f)
	// λy.f(x, y) = f(x)
	s = y.To(f.Apply(x, y))
	assertRewrite(t, deepEta, s, f.Apply(x))
	// λx.f(x, y)
	s = x.To(f.Apply(x, y))
	assert.Nil(t, deepEta(s))
	// λf.f(x, y)
	s = f.To(f.Apply(x, y))
	assert.Nil(t, deepEta(s))
	// (λx.f(x))(a) = f(a)
	s = x.To(f.Apply(x)).Apply(a)
	assertRewrite(t, deepEta, s, f.Apply(a))
	// (λx.f(x))(a = b) = f(a = b)
	s = x.To(f.Apply(x)).Apply(a.Eq(b))
	assertRewrite(t, deepEta, s, f.Apply(a.Eq(b)))
	// (λx.λy.f(x, y))(a, b) = f(a, b)
	s = x.To(y.To(f.Apply(x, y))).Apply(a, b)
	assertRewrite(t, deepEta, s, f.Apply(a, b))
	// (λx.λy.f(x, y))(b, a) = f(b, a)
	s = x.To(y.To(f.Apply(x, y))).Apply(b, a)
	assertRewrite(t, deepEta, s, f.Apply(b, a))
	// (λx.λy.f(x, y))(b) = f(b)
	s = x.To(y.To(f.Apply(x, y))).Apply(b)
	assertRewrite(t, deepEta, s, f.Apply(b))
	// (λx.λy.λz.f(x, y, z))(b, a) = f(b, a)
	s = x.To(y.To(z.To(f.Apply(x, y, z)))).Apply(b, a)
	assertRewrite(t, deepEta, s, f.Apply(b, a))
	// (λx.λy.f(x))(b)
	s = x.To(y.To(f.Apply(x))).Apply(b)
	assert.Nil(t, deepEta(s))
	// λx.(λy.f(y))(b)) = λx.f(b)
	s = x.To(y.To(f.Apply(y)).Apply(b))
	assertRewrite(t, deepEta, s, x.To(f.Apply(b)))
	// (λx.(λy.f(y))(b))(a) = (λx.f(b))(a)
	s = x.To(y.To(f.Apply(y)).Apply(b)).Apply(a)
	assertRewrite(t, deepEta, s, x.To(f.Apply(b)).Apply(a))
}

// etaContextRewrite reduces an η-redex where the normal form is η-short
// — as an argument or as a λ body — and leaves the heads whose normal
// form is the expanded λ to their own rules.
func TestEtaContextRewrite(t *testing.T) {
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	s := Var("s", MakeFun(TypeInd, TypeBool))
	P := Var("P", MakeFun(TypeInd, TypeBool))
	F := Var("F", MakeFun(TypeInd, TypeInd))
	G := Var("G", MakeFun(TypeInd, TypeInd, TypeInd))
	g := Var("g", MakeFun(MakeFun(TypeInd, TypeBool), MakeFun(TypeInd, TypeInd), TypeInd))
	h := Var("h", MakeFun(MakeFun(TypeInd, TypeInd, TypeInd), TypeInd))
	deep := DeepRewrite(etaContextRewrite)

	// An argument: g(s, λi.F(i)) = g(s, F).
	assertRewrite(t, deep, g.Apply(s, x.To(F.Apply(x))), g.Apply(s, F))
	// A nested spine collapses as the parent re-fires: h(λy.λx.G(y, x)) = h(G).
	assertRewrite(t, deep, h.Apply(y.To(x.To(G.Apply(y, x)))), h.Apply(G))
	// A λ body: λy.λx.G(y, x) = λy.G(y) — the outer λ, at the root, has no
	// context and stays.
	assertRewrite(t, deep, y.To(x.To(G.Apply(y, x))), y.To(G.Apply(y)))
	assert.Nil(t, deep(x.To(F.Apply(x))))
	// Not a redex: the bound variable occurs in the function.
	assert.Nil(t, deep(g.Apply(s, x.To(G.Apply(x, x)))))

	// The expanding heads: the λ under ∀ / ∃ / ∃! / ε and on either side
	// of a function-typed = is left to QuantifierRewrite, hilbertRewrite
	// and FunEqRewrite.
	assert.Nil(t, deep(ForAll(x)(P.Apply(x))))
	assert.Nil(t, deep(Exists(x)(P.Apply(x))))
	assert.Nil(t, deep(Unique(x)(P.Apply(x))))
	assert.Nil(t, deep(x.SuchThat(P.Apply(x))))
	assert.Nil(t, deep(F.Eq(x.To(G.Apply(y, x)))))
	assert.Nil(t, deep(x.To(G.Apply(y, x)).Eq(F)))
	// ... and the bundle that owns all three reaches the same fixpoint it
	// always did, with no ping-pong.
	assert.Nil(t, BasicRewrite(ForAll(x)(P.Apply(x))))
	assert.Nil(t, BasicRewrite(x.SuchThat(P.Apply(x))))
	assertRewrite(t, TrivialNormalize, F.Eq(x.To(G.Apply(y, x))), ForAll(x)(F.Apply(x).Eq(G.Apply(y, x))))
	// A redex the expansion rules put under a binder stays put:
	// ∀P is ∀x.P(x), not P.
	forall := Const(FORALL.Meta(), MakeFun(MakeFun(TypeInd, TypeBool), TypeBool))
	assertRewrite(t, BasicRewrite, ext.WrapTerm(Apply(forall, P)), ForAll(x)(P.Apply(x)))

	// The key is η-invariant: g(s, λi.F(i)) and g(s, F) normalize alike.
	spelled, _ := Normalize(MakeProp(g.Apply(s, x.To(F.Apply(x))).Eq(y)))
	short, _ := Normalize(MakeProp(g.Apply(s, F).Eq(y)))
	assert.Equal(t, short.AlphaKey(), spelled.AlphaKey())
}

func TestHilbertRewrite(t *testing.T) {
	x := Var("x", TypeInd)
	a := Var("a", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))

	rewrite := DeepRewrite(hilbertRewrite)

	s := x.SuchThat(x.Eq(a))
	assertRewrite(t, rewrite, s, a)

	s = x.SuchThat(a.Eq(x))
	assertRewrite(t, rewrite, s, a)

	s = x.SuchThat(x.Eq(x))
	assert.Nil(t, rewrite(s))

	s = Const(
		core.MetaHilbert(),
		MakeFun(
			MakeFun(
				TypeInd,
				TypeBool),
			TypeInd)).Apply(P)
	assertRewrite(t, rewrite, s, x.SuchThat(P.Apply(x)))

	p := Var("p", TypeBool)
	q := Var("q", TypeBool)

	s = p.SuchThat(q)
	assert.Nil(t, rewrite(s))

	s = p.SuchThat(p.And(Not(q)).Or(q.And(Not(p))))
	assertRewrite(t, rewrite, s, Not(q))

	s = p.SuchThat(p.Imply(q).And(q.Imply(ForAll(x)(p))))
	assertRewrite(t, rewrite, s, q)
}

func TestHilbertExistsRewrite(t *testing.T) {
	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	z := Var("z", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeInd, TypeInd, TypeBool))

	rewrite := HilbertExistsRewrite

	s := Not(P.Apply(z.SuchThat(Q.Apply(x, y, z))))
	assert.Nil(t, rewrite(s))

	s = Q.Apply(z, y.SuchThat(Q.Apply(x, y, z)), x)
	assert.Nil(t, rewrite(s))

	s = P.Apply(x.SuchThat(F)).Or(P.Apply(x.SuchThat(P.Apply(x))))
	assertRewrite(t, rewrite, s,
		P.Apply(x.SuchThat(F)).Or(Exists(x)(P.Apply(x))))

	s = Not(P.Apply(x.SuchThat(P.Apply(x))))
	assertRewrite(t, rewrite, s,
		Not(Exists(x)(P.Apply(x))))

	s = ForAll(x)(Q.Apply(x, y.SuchThat(Q.Apply(x, y, z)), z)).Eq(P.Apply(x.SuchThat(P.Apply(x))))
	assertRewrite(t, rewrite, s,
		ForAll(x)(Exists(y)(Q.Apply(x, y, z))).Eq(Exists(x)(P.Apply(x))))

	s = Not(P.Apply(Apply(Const(core.MetaHilbert(), MakeFun(MakeFun(TypeInd, TypeBool), TypeInd)), P)))
	assertRewrite(t, rewrite, s,
		Not(Apply(Const(
			EXISTS.Meta(),
			MakeFun(MakeFun(TypeInd, TypeBool), TypeBool)), P)))

	s = P.To(P.Apply(x.SuchThat(P.Apply(x))))
	assertRewrite(t, rewrite, s,
		P.To(Exists(x)(P.Apply(x))))

	s = ForAll(x, z)(Q.Apply(x, y.SuchThat(Q.Apply(x, y, z)), z).And(P.Apply(x.SuchThat(P.Apply(x)))))
	assertRewrite(t, rewrite, s,
		ForAll(x, z)(Exists(y)(Q.Apply(x, y, z)).And(Exists(x)(P.Apply(x)))))
}

func TestQuantifierRewrite(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeInd))

	rewrite := DeepRewrite(QuantifierRewrite)

	quantifierType := MakeFun(MakeFun(TypeInd, TypeBool), TypeBool)
	forall := Const(FORALL.Meta(), quantifierType)
	exists := Const(EXISTS.Meta(), quantifierType)
	unique := Const(UNIQUE.Meta(), quantifierType)

	s := ForAll(a)(P.Apply(a)).Eq(Apply(exists, P))
	assertRewrite(t, rewrite, s,
		ForAll(a)(P.Apply(a)).Eq(Exists(a)(P.Apply(a))))

	s = Exists(a)(P.Apply(a)).Eq(Apply(forall, P))
	assertRewrite(t, rewrite, s,
		Exists(a)(P.Apply(a)).Eq(ForAll(a)(P.Apply(a))))

	s = Unique(a)(P.Apply(a)).Eq(Apply(unique, P))
	assertRewrite(t, DeepRewrite(QuantifierRewrite, UniqueRewrite), s,
		Eq(Rhs(AltUnique(a.To(P.Apply(a)))),
			Rhs(AltUnique(a.To(P.Apply(a))))))

	assertRewrite(t, UniqueWitnessRewrite, Unique(a)(P.Apply(a)),
		Exists(a)(P.Apply(a).And(ForAll(b)(P.Apply(b).Imply(b.Eq(a))))))
	assert.Nil(t, UniqueWitnessRewrite(Exists(a)(P.Apply(a))))

	s = ForAll(P, a)(P.Apply(a))
	assertRewrite(t, rewrite, s, F)

	s = ForAll(P, a)(Not(P.Apply(a)))
	assertRewrite(t, rewrite, s, F)

	s = ForAll(a, Q)(a.Neq(Q.Apply(b)))
	assertRewrite(t, rewrite, s, F)

	s = ForAll(a, Q)(Q.Apply(b).Neq(a))
	assertRewrite(t, rewrite, s, F)

	s = Exists(P, a)(P.Apply(a))
	assertRewrite(t, rewrite, s, T)

	s = Exists(P, a)(Not(P.Apply(a)))
	assertRewrite(t, rewrite, s, T)

	s = Exists(a)(a.Eq(Q.Apply(b)))
	assertRewrite(t, rewrite, s, T)

	s = Exists(a)(Q.Apply(b).Eq(a))
	assertRewrite(t, rewrite, s, T)
}

func TestFunEqRewrite(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	aPrime := Var("a'", TypeInd)
	c := Var("c", TypeA)
	H := Var("H", MakeFun(TypeInd, TypeB))
	P := Var("P", MakeFun(TypeInd, TypeA, TypeB))
	Q := Var("Q", MakeFun(TypeInd, TypeA, TypeB))
	R := Var("R", MakeFun(TypeInd, TypeA))

	rewrite := DeepFunEqRewrite

	// (λa.P(a, b) = λa.Q(a, b)) = (b = R(a))
	s := a.To(P.Apply(a, c)).Eq(a.To(Q.Apply(a, c))).Eq(c.Eq(R.Apply(a)))
	// ∀a.(P(a, b) = Q(a, b)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(a)(P.Apply(a, c).Eq(Q.Apply(a, c))).Eq(c.Eq(R.Apply(a))))

	// (λa.P(b, c) = λaʹ.Q(b, c)) = (b = R(a))
	s = a.To(P.Apply(b, c)).Eq(aPrime.To(Q.Apply(b, c))).Eq(c.Eq(R.Apply(a)))
	// (P(b, c) = Q(b, c)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		P.Apply(b, c).Eq(Q.Apply(b, c)).Eq(c.Eq(R.Apply(a))))

	// (λa.P(a, b) = λaʹ.Q(aʹ, b)) = (b = R(a))
	s = a.To(P.Apply(a, c)).Eq(aPrime.To(Q.Apply(aPrime, c))).Eq(c.Eq(R.Apply(a)))
	// ∀a.(P(a, b) = Q(a, b)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(a)(P.Apply(a, c).Eq(Q.Apply(a, c))).Eq(c.Eq(R.Apply(a))))

	// (λa.P(a, b) = λaʹ.Q(aʹ, R(a))) = (b = R(a))
	s = a.To(P.Apply(a, c)).Eq(aPrime.To(Q.Apply(aPrime, R.Apply(a)))).Eq(c.Eq(R.Apply(a)))
	// ∀a.(P(a, b) = Q(a, R(a))) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(aPrime)(P.Apply(aPrime, c).Eq(Q.Apply(aPrime, R.Apply(a)))).Eq(c.Eq(R.Apply(a))))

	// (λa.P(a, b) = H) = (b = R(a))
	s = a.To(P.Apply(a, c)).Eq(H).Eq(c.Eq(R.Apply(a)))
	// ∀a.(P(a, b) = H(a)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(a)(P.Apply(a, c).Eq(H.Apply(a))).Eq(c.Eq(R.Apply(a))))

	// (H = λa.P(a, b)) = (b = R(a))
	s = H.Eq(a.To(P.Apply(a, c))).Eq(c.Eq(R.Apply(a)))
	// ∀a.(H(a) = P(a, b)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(a)(H.Apply(a).Eq(P.Apply(a, c))).Eq(c.Eq(R.Apply(a))))

	// (H = Hʹ) = (b = R(a))
	s = H.Eq(H.AssertVar().Rename()).Eq(c.Eq(R.Apply(a)))
	// ∀a.(H(a) = Hʹ(a)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(a)(H.Apply(a).Eq(Apply(H.AssertVar().Rename(), a))).Eq(c.Eq(R.Apply(a))))

	// (P = Q) = (b = R(a))
	s = P.Eq(Q).Eq(c.Eq(R.Apply(a)))
	// ∀a.∀b.(P(a, b) = Q(a, b)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(a, c)(P.Apply(a, c).Eq(Q.Apply(a, c))).Eq(c.Eq(R.Apply(a))))

	// (P = Q) = (b = R(a))
	s = P.Eq(Q).Eq(c.Eq(R.Apply(a)))
	// ∀a.∀b.(P(a, b) = Q(a, b)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(a, c)(P.Apply(a, c).Eq(Q.Apply(a, c))).Eq(c.Eq(R.Apply(a))))

	// (P(a) = Q(a)) = (b = R(a))
	s = P.Apply(a).Eq(Q.Apply(a)).Eq(c.Eq(R.Apply(a)))
	// ∀b.(P(a, b) = Q(a, b)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(c)(P.Apply(a, c).Eq(Q.Apply(a, c))).Eq(c.Eq(R.Apply(a))))

	// (λa.P(a) = λa.Q(a)) = (b = R(a))
	s = a.To(P.Apply(a)).Eq(a.To(Q.Apply(a))).Eq(c.Eq(R.Apply(a)))
	// ∀a.∀b.(P(a, b) = Q(a, b)) = (b = R(a))
	assertRewrite(t, rewrite, s,
		ForAll(a, c)(P.Apply(a, c).Eq(Q.Apply(a, c))).Eq(c.Eq(R.Apply(a))))

	// ((λa.(λb.P(b))(a)) = (λa.P(a)))
	s = a.To(b.To(P.Apply(b)).Apply(a)).Eq(a.To(P.Apply(a)))
	// (∀a.∀c.((λb.P(b))(a, c) = P(a, c)))
	assertRewrite(t, rewrite, s,
		ForAll(a, c)(b.To(P.Apply(b)).Apply(a, c).Eq(P.Apply(a, c))))
}

func TestBoolRewrite(t *testing.T) {
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	P := Var("P", MakeFun(TypeBool, TypeBool))
	assertPropAlphaEqual(t,
		DoubleNeg(a),
		testThm(Not(Not(a)).Eq(a)))

	rewrite := DeepRewrite(
		betaRewrite, BoolRewrite, DoubleNegRewrite, PushNegRewrite)

	s := a.Eq(b)
	assert.Nil(t, rewrite(s))

	s = a.Eq(F).Eq(b)
	assertRewrite(t, rewrite, s, Not(a).Eq(b))

	s = b.Imply(a.Eq(Not(a)))
	assertRewrite(t, rewrite, s, Not(b))

	s = b.Eq(Not(a).Eq(a))
	assertRewrite(t, rewrite, s, Not(b))

	s = b.Eq(Not(P.Apply(a)).Eq(b.To(P.Apply(b)).Apply(a)))
	assertRewrite(t, rewrite, s, Not(b))

	s = b.Eq(Not(b.To(P.Apply(b)).Apply(a)).Eq(P.Apply(a)))
	assertRewrite(t, rewrite, s, Not(b))

	s = a.Imply(Not(F))
	assertRewrite(t, rewrite, s, T)

	s = a.Imply(Not(T))
	assertRewrite(t, rewrite, s, Not(a))

	s = Not(F).Imply(Not(a))
	assertRewrite(t, rewrite, s, Not(a))

	s = Not(T).Imply(Not(a))
	assertRewrite(t, rewrite, s, T)

	s = a.Imply(Not(a))
	assertRewrite(t, rewrite, s, Not(a))

	s = Not(a).Imply(a)
	assertRewrite(t, rewrite, s, a)

	s = a.Imply(b.Eq(T))
	assertRewrite(t, rewrite, s, a.Imply(b))

	s = a.Imply(Eq(T, b))
	assertRewrite(t, rewrite, s, a.Imply(b))

	s = a.Imply(Not(F).Eq(b))
	assertRewrite(t, rewrite, s, a.Imply(b))

	s = a.Imply(F).Eq(b)
	assertRewrite(t, rewrite, s, Not(a).Eq(b))

	s = Not(Not(a)).Eq(b)
	assertRewrite(t, rewrite, s, a.Eq(b))

	s = Not(a.Xor(F)).Eq(b)
	assertRewrite(t, rewrite, s, Not(a).Eq(b))

	s = a.Xor(F).Eq(b)
	assertRewrite(t, rewrite, s, a.Eq(b))

	s = a.Eq(b).Eq(b.Eq(a))
	assertRewrite(t, rewrite, s, T)

	s = Not(a).Eq(Not(b))
	assertRewrite(t, rewrite, s, a.Eq(b))

	s = a.Xor(b).Eq(b.Xor(a))
	assertRewrite(t, rewrite, s, T)

	c := Var("c", TypeA) // Not a boolean

	s = ForAll(c)(b.Or(T))
	assertRewrite(t, rewrite, s, T)

	s = Exists(c)(F)
	assertRewrite(t, rewrite, s, F)

	s = Not(c.Eq(c)).Eq(b)
	assertRewrite(t, rewrite, s, Not(b))

	s = Not(a.Xor(a)).Eq(b)
	assertRewrite(t, rewrite, s, b)

	s = a.Eq(F).Eq(F).Eq(b)
	assertRewrite(t, rewrite, s, a.Eq(b))

	s = WrapTerm(F).Eq(WrapTerm(F).Eq(a)).Eq(b)
	assertRewrite(t, rewrite, s, a.Eq(b))

	s = WrapTerm(F).Eq(a).Eq(F).Eq(b)
	assertRewrite(t, rewrite, s, a.Eq(b))

	s = b.Or(a.And(F))
	assertRewrite(t, rewrite, s, b)

	s = b.And(Not(a).Or(a))
	assertRewrite(t, rewrite, s, b)

	s = a.To(P.Apply(a).And(b.To(P.Apply(b)).Apply(a))).Apply(b)
	assertRewrite(t, rewrite, s, P.Apply(b))

	s = b.Or(b.Imply(Not(a).And(a)))
	assertRewrite(t, rewrite, s, T)

	s = b.Eq(a.Imply(F))
	assertRewrite(t, rewrite, s, b.Eq(Not(a)))

	s = WrapTerm(F).Eq(a).Imply(F).Eq(b)
	assertRewrite(t, rewrite, s, a.Eq(b))

	s = a.Imply(F).Imply(F).Eq(b)
	assertRewrite(t, rewrite, s, a.Eq(b))

	s = b.To(a.Imply(F).Eq(F))
	assertRewrite(t, rewrite, s, b.To(a))

	s = b.To(P.Apply(a).Imply(b.To(P.Apply(b)).Apply(a)))
	assertRewrite(t, rewrite, s, b.To(T))

	s = Not(a).Or(a.Imply(F).Eq(F))
	assertRewrite(t, rewrite, s, T)

	s = b.And(WrapTerm(F).Eq(a).Imply(F))
	assertRewrite(t, rewrite, s, b.And(a))

	s = Not(Not(a.Imply(F).Eq(F))).Eq(WrapTerm(F).Eq(b.Imply(F)))
	assertRewrite(t, rewrite, s, a.Eq(b))

	s = ForAll(a)(a)
	assertRewrite(t, rewrite, s, F)

	s = ForAll(a)(Not(a))
	assertRewrite(t, rewrite, s, F)

	s = Exists(a)(a)
	assertRewrite(t, rewrite, s, T)

	s = Exists(a)(Not(a))
	assertRewrite(t, rewrite, s, T)

}

func TestPushNegRewrite(t *testing.T) {
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	c := Var("c", TypeInd)
	d := Var("d", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))

	rewrite := DeepRewrite(BoolRewrite, PushNegRewrite)

	s := b.Imply(Not(ForAll(c)(Not(P.Apply(c)))))
	assertRewrite(t, rewrite, s,
		b.Imply(Exists(c)(Not(Not(P.Apply(c))))))

	s = b.Eq(Not(Exists(c)(Not(P.Apply(c)))))
	assertRewrite(t, rewrite, s,
		b.Eq(ForAll(c)(Not(Not(P.Apply(c))))))

	s = b.Eq(Not(Exists(c)(Not(P.Apply(d)))))
	assertRewrite(t, rewrite, s,
		b.Eq(Not(Not(P.Apply(d)))))

	s = b.Eq(Not(ForAll(c)(Not(P.Apply(d)))))
	assertRewrite(t, rewrite, s,
		b.Eq(Not(Not(P.Apply(d)))))

	s = Not((a.Eq(b)).Eq(a))
	assertRewrite(t, rewrite, s,
		Not(a).Eq(b).Eq(a))

	s = Not((a.Eq(Not(b))).Eq(a))
	assertRewrite(t, rewrite, s,
		a.Eq(b).Eq(a))

	s = Not(Not(a).Eq(b)).Eq(a)
	assertRewrite(t, rewrite, s, a.Eq(b).Eq(a))
}

func TestBooleanDisjunctiveRewrite(t *testing.T) {
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	c := Var("c", TypeBool)
	s := a.Eq(b.Imply(c))
	assertRewrite(t, BasicRewritesWith(ImplyToOrRewrite, IffToOrRewrite), s,
		a.And(Not(b).Or(c)).Or(Not(a).And(b.And(Not(c)))))
}

func TestPrenexRewrite(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	c := WrapTerm(b.AssertVar().Rename())
	d := c.AssertVar().Rename()
	g := Var("g", TypeBool)
	h := g.AssertVar().Rename()
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool))

	rewrite := BasicRewritesWith(
		ImplyToOrRewrite,
		IffToOrRewrite,
		UniversalPrenexRewrite)

	// ∀a. P(a) ∧ ∀b. (Q(a) ∨ Q(b))
	s := ForAll(a)(P.Apply(a)).And(ForAll(b)(Q.Apply(a).Or(Q.Apply(b))))
	// ∀b. (P(b) ∧ (Q(a) ∨ Q(b)))
	assertRewrite(t, rewrite, s,
		ForAll(b)(P.Apply(b).And(Q.Apply(a).Or(Q.Apply(b)))))

	// ∀b. (Q(a) ∨ Q(b)) ∧ ∀a. P(a)
	s = ForAll(b)(Q.Apply(a).Or(Q.Apply(b))).And(ForAll(a)(P.Apply(a)))
	// ∀b. ((Q(a) ∨ Q(b)) ∧ P(b))
	assertRewrite(t, rewrite, s,
		ForAll(b)(Q.Apply(a).Or(Q.Apply(b)).And(P.Apply(b))))

	// (P(a) ∨ ∃b. Q(b)) ⇒ ∀h. R(h)
	s = P.Apply(a).Or(Exists(b)(Q.Apply(b))).Imply(ForAll(g)(R.Apply(g)))
	// ∀b. ∀g. ((¬P(a) ∧ ¬Q(b)) ∨ R(g)) — the chain rule waits for the ∀b
	// hidden under the negation to surface, then pulls in chain order.
	assertRewrite(t, rewrite, s,
		ForAll(b, g)(Not(P.Apply(a)).And(Not(Q.Apply(b))).Or(R.Apply(g))))

	rewrite = BasicRewritesWith(
		ImplyToOrRewrite,
		IffToOrRewrite,
		ExistentialPrenexRewrite)

	// ∀h. R(h) ⇒ (P(a) ∨ ∃b. Q(b))
	s = ForAll(g)(R.Apply(g)).Imply(P.Apply(a).Or(Exists(b)(Q.Apply(b))))
	// ∃h. ∃b. (¬R(h) ∨ (P(a) ∨ Q(b)))
	assertRewrite(t, rewrite, s,
		Exists(g, b)(Not(R.Apply(g)).Or(P.Apply(a).Or(Q.Apply(b)))))

	// ∃a. P(a) ∨ ∃b. (Q(a) ∧ Q(b))
	s = Exists(a)(P.Apply(a)).Or(Exists(b)(Q.Apply(a).And(Q.Apply(b))))
	// ∃b. (P(b) ∨ (Q(a) ∧ Q(b)))
	assertRewrite(t, rewrite, s,
		Exists(b)(P.Apply(b).Or(Q.Apply(a).And(Q.Apply(b)))))

	// ∃b. (Q(a) ∧ Q(b)) ∨ ∃a. P(a)
	s = Exists(b)(Q.Apply(a).And(Q.Apply(b))).Or(Exists(a)(P.Apply(a)))
	// ∃b. ((Q(a) ∧ Q(b)) ∨ P(b))
	assertRewrite(t, rewrite, s,
		Exists(b)(Q.Apply(a).And(Q.Apply(b)).Or(P.Apply(b))))

	rewrite = ChainRewrites(
		BasicRewritesWith(
			UniqueRewrite,
			ImplyToOrRewrite,
			IffToOrRewrite,
			ExistentialPrenexRewrite),
		DeepRewrite(UniversalPrenexRewrite))

	// P(a) ∨ ∃!b. Q(b)
	s = P.Apply(a).Or(Unique(b)(Q.Apply(b)))
	// (∃b.(∀c.(∀d.(P(a) ∨ (Q(b) ∧ ((¬Q(c) ∨ ¬Q(d)) ∨ (c = d)))))))
	assertRewrite(t, rewrite, s,
		Exists(b)(
			ForAll(c, d)(P.Apply(a).Or((Q.Apply(b)).And(Not(Q.Apply(c)).Or(Not(Q.Apply(d))).Or(c.Eq(d)))))))

	// ∀h. R(h) ⇔ (P(a) ∨ ∃b. Q(b))
	s = ForAll(g)(R.Apply(g)).Eq(P.Apply(a).Or(Exists(b)(Q.Apply(b))))
	// ∃b. ∃g. ∀h. ∀c. (R(h) ∧ (P(a) ∨ Q(b))) ∨ (¬R(h) ∧ ¬P(a) ∧ ¬Q(c)))
	assertRewrite(t, rewrite, s,
		Exists(b, g)(ForAll(h, c)(
			R.Apply(h).And(P.Apply(a).Or(Q.Apply(b))).Or(
				Not(R.Apply(g)).And(Not(P.Apply(a)).And(Not(Q.Apply(c))))))))
}

func TestChainArrange(t *testing.T) {
	x0 := Var("x0", TypeBool)
	x1 := Var("x1", TypeBool)
	x2 := Var("x2", TypeBool)
	x3 := Var("x3", TypeBool)

	s := x0.Or(x1.Or(x2.Or(x3)))
	assertRewrite(t,
		AssocORRewrite,
		s,
		x0.Or(x1).Or(x2).Or(x3))

	s = x0.Or(x1).Or(x2).Or(x3)
	assert.Nil(t, AssocORRewrite(s))

	s = x0.And(x1)
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, -1, 1),
		testThm(s.Eq(
			x1.And(x0))))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 0, 1),
		testThm(s.Eq(s)))

	s = x0.And(x1.And(x1))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 0, 2),
		testThm(s.Eq(
			x0.And(x1).And(x1))))

	s = x0.And(x1.And(x2))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 0, 1),
		testThm(s.Eq(
			x0.And(x1).And(x2))))

	s = x0.And(x1).And(x2)
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, -1, 0),
		testThm(s.Eq(
			x0.And(x1.And(x2)))))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, -1, 1),
		testThm(s.Eq(
			x1.And(x0.And(x2)))))

	s = x0.And(x1.And(x2.And(x3)))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 2, 3),
		testThm(s.Eq(s)))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 1, 3),
		testThm(s.Eq(
			x0.And(x1.And(x3).And(x2)))))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 0, 2),
		testThm(s.Eq(
			x0.And(x2).And(x1.And(x3)))))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 0, 1),
		testThm(s.Eq(
			x0.And(x1).And(x2.And(x3)))))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, -1, 2),
		testThm(s.Eq(
			x2.And(x0.And(x1.And(x3))))))

	s = x0.And(x1.And(x2.And(x3))).And(x0)
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 3, 4),
		testThm(s.Eq(
			x0.And(x1).And(x2).And(x3.And(x0)))))

	s = x0.And(x1).And(x2.And(x0))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 0, 3),
		testThm(s.Eq(
			x0.And(x0).And(x1).And(x2))))

	s = x0.And(x1).And(x2).And(x3.And(x0))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 1, 3),
		testThm(s.Eq(
			x0.And(x1.And(x3)).And(x2).And(x0))))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, 2, 4),
		testThm(s.Eq(
			x0.And(x1).And(x2.And(x0)).And(x3))))

	s = x0.And(x1).And(x2.And(x3).And(x1))
	assertPropAlphaEqual(t,
		ArrangeANDChain(s, -1, 2),
		testThm(s.Eq(
			x2.And(x0.And(x1).And(x3.And(x1))))))

	s = x0.Or(x1).Or(x2).Or(x3)
	assertPropAlphaEqual(t,
		ArrangeORChain(s, 0, 1),
		testThm(s.Eq(s)))
	assertPropAlphaEqual(t,
		ArrangeORChain(s, -1, 3),
		testThm(s.Eq(
			x3.Or(x0.Or(x1).Or(x2)))))

	s = x0.Or(x1).Or(x2).Or(x0)
	assertPropAlphaEqual(t,
		ArrangeORChain(s, -1, 3),
		testThm(s.Eq(
			x0.Or(x0.Or(x1).Or(x2)))))

	s = x0.Or(x1.Or(x2.Or(x3)))
	assertPropAlphaEqual(t,
		ArrangeORChain(s, 1, 2),
		testThm(s.Eq(
			x0.Or(x1.Or(x2).Or(x3)))))
	assertPropAlphaEqual(t,
		ArrangeORChain(s, 0, 3),
		testThm(s.Eq(
			x0.Or(x3).Or(x1.Or(x2)))))
	assertPropAlphaEqual(t,
		ArrangeORChain(s, -1, 0),
		testThm(s.Eq(s)))

	s = x0.Or(x1.Or(x2)).Or(x0.Or(x3))
	assertPropAlphaEqual(t,
		ArrangeORChain(s, 0, 3),
		testThm(s.Eq(
			x0.Or(x0).Or(x1.Or(x2)).Or(x3))))
	assertPropAlphaEqual(t,
		ArrangeORChain(s, 2, 4),
		testThm(s.Eq(
			x0.Or(x1).Or(x2.Or(x3)).Or(x0))))

	s = x0.Or(x1.Or(x2.And(x3)))
	assertPropAlphaEqual(t,
		ArrangeORChain(s, 0, 2),
		testThm(s.Eq(
			x0.Or(x2.And(x3)).Or(x1))))

	s = x0.Or(x1.Or(x2)).Or(x0.Or(x3))
	assertPropAlphaEqual(t,
		ArrangeORChain(s, 1, 3),
		testThm(s.Eq(
			x0.Or(x1.Or(x0).Or(x2)).Or(x3))))

	s = x0.Eq(x1.Eq(x2)).Eq(x3)
	assertPropAlphaEqual(t,
		ArrangeIFFChain(s, 1, 2),
		testThm(s.Eq(s)))
	assertPropAlphaEqual(t,
		ArrangeIFFChain(s, -1, 3),
		testThm(s.Eq(
			x3.Eq(x0.Eq(x1.Eq(x2))))))
}

func TestBinaryOpRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	x0 := Var("x0", TypeBool)
	x1 := Var("x1", TypeBool)
	x2 := Var("x2", TypeBool)
	x3 := Var("x3", TypeBool)

	s := x0.And(x1.Or(x0.Or(x3).Or(x0.Or((x1)))))
	assertRewrite(t, distributeSimplifyANDOR, s,
		x0)

	s = x0.Or(x1.And(Not(x0).And(x3).And(Not(x0).And(Not(x1)))))
	assertRewrite(t, distributeSimplifyORAND, s,
		x0.Or(x1.And(x3.And(Not(x1)))))

	s = x0.And(x1).And(x2.And(x0))
	assertRewrite(t, MergeANDRewrite, s,
		x0.And(x1).And(x2))

	s = x0.Or(x1).Or(Not(x1).Or(x2))
	assertRewrite(t, MergeORRewrite, s, T)

	s = x0.And(x1).And(x2.And(x0))
	assertRewrite(t, SimplifyConjunct, s,
		x0.And(x1).And(x2))

	s = x0.And(x1).And(x2.And(Not(x0)))
	assertRewrite(t, SimplifyConjunct, s, F)

	s = x0.Or(x1.And(x2.And(x1.And(Not(x2)))))
	assertRewrite(t, SimplifyDisjunct, s, x0)

	s = (x0.Or(x1).Or(x2)).Or(x0)
	assertRewrite(t, SimplifyDisjunct, s,
		x0.Or(x1).Or(x2))

	s = Not(x0).Or(x1).Or(x2.Or(x0))
	assertRewrite(t, SimplifyDisjunct, s, T)

	s = (x0.Or(x1)).And(x0.Or(x2.Or(x1)))
	assertRewrite(t, SimplifyConjunct, s,
		x0.Or(x1))

	s = (x0.And(x1.And(x2))).Or(x0.And(x2))
	assertRewrite(t, SimplifyDisjunct, s,
		x0.And(x2))

	s = (x0.Or(x1)).And(Not(x1))
	assertRewrite(t, SimplifyConjunct, s,
		Not(x1).And(x0))

	s = (x0.Or(Not(x1)).Or(x2)).And(x1)
	assertRewrite(t, SimplifyConjunct, s,
		x1.And(x0.Or(x2)))

	s = x0.Or(x1.Or(x0)).And(x1.Or(x0.Or(Not(x1))))
	assertRewrite(t, SimplifyConjunct, s,
		x0.Or(x1))

	s = x0.And(x0.Or(x2)).And(Not(x0).Or(x1))
	assertRewrite(t, SimplifyConjunct, s,
		x0.And(x1))

	s = x0.And(Not(x1)).And(x2).Or(x1.And(x1))
	assertRewrite(t, SimplifyDisjunct, s,
		x1.Or(x0.And(x2)))

	s = (x0.And(x1)).And(x1.Or(x2)).And(Not(x0).Or(x1.Or(x2)))
	assertRewrite(t, SimplifyConjunct, s,
		x0.And(x1))

	s = (x0.And(x2).And(x1.And(x2))).Or(x0.And(x2.And(x0.And(x2))).Or(x1.And(x2).And(x1)))
	assertRewrite(t, SimplifyDisjunct, s,
		x0.And(x2).Or(x1.And(x2)))

	s = (Not(x0).Or(x1.Or(x2))).Or(x0.Or(x3))
	assertRewrite(t, SimplifyDisjunct, s, T)

	binaryOpRewrite := DeepRewrite(
		BoolRewrite,
		MergeANDRewrite,
		MergeORRewrite,
		simplifyANDORRewrite,
		simplifyORANDRewrite,
	)

	s = x0.And((x1).Or(x2.Or(x0))).Eq(x3)
	assertRewrite(t, binaryOpRewrite, s,
		x0.Eq(x3))

	s = x1.Or(x0.Or(x2)).And(x0).Eq(x3)
	assertRewrite(t, binaryOpRewrite, s,
		x0.Eq(x3))

	s = x1.And(x0.And(x2)).Or(x0).Eq(x3)
	assertRewrite(t, binaryOpRewrite, s,
		x0.Eq(x3))

	s = x0.And((x1).Or(x2.Or(Not(x0)))).Eq(x3)
	assertRewrite(t, binaryOpRewrite, s,
		x0.And((x1).Or(x2)).Eq(x3))

	s = Not(x0).Or((x1).And(x0.And(x2))).Eq(x3)
	assertRewrite(t, binaryOpRewrite, s,
		Not(x0).Or((x1).And(x2)).Eq(x3))
}

func TestSkolem(t *testing.T) {
	defer goleak.VerifyNone(t)
	a := Var("a", TypeInd)
	b := Var("b", TypeB)
	c := Var("c", TypeA)
	bPrime := Var("bf", MakeFun(TypeInd, TypeB))
	cPrime := Var("cf", MakeFun(TypeInd, TypeB, TypeA))
	P := Var("P", MakeFun(TypeInd, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeB, TypeBool))
	H := Var("H", MakeFun(TypeB, TypeA, TypeBool))

	assertPropAlphaEqual(t, Skolem(bPrime.AssertVar(), a.To(b.To(Q.Apply(a, b)))),
		testThm(
			ForAll(a)(Exists(b)(Q.Apply(a, b))).Eq(
				Exists(bPrime)(ForAll(a)(Q.Apply(a, bPrime.Apply(a)))))))

	rewrite := DeepRewrite(SkolemRewrite)

	s := Not(Exists(a)(ForAll(b, c)(P.Apply(a, c).Eq(H.Apply(b, c)))))
	assert.Nil(t, rewrite(s))

	s = Not(ForAll(a)(Exists(b)(ForAll(c)(P.Apply(a, c).Eq(H.Apply(b, c))))))
	assertRewrite(t, rewrite, s,
		Not(Exists(bPrime)(ForAll(a, c)(
			P.Apply(a, c).Eq(H.Apply(bPrime.Apply(a), c))))))

	s = Not(ForAll(a, b)(Exists(c)(P.Apply(a, c).Eq(H.Apply(b, c)))))
	assertRewrite(t, rewrite, s,
		Not(Exists(cPrime)(ForAll(a, b)(
			P.Apply(a, cPrime.Apply(a, b)).Eq(H.Apply(b, cPrime.Apply(a, b)))))))

	s = Not(ForAll(a, b)(Unique(c)(P.Apply(a, c).Eq(H.Apply(b, c)))))
	assertRewrite(t, rewrite, s,
		Not(Unique(cPrime)(ForAll(a, b)(
			(P.Apply(a, cPrime.Apply(a, b)).Eq(H.Apply(b, cPrime.Apply(a, b))))))))

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
	S := Var("S", MakeFun(TypeA, TypeA))

	s = ForAll(y)(Exists(x)(R.Apply(x, y)))
	assertRewrite(t, rewrite, s, Exists(f)(ForAll(y)(R.Apply(f.Apply(y), y))))

	s = ForAll(y)(Exists(x)(R.Apply(x, y).And(z.To(S.Apply(z)).Apply(y).Eq(x))))
	assertRewrite(t, rewrite, s,
		Exists(f)(ForAll(y)(R.Apply(f.Apply(y), y).And(S.Apply(y).Eq(f.Apply(y))))))

	s = ForAll(y)(Unique(x)(R.Apply(x, y).And(z.To(S.Apply(z)).Apply(y).Eq(x))))
	assertRewrite(t, rewrite, s,
		Unique(f)(ForAll(y)(R.Apply(f.Apply(y), y).And(S.Apply(y).Eq(f.Apply(y))))))
}

func TestForAllANDExistsOR(t *testing.T) {
	defer goleak.VerifyNone(t)
	a := Var("a", TypeInd)
	aPrime := WrapTerm(a.AssertVar().Rename())
	b := Var("b", TypeB)
	c := Var("c", TypeA)
	P := Var("P", MakeFun(TypeInd, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	H := Var("H", MakeFun(TypeB, TypeA, TypeBool))

	s := ForAll(a, b)(P.Apply(a, c).Or(H.Apply(b, c)))
	assert.Nil(t, DeepRewrite(ForAllANDRewrite)(s))

	s = ForAll(a)(aPrime.To(Q.Apply(aPrime)).Apply(a).And(Q.Apply(a)))
	assertRewrite(t, DeepRewrite(ForAllANDRewrite), s,
		ForAll(a)(aPrime.To(Q.Apply(aPrime)).Apply(a)).And(ForAll(a)(Q.Apply(a))))

	s = Exists(a, b)(P.Apply(a, c).And(H.Apply(b, c)))
	assert.Nil(t, DeepRewrite(ExistsORRewrite)(s))

	s = ForAll(a, c)(P.Apply(a, c).And(H.Apply(b, c)))
	assertRewrite(t, DeepRewrite(ForAllANDRewrite), s,
		ForAll(a, c)(P.Apply(a, c)).And(ForAll(c)(H.Apply(b, c))))

	s = Exists(a, c)(P.Apply(a, c).Or(H.Apply(b, c)))
	assertRewrite(t, DeepRewrite(ExistsORRewrite), s,
		Exists(a, c)(P.Apply(a, c)).Or(Exists(c)(H.Apply(b, c))))

	s = Exists(a)(Q.Apply(a).Or(aPrime.To(Q.Apply(aPrime)).Apply(a)))
	assertRewrite(t, DeepRewrite(ExistsORRewrite), s,
		Exists(a)(Q.Apply(a)).Or(Exists(a)(aPrime.To(Q.Apply(aPrime)).Apply(a))))

}

func TestForAllOR(t *testing.T) {
	defer goleak.VerifyNone(t)
	a := Var("a", TypeInd)
	b := Var("b", TypeB)
	c := Var("c", TypeA)
	d := Var("d", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	H := Var("H", MakeFun(TypeB, TypeA, TypeBool))

	assertForAllORRewrite := func(s *ext.TermWrapper, terms ...core.Term) {
		assertRewrite(t, ForAllORRewrite, s, Or(terms...))
	}

	s := P.Apply(a).Or(H.Apply(b, c)).Or(Q.Apply(a))
	assert.Nil(t, ForAllORRewrite(s))

	s = P.Apply(a).Or(H.Apply(b, c).Or(Q.Apply(a)))
	assertForAllORRewrite(s,
		P.Apply(a),
		H.Apply(b, c),
		Q.Apply(a))

	s = ForAll(a, b, c)(P.Apply(a).Or(H.Apply(b, c).Or(Q.Apply(a))))
	assertForAllORRewrite(s,
		ForAll(a)(P.Apply(a).Or(Q.Apply(a))),
		ForAll(b, c)(H.Apply(b, c)))

	s = ForAll(b, c, a)(P.Apply(a).Or(H.Apply(b, c).Or(Q.Apply(a))))
	assertForAllORRewrite(s,
		ForAll(b, c)(H.Apply(b, c)),
		ForAll(a)(P.Apply(a).Or(Q.Apply(a))))

	s = ForAll(b, c, a)(P.Apply(a).Or(Q.Apply(a)).Or(H.Apply(b, c)))
	assertForAllORRewrite(s,
		ForAll(b, c)(H.Apply(b, c)),
		ForAll(a)(P.Apply(a).Or(Q.Apply(a))))

	s = ForAll(b, c)(P.Apply(a).Or(Q.Apply(a)).Or(H.Apply(b, c)))
	assertForAllORRewrite(s,
		ForAll(b, c)(H.Apply(b, c)),
		P.Apply(a),
		Q.Apply(a))

	// Notice that this means ForAllOrRewrite is not merging identical terms.
	s = ForAll(a, d)(P.Apply(a).Or(P.Apply(d)))
	assertForAllORRewrite(s,
		ForAll(a)(P.Apply(a)),
		ForAll(a)(P.Apply(a)))

	s = P.Apply(a).Or(Q.Apply(a)).Or(H.Apply(b, c))
	assert.Nil(t, ForAllORRewrite(s))

	s = ForAll(a)(P.Apply(a).Or(Q.Apply(a)))
	assert.Nil(t, ForAllORRewrite(s))

	s = ForAll(d)(P.Apply(a).Or(Q.Apply(d)))
	assertForAllORRewrite(s,
		ForAll(d)(Q.Apply(d)),
		P.Apply(a))

	s = ForAll(a, b, c, d)(P.Apply(a).Or(Q.Apply(d)).Or(H.Apply(b, c)))
	assertForAllORRewrite(s,
		ForAll(a)(P.Apply(a)),
		ForAll(b, c)(H.Apply(b, c)),
		ForAll(d)(Q.Apply(d)))

	s = ForAll(d, c, b, a)(P.Apply(a).Or(Q.Apply(d)).Or(H.Apply(b, c)))
	assertForAllORRewrite(s,
		ForAll(d)(Q.Apply(d)),
		ForAll(c, b)(H.Apply(b, c)),
		ForAll(a)(P.Apply(a)))

	s = ForAll(a, b, c, d)(P.Apply(a).Eq(Q.Apply(d)).Or(H.Apply(b, c)))
	assertForAllORRewrite(s,
		ForAll(a, d)(P.Apply(a).Eq(Q.Apply(d))),
		ForAll(b, c)(H.Apply(b, c)))

	s = ForAll(c, b, a)(P.Apply(a).Or(Q.Apply(d)).Or(H.Apply(b, c)))
	assertForAllORRewrite(s,
		ForAll(c, b)(H.Apply(b, c)),
		ForAll(a)(P.Apply(a)),
		(Q.Apply(d)))

	rewrite := DeepRewrite(ExistsORRewrite, ForAllORRewrite, AssocORRewrite)
	s = Exists(d)(ForAll(c, b, a)(P.Apply(a).Or(Q.Apply(d)).Or(H.Apply(b, c))))
	assertRewrite(t, rewrite, s, Or(
		ForAll(c, b)(H.Apply(b, c)),
		ForAll(a)(P.Apply(a)),
		Exists(d)(Q.Apply(d))))

	s = Exists(a, d)(ForAll(c, b)(P.Apply(a).Or(Q.Apply(d)).Or(H.Apply(b, c))))
	assertRewrite(t, rewrite, s, Or(
		ForAll(c, b)(H.Apply(b, c)),
		Exists(a)(P.Apply(a)),
		Exists(d)(Q.Apply(d))))
}

func TestExistsAND(t *testing.T) {
	defer goleak.VerifyNone(t)
	a := Var("a", TypeInd)
	b := Var("b", TypeB)
	c := Var("c", TypeA)
	d := Var("d", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	H := Var("H", MakeFun(TypeB, TypeA, TypeBool))

	assertExistsANDRewrite := func(s *ext.TermWrapper, terms ...core.Term) {
		assertRewrite(t, ExistsANDRewrite, s, And(terms...))
	}

	s := P.Apply(a).And(H.Apply(b, c)).And(Q.Apply(a))
	assert.Nil(t, ExistsANDRewrite(s))

	s = P.Apply(a).And(H.Apply(b, c).And(Q.Apply(a)))
	assertExistsANDRewrite(s,
		P.Apply(a),
		H.Apply(b, c),
		Q.Apply(a))

	s = Exists(a, b, c)(P.Apply(a).And(H.Apply(b, c).And(Q.Apply(a))))
	assertExistsANDRewrite(s,
		Exists(a)(P.Apply(a).And(Q.Apply(a))),
		Exists(b, c)(H.Apply(b, c)))

	s = Exists(b, c, a)(P.Apply(a).And(H.Apply(b, c).And(Q.Apply(a))))
	assertExistsANDRewrite(s,
		Exists(b, c)(H.Apply(b, c)),
		Exists(a)(P.Apply(a).And(Q.Apply(a))))

	s = Exists(b, c, a)(P.Apply(a).And(Q.Apply(a)).And(H.Apply(b, c)))
	assertExistsANDRewrite(s,
		Exists(b, c)(H.Apply(b, c)),
		Exists(a)(P.Apply(a).And(Q.Apply(a))))

	s = Exists(b, c)(P.Apply(a).And(Q.Apply(a)).And(H.Apply(b, c)))
	assertExistsANDRewrite(s,
		Exists(b, c)(H.Apply(b, c)),
		P.Apply(a),
		Q.Apply(a))

	// Notice that this means ForAllOrRewrite is not merging identical terms.
	s = Exists(a, d)(P.Apply(a).And(P.Apply(d)))
	assertExistsANDRewrite(s,
		Exists(a)(P.Apply(a)),
		Exists(a)(P.Apply(a)))

	s = P.Apply(a).And(Q.Apply(a)).And(H.Apply(b, c))
	assert.Nil(t, ForAllORRewrite(s))

	s = Exists(a)(P.Apply(a).And(Q.Apply(a)))
	assert.Nil(t, ForAllORRewrite(s))

	s = Exists(d)(P.Apply(a).And(Q.Apply(d)))
	assertExistsANDRewrite(s,
		Exists(d)(Q.Apply(d)),
		P.Apply(a))

	s = Exists(a, b, c, d)(P.Apply(a).And(Q.Apply(d)).And(H.Apply(b, c)))
	assertExistsANDRewrite(s,
		Exists(a)(P.Apply(a)),
		Exists(b, c)(H.Apply(b, c)),
		Exists(d)(Q.Apply(d)))

	s = Exists(d, c, b, a)(P.Apply(a).And(Q.Apply(d)).And(H.Apply(b, c)))
	assertExistsANDRewrite(s,
		Exists(d)(Q.Apply(d)),
		Exists(c, b)(H.Apply(b, c)),
		Exists(a)(P.Apply(a)))

	s = Exists(a, b, c, d)(P.Apply(a).Eq(Q.Apply(d)).And(H.Apply(b, c)))
	assertExistsANDRewrite(s,
		Exists(a, d)(P.Apply(a).Eq(Q.Apply(d))),
		Exists(b, c)(H.Apply(b, c)))

	s = Exists(c, b, a)(P.Apply(a).And(Q.Apply(d)).And(H.Apply(b, c)))
	assertExistsANDRewrite(s,
		Exists(c, b)(H.Apply(b, c)),
		Exists(a)(P.Apply(a)),
		(Q.Apply(d)))

	rewrite := DeepRewrite(ForAllANDRewrite, ExistsANDRewrite, AssocANDRewrite)
	s = ForAll(d)(Exists(c, b, a)(P.Apply(a).And(Q.Apply(d)).And(H.Apply(b, c))))
	assertRewrite(t, rewrite, s, And(
		Exists(c, b)(H.Apply(b, c)),
		Exists(a)(P.Apply(a)),
		ForAll(d)(Q.Apply(d))))

	s = ForAll(a, d)(Exists(c, b)(P.Apply(a).And(Q.Apply(d)).And(H.Apply(b, c))))
	assertRewrite(t, rewrite, s, And(
		Exists(c, b)(H.Apply(b, c)),
		ForAll(a)(P.Apply(a)),
		ForAll(d)(Q.Apply(d))))
}

func TestAssocDistribute(t *testing.T) {
	defer goleak.VerifyNone(t)
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	c := Var("c", TypeBool)
	d := Var("d", TypeBool)

	s := a.Or(b.And(c).And(d.And(c)))
	assertRewrite(t, DistributeListORAND, s,
		a.Or(b).And(a.Or(c)).And(a.Or(d).And(a.Or(c))))

	s = a.Or(a.Or(b.And(c)).And(b.And(c)))
	assertRewrite(t, DistributeListORAND, s,
		a.Or(a.Or(b.And(c))).And(a.Or(b).And(a.Or(c))))

	s = a.And(a.And(b.Or(c)).Or(b.Or(c)))
	assertRewrite(t, DistributeListANDOR, s,
		a.And(a.And(b.Or(c))).Or(a.And(b).Or(a.And(c))))
}

func TestCondRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	Cond := ext.Cond
	deepCondElimRewrite := DeepRewrite(CondElimRewrite)
	deepCondSwapRewrite := DeepRewrite(CondSwapRewrite)

	a := Var("a", TypeB)
	b := Var("b", TypeB)
	c := Var("c", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeB, TypeBool))

	assert.Nil(t, CondElimRewrite((Cond(P.Apply(c), a, b))))
	assert.Nil(t, CondElimRewrite(c.To(Cond(P.Apply(c), a, b))))
	assert.Nil(t, CondElimRewrite(b.To(Cond(b.Eq(a), a, b)).Eq(b.To(Cond(b.Eq(a), b, a)))))

	assertRewrite(t, CondElimRewrite, Cond(T, a, b), a)
	assertRewrite(t, CondElimRewrite, Q.Apply(Cond(F, a, b)), Q.Apply(b))

	assert.Nil(t, CondElimRewrite(Cond(P.Apply(c), Cond(Q.Apply(b), a, b), b)))
	assert.Nil(t, deepCondElimRewrite(Cond(P.Apply(c), Cond(Q.Apply(b), a, b), b)))

	assertRewrite(t, CondElimRewrite,
		Q.Apply(Cond(P.Apply(c), Cond(Q.Apply(b), a, b), b)),
		P.Apply(c).Imply(Q.Apply(Cond(Q.Apply(b), a, b))).
			And(Not(P.Apply(c)).Imply(Q.Apply(b))))

	assertRewrite(t, CondElimRewrite,
		ForAll(Q)(Q.Apply(Cond(P.Apply(c), a, b))),
		ForAll(Q)(P.Apply(c).Imply(Q.Apply(a)).
			And(Not(P.Apply(c)).Imply(Q.Apply(b)))))

	assertRewrite(t, CondElimRewrite,
		Exists(Q, b)(Q.Apply(Cond(P.Apply(c), a, b))),
		Exists(Q, b)(P.Apply(c).Imply(Q.Apply(a)).
			And(Not(P.Apply(c)).Imply(Q.Apply(b)))))

	// Q(Cond(P(c), a, b)) ∧ Q(Cond(a = b, b, a))
	// Only rewrite the first cond term.
	assertRewrite(t, CondElimRewrite,
		Q.Apply(Cond(P.Apply(c), a, b)).And(Q.Apply(Cond(a.Eq(b), b, a))),
		P.Apply(c).Imply(Q.Apply(a)).And(Not(P.Apply(c)).Imply(Q.Apply(b))).
			And(Q.Apply(Cond(a.Eq(b), b, a))))

	assertRewrite(t, deepCondElimRewrite,
		Q.Apply(Cond(P.Apply(c), a, b)).And(Q.Apply(Cond(a.Eq(b), b, a))),
		P.Apply(c).Imply(Q.Apply(a)).And(Not(P.Apply(c)).Imply(Q.Apply(b))).
			And(a.Eq(b).Imply(Q.Apply(b)).And(a.Neq(b).Imply(Q.Apply(a)))))

	// ((∀Q.Q(Cond(P(c), a, b))) ∧ (∃Q.∃b.Q(Cond(P(c), b, a))))
	// rewrite both cond terms
	// → (∀Q.((P(c) ⇒ Q(a)) ∧ (¬P(c) ⇒ Q(b)))) ∧ (∃Q.∃b.((P(c) ⇒ Q(b)) ∧ (¬P(c) ⇒ Q(a))))
	assertRewrite(t, deepCondElimRewrite,
		ForAll(Q)(Q.Apply(Cond(P.Apply(c), a, b))).
			And(Exists(Q, b)(Q.Apply(Cond(P.Apply(c), b, a)))),
		ForAll(Q)(P.Apply(c).Imply(Q.Apply(a)).And(Not(P.Apply(c)).Imply(Q.Apply(b)))).
			And(Exists(Q, b)(P.Apply(c).Imply(Q.Apply(b)).And(Not(P.Apply(c)).Imply(Q.Apply(a))))))

	// (λc.Cond(b = a, a, b)) = (λc.Cond(b = a, b, a))
	// → ((b = a) ⇒ ((λc.a) = (λc.b))) ∧ ((b ≠ a) ⇒ ((λc.b) = (λc.a)))
	assertRewrite(t, CondElimRewrite,
		c.To(Cond(b.Eq(a), a, b)).Eq(c.To(Cond(b.Eq(a), b, a))),
		b.Eq(a).Imply(c.To(a).Eq(c.To(b))).And(b.Neq(a).Imply(c.To(b).Eq(c.To(a)))))

	// λa.Cond(P(c), a, b): no swap THROUGH the λ (that direction
	// would leave a COND of functions for the binder above to undo — see
	// condSwapRewriteImpl), and inside the body the COND is already
	// outermost, so the deep driver has nothing to do either.
	assert.Nil(t, CondSwapRewrite(a.To(Cond(P.Apply(c), a, b))))
	assert.Nil(t, deepCondSwapRewrite(a.To(Cond(P.Apply(c), a, b))))

	{
		// ∀c.Q(Cond(P(c), a, b))
		s := ForAll(c)(Q.Apply(Cond(P.Apply(c), a, b)))

		// ∀c.Q(Cond(P(c), a, b)) → ∀c.((P(c) ⇒ Q(a)) ∧ (¬P(c) ⇒ Q(b)))
		assertRewrite(t, CondElimRewrite,
			s,
			ForAll(c)(P.Apply(c).Imply(Q.Apply(a)).
				And(Not(P.Apply(c)).Imply(Q.Apply(b)))))
	}

	{
		s := Q.Apply(Cond(P.Apply(c), Cond(Q.Apply(a), a, b), Cond(Q.Apply(b), a, b)))
		assertRewrite(t, CondElimRewrite,
			s,
			P.Apply(c).
				Imply(Q.Apply(Cond(Q.Apply(a), a, b))).
				And(Not(P.Apply(c)).Imply(Q.Apply(Cond(Q.Apply(b), a, b)))))

		s = Cond(P.Apply(c), Q.Apply(Cond(Q.Apply(a), a, b)), Q.Apply(Cond(Q.Apply(b), a, b)))
		assertRewrite(t, CondElimRewrite,
			s,
			Cond(P.Apply(c),
				Q.Apply(a).Imply(Q.Apply(a)).And(Not(Q.Apply(a)).Imply(Q.Apply(b))),
				Q.Apply(Cond(Q.Apply(b), a, b))))

	}

	{
		// non bool term
		S0 := Var("S0", MakeFun(TypeB, TypeA))
		S1 := Var("S1", MakeFun(TypeB, TypeB))
		s := S0.Apply(Cond(P.Apply(c), a, b))
		assertRewrite(t, CondSwapRewrite,
			s,
			Cond(P.Apply(c), S0.Apply(a), S0.Apply(b)))

		// λc.S0(Cond(P(c), a, b))
		assert.Nil(t, CondSwapRewrite(c.To(s)))
		// λc.S0(Cond(P(c), a, b)) → λc.Cond(P(c), S0(a), S0(b))
		assertRewrite(t, deepCondSwapRewrite,
			c.To(s),
			c.To(Cond(P.Apply(c), S0.Apply(a), S0.Apply(b))))

		f := Var("f", MakeFun(MakeFun(TypeA, TypeA), TypeBool))
		// f(λc.S0(Cond(P(c), a, b)))
		assert.Nil(t, CondSwapRewrite(f.Apply(c.To(s))))
		// f(λc.S0(Cond(P(c), a, b))) → f(λc.Cond(P(c), S0(a), S0(b)))
		assertRewrite(t, deepCondSwapRewrite,
			f.Apply(c.To(s)),
			f.Apply(c.To(Cond(P.Apply(c), S0.Apply(a), S0.Apply(b)))))

		// S0(Cond(P(c), Cond(P(c), S1(a), S1(b)), b))
		// → Cond(P(c), S0(S1(a)), S0(b))
		assertRewrite(t, CondSwapRewrite,
			S0.Apply(Cond(P.Apply(c), Cond(P.Apply(c), S1.Apply(a), S1.Apply(b)), b)),
			Cond(P.Apply(c), S0.Apply(S1.Apply(a)), S0.Apply(b)))

		// S0(Cond(P(c), Cond(a = b, S1(a), S1(b)), b))
		s = S0.Apply(Cond(P.Apply(c), Cond(a.Eq(b), S1.Apply(a), S1.Apply(b)), b))
		// → Cond(P(c), S0(Cond(a = b, S1(a), S1(b))), S0(b))
		assertRewrite(t, CondSwapRewrite,
			s,
			Cond(P.Apply(c), S0.Apply(Cond(a.Eq(b), S1.Apply(a), S1.Apply(b))), S0.Apply(b)))
		// → Cond(P(c), Cond(a = b, S0(S1(a)), S0(S1(b))), S0(b))
		assertRewrite(t, deepCondSwapRewrite,
			s,
			Cond(P.Apply(c), Cond(a.Eq(b), S0.Apply(S1.Apply(a)), S0.Apply(S1.Apply(b))), S0.Apply(b)))

		// S0(Cond(P(c), Cond(P(c), S1(a), S1(b)), b))
		s = S0.Apply(Cond(P.Apply(c), Cond(P.Apply(c), S1.Apply(a), S1.Apply(b)), b))
		// → Cond(P(c), S0(S1(a)), S0(b))
		assertRewrite(t, CondSwapRewrite,
			s,
			Cond(P.Apply(c), S0.Apply(S1.Apply(a)), S0.Apply(b)))

		// S0(Cond(P(c), a, Cond(P(c), S1(a), S1(b))))
		s = S0.Apply(Cond(P.Apply(c), a, Cond(P.Apply(c), S1.Apply(a), S1.Apply(b))))
		// → Cond(P(c), S0(a), S0(S1(b)))
		assertRewrite(t, CondSwapRewrite,
			s,
			Cond(P.Apply(c), S0.Apply(a), S0.Apply(S1.Apply(b))))
	}

	{
		f := Var("f", MakeFun(TypeB, TypeB))
		x := Var("x", TypeB)
		R := Var("R", MakeFun(TypeB, TypeB, TypeBool))
		// ∀x.R(x, Cond(x = a, b, f(x)))
		s := ForAll(x)(R.Apply(x, Cond(x.Eq(a), b, f.Apply(x))))
		// direct rewrite fails, but deep rewrite succeeds.
		assertRewrite(t, CondElimRewrite, s,
			ForAll(x)(x.Eq(a).Imply(R.Apply(x, b)).And(x.Neq(a).Imply(R.Apply(x, f.Apply(x))))))
	}
}

// DeepRewriteWithEnv must rename a binder whose bound var collides with a free
// var of a hyp the leaf carries, so lifting the hyp-carrying equality back
// through that binder via .Abs() never trips the kernel's `v ∉ FV(hyps)` assert.
// The env-FREE DeepRewrite guards against the same hazard by DROPPING the fire
// at an AbsTerm whose binder is free in the returned equation's hyps —
// semantically α-blind so the correct behavior at a capture position IS
// "no rewrite" (see rewriteSubTerms). Both paths surface as `nil` at the
// binder; the env-aware path additionally rewrites the renamed body when
// the leaf matches something other than the binder itself.
func TestDeepRewriteWithEnvAvoidsCapture(t *testing.T) {
	p := Var("p", TypeBool)

	// A hyp-carrying leaf: rewrite the atom `p` to ⊤, carrying the hyp {p}
	// (contextEq(p) : {p} ⊢ p = ⊤).
	leaf := func(t Term) *PropWrapper {
		if t.AlphaEquals(p) {
			return contextEq(p)
		}
		return nil
	}
	// The leaf can carry the hyp `p`; anyHyp reports its free vars.
	anyHyp := func(pred func(Term) bool) bool { return pred(p) }

	// (a) No binder: the leaf fires; result is {p} ⊢ p = ⊤.
	w := DeepRewriteWithEnv(anyHyp, leaf)(p)
	if assert.NotNil(t, w, "should fire on the bare atom") {
		assert.True(t, Lhs(w).AlphaEquals(p))
		assert.True(t, Rhs(w).Equals(T))
	}

	// (b) Under a binder that REBINDS the name `p` (λp.p): the env-aware traversal
	// renames the binder before descending, so the leaf does not match the (now
	// renamed) bound occurrence — no capture, no panic, nothing rewrites.
	lam := p.To(p)
	assert.NotPanics(t, func() {
		assert.Nil(t, DeepRewriteWithEnv(anyHyp, leaf)(lam))
	})

	// (c) Env-FREE DeepRewrite: the leaf's α-blind match on the (unrenamed)
	// bound `p` returns {p} ⊢ p = ⊤. The AbsTerm case in rewriteSubTerms
	// detects that the binder `p` is free in the equation's hyps and drops
	// the fire — sound because the leaf's match was semantically spurious
	// (the binder's `p` and the leaf's free `p` are distinct under
	// α-equivalence). Previously this trip the kernel's `v ∉ FV(hyps)`
	// assert inside PropAbs; the guard replaces that panic with a clean nil.
	assert.NotPanics(t, func() {
		assert.Nil(t, DeepRewrite(leaf)(lam))
	})
}

// A rewrite that fires on every term (u → ¬u) models a self-feeding
// rule inside one deep-rewrite step — the shape the goal-level whistle
// in prover/tactic cannot see. The old loop ("caller's responsibility")
// spins forever; the whistle must cut the chain right past the
// size-derived backstop. Entry term x has size 1, so the backstop is 1:
// iteration 2 records the first post-backstop RHS (no ancestor yet),
// iteration 3 embeds it and breaks — the chain ends at exactly ¬³x.
func TestRewriteRecurWhistleStopsSelfFeed(t *testing.T) {
	feed := func(u Term) *PropWrapper {
		return WrapProp(testThm(ext.WrapTerm(u).Eq(ext.Not(u))))
	}

	x := Var("x", TypeBool)
	w := WrapProp(testThm(x.Eq(x))).RewriteConclRhsRecurWhistled(feed)
	require.NotNil(t, w)
	expected := x.Core()
	for range 3 {
		expected = ext.Not(expected).Core()
	}
	assert.True(t, Rhs(w).Equals(expected))
}

// A strictly shrinking chain must run to its true fixpoint no matter
// how far past the backstop it gets — here the entry size is 5·8+1 but
// every iteration shrinks, and the size gate keeps every larger
// earlier RHS out of the embedding check. This pins the
// bit-identical-replay guarantee for terminating chains of any length.
func TestRewriteRecurWhistleSparesShrinkingChain(t *testing.T) {
	strip := func(u Term) *PropWrapper {
		body := ext.MatchesNOT(u)
		if body == nil {
			return nil
		}
		return WrapProp(testThm(ext.WrapTerm(u).Eq(body)))
	}

	x := Var("x", TypeBool)
	deep := x.Core()
	for range 40 {
		deep = ext.Not(deep).Core()
	}

	w := WrapProp(testThm(ext.WrapTerm(deep).Eq(deep))).RewriteConclRhsRecurWhistled(strip)
	require.NotNil(t, w)
	assert.True(t, Rhs(w).AlphaEquals(x.Core()))
}

// A growth chain that stops on its own within the entry-size budget is
// untouched: the whistle never engages below the backstop, so a
// legitimate bounded expansion (k sites, k ≤ entry size) completes
// exactly as before. Entry term ¬⁵x (size 6), the rule fires 5 more
// times (until 10 ¬'s) — 5 iterations ≤ backstop 6, no recording, no
// cut.
func TestRewriteRecurWhistleSparesBoundedGrowth(t *testing.T) {
	countNots := func(u Term) int {
		n := 0
		for b := ext.MatchesNOT(u); b != nil; b = ext.MatchesNOT(b) {
			n++
			u = b
		}
		return n
	}
	growTo10 := func(u Term) *PropWrapper {
		if countNots(u) >= 10 {
			return nil
		}
		return WrapProp(testThm(ext.WrapTerm(u).Eq(ext.Not(u))))
	}

	x := Var("x", TypeBool)
	start := x.Core()
	for range 5 {
		start = ext.Not(start).Core()
	}
	w := WrapProp(testThm(ext.WrapTerm(start).Eq(start))).RewriteConclRhsRecurWhistled(growTo10)
	require.NotNil(t, w)
	assert.Equal(t, 10, countNots(Rhs(w)))
}

// DeepRewriteWhistled terminates on a self-feeding leaf — the
// composition shape of the multi-clause LeanRw path — where plain
// DeepRewrite would rescan forever. The growth chain allows three fires
// and the fourth is the cut: the result is the equality built by then,
// and the cut comes back with its event.
func TestDeepRewriteWhistledStopsSelfFeedingLeaf(t *testing.T) {
	x := Var("x", TypeBool)
	feed := func(u Term) *PropWrapper {
		if u.Equals(x) || ext.MatchesNOT(u) != nil {
			return WrapProp(testThm(ext.WrapTerm(u).Eq(ext.Not(u))))
		}
		return nil
	}

	// Tripwire observability: one event for the cut call, carrying the
	// number of the fire that was cut and the trajectory budget — the
	// entry's size, 1, raised to two fires for the one leaf.
	var events []skeleton.WhistleEvent
	skeleton.OnWhistleFire = func(ev skeleton.WhistleEvent) { events = append(events, ev) }
	t.Cleanup(func() { skeleton.OnWhistleFire = nil })
	firesBefore := skeleton.WhistleFires()

	w, cut := DeepRewriteWhistled(noHyps, feed)(x.Core())
	require.NotNil(t, w)
	require.NotNil(t, cut)
	assert.True(t, Lhs(w).Equals(x.Core()))
	expected := x.Core()
	for range _FIRE_GROWTH_FLOOR {
		expected = ext.Not(expected).Core()
	}
	assert.True(t, Rhs(w).Equals(expected))

	assert.Equal(t, int64(1), skeleton.WhistleFires()-firesBefore)
	require.Len(t, events, 1)
	assert.Equal(t, "DeepRewriteWhistled", events[0].Driver)
	assert.Equal(t, _FIRE_GROWTH_FLOOR+1, events[0].Depth)
	assert.Equal(t, 2, events[0].Budget)
	require.NotNil(t, events[0].Term)
	assert.True(t, events[0].Term.Equals(x.Core()))
	assert.Equal(t, events[0].Depth, cut.Depth)

	// The unreported form makes the same cut and tells no one else.
	firesBefore = skeleton.WhistleFires()
	w, cut = DeepRewriteWhistledUnreported(noHyps, feed)(x.Core())
	require.NotNil(t, cut)
	assert.True(t, Rhs(w).Equals(expected))
	assert.Equal(t, int64(0), skeleton.WhistleFires()-firesBefore)
	assert.Len(t, events, 1)
}

// A cut ends the call: no leaf is tried after the fire that was refused.
// The self-feeding leaf sits beside sixty atoms the walk has not reached
// when the fourth fire is cut, and a walk that went on would offer each
// of them to both leaves.
func TestDeepRewriteWhistledTriesNoLeafAfterTheCut(t *testing.T) {
	x := Var("x", TypeBool)
	hits, after := 0, 0
	feed := func(u Term) *PropWrapper {
		if hits > _FIRE_GROWTH_FLOOR {
			after++
		}
		if u.Equals(x) || ext.MatchesNOT(u) != nil {
			hits++
			return WrapProp(testThm(ext.WrapTerm(u).Eq(ext.Not(u))))
		}
		return nil
	}
	idle := func(Term) *PropWrapper {
		if hits > _FIRE_GROWTH_FLOOR {
			after++
		}
		return nil
	}
	entry := ext.WrapTerm(x)
	for i := range 60 {
		entry = entry.And(Var(core.TermName(fmt.Sprintf("v%d", i)), TypeBool))
	}

	w, cut := DeepRewriteWhistled(noHyps, feed, idle)(entry.Core())
	require.NotNil(t, w)
	require.NotNil(t, cut)
	assert.Equal(t, _FIRE_GROWTH_FLOOR+1, hits, "the growth chain allows its floor of fires and cuts the next")
	assert.Zero(t, after, "no leaf is tried once the call is cut")
}

// A cascade through every rule at one site is within the trajectory
// budget whatever the entry's size: each rule fires once and the
// normalizer once after it. Each right side here is a β-redex over the
// next constant, so the raw terms the trajectory would record repeat one
// shape, and on a budget of the entry's two nodes the third rule's fire
// would be cut.
func TestDeepRewriteWhistledBudgetCoversACascade(t *testing.T) {
	const links = 4
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	preds := make([]*ext.TermWrapper, links+1)
	for i := range preds {
		preds[i] = ext.TestConst(core.TermName(fmt.Sprintf("cascade%d", i)), MakeFun(TypeA, TypeBool))
	}
	leaves := make([]Rewrite, 0, links+1)
	for i := range links {
		leaves = append(leaves, func(u Term) *PropWrapper {
			head, args := ext.MatchesApply(u)
			if head == nil || len(args) != 1 || !head.Equals(preds[i].Core()) {
				return nil
			}
			redex := x.To(preds[i+1].Apply(x)).Apply(args[0])
			return WrapProp(testThm(ext.WrapTerm(u).Eq(redex)))
		})
	}
	leaves = append(leaves, BetaRewrite)

	before := skeleton.WhistleFires()
	w, cut := DeepRewriteWhistled(noHyps, leaves...)(preds[0].Apply(y).Core())
	require.Nil(t, cut)
	require.NotNil(t, w)
	assert.True(t, Rhs(w).Equals(preds[links].Apply(y).Core()))
	assert.Equal(t, before, skeleton.WhistleFires())
}

// The growth-chain whistle cuts a growing tower at its fourth rung even
// when the entry term is LARGE — the shape of the simp_with pin
// (cardinality.HasSizeClauses and comprehension membership feeding each other): on a big entry,
// the trajectory check's free-budget window admits entry-size-many
// unchecked fires, each recursing into a bigger term, so before the
// growth blade existed this ran entry-size fires (~padded size here,
// with a full HO-unify walk per fire in the live composition) instead
// of 3. The tower must stop at exactly the effective growth backstop —
// a single-rule composition gets max(_FIRE_GROWTH_FLOOR, 1+1) = the floor —
// independent of entry size.
func TestDeepRewriteWhistledCutsGrowthChainOnLargeEntry(t *testing.T) {
	x := Var("x", TypeBool)
	feed := func(u Term) *PropWrapper {
		if u.Equals(x) || ext.MatchesNOT(u) != nil {
			return WrapProp(testThm(ext.WrapTerm(u).Eq(ext.Not(u))))
		}
		return nil
	}

	// Pad the entry so its size (and hence the trajectory budget) is far
	// larger than the backstop: x ∧ v1 ∧ v2 ∧ … ∧ v60.
	entry := ext.WrapTerm(x)
	for i := range 60 {
		entry = entry.And(Var(core.TermName(fmt.Sprintf("v%d", i)), TypeBool))
	}

	w, cut := DeepRewriteWhistled(noHyps, feed)(entry.Core())
	require.NotNil(t, w)
	require.NotNil(t, cut)

	countNots := func(u Term) int {
		n := 0
		for b := ext.MatchesNOT(u); b != nil; b = ext.MatchesNOT(b) {
			n++
			u = b
		}
		return n
	}
	// The rewritten x sits at the leftmost conjunct spine; find it.
	maxNots := 0
	var walk func(u Term)
	walk = func(u Term) {
		if n := countNots(u); n > maxNots {
			maxNots = n
		}
		if l, r, ok := ext.MatchesAND(u); ok {
			walk(l)
			walk(r)
		}
	}
	walk(Rhs(w))
	assert.Equal(t, _FIRE_GROWTH_FLOOR, maxNots,
		"tower must stop at the growth backstop, not run out the entry-size budget")
}

// A LONE fire with a huge RHS is legitimate: its size witnesses a big
// rule TEMPLATE (a definitional expansion), not divergence — divergence
// is a property of fire SEQUENCES, owned by the permutation gate /
// growth chain / trajectory blades. The removed max(64, 2×entry)
// single-fire cap suppressed exactly such expansions
// (set unfolds of the intersection-of / union-of class on small goals) and, the
// whistle policy being part of replay semantics, baked the suppression
// into proofs recorded while it was live.
func TestDeepRewriteWhistledAllowsBigSingleFire(t *testing.T) {
	x := Var("x", TypeBool)
	// RHS: a conjunction of ~80 fresh vars on a size-1 entry term —
	// far beyond the removed cap.
	big := ext.WrapTerm(Var("y0", TypeBool))
	for i := 1; i < 80; i++ {
		big = big.And(Var(core.TermName(fmt.Sprintf("y%d", i)), TypeBool))
	}
	expand := func(u Term) *PropWrapper {
		if u.Equals(x) {
			return WrapProp(testThm(ext.WrapTerm(u).Eq(big)))
		}
		return nil
	}
	w, cut := DeepRewriteWhistled(noHyps, expand)(x.Core())
	require.Nil(t, cut)
	require.NotNil(t, w, "a single big-template fire must be allowed")
	assert.True(t, Rhs(w).AlphaEquals(big.Core()))
}

func TestDeepRewriteWhistledAvoidsBoundRuleVariable(t *testing.T) {
	j := core.Var("J", core.MakeVarType("A"))
	f := core.Var("f", core.MakeFun(core.MakeFun(j.Type(), j.Type()), j.Type()))
	p := core.Var("p", core.MakeFun(j.Type(), core.TypeBool()))
	rhs := core.Apply(f, core.Abs(j, j))
	rule := core.Eq(j, rhs)
	target := core.Apply(p, j)
	anyHyp := func(pred func(Term) bool) bool { return pred(rule) }
	before := skeleton.WhistleFires()
	w, cut := DeepRewriteWhistled(anyHyp,
		ContextEqRewriteOrdered(new(PreCNFCache), rule, true, true))(target)
	require.Nil(t, cut)
	require.NotNil(t, w)
	assert.True(t, Lhs(w).AlphaEquals(target))
	assert.True(t, Rhs(w).AlphaEquals(core.Apply(p, rhs)))
	assert.Equal(t, before, skeleton.WhistleFires())
}

// noHyps is the anyHyp of a walk whose leaves carry no hypothesis.
func noHyps(func(Term) bool) bool { return false }

// uncut is a whistled rewrite as a plain one, for a test whose rewrite
// the whistle has no call to cut: a cut fails the test.
func uncut(t *testing.T, whistled WhistledRewrite) Rewrite {
	return func(u Term) *PropWrapper {
		w, cut := whistled(u)
		require.Nil(t, cut, "the whistle cut a rewrite that terminates")
		return w
	}
}
