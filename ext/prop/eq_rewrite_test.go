package prop

import (
	"context"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

func TestEqRewrite(t *testing.T) {
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	z := Var("z", TypeBool)
	a := Var("a", TypeA)
	f := Var("f", MakeFun(TypeBool, TypeBool, TypeBool))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool, TypeBool))

	rewrite := EqRewrite

	// Not an equality
	s := x.To(f.Apply(x))
	assert.Panics(t, func() { rewrite(testProp(x))(s) })

	// Nothing to rewrite
	s = x.To(f.Apply(x))
	w := rewrite(testProp(y.Eq(x)))(s)
	assert.Nil(t, w)

	s = x.And(y).And(y)
	w = rewrite(testProp(x.And(y).Eq(x)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(x.And(y))))
	assertPropAlphaEqual(t,
		w.RewriteConclRhsRecur(rewrite(testProp(x.And(y).Eq(x)))),
		testProp(s.Eq(x)))

	s = a.To(P.Apply(a))
	w = rewrite(testProp(a.To(P.Apply(a)).Eq(P)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(P)))

	s = a.To(P.Apply(a))
	w = rewrite(testProp(a.To(P.Apply(a)).Eq(Q)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(Q)))

	s = x.To(f.Apply(y))
	w = rewrite(testProp(y.Eq(y.To(x).Apply(x))))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(x.To(f.Apply(y.To(x).Apply(x))))))

	s = z.To(f.Apply(y))
	w = rewrite(testProp(y.Eq(y.To(x).Apply(x))))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(z.To(f.Apply(y.To(x).Apply(x))))))

	s = f.Apply(ForAll(a)(x.Imply(P.Apply(a))), x)
	w = rewrite(testProp(a.To(P.Apply(a)).Eq(P)))(s)
	assert.Nil(t, w)

	s = ForAll(a)(P.Apply(a).And(R.Apply(a, x)))
	w = rewrite(testProp(a.To(R.Apply(a, x)).Eq(Q), R.Apply(a, x)))(s)
	assertPropAlphaEqual(t, w,
		testProp(s.Eq(ForAll(a)(P.Apply(a).And(Q.Apply(a)))), R.Apply(a, x)))

	s = ForAll(a, x)(f.Apply(P.Apply(a).And(x), y))
	w = rewrite(testProp(a.To(x.To(P.Apply(a).And(x))).Eq(R)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(ForAll(a, x)(f.Apply(R.Apply(a, x), y)))))

	s = a.To(ForAll(a)(P.Apply(a).And(Q.Apply(a))).And(Q.Apply(a)))
	w = rewrite(testProp(Eq(a.To(P.Apply(a)), Q)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(
		a.To(ForAll(a)(Q.Apply(a).And(Q.Apply(a))).And(Q.Apply(a))))))

	s = ForAll(a, x)(R.Apply(a, x).And(y).And(z))
	w = rewrite(testProp(a.To(x.To(R.Apply(a, x).And(y))).Eq(a.To(x.To(z)))))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(
		ForAll(a, x)(z.And(z)))))

	// λx.f(x) --> λx.f(y)
	s = x.To(f.Apply(x))
	// x = y
	w = rewrite(testProp(x.Eq(y)))(s)
	assert.Nil(t, w)

	// λx.f(x) --> λx.(λy.z)
	s = x.To(f.Apply(x))
	// f(x) = λy.z
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z))))(s)
	assert.Nil(t, w)

	// f(x, x) --> x
	s = f.Apply(x, f.Apply(x, x))
	// f(x, f(x, x)) = x
	w = rewrite(testProp(f.Apply(x, x).Eq(x)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(f.Apply(x, x))))
	assertPropAlphaEqual(t,
		w.RewriteConclRhsRecur(rewrite(testProp(f.Apply(x, x).Eq(x)))),
		testProp(s.Eq(x)))

	// λx.f(x) , f(x) is abstracted, returns nil
	s = x.To(f.Apply(x))
	// x = t ⊢ f(x) = λy.z
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z)), x.Eq(y)))(s)
	assert.Nil(t, w)

	// λx.(f(x) = f(z)) --> λx.(f(x) = (λy.z))
	s = x.To(f.Apply(x).Eq(f.Apply(z)))
	// x = t ⊢ f(z) = λy.z
	w = rewrite(testProp(f.Apply(z).Eq(y.To(z)), x.Eq(y)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(x.To(f.Apply(x).Eq(y.To(z)))), x.Eq(y)))

	// λx.f(y) not changed.
	s = x.To(f.Apply(y))
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z))))(s)
	assert.Nil(t, w)

	// f(x, y) --> (λy.z)(y)
	s = f.Apply(x, y)
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z))))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(y.To(z).Apply(y))))
	assert.Panics(t, func() { w.AsThmCert() })

	// with hyp
	s = f.Apply(x, y)
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z)), x))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(y.To(z).Apply(y)), x))
	assert.Panics(t, func() { w.AsThmCert() })

	// f(y, x) not changed.
	s = f.Apply(y, x)
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z))))(s)
	assert.Nil(t, w)

	// a --> εa.P(a)
	s = P.Apply(a)
	// P(a) = P(εa.P(a))
	w = rewrite(testProp(a.Eq(a.SuchThat(P.Apply(a)))))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(P.Apply(a.SuchThat(P.Apply(a))))))
}

func TestEqReplacementRewrite(t *testing.T) {
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	z := Var("z", TypeBool)
	f := Var("f", MakeFun(TypeBool, TypeBool, TypeBool))
	P := Var("P", MakeFun(TypeBool, TypeBool))

	rewrite := EqReplacementRewrite

	// Not an equality
	s := x.To(f.Apply(x))
	assert.Panics(t, func() { rewrite(testProp(x))(s) })

	// Equality rewrite once.
	s = f.Apply(x, y)
	assertRewrite(t, rewrite(testThm(x.Eq(x.And(z)))),
		s, f.Apply(x.And(z), y))

	// λx.f(x)
	s = x.To(f.Apply(x))
	// x = t ⊢ f(x) = λy.z, because the hyp contains x, no rewrite
	assert.Nil(t, rewrite(testProp(f.Apply(x).Eq(y.To(z)), x.Eq(y)))(s))
	// ⊢ f(x) = λy.z rewrites s to λx.λy.z
	assertRewrite(t,
		rewrite(testProp(f.Apply(x).Eq(y.To(z)))), s, x.To(y.To(z)))

	// (λx.f(x))(z) -> (λy.f(y))(z)
	s = x.To(f.Apply(x)).Apply(z)
	// λy.f(y) = λy.f(y)
	assert.Nil(t, rewrite(Refl(y.To(f.Apply(y))))(s))
	// λy.f(y) = λx.f(x)
	assertRewrite(t,
		rewrite(testThm(y.To(f.Apply(y)).Eq((x.To(f.Apply(y)))))),
		s, x.To(f.Apply(y)).Apply(z))

	// λx.f(x, f(x, x)) --> λx.f(x, x)
	s = x.To(f.Apply(x, f.Apply(x, x)))
	// f(x, x) = x
	assertRewrite(t,
		rewrite(testThm(f.Apply(x, x).Eq(x))),
		s, x.To(f.Apply(x, x)))

	s = ForAll(x)(P.Apply(x))
	assertRewrite(t, rewrite(testThm(P.Apply(x).Eq(x.Eq(y)))),
		s, ForAll(x)(x.Eq(y)))

	// λx.(f(x) = f(z)) --> λx.(f(x) = (λy.z))
	s = x.To(f.Apply(x).Eq(f.Apply(z)))
	// x = t ⊢ f(z) = λy.z, with hyp.
	assertPropAlphaEqual(t,
		rewrite(testProp(f.Apply(z).Eq(y.To(z)), x.Eq(y)))(s),
		testProp(s.Eq(x.To(f.Apply(x).Eq(y.To(z)))), x.Eq(y)))

	// λx.(f(x) = f(z)) --> λx.(f(x) = (λy.z))
	s = x.To(f.Apply(x).Eq(f.Apply(z)))
	// x = t ⊢ λx.f(x) = λy.z, with hyp.
	assert.Nil(t, rewrite(testProp(x.To(f.Apply(x)).Eq(x.To(y.To(z))), x.Eq(y)))(s))

	// Equality rewrite once, nothing to rewrite.
	s = f.Apply(x, y)
	assert.Nil(t, rewrite(testThm(z.Eq(x.And(z))))(s))

	// Equality rewrite once with hyp.
	s = f.Apply(x, y)
	assertPropAlphaEqual(t,
		rewrite(testThm(x.Eq(x.And(z)), x))(s),
		testThm(s.Eq(f.Apply(x.And(z), y)), x))

	// If equality is not thm, result is not thm.
	w := rewrite(testProp(x.Eq(x.And(z)), x))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(f.Apply(x.And(z), y)), x))
	assert.Panics(t, func() { w.AsThmCert() })
}

func TestBoundVarRewrite(t *testing.T) {
	a := Var("a", TypeBool).AssertVar()
	b := Var("b", TypeBool).AssertVar()
	c := Var("c", TypeBool).AssertVar()
	P := Var("P", MakeFun(TypeBool, TypeBool))
	Q := Var("Q", MakeFun(TypeBool, TypeBool, TypeBool))

	s := ForAll(a, b)(Q.Apply(a, b))
	assertTermEqual(t, Rhs(BoundVarRewrite(a, c)(s)), ForAll(c, b)(Q.Apply(c, b)))
	assertTermEqual(t, Rhs(BoundVarRewrite(b, c)(s)), ForAll(a, c)(Q.Apply(a, c)))
	assertTermEqual(t, Rhs(BoundVarRewrite(a, b)(s)), ForAll(c, b)(Q.Apply(c, b)))
	assertTermEqual(t, Rhs(BoundVarRewrite(b, a)(s)), ForAll(a, c)(Q.Apply(a, c)))

	s = Q.Apply(a, ForAll(b)(P.Apply(b)))
	assert.Nil(t, BoundVarRewrite(a, b)(s))
	assertTermEqual(t, Rhs(BoundVarRewrite(b, a)(s)), Q.Apply(a, ForAll(a)(P.Apply(a))))

	s = Exists(a)(Q.Apply(a, ForAll(b)(P.Apply(b))))
	assertTermEqual(t, Rhs(BoundVarRewrite(a, b)(s)),
		Exists(c)(Q.Apply(c, ForAll(b)(P.Apply(b)))))
	assertTermEqual(t, Rhs(BoundVarRewrite(b, a)(s)),
		Exists(a)(Q.Apply(a, ForAll(c)(P.Apply(c)))))
}

func TestUnifyEq(t *testing.T) {
	getProps := func(eq Prop, t Term) []Prop {
		return slices.Collect(unifyEq(context.Background(), eq, t))
	}

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(MakeFun(TypeA, TypeA), TypeA))

	var eq *PropWrapper
	var s *ext.TermWrapper
	var eqs []Prop

	eq = MakeProp(a.To(b.To(Q.Apply(a, b))).Eq(c.To(P)))

	s = b.To(c.To(Q.Apply(b, c)))
	eqs = getProps(eq, s)
	assert.Equal(t, len(eqs), 1)
	assertPropAlphaEqual(t, eqs[0], eq)

	s = c.To(Q.Apply(b, c))
	eqs = getProps(eq, s)
	assert.Equal(t, len(eqs), 1)
	assertPropAlphaEqual(t, eqs[0],
		MakeProp(s.Eq(c.To(P).Apply(b))))

	s = b.To(Q.Apply(b, c))
	eqs = getProps(eq, s)
	assert.Nil(t, eqs)

	s = Q.Apply(b)
	eqs = getProps(eq, s)
	assert.Equal(t, len(eqs), 1)
	assertPropAlphaEqual(t, eqs[0],
		MakeProp(s.Eq(c.To(P).Apply(b))))

	s = a.To(b.To(c.To(Q.Apply(b, c))))
	eqs = getProps(eq, s)
	assert.Nil(t, eqs)

	s = Q.Apply(b, b)
	eqs = getProps(eq, s)
	assert.Equal(t, len(eqs), 1)
	assertPropAlphaEqual(t, eqs[0],
		MakeProp(s.Eq(c.To(P).Apply(b, b))))

	eq = MakeProp(a.To(b.To(Q.Apply(b, a))).Eq(c.To(P)))

	s = b.To(c.To(Q.Apply(b, c)))
	eqs = getProps(eq, s)
	assert.Nil(t, eqs)

	s = c.To(Q.Apply(c, b))
	eqs = getProps(eq, s)
	assert.Equal(t, len(eqs), 1)
	assertPropAlphaEqual(t, eqs[0],
		MakeProp(s.Eq(c.To(P).Apply(b))))

	s = Q.Apply(b)
	eqs = getProps(eq, s)
	assert.Nil(t, eqs)

	s = Q.Apply(b, b)
	eqs = getProps(eq, s)
	assert.Equal(t, len(eqs), 1)
	assertPropAlphaEqual(t, eqs[0],
		MakeProp(s.Eq(c.To(P).Apply(b, b))))

	eq = MakeProp(R.To(R.Apply(a)).Eq(g))

	s = a
	eqs = getProps(eq, s)
	assert.Equal(t, len(eqs), 2)
	assertPropAlphaEqual(t, eqs[0],
		MakeProp(s.Eq(g.Apply(b.To(a)))))
	assertPropAlphaEqual(t, eqs[1],
		MakeProp(s.Eq(g.Apply(b.To(b)))))

	s = R.Apply(a)
	eqs = getProps(eq, s)
	assert.Equal(t, len(eqs), 2)
	assertPropAlphaEqual(t, eqs[0],
		MakeProp(s.Eq(g.Apply(R))))
	assertPropAlphaEqual(t, eqs[1],
		MakeProp(s.Eq(g.Apply(b.To(R.Apply(a))))))
}

func TestUnifyEqRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	z := Var("z", TypeBool)
	a := Var("a", TypeA)
	f := Var("f", MakeFun(TypeBool, TypeBool, TypeBool))
	g := Var("g", MakeFun(MakeFun(TypeA, TypeBool), TypeBool))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool, TypeBool))

	rewrite := unifyEqRewrite

	// Not an equality
	s := x.To(f.Apply(x))
	assert.Panics(t, func() { rewrite(testProp(x))(s) })

	// Nothing to rewrite
	s = x.To(f.Apply(x))
	w := rewrite(testProp(y.Eq(x)))(s)
	assert.Nil(t, w)

	// Nothing to rewrite because the equality would cause infinite loop.
	s = x.To(f.Apply(y))
	w = rewrite(testProp(y.Eq(x.And(y))))(s)
	assert.Nil(t, w)

	// Nothing to rewrite because the equality would cause infinite loop.
	s = x.To(f.Apply(y))
	w = rewrite(testProp(y.Eq(x.To(y).Apply(x))))(s)
	assert.Nil(t, w)

	s = a.To(P.Apply(a))
	w = rewrite(testProp(a.To(P.Apply(a)).Eq(P)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(P)))

	s = a.To(P.Apply(a))
	w = rewrite(testProp(a.To(P.Apply(a)).Eq(Q)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(a.To(Q.Apply(a)))))

	s = x.To(f.Apply(y))
	w = rewrite(testProp(y.Eq(y.To(x).Apply(x))))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(x.To(f.Apply(y.To(x).Apply(x))))))

	s = z.To(f.Apply(y))
	w = rewrite(testProp(y.Eq(y.To(x).Apply(x))))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(z.To(f.Apply(y.To(x).Apply(x))))))

	s = f.Apply(ForAll(a)(x.Imply(P.Apply(a))), x)
	assert.Nil(t, rewrite(testProp(a.To(P.Apply(a)).Eq(P)))(s))

	s = ForAll(a)(P.Apply(a).And(R.Apply(a, x)))
	w = rewrite(testProp(a.To(R.Apply(a, x)).Eq(Q), R.Apply(a, x)))(s)
	assertPropAlphaEqual(t, w,
		testProp(s.Eq(ForAll(a)(P.Apply(a).And(Q.Apply(a)))), R.Apply(a, x)))

	s = R.Apply(a, x).And(P.Apply(a))
	w = rewrite(testProp(a.To(y.To(R.Apply(a, y).And(P.Apply(a)))).Eq(R), R.Apply(a, x)))(s)
	assertPropAlphaEqual(t, w,
		testProp(s.Eq(R.Apply(a, x)), R.Apply(a, x)))

	s = ForAll(a, x)(f.Apply(P.Apply(a).And(x), y))
	w = rewrite(testProp(a.To(x.To(P.Apply(a).And(x))).Eq(R)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(ForAll(a, x)(f.Apply(R.Apply(a, x), y)))))

	s = a.To(ForAll(a)(P.Apply(a).And(Q.Apply(a))).And(Q.Apply(a)))
	w = rewrite(testProp(Eq(a.To(P.Apply(a)), Q)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(
		a.To(ForAll(a)(Q.Apply(a).And(Q.Apply(a))).And(Q.Apply(a))))))

	// λx.f(x) --> λx.f(y)
	s = x.To(f.Apply(x))
	// x = y
	w = rewrite(testProp(x.Eq(y)))(s)
	assert.Nil(t, w)

	// λx.f(x) --> λx.(λy.z)
	s = x.To(f.Apply(x))
	// f(x) = λy.z
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z))))(s)
	assert.Nil(t, w)

	// f(x, x) --> x
	s = f.Apply(x, f.Apply(x, x))
	// f(x, f(x, x)) = x
	w = rewrite(testProp(f.Apply(x, x).Eq(x)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(f.Apply(x, x))))
	assertPropAlphaEqual(t,
		w.RewriteConclRhsRecur(rewrite(testProp(f.Apply(x, x).Eq(x)))),
		testProp(s.Eq(x)))

	// λx.f(x) , f(x) is abstracted, returns nil
	s = x.To(f.Apply(x))
	// x = t ⊢ f(x) = λy.z
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z)), x.Eq(y)))(s)
	assert.Nil(t, w)

	// λx.(f(x) = f(z)) --> λx.(f(x) = (λy.z))
	s = x.To(f.Apply(x).Eq(f.Apply(z)))
	// x = t ⊢ f(z) = λy.z
	w = rewrite(testProp(f.Apply(z).Eq(y.To(z)), x.Eq(y)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(x.To(f.Apply(x).Eq(y.To(z)))), x.Eq(y)))

	// λx.f(y) not changed.
	s = x.To(f.Apply(y))
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z))))(s)
	assert.Nil(t, w)

	// f(x, y) --> (λy.z)(y)
	s = f.Apply(x, y)
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z))))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(y.To(z).Apply(y))))
	assert.Panics(t, func() { w.AsThmCert() })

	// with hyp
	s = f.Apply(x, y)
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z)), x))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(y.To(z).Apply(y)), x))
	assert.Panics(t, func() { w.AsThmCert() })

	// f(y, x) not changed.
	s = f.Apply(y, x)
	w = rewrite(testProp(f.Apply(x).Eq(y.To(z))))(s)
	assert.Nil(t, w)

	// a --> εa.P(a)
	s = P.Apply(a)
	// P(a) = P(εa.P(a))
	w = rewrite(testProp(a.Eq(a.SuchThat(P.Apply(a)))))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(P.Apply(a.SuchThat(P.Apply(a))))))

	s = Q.Apply(a)
	w = rewrite(testProp(P.To(Q.Apply(a)).Eq(g)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(g.Apply(P))))

	s = Q.Apply(a)
	w = rewrite(testProp(P.To(P.Apply(a)).Eq(g)))(s)
	assertPropAlphaEqual(t, w, testProp(s.Eq(g.Apply(Q))))
}

func TestContextRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	I := Var("Inv", MakeFun(TypeA, TypeA))
	One := Var("One", TypeA)

	s0 := x.Eq(I.Apply(x))
	s1 := ForAll(x)(x.Eq(I.Apply(x)))
	assert.Nil(t, ContextEqRewrite(s0, true)(s1))

	assertSimplify := func(s0, s1 Term, simplifed Term) {
		rewrite := ChainRewrites(ContextEqRewrite(s0, true), BasicRewrite)
		assertPropAlphaEqual(t, rewrite(s1).AsThmCert(),
			MakeProp(Eq(s1, simplifed), s0))
	}

	s0 = One.Eq(I.Apply(One))
	s1 = I.Apply(One).Eq(One)
	assertSimplify(s0, s1, T)

	s0 = One.Eq(I.Apply(One))
	s1 = ForAll(x)(P.Apply(I.Apply(I.Apply(One)), x).Eq(x))
	assertSimplify(s0, s1, ForAll(x)(P.Apply(I.Apply(One), x).Eq(x)))

	s0 = I.Apply(One).Eq(One)
	s1 = ForAll(x)(P.Apply(I.Apply(I.Apply(One)), x).Eq(x))
	assertSimplify(s0, s1, ForAll(x)(P.Apply(I.Apply(One), x).Eq(x)))

	s0 = x.Neq(I.Apply(x))
	s1 = (One.Eq(I.Apply(One))).Or(x.Eq(I.Apply(x)))
	assertSimplify(s0, s1, One.Eq(I.Apply(One)))

	s0 = Q.Apply(I.Apply(x))
	s1 = Q.Apply(I.Apply(x)).Or(x.Eq(One))
	assertSimplify(s0, s1, T)

	s0 = Q.Eq(x.To(y.Eq(x)))
	s1 = ForAll(x)(y.Eq(x))
	assertSimplify(s0, s1, ForAll(x)(Q.Apply(x)))

	s0 = ForAll(x)(x.Eq(I.Apply(x)))
	s1 = ForAll(x)(P.Apply(I.Apply(I.Apply(x)), x).Eq(x))
	assertSimplify(s0, s1, ForAll(x)(P.Apply(x, x).Eq(x)))

	s0 = ForAll(x)(x.Neq(y))
	s1 = z.Eq(y)
	assertSimplify(s0, s1, F)

	PIxx := P.Apply(I.Apply(x), x)
	s0 = ForAll(x)(One.Eq(PIxx))
	s1 = ForAll(x)(P.Apply(I.Apply(PIxx), PIxx).Eq(PIxx))
	assertSimplify(s0, s1, P.Apply(I.Apply(One), One).Eq(One))
}

func TestTermDiff(t *testing.T) {
	// Helper function to verify TermDiff results
	verify := func(_ string,
		s0, s1, expectedL, expectedR Term) {
		rewriteLeft, rewriteRight := TermDiff(s0, s1)
		assert.True(t, rewriteLeft != nil || rewriteRight != nil)
		if rewriteLeft != nil {
			assert.Equal(t, rewriteLeft.NumHyps(), 1)
			s := rewriteLeft.Hyp(0)
			assertTermEqual(t, s, Eq(expectedL, expectedR))
			assertPropAlphaEqual(t, rewriteLeft,
				MakeProp(Eq(s0, s1), s))
		} else {
			assert.NotNil(t, rewriteRight)
			assert.Equal(t, rewriteRight.NumHyps(), 1)
			s := rewriteRight.Hyp(0)
			assertTermEqual(t, s, Eq(expectedR, expectedL))
			assertPropAlphaEqual(t, rewriteRight,
				MakeProp(Eq(s1, s0), Eq(expectedR, expectedL)))
		}

		// Test symmetry: s1 -> s0 should give expectedR = expectedL
		rewriteLeft, rewriteRight = TermDiff(s1, s0)
		assert.True(t, rewriteLeft != nil || rewriteRight != nil)
		if rewriteLeft != nil {
			s := rewriteLeft.Hyp(0)
			assertTermEqual(t, s, Eq(expectedR, expectedL))
			assertPropAlphaEqual(t, rewriteLeft,
				MakeProp(Eq(s1, s0), s))
		} else {
			assert.NotNil(t, rewriteRight)
			assert.Equal(t, rewriteRight.NumHyps(), 1)
			s := rewriteRight.Hyp(0)
			assertTermEqual(t, s, Eq(expectedL, expectedR))
			assertPropAlphaEqual(t, rewriteRight,
				MakeProp(Eq(s0, s1), Eq(expectedL, expectedR)))
		}

	}

	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	z := Var("z", TypeBool)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	f := Var("f", MakeFun(TypeBool, TypeBool, TypeBool))
	g := Var("g", MakeFun(TypeBool, TypeBool))
	h := Var("h", MakeFun(TypeBool, TypeBool))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	S := Var("S", MakeFun(TypeA, TypeA, TypeBool))
	T := Var("T", MakeFun(TypeA, TypeA, TypeBool))

	// Test case 1: Simple replacement with multiple occurrences
	// f(Q(a), Q(a)) -> f(R(a), R(a))
	// Should return Q = R (the minimal difference)
	{
		fBinary := Var("fBinary", MakeFun(TypeBool, TypeBool, TypeBool))
		verify("Test case 1",
			fBinary.Apply(Q.Apply(a), Q.Apply(a)),
			fBinary.Apply(R.Apply(a), R.Apply(a)),
			Q, R)
	}

	// Test case 2: returns whole term (trivial but correct)
	{
		P := Var("P", MakeFun(TypeA, TypeBool, TypeBool, TypeBool))
		S := Var("S", MakeFun(TypeA, TypeBool))
		s0 := P.Apply(a, Q.Apply(a), Q.Apply(a))
		s1 := P.Apply(a, R.Apply(a), S.Apply(a))
		verify("Test case 2", s0, s1, s0, s1)

	}

	// Test case 3: Nested replacement f(g(x)) -> f(h(x))
	// Should return g = h (the minimal difference)
	verify("Test case 3",
		f.Apply(g.Apply(x), y),
		f.Apply(h.Apply(x), y),
		g, h)

	// Test case 4: Complete term replacement
	// f(x, y) -> g(z)
	verify("Test case 4",
		f.Apply(x, y),
		g.Apply(z),
		f.Apply(x, y), g.Apply(z))

	// Test case 5: Q(a) -> Q(S(a))
	// Should return a -> S(a)
	{
		S := Var("S", MakeFun(TypeA, TypeA))
		verify("Test case 5",
			Q.Apply(a),
			Q.Apply(S.Apply(a)),
			a, S.Apply(a))
	}

	// Test case 6: Complex nested structure with multiple occurrences
	// f(g(h(x)), g(h(x))) -> f(g(h(y)), g(h(y)))
	// Should return x = y
	verify("Test case 6",
		f.Apply(g.Apply(h.Apply(x)), g.Apply(h.Apply(x))),
		f.Apply(g.Apply(h.Apply(y)), g.Apply(h.Apply(y))),
		x, y)

	// Test case 7: Binary operators
	// x ∧ y -> z ∧ y (should return x = z)
	verify("Test case 7",
		x.And(y),
		z.And(y),
		x, z)

	// Test case 8: More complex binary operator case
	// (x ∧ y) ∨ (x ∧ z) -> (x ∧ y) ∨ (z ∧ y)
	// Should return x ∧ z = z ∧ y
	verify("Test case 8",
		x.And(y).Or(x.And(z)),
		x.And(y).Or(z.And(y)),
		x.And(z), z.And(y))

	// Test case 9: Partial match
	{

		// x ∧ y -> (x = z) ∧ y
		// Should return x = (x = z)
		s0 := x.And(y)
		s1 := x.Eq(z).And(y)
		verify("Test case 9a",
			s0, s1,
			x, x.Eq(z))

		// f(x, x) -> x ⇔ x
		// f -> ⇔
		verify("Test case 9b",
			f.Apply(x, x), x.Eq(x),
			f, core.IFF())
	}

	{

		// Test case 10: Equalities with different side types
		// a = a -> x ⇔ x
		// Should return the whole term replacement
		verify("Test 10a",
			a.Eq(a), x.Eq(x),
			a.Eq(a), x.Eq(x))

		// x ∧ x -> x ⇔ x
		// Should return the whole term replacement
		verify("Test 10b",
			x.And(x), x.Eq(x),
			x.And(x), x.Eq(x))
	}

	// Test case 11: Deep nesting with consistent replacement
	// f(f(f(x))) -> f(f(f(y)))
	// Should return x = y
	verify("Test case 11",
		f.Apply(f.Apply(f.Apply(x, x), x), x),
		f.Apply(f.Apply(f.Apply(y, y), y), y),
		x, y)

	// Test case 12: Replacement under universal quantifier
	// ∀a. P(a) ∧ R(a) -> ∀a. Q(a) ∧ R(a)
	// Should return P = Q which is the minimal replacement
	{
		R := Var("R", MakeFun(TypeA, TypeBool))
		verify("Test 12",
			ForAll(a)(P.Apply(a).And(R.Apply(a))),
			ForAll(a)(Q.Apply(a).And(R.Apply(a))),
			P, Q)
	}

	// Test case 13: Nested quantifiers
	// ∀a. ∃b. S(a, b) -> ∀a. ∃b. T(a, b)
	// Should return S = T
	verify("Test 13",
		ForAll(a)(Exists(b)(S.Apply(a, b))),
		ForAll(a)(Exists(b)(T.Apply(a, b))),
		S, T)

	// Test case 14: Mixed free and bound variables
	// Should return P = Q which is the minimal replacement
	verify("Test 14",
		a.To(P.Apply(a).And(x)),
		a.To(Q.Apply(a).And(x)),
		P, Q)

	// Test case 15: Multiple occurrences under binder
	// ∃a. P(a) ∨ P(a) -> ∃a. Q(a) ∨ Q(a)
	// Should return P = Q
	verify("Test 15",
		Exists(a)(P.Apply(a).Or(P.Apply(a))),
		Exists(a)(Q.Apply(a).Or(Q.Apply(a))),
		P, Q)

	// Test case 16: Partial binding - only some variables are bound
	// λa. S(a, b) -> λa. T(a, b)
	// where b is free, should return S = T
	verify("Test 16",
		a.To(S.Apply(a, b)),
		a.To(T.Apply(a, b)),
		S, T)

	// Test case 17: Complex case with multiple abstraction levels
	// ∀x.∃y. (P(x) ∧ Q(y)) -> ∀x.∃y. (R(x) ∧ Q(y))
	// Should return P = R
	{
		Px := Var("Px", MakeFun(TypeBool, TypeBool))
		Qy := Var("Qy", MakeFun(TypeBool, TypeBool))
		Rx := Var("Rx", MakeFun(TypeBool, TypeBool))

		verify("Test 17",
			ForAll(x)(Exists(y)(Px.Apply(x).And(Qy.Apply(y)))),
			ForAll(x)(Exists(y)(Rx.Apply(x).And(Qy.Apply(y)))),
			Px, Rx)
	}

	// Test case 18: Non-trivial case with lambda term as replacement
	// ∃a. P(a) -> ∃a. (λb.b=c)(a) where b,c are of TypeA
	// Should return P = λb.b=c (non-trivial right side)
	{
		c := Var("c", TypeA)
		verify("Test 18",
			Exists(a)(P.Apply(a)),
			Exists(a)(b.To(b.Eq(c)).Apply(a)),
			P, b.To(b.Eq(c)))
	}

	// Test case 19: Test that TermDiff correctly handles type compatibility
	// ∃a. Q(a) -> ∃a. T(a, a)
	// TermDiff should find λa.Q(a) = λa.T(a,a)
	verify("Test 19",
		Exists(a)(Q.Apply(a)),
		Exists(a)(T.Apply(a, a)),
		a.To(Q.Apply(a)), a.To(T.Apply(a, a)))

	// Test case 20: Non symmetric case
	// R(x, Q(y, z)) -> R(y, Q(y, z))
	// TermDiff should find x = y
	// R(y, Q(y, z)) -> R(x, Q(y, z))
	// TermDiff should find R(y) = R(x)
	{
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		z := Var("z", TypeA)
		R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
		Q := Var("Q", MakeFun(TypeA, TypeA, TypeA))
		verify("Test 20a",
			R.Apply(x, Q.Apply(y, z)),
			R.Apply(y, Q.Apply(y, z)),
			x, y)
		verify("Test 20b",
			R.Apply(x, Q.Apply(y, z)),
			R.Apply(x, Q.Apply(x, z)),
			y, x)
	}

	// Test case 21: the result is abs term
	// f(λx.(x ≠ y)) -> f(λx.(z ≠ x))
	// Should return λx.(x = y) = λx.(z = x)
	{
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		z := Var("z", TypeA)
		f := Var("f", MakeFun(MakeFun(TypeA, TypeBool), TypeA))
		verify("Test 21",
			f.Apply(x.To(x.Neq(y))),
			f.Apply(x.To(z.Neq(x))),
			x.To(x.Eq(y)), x.To(z.Eq(x)))
	}
}

// TestUnifyEqRewrite_RefusesHigherOrderSelfEmbed asserts that the
// unify-aware self-embedding guard refuses the set_comprehension identity-definition
// shape, which the syntactic ext.IsSub guard misses.
//
// Rule shape (the canonical form set_comprehension's definition normalizes to):
//
//	λp. λx. p(x)  =  λp. λx. set_comprehension(p)(x)
//
// IsSub(l, r) is false syntactically (l is not a subterm of r as
// strings of operators), but the unifier matches l's body `p(x)`
// against r's body `set_comprehension(p)(x)` via `p ↦ set_comprehension(p)`. So when the rule
// is admitted and the outer merged-tactic fixpoint re-applies it on
// its own RHS, the result keeps growing: `q(a) → set_comprehension(q)(a) →
// set_comprehension(set_comprehension(q))(a) → …`. The guard at eq_rewrite.go probes the
// rule's effect on a single instance of its LHS, then on the result,
// and refuses if both steps fire.
func TestUnifyEqRewrite_RefusesHigherOrderSelfEmbed(t *testing.T) {
	defer goleak.VerifyNone(t)

	setComprehension := Var("set_comprehension", MakeFun(MakeFun(TypeA, TypeBool), MakeFun(TypeA, TypeBool)))
	p := Var("p", MakeFun(TypeA, TypeBool))
	x := Var("x", TypeA)
	l := p.To(x.To(p.Apply(x)))
	r := p.To(x.To(setComprehension.Apply(p).Apply(x)))
	rule := testProp(l.Eq(r))

	// IsSub-only check at line 329 misses the higher-order shape —
	// asserting this pins the requirement that the broader guard exists.
	assert.False(t, ext.IsSub(l, r),
		"sanity: syntactic IsSub is intentionally insufficient for higher-order self-embed")

	q := Var("q", MakeFun(TypeA, TypeBool))
	a := Var("a", TypeA)
	target := q.Apply(a)

	// The rule, if admitted, would produce a rewritable RHS — the bug.
	// With the guard, unifyEqRewrite returns NilRewrite, which yields
	// nil for any target.
	w := unifyEqRewrite(rule)(target)
	assert.Nil(t, w,
		"unify-aware self-embedding guard must refuse the set_comprehension identity-def shape")
}

// TestUnifyEqRewrite_AcceptsAssociativity is the behavior-preservation
// regression: the unify-aware self-embedding guard must NOT refuse a
// legitimate (size-stable but non-self-embedding) equational rule like
// ring associativity, which is widely used in the rewrite paths.
//
// Rule:
//
//	λx. λy. λz. plus(x, plus(y, z))  =  λx. λy. λz. plus(plus(x, y), z)
//
// The rule is NOT self-embedding: unifying l's body `plus(x, plus(y,z))`
// against r's body `plus(plus(x,y), z)` fails — the pattern's second arg
// `plus(y,z)` (a function application) cannot unify with the target's
// second arg `z` (an abstraction-bound variable, structurally rigid).
// So the guard must admit it.
func TestUnifyEqRewrite_AcceptsAssociativity(t *testing.T) {
	defer goleak.VerifyNone(t)

	plus := ext.TestConst("+", MakeFun(TypeA, TypeA, TypeA))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	l := x.To(y.To(z.To(plus.Apply(x, plus.Apply(y, z)))))
	r := x.To(y.To(z.To(plus.Apply(plus.Apply(x, y), z))))
	rule := testProp(l.Eq(r))

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	target := plus.Apply(a, plus.Apply(b, c))

	w := unifyEqRewrite(rule)(target)
	assert.NotNil(t, w,
		"associativity is not self-embedding under unification; the guard must admit it")
}

// TestUnifyEqRewrite_AcceptsCommutativity is the involutive-rule
// regression for the self-embedding guard. A commutativity rule can
// rewrite its own RHS back toward the LHS, but that is not the
// expanding set_comprehension shape the guard is meant to reject. The plain
// (one-shot channel) constructor keeps the rule's written orientation —
// ordered rewriting is the simp-set channels' discipline only (see
// TestUnifyEqRewriteOrdered_CommDirectional).
func TestUnifyEqRewrite_AcceptsCommutativity(t *testing.T) {
	defer goleak.VerifyNone(t)

	plus := ext.TestConst("+", MakeFun(TypeA, TypeA, TypeA))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	l := x.To(y.To(plus.Apply(x, y)))
	r := x.To(y.To(plus.Apply(y, x)))
	rule := testProp(l.Eq(r))

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	target := plus.Apply(a, b)

	w := unifyEqRewrite(rule)(target)
	assert.NotNil(t, w,
		"commutativity is involutive, not self-embedding; the guard must admit it")
}

// TestUnifyEqRewriteOrdered_CommDirectional pins the simp-set channel's
// ordered-rewriting contract (unifyEqRewriteImpl with orderPermutative):
// a permutative rule fires only in the strictly Compare-decreasing
// direction — an unsorted target flips to the sorted form, and the
// sorted form is an ordered normal form on which the rule declines.
func TestUnifyEqRewriteOrdered_CommDirectional(t *testing.T) {
	defer goleak.VerifyNone(t)

	plus := ext.TestConst("+", MakeFun(TypeA, TypeA, TypeA))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	l := x.To(y.To(plus.Apply(x, y)))
	r := x.To(y.To(plus.Apply(y, x)))
	rule := testProp(l.Eq(r))

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	ordered := unifyEqRewriteImpl(context.Background(), rule, "", orderedVariants, false)

	// Unsorted target: the decreasing flip fires and sorts. The raw RHS
	// is the un-β-reduced instance `(λx.λy.y+x)(b,a)` (unifyEq leaves the
	// redex; DeepBeta cleans it in tactic compositions), so compare
	// modulo β.
	w := ordered(plus.Apply(b, a).Core())
	assert.NotNil(t, w, "the decreasing COMM flip must fire on an unsorted target")
	if w != nil {
		got := Rhs(w)
		if u := BasicRewrite(got); u != nil {
			got = Rhs(u)
		}
		assert.True(t, got.AlphaEquals(plus.Apply(a, b).Core()),
			"the ordered COMM fire must produce the sorted form (mod β)")
	}

	// Sorted target: the increasing flip is declined — ordered normal form.
	assert.Nil(t, ordered(plus.Apply(a, b).Core()),
		"ordered rewriting declines the Compare-increasing flip on a sorted target")
}

// TestUnifyEqRewriteOrdered_NoPartialApplicationFire pins the
// applied-site-only contract of ordered rewriting: a permutative rule
// must NOT fire at a partial-application (function-typed) site. At that
// level the only order verdict available is on η-long forms, where a
// bound λ-var is Compare-minimal, so the "λ-var first" flip is
// unconditionally judged decreasing — contradicting the applied-level
// verdict on the concrete arguments and 2-cycling with it (the
// int_add_th SimpWith storm). The sorted sum a+b (a < b) contains the
// partial application (+)(a) as its Fun subterm; the old gate flipped
// it to the βη-form of b+a even though the applied-level flip is
// declined as increasing.
func TestUnifyEqRewriteOrdered_NoPartialApplicationFire(t *testing.T) {
	defer goleak.VerifyNone(t)

	plus := ext.TestConst("+", MakeFun(TypeA, TypeA, TypeA))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	l := x.To(y.To(plus.Apply(x, y)))
	r := x.To(y.To(plus.Apply(y, x)))
	rule := testProp(l.Eq(r))

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	ordered := unifyEqRewriteImpl(context.Background(), rule, "", orderedVariants, false)

	// Sorted target: no fire anywhere — neither the (declined) applied-
	// level flip nor the (banned) partial-application flip at (+)(a).
	assert.Nil(t, ordered(plus.Apply(a, b).Core()),
		"ordered COMM must not fire at the partial-application site of a sorted sum")
	// Bare partial application: no fire either.
	assert.Nil(t, ordered(plus.Apply(a).Core()),
		"ordered COMM must not fire on a bare partial application")
}

// TestUnifyEqRewriteOrdered_ACGroupGatesRotation pins the AC-group
// discipline: under orderedACGroup a same-material rotation (ASSOC)
// fires only Compare-decreasing, while under orderedVariants (a lone
// directional ASSOC in a simp set without a same-operator variants
// clause) it keeps its written orientation.
func TestUnifyEqRewriteOrdered_ACGroupGatesRotation(t *testing.T) {
	defer goleak.VerifyNone(t)

	plus := ext.TestConst("+", MakeFun(TypeA, TypeA, TypeA))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	// ASSOC toward left nesting (the normal form's smaller-side-first
	// orientation): x+(y+z) = (x+y)+z — Compare-INCREASING.
	l := x.To(y.To(z.To(plus.Apply(x, plus.Apply(y, z)))))
	r := x.To(y.To(z.To(plus.Apply(plus.Apply(x, y), z))))
	rule := testProp(l.Eq(r))

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	target := plus.Apply(a, plus.Apply(b, c)).Core()

	// Lone directional ASSOC (variants-only mode): written direction fires.
	assert.NotNil(t, unifyEqRewriteImpl(context.Background(), rule, "", orderedVariants, false)(target),
		"a lone ASSOC keeps its written (left-nesting) orientation")
	// AC-group mode: the increasing rotation is declined.
	assert.Nil(t, unifyEqRewriteImpl(context.Background(), rule, "", orderedACGroup, false)(target),
		"AC-group mode declines the Compare-increasing rotation")
}

// TestSimpSetACGates pins the group detection: the rotation's gate
// flips on exactly when a variants clause over the same operator is in
// the set.
func TestSimpSetACGates(t *testing.T) {
	defer goleak.VerifyNone(t)

	plus := ext.TestConst("+", MakeFun(TypeA, TypeA, TypeA))
	times := ext.TestConst("*", MakeFun(TypeA, TypeA, TypeA))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	forAll := func(body *ext.TermWrapper, vars ...*ext.TermWrapper) Term {
		w := body
		for i := len(vars) - 1; i >= 0; i-- {
			w = ForAll(vars[i])(w)
		}
		return w.Core()
	}
	comm := forAll(plus.Apply(x, y).Eq(plus.Apply(y, x)), x, y)
	assocPlus := forAll(plus.Apply(x, plus.Apply(y, z)).Eq(plus.Apply(plus.Apply(x, y), z)), x, y, z)
	assocTimes := forAll(times.Apply(x, times.Apply(y, z)).Eq(times.Apply(times.Apply(x, y), z)), x, y, z)

	// COMM(+) + ASSOC(+): the rotation is gated, the variants clause is not.
	assert.Equal(t, []bool{false, true}, SimpSetACGates([]Term{comm, assocPlus}))
	// ASSOC(+) alone: no gate.
	assert.Equal(t, []bool{false}, SimpSetACGates([]Term{assocPlus}))
	// COMM(+) + ASSOC(*): different operators — no gate.
	assert.Equal(t, []bool{false, false}, SimpSetACGates([]Term{comm, assocTimes}))
}

// TestUnifyEqRewrite_RefusesBareIdentity asserts the syntactic guard at
// the top of unifyEqRewrite still catches bare `⊢ l = l` rules. The
// guard exists at eq_rewrite.go:329 and is unaffected by the unify-aware
// addition below it; this test pins that contract.
func TestUnifyEqRewrite_RefusesBareIdentity(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	body := x.To(P.Apply(x))
	rule := testProp(body.Eq(body))

	q := Var("q", TypeA)
	w := unifyEqRewrite(rule)(P.Apply(q))
	assert.Nil(t, w,
		"unifyEqRewrite must refuse a bare identity equation `⊢ l = l`")
}

// TestUnifyEqRewrite_RefusesVariableLHSRule pins the variable-LHS
// rewrite-rule ban in unifyEq: without it def_expand(set_comprehension)
// on nested prod-type binders wedges the session.
//
// set_comprehension's definition is the identity `⊢ set_comprehension = (λp.p)`. LeanRwTactic's
// bidirectional retry flips it to `⊢ (λp.p) = set_comprehension`. After unifyEq
// peels the λp, the pattern body is the bare flexible var p — it
// matches ANY (A→bool)-typed subterm by absorbing it whole, rewriting
// t → set_comprehension(λx.t̃(x)) where t̃ is the unifier's βη-VARIANT of t (binder
// names drift), so the per-instance syntactic `!IsSub(t, Rhs)` check
// misses the self-embedding and the eqLemmaTacticExpand mergeTactics
// fixpoint re-fires on its own output without bound (+3 nodes per
// firing — verified live on the BASE leaf of an iterated-product proof).
//
// The ban: a peeled pattern body that IS one of the peeled vars is a
// vacuous match-anything rule (classical term rewriting
// rejects variable-LHS rules for the same reason) — unifyEq
// yields no instances. The α-match fast path is unaffected: a literal
// occurrence of the identity lambda still folds to set_comprehension (second
// assertion).
func TestUnifyEqRewrite_RefusesVariableLHSRule(t *testing.T) {
	defer goleak.VerifyNone(t)

	setComprehension := Var("set_comprehension", MakeFun(MakeFun(TypeA, TypeBool), MakeFun(TypeA, TypeBool)))
	p := Var("p", MakeFun(TypeA, TypeBool))
	rule := testProp(p.To(p).Eq(setComprehension)) // ⊢ (λp.p) = set_comprehension — flipped identity def

	// A ∀-guarded composite target: the walk descends under the binder,
	// wraps body subterms with their env vars, and (pre-ban) the bare
	// flexible pattern var absorbed the wrapped body → ∀i.R(i) grew to
	// ∀i.set_comprehension(λx.R(x), i), forever.
	R := Var("R", MakeFun(TypeA, TypeBool))
	i := Var("i", TypeA)
	target := ForAll(i)(R.Apply(i))
	assert.Nil(t, unifyEqRewrite(rule)(target),
		"variable-LHS rule (flipped identity def) must yield no rewrite")

	// Definition FOLDING via a literal α-match must keep working: an
	// exact occurrence of the identity lambda still rewrites to set_comprehension.
	q := Var("q", MakeFun(TypeA, TypeBool))
	lit := q.To(q)
	w := unifyEqRewrite(rule)(lit)
	if assert.NotNil(t, w,
		"literal identity-lambda occurrence must still fold to set_comprehension (α-match fast path)") {
		assert.True(t, Rhs(w).AlphaEquals(setComprehension),
			"folded RHS must be set_comprehension, got %v", Rhs(w))
	}
}

// TestUnifyEqRewrite_RefusesProjectionRuleAtFullType pins the
// projection-pattern ban in unifyEq — the level-0 sibling of the
// variable-LHS ban above: without it def_expand(set_comprehension)
// succeeds without net change, a treadmill (see
// engine.TestDefExpandSetComprehension_NoTreadmill).
//
// Same flipped identity def `⊢ (λp.p) = set_comprehension`, but the absorbable
// application site's HEAD var is itself ∀-bound: at the site s(x')
// inside `∀s.∀x'. s(x')`, the walk wraps BOTH env vars, offering
// tAbs = λs.λx'.s(x') — the same type as the un-peeled pattern. So the
// peel level is 0, no vars are peeled, and the pattern body is the
// identity ABSTRACTION λp.p (not a bare var): the variable-LHS ban
// never fires, λp.p unifies with tAbs modulo η on an EMPTY
// substitution, and (pre-ban) the rule folded s(x') → set_comprehension(s)(x') —
// an α-key 2-cycle with the forward unfold direction. The projection
// ban refuses any pattern that is a projection combinator of its own
// binders (λp.p, λx.λy.x, …).
func TestUnifyEqRewrite_RefusesProjectionRuleAtFullType(t *testing.T) {
	defer goleak.VerifyNone(t)

	setComprehension := Var("set_comprehension", MakeFun(MakeFun(TypeA, TypeBool), MakeFun(TypeA, TypeBool)))
	p := Var("p", MakeFun(TypeA, TypeBool))
	rule := testProp(p.To(p).Eq(setComprehension)) // ⊢ (λp.p) = set_comprehension — flipped identity def

	s := Var("s", MakeFun(TypeA, TypeBool))
	x := Var("x'", TypeA)
	target := ForAll(s)(ForAll(x)(s.Apply(x))) // ∀s.∀x'. s(x')
	assert.Nil(t, unifyEqRewrite(rule)(target),
		"projection pattern (λp.p at the site-abstraction's full type) must yield no rewrite")

	// Definition FOLDING via a literal α-match must keep working.
	q := Var("q", MakeFun(TypeA, TypeBool))
	lit := q.To(q)
	w := unifyEqRewrite(rule)(lit)
	if assert.NotNil(t, w,
		"literal identity-lambda occurrence must still fold to set_comprehension (α-match fast path)") {
		assert.True(t, Rhs(w).AlphaEquals(setComprehension),
			"folded RHS must be set_comprehension, got %v", Rhs(w))
	}
}

// An η-redex pattern λx.h(x) stands for h: EqRewrite reaches an
// occurrence of h itself — a clause's absEq (λw.α(w) = λw.⊥, from
// ∀w.¬α(w)) rewrites the bare symbol α in argument position, which the
// normalizer's η leaves there, as well as the η-long occurrence.
func TestEqRewriteMatchesEtaContractedPattern(t *testing.T) {
	w := Var("w", TypeInd)
	alpha := Var("α", MakeFun(TypeInd, TypeBool))
	G := Var("G", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd))
	absEq := ContextAbsEq(ForAll(w)(Not(alpha.Apply(w))).Core())
	rewrite := EqRewrite(absEq)

	bare := rewrite(G.Apply(alpha))
	if assert.NotNil(t, bare, "the bare symbol is an instance of the pattern") {
		assertTermEqual(t, Rhs(bare), G.Apply(w.To(F)))
		assert.Equal(t, 1, bare.NumHyps())
	}
	long := rewrite(G.Apply(w.To(alpha.Apply(w))))
	if assert.NotNil(t, long) {
		assertTermEqual(t, Rhs(long), G.Apply(w.To(F)))
	}
	// A rule whose right side carries the contracted pattern itself
	// (∀ẋ. E(x, ẋ) ⇔ D(M(E(x)), ẋ), the lifted-class shape) still
	// rewrites applications of E(x), but never the bare E(x) inside its
	// own right side — that fold would embed forever.
	x := Var("x", TypeInd)
	E := Var("E", MakeFun(TypeInd, TypeInd, TypeBool))
	M := Var("M", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd))
	D := Var("D", MakeFun(TypeInd, TypeInd, TypeBool))
	// (contextAbsEqOpt with noSwap keeps the E → D orientation; ContextAbsEq
	// would put the bigger side on the left.)
	lifted := contextAbsEqOpt(ForAll(w)(E.Apply(x, w).Eq(D.Apply(M.Apply(E.Apply(x)), w))).Core(), true)
	assert.Nil(t, EqRewrite(lifted)(M.Apply(E.Apply(x))), "the bare E(x) is not folded")
	y := Var("y", TypeInd)
	applied := EqRewrite(lifted)(ForAll(y)(E.Apply(x, y)))
	if assert.NotNil(t, applied) {
		assert.True(t, Rhs(applied).AlphaEquals(ForAll(y)(D.Apply(M.Apply(E.Apply(x)), y))))
	}
	// A pattern that is not an η-redex gains nothing: λw.α(w, w) is
	// not α.
	beta := Var("β", MakeFun(TypeInd, TypeInd, TypeBool))
	square := ContextAbsEq(ForAll(w)(Not(beta.Apply(w, w))).Core())
	assert.Nil(t, EqRewrite(square)(G.Apply(w.To(beta.Apply(w, w)).Core().(AbsTerm).Body().(AppliedTerm).Fun())))
}

// TestUnifyEqRewrite_FirstOrderRuleFiresOnLargeTarget — a first-order
// rule whose left side NESTS its variables (`p(k(a, b)) = a`, the shape
// of a record's projection law `re(complex(a, b)) = a`) fires on a
// target whose matched subterm is large. Such a rule cannot fire on its
// head by η (its left side is no bare head applied to its binders), so
// its variables reach the unifier as bare meta-variables against ground
// subterms — the n = 0 Miller pattern. Left to Huet's imitation that
// match cost quadratically in the subterm and, beyond a few hundred
// nodes, exhausted the deterministic work budget, so the rewrite
// silently did not fire. The contract at this surface: the size of the
// target does not decide whether a first-order rule fires.
func TestUnifyEqRewrite_FirstOrderRuleFiresOnLargeTarget(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := Var("c", TypeInd)
	f := Var("f", MakeFun(TypeInd, TypeInd, TypeInd))
	k := Var("k", MakeFun(TypeInd, TypeInd, TypeInd))
	p := Var("p", MakeFun(TypeInd, TypeInd))
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)

	// ⊢ λa.λb. p(k(a, b)) = λa.λb. a — the projection law's shape.
	rule := testProp(a.To(b.To(p.Apply(k.Apply(a, b)))).Eq(a.To(b.To(a))))

	// A ground subterm of ~1000 nodes for a to absorb.
	big := c
	for range 500 {
		big = f.Apply(big, c)
	}
	s := p.Apply(k.Apply(big, c))

	fired := unifyEqRewrite(rule)(s)
	assert.NotNil(t, fired, "a first-order rule must fire regardless of the target's size")
	if fired != nil {
		assertTermAlphaEqual(t, Lhs(fired), s)
		// The instance is left as the rule's abstraction applied to the
		// arguments; compare up to βη.
		assert.True(t, ext.BetaEtaEquals(context.Background(), Rhs(fired), big))
	}
}

// TestPreCNFFallbackServesEveryPatternButAnImplication pins the
// fallback's contract: a rule that fails as written on a Bool target is
// retried on the target's pre-CNF normal form — a propositional pattern
// meeting the normal form's skeleton, a term pattern meeting, through
// the normalizer's β, an instance a redex hid — unless its pattern is
// an implication, which no normal form contains: that rule is never
// retried and normalizes nothing.
func TestPreCNFFallbackServesEveryPatternButAnImplication(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	u := Var("u", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	S := Var("S", MakeFun(TypeA, TypeBool))

	// Term rule ∀a b. f(g(a, b)) = a against (λu. Q(f(u)))(g(x, y)): the
	// pattern's instance f(g(x, y)) exists only after β, at a node the
	// unreduced target does not have (f(u) with u bound; g(x, y) alone)
	// — the normal form has it, and the retry fires on it.
	termRule := ForAll(a, b)(f.Apply(g.Apply(a, b)).Eq(a))
	redex := u.To(Q.Apply(f.Apply(u))).Apply(g.Apply(x, y)).Core()
	cache := new(PreCNFCache)
	w := ContextEqRewriteOrdered(cache, termRule, true, true)(redex)
	if assert.NotNil(t, w, "a term rule is retried on the normal form") {
		// The unifier's instance is Q((λa.λb.a)(x, y)); the driver's β
		// rule reduces it inline.
		assert.True(t, ext.BetaEtaEquals(context.Background(), Rhs(w), Q.Apply(x).Core()), "got %s", ext.PrintTerm(Rhs(w)))
		assert.True(t, Lhs(w).AlphaEquals(redex))
	}
	assert.Equal(t, 1, cache.TermCacheSize())

	// Propositional rule ∀a. nf(P(a) ⇒ R(a)) ⇔ S(a) — its pattern the
	// implication's pre-CNF normal form (¬P ∨ R, in the normalizer's
	// disjunct order) — against P(x) ⇒ R(x): written as an implication
	// the target matches nothing; its normal form is the pattern's
	// instance.
	propRule := ForAll(a)(WrapTerm(Rhs(PreCNFNormalizeTerm(P.Apply(a).Imply(R.Apply(a))))).Eq(S.Apply(a)))
	target := P.Apply(x).Imply(R.Apply(x)).Core()
	cache = new(PreCNFCache)
	w = ContextEqRewriteOrdered(cache, propRule, true, true)(target)
	if assert.NotNil(t, w, "a propositional rule is retried on the normal form") {
		// The unifier's instance is (λa.S(a))(x); the driver's β rule
		// reduces it inline.
		assert.True(t, ext.BetaEtaEquals(context.Background(), Rhs(w), S.Apply(x).Core()), "got %s", ext.PrintTerm(Rhs(w)))
		assert.True(t, Lhs(w).AlphaEquals(target))
	}
	assert.Equal(t, 1, cache.TermCacheSize())

	// Implication rule ∀a. (P(a) ⇒ R(a)) ⇔ S(a) against the same target
	// spelled as its normal form ¬P(x) ∨ R(x): no normal form holds an
	// implication, so the rule is never retried and normalizes nothing.
	implyRule := ForAll(a)(P.Apply(a).Imply(R.Apply(a)).Eq(S.Apply(a)))
	normalTarget := Rhs(PreCNFNormalizeTerm(target))
	cache = new(PreCNFCache)
	assert.Nil(t, ContextEqRewriteOrdered(cache, implyRule, true, true)(normalTarget))
	assert.Equal(t, 0, cache.TermCacheSize(), "an implication pattern normalizes nothing")
	// The same hypothesis read by the structural channel (eqSimplify's:
	// no unification, the larger side on the left) — the fact P(x) ⇒ R(x)
	// stands for (P(x) ⇒ R(x)) ⇔ ⊤ and is an implication pattern too.
	cache = new(PreCNFCache)
	assert.Nil(t, ContextEqRewriteOpt(cache, target, false, false)(ext.Not(normalTarget).Core()))
	assert.Equal(t, 0, cache.TermCacheSize())
}

// TestPreCNFFallbackSharesOneCacheAcrossARuleSet pins that the rule
// rewrites built over one PreCNFCache normalize a node once for the
// set: the second propositional rule's fallback on the same target
// reads the first's normal form.
func TestPreCNFFallbackSharesOneCacheAcrossARuleSet(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	a := Var("a", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))
	S := Var("S", MakeFun(TypeA, TypeBool))
	T2 := Var("T2", MakeFun(TypeA, TypeBool))

	target := P.Apply(x).Imply(R.Apply(x)).Core()
	// Neither rule's pattern is in the target as written or in its
	// normal form, so both fallbacks run and neither fires.
	rule1 := ForAll(a)(WrapTerm(Rhs(PreCNFNormalizeTerm(P.Apply(a).Imply(T2.Apply(a))))).Eq(S.Apply(a)))
	rule2 := ForAll(a)(WrapTerm(Rhs(PreCNFNormalizeTerm(T2.Apply(a).Imply(R.Apply(a))))).Eq(S.Apply(a)))
	cache := new(PreCNFCache)
	rw1 := ContextEqRewriteOrdered(cache, rule1, true, true)
	rw2 := ContextEqRewriteOrderedAC(cache, rule2, true, true)
	assert.Nil(t, rw1(target))
	assert.Equal(t, 1, cache.TermCacheSize())
	assert.Nil(t, rw2(target))
	assert.Equal(t, 1, cache.TermCacheSize(), "the second rule reads the first's normal form")
}

// TestPreCNFFallbackLeavesATargetWithoutThePatternsHead pins the
// fallback's test of a target: a rule whose pattern is headed by a
// constant is not retried on a Bool target that lacks the constant —
// the normal form lacks it too — and normalizes nothing there. A target
// that holds the constant is retried, the instance a redex hides
// included.
func TestPreCNFFallbackLeavesATargetWithoutThePatternsHead(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	u := Var("u", TypeA)
	f := ext.TestConst("retryHeadLeft", MakeFun(TypeA, TypeA))
	g := Var("g", MakeFun(TypeA, TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))

	rule := ForAll(a, b)(f.Apply(g.Apply(a, b)).Eq(a))

	// P(x) ⇒ R(x) is not its own normal form, and holds no f: the rule
	// fails as written and the target is left as it is.
	absent := P.Apply(x).Imply(R.Apply(x)).Core()
	assert.False(t, Rhs(PreCNFNormalizeTerm(absent)).AlphaEquals(absent))
	cache := new(PreCNFCache)
	assert.Nil(t, ContextEqRewriteOrdered(cache, rule, true, true)(absent))
	assert.Equal(t, 0, cache.TermCacheSize(), "a target without the pattern's head is not normalized")

	// (λu. Q(f(u)))(g(x, y)) holds f, and f(g(x, y)) only after β.
	redex := u.To(Q.Apply(f.Apply(u))).Apply(g.Apply(x, y)).Core()
	cache = new(PreCNFCache)
	w := ContextEqRewriteOrdered(cache, rule, true, true)(redex)
	if assert.NotNil(t, w, "a target that holds the pattern's head is retried on its normal form") {
		assert.True(t, ext.BetaEtaEquals(context.Background(), Rhs(w), Q.Apply(x).Core()), "got %s", ext.PrintTerm(Rhs(w)))
		assert.True(t, Lhs(w).AlphaEquals(redex))
	}
	assert.Equal(t, 1, cache.TermCacheSize())
}

// TestPreCNFRetryOf_ReadsThePatternsHead pins what the fallback reads
// off a rule: the head of the side the primary matches, when it is a
// constant the normalizer never introduces.
func TestPreCNFRetryOf_ReadsThePatternsHead(t *testing.T) {
	x := Var("x", TypeA)
	a := Var("a", TypeA)
	f := ext.TestConst("retryOfFunction", MakeFun(TypeA, TypeA))
	holds := ext.TestConst("retryOfPredicate", MakeFun(TypeA, TypeBool))
	h := Var("h", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeBool))

	cases := []struct {
		name   string
		rule   Term
		noSwap bool
		want   preCNFRetry
	}{
		{"an equation's left side", ForAll(a)(f.Apply(a).Eq(a)), true, preCNFRetry{serves: true, head: "retryOfFunction"}},
		{"the larger side, where the primary swaps", x.Eq(f.Apply(f.Apply(a))), false, preCNFRetry{serves: true, head: "retryOfFunction"}},
		{"the left side as written, where it does not", x.Eq(f.Apply(f.Apply(a))), true, preCNFRetry{serves: true}},
		{"a fact", ForAll(a)(holds.Apply(a)), true, preCNFRetry{serves: true, head: "retryOfPredicate"}},
		{"a negated fact", ForAll(a)(ext.Not(holds.Apply(a))), true, preCNFRetry{serves: true, head: "retryOfPredicate"}},
		{"a pattern headed by a binder", ForAll(h, a)(h.Apply(f.Apply(a)).Eq(a)), true, preCNFRetry{serves: true}},
		{"a pattern headed by a free variable", ForAll(a)(P.Apply(f.Apply(a))), true, preCNFRetry{serves: true}},
		{"a pattern headed by a connective", ForAll(a)(holds.Apply(a).Or(R.Apply(a)).Eq(P.Apply(a))), true, preCNFRetry{serves: true}},
		{"a pattern headed by a quantifier", ForAll(a)(holds.Apply(a)).Eq(P.Apply(x)), true, preCNFRetry{serves: true}},
		{"a pattern headed by equality", ForAll(a)(f.Apply(a).Eq(a).Eq(P.Apply(a))), true, preCNFRetry{serves: true}},
		{"an implication", ForAll(a)(holds.Apply(a).Imply(R.Apply(a)).Eq(P.Apply(a))), true, preCNFRetry{}},
	}
	for _, c := range cases {
		assert.Equal(t, c.want, preCNFRetryOf(c.rule, c.noSwap), c.name)
	}
}

// A rule can expose its own left pattern below a binder whose type is
// different from the pattern's parameters. The fixpoint walk presents
// that binder's body separately, so the self-embedding check must too.
func TestUnifyEqRewrite_RefusesSelfEmbedUnderDifferentBinder(t *testing.T) {
	rel := ext.TestConst("nestedRelation", MakeFun(TypeA, TypeA, TypeBool))
	first := ext.TestConst("nestedFirst", MakeFun(TypeBool, TypeA))
	second := ext.TestConst("nestedSecond", MakeFun(TypeBool, TypeA))
	wrap := ext.TestConst("nestedWrap", MakeFun(MakeFun(TypeBool, TypeBool), TypeA, TypeA, TypeBool))
	x, y := Var("x", TypeA), Var("y", TypeA)
	p := Var("p", TypeBool)
	left := x.To(y.To(rel.Apply(x, y)))
	right := x.To(y.To(wrap.Apply(p.To(rel.Apply(first.Apply(p), second.Apply(p))), x, y)))
	rule := testProp(left.Eq(right))
	assert.False(t, ext.IsSub(left, right))
	a, b := Var("a", TypeA), Var("b", TypeA)
	assert.Nil(t, unifyEqRewrite(rule)(rel.Apply(a, b)),
		"a fixpoint rule cannot re-create its pattern under a differently typed binder")
}

// A nonrecursive definition with the same binder profile is still a
// valid expanding rewrite.
func TestUnifyEqRewrite_AllowsDifferentBinderWithoutSelfEmbed(t *testing.T) {
	rel := ext.TestConst("sourceRelation", MakeFun(TypeA, TypeA, TypeBool))
	other := ext.TestConst("targetRelation", MakeFun(TypeA, TypeA, TypeBool))
	first := ext.TestConst("targetFirst", MakeFun(TypeBool, TypeA))
	second := ext.TestConst("targetSecond", MakeFun(TypeBool, TypeA))
	wrap := ext.TestConst("targetWrap", MakeFun(MakeFun(TypeBool, TypeBool), TypeA, TypeA, TypeBool))
	x, y := Var("x", TypeA), Var("y", TypeA)
	p := Var("p", TypeBool)
	left := x.To(y.To(rel.Apply(x, y)))
	payload := p.To(other.Apply(first.Apply(p), second.Apply(p)))
	right := x.To(y.To(wrap.Apply(payload, x, y)))
	a, b := Var("a", TypeA), Var("b", TypeA)
	got := unifyEqRewrite(testProp(left.Eq(right)))(rel.Apply(a, b))
	if assert.NotNil(t, got) {
		assert.True(t, ext.BetaEtaNormalize(context.Background(), Rhs(got)).AlphaEquals(wrap.Apply(payload, a, b)))
	}
}

// A rule's rewrite ends with its caller's context: under a context that
// is never done it is ContextEqRewriteOpt, and under one that is done it
// answers nil on a target the rule rewrites — an answer its caller reads
// its context before, not a report that the rule does not fire.
func TestContextEqRewriteOptUnder_EndsWithItsContext(t *testing.T) {
	f := ext.TestConst("ruleLeft", MakeFun(TypeA, TypeA))
	g := ext.TestConst("ruleRight", MakeFun(TypeA, TypeA))
	holds := ext.TestConst("ruleHolds", MakeFun(TypeA, TypeBool))
	x, a := Var("x", TypeA), Var("a", TypeA)
	rule := ForAll(x)(f.Apply(f.Apply(x)).Eq(g.Apply(x)))
	target := holds.Apply(f.Apply(f.Apply(a)))

	unbounded := ContextEqRewriteOpt(new(PreCNFCache), rule, true, false)(target)
	if !assert.NotNil(t, unbounded) {
		return
	}
	assert.True(t, ext.BetaEtaNormalize(context.Background(), Rhs(unbounded)).AlphaEquals(holds.Apply(g.Apply(a))))

	live := ContextEqRewriteOptUnder(context.Background(), new(PreCNFCache), rule, true, false)(target)
	if assert.NotNil(t, live) {
		assertTermAlphaEqual(t, Rhs(live), Rhs(unbounded))
	}

	done, cancel := context.WithCancel(context.Background())
	cancel()
	assert.Nil(t, ContextEqRewriteOptUnder(done, new(PreCNFCache), rule, true, false)(target))
}
