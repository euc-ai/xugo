package clause

import (
	"fmt"
	"slices"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

var (
	testProp = MakeProp
	testThm  = core.TestThm
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

func TestMakeClause(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	d := Var("d", TypeA)
	q := Var("q", TypeBool)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeBool, TypeBool))
	R := Var("R", MakeFun(TypeInd, TypeBool))

	assert.Panics(t, func() {
		MakeClause(
			ForAll(R, a, b, d)(Not(R.Apply(a)).Or(P.Apply(b))))
	})
	verifyClause := func(s Term,
		equivalentTerm Term,
		components ...Term) {
		c := MakeClause(s)
		assertTermAlphaEqual(t, c.originalTerm, s)
		assert.Equal(t,
			equivalentTerm == nil,
			c.equivalentClause == nil)

		if !c.EquatesT() && !c.EffectiveBody().Equals(F) {
			assert.Equal(t,
				len(DecomposesOR(c.EffectiveBody())) == 1,
				c.absEq != nil)
		}

		if equivalentTerm != nil {
			assert.Equal(t, equivalentTerm.Equals(T), c.EquatesT())
			assertTermEqual(t, c.equivalentClause.Term(), equivalentTerm)
			assertTermEqual(t, Lhs(c.simplificationThm), c.leftAssocWithUniv)
			assertTermEqual(t, Rhs(c.simplificationThm), equivalentTerm)
		}
		assert.Equal(t, len(components), len(c.components))
		for i, ci := range components {
			assertTermAlphaEqual(t, c.components[i], ci)
		}
	}

	term := ForAll(b)(P.Apply(b).Or(P.Apply(c)))
	verifyClause(
		term,
		nil,
		P.Apply(c),
		ForAll(b)(P.Apply(b)))

	term = ForAll(b)(P.Apply(b).Or(F))
	verifyClause(term,
		ForAll(b)(P.Apply(b)),
		ForAll(b)(P.Apply(b)))

	term = ForAll(P, b)(P.Apply(b).Or(Not(P.Apply(b))))
	verifyClause(term, T, T)

	term = ForAll(a, b)(P.Apply(b).Or(Not(R.Apply(a))))
	verifyClause(term,
		nil,
		ForAll(b)(P.Apply(b)),
		ForAll(a)(Not(R.Apply(a))))

	term = P.Apply(b).Or(Not(R.Apply(a)))
	verifyClause(term,
		nil,
		P.Apply(b),
		Not(R.Apply(a)))

	term = ForAll(a, b)(P.Apply(b).Or(Not(R.Apply(a))).Or(d.Eq(b)))
	verifyClause(term,
		nil,
		ForAll(b)(P.Apply(b).Or(d.Eq(b))),
		ForAll(a)(Not(R.Apply(a))))

	term = ForAll(a, b)(P.Apply(b).Or(Not(R.Apply(a)).Or(d.Eq(b))))
	verifyClause(term,
		nil,
		ForAll(b)(P.Apply(b).Or(d.Eq(b))),
		ForAll(a)(Not(R.Apply(a))))

	term = ForAll(b)(P.Apply(b).Or(P.Apply(d)).Or(d.Eq(c)).Or(c.Eq(d)))
	verifyClause(term,
		ForAll(b)(P.Apply(d).Or(P.Apply(b)).Or(c.Eq(d))),
		P.Apply(d),
		ForAll(b)(P.Apply(b)),
		c.Eq(d))

	term = Q.Apply(b.To(b).Eq(c.To(d)))
	verifyClause(term,
		nil,
		Q.Apply(c.To(d).Eq(b.To(b))))

	// A λ-equality nested under a bool head stays as it stands, sides
	// sorted: clause normalization does not extensionalize (the pre-CNF
	// pipeline's FunEqRewrite reads `(λb.c) = (λc.d)` as `c = d` before
	// any clause is made).
	term = Q.Apply(b.To(c).Eq(c.To(d)))
	verifyClause(term,
		nil,
		Q.Apply(b.To(c).Eq(c.To(d))))

	term = ForAll(b)(Not(b.Eq(c)))
	verifyClause(term, F, F)

	term = ForAll(c, b)(Not(b.Eq(c)).Or(P.Apply(b)))
	verifyClause(term,
		ForAll(c)(P.Apply(c)),
		ForAll(c)(P.Apply(c)))

	term = ForAll(q)(q)
	verifyClause(term, F, F)

	// Prenex changes disjunctive structure: P(b) ∨ P(b) ∨ ∀c.P(c) normalizes
	// to P(b) ∨ ∀c.P(c) (dedup, size 2 < 3), then prenex pulls ∀c out to get
	// ∀c.(P(b) ∨ P(c)). The equivalentClause's components must match the
	// prenexed form, not the pre-prenex components.
	// Prenex changes disjunctive structure: P(b) ∨ P(b) ∨ ∀c.Q(c) normalizes
	// to P(b) ∨ ∀c.Q(c) (dedup, size 2 < 3), then prenex pulls ∀c out to get
	// ∀c.(P(b) ∨ Q(c)). The equivalentClause must have its own components
	// matching the prenexed form, not the pre-prenex components.
	// Prenex changes disjunctive structure: P(b) ∨ P(b) ∨ ∀c.Q(c) normalizes
	// to P(b) ∨ ∀c.Q(c) (dedup, size 2 < 3), then prenex pulls ∀c out to get
	// ∀c.(P(b) ∨ Q(c)). Without the fix, equivalentClause.Division() panics
	// because components [P(b), ∀c.Q(c)] don't match term ∀c.(P(b) ∨ Q(c)).
	{
		Q := Var("Q", MakeFun(TypeA, TypeBool))
		term = P.Apply(b).Or(P.Apply(b)).Or(ForAll(c)(Q.Apply(c)))
		cl := MakeClause(term)
		assert.NotNil(t, cl.equivalentClause)
		eq := cl.equivalentClause
		// Division must not panic on the equivalentClause
		assert.NotPanics(t, func() {
			if len(eq.components) > 1 {
				eq.Division()
			}
		})
	}

	// A function-typed equality literal is normalized as the equality it
	// is: clause normalization does not extensionalize (FunEqRewrite is
	// the pre-CNF pipeline's step), so the dedup of `(S = E) ∨ (S = E)` at
	// a set type simplifies to the unit equality S = E — a disjunctive
	// clause, which MakeClause's second prepareClause accepts (the
	// pointwise `∀x. S(x) ⇔ E(x)` is not one, and would panic it).
	{
		S := Var("S", MakeFun(TypeA, TypeBool))
		E := Var("E", MakeFun(TypeA, TypeBool))
		term = S.Eq(E).Or(S.Eq(E))
		cl := MakeClause(term)
		if assert.NotNil(t, cl.equivalentClause) {
			eq := cl.equivalentClause
			assert.True(t, ext.IsDisjunctive(eq.leftAssocWithUniv))
			if assert.Len(t, eq.literals, 1) {
				lit := eq.literals[0]
				assert.True(t, lit.AlphaEquals(Eq(S, E)) || lit.AlphaEquals(Eq(E, S)),
					"the equivalent clause is the equality itself, got %s",
					ext.PrintTerm(lit))
			}
		}
	}
}

func TestNormalizeClause(t *testing.T) {
	defer goleak.VerifyNone(t)

	verify := func(d Term, components ...Term) {
		s := normalizeClause(d)
		if len(components) == 0 {
			assert.Nil(t, s)
		} else {
			assertTermAlphaEqual(t, Lhs(s), d)
			assert.Equal(t, len(components), len(DecomposesOR(Rhs(s))))
			for i, si := range DecomposesOR(Rhs(s)) {
				if !si.AlphaEquals(components[i]) {
					fmt.Println(ext.PrintTerm(si), ext.PrintTerm(components[i]))
				}
				assertTermAlphaEqual(t, si, components[i])
			}
		}
	}

	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool))
	G := Var("G", MakeFun(MakeFun(TypeA, TypeA), TypeBool))
	S := Var("S", MakeFun(TypeA, TypeA, TypeBool))

	d := P.Apply(b)
	verify(d)

	d = P.Apply(b).Or(Not(P.Apply(b)))
	verify(d, T)

	d = ForAll(b)(P.Apply(b).Or(Not(P.Apply(b))))
	verify(d, T)

	d = P.Apply(b).Or(P.Apply(b))
	verify(d, P.Apply(b))

	d = ForAll(b)(P.Apply(b).Or(P.Apply(b)))
	verify(d, ForAll(b)(P.Apply(b)))

	d = ForAll(c)((P.Apply(c)).Or(P.Apply(b.SuchThat(P.Apply(b)))))
	verify(d, P.Apply(b.SuchThat(P.Apply(b))), ForAll(c)(P.Apply(c)))

	d = ForAll(b)((P.Apply(b)).Or(P.Apply(b.SuchThat(P.Apply(b)))))
	verify(d, P.Apply(b.SuchThat(P.Apply(b))), ForAll(b)(P.Apply(b)))

	d = P.Apply(b).Or(P.Apply(c)).Or(Not(P.Apply(b)))
	verify(d, T)

	d = ForAll(b, c)(Q.Apply(c).Or(P.Apply(b)))
	verify(d, ForAll(b)(P.Apply(b)), ForAll(c)(Q.Apply(c)))

	d = ForAll(c, b)(Q.Apply(c).Or(P.Apply(b)))
	verify(d, ForAll(b)(P.Apply(b)), ForAll(c)(Q.Apply(c)))

	d = ForAll(b, c)(P.Apply(b).Or(Q.Apply(c)))
	verify(d, ForAll(b)(P.Apply(b)), ForAll(c)(Q.Apply(c)))

	d = ForAll(c, b)(P.Apply(b).Or(Q.Apply(c)))
	verify(d, ForAll(b)(P.Apply(b)), ForAll(c)(Q.Apply(c)))

	d = ForAll(b, c)(P.Apply(c).Or(P.Apply(b)))
	verify(d, ForAll(b)(P.Apply(b)))

	d = ForAll(c, b)(P.Apply(c).Or(P.Apply(b)))
	verify(d, ForAll(c)(P.Apply(c)))

	d = P.Apply(b.SuchThat(P.Apply(b))).Or(P.Apply(b.SuchThat(F)))
	verify(d, P.Apply(b.SuchThat(F)), P.Apply(b.SuchThat(P.Apply(b))))

	d = ForAll(c, b)(G.Apply(b.To(c)).Or(P.Apply(b)))
	verify(d, ForAll(b)(P.Apply(b)), ForAll(c)(G.Apply(b.To(c))))

	d = ForAll(c, b)(G.Apply(c.To(c)).Or(P.Apply(b).Eq(Q.Apply(c))))
	verify(d, G.Apply(c.To(c)), ForAll(c, b)(P.Apply(c).Eq(Q.Apply(b))))

	d = P.Apply(b.SuchThat(F)).Or(Not(P.Apply(b.SuchThat(P.Apply(b)))))
	verify(d, P.Apply(b.SuchThat(F)), ForAll(b)(Not(P.Apply(b))))

	d = R.Apply(b.To(b).Eq(c.To(a)))
	verify(d, R.Apply(c.To(a).Eq(b.To(b))))

	// A λ-equality under a bool head is sorted, not extensionalized (the
	// pre-CNF pipeline's FunEqRewrite reads it as `a = c` before any
	// clause is made).
	d = R.Apply(b.To(c).Eq(c.To(a)))
	verify(d, R.Apply(c.To(a).Eq(b.To(c))))

	d = ForAll(b)(b.Neq(c))
	verify(d, F)

	d = ForAll(c, b)(b.Neq(c).Or(P.Apply(b)))
	verify(d, ForAll(c)(P.Apply(c)))

	d = c.Eq(b).Or(S.Apply(b, c))
	verify(d, S.Apply(b, c), b.Eq(c))

	d = S.Apply(b, c).Or(c.Eq(b))
	verify(d, S.Apply(b, c), b.Eq(c))

	d = S.Apply(b, c).Or(b.Eq(c))
	verify(d)

	d = ForAll(b, c)(c.Eq(b).Or(S.Apply(b, c)))
	verify(d, ForAll(b, c)(S.Apply(b, c).Or(b.Eq(c))))

	d = ForAll(b, c)(c.Eq(b).Or(S.Apply(c, b)))
	verify(d, ForAll(b, c)(S.Apply(b, c).Or(b.Eq(c))))

	d = ForAll(b, c)(S.Apply(b, c).Or(S.Apply(b, b)))
	verify(d, ForAll(b, c)(S.Apply(b, b).Or(S.Apply(b, c))))

	d = ForAll(b, c)(S.Apply(c, c).Or(S.Apply(b, c)))
	verify(d, ForAll(b, c)(S.Apply(b, c).Or(S.Apply(c, c))))

	d = ForAll(b, c)(S.Apply(b, c).Or(S.Apply(c, b)))
	verify(d)

	d = ForAll(b, c)(S.Apply(c, b).Or(S.Apply(b, c)))
	verify(d, ForAll(b, c)(S.Apply(b, c).Or(S.Apply(c, b))))

	d = ForAll(c, b)(S.Apply(c, b).Or(S.Apply(b, c)))
	verify(d)

	d = ForAll(c, b)(S.Apply(b, c).Or(S.Apply(c, b)))
	verify(d, ForAll(c, b)(S.Apply(c, b).Or(S.Apply(b, c))))

	{
		P := Var("P", MakeFun(TypeA, TypeA))
		Q := Var("Q", MakeFun(TypeA, TypeA))
		d = ForAll(P)(P.Apply(b).Neq(Q.Apply(b)))
		verify(d, ForAll(P)(Q.Apply(b).Neq(P.Apply(b))))
	}
	{
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		z := Var("z", TypeA)
		F := Var("F", MakeFun(MakeFun(TypeA, TypeB), TypeA))
		H := Var("H", MakeFun(TypeA, TypeB))
		R := Var("R", MakeFun(TypeA, TypeB, TypeBool))

		d = ForAll(y, z, H)(
			R.Apply(F.Apply(H), H.Apply(F.Apply(H))).
				Or(R.Apply(z, H.Apply(y))).
				Or(Not(R.Apply(F.Apply(x.To(H.Apply(y))), H.Apply(y)))))
		verify(d, ForAll(H, y, z)(
			Not(R.Apply(F.Apply(x.To(H.Apply(y))), H.Apply(y))).
				Or(R.Apply(z, H.Apply(y))).
				Or(R.Apply(F.Apply(H), H.Apply(F.Apply(H))))))
	}
}

func TestEquivalentKey(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	D := Var("D", MakeFun(TypeInd, TypeBool))
	h := Var("h", MakeFun(TypeA, TypeA))
	P := Var("P", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeA, TypeBool))

	c0 := MakeClause(ForAll(D, a, b)(
		Not(D.Apply(a)).Or(P.Apply(b))))
	c1 := MakeClause(ForAll(a, b, D)(
		(P.Apply(b)).Or(Not(D.Apply(a)))))
	c2 := MakeClause(ForAll(a, b, D)(
		Not(P.Apply(b)).Or(D.Apply(a))))

	c3 := MakeClause(ForAll(R, b, c)(
		Not(R.Apply(b.Eq(c))).Or(P.Apply(b))))
	c4 := MakeClause(ForAll(b, c, R)(
		P.Apply(b).Or(Not(R.Apply(c.Eq(b))))))
	c5 := MakeClause(ForAll(a, c, D)(
		(P.Apply(c)).Or(Not(D.Apply(a)))))

	c6 := MakeClause(ForAll(a, b, D)(
		Not(P.Apply(c)).Or(D.Apply(a)).Or(P.Apply(b))))
	c7 := MakeClause(ForAll(a, c, D)(
		Not(P.Apply(c)).Or(D.Apply(a).Or(P.Apply(b)))))
	c8 := MakeClause(ForAll(a, c, D)(
		(P.Apply(c)).Or(D.Apply(a)).Or(Not(P.Apply(b)))))

	c9 := MakeClause(ForAll(a, b, c)(
		Not(P.Apply(c)).Or(D.Apply(a)).Or(P.Apply(b))))
	c10 := MakeClause(ForAll(a, b, c)(
		Not(P.Apply(b)).Or(D.Apply(a)).Or(P.Apply(c))))

	assert.Equal(t, c0.Key(), c1.Key())
	assert.NotEqual(t, c1.Key(), c2.Key())
	assert.Equal(t, c3.Key(), c4.Key())
	assert.Equal(t, c0.Key(), c5.Key())
	assert.NotEqual(t, c6.Key(), c7.Key())
	assert.NotEqual(t, c6.Key(), c8.Key())
	assert.NotEqual(t, c6.Key(), c9.Key())
	assert.Equal(t, c9.Key(), c10.Key())

	c11 := MakeClause(ForAll(b, c)((c.Eq(h.Apply(b)).Or(P.Apply(c)))))
	c12 := MakeClause(ForAll(b, c)((h.Apply(b).Eq(c)).Or(P.Apply(c))))
	c13 := MakeClause(ForAll(c, b)((h.Apply(b).Eq(c)).Or(P.Apply(c))))
	c14 := MakeClause(ForAll(c, b)((P.Apply(c)).Or(h.Apply(b).Eq(c))))
	c15 := MakeClause(ForAll(c, b)((P.Apply(b)).Or(h.Apply(b).Eq(c))))
	c16 := MakeClause(ForAll(c, b)((P.Apply(c)).Or(b.Eq(h.Apply(c)))))

	assert.Equal(t, c11.Key(), c12.Key())
	assert.Equal(t, c11.Key(), c13.Key())
	assert.Equal(t, c11.Key(), c14.Key())
	assert.NotEqual(t, c11.Key(), c15.Key())
	assert.Equal(t, c15.Key(), c16.Key())

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	c20 := MakeClause(ForAll(z)(y.Eq(z)))
	c21 := MakeClause(ForAll(x)(y.Eq(x)))
	c22 := MakeClause(ForAll(y)(y.Eq(x)))
	c23 := MakeClause(ForAll(z)(x.Eq(z)))
	assert.Equal(t, c20.Key(), c21.Key())
	assert.NotEqual(t, c20.Key(), c22.Key())
	assert.Equal(t, c22.Key(), c23.Key())

	c24 := MakeClause(
		ForAll(x, y, z)(Q.Apply(x, y).Or(Q.Apply(y, z)).Or(Q.Apply(x, z))))
	c25 := MakeClause(
		ForAll(x, y, z)(Q.Apply(x, y).Or(Q.Apply(y, x)).Or(Q.Apply(x, z))))
	assert.NotEqual(t, c24.Key(), c25.Key())

	d0 := ForAll(x, y, z)(Q.Apply(x, y).Or(Q.Apply(y, x)).Or(Q.Apply(z, z)))
	d1 := ForAll(x, y, z)(Q.Apply(y, x).Or(Q.Apply(z, z).Or(Q.Apply(x, y))))
	d2 := ForAll(x, y, z)(Q.Apply(x, x).Or(Q.Apply(z, z).Or(Q.Apply(x, y))))
	d3 := ForAll(x, y, z)(Q.Apply(x, x).Or(Q.Apply(x, z).Or(Q.Apply(x, y))))
	components0, _, _, _ := getEquivalentClause(d0)
	components1, _, _, _ := getEquivalentClause(d1)
	components2, _, _, _ := getEquivalentClause(d2)
	components3, _, _, _ := getEquivalentClause(d3)

	assert.Equal(t, len(components0), 2)
	assert.Equal(t, len(components1), 2)
	assert.Equal(t, len(components2), 2)
	assert.Equal(t, len(components3), 1)
	assert.True(t, slices.EqualFunc(components0, components1, Term.AlphaEquals))
	assert.False(t, utils.IsSubset(components0, components2, Term.AlphaEquals))
	assert.False(t, utils.IsSubset(components3, components0, Term.AlphaEquals))

	w := Var("w", TypeA)
	v := Var("v", TypeA)
	P = Var("P", MakeFun(TypeA, TypeA, TypeBool))
	Q = Var("Q", MakeFun(TypeA, TypeA, TypeBool))
	g0 := ForAll(y, z)(Q.Apply(z, y).Or(P.Apply(y, z)))
	g1 := ForAll(y, w)(Q.Apply(w, y).Or(P.Apply(y, w)))
	assert.Equal(t,
		MakeClause(g0).Key(),
		MakeClause(g1).Key())

	g0 = ForAll(y, v)(Q.Apply(y, v).Or(Q.Apply(v, v)))
	g1 = ForAll(w, v)(Q.Apply(w, v).Or(Q.Apply(v, v)))
	assert.Equal(t, MakeClause(g0).Key(), MakeClause(g1).Key())

	d4 := ForAll(x)(x.Eq(z).Or(x.To(P.Apply(x)).Eq((z.To(P.Apply(z))))))
	d5 := ForAll(w)(w.Eq(z).Or(x.To(P.Apply(x)).Eq((z.To(P.Apply(z))))))
	assert.Equal(t, MakeClause(d4).Key(), MakeClause(d5).Key())

	x = Var("x", TypeBool)
	y = Var("y", TypeA)
	z = Var("z", TypeB)
	h = Var("h", MakeFun(TypeA, TypeB))
	d6 := ForAll(x, y, z)(h.Apply(y).Neq(z).Or(x))
	d7 := ForAll(y, z)(h.Apply(y).Neq(z))
	components0, _, _, _ = getEquivalentClause(d6)
	components1, _, _, _ = getEquivalentClause(d7)
	assert.ElementsMatch(t, components0, []Term{F})
	assert.ElementsMatch(t, components1, []Term{F})

	b = Var("b", TypeA)
	c = Var("c", TypeA)
	P = Var("P", MakeFun(TypeA, TypeA, TypeBool))
	d8 := MakeClause(ForAll(b, c)(P.Apply(b, c).Or(P.Apply(b, b))))
	d9 := MakeClause(ForAll(b, c)(P.Apply(b, b).Or(P.Apply(b, c))))
	d10 := MakeClause(ForAll(b, c)(P.Apply(c, b).Or(P.Apply(c, c))))
	d11 := MakeClause(ForAll(b, c)(P.Apply(c, b).Or(P.Apply(b, c))))
	d12 := MakeClause(ForAll(c, b)(P.Apply(c, b).Or(P.Apply(b, c))))
	d13 := MakeClause(ForAll(c, b)(P.Apply(b, c).Or(P.Apply(c, b))))

	assert.Equal(t, d8.Key(), d9.Key())
	assert.Equal(t, d8.Key(), d10.Key())
	assert.NotEqual(t, d8.Key(), d11.Key())
	assert.Equal(t, d12.Key(), d11.Key())
	assert.Equal(t, d13.Key(), d11.Key())

	u := Var("u", TypeA)
	x = Var("x", TypeA)
	z = Var("z", TypeA)
	P = Var("P", MakeFun(TypeA, TypeBool))
	Q = Var("Q", MakeFun(TypeA, TypeBool))

	// ∀z.∀u.∀v.(((z) ∨ (P(u) ∨ z = u) ∨ Q(v))
	g14 := ForAll(z, u, v)((P.Apply(z)).Or(P.Apply(u).Or(z.Eq(u))).Or(Q.Apply(v)))
	// ∀v.∀x.∀y.(x = y ∨ Q(v) ∨ (P(y) ∨ P(x))))
	g15 := ForAll(v, x, y)((y.Eq(x)).Or(Q.Apply(v)).Or(P.Apply(y).Or(P.Apply(x))))
	d14 := MakeClause(g14)
	d15 := MakeClause(g15)

	assert.True(t, slices.EqualFunc(d14.components, d15.components, Term.AlphaEquals))

	P = Var("P", MakeFun(TypeA, TypeA, TypeBool))
	// ∀x.∀y.∀z.(P(x, y) ∨ P(y, z))
	g16 := ForAll(x, y, z)((P.Apply(x, y)).Or(P.Apply(y, z)))
	// ∀x.∀y.∀z.(P(y, z) ∨ P(z, x))
	g17 := ForAll(x, y, z)((P.Apply(y, z)).Or(P.Apply(z, x)))
	d16 := MakeClause(g16)
	d17 := MakeClause(g17)
	assert.True(t, slices.EqualFunc(d16.components, d17.components, Term.AlphaEquals))
}

func TestClauseEquivalentEq(t *testing.T) {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	u := Var("u", TypeA)
	v := Var("v", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	// ∀z.∀u.∀v.(((z) ∨ (P(u) ∨ z = u) ∨ Q(v))
	g0 := ForAll(z, u, v)((P.Apply(z)).Or(P.Apply(u).Or(z.Eq(u))).Or(Q.Apply(v)))
	// ∀v.∀x.∀y.(x = y ∨ Q(v) ∨ (P(y) ∨ P(x))))
	g1 := ForAll(v, x, y)((x.Eq(y)).Or(Q.Apply(v)).Or(P.Apply(y).Or(P.Apply(x))))
	d0 := MakeClause(g0)
	d1 := MakeClause(g1)

	assert.NotEqual(t, g0.AlphaKey(), g1.AlphaKey())
	assert.Equal(t, d0.Key(), d1.Key())
	assertPropAlphaEqual(t, clauseEquivalentEq(g0, g1), testThm(g0.Eq(g1)))

	g2 := P.Apply(x).Or(Q.Apply(y))
	g3 := Q.Apply(y).Or(P.Apply(x))
	d2 := MakeClause(g2)
	d3 := MakeClause(g3)
	assert.NotEqual(t, g2.AlphaKey(), g3.AlphaKey())
	assert.Equal(t, d2.Key(), d3.Key())
	assertPropAlphaEqual(t, clauseEquivalentEq(g2, g3), testThm(g2.Eq(g3)))
}

func TestClauseSpecialize(t *testing.T) {
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	c := Var("c", TypeInd)
	D := Var("D", MakeFun(TypeInd, TypeBool))
	h := Var("h", MakeFun(TypeInd, TypeBool))
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeInd, TypeBool))
	R := Var("R", MakeFun(MakeFun(TypeInd, TypeBool), TypeBool))

	clause := MakeClause(ForAll(Q, D, a, h)(
		(D.Apply(a)).Or(h.Apply(b)).Or(Q.Apply(a, b)).Or(R.Apply(h))))

	thm := clause.Specialize([]TermSubst{
		ext.MakeTermSubst(Q, b.To(a.To(D.Apply(a).Eq(P.Apply(b))))),
		ext.MakeTermSubst(h, c.To(P.Apply(c)))})
	assert.Equal(t, thm.NumHyps(), 1)
	assertTermAlphaEqual(t, thm.Hyp(0), clause.Term())
	assertTermAlphaEqual(t,
		thm.Conclusion(),
		D.Apply(a).Or(P.Apply(b)).Or(D.Apply(b).Eq(P.Apply(a))).Or(R.Apply(P)))
}

func TestSubsumes(t *testing.T) {
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeA))
	I := Var("Inv", MakeFun(TypeA, TypeA))
	One := Var("One", TypeA)

	c0 := MakeClause(ForAll(x)(One.Eq(P.Apply(I.Apply(x), x))))
	c1 := MakeClause(ForAll(x)(x.Eq(P.Apply(I.Apply(One), x))))
	assert.False(t, c0.TriviallySubsumes(c1))

	c0 = MakeClause(ForAll(x)(x.Eq(P.Apply(One, x))))
	c1 = MakeClause(
		ForAll(x, y)(x.Eq(P.Apply(One, x)).Or(y.Eq(I.Apply(y)))))
	assert.True(t, c0.TriviallySubsumes(c1))

	c0 = MakeClause(ForAll(x)(x.Eq(P.Apply(One, x))))
	c1 = MakeClause(
		ForAll(x, y)(x.Eq(P.Apply(One, x)).Or(x.Eq(I.Apply(y)))))
	assert.True(t, c0.TriviallySubsumes(c1))

	c0 = MakeClause(ForAll(y)(y.Eq(P.Apply(One, y))))
	c1 = MakeClause(
		ForAll(x, y)(x.Eq(I.Apply(y)).Or(x.Eq(P.Apply(One, x)))))
	assert.True(t, c0.TriviallySubsumes(c1))

	c0 = MakeClause(ForAll(y)(x.Eq(P.Apply(One, y))))
	c1 = MakeClause(
		ForAll(x, y)(x.Eq(I.Apply(y)).Or(x.Eq(P.Apply(One, y)))))
	assert.False(t, c0.TriviallySubsumes(c1))
}

func TestClauseDivide(t *testing.T) {
	a := Var("a", TypeA)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	d := MakeClause((c.Eq(b).Or(P.Apply(c))))
	division := d.Division()
	thm, dividedClauses, merge := division.RefutingThm, division.DividedClauses, division.Merge
	assert.Equal(t, len(dividedClauses), 2)
	assertTermEqual(t, P.Apply(c), dividedClauses[0].Term())
	assertTermEqual(t, b.Eq(c), dividedClauses[1].Term())
	negTerms := make([]Term, len(dividedClauses))
	for i, c := range dividedClauses {
		assert.True(t, c.divides(d))
		negTerms[i] = Not(c.Term())
	}
	assert.NotNil(t, merge)
	assertPropAlphaEqual(t, thm, testThm(F, append(negTerms, d.Term())...))
	assertPropAlphaEqual(t,
		testThm(F, d.Term()),
		merge([]*ClauseThm{
			MakeClauseThm(testThm(F, dividedClauses[0].Term()), FClause, dividedClauses[0]),
			MakeClauseThm(testThm(F, dividedClauses[1].Term()), FClause, dividedClauses[1]),
		}).Thm)

	randomClause0, randomClause1 := MakeClause(P.Apply(a)), MakeClause(a.Eq(c))
	assertPropAlphaEqual(t,
		testThm(F, d.Term(), randomClause0.Term(), randomClause1.Term()),
		merge([]*ClauseThm{
			MakeClauseThm(
				testThm(F, dividedClauses[0].Term(), randomClause0.Term()),
				FClause, dividedClauses[0], randomClause0),
			MakeClauseThm(
				testThm(F, dividedClauses[1].Term(), randomClause1.Term()),
				FClause, dividedClauses[1], randomClause1),
		}).Thm)

	d = MakeClause(ForAll(b)(c.Eq(b).Or(P.Apply(c))))
	division = d.Division()
	thm, dividedClauses, merge = division.RefutingThm, division.DividedClauses, division.Merge
	assert.Equal(t, len(dividedClauses), 2)
	assertTermEqual(t,
		P.Apply(c),
		dividedClauses[0].Term())
	assertTermEqual(t,
		ForAll(b)(c.Eq(b)),
		dividedClauses[1].Term())
	negTerms = make([]Term, len(dividedClauses))
	for i, c := range dividedClauses {
		assert.True(t, c.divides(d))
		negTerms[i] = Not(c.Term())
	}
	assert.NotNil(t, merge)
	assertPropAlphaEqual(t, thm, testThm(F, append(negTerms, d.Term())...))

	d = MakeClause(ForAll(b, c)(P.Apply(b).Or(P.Apply(c))))
	assert.Nil(t, d.Division())

	d = MakeClause(ForAll(c)(c.Eq(b).Or(P.Apply(c))))
	assert.Nil(t, d.Division())

	f := MakeClause(ForAll(c)(c.Eq(b).Or(P.Apply(c))).Or(P.Apply(b)))
	assert.True(t, d.divides(f))
	assert.False(t, d.divides(d))
	assert.False(t, f.divides(d))

	f = MakeClause(ForAll(c)(c.Eq(b)))
	assert.False(t, f.divides(d))
	assert.False(t, d.divides(f))

	f = MakeClause(ForAll(c)(c.Eq(b)).Or(ForAll(c)(P.Apply(c))))
	assert.False(t, f.divides(d))
	assert.False(t, d.divides(f))

	x := Var("x", TypeA)
	z := Var("z", TypeA)
	u := Var("u", TypeA)
	P = Var("P", MakeFun(TypeA, TypeBool))

	g4 := ForAll(x)(Not(P.Apply(x)).Or(x.Eq(z)).Or(P.Apply(u)))
	g5 := ForAll(x)(Not(P.Apply(x)).Or(x.Eq(z)))
	d4 := MakeClause(g4)
	d5 := MakeClause(g5)
	assert.True(t, d5.divides(d4))

	y := Var("y", TypeA)
	v := Var("v", TypeA)
	w := Var("w", TypeA)
	z = Var("z", TypeA)
	u = Var("u", TypeA)

	x0 := Var("x_0", TypeA)
	y0 := Var("y_0", TypeA)
	z0 := Var("z_0", TypeA)
	P = Var("P", MakeFun(TypeA, TypeA, TypeA))

	g6 := ForAll(y, v, w, z, u)(
		z0.Neq(P.Apply(u, z)).
			Or(P.Apply(z0, y0).Neq(P.Apply(P.Apply(P.Apply(w, v), y), x0))))
	g7 := ForAll(y, w, v)(P.Apply(z0, y0).Neq(P.Apply(P.Apply(P.Apply(w, v), y), x0)))
	d6 := MakeClause(g6)
	d7 := MakeClause(g7)
	assert.True(t, d7.divides(d6))
}

func TestAvoidVarsCollision(t *testing.T) {
	P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	c0 := MakeClause(ForAll(x, y)(Not(R.Apply(x, y)).Or(P.Apply(x, y))))
	c1 := MakeClause(R.Apply(y, x))
	_c0 := c0.AvoidVarsCollision(c1)
	assertTermAlphaEqual(t, _c0.Term(), c0.Term())
	assert.False(t, _c0.Term().HasName(x.AssertVar().Name()))
	assert.False(t, _c0.Term().HasName(y.AssertVar().Name()))

	c0 = MakeClause(R.Apply(y, x))
	c1 = MakeClause(ForAll(x, y)(Not(R.Apply(x, y)).Or(P.Apply(x, y))))
	_c0 = c0.AvoidVarsCollision(c1)
	assertTermEqual(t, _c0.Term(), c0.Term())

	c0 = MakeClause(ForAll(x, y)(Not(R.Apply(x, y)).Or(P.Apply(x, y))))
	c1 = MakeClause(ForAll(x, y)(P.Apply(x, y)))
	_c0 = c0.AvoidVarsCollision(c1)
	assertTermAlphaEqual(t, _c0.Term(), c0.Term())
	assert.False(t, _c0.Term().HasName(x.AssertVar().Name()))
	assert.False(t, _c0.Term().HasName(y.AssertVar().Name()))

	c0 = MakeClause(ForAll(x, y)(Not(R.Apply(x, y)).Or(P.Apply(x, y))))
	c1 = MakeClause(ForAll(x)(P.Apply(x, x)))
	_c0 = c0.AvoidVarsCollision(c1)
	assertTermAlphaEqual(t, _c0.Term(), c0.Term())
	assert.False(t, _c0.Term().HasName(x.AssertVar().Name()))
	assert.True(t, _c0.Term().HasName(y.AssertVar().Name()))
}
