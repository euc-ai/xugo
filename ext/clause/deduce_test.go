package clause

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

func TestContradict(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA))

	assertSelfContradict := func(s Term) {
		c := MakeClause(s)
		assert.NotNil(t, c.SelfContradict())
	}

	assertSelfContradict(ForAll(P)(P.Apply(x).Neq(R.Apply(x))))

	// Eta-asymmetric unit refutation: (λa.f(a)) ≠ f.
	// Unify accepts the sides as βη-equal, so SelfContradict must also run
	// η-normalization after specialization before asserting the conclusion is F.
	{
		a := Var("a", TypeA)
		f := Var("f", MakeFun(TypeA, TypeA))
		assertSelfContradict(a.To(f.Apply(a)).Neq(f))
	}

	assertContradict := func(s0, s1 Term) {
		c0, c1 := MakeClause(s0), MakeClause(s1)
		assert.NotNil(t, c0.Contradicts(c1))
		assert.NotNil(t, c1.Contradicts(c0))
	}

	assertContradict(ForAll(x)(Not(Q.Apply(x))), Q.Apply(y))
	assertContradict(ForAll(x)(Q.Apply(x)), Not(Q.Apply(y)))
	assertContradict(ForAll(x)(Q.Apply(x)), ForAll(y)(Not(Q.Apply(y))))

	assertContradict(
		ForAll(x)(P.Apply(x).Neq(R.Apply(x))),
		R.Apply(y).Eq(P.Apply(y)))
	assertContradict(
		ForAll(x)(P.Apply(x).Eq(R.Apply(x))),
		Not(R.Apply(y).Eq(P.Apply(y))))
	assertContradict(
		ForAll(x)(P.Apply(x).Neq(y)),
		P.Apply(z).Eq(y))

	// Beta-eta case: unification produces lambda terms that need
	// beta-eta normalization before BoolRewrite can reduce to F.
	// Regression test for a panic on an ∃-swap over a function variable.
	{
		a := Var("a", TypeA)
		b := Var("b", TypeA)
		h := Var("h", MakeFun(TypeA, TypeA, TypeA))
		f := Var("f", MakeFun(TypeA, TypeA, TypeA))
		Q2 := Var("Q", MakeFun(MakeFun(TypeA, TypeA, TypeA), TypeBool))

		// ¬Q(h) vs Q(λa.λb.f(b, a))
		// h unifies to λa.λb.f(b, a), needs beta-eta to see contradiction
		assertContradict(
			ForAll(h)(Not(Q2.Apply(h))),
			Q2.Apply(a.To(b.To(f.Apply(b, a)))))
	}
}

func TestSimplifies(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeA))
	Q := Var("P", MakeFun(TypeA, TypeBool))
	I := Var("Inv", MakeFun(TypeA, TypeA))
	One := Var("One", TypeA)

	assertSimplify := func(c0, c1 *Clause, simplifed Term) {
		assertPropAlphaEqual(t, c0.Simplifies(c1).AsThmCert(),
			MakeProp(simplifed, c0.Term(), c1.Term()))
	}

	c0 := MakeClause(x.Eq(I.Apply(x)))
	c1 := MakeClause(ForAll(x)(x.Eq(I.Apply(x))))
	assert.Nil(t, c0.Simplifies(c1))

	c0 = MakeClause(One.Eq(I.Apply(One)))
	c1 = MakeClause(I.Apply(One).Eq(One))
	assert.Nil(t, c0.Simplifies(c1))

	c0 = MakeClause(One.Eq(I.Apply(One)))
	c1 = MakeClause(ForAll(x)(P.Apply(I.Apply(I.Apply(One)), x).Eq(x)))
	assertSimplify(c0, c1, ForAll(x)(P.Apply(One, x).Eq(x)))

	c0 = MakeClause(I.Apply(One).Eq(One))
	c1 = MakeClause(ForAll(x)(P.Apply(I.Apply(I.Apply(One)), x).Eq(x)))
	assertSimplify(c0, c1, ForAll(x)(P.Apply(One, x).Eq(x)))

	c0 = MakeClause(x.Neq(I.Apply(x)))
	c1 = MakeClause((One.Eq(I.Apply(One))).Or(x.Eq(I.Apply(x))))
	assertSimplify(c0, c1, One.Eq(I.Apply(One)))

	c0 = MakeClause(Q.Apply(I.Apply(x)))
	c1 = MakeClause(Q.Apply(I.Apply(x)).Or(x.Eq(One)))
	assertSimplify(c0, c1, T)

	c0 = MakeClause(ForAll(x)(x.Eq(I.Apply(x))))
	c1 = MakeClause(ForAll(x)(P.Apply(I.Apply(I.Apply(x)), x).Eq(x)))
	assertSimplify(c0, c1, ForAll(x)(P.Apply(x, x).Eq(x)))

	PIxx := P.Apply(I.Apply(x), x)
	c0 = MakeClause(ForAll(x)(One.Eq(PIxx)))
	c1 = MakeClause(ForAll(x)(P.Apply(I.Apply(PIxx), PIxx).Eq(PIxx)))
	assertSimplify(c0, c1, P.Apply(I.Apply(One), One).Eq(One))

	// Regression: c1 whose original Term() differs from EffectiveTerm()
	// (here a duplicated disjunct Q(I(One)) ∨ Q(I(One)) that MakeClause
	// normalizes to the unit clause Q(I(One)), giving c1 a simplificationThm).
	// Simplifies rewrites c1.EffectiveTerm(), so the produced thm's hyp for c1
	// is the EFFECTIVE term; MakeClauseThm aligns hyps against c1.Term() (the
	// ORIGINAL), so without bridging that hyp back through c1.simplificationThm
	// the hyp-alignment assert (clause_thm.go) panics ("Should not happen.").
	// This reproduces a crash seen on a finite/∀ set-theory goal.
	QIOne := Q.Apply(I.Apply(One))
	c0 = MakeClause(One.Eq(I.Apply(One)))
	c1 = MakeClause(QIOne.Or(QIOne))
	assert.False(t, c1.simplificationThm.IsZero()) // guard: c1 really has Term ≠ EffectiveTerm
	assertSimplify(c0, c1, Q.Apply(One))
}

func TestFactor(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := utils.Map[ClauseKey, *Clause]{}
	resultChan := make(chan *ClauseThm, 100)
	check := func(terms ...Term) {
		m.Clear()
		for thm := range resultChan {
			m.Store(thm.ConclClause().Key(), thm.ConclClause())
		}
		assert.Equal(t, m.Size(), len(terms))
		for _, c := range terms {
			_, ok := m.Load(MakeClause(c).Key())
			assert.True(t, ok)
		}

		// reopen the channel
		resultChan = make(chan *ClauseThm, 100)
	}

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeBool, TypeBool))

	/////////////////////////////////////////////////////////////////

	// ∀x.∀y.(y ≠ P(x)) ∨ Q(y) ∨ R(Q(P(x)))
	clause := MakeClause(ForAll(x, y)(Not(y.Eq(P.Apply(x))).Or(Q.Apply(y)).Or(R.Apply(Q.Apply(P.Apply(x))))))
	clause.Factor(t.Context(), resultChan)
	check(
		ForAll(x)(Q.Apply(P.Apply(x)).Or(R.Apply(Q.Apply(P.Apply(x))))),
		ForAll(x)(Q.Apply(P.Apply(x)).Or(R.Apply(F))))

	/////////////////////////////////////////////////////////////////

	// ∀x.(P(y) ≠ P(x))
	clause = MakeClause(ForAll(x)(P.Apply(y).Neq(P.Apply(x))))
	clause.Factor(t.Context(), resultChan)
	check(
		F,
		Not(P.Apply(y).Eq(P.Apply(P.Apply(y)))))

	/////////////////////////////////////////////////////////////////

	// ∀x. ¬Q(x) ∨ ¬R(Q(x))
	clause = MakeClause(ForAll(x)(Not(Q.Apply(x)).Or(Not(R.Apply(Q.Apply(x))))))
	clause.Factor(t.Context(), resultChan)
	check(
		ForAll(x)(Not(Q.Apply(x)).Or(Not(R.Apply(T)))))

	// ∀x. Q(x) ∨ ¬R(Q(x))
	clause = MakeClause(ForAll(x)(Q.Apply(x).Or(Not(R.Apply(Q.Apply(x))))))
	clause.Factor(t.Context(), resultChan)
	check(
		ForAll(x)(Q.Apply(x).Or(Not(R.Apply(F)))))

	// ∀x.(P(y) ≠ P(x)) ∨ ¬Q(x)
	clause = MakeClause(ForAll(x)(P.Apply(y).Neq(P.Apply(x)).Or(Not(Q.Apply(x)))))
	clause.Factor(t.Context(), resultChan)
	check(
		Not(Q.Apply(y)),
		P.Apply(y).Neq(P.Apply(P.Apply(y))).Or(Not(Q.Apply(P.Apply(y)))))

	/////////////////////////////////////////////////////////////////

	a := Var("a", TypeB)
	P = Var("P", MakeFun(TypeA, TypeB, TypeBool))
	clause = MakeClause(
		ForAll(x, y, z)(Not(P.Apply(x, a.SuchThat(P.Apply(y, a)))).Or(Not(y.Eq(x))).Or(Q.Apply(z))))
	clause.Factor(t.Context(), resultChan)
	check(
		ForAll(y, z, a)(Not(P.Apply(y, a)).Or(Q.Apply(z))))

	clause = MakeClause(
		ForAll(x)(P.Apply(x, a.SuchThat(P.Apply(y, a))).Or(y.Neq(x))))
	clause.Factor(t.Context(), resultChan)
	check(
		P.Apply(y, a.SuchThat(P.Apply(y, a))))
}

func TestFactorClauseHiddenNegatedImply(t *testing.T) {
	defer goleak.VerifyNone(t)

	p := Var("p", TypeBool)
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	x := Var("x", MakeFun(TypeBool, TypeBool, TypeBool))

	opType := MakeFun(TypeBool, TypeBool, TypeBool)
	y := Var("y", TypeA)
	hiddenI := Const(
		core.NewConstDef(y.To(y), "HIDDEN_NEG_IMPLY_I").Meta(),
		MakeFun(opType, opType))

	c := MakeClause(ForAll(x.AssertVar(), a.AssertVar())(
		Not(hiddenI.Apply(x, a, b)).Or(x.Apply(a, b))))
	subst := TermSubstsGroup{
		ext.MakeTermSubst(x, ext.IMPLY),
		ext.MakeTermSubst(a, p),
	}

	thms := factorClause(c, subst, 1)
	assert.Equal(t, len(thms), 1)
	assertPropAlphaEqual(t, thms[0], MakeProp(b.Or(Not(hiddenI.Apply(ext.IMPLY, T, b))), c.Term()))
}

func TestFactorSkipsArityChangingSpecialize(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	x := Var("x", TypeInd)
	q := Var("q", TypeBool)
	r := Var("r", TypeBool)
	H := Var("H", MakeFun(TypeInd, TypeBool))
	S := Var("S", MakeFun(TypeBool, TypeBool))

	clause := MakeClause(ForAll(H)(
		H.Apply(a).Or(Not(H.Apply(b))).Or(S.Apply(q.Or(r)))))
	subst := TermSubstsGroup{ext.MakeTermSubst(H, x.To(q.Or(r)))}

	specialized := clause.Specialize(subst).RewriteConcl(prop.DeepBetaEta)
	assert.Equal(t, 3, clause.EffectiveNumLits())
	assert.Equal(t, 4, len(DecomposesOR(specialized.Conclusion())))

	assert.Nil(t, factorClause(clause, subst, 0))
}

func TestResolve(t *testing.T) {
	defer goleak.VerifyNone(t)

	m := utils.Map[ClauseKey, *Clause]{}
	resultChan := make(chan *ClauseThm, 100)
	check := func(terms ...Term) {
		m.Clear()
		for thm := range resultChan {
			m.Store(thm.ConclClause().Key(), thm.ConclClause())
		}
		assert.Equal(t, m.Size(), len(terms))
		for _, c := range terms {
			_, ok := m.Load(MakeClause(c).Key())
			assert.True(t, ok)
		}

		// reopen the channel
		resultChan = make(chan *ClauseThm, 100)
	}

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA))
	Q := Var("Q", MakeFun(TypeA, TypeA))
	R := Var("R", MakeFun(TypeA, TypeBool))

	/////////////////////////////////////////////////////////////////

	// P(y) = y
	c0 := MakeClause(P.Apply(y).Eq(y))
	// P(y) = Q(y)
	c1 := MakeClause((P.Apply(y).Eq(Q.Apply(y))))

	c0.Resolve(t.Context(), c1, resultChan)
	check(
		y.Eq(Q.Apply(y)))

	/////////////////////////////////////////////////////////////////

	// ¬R(y)
	c0 = MakeClause(Not(R.Apply(y)))
	// R(y) ∨ (P(y) = Q(y))
	c1 = MakeClause(R.Apply(y).Or(P.Apply(y).Eq(Q.Apply(y))))

	c0.Resolve(t.Context(), c1, resultChan)
	check(
		P.Apply(y).Eq(Q.Apply(y)))

	/////////////////////////////////////////////////////////////////

	// ∀x.(P(x) = y)
	c0 = MakeClause(ForAll(x)(P.Apply(x).Eq(y)))
	// P(y) = Q(y)
	c1 = MakeClause((P.Apply(y).Eq(Q.Apply(y))))

	c0.Resolve(t.Context(), c1, resultChan)
	check(
		y.Eq(Q.Apply(y)),
		ForAll(x)(P.Apply(P.Apply(x)).Eq(Q.Apply(P.Apply(x)))))

	/////////////////////////////////////////////////////////////////

	// ∀x.(P(x) = x)
	c0 = MakeClause(ForAll(x)(P.Apply(x).Eq(x)))
	// P(y) = Q(y)
	c1 = MakeClause((P.Apply(y).Eq(Q.Apply(y))))

	c0.Resolve(t.Context(), c1, resultChan)
	check(
		y.Eq(Q.Apply(y)))

	/////////////////////////////////////////////////////////////////

	// ∀x.(P(x) = x)
	c0 = MakeClause(ForAll(x)(P.Apply(x).Eq(x)))
	// P(y) = P(Q(y))
	c1 = MakeClause((P.Apply(y).Eq(P.Apply(Q.Apply(y)))))

	c0.Resolve(t.Context(), c1, resultChan)
	check(
		P.Apply(y).Eq(Q.Apply(y)),
		y.Eq(P.Apply(Q.Apply(y))))

	/////////////////////////////////////////////////////////////////

	// ∀x.(x = P(x))
	c0 = MakeClause(ForAll(x)(x.Eq(P.Apply(x))))
	// P(y) = P(Q(y))
	c1 = MakeClause((P.Apply(y).Eq(P.Apply(Q.Apply(y)))))

	c0.Resolve(t.Context(), c1, resultChan)
	check(
		P.Apply(y).Eq(Q.Apply(y)),
		y.Eq(P.Apply(Q.Apply(y))))

	/////////////////////////////////////////////////////////////////

	// ∀x.((P(x) = x) ∨ R(x))
	c0 = MakeClause(ForAll(x)(P.Apply(x).Eq(x).Or(R.Apply(x))))
	// P(y) = Q(y)
	c1 = MakeClause((P.Apply(y).Eq(Q.Apply(y))))

	c0.Resolve(t.Context(), c1, resultChan)
	check(
		R.Apply(y).Or(y.Eq(Q.Apply(y))))

	/////////////////////////////////////////////////////////////////

	// ∀x.((P(x) = x) ∨ R(x))
	c0 = MakeClause(ForAll(x)(P.Apply(x).Eq(x).Or(R.Apply(x))))
	// (P(y) = Q(y)) ∨ R(y)
	c1 = MakeClause((P.Apply(y).Eq(Q.Apply(y)).Or(R.Apply(y))))

	c0.Resolve(t.Context(), c1, resultChan)
	check(R.Apply(y).Or(y.Eq(Q.Apply(y))))

	/////////////////////////////////////////////////////////////////

	c0 = MakeClause(ForAll(x)(Not(R.Apply(x))))
	c1 = MakeClause(ForAll(y)(R.Apply(y).Or(x.Neq(y))))
	c0.Resolve(t.Context(), c1, resultChan)
	check(F)

	// ∀x.R(x)
	c0 = MakeClause(ForAll(x)(R.Apply(x)))
	// (P(y) = Q(y)) ∨ ¬R(P(y))
	c1 = MakeClause((P.Apply(y).Eq(Q.Apply(y)).Or(Not(R.Apply(P.Apply(y))))))

	c0.Resolve(t.Context(), c1, resultChan)
	check(
		P.Apply(y).Eq(Q.Apply(y)))

	/////////////////////////////////////////////////////////////////

	c0 = MakeClause(y.Eq(z))
	c1 = MakeClause(ForAll(x, y)(Not(R.Apply(x)).Or(Not(R.Apply(y))).Or(x.Neq(y))))
	c0.Resolve(t.Context(), c1, resultChan)
	check(
		Not(R.Apply(z)))

	c0 = MakeClause(ForAll(x, y)(Not(R.Apply(x)).Or(Not(R.Apply(y))).Or(x.Eq(y))))
	c1 = MakeClause(ForAll(z)(R.Apply(z).Or(x.Neq(z))))
	c0.Resolve(t.Context(), c1, resultChan)
	check(
		ForAll(y)(Not(R.Apply(y)).Or(x.Eq(y))))

	/////////////////////////////////////////////////////////////////

	{
		R = Var("R", MakeFun(TypeA, TypeB, TypeBool))
		f0 := Var("f_0", MakeFun(MakeFun(TypeA, TypeB), TypeA))
		x0 := Var("x_0", TypeA)
		y0 := Var("y_0", TypeB)
		g := Var("g", MakeFun(TypeA, TypeB))
		x = Var("x", TypeA)
		a := Var("a", TypeB)

		// ∀g. (¬R(f₀(g), g(f₀(g))) ∨ y₀ ≠ g(x₀))
		c0 = MakeClause(ForAll(g)(Not(R.Apply(f0.Apply(g), g.Apply(f0.Apply(g)))).Or(y0.Neq(g.Apply(x0)))))
		// ∀x. R(x, εa.(((x = x₀) ⇒ (a = y₀)) ∧ ((x ≠ x₀) ⇒ (a = g(x)))))
		c1 = MakeClause(ForAll(x)(R.Apply(x, a.SuchThat(x.Eq(x0).Imply(a.Eq(y0)).
			And(x.Neq(x0).Imply(a.Eq(g.Apply(x))))))))
		c0.Resolve(t.Context(), c1, resultChan)
		check(F)
	}

	/////////////////////////////////////////////////////////////////

	{
		y := Var("y", TypeA)
		z := Var("z", TypeA)
		x0 := Var("x_0", TypeA)
		y0 := Var("y_0", TypeA)
		z0 := Var("z_0", TypeA)
		Q := Var("Q", MakeFun(TypeA, TypeA, TypeA))
		R := Var("R", MakeFun(TypeA, TypeA, TypeBool))

		// ¬R(x₀, Q(y₀, z₀))
		c0 := MakeClause(Not(R.Apply(x0, Q.Apply(y0, z0))))
		// ∀y.∀z.R(y, Q(y, z))
		c1 := MakeClause(ForAll(y, z)(R.Apply(y, Q.Apply(y, z))))
		c0.Resolve(t.Context(), c1, resultChan)
		check(
			x0.Neq(y0),
			ForAll(z)(Q.Apply(x0, z).Neq(Q.Apply(y0, z0))))
	}

	{
		h := Var("h", MakeFun(TypeA, TypeA, TypeBool))
		x0 := Var("x_0", TypeA)
		y0 := Var("y_0", TypeA)
		z0 := Var("z_0", TypeA)
		alpha := Var("α", MakeFun(MakeFun(TypeA, TypeBool), TypeA, TypeBool))
		// ∀h.α₀(λƶ₀.α₀(h(ƶ₀), y₀), x₀)
		c0 := MakeClause(ForAll(h)(alpha.Apply(z0.To(alpha.Apply(h.Apply(z0), y0)), x0)))
		// ¬α₀(λƶ₀.⊥, x₀)
		c1 := MakeClause(Not(alpha.Apply(z0.To(F), x0)))
		c0.Resolve(t.Context(), c1, resultChan)
		check(
			alpha.Apply(z0.To(F), y0),
			ForAll(h)(z0.To(F).Neq(z0.To(alpha.Apply(h.Apply(z0), y0)))))
	}

	{
		alpha0 := Var("α₀", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd, TypeBool))
		_0 := ext.TestConst("0", TypeInd)
		x := Var("x", TypeInd)

		// c0 α₀(λẋ₁.⊥, 0)
		c0 := MakeClause(alpha0.Apply(x.To(F), _0))
		// c1 α₀(λẋ₁.⊤, 0)
		c1 := MakeClause(alpha0.Apply(x.To(T), _0))
		c0.Resolve(t.Context(), c1, resultChan)
		check()
	}

	{
		// α₀ : (A, A→bool, ind) → bool
		alpha := Var("α", MakeFun(TypeA, MakeFun(TypeA, TypeBool), TypeInd, TypeBool))

		i := Var("i", TypeA)
		i0 := Var("i_0", TypeA)
		k := Var("k", TypeInd) // FREE in c0, BOUND in c1
		n := Var("n", TypeInd) // BOUND in c1
		z := Var("z", TypeA)
		P := Var("P", MakeFun(TypeA, TypeBool))
		Q := Var("Q", MakeFun(TypeA, TypeBool))

		// c0 = ∀i. α(i, P, k)                       — k is free
		c0 := MakeClause(ForAll(i)(alpha.Apply(i, P, k)))
		// c1 = ∀k.∀n. ¬α(i₀, λz.α(z, Q, k), n)      — k is bound
		c1 := MakeClause(ForAll(k, n)(
			Not(alpha.Apply(i0, z.To(alpha.Apply(z, Q, k)), n))))
		c0.Resolve(t.Context(), c1, resultChan)
		//∀i.∀k. α(i₀, λz.α(z, Q, k)) ≠ α(i, P)
		check(
			ForAll(i, k)(alpha.Apply(i0, z.To(alpha.Apply(z, Q, k))).
				Neq(alpha.Apply(i, P))))
	}
}

func TestResolveClauseHiddenNegatedImply(t *testing.T) {
	defer goleak.VerifyNone(t)

	p := Var("p", TypeBool)
	q := Var("q", TypeBool)
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	x := Var("x", MakeFun(TypeBool, TypeBool, TypeBool))

	opType := MakeFun(TypeBool, TypeBool, TypeBool)
	y := Var("y", TypeA)
	hiddenI := Const(
		core.NewConstDef(y.To(y), "HIDDEN_NEG_IMPLY_I").Meta(),
		MakeFun(opType, opType))

	c0 := MakeClause(Not(hiddenI.Apply(ext.IMPLY, p, q)))
	c1 := MakeClause(ForAll(x.AssertVar(), a.AssertVar(), b.AssertVar())(
		Not(x.Apply(a, b)).Or(hiddenI.Apply(x, a, b))))
	subst := TermSubstsGroup{
		ext.MakeTermSubst(x, ext.IMPLY),
		ext.MakeTermSubst(a, p),
		ext.MakeTermSubst(b, q),
	}
	thms := resolveClause(c0, c1, subst, 0, rewriteNeg)
	assert.Equal(t, len(thms), 2)
	assertPropAlphaEqual(t, thms[0], MakeProp(p, c0.Term(), c1.Term()))
	assertPropAlphaEqual(t, thms[1], MakeProp(Not(q), c0.Term(), c1.Term()))
}

func TestResolveSkipsArityChangingSpecialize(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	x := Var("x", TypeInd)
	q := Var("q", TypeBool)
	r := Var("r", TypeBool)
	H := Var("H", MakeFun(TypeInd, TypeBool))
	S := Var("S", MakeFun(TypeBool, TypeBool))

	problematic := MakeClause(ForAll(H)(
		H.Apply(a).Or(Not(H.Apply(b))).Or(S.Apply(q.Or(r)))))
	other := MakeClause(Not(S.Apply(q.Or(r))))
	subst := TermSubstsGroup{ext.MakeTermSubst(H, x.To(q.Or(r)))}

	thm := problematic.Specialize(subst).RewriteConcl(prop.DeepBetaEta)
	components := DecomposesOR(thm.Conclusion())
	assert.NotEqual(t, len(components), problematic.EffectiveNumLits())
	assert.Nil(t, resolveClause(problematic, other, subst, 0, rewriteWhole))
	assert.Nil(t, resolveClause(other, problematic, subst, 0, rewriteNeg))
}

func TestDiffResolveSkipsArityChangingSpecialize(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	c := Var("c", TypeInd)
	d := Var("d", TypeInd)
	x := Var("x", TypeInd)
	q := Var("q", TypeBool)
	r := Var("r", TypeBool)
	H := Var("H", MakeFun(TypeInd, TypeBool))
	S := Var("S", MakeFun(TypeBool, TypeBool))

	problematic := MakeClause(ForAll(H)(
		H.Apply(a).Or(Not(H.Apply(b))).Or(S.Apply(q.Or(r)))))
	subst := TermSubstsGroup{ext.MakeTermSubst(H, x.To(q.Or(r)))}

	specialized := problematic.Specialize(subst).RewriteConcl(prop.DeepBetaEta)
	components := DecomposesOR(specialized.Conclusion())
	assert.NotEqual(t, len(components), problematic.EffectiveNumLits())

	other := MakeClause(Not(S.Apply(q)).Or(c.Eq(d)).Or(q).Or(r))
	assert.Nil(t, diffResolveClause(problematic, other, S.Apply(q), subst, 2, rewriteWhole))
}

// TestResolveDropsGrownResolvent: unification binds c1's higher-order
// `op` slot to a concrete connective, DeepBetaEta expands c1's second
// literal into a top-level disjunction (2 lits → 3), and the
// paramodulation rewrite (c0's equation RHS → LHS, rewriteEqRight)
// deletes no literal — so the kernel-valid resolvent reaches n0+n1 and
// the strict shrink bound fails. resolveClause drops the candidate; an
// Assert there would kill the process from inside a Resolve worker.
//
// The shape is word_bits.BitOfOr's:
//
//	c0: ∀ẋ,ẋʹ.  W(ẋ,ẋʹ) = F(∨λ, ẋ, ẋʹ)          (word_or def, 1 lit)
//	c1: ∀x,y,op. ¬P(F(op,x,y)) ∨ op(R(x), R(y))   (word_bits.BitwiseBinaryProjection ⇒, 2 lits)
//	subst: op ↦ λa.λb.(a ∨ b), ẋ ↦ x, ẋʹ ↦ y      (rewriteEqRight)
func TestResolveDropsGrownResolvent(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeInd)
	y := Var("y", TypeInd)
	xd := Var("xd", TypeInd)
	xd2 := Var("xd2", TypeInd)
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	opTy := MakeFun(TypeBool, TypeBool, TypeBool)
	op := Var("op", opTy)
	F := Var("F", MakeFun(opTy, TypeInd, TypeInd, TypeInd))
	W := Var("W", MakeFun(TypeInd, TypeInd, TypeInd))
	P := Var("P", MakeFun(TypeInd, TypeBool))
	R := Var("R", MakeFun(TypeInd, TypeBool))
	orLam := a.To(b.To(a.Or(b)))

	c0 := MakeClause(ForAll(xd, xd2)(
		W.Apply(xd, xd2).Eq(F.Apply(orLam, xd, xd2))))
	c1 := MakeClause(ForAll(x, y, op)(
		Not(P.Apply(F.Apply(op, x, y))).Or(op.Apply(R.Apply(x), R.Apply(y)))))
	subst := TermSubstsGroup{
		ext.MakeTermSubst(op, orLam),
		ext.MakeTermSubst(xd, x),
		ext.MakeTermSubst(xd2, y),
	}

	// Preconditions of the captured scene: c0 keeps its arity under the
	// substitution (the top-of-function c0 guard passes), while c1's
	// second literal β-expands, 2 lits → 3.
	c0Spec := c0.Specialize(subst).RewriteConcl(prop.DeepBetaEta)
	assert.Equal(t, c0.EffectiveNumLits(), len(DecomposesOR(c0Spec.Conclusion())))
	c1Spec := c1.Specialize(subst).RewriteConcl(prop.DeepBetaEta)
	assert.Equal(t, 2, c1.EffectiveNumLits())
	assert.Equal(t, 3, len(DecomposesOR(c1Spec.Conclusion())))

	// The resolvent would be ¬P(W(x,y)) ∨ R(x) ∨ R(y): true, kernel-
	// derivable, but 3 ≥ 1+2, so it is dropped.
	assert.Nil(t, resolveClause(c0, c1, subst, 0, rewriteEqRight))
}

// TestSimplifiesEtaShortArgument: the pointwise unit ∀x. f(x) = g(x)
// reaches a bare occurrence of f in argument position, K(f) ≠ K(g),
// through Simplifies — EqRewrite reads the pattern λx. f(x) as f — and
// not through Contradicts, which unifies the two literals and finds
// nothing. RefutesByRewrite is this check with the refutation as its only
// answer; the refuter applies it to the clauses a search starts from so a
// given unit closes what a derived one closes.
func TestSimplifiesEtaShortArgument(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))
	K := Var("K", MakeFun(MakeFun(TypeA, TypeB), TypeInd))

	pointwise := MakeClause(ForAll(x)(f.Apply(x).Eq(g.Apply(x))))
	goal := MakeClause(K.Apply(f).Neq(K.Apply(g)))

	assert.Nil(t, pointwise.Contradicts(goal))
	assert.Nil(t, goal.Contradicts(pointwise))
	simp := pointwise.Simplifies(goal)
	if simp == nil {
		t.Fatal("Simplifies must rewrite K(f) ≠ K(g) by ∀x. f(x) = g(x)")
	}
	assert.True(t, simp.IsRefuted(), "got %s", simp)
}

// TestSimplifiesDeclinesANonClauseResult: rewriting set_comprehension to
// λx. x opens the predicate an atom held, set_comprehension(λz. ∃w. P(w),
// y) reducing to ∃w. P(w). The result is no clause, so the rewrite is no
// simplification, and Simplifies declines it rather than build one.
func TestSimplifiesDeclinesANonClauseResult(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", MakeFun(TypeA, TypeBool))
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	w := Var("w", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	setComprehension := Var("set_comprehension",
		MakeFun(MakeFun(TypeA, TypeBool), MakeFun(TypeA, TypeBool)))

	identity := MakeClause(x.To(x).Eq(setComprehension))
	member := MakeClause(ForAll(y)(setComprehension.Apply(z.To(Exists(w)(P.Apply(w)))).Apply(y)))
	assert.Nil(t, identity.Simplifies(member))
}

// TestSimplifiesStopsARuleFeedingItself: (λx. x) = set_comprehension,
// read at a bound variable, rewrites s to set_comprehension(s), and again
// inside that, without end. Its first pass still simplifies the clause —
// the equation (λy. y) = set_comprehension inside it becomes ⊤ — and the
// rewrite stops there, with a clause smaller than it started from.
func TestSimplifiesStopsARuleFeedingItself(t *testing.T) {
	defer goleak.VerifyNone(t)

	predicate := MakeFun(TypeA, TypeBool)
	x := Var("x", predicate)
	y := Var("y", predicate)
	s := Var("s", predicate)
	z := Var("z", TypeA)
	finite := Var("finite", MakeFun(predicate, TypeBool))
	setComprehension := Var("set_comprehension", MakeFun(predicate, predicate))

	identity := MakeClause(x.To(x).Eq(setComprehension))
	member := MakeClause(ForAll(s)(finite.Apply(s).Or(
		Not(finite.Apply(z.To(y.To(y).Eq(setComprehension)))))))
	simp := identity.Simplifies(member)
	if simp == nil {
		t.Fatal("the first pass rewrites (λy. y) = set_comprehension to ⊤ and simplifies the clause")
	}
	assert.Less(t, simp.ConclClause().Term().Size(), member.Term().Size(), "got %s", simp)
}

// TestRefutesByRewrite: the refutation alone, and the clauses it declines
// before building a proof — one whose literal lacks the equation's heads,
// and one the rewrite shrinks without refuting.
func TestRefutesByRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	f := Var("f", MakeFun(TypeA, TypeB))
	g := Var("g", MakeFun(TypeA, TypeB))
	K := Var("K", MakeFun(MakeFun(TypeA, TypeB), TypeInd))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	d := Var("d", TypeInd)

	pointwise := MakeClause(ForAll(x)(f.Apply(x).Eq(g.Apply(x))))
	goal := MakeClause(K.Apply(f).Neq(K.Apply(g)))
	refuted := pointwise.RefutesByRewrite(goal)
	if refuted == nil {
		t.Fatal("∀x. f(x) = g(x) must refute K(f) ≠ K(g)")
	}
	assert.True(t, refuted.IsRefuted())
	assert.Nil(t, goal.RefutesByRewrite(pointwise), "the goal is not a unit equation")

	// A literal without f or g: the rewrite cannot reach ⊥.
	assert.Nil(t, pointwise.RefutesByRewrite(
		MakeClause(K.Apply(f).Neq(K.Apply(g)).Or(Q.Apply(d)))))
	// Every literal carries g, the rewrite shrinks the clause to Q(K(g))
	// and leaves it standing: not a refutation.
	assert.Nil(t, pointwise.RefutesByRewrite(
		MakeClause(K.Apply(f).Neq(K.Apply(g)).Or(Q.Apply(K.Apply(g))))))
}

// TestRulesInstantiateTheBindersAClauseIsReadWith: the rules unify on a
// clause's simplified equivalent, and Specialize instantiates that
// clause's binders, which the clause as it stands need not have.
// ¬P(y, εx.P(y, x)) binds nothing and is read as ∀x.¬P(y, x)
// (univHilbertRewrite), so against P(y, a) the unifier binds x to a, and
// the contradiction, the resolvent and the self-contradiction below are
// each built from the instance at that x.
func TestRulesInstantiateTheBindersAClauseIsReadWith(t *testing.T) {
	defer goleak.VerifyNone(t)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	a := Var("a", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	k := Var("k", MakeFun(TypeA, TypeA))

	chosen := MakeClause(Not(P.Apply(y, x.SuchThat(P.Apply(y, x)))))
	unit := MakeClause(P.Apply(y, a))
	subst := TermSubstsGroup{ext.MakeTermSubst(x, a)}

	// The scene: no binder in the clause, one in the clause it is read as.
	assert.Equal(t, 0, chosen.univBoundVars.Size())
	assert.Equal(t, 1, chosen.effectiveUnivBoundVarCount())
	assert.True(t, chosen.EffectiveTerm().AlphaEquals(ForAll(x)(Not(P.Apply(y, x)))),
		"read as %s", WrapTerm(chosen.EffectiveTerm()))

	// rule runs one rule, a panic inside it reported as the rule's failure.
	rule := func(name string, run func()) {
		t.Helper()
		defer func() {
			if r := recover(); r != nil {
				t.Errorf("%s panicked: %v", name, r)
			}
		}()
		run()
	}

	rule("Specialize", func() {
		instance := chosen.Specialize(subst)
		assert.True(t, instance.Conclusion().AlphaEquals(Not(P.Apply(y, a))),
			"Specialize concludes %s", WrapTerm(instance.Conclusion()))
		assert.True(t, instance.NumHyps() == 1 && instance.HasHyp(chosen.Term()))
	})

	contradicts := func(name string, c0, c1 *Clause) {
		t.Helper()
		rule(name, func() {
			refuted := c0.Contradicts(c1)
			if refuted == nil {
				t.Errorf("%s found no contradiction", name)
				return
			}
			assert.True(t, refuted.IsRefuted())
			assert.True(t, refuted.HasHypClause(chosen) && refuted.HasHypClause(unit))
		})
	}
	contradicts("Contradicts, the read clause first", chosen, unit)
	contradicts("Contradicts, the read clause second", unit, chosen)

	// The read clause rewrites: its literal ¬P(y, x) at x ↦ a turns the
	// P(y, a) of P(y, a) ∨ Q(a) into ⊥.
	rule("resolveClause, the read clause rewriting", func() {
		target := MakeClause(P.Apply(y, a).Or(Q.Apply(a)))
		resolvents := resolveClause(chosen, target, subst, 0, rewriteNeg)
		if assert.Len(t, resolvents, 1) {
			assert.True(t, resolvents[0].ConclClause().Equivalent(MakeClause(Q.Apply(a))),
				"resolvent %s", WrapTerm(resolvents[0].ConclClause().Term()))
		}
	})
	// The read clause is rewritten: P(y, a) = ⊤ meets its instance ¬P(y, a).
	rule("resolveClause, the read clause rewritten", func() {
		resolvents := resolveClause(unit, chosen, subst, 0, rewriteWhole)
		if assert.Len(t, resolvents, 1) {
			assert.True(t, resolvents[0].IsRefuted(),
				"resolvent %s", WrapTerm(resolvents[0].ConclClause().Term()))
		}
	})

	// k(εx. k(x) = k(a)) ≠ k(a) is read as ∀x. k(x) ≠ k(a), false at x ↦ a.
	rule("SelfContradict", func() {
		c := MakeClause(k.Apply(x.SuchThat(k.Apply(x).Eq(k.Apply(a)))).Neq(k.Apply(a)))
		assert.Equal(t, 0, c.univBoundVars.Size())
		assert.Equal(t, 1, c.effectiveUnivBoundVarCount())
		refuted := c.SelfContradict()
		if assert.NotNil(t, refuted) {
			assert.True(t, refuted.IsRefuted())
		}
	})
}

// TestResolveAndFactor_CloseTheirChannelWhenTheyPanic: the consumer of a
// rule's results waits on the channel, so the rule closes it on every
// exit — here a panic on the calling goroutine, which a search reads as
// its fault while the consumer goes on.
func TestResolveAndFactor_CloseTheirChannelWhenTheyPanic(t *testing.T) {
	defer goleak.VerifyNone(t)

	y := Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeA))
	c := MakeClause(P.Apply(y).Eq(y))

	resolved := make(chan *ClauseThm, 1)
	assert.Panics(t, func() { c.Resolve(t.Context(), nil, resolved) })
	_, open := <-resolved
	assert.False(t, open, "Resolve closed its channel")

	var none *Clause
	factored := make(chan *ClauseThm, 1)
	assert.Panics(t, func() { none.Factor(t.Context(), factored) })
	_, open = <-factored
	assert.False(t, open, "Factor closed its channel")
}
