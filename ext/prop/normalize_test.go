package prop

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

func TestUnivQuantifiersSortRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeBool)
	b := Var("b", TypeA)
	c := Var("c", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))

	d := (P.Apply(b).Or(Not(P.Apply(b))))
	assert.Nil(t, univQuantifiersSortRewrite(d))

	d = ForAll(b)(P.Apply(b).Or(Not(P.Apply(b))))
	assert.Nil(t, univQuantifiersSortRewrite(d))

	d = ForAll(c, b)(P.Apply(b).Or(P.Apply(c)).Or(Not(P.Apply(b))))
	assertTermAlphaEqual(t,
		Rhs(univQuantifiersSortRewrite(d)),
		ForAll(b, c)(P.Apply(b).Or(P.Apply(c)).Or(Not(P.Apply(b)))))

	d = ForAll(c, b)(Q.Apply(c).Or(P.Apply(b)))
	assert.Nil(t, univQuantifiersSortRewrite(d))

	d = ForAll(b, c)(Q.Apply(c).Or(P.Apply(b)))
	assertTermAlphaEqual(t,
		Rhs(univQuantifiersSortRewrite(d)),
		ForAll(c, b)(Q.Apply(c).Or(P.Apply(b))))

	d = ForAll(c, b, a)(P.Apply(b).Or(P.Apply(c)).Or(a))
	assertTermAlphaEqual(t,
		Rhs(univQuantifiersSortRewrite(d)),
		ForAll(a, b, c)(P.Apply(b).Or(P.Apply(c)).Or(a)))

	d = ForAll(c, a, b)(a.Or(P.Apply(b).Or(P.Apply(c))))
	assertTermAlphaEqual(t,
		Rhs(univQuantifiersSortRewrite(d)),
		ForAll(a, b, c)(a.Or(P.Apply(b).Or(P.Apply(c)))))
}

func TestDisjunctNormalizeRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	// we assert exact equal, not α-equal, because we want to check whether
	// the quantifier vars are reconstructed correctly.
	assertRewrite := func(t *testing.T, rewrite Rewrite, s0 *ext.TermWrapper, s1 Term) {
		r := rewrite(s0)
		assert.True(t, r.Conclusion().Equals(s0.Eq(s1)),
			"got rhs %v, want rhs %v", ext.FormatTerm(Rhs(r), false), ext.FormatTerm(s1, false))
		assert.Equal(t, r.NumHyps(), 0)
	}
	// For a body symmetric in two binders only the α-class is canonical.
	assertAlphaRewrite := func(t *testing.T, rewrite Rewrite, s0 *ext.TermWrapper, s1 Term) {
		r := rewrite(s0)
		assert.True(t, r != nil && Lhs(r).Equals(s0.Core()) && Rhs(r).AlphaEquals(s1),
			"got rhs %v, want rhs α-equal to %v", ext.FormatTerm(Rhs(r), false), ext.FormatTerm(s1, false))
		assert.Equal(t, r.NumHyps(), 0)
	}

	b := Var("b", TypeA)
	c := Var("c", TypeA)
	d := Var("d", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA, TypeBool))

	rewrite := DisjunctNormalizeRewrite

	s := ForAll(b)(T)
	assertRewrite(t, rewrite, s, T)

	s = Exists(b)(T)
	assertRewrite(t, rewrite, s, T)

	s = ForAll(b)(Exists(c)(R.Apply(b, c)))
	assert.Nil(t, rewrite(s))

	s = Exists(b)(ForAll(c)(R.Apply(b, c)))
	assert.Nil(t, rewrite(s))

	s = ForAll(b)(Not(Exists(c)(R.Apply(b, c))))
	assertRewrite(t, rewrite, s, ForAll(b, c)(Not(R.Apply(b, c))))

	s = ForAll(b)(P.Apply(b).Or(Not(P.Apply(b))))
	assertRewrite(t, rewrite, s, T)

	s = ForAll(b)(P.Apply(b).Or(Not(P.Apply(c))))
	assert.Nil(t, rewrite(s))

	s = ForAll(b, P, Q)(P.Apply(b).Imply(Q.Apply(b)))
	// restoreDisjunctDeBruijnVars is the strict inverse of the DeBruijn
	// rename, so same-type binders are not reshuffled across DeBruijn
	// slots during the sort/restore round-trip. The output is
	// α-equivalent to `∀P.∀Q.∀b.(P(b) ∨ ¬Q(b))`, with P and Q in the
	// positions they occupy after the body-walk sort.
	assertRewrite(t, rewrite, s,
		ForAll(Q, P, b)(Q.Apply(b).Or(Not(P.Apply(b)))))

	s = ForAll(b)(P.Apply(b).Or(P.Apply(b)))
	assertRewrite(t, rewrite, s, ForAll(b)(P.Apply(b)))

	s = P.Apply(b).Or(P.Apply(c)).Or(Not(P.Apply(b)))
	assertRewrite(t, rewrite, s, T)

	s = ForAll(b, c)(Q.Apply(c).Or(P.Apply(b)))
	assertRewrite(t, rewrite, s,
		ForAll(b, c)(P.Apply(b).Or(Q.Apply(c))))

	// b and c are automorphic here (swapping them is a symmetry of the
	// body), so the canonical form is the α-class: which of the two
	// names ends up outermost is not part of the contract.
	s = ForAll(b, c)(P.Apply(c).Or(P.Apply(b)))
	assertAlphaRewrite(t, rewrite, s,
		ForAll(b, c)(P.Apply(b).Or(P.Apply(c))))

	s = P.Apply(b.SuchThat(P.Apply(b))).Or(P.Apply(c.SuchThat(F)))
	assertRewrite(t, rewrite, s,
		P.Apply(c.SuchThat(F)).Or(P.Apply(b.SuchThat(P.Apply(b)))))

	s = c.Eq(b).Or(R.Apply(b, c))
	assertRewrite(t, rewrite, s,
		R.Apply(b, c).Or(b.Eq(c)))

	s = ForAll(b, c)(R.Apply(b, c).Or(R.Apply(b, b)))
	assertRewrite(t, rewrite, s,
		ForAll(b, c)(R.Apply(b, b).Or(R.Apply(b, c))))

	s = ForAll(b, c)(R.Apply(c, c).Or(R.Apply(b, c)))
	assertRewrite(t, rewrite, s,
		ForAll(b, c)(R.Apply(b, c).Or(R.Apply(c, c))))

	s = ForAll(b, c)(R.Apply(b, c).Or(R.Apply(c, b)))
	assert.Nil(t, rewrite(s))

	// Automorphic again: the two spellings of the symmetric body must
	// normalize to one α-class.
	s = ForAll(b, c)(R.Apply(c, b).Or(R.Apply(b, c)))
	assertAlphaRewrite(t, rewrite, s,
		ForAll(b, c)(R.Apply(b, c).Or(R.Apply(c, b))))

	s = ForAll(c, b)(R.Apply(c, b).Or(R.Apply(b, c)))
	assert.Nil(t, rewrite(s))

	s = ForAll(c, b)(R.Apply(b, c).Or(R.Apply(c, b)))
	assertAlphaRewrite(t, rewrite, s,
		ForAll(c, b)(R.Apply(c, b).Or(R.Apply(b, c))))

	s = ForAll(b)(ForAll(c)(R.Apply(b, c)).Or(ForAll(c)(P.Apply(c))))
	assertRewrite(t, rewrite, s,
		ForAll(b)(ForAll(c)(P.Apply(c)).Or(ForAll(c)(R.Apply(b, c)))))

	s = ForAll(b)(ForAll(c)(R.Apply(b, c)).Or(ForAll(b)(P.Apply(b))))
	assertRewrite(t, rewrite, s,
		ForAll(d)(ForAll(b)(P.Apply(b)).Or(ForAll(c)(R.Apply(d, c)))))

	assertNoPanicAndValidEq := func(msg string, s Term) {
		var r *PropWrapper
		assert.NotPanics(t, func() { r = rewrite(s) }, msg)
		if r != nil {
			assert.Equal(t, 0, r.NumHyps())
			assert.True(t, Lhs(r).AlphaEquals(s),
				"rewrite LHS must stay at the original input")
			assert.True(t, Lhs(r).Type().Equals(Rhs(r).Type()),
				"rewrite equality must preserve type")
		}
	}

	s = ForAll(b)(P.Apply(b).Or(Not(P.Apply(b))).And(ForAll(c)(Q.Apply(c))))
	assertNoPanicAndValidEq(
		"newly exposed top-level forall binders must not consume original De Bruijn names", s)

	x := Var("x", TypeA)
	y := Var("y", TypeA)
	z := Var("z", TypeA)
	u := Var("u", TypeA)
	s = ForAll(Q, P, u, z, y)(
		Exists(x)(
			(Q.Apply(x).Or(P.Apply(x))).
				Or(Not(Q.Apply(u)).And(Not(P.Apply(u)))).
				Or(Q.Apply(x).And(Not(Q.Apply(z)).And(Not(P.Apply(z))))).
				Or(P.Apply(x).And(Not(Q.Apply(y)).And(Not(P.Apply(y)))))))
	assertNoPanicAndValidEq(
		"De Bruijn spare-window binders under the forall prefix must be restored", s)

	inner := ForAll(c)(Q.Apply(c)).DeBruijn(0)
	s = ForAll(b)(P.Apply(b).And(inner))
	assert.Panics(t, func() { rewrite(s) },
		"reserved De Bruijn-style binders must be rejected at the normalization boundary")
}

func TestNormalize(t *testing.T) {
	defer goleak.VerifyNone(t)

	// Test variables
	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	c := Var("c", TypeInd)
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	R := Var("R", MakeFun(TypeInd, TypeInd, TypeBool))

	t.Run("Proposition with hypotheses", func(t *testing.T) {
		// Test: x, y ⊢ x ∧ y
		prop := testThm(x.And(y), x, y)
		normalized, reconstruct := Normalize(prop)

		// Should remove hypotheses and create disjunction
		assert.Equal(t, 0, normalized.NumHyps())
		// ⊢ (x ∧ y) ∨ ¬x ∨ ¬y simplifies to ⊤
		expectedConcl := T
		assertTermAlphaEqual(t, normalized.Conclusion(), expectedConcl)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with quantifiers", func(t *testing.T) {
		// Test: ⊢ ∀a.P(a) ⇒ Q(a)
		prop := testThm(ForAll(a)(P.Apply(a).Imply(Q.Apply(a))))
		normalized, reconstruct := Normalize(prop)

		// Should convert implication to disjunction and preserve quantifier
		assert.Equal(t, 0, normalized.NumHyps())
		// Also adds quantifiers for P and Q: ∀a.∀Q.∀P.(Q(a) ∨ ¬P(a))
		expectedConcl := ForAll(a, Q, P)(Q.Apply(a).Or(Not(P.Apply(a))))
		assertTermAlphaEqual(t, normalized.Conclusion(), expectedConcl)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Closed proposition with implication is not fast-pathed", func(t *testing.T) {
		// This is already closed and hypothesis-free, so Normalize's fast path
		// must rely on DisjunctNormalizeRewrite to notice the implication.
		prop := testThm(ForAll(a, P, Q)(P.Apply(a).Imply(Q.Apply(a))))
		normalized, reconstruct := Normalize(prop)

		expectedConcl := ForAll(a, Q, P)(Q.Apply(a).Or(Not(P.Apply(a))))
		assertTermAlphaEqual(t, normalized.Conclusion(), expectedConcl)

		normalizedTwice, _ := Normalize(normalized)
		assert.True(t, normalized.AlphaEquals(normalizedTwice))

		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with existential quantifier", func(t *testing.T) {
		// Test: ⊢ ∃a.P(a)
		prop := testThm(Exists(a)(P.Apply(a)))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Should handle existential quantifier properly
		assert.True(t, normalized.Conclusion().HasFree(a.AssertVar()) == false)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Complex proposition with multiple quantifiers", func(t *testing.T) {
		// Test: ∀a.P(a) ⊢ ∃b.Q(b)
		prop := testThm(Exists(b)(Q.Apply(b)), ForAll(a)(P.Apply(a)))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Should handle the transformation correctly
		assert.True(t, normalized.Conclusion().HasFree(a.AssertVar()) == false)
		assert.True(t, normalized.Conclusion().HasFree(b.AssertVar()) == false)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with tautology simplification", func(t *testing.T) {
		// Test: ⊢ x ∨ ¬x (excluded middle)
		prop := testThm(x.Or(Not(x)))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Should simplify to ⊤ (true)
		assertTermAlphaEqual(t, normalized.Conclusion(), T)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with contradiction", func(t *testing.T) {
		// Test: x, ¬x ⊢ y
		prop := testThm(y, x, Not(x))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Should detect contradiction and simplify
		// ⊢ y ∨ ¬x ∨ ¬¬x = y ∨ ¬x ∨ x = ⊤
		assertTermAlphaEqual(t, normalized.Conclusion(), T)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with equality sorting", func(t *testing.T) {
		// Test: ⊢ b = a should normalize to a = b if a < b
		prop := testThm(b.Eq(a))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Should sort equality terms
		expectedConcl := ForAll(a, b)(a.Eq(b))
		assertTermAlphaEqual(t, normalized.Conclusion(), expectedConcl)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with nested quantifiers", func(t *testing.T) {
		// Test: ⊢ ∀a.∀b.R(a,b) ⇒ R(b,a)
		prop := testThm(ForAll(a, b)(R.Apply(a, b).Imply(R.Apply(b, a))))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Also adds quantifier for R: ∀a.∀b.∀R.(¬R(a, b) ∨ R(b, a))
		expectedConcl := ForAll(a, b, R)(Not(R.Apply(a, b)).Or(R.Apply(b, a)))
		assertTermAlphaEqual(t, normalized.Conclusion(), expectedConcl)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with free variables in hypotheses", func(t *testing.T) {
		// Test: P(a) ⊢ P(a) ⇔ Q(a)
		prop := testThm(P.Apply(a).Eq(Q.Apply(a)), P.Apply(a))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Should add quantifiers for all free vars:
		// ∀a.∀P.∀Q.(¬P(a) ∨ (P(a) ⇔ Q(a)))
		expectedConcl := ForAll(a, P, Q)(Not(P.Apply(a)).Or(P.Apply(a).Eq(Q.Apply(a))))
		assertTermAlphaEqual(t, normalized.Conclusion(), expectedConcl)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with conjunction in hypothesis", func(t *testing.T) {
		// Test: x ∧ y ⊢ x ∨ y
		prop := testThm(x.Or(y), x.And(y))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// ⊢ (x ∨ y) ∨ ¬(x ∧ y) = (x ∨ y) ∨ (¬x ∨ ¬y)
		// This should simplify due to absorption
		assertTermAlphaEqual(t, normalized.Conclusion(), T)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Empty proposition (just true)", func(t *testing.T) {
		// Test: ⊢ ⊤
		prop := testThm(T)
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		assertTermAlphaEqual(t, normalized.Conclusion(), T)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with false conclusion", func(t *testing.T) {
		// Test: ⊢ ⊥
		prop := testThm(F)
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		assertTermAlphaEqual(t, normalized.Conclusion(), F)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with equivalence", func(t *testing.T) {
		// Test: ⊢ x ⇔ y
		prop := testThm(x.Eq(y))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Actually gets normalized to ∀y.∀x.(y = x)
		expectedConcl := ForAll(y, x)(y.Eq(x))
		assertTermAlphaEqual(t, normalized.Conclusion(), expectedConcl)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Proposition with unique quantifier", func(t *testing.T) {
		// Test: ⊢ ∃!a.P(a)
		prop := testThm(ext.Unique(a)(P.Apply(a)))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Should handle unique quantifier transformation
		assert.True(t, normalized.Conclusion().HasFree(a.AssertVar()) == false)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Multiple hypotheses with shared variables", func(t *testing.T) {
		// Test: P(a), Q(a) ⊢ P(a) ∧ Q(a)
		prop := testThm(P.Apply(a).And(Q.Apply(a)), P.Apply(a), Q.Apply(a))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// This actually simplifies to ⊤
		expectedConcl := T
		assertTermAlphaEqual(t, normalized.Conclusion(), expectedConcl)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Complex nested proposition", func(t *testing.T) {
		// Test: ⊢ ∀a.(∃b.R(a,b)) ⇒ (∃c.R(a,c))
		innerExistsLeft := Exists(b)(R.Apply(a, b))
		innerExistsRight := Exists(c)(R.Apply(a, c))
		prop := testThm(ForAll(a)(innerExistsLeft.Imply(innerExistsRight)))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		// Should handle nested quantifiers properly
		assert.True(t, normalized.Conclusion().HasFree(a.AssertVar()) == false)
		assert.True(t, normalized.Conclusion().HasFree(b.AssertVar()) == false)
		assert.True(t, normalized.Conclusion().HasFree(c.AssertVar()) == false)

		// Reconstruction should work
		reconstructed := reconstruct(normalized)
		assertPropAlphaEqual(t, reconstructed, prop)
	})

	t.Run("Examples", func(t *testing.T) {
		x := Var("x", TypeA)
		y := Var("y", TypeA)
		z := Var("z", TypeA)
		P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
		Q := Var("Q", MakeFun(TypeA, TypeA))
		R := Var("R", MakeFun(TypeA, TypeBool))
		S := Var("S", MakeFun(TypeA, TypeA, TypeBool))

		check := func(p, expectedNormalized Prop, exactReconstruct bool) {
			normalizedProp, reconstruct := Normalize(p)
			assert.True(t, normalizedProp.AlphaEquals(expectedNormalized),
				"normalized shape mismatch\n  got=%s\n  expected=%s",
				PrintProp(normalizedProp), PrintProp(expectedNormalized))
			assert.True(t, normalizedProp.Conclusion().AllFree(utils.EmptyPredicate))
			if exactReconstruct {
				assert.True(t, reconstruct(WrapProp(normalizedProp)).AlphaEquals(p))
			} else {
				assert.True(t, IsStronger(reconstruct(WrapProp(normalizedProp)), p))
			}
			normalizedPropTwice, _ := Normalize(normalizedProp)
			assert.True(t, normalizedProp.AlphaEquals(normalizedPropTwice))
		}

		check(MakeProp(T), MakeProp(T), true)

		// P and S share a type and the block has two fixed points of the
		// appearance-order iteration; the canonical start selects the one
		// with S outermost. The respelling below must key the same.
		check(
			MakeProp(F, P.Apply(Q.Apply(x), y), S.Apply(y, y)),
			MakeProp(ForAll(S, P, Q, y, x)(Not(S.Apply(y, y)).Or(Not(P.Apply(Q.Apply(x), y))))),
			true)

		check(
			MakeProp(P.Apply(Q.Apply(x), y), P.Apply(Q.Apply(x), y)),
			MakeProp(T),
			true)

		check(
			MakeProp(P.Apply(Q.Apply(x), y), ForAll(P)(P.Apply(Q.Apply(x), y))),
			MakeProp(T),
			true)

		// Flatten-first Normalize does not push the conclusion's
		// quantifiers into disjuncts before MoveHypsToConcl just to expose
		// a pre-NNF p∨¬p window. The normalized form is canonical and
		// reconstructable, and this stronger tautology collapse is left to
		// later proof search.
		p := MakeProp(R.Apply(x).Or(P.Apply(z, z)).Or(R.Apply(y)), ForAll(y)(R.Apply(y)), S.Apply(z, z))
		normalizedProp, reconstruct := Normalize(p)
		assert.Equal(t, 0, normalizedProp.NumHyps())
		assert.True(t, normalizedProp.Conclusion().AllFree(utils.EmptyPredicate))
		assert.Nil(t, PreCNFNormalizeRewrite(normalizedProp.Conclusion()))
		normalizedPropTwice, _ := Normalize(normalizedProp)
		assert.True(t, normalizedProp.AlphaEquals(normalizedPropTwice))
		assert.True(t, reconstruct(WrapProp(normalizedProp)).AlphaEquals(p))

		check(
			MakeProp(R.Apply(x), Exists(x, y)(R.Apply(x).And(P.Apply(z, z).And(R.Apply(y))))),
			MakeProp(ForAll(P, R, x, y, z)(R.Apply(x).Or(Not(R.Apply(y))).Or(Not(P.Apply(z, z))))),
			true)

		check(
			MakeProp(P.Apply(Q.Apply(x), y)),
			MakeProp(ForAll(P, Q, x, y)(P.Apply(Q.Apply(x), y))),
			true)

		check(
			MakeProp(P.Apply(Q.Apply(x), y), Not(P.Apply(Q.Apply(x), y))),
			MakeProp(ForAll(P, Q, x, y)(P.Apply(Q.Apply(x), y))),
			true)

		check(
			MakeProp(ForAll(P)(Not(P.Apply(Q.Apply(x), y))).Or(S.Apply(z, z)), P.Apply(Q.Apply(x), y)),
			MakeProp(ForAll(P, S, Q, x, y, z)(Not(P.Apply(Q.Apply(x), y)).Or(S.Apply(z, z)))),
			true)

		check(
			MakeProp(P.Apply(Q.Apply(x), y), Exists(P)(P.Apply(Q.Apply(x), y))),
			MakeProp(ForAll(P, S, Q, x, y)(Not(P.Apply(Q.Apply(x), y)).Or(S.Apply(Q.Apply(x), y)))),
			true)

		check(
			MakeProp(F, P.Apply(Q.Apply(x), y), Exists(P)(P.Apply(Q.Apply(x), y))),
			MakeProp(ForAll(P, Q, x, y)(Not(P.Apply(Q.Apply(x), y)))),
			false)
	})

	t.Run("Idempotency after vacuous quantifier elimination", func(t *testing.T) {
		// Regression test: Normalize was not idempotent when Step 2 introduced
		// a universal quantifier that could be eliminated by ForAllORRewrite.
		// Example: p, (p ∧ q) ⇒ r ⊢ (q ∧ r) ⇔ q
		//   Normalize:            ⊢ ∀p.∀r.∀q.((¬p ∨ (r ⇔ (r ∧ q))) ∨ (r ∧ ¬q))  [before fix]
		//   Normalize(Normalize): ⊢ ∀r.∀q.((r ⇔ (r ∧ q)) ∨ (r ∧ ¬q))
		// After the fix, a single Normalize eliminates ∀p.(¬p ∨ X) → X.
		p := Var("p", TypeBool)
		q := Var("q", TypeBool)
		r := Var("r", TypeBool)

		prop := testThm(q.And(r).Eq(q), p, p.And(q).Imply(r))
		normalized, reconstruct := Normalize(prop)

		assert.Equal(t, 0, normalized.NumHyps())
		assert.True(t, normalized.Conclusion().AllFree(utils.EmptyPredicate))

		// Idempotency: normalizing again should produce the same result
		normalizedTwice, _ := Normalize(normalized)
		assert.True(t, normalized.AlphaEquals(normalizedTwice))

		// Reconstruction should produce something at least as strong as the original
		reconstructed := reconstruct(WrapProp(normalized))
		assert.True(t, IsStronger(reconstructed, prop))

		// Second example: ⊢ ((x ∧ hashek) ⇒ (y ∧ hashek)) ⇒ (x ⇒ y)
		// ForAllORRewrite splits ∀x over ∨, producing (∀x.¬x) as a disjunct.
		// BasicRewrite must then reduce ∀x:Bool.¬x → ⊥ before SimplifyDisjunct
		// can remove it. This requires forAllORSimplify followed by
		// disjunctConclSimplifyRewrite in Step 2b.
		hashek := Var("hashek", TypeBool)
		prop2 := testThm(x.And(hashek).Imply(y.And(hashek)).Imply(x.Imply(y)))
		normalized2, reconstruct2 := Normalize(prop2)

		assert.Equal(t, 0, normalized2.NumHyps())
		assert.True(t, normalized2.Conclusion().AllFree(utils.EmptyPredicate))

		normalizedTwice2, _ := Normalize(normalized2)
		assert.True(t, normalized2.AlphaEquals(normalizedTwice2))

		reconstructed2 := reconstruct2(WrapProp(normalized2))
		assert.True(t, IsStronger(reconstructed2, prop2))

		// Third example: separable quantifier groups with no vacuous quantifiers.
		// Regression test for a canonicalization instability where ForAllORRewrite
		// in Steps 0b/1b would split quantifier groups non-productively, changing
		// variable ordering and producing a different canonical form on each call.
		//
		// a=b, c=d, a=e ⊢ ⊥ normalizes to a flat prenex disjunction where {a,b,e}
		// and {c,d} form separable groups (connected only through the constant '=',
		// not through any quantified function variable). ForAllORRewrite can split
		// them, but doing so changes the variable assignment after re-prenexing,
		// which destabilizes DisjunctNormalizeRewrite's sort order.
		// The fast path in Normalize prevents this by detecting that the output of
		// a previous Normalize call is already canonical.
		d := Var("d", TypeInd)
		e := Var("e", TypeInd)

		prop3 := testThm(F, a.Eq(b), c.Eq(d), a.Eq(e))
		normalized3, reconstruct3 := Normalize(prop3)

		assert.Equal(t, 0, normalized3.NumHyps())
		assert.True(t, normalized3.Conclusion().AllFree(utils.EmptyPredicate))

		normalizedTwice3, _ := Normalize(normalized3)
		assert.True(t, normalized3.AlphaEquals(normalizedTwice3))

		reconstructed3 := reconstruct3(WrapProp(normalized3))
		assert.True(t, IsStronger(reconstructed3, prop3))

		// Verify the fast path: a closed canonical prop normalizes to itself.
		// This is the mechanism that prevents canonicalization instability for
		// complex theorems with separable quantifier groups (like the real_ge
		// theorems). The predicate is the strengthened
		// pre-CNF invariant — DisjunctNormalize-only would let through
		// disjunct-sorted but non-prenex forms.
		assert.Nil(t, PreCNFNormalizeRewrite(normalized3.Conclusion()),
			"PreCNFNormalizeRewrite should be a no-op on already-canonical forms")
	})

	t.Run("Fast path: disjunct-normal but not prenex-normal closed input", func(t *testing.T) {
		// A closed, hyp-free prop can be DisjunctNormalize-canonical (no
		// top-level FORALL → DeBruijn / disjunct-sort no-op) yet still
		// require PreCNFNormalize to pull inner ∀'s to the head and
		// dedup alpha-equivalent disjuncts. Before the fast-path predicate
		// was tightened from `DisjunctNormalize == nil` to
		// `PreCNFNormalize == nil`, such inputs leaked through Normalize
		// unchanged, which broke the statement identity.
		Pa := Var("Pa", MakeFun(TypeInd, TypeBool))
		Qa := Var("Qa", MakeFun(TypeInd, TypeBool))
		ai := Var("ai", TypeInd)
		bi := Var("bi", TypeInd)

		closed := ForAll(Pa, Qa)(ForAll(ai)(Pa.Apply(ai)).Or(ForAll(bi)(Qa.Apply(bi))))
		input := MakeProp(closed)

		// Sanity: input is closed, hyp-free, and DisjunctNormalize-canonical.
		assert.Equal(t, 0, input.NumHyps())
		assert.True(t, input.Conclusion().AllFree(utils.EmptyPredicate))
		assert.Nil(t, DisjunctNormalizeRewrite(input.Conclusion()),
			"input must escape the OLD fast path (DisjunctNormalize == nil)")

		// PreCNFNormalize is NOT a no-op on this input — that's the leak.
		assert.NotNil(t, PreCNFNormalizeRewrite(input.Conclusion()),
			"input must NOT be at PreCNFNormalize fixed point")

		// Normalize should run the full pipeline and produce a prenex-normal
		// canonical form. The exact shape doesn't matter for this test — the
		// invariant we care about is: the output IS at PreCNFNormalize fixed
		// point, and is alpha-different from the input.
		normalized, _ := Normalize(input)
		assert.False(t, normalized.AlphaEquals(input),
			"Normalize must transform a non-prenex-normal closed input")
		assert.Nil(t, PreCNFNormalizeRewrite(normalized.Conclusion()),
			"Normalize output must be PreCNFNormalize-fixed")
		termNormalized, _ := TermNormalize(closed)
		assertTermAlphaEqual(t, normalized.Conclusion(), termNormalized)

		// Idempotency on the new output (which now hits the fast path).
		normalizedTwice, _ := Normalize(normalized)
		assert.True(t, normalized.AlphaEquals(normalizedTwice),
			"Normalize must be idempotent on its own output")
	})

	t.Run("Pre-CNF invariant: implication-free output", func(t *testing.T) {
		// Strengthened Normalize must guarantee its output contains no ⇒.
		// We test a few shapes where ⇒ appears in different positions.
		cases := []Prop{
			testThm(ForAll(a)(P.Apply(a).Imply(Q.Apply(a)))),
			testThm(ForAll(a, b)(R.Apply(a, b).Imply(R.Apply(b, a)))),
			testThm(P.Apply(a).Imply(Q.Apply(a)).Imply(P.Apply(a).Imply(Q.Apply(a)))),
			testThm(ForAll(a)(Exists(b)(R.Apply(a, b))).Imply(Exists(b)(ForAll(a)(R.Apply(a, b))))),
			testThm(ForAll(a)(P.Apply(a)).Imply(P.Apply(a))),
			// implication inside a conjunction inside a disjunction
			testThm(ForAll(a)(P.Apply(a).Imply(Q.Apply(a))).Or(R.Apply(a, b))),
		}
		for i, p := range cases {
			normalized, _ := Normalize(p)
			assert.False(t, hasImplyDeep(normalized.Conclusion()),
				"case %d: normalized form still contains ⇒", i)
		}
	})

	t.Run("Pre-CNF invariant: conjunction ordering", func(t *testing.T) {
		// Conjunction operands must be ordered deterministically by Term.Compare.
		// Build a prop whose normalized form contains a top-level conjunction
		// derived directly from input ordering, and verify ordering.
		// The conjuncts are of different types on purpose: the ∀-closure
		// of two free variables of ONE type over separate conjuncts is a
		// block of separable binders, which Normalize identifies
		// (⊢ B ∧ A with B, A : bool closes to ∀A.A).
		A := Var("A", TypeBool)
		R := Var("R", MakeFun(TypeInd, TypeBool))
		b := Var("b", TypeInd)
		Rb := R.Apply(b)

		// (R(b) ∧ A) and (A ∧ R(b)) should normalize to the same form.
		p1 := testThm(Rb.And(A))
		p2 := testThm(A.And(Rb))
		n1, _ := Normalize(p1)
		n2, _ := Normalize(p2)
		assertPropAlphaEqual(t, n1, n2)

		// And the canonical conjunct order makes the smaller term come first.
		_, body := DecomposesFORALL(n1.Conclusion())
		conjuncts := DecomposesAND(body)
		assert.Equal(t, 2, len(conjuncts))
		assert.True(t, conjuncts[0].AlphaEquals(A), "smaller conjunct first: %s", ext.PrintTerm(body))
	})

	t.Run("Pre-CNF invariant: ⇔ preserved as equality", func(t *testing.T) {
		// ⇔ should be preserved as an equality witness in the
		// normalize layer, not blindly expanded to ((a ∧ b) ∨ (¬a ∧ ¬b)).
		// A propositional comparison key may want ⇔ expanded, but the
		// identity/rewrite layer must not destroy the iff witness.
		bx := Var("x", TypeBool)
		by := Var("y", TypeBool)

		prop := testThm(bx.Eq(by))
		normalized, _ := Normalize(prop)

		// The normalized form should still contain a Bool equality (= for
		// booleans is iff). It must NOT have been expanded into a
		// disjunction of conjunctions.
		assert.True(t, hasBoolEqDeep(normalized.Conclusion()),
			"⇔ witness was destroyed during normalization")
	})

	t.Run("Pre-CNF invariant: idempotency on a small corpus", func(t *testing.T) {
		// Apply Normalize twice on a representative corpus and check stability.
		B := Var("B", TypeBool)
		A := Var("A", TypeBool)
		corpus := []Prop{
			testThm(T),
			testThm(F),
			testThm(ForAll(a)(P.Apply(a))),
			testThm(Exists(a)(P.Apply(a))),
			testThm(ForAll(a)(P.Apply(a).Imply(Q.Apply(a)))),
			testThm(ForAll(a, b)(R.Apply(a, b).Imply(R.Apply(b, a)))),
			testThm(P.Apply(a).Eq(Q.Apply(a))),
			testThm(B.And(A)),
			testThm(B.And(A).Or(A.And(B))),
			testThm(P.Apply(a).Imply(Q.Apply(a)).Imply(P.Apply(a).Imply(Q.Apply(a)))),
			testThm(ForAll(a)(Exists(b)(R.Apply(a, b))).Imply(Exists(b)(ForAll(a)(R.Apply(a, b))))),
			testThm(y, x, Not(x)),
			testThm(x.Or(Not(x))),
			testThm(P.Apply(a).And(Q.Apply(a)), P.Apply(a), Q.Apply(a)),
		}
		for i, p := range corpus {
			n1, _ := Normalize(p)
			n2, _ := Normalize(n1)
			assert.True(t, n1.AlphaEquals(n2),
				"case %d: Normalize is not idempotent", i)
			assert.False(t, hasImplyDeep(n1.Conclusion()),
				"case %d: normalized form contains ⇒", i)
		}
	})

	t.Run("Pre-CNF invariant: closed and hypothesis-free", func(t *testing.T) {
		// Whatever the input shape, the output must have no hypotheses and
		// no free variables.
		B := Var("B", TypeBool)
		corpus := []Prop{
			testThm(P.Apply(a)),
			testThm(P.Apply(a), Q.Apply(a)),
			testThm(P.Apply(a).And(Q.Apply(a))),
			testThm(B),
			testThm(B.And(P.Apply(a))),
			testThm(P.Apply(a).Imply(Q.Apply(a)), P.Apply(a)),
		}
		for i, p := range corpus {
			n, _ := Normalize(p)
			assert.Equal(t, 0, n.NumHyps(),
				"case %d: normalized form still has hypotheses", i)
			assert.True(t, n.Conclusion().AllFree(utils.EmptyPredicate),
				"case %d: normalized form still has free variables", i)
		}
	})

	t.Run("Pre-CNF invariant: ∃ scope variants collapse", func(t *testing.T) {
		// `(∃x.P(x)) ⊕ Q` and `∃x.(P(x) ⊕ Q)` (with x ∉ FV(Q)) are equivalent
		// under safe ∃ prenex. The pre-CNF invariant promises both forms
		// collapse to the same canonical key — without it, the identity and
		// matcher layers see them as distinct, and CNF middle/tail has to
		// re-do the prenex work the identity layer should have done.
		//
		// The deep conjunct/disjunct sort inside ∃ also ensures
		// `∃a.B(a)⊕A(a)` and `∃a.A(a)⊕B(a)` collapse — covered as the
		// "operand order under ∃" pairs below.
		Qb := Q.Apply(b) // bool-typed, free var b shared with the body

		// Each pair: `<∃ pushed in>` and `<∃ pulled out>`, or two operand
		// orderings under ∃.
		pairs := [][2]Prop{
			// ∨ over ∃
			{
				testThm(Exists(a)(P.Apply(a)).Or(Qb)),
				testThm(Exists(a)(P.Apply(a).Or(Qb))),
			},
			// ∧ over ∃
			{
				testThm(Exists(a)(P.Apply(a)).And(Qb)),
				testThm(Exists(a)(P.Apply(a).And(Qb))),
			},
			// inside a hyp — both shapes should produce the same normalized goal
			{
				testThm(R.Apply(a, b), Exists(a)(P.Apply(a)).Or(Qb)),
				testThm(R.Apply(a, b), Exists(a)(P.Apply(a).Or(Qb))),
			},
			// operand order under ∃ (the immediate gap motivating deepDisjunct/Conjunct):
			{
				testThm(Exists(a)(Q.Apply(a).And(P.Apply(a)))),
				testThm(Exists(a)(P.Apply(a).And(Q.Apply(a)))),
			},
			{
				testThm(Exists(a)(Q.Apply(a).Or(P.Apply(a)))),
				testThm(Exists(a)(P.Apply(a).Or(Q.Apply(a)))),
			},
		}
		for i, pair := range pairs {
			n0, rec0 := Normalize(pair[0])
			n1, rec1 := Normalize(pair[1])
			assert.True(t, n0.AlphaEquals(n1),
				"pair %d: ∃ scope variants must collapse\n  pre-canonical: %s\n  post-canonical: %s",
				i, PrintProp(n0), PrintProp(n1))

			// Reconstruct: a proof of the normalized form must lift back to
			// something at least as strong as the original input.
			assert.True(t, IsStronger(rec0(WrapProp(n0)), pair[0]),
				"pair %d: reconstruct(N(t1)) must be stronger than t1", i)
			assert.True(t, IsStronger(rec1(WrapProp(n1)), pair[1]),
				"pair %d: reconstruct(N(t2)) must be stronger than t2", i)

			// Idempotency: normalizing the canonical form is a no-op.
			n0Twice, _ := Normalize(n0)
			n1Twice, _ := Normalize(n1)
			assert.True(t, n0.AlphaEquals(n0Twice),
				"pair %d: Normalize is not idempotent on its own output", i)
			assert.True(t, n1.AlphaEquals(n1Twice),
				"pair %d: Normalize is not idempotent on the paired output", i)
		}
	})

	t.Run("normalized-key shifting shapes", func(t *testing.T) {
		// These are the concrete families on which prop.Normalize has to
		// agree with PreCNFNormalizeTerm.
		// The assertions check the observable contract rather than an exact
		// printed shape: same pre-CNF key where the representations are meant
		// to collapse, idempotency, and reconstruction.
		assertCanonical := func(t *testing.T, p Prop) Prop {
			t.Helper()
			normalized, reconstruct := Normalize(p)
			assert.Equal(t, 0, normalized.NumHyps())
			assert.True(t, normalized.Conclusion().AllFree(utils.EmptyPredicate))

			normalizedTwice, _ := Normalize(normalized)
			assert.True(t, normalized.AlphaEquals(normalizedTwice),
				"Normalize must be idempotent on its output")
			assert.True(t, IsStronger(reconstruct(WrapProp(normalized)), p),
				"reconstruct(N(p)) must be stronger than p")
			return normalized
		}

		t.Run("closed disjunct-normal input still needs pre-CNF", func(t *testing.T) {
			// Old fast path accepted this because DisjunctNormalizeRewrite is
			// nil. It is not a pre-CNF fixed point: the inner universals must
			// be pulled to the prenex prefix.
			Pa := Var("Pa", MakeFun(TypeInd, TypeBool))
			Qa := Var("Qa", MakeFun(TypeInd, TypeBool))
			ai := Var("ai", TypeInd)
			bi := Var("bi", TypeInd)
			closed := ForAll(Pa, Qa)(ForAll(ai)(Pa.Apply(ai)).Or(ForAll(bi)(Qa.Apply(bi))))
			input := testThm(closed)

			assert.Nil(t, DisjunctNormalizeRewrite(closed))
			assert.NotNil(t, PreCNFNormalizeRewrite(closed))

			normalized := assertCanonical(t, input)
			termNormalized, _ := TermNormalize(closed)
			assertTermAlphaEqual(t, normalized.Conclusion(), termNormalized)
			assert.Nil(t, PreCNFNormalizeRewrite(normalized.Conclusion()))
			assert.False(t, normalized.AlphaEquals(input))
		})

		t.Run("raw conclusion scope variants collapse without pre-Move prenex", func(t *testing.T) {
			// Scope variants should be handled by the post-Move whole-clause
			// normalization path, not by a conclusion-only Step 0pre. This
			// keeps the same collapse while preserving contrapositive symmetry.
			left := testThm(Exists(a)(P.Apply(a)).Or(Q.Apply(b)))
			right := testThm(Exists(a)(P.Apply(a).Or(Q.Apply(b))))

			assert.NotNil(t, PreCNFNormalizeRewrite(left.Conclusion()))
			nLeft := assertCanonical(t, left)
			nRight := assertCanonical(t, right)
			assert.True(t, nLeft.AlphaEquals(nRight),
				"∃ scope variants in the raw conclusion must share a normalized key")
		})

		t.Run("hypotheses are implication-normalized before flattening", func(t *testing.T) {
			// Step 0c still applies local implication elimination, so a hyp
			// written with ⇒ shares the same statement identity as the
			// corresponding ¬∨ hyp once the whole clause is normalized.
			rawHyp := x.Imply(y)
			preHyp := Not(x).Or(y)
			assert.NotNil(t, PreCNFNormalizeRewrite(rawHyp))

			rawProp := testThm(x.Or(y), rawHyp)
			preProp := testThm(x.Or(y), preHyp)
			nRaw := assertCanonical(t, rawProp)
			nPre := assertCanonical(t, preProp)
			assert.True(t, nRaw.AlphaEquals(nPre),
				"pre-CNF-equivalent hypotheses must share a normalized key")
		})

		t.Run("post-Move normalization sorts simple hyp conjuncts", func(t *testing.T) {
			// Conjunct order in a hyp is now canonicalized after
			// MoveHypsToConcl, when the hyp appears at its final polarity.
			A := Var("A", TypeBool)
			B := Var("B", TypeBool)
			leftHyp := B.And(A)
			rightHyp := A.And(B)
			assert.NotNil(t, PreCNFNormalizeRewrite(leftHyp))

			left := testThm(A.Or(B), leftHyp)
			right := testThm(A.Or(B), rightHyp)
			nLeft := assertCanonical(t, left)
			nRight := assertCanonical(t, right)
			assert.True(t, nLeft.AlphaEquals(nRight),
				"per-hyp conjunct ordering must be canonical")
		})

		t.Run("quantified hyp conjunct variants still collapse", func(t *testing.T) {
			// Keep the heavier quantified shape from the original
			// investigation. PreCNFNormalizeTerm still sorts under ∃ at the
			// term level for matcher/refuter callers; prop.Normalize reaches
			// the same hyp-key collapse after MoveHypsToConcl.
			A := Var("A", MakeFun(TypeInd, TypeBool))
			B := Var("B", MakeFun(TypeInd, TypeBool))
			leftHyp := Exists(a)(B.Apply(a).And(A.Apply(a)))
			rightHyp := Exists(a)(A.Apply(a).And(B.Apply(a)))
			assert.NotNil(t, PreCNFNormalizeRewrite(leftHyp),
				"deep conjunct sort should rewrite ∃-body conjunct order")
			preLeft := PreCNFNormalizeTerm(leftHyp)
			preRight := PreCNFNormalizeTerm(rightHyp)
			assert.True(t, Rhs(preLeft).AlphaEquals(Rhs(preRight)),
				"PreCNFNormalizeTerm must collapse ∃-body conjunct variants")

			left := testThm(F, leftHyp)
			right := testThm(F, rightHyp)
			nLeft := assertCanonical(t, left)
			nRight := assertCanonical(t, right)
			assert.True(t, nLeft.AlphaEquals(nRight),
				"quantified hyp conjunct variants must share a normalized key")
		})

		t.Run("deep sort under binders is alpha-invariant", func(t *testing.T) {
			// Regression for env-aware deep sort: sorting inside an existential
			// body must compare bound variables by binder position, not by the
			// binder's raw name. These two inputs are alpha-equivalent; before
			// using CompareWithEnv, deep conjunct sort could order the bound
			// and free operands differently for `a` vs `z`.
			z := Var("z", TypeInd)
			t1 := Exists(a)(P.Apply(a).And(P.Apply(b)))
			t2 := Exists(z)(P.Apply(z).And(P.Apply(b)))
			assert.True(t, t1.AlphaEquals(t2))
			assert.NotNil(t, PreCNFNormalizeRewrite(t1))

			pre1 := PreCNFNormalizeTerm(t1)
			pre2 := PreCNFNormalizeTerm(t2)
			assert.True(t, Rhs(pre1).AlphaEquals(Rhs(pre2)),
				"PreCNFNormalizeTerm must preserve alpha-equivalence under binder-local sort")
		})

		t.Run("deep equality sort under binders is alpha-invariant", func(t *testing.T) {
			// Same root cause as the deep conjunct/disjunct sort case, but for
			// equalitySortRewrite. Sorting `h(a) = h(b)` inside `∃a.…` must
			// compare the operands by binder position, not by raw variable
			// name. Without env, `a < b` (no swap) but the alpha-rename `z`
			// gives `z > b` (swap), so the deep equality sort would emit
			// alpha-inequivalent shapes for alpha-equivalent inputs.
			z := Var("z", TypeInd)
			h := Var("h", MakeFun(TypeInd, TypeInd))

			// 1. The deep equality sort itself must be alpha-invariant.
			t1 := Exists(a)(Eq(h.Apply(a), h.Apply(b)))
			t2 := Exists(z)(Eq(h.Apply(z), h.Apply(b)))
			assert.True(t, t1.AlphaEquals(t2))

			w1 := deepEqualitySortRewrite(t1)
			w2 := deepEqualitySortRewrite(t2)
			var r1, r2 Term = t1, t2
			if w1 != nil {
				r1 = Rhs(w1)
			}
			if w2 != nil {
				r2 = Rhs(w2)
			}
			assert.True(t, r1.AlphaEquals(r2),
				"deepEqualitySortRewrite must preserve alpha-equivalence:\n  r1=%s\n  r2=%s",
				ext.PrintTerm(r1), ext.PrintTerm(r2))

			// 2. The bug also surfaced at the PreCNFNormalizeTerm level,
			// where it changes the term-level key. Wrap the equality
			// in a context that the rest of pre-CNF can't simplify away, so
			// the equality sort is the only thing that can shift the shape.
			u1 := P.Apply(b).Or(Exists(a)(WrapTerm(Eq(h.Apply(a), h.Apply(b))).And(P.Apply(a))))
			u2 := P.Apply(b).Or(Exists(z)(WrapTerm(Eq(h.Apply(z), h.Apply(b))).And(P.Apply(z))))
			assert.True(t, u1.AlphaEquals(u2))

			pre1 := PreCNFNormalizeTerm(u1)
			pre2 := PreCNFNormalizeTerm(u2)
			assert.True(t, Rhs(pre1).AlphaEquals(Rhs(pre2)),
				"PreCNFNormalizeTerm must preserve alpha-equivalence under binder-local equality sort:\n  pre1=%s\n  pre2=%s",
				ext.PrintTerm(Rhs(pre1)), ext.PrintTerm(Rhs(pre2)))
		})

		t.Run("size-neutral structural rewrites are not skipped", func(t *testing.T) {
			// This rewrite is structural rather than size-reducing: Normalize
			// must still reach the same fixed point as TermNormalize.
			closed := ForAll(P, Q)(ForAll(a)(P.Apply(a)).Or(ForAll(b)(Q.Apply(b))))
			assert.NotNil(t, PreCNFNormalizeRewrite(closed))

			normalized := assertCanonical(t, testThm(closed))
			termNormalized, _ := TermNormalize(closed)
			assertTermAlphaEqual(t, normalized.Conclusion(), termNormalized)
		})
	})

	t.Run("Pre-CNF: structurally-decoupled ∀-∃ swap is bridged", func(t *testing.T) {
		// `∀b.((∃a.P(a)) ∨ Q(b))` and `∀b.∃a.(P(a) ∨ Q(b))` are equivalent
		// because the body decouples a and b (P only sees a, Q only sees b),
		// so the ∃-witness is uniform across b. Both forms canonicalize to
		// the same pre-CNF key.
		//
		// pair[0] takes the top-∨-then-prenex chain
		// (∀-push, ∃-pull, ∀-pull). pair[1] doesn't have a ∨ between ∀b
		// and ∃a, but with the deep conjunct/disjunct sort inside ∃ — the
		// previous "limitation" turned out to be the same root cause as
		// the operand-order-under-∃ gap: without the deep sort the
		// inner-disjunct order differed between the two inputs, which
		// drove univQuantifiersSort to pick different ∀ orderings. With
		// the deep sort, both reach the same body and the same outer ∀
		// order, hence the same canonical key.
		//
		// The unsound general swap (∀x.∃y.R(x,y) vs ∃y.∀x.R(x,y), where
		// y can depend on x) remains distinct: see the soundness test
		// below.
		Qb := Q.Apply(b)
		t1 := testThm(ForAll(b)(Exists(a)(P.Apply(a)).Or(Qb)))
		t2 := testThm(ForAll(b)(Exists(a)(P.Apply(a).Or(Qb))))

		n1, rec1 := Normalize(t1)
		n2, rec2 := Normalize(t2)
		assert.True(t, n1.AlphaEquals(n2),
			"structurally-decoupled ∀-∃ swap should bridge\n  n1=%s\n  n2=%s",
			PrintProp(n1), PrintProp(n2))

		// Each is a fixed point.
		n1Twice, _ := Normalize(n1)
		n2Twice, _ := Normalize(n2)
		assert.True(t, n1.AlphaEquals(n1Twice),
			"t1 must be idempotent on its own output")
		assert.True(t, n2.AlphaEquals(n2Twice),
			"t2 must be idempotent on its own output")

		// Reconstruct preserves IsStronger.
		assert.True(t, IsStronger(rec1(WrapProp(n1)), t1))
		assert.True(t, IsStronger(rec2(WrapProp(n2)), t2))
	})

	t.Run("Pre-CNF: induction-shape variants collapse", func(t *testing.T) {
		// Regression for a canonicalization bug where semantically equivalent
		// writings of an induction-style theorem reach different (each
		// idempotent) pre-CNF fixed points.
		//
		// All four forms should canonicalize to the same prenex shape
		//     ∀n.∀P.∃kʹ.((P(n) ∨ ¬P(c)) ∨ (P(kʹ) ∧ ¬P(f(kʹ))))
		// (modulo independent-quantifier reordering).
		//
		// `c` and `f` are CONSTANTS (matching the num_induction shape, where
		// 0 and suc are constants). Using free vars instead would have
		// step 0a close them and accidentally canonicalize the prefix
		// symmetrically.
		//
		// Form A: hyp form, free var in concl
		//     P(c), ∀n.(P(n) ⇒ P(f n)) ⊢ P(n)
		// Form B: closed-impl form
		//     ⊢ (P(c) ∧ ∀n.(P(n) ⇒ P(f n))) ⇒ ∀n.P(n)
		// Form A1: hyp form with bool-eq concl
		//     P(c), ∀n.(P(n) ⇒ P(f n)) ⊢ P(n) ⇔ ⊤
		// Form A2: hyp form with funext-wrapped concl
		//     P(c), ∀n.(P(n) ⇒ P(f n)) ⊢ (λn.P(n)) = (λn.⊤)
		//
		// Before the ∀-prepass fix, Form A reached `∀P.∃n.∀kʹ.…` (∀∃∀
		// prefix) because step 1b's deepPrenexRewrite exposed ∃ at the top
		// OR before the inner ∀ was lifted, and no later pass can swap
		// unlike adjacent quantifiers. The fix inserts a deep ∀-only
		// prenex pass in disjunctConclSimplifyRewrite that surfaces every
		// safely-liftable ∀ before ∃ commits.
		//
		// Form A2 reveals a second instance of the same family: the
		// `(λn.φ) = (λn.⊤)` shape must be funext-expanded (via FunEqRewrite)
		// BEFORE the post-Move prenex commits — otherwise the resulting ∀n
		// only appears at step 5, by which time the ∃n has already been
		// pulled outside it.
		cMeta := core.MakeConstMeta("c", TypeInd)
		fMeta := core.MakeConstMeta("f", MakeFun(TypeInd, TypeInd))
		cc := Const(cMeta, TypeInd)
		ff := Const(fMeta, MakeFun(TypeInd, TypeInd))

		Pp := Var("P", MakeFun(TypeInd, TypeBool))
		nn := Var("n", TypeInd)

		hyp1 := Pp.Apply(cc)
		hyp2 := ForAll(nn)(Pp.Apply(nn).Imply(Pp.Apply(ff.Apply(nn))))

		nnVar := nn.AssertVar()
		variants := []struct {
			name string
			prop Prop
		}{
			{"A: hyp form, free var in concl",
				testThm(Pp.Apply(nn), hyp1, hyp2)},
			{"B: closed-impl form",
				testThm(hyp1.And(hyp2).Imply(ForAll(nn)(Pp.Apply(nn))))},
			{"A1: hyp form with P(n) ⇔ ⊤ concl",
				testThm(Pp.Apply(nn).Eq(T), hyp1, hyp2)},
			{"A2: hyp form with (λn.P(n)) = (λn.⊤) concl",
				testThm(WrapTerm(Eq(Abs(nnVar, Pp.Apply(nn)), Abs(nnVar, T))), hyp1, hyp2)},
		}

		var baseline Prop
		for i, v := range variants {
			norm, rec := Normalize(v.prop)
			normTwice, _ := Normalize(norm)
			assert.True(t, norm.AlphaEquals(normTwice),
				"%s: Normalize is not idempotent on its own output", v.name)
			assert.True(t, IsStronger(rec(WrapProp(norm)), v.prop),
				"%s: reconstruct must preserve IsStronger", v.name)
			if i == 0 {
				baseline = norm
				continue
			}
			assert.True(t, baseline.AlphaEquals(norm),
				"%s: must share a normalized key with the baseline\n  baseline=%s\n  this=%s",
				v.name, PrintProp(baseline), PrintProp(norm))
		}
	})

	t.Run("Pre-CNF: contrapositive symmetry", func(t *testing.T) {
		// `Γ, h ⊢ φ` and the contrapositive `Γ, ¬φ ⊢ ¬h` are the same
		// clause (`¬h ∨ φ`) — they should canonicalize to the same
		// normalized key. This was broken by c916b963 when Step 0c
		// switched from `existsANDSimplify` to a full per-hyp
		// PreCNFNormalize: full pre-CNF on a hypothesis commits the
		// hyp to a forward-canonical (∀ outside, ∃ inside) prefix, but
		// MoveHypsToConcl negates the hyp into the conclusion, flipping
		// it to a `∃ outside, ∀ inside` shape that the post-Move
		// pipeline cannot re-canonicalize without an unsound general
		// ∀-∃ swap. The two writings of the same prop end up at
		// different prefix orders.
		//
		// The fix makes Normalize genuinely flatten-first: before
		// MoveHypsToConcl, conclusion processing only closes conclusion-only
		// free variables, and hyp processing only does hyp-only ∃ closure plus
		// local basic rewrites. Prenex/anti-prenex movement happens only after
		// the whole clause is a single disjunction.
		Pa := Var("Pa", MakeFun(TypeInd, TypeBool))
		ai := Var("ai", TypeInd)
		bi := Var("bi", TypeInd)

		// "P is a singleton": ∃ai.P(ai) ∧ ∀ai.∀bi.((P(ai)∧P(bi)) ⇒ ai=bi).
		g0 := Exists(ai)(Pa.Apply(ai)).And(
			ForAll(ai, bi)(Pa.Apply(ai).And(Pa.Apply(bi)).Imply(ai.Eq(bi))))
		// Same "P is a singleton" — uniqueness witness form.
		g1 := Exists(ai)(ForAll(bi)(Pa.Apply(bi).Eq(ai.Eq(bi))))

		direct := testThm(g0, g1)           // g1 ⊢ g0
		contra := testThm(Not(g1), Not(g0)) // ¬g0 ⊢ ¬g1

		nDirect, _ := Normalize(direct)
		nContra, _ := Normalize(contra)
		assert.True(t, nDirect.AlphaEquals(nContra),
			"contrapositive variants must share a normalized key\n  direct=%s\n  contra=%s",
			PrintProp(nDirect), PrintProp(nContra))

		// Regression for conclusion-only anti-prenex: if Normalize pushes
		// `∃` into `∨` on a theorem conclusion before Move, this direct form
		// and its `¬c ⊢ F` writing diverge.
		c := Exists(ai)(Pa.Apply(ai).Or(Pa.Apply(bi)))
		direct = testThm(c)
		contra = testThm(F, Not(c))
		nDirect, _ = Normalize(direct)
		nContra, _ = Normalize(contra)
		assert.True(t, nDirect.AlphaEquals(nContra),
			"conclusion anti-prenex must not run before flattening\n  direct=%s\n  contra=%s",
			PrintProp(nDirect), PrintProp(nContra))
	})

	t.Run("Pre-CNF soundness: unsound ∀-∃ swap is NOT bridged", func(t *testing.T) {
		// `∀x.∃y.R(x,y)` (y can depend on x) and `∃y.∀x.R(x,y)` (uniform y,
		// strictly stronger) are NOT semantically equivalent. The statement
		// identity layer must keep them distinct — collapsing them would be
		// a soundness bug: a proof of the stronger form would be accepted
		// as a proof of the weaker form's key.
		t1 := testThm(ForAll(a)(Exists(b)(R.Apply(a, b))))
		t2 := testThm(Exists(b)(ForAll(a)(R.Apply(a, b))))
		n1, _ := Normalize(t1)
		n2, _ := Normalize(t2)
		assert.False(t, n1.AlphaEquals(n2),
			"unsound ∀-∃ swap unexpectedly collapsed:\n  n1=%s\n  n2=%s",
			PrintProp(n1), PrintProp(n2))
	})

	t.Run("Idempotent", func(t *testing.T) {
		numT := TypeInd
		predT := ext.MakeFun(numT, TypeBool)
		natIntT := ext.MakeFun(numT, ext.MakeFun(numT, TypeBool))

		P := Var("P", predT)
		n := Var("n", numT)
		r := Var("r", numT)
		i := Var("i", numT)
		qp := Var("q'", TypeBool)

		sucMeta := core.MakeConstMeta("suc", ext.MakeFun(numT, numT))
		sucC := ext.Const(sucMeta, ext.MakeFun(numT, numT))
		leMeta := core.MakeConstMeta("≤", natIntT)
		leC := ext.Const(leMeta, natIntT)

		le := func(a, b Term) Term { return leC.Apply(a, b) }
		suc := func(x Term) Term { return sucC.Apply(x) }
		B := suc(n)

		// A = ¬(∀i. P(i) ⇒ suc(n) ≤ i) ⇔ (∃i. ¬(suc(n) ≤ i) ∧ P(i))
		mkA := func() Term {
			forAllImp := ForAll(i)(P.Apply(i).Imply(le(B, i)))
			existsAnd := Exists(i)(Not(le(B, i)).And(P.Apply(i)))
			return Not(forAllImp).Eq(existsAnd)
		}

		existsP := Exists(r)(P.Apply(r))
		// LHS = (∃r.P(r)) ⇒ (A ⇔ q')
		lhs := existsP.Imply(WrapTerm(mkA()).Eq(qp))
		// RHS = ((∃r.P(r)) ⇒ A) ⇔ ((∃r.P(r)) ⇒ q')
		rhs := existsP.Imply(mkA()).Eq(existsP.Imply(qp))
		concl := lhs.Imply(rhs)

		propA := testThm(concl)
		normA, _ := Normalize(propA)
		twiceA, _ := Normalize(normA)
		thriceA, _ := Normalize(twiceA)

		assert.True(t, thriceA.AlphaEquals(normA),
			"Normalize is not idempotent: inner ∀r shadowing outer ∃r is not fully resolved in one pass")
	})

	t.Run("Idempotent", func(t *testing.T) {
		numT := TypeInd
		predT := ext.MakeFun(numT, TypeBool)
		natIntT := ext.MakeFun(numT, ext.MakeFun(numT, TypeBool))

		P := Var("P", predT)
		n := Var("n", numT)
		r := Var("r", numT)
		i := Var("i", numT)

		// suc : num → num (using a generic unary const-like stub via TypeInd)
		sucMeta := core.MakeConstMeta("suc", ext.MakeFun(numT, numT))
		sucC := ext.Const(sucMeta, ext.MakeFun(numT, numT))
		// LE : num → num → bool
		leMeta := core.MakeConstMeta("≤", natIntT)
		leC := ext.Const(leMeta, natIntT)
		le := func(a, b Term) Term { return leC.Apply(a, b) }
		// minimal : (num→bool) → num
		minMeta := core.MakeConstMeta("minimal", ext.MakeFun(predT, numT))
		minC := ext.Const(minMeta, ext.MakeFun(predT, numT))

		suc := func(x Term) Term { return sucC.Apply(x) }

		// B = suc(n)
		Bof := func() Term { return suc(n) }

		// E = (∃r.P(r)) ⇒ (¬(suc(n) ≤ minimal(P)) ⇔ (∃i. ¬(suc(n) ≤ i) ∧ P(i)))
		mkLHS := func() Term {
			existsP := Exists(r)(P.Apply(r))
			minP := minC.Apply(P)
			body := Not(le(Bof(), minP)).Eq(Exists(i)(Not(le(Bof(), i)).And(P.Apply(i))))
			return ForAll(P, n)(existsP.Imply(body))
		}
		// F = (∃r.P(r)) ⇒ (¬(∀i. P(i) ⇒ (suc(n) ≤ i)) ⇔ (∃i. ¬(suc(n) ≤ i) ∧ P(i)))
		mkRHS := func() Term {
			existsP := Exists(r)(P.Apply(r))
			forAllImp := ForAll(i)(P.Apply(i).Imply(le(Bof(), i)))
			body := Not(forAllImp).Eq(Exists(i)(Not(le(Bof(), i)).And(P.Apply(i))))
			return ForAll(P, n)(existsP.Imply(body))
		}

		concl := ext.WrapTerm(mkLHS()).Eq(mkRHS())
		propB := testThm(concl)
		normB, _ := Normalize(propB)
		twiceB, _ := Normalize(normB)
		thriceB, _ := Normalize(twiceB)

		assert.True(t, thriceB.AlphaEquals(normB),
			"Normalize is not idempotent on the ∀-prefix sort permutation pattern")
	})

	t.Run("Idempotent", func(t *testing.T) {
		indT := TypeInd
		setT := ext.MakeFun(indT, TypeBool) // a set is a predicate on ind here
		inMeta := core.MakeConstMeta("set_member", ext.MakeFun(indT, setT, TypeBool))
		inC := ext.Const(inMeta, ext.MakeFun(indT, setT, TypeBool))
		in := func(a, b Term) Term { return inC.Apply(a, b) }

		s := Var("s", setT)
		tt := Var("t", setT)
		tp := Var("t'", setT)
		x := Var("x", indT)

		// (∀x.¬set_member(x, s)) ∨ ((∀x.¬set_member(x, t)) ∨ (∀x.(¬set_member(x, t) ∨ set_member(x, t'))))
		d1 := ForAll(x)(Not(in(x, s)))
		d2 := ForAll(x)(Not(in(x, tt)))
		d3 := ForAll(x)(Not(in(x, tt)).Or(in(x, tp)))
		concl := WrapTerm(d1).Or(WrapTerm(d2).Or(WrapTerm(d3)))

		propC := testThm(concl)
		normC, _ := Normalize(propC)
		twiceC, _ := Normalize(normC)
		thriceC, _ := Normalize(twiceC)

		assert.True(t, thriceC.AlphaEquals(normC),
			"Normalize is not idempotent on the ForAllOR ↔ prenex 2-cycle pattern")
	})
}

func TestPreCNFCacheNormalize(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))

	t.Run("repeat call returns the same cached Prop", func(t *testing.T) {
		// On the SECOND call with the same input, the cache should
		// return the prop stored on the first call — pointer-identical,
		// not just α-equal — proving no recomputation happened.
		cache := &PreCNFCache{}
		p := MakeProp(ForAll(a)(P.Apply(a).Imply(Q.Apply(a))))

		first, _ := cache.Normalize(p)
		assert.Equal(t, 1, cache.PropCacheSize(), "first call should populate cache")

		second, _ := cache.Normalize(p)
		assert.Equal(t, 1, cache.PropCacheSize(), "second call should not grow cache")
		assert.True(t, any(first.Core()) == any(second.Core()), "cache hit must return the same Prop object, not recompute")
	})

	t.Run("α-equivalent input hits the cache", func(t *testing.T) {
		// Two α-equivalent but distinct Prop instances should share the
		// cache entry: the second call returns the first's cached prop.
		cache := &PreCNFCache{}
		p1 := MakeProp(ForAll(a)(P.Apply(a).Imply(Q.Apply(a))))
		p2 := MakeProp(ForAll(a)(P.Apply(a).Imply(Q.Apply(a))))
		assert.True(t, p1.AlphaEquals(p2), "fixture: inputs must be α-equal")

		first, _ := cache.Normalize(p1)
		second, _ := cache.Normalize(p2)
		assert.Equal(t, 1, cache.PropCacheSize(),
			"α-equal inputs should share one cache entry")
		assert.True(t, any(first.Core()) == any(second.Core()), "cache hit on α-equal input must return the first's prop")
	})

	t.Run("lazy reconstruct on cache hit lifts correctly", func(t *testing.T) {
		// The second call's reconstruct is a lazy closure that re-runs
		// the pipeline. Invoking it must still produce a correct lift.
		cache := &PreCNFCache{}
		p := testThm(ForAll(a)(P.Apply(a).Imply(P.Apply(a))))

		_, _ = cache.Normalize(p) // populate cache

		second, reconstruct := cache.Normalize(p)
		lifted := reconstruct(second)
		assertPropAlphaEqual(t, lifted, p)
	})

	t.Run("proved input bypasses cache (no write)", func(t *testing.T) {
		// PreCNFCache.Normalize skips proved inputs: a Thm input should
		// neither read from nor write to the prop cache. Otherwise the
		// cache risks returning an unproved cached prop on a later
		// proved-input call (silently dropping the kernel witness).
		cache := &PreCNFCache{}
		thm := testThm(ForAll(a)(P.Apply(a).Imply(Q.Apply(a))))
		assert.True(t, thm.Proved(), "fixture: input must be a *Thm")

		result, _ := cache.Normalize(thm)
		assert.Equal(t, 0, cache.PropCacheSize(),
			"proved-input Normalize must not write the cache")
		assert.True(t, result.Proved(),
			"proved-input Normalize must return a proved result")
	})

	t.Run("proved input doesn't get poisoned by prior unproved entry", func(t *testing.T) {
		// Critical regression: caching the unproved-normalize result and
		// then returning it for a proved-input call would silently drop
		// the kernel witness. The Normalize impl guards against this by
		// skipping cache READ for proved inputs.
		cache := &PreCNFCache{}
		unproved := MakeProp(ForAll(a)(P.Apply(a).Imply(Q.Apply(a))))
		_, _ = cache.Normalize(unproved) // poison cache with unproved entry
		assert.Equal(t, 1, cache.PropCacheSize())

		thm := testThm(ForAll(a)(P.Apply(a).Imply(Q.Apply(a))))
		result, _ := cache.Normalize(thm)
		assert.True(t, result.Proved(),
			"proved-input call must return a proved result even when an "+
				"α-equivalent unproved entry sits in the cache")
	})

	t.Run("nil receiver bypasses cache entirely", func(t *testing.T) {
		// Backwards compatibility: package-level Normalize routes through
		// (*PreCNFCache)(nil), which must work without any cache state.
		var cache *PreCNFCache // nil
		p := MakeProp(ForAll(a)(P.Apply(a).Imply(Q.Apply(a))))
		result, reconstruct := cache.Normalize(p)
		assert.NotNil(t, result)
		lifted := reconstruct(result)
		assertPropAlphaEqual(t, lifted, p)
	})
}

func TestBridgeNormalize(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))

	t.Run("α-equal inputs return b directly", func(t *testing.T) {
		// Two α-equal props — should return b at the initial fast path
		// without running any pipeline step.
		propA := testThm(P.Apply(a))
		propB := testThm(P.Apply(a))
		bridged := BridgeNormalize(propA, propB)
		assert.NotNil(t, bridged)
		assertPropAlphaEqual(t, bridged, propA)
	})

	t.Run("normalize-equivalent inputs bridge to a's α-form", func(t *testing.T) {
		// p ⇒ q vs ¬p ∨ q — same normalize form, distinct α.
		x := Var("x", TypeBool)
		y := Var("y", TypeBool)
		propA := testThm(x.Imply(y))
		propB := testThm(Not(x).Or(y))

		bridged := BridgeNormalize(propA, propB)
		assert.NotNil(t, bridged)

		// The bridge lifts a proof of propB back through a's reverse
		// chain, so the result must α-equal propA (the target), NOT
		// Normalize(propA).
		assertPropAlphaEqual(t, bridged, propA)
	})

	t.Run("non-normalize-equivalent inputs return nil", func(t *testing.T) {
		// f(a) = a against f(a) = f(f(a)) — the first implies the
		// second, not conversely, so the normal forms differ. (Two free
		// boolean variables over ∧ and over ∨ would NOT do: both close to
		// ∀x.x, since the closure's separable binders are identified.)
		f := Var("f", MakeFun(TypeInd, TypeInd))
		a := Var("a", TypeInd)
		propA := testThm(f.Apply(a).Eq(a))
		propB := testThm(f.Apply(a).Eq(f.Apply(f.Apply(a))))
		// Sanity-check the test fixture: their normalize forms differ.
		normA, _ := Normalize(propA)
		normB, _ := Normalize(propB)
		assert.False(t, normA.AlphaEquals(normB),
			"fixture invalid: expected non-normalize-equivalent inputs")
		assert.Nil(t, BridgeNormalize(propA, propB))
	})

	t.Run("proved source produces proved result", func(t *testing.T) {
		// Build a proved Thm and bridge it back to an α-different but
		// normalize-equivalent target prop. The bridged result must be
		// in target's α-form AND still be a proved Thm.
		raw := ForAll(a)(P.Apply(a).Imply(P.Apply(a)))
		sourceThm := testThm(raw)
		// Target uses ¬∨ form — normalize-equivalent.
		targetProp := MakeProp(ForAll(a)(Not(P.Apply(a)).Or(P.Apply(a))))

		bridged := BridgeNormalize(targetProp, sourceThm)
		assert.NotNil(t, bridged)
		assert.True(t, bridged.Proved(),
			"bridge of a proved source must produce a proved result")
		// Result is in target's α-form (reconstruct lifts back to input).
		assertPropAlphaEqual(t, bridged, targetProp)
	})

	t.Run("matches independent two-call bridge", func(t *testing.T) {
		// Cross-check: BridgeNormalize result == standard
		// reconstructA(normB) computation.
		x := Var("x", TypeBool)
		propA := testThm(ForAll(a)(P.Apply(a).Or(x)))
		propB := testThm(ForAll(b)(x.Or(P.Apply(b))))

		bridged := BridgeNormalize(propA, propB)
		assert.NotNil(t, bridged)

		// Reference computation: full pipeline both sides + emit.
		normA, reconstructA := Normalize(propA)
		normB, _ := Normalize(propB)
		assert.True(t, normA.AlphaEquals(normB),
			"sanity: inputs must be normalize-equivalent for this test")
		reference := reconstructA(normB)

		assertPropAlphaEqual(t, bridged, reference)
	})
}

// walkAllSubterms visits every structural subterm of t, including subterms
// that contain bound variables under enclosing binders. Unlike ext.SubTerms,
// it does not skip subterms with free variables captured by an outer Abs.
func walkAllSubterms(t Term, visit func(Term) bool) bool {
	if visit(t) {
		return true
	}
	switch s := t.Core().(type) {
	case AppliedTerm:
		return walkAllSubterms(s.Fun(), visit) || walkAllSubterms(s.Arg(), visit)
	case AbsTerm:
		return walkAllSubterms(s.Body(), visit)
	}
	return false
}

func TestTermNormalize(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	R := Var("R", MakeFun(TypeInd, TypeInd, TypeBool))
	x := Var("x", TypeBool)
	y := Var("y", TypeBool)

	t.Run("term-level key for matcher use", func(t *testing.T) {
		// Two logically-equivalent but syntactically-different forms must
		// produce the same TermNormalize output (and thus the same alpha key).
		// This is the matcher's primary use case.
		t1 := P.Apply(a).Imply(Q.Apply(a))   // P(a) ⇒ Q(a)
		t2 := Not(P.Apply(a)).Or(Q.Apply(a)) // ¬P(a) ∨ Q(a)
		n1, _ := TermNormalize(t1)
		n2, _ := TermNormalize(t2)
		assertTermAlphaEqual(t, n1, n2)
		assert.Equal(t, n1.AlphaKey(), n2.AlphaKey(),
			"term-level key must collapse ⇒ ↔ ¬∨ representation difference")
	})

	t.Run("free-variable rename collapses", func(t *testing.T) {
		// P(x) and P(y), both with the var free, should produce the same
		// canonical form because TermNormalize closes free variables.
		n1, _ := TermNormalize(P.Apply(a))
		n2, _ := TermNormalize(P.Apply(b))
		assert.Equal(t, n1.AlphaKey(), n2.AlphaKey())
	})

	t.Run("equality witness reconstructs", func(t *testing.T) {
		// The returned equality has the closed form on the left-hand side and
		// the normalized form on the right. For an already-closed input, lhs
		// equals the input.
		t0 := ForAll(a, P, Q)(P.Apply(a).Imply(Q.Apply(a)))
		n, eq := TermNormalize(t0)
		assertTermAlphaEqual(t, Lhs(eq), t0)
		assertTermAlphaEqual(t, Rhs(eq), n)
	})

	t.Run("idempotent", func(t *testing.T) {
		// TermNormalize(TermNormalize(t)) ≡ TermNormalize(t)
		corpus := []Term{
			P.Apply(a),
			ForAll(a)(P.Apply(a).Imply(Q.Apply(a))),
			x.And(y).Imply(x.Or(y)),
			Exists(a)(P.Apply(a)),
			ForAll(a, b)(R.Apply(a, b).Imply(R.Apply(b, a))),
		}
		for i, c := range corpus {
			n1, _ := TermNormalize(c)
			n2, _ := TermNormalize(n1)
			assert.True(t, n1.AlphaEquals(n2), "case %d: TermNormalize not idempotent", i)
		}
	})

	t.Run("matches Normalize(Prop) for closed input", func(t *testing.T) {
		// For a hypothesis-free, closed prop, Normalize(Prop) and TermNormalize
		// must agree on the conclusion's canonical form.
		closedTerm := ForAll(a, P, Q)(P.Apply(a).Imply(Q.Apply(a)))
		propResult, _ := Normalize(testThm(closedTerm))
		termResult, _ := TermNormalize(closedTerm)
		assertTermAlphaEqual(t, propResult.Conclusion(), termResult)
	})
}

// hasImplyDeep returns true if t contains any ⇒ subterm.
// Used to verify the implication-free invariant of pre-CNF Normalize output.
func hasImplyDeep(t Term) bool {
	return walkAllSubterms(t, func(sub Term) bool {
		_, _, ok := MatchesIMPLY(sub)
		return ok
	})
}

// hasBoolEqDeep returns true if t contains an equality between Bool-typed
// terms (i.e., an iff witness). Used to verify ⇔ preservation.
func hasBoolEqDeep(t Term) bool {
	return walkAllSubterms(t, func(sub Term) bool {
		l, _, ok := MatchesEQ(sub)
		return ok && l.Type().Equals(TypeBool)
	})
}

// TestNormalizeHypExistsAbsorbsSibling regression-covers the "Should not
// happen." panic at prop_wrapper.go's DeriveTrans (the HasHyp assert),
// reachable through normalizeHypotheses' outer loop when a mutating
// iteration silently merges a hyp with an α-equal sibling.
//
// The trigger is a pair of hyps
//
//	h₀ = Φ(α)         (α is hyp-only free)
//	h₁ = Φ(εy.Φ(y))   (the Select-property instance of the same predicate)
//
// where Φ(w) := ∃n. (w = s(x,n)) ∧ (¬Q(s(x,n)) ∧ ∀m.(m<n ⇒ Q(s(x,m)))).
// This shape arises naturally in AutoDenote-abbreviation contexts (a Skolem
// const α being denoted as εy.Φ(y) while another hyp still carries the
// literal ε-form); `retrieve goal` reaches it, the StrongerGoals
// hyp-subset variants it normalizes exposing exactly this pair.
// normalizeHypotheses' ∃-closure of α over h₀ (HypExists) substitutes
// α := ε(λα.Φ(α)) — α-equal to h₁ — so the sorted hyp set dedups the two
// and the SelectExists discharge removes the merged hyp. The iterator
// snapshot still yields the absorbed h₁, and an unconditional
// step0LocalRewrite → DeriveTrans on it would hit the "hyp not there"
// assert.
func TestNormalizeHypExistsAbsorbsSibling(t *testing.T) {
	defer goleak.VerifyNone(t)

	A := TypeA
	N := TypeInd
	ltMeta := core.MakeConstMeta("lt_probe", MakeFun(N, N, TypeBool))
	lt := core.MakeConstTerm(ltMeta, MakeFun(N, N, TypeBool))

	Q := Var("Q", MakeFun(A, TypeBool))
	x := Var("x", A)
	s := Var("s", MakeFun(A, N, A))
	alpha := Var("alpha", A)
	a := Var("a", A)
	b := Var("b", A)
	n := Var("n", N)
	m := Var("m", N)
	y := Var("y", A)

	ltT := func(l, r Term) *ext.TermWrapper { return WrapTerm(lt).Apply(l, r) }
	sA := func(base, idx Term) *ext.TermWrapper { return WrapTerm(s).Apply(base, idx) }

	// Φ(w) := ∃n. (w = s(x,n)) ∧ (¬Q(s(x,n)) ∧ ∀m.(m<n ⇒ Q(s(x,m))))
	phi := func(w Term) Term {
		return Exists(n)(
			WrapTerm(w).Eq(sA(x, n)).And(
				Not(Q.Apply(sA(x, n))).And(
					ForAll(m)(ltT(m, n).Imply(Q.Apply(sA(x, m))))))).Core()
	}
	eps := y.SuchThat(phi(y)) // εy.Φ(y)
	concl := WrapTerm(a).Eq(b).Core()

	p := testThm(concl, phi(alpha), phi(eps))
	assert.Equal(t, 2, p.NumHyps(),
		"sanity: the two hyps are distinct at the term level")

	var norm Prop
	assert.NotPanics(t, func() { norm, _ = Normalize(p) })
	// Post-normalize shape: hyps are moved into the conclusion clause.
	assert.Equal(t, 0, norm.NumHyps())
}

// prefixBinderCount counts the leading ∀/∃ binders of t, by kind.
func prefixBinderCount(t Term) (forall, exists int) {
	for {
		if vars, body := DecomposesFORALL(t); !vars.Empty() {
			forall += vars.Size()
			t = body
		} else if vars, body := DecomposesEXISTS(t); !vars.Empty() {
			exists += vars.Size()
			t = body
		} else {
			return
		}
	}
}

// assertOneNormalForm normalizes every variant and requires one α-key;
// it returns that normal form. Each normal form must also be a fixed
// point of Normalize.
func assertOneNormalForm(t *testing.T, variants map[string]Term) Prop {
	t.Helper()
	var first Prop
	var firstName string
	for name, v := range variants {
		n, _ := Normalize(MakeProp(v))
		again, _ := Normalize(n)
		assert.True(t, n.AlphaEquals(again), "%s: Normalize is not idempotent\n  %s\n  %s",
			name, ext.PrintTerm(n.Conclusion()), ext.PrintTerm(again.Conclusion()))
		if first == nil {
			first, firstName = n, name
			continue
		}
		assert.True(t, n.AlphaEquals(first), "%s and %s normalize apart\n  %s\n  %s",
			firstName, name, ext.PrintTerm(first.Conclusion()), ext.PrintTerm(n.Conclusion()))
	}
	return first
}

// The prenex merge must not depend on how a hypothesis's conjunction is
// associated or ordered: two set equations extensionalize into two ∀,
// negate into two ∃, and every spelling of the three-conjunct premise
// must merge them into ONE binder (the nat_sum.UnionEq mismatch: the
// left-nested `(finite(u) ∧ s∩t=∅) ∧ s∪t=u` kept two ∃ where the
// right-nested spelling kept one).
func TestNormalizeConjunctionAssociationCanonical(t *testing.T) {
	setT := MakeFun(TypeA, TypeBool)
	s, v, u, e := Var("s", setT), Var("v", setT), Var("u", setT), Var("e", setT)
	g := Var("g", MakeFun(setT, setT, setT))
	h := Var("h", MakeFun(setT, setT, setT))
	P := Var("P", MakeFun(setT, TypeBool))
	R := Var("R", MakeFun(setT, setT, setT, TypeBool))
	fin := P.Apply(u)
	eq1 := g.Apply(s, v).Eq(e)
	eq2 := h.Apply(s, v).Eq(u)
	concl := R.Apply(s, v, u)
	closed := func(hyp *ext.TermWrapper) Term {
		return ForAll(s, v, u, e)(hyp.Imply(concl))
	}
	n := assertOneNormalForm(t, map[string]Term{
		"(fin ∧ eq1) ∧ eq2": closed(fin.And(eq1).And(eq2)),
		"fin ∧ (eq1 ∧ eq2)": closed(fin.And(eq1.And(eq2))),
		"(eq1 ∧ eq2) ∧ fin": closed(eq1.And(eq2).And(fin)),
		"eq1 ∧ (eq2 ∧ fin)": closed(eq1.And(eq2.And(fin))),
		"(eq1 ∧ fin) ∧ eq2": closed(eq1.And(fin).And(eq2)),
		"eq1 ∧ (fin ∧ eq2)": closed(eq1.And(fin.And(eq2))),
	})
	_, exists := prefixBinderCount(n.Conclusion())
	assert.Equal(t, 1, exists, "the two extensionality binders must merge: %s",
		ext.PrintTerm(n.Conclusion()))
}

// A pack of ∀-closed clauses keys the same in every clause order and
// association: the ∀ over ∧ merge sees the whole flattened chain, and the
// block canonicalization identifies the clauses' binders by rank. The
// clauses share one free function symbol on purpose — the ∀-closure of
// several free symbols of one type is itself a block of separable
// binders, which the canonicalization would (soundly) identify.
func TestNormalizeClausePackCanonical(t *testing.T) {
	m, n := Var("m", TypeInd), Var("n", TypeInd)
	f := Var("f", MakeFun(TypeInd, TypeInd, TypeInd))
	c1 := ForAll(m, n)(f.Apply(m, n).Eq(f.Apply(n, m)))
	c2 := ForAll(m)(f.Apply(m, m).Eq(m))
	c3 := ForAll(m, n)(f.Apply(m, n).Eq(f.Apply(f.Apply(m, n), n)))
	nf := assertOneNormalForm(t, map[string]Term{
		"(1 ∧ 2) ∧ 3": c1.And(c2).And(c3),
		"1 ∧ (2 ∧ 3)": c1.And(c2.And(c3)),
		"(3 ∧ 1) ∧ 2": c3.And(c1).And(c2),
		"2 ∧ (3 ∧ 1)": c2.And(c3.And(c1)),
		"(2 ∧ 1) ∧ 3": c2.And(c1).And(c3),
		"3 ∧ (2 ∧ 1)": c3.And(c2.And(c1)),
	})
	forall, _ := prefixBinderCount(nf.Conclusion())
	// f (∀-closed as a free variable) plus one m and one n.
	assert.Equal(t, 3, forall, "the clauses' binders must merge by rank: %s",
		ext.PrintTerm(nf.Conclusion()))
}

// How the clauses of one block share binders is representation:
// Qx̄.(c₁ op … op cₙ) ⇔ (Qx̄₁.c₁) op … op (Qx̄ₙ.cₙ). The prenex rules
// identify binders by position as they pull them, so a premise's own
// binder order, the premises' order and the ∨ tree a ⇒ chain leaves all
// reached the key (presheaf.GermActionDistributive keyed apart from its
// ∧-joined restatement); canonicalQuantifierBlockRewrite identifies them
// by canonical rank instead.
func TestNormalizeBinderIdentificationCanonical(t *testing.T) {
	s, u, b := Var("s", TypeA), Var("t", TypeA), Var("b", TypeB)
	P := Var("P", MakeFun(TypeA, TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeA, TypeA, TypeBool))
	R := Var("R", MakeFun(TypeB, TypeA, TypeBool))
	c := Var("c", TypeBool)
	p := ForAll(s, u)(P.Apply(s, u))
	q := ForAll(s, u)(Q.Apply(s, u))
	qSwapped := ForAll(u, s)(Q.Apply(s, u))
	r := ForAll(b, s)(R.Apply(b, s))
	// A premise's binder order: ∀s t. Q(s,t) and ∀t s. Q(s,t) are one
	// premise, so the two statements are one.
	assertOneNormalForm(t, map[string]Term{
		"p ⇒ q ⇒ c":  p.Imply(q.Imply(c)),
		"p ⇒ q' ⇒ c": p.Imply(qSwapped.Imply(c)),
		"q' ⇒ p ⇒ c": qSwapped.Imply(p.Imply(c)),
		"p ∧ q ⇒ c":  p.And(q).Imply(c),
		"q' ∧ p ⇒ c": qSwapped.And(p).Imply(c),
	})
	// The premises' order, with a one-binder premise that may share
	// either of the other's two.
	assertOneNormalForm(t, map[string]Term{
		"p ⇒ r ⇒ c":   p.Imply(r.Imply(c)),
		"r ⇒ p ⇒ c":   r.Imply(p.Imply(c)),
		"p ∧ r ⇒ c":   p.And(r).Imply(c),
		"r ∧ p ⇒ c":   r.And(p).Imply(c),
		"p ⇒ (r ⇒ c)": p.Imply(r.Imply(c)),
	})
	// A clause symmetric in its two binders (cardinality.FoldOfAgreeingSteps's
	// commuting steps) ties their ranks; the one-binder clause joins
	// either, and the start labeling then orders the block alike.
	z := Var("z", TypeB)
	h := Var("h", MakeFun(TypeA, TypeB, TypeB))
	S := Var("S", MakeFun(TypeA, TypeBool))
	commute := func(x1, x2 *ext.TermWrapper) *ext.TermWrapper {
		return ForAll(x1, x2, z)(Not(x1.Eq(x2)).Imply(h.Apply(x1, h.Apply(x2, z)).Eq(h.Apply(x2, h.Apply(x1, z)))))
	}
	agree := ForAll(s)(S.Apply(s).Imply(h.Apply(s, z).Eq(z)))
	assertOneNormalForm(t, map[string]Term{
		"commute(s,t) ⇒ agree ⇒ c": commute(s, u).Imply(agree.Imply(c)),
		"commute(t,s) ⇒ agree ⇒ c": commute(u, s).Imply(agree.Imply(c)),
		"agree ⇒ commute(s,t) ⇒ c": agree.Imply(commute(s, u).Imply(c)),
		"agree ∧ commute(t,s) ⇒ c": agree.And(commute(u, s)).Imply(c),
	})
	// A ∀ block over an ∧ chain likewise: the clauses share binders by
	// rank, however the author bound them.
	assertOneNormalForm(t, map[string]Term{
		"∀s t. P ∧ Q":           ForAll(s, u)(P.Apply(s, u).And(Q.Apply(s, u))),
		"(∀s t. P) ∧ (∀s t. Q)": p.And(q),
		"(∀s t. P) ∧ (∀t s. Q)": p.And(qSwapped),
	})
}

// NormalizeKeepingSharing is the normal form with the clauses sharing
// binders as the input shares them: the install form of a dependency,
// which a consumer grounds by the statement's own binders in the
// statement's own roles (prover/proof's NormalizedThm). On
// `∀mx le x y. le(x, mx(x,y)) ∧ le(y, mx(x,y))` the canonical form shares
// the two clauses' binders by rank and so permutes one clause's roles;
// the keep-sharing form's clauses are the input's, and it is the same
// theorem.
func TestNormalizeKeepingSharingKeepsTheClauses(t *testing.T) {
	x, y := Var("x", TypeInd), Var("y", TypeInd)
	mx := Var("mx", MakeFun(TypeInd, TypeInd, TypeInd))
	le := Var("le", MakeFun(TypeInd, TypeInd, TypeBool))
	first := le.Apply(x, mx.Apply(x, y))
	second := le.Apply(y, mx.Apply(x, y))
	stated := MakeProp(ForAll(mx, le, x, y)(first.And(second)))
	kept, _ := NormalizeKeepingSharing(stated)
	_, body := DecomposesFORALL(kept.Conclusion())
	var clauses []string
	for _, c := range DecomposesAND(body) {
		clauses = append(clauses, ext.PrintTerm(c))
	}
	assert.ElementsMatch(t, []string{ext.PrintTerm(first), ext.PrintTerm(second)}, clauses,
		"the clauses as stated: %s", ext.PrintTerm(kept.Conclusion()))
	canonical, _ := Normalize(stated)
	_, canonicalBody := DecomposesFORALL(canonical.Conclusion())
	var canonicalClauses []string
	for _, c := range DecomposesAND(canonicalBody) {
		canonicalClauses = append(canonicalClauses, ext.PrintTerm(c))
	}
	assert.NotElementsMatch(t, clauses, canonicalClauses, "the canonical form shares the binders otherwise")
	renorm, _ := Normalize(kept)
	assert.Equal(t, canonical.AlphaKey(), renorm.AlphaKey(), "one theorem")
}

// A ∀ block under an ∃ and an ∃ block are sorted like the outermost
// prefix, so the order the conjuncts happened to induce is not a key
// (finite_set.FiniteImageEqInj: ∃t.∀x.∀y.∀ẋ. against ∃t.∀ẋ.∀x.∀y.).
func TestNormalizeInnerBlockOrderCanonical(t *testing.T) {
	setT := MakeFun(TypeA, TypeBool)
	tt := Var("t", setT)
	x, y := Var("x", TypeA), Var("y", TypeA)
	z := Var("z", TypeB)
	fin := Var("FIN", MakeFun(setT, TypeBool))
	E := Var("E", MakeFun(TypeB, setT, TypeBool))
	I := Var("I", MakeFun(TypeA, TypeA, setT, TypeBool))
	finT := fin.Apply(tt)
	eq := ForAll(z)(E.Apply(z, tt))
	inj := ForAll(x, y)(I.Apply(x, y, tt))
	assertOneNormalForm(t, map[string]Term{
		"fin ∧ (eq ∧ inj)": Exists(tt)(finT.And(eq.And(inj))),
		"(fin ∧ eq) ∧ inj": Exists(tt)(finT.And(eq).And(inj)),
		"fin ∧ (inj ∧ eq)": Exists(tt)(finT.And(inj.And(eq))),
		"(inj ∧ fin) ∧ eq": Exists(tt)(inj.And(finT).And(eq)),
		"∀y x":             Exists(tt)(finT.And(eq.And(ForAll(y, x)(I.Apply(x, y, tt))))),
	})

	B := Var("B", MakeFun(TypeA, TypeA, TypeBool))
	assertOneNormalForm(t, map[string]Term{
		"∃x y": Exists(x, y)(B.Apply(x, y)),
		"∃y x": Exists(y, x)(B.Apply(x, y)),
	})
}

// prefixBlocks lists the leading quantifier blocks of t as (kind, size),
// kind '∀' or '∃'.
func prefixBlocks(t Term) (blocks []struct {
	kind rune
	size int
}) {
	for {
		if vars, body := DecomposesFORALL(t); !vars.Empty() {
			blocks = append(blocks, struct {
				kind rune
				size int
			}{'∀', vars.Size()})
			t = body
		} else if vars, body := DecomposesEXISTS(t); !vars.Empty() {
			blocks = append(blocks, struct {
				kind rune
				size int
			}{'∃', vars.Size()})
			t = body
		} else {
			return
		}
	}
}

// A completeness-shaped statement — `(∃x.P x) ∧ (∃M.∀x. P x ⇒ x ≤ M) ⇒
// ∃M. (∀x. P x ⇒ x ≤ M) ∧ (∀M'. (∀x. P x ⇒ x ≤ M') ⇒ M ≤ M')` — normalizes
// to ∀…∃N.∀M'.∃y: the hypothesis's unboundedness witness (the ∃ its
// negated ∀ leaves) is NOT identified with the supremum, although both
// are exposed on one ∨ chain; the ∀ under the supremum rises first and
// the two witnesses under it merge. Consumers unpack the supremum by
// position (real_completeness.HrealComplete), so this shape is load-bearing.
func TestNormalizeExistentialHoldingForallPulledBeforeMerge(t *testing.T) {
	x, M, Mp, y := Var("x", TypeA), Var("M", TypeA), Var("M'", TypeA), Var("y", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	L := Var("L", MakeFun(TypeA, TypeA, TypeBool)) // ≤
	bounded := func(b *ext.TermWrapper) *ext.TermWrapper {
		return ForAll(y)(P.Apply(y).Imply(L.Apply(y, b)))
	}
	hyp := Exists(x)(P.Apply(x)).And(Exists(M)(bounded(M)))
	concl := Exists(M)(bounded(M).And(ForAll(Mp)(bounded(Mp).Imply(L.Apply(M, Mp)))))
	n, _ := Normalize(MakeProp(hyp.Imply(concl)))
	blocks := prefixBlocks(n.Conclusion())
	var kinds []rune
	for _, b := range blocks {
		kinds = append(kinds, b.kind)
	}
	assert.Equal(t, []rune{'∀', '∃', '∀', '∃'}, kinds, "prefix: %s", ext.PrintTerm(n.Conclusion()))
	if len(blocks) == 4 {
		assert.Equal(t, 1, blocks[1].size, "the supremum stands alone: %s", ext.PrintTerm(n.Conclusion()))
		assert.Equal(t, 1, blocks[3].size, "the two witnesses merge under the ∀: %s", ext.PrintTerm(n.Conclusion()))
	}
}

// A quantifier block inside a term the statement DENOTES — the argument
// of a head that is no connective and no quantifier — is an encoding
// whose binder order is positional to its readers (pattern_abstraction's paired lambda
// `λ(x,y). t` is `pattern_abstraction(λf. ∀x y. f(x,y) = t)`, the set-builder is
// `set_comprehension(λv. ∃x y. comprehension_spec(…))`), so the block passes must leave it as
// written; the same block in boolean position is canonicalized.
func TestNormalizeLeavesDenotedBlocksAlone(t *testing.T) {
	x, y, z := Var("x", TypeA), Var("y", TypeB), Var("z", TypeInd)
	f := Var("f", MakeFun(TypeA, TypeB, TypeBool))
	Q := Var("Q", MakeFun(MakeFun(TypeA, TypeB, TypeBool), TypeA, TypeB, TypeBool))
	K := Var("K", MakeFun(MakeFun(MakeFun(TypeA, TypeB, TypeBool), TypeBool), TypeInd))
	P := Var("P", MakeFun(TypeInd, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeB, TypeInd, TypeBool))
	T := Var("T", MakeFun(TypeInd, TypeBool))

	// K(λf. ∀y x. Q f x y) and K(λf. ∀x y. Q f x y) are two terms; if the
	// block inside were canonicalized they would become one and
	// P(t₁) ⇒ P(t₂) would collapse to ⊤.
	tYX := K.Apply(f.To(ForAll(y, x)(Q.Apply(f, x, y))))
	tXY := K.Apply(f.To(ForAll(x, y)(Q.Apply(f, x, y))))
	n1, _ := Normalize(MakeProp(P.Apply(tYX).Imply(P.Apply(tXY))))
	n2, _ := Normalize(MakeProp(P.Apply(tXY).Imply(P.Apply(tYX))))
	assert.False(t, n1.Conclusion().Equals(ext.T), "denoted blocks were identified: %s", ext.PrintTerm(n1.Conclusion()))
	assert.NotEqual(t, n1.AlphaKey(), n2.AlphaKey(),
		"a block inside a denoted term must be left as written\n  %s\n  %s",
		ext.PrintTerm(n1.Conclusion()), ext.PrintTerm(n2.Conclusion()))
	assert.Contains(t, ext.PrintTerm(n1.Conclusion()), "∀y.∀x.")
	assert.Contains(t, ext.PrintTerm(n1.Conclusion()), "∀x.∀y.")
	again, _ := Normalize(n1)
	assert.True(t, again.AlphaEquals(n1), "idempotent on the denoted blocks")

	// The same block in boolean position — under an ∃ — is canonical.
	bYX := Exists(z)(ForAll(y, x)(R.Apply(x, y, z)).And(T.Apply(z)))
	bXY := Exists(z)(ForAll(x, y)(R.Apply(x, y, z)).And(T.Apply(z)))
	m1, _ := Normalize(MakeProp(bYX))
	m2, _ := Normalize(MakeProp(bXY))
	assert.Equal(t, m1.AlphaKey(), m2.AlphaKey(),
		"a block in boolean position is canonical\n  %s\n  %s",
		ext.PrintTerm(m1.Conclusion()), ext.PrintTerm(m2.Conclusion()))
}

// TestPreCNFNormalFormHoldsNoConstantItsInputLacks pins what the rule
// rewrites' pre-CNF fallback reads a target by (preCNFRetry.reaches): the
// normalizer's rewrites are those of the logic, so the normal form names
// no constant beside the logic's own that its input does not name.
func TestPreCNFNormalFormHoldsNoConstantItsInputLacks(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	u := Var("u", TypeInd)
	holds := ext.TestConst("normalHolds", MakeFun(TypeInd, TypeBool))
	other := ext.TestConst("normalOther", MakeFun(TypeInd, TypeBool))
	rel := ext.TestConst("normalRelation", MakeFun(TypeInd, TypeInd, TypeBool))
	fn := ext.TestConst("normalFunction", MakeFun(TypeInd, TypeInd))
	gn := ext.TestConst("normalSecond", MakeFun(TypeInd, TypeInd))
	choice := Const(core.MetaHilbert(), MakeFun(MakeFun(TypeInd, TypeBool), TypeInd))

	inputs := []Term{
		holds.Apply(a).Imply(other.Apply(a)),
		holds.Apply(a).Eq(other.Apply(a)),
		Not(ForAll(a)(holds.Apply(a).And(other.Apply(a)))),
		Not(Exists(a)(holds.Apply(a).Imply(Not(other.Apply(a))))),
		ext.Unique(a)(holds.Apply(a)),
		ForAll(a)(Exists(b)(rel.Apply(a, b))).Or(holds.Apply(a)),
		u.To(holds.Apply(fn.Apply(u))).Apply(gn.Apply(a)),
		WrapTerm(fn).Eq(u.To(gn.Apply(u))),
		holds.Apply(ext.Cond(other.Apply(a), fn.Apply(a), fn.Apply(a))),
		holds.Apply(Apply(choice, u.To(u.Eq(fn.Apply(a))))),
		holds.Apply(Apply(choice, other)),
		ForAll(a)(holds.Apply(a).Imply(Exists(b)(rel.Apply(a, b).And(Not(other.Apply(b)))))),
	}
	for _, input := range inputs {
		normal := Rhs(PreCNFNormalizeTerm(input))
		before := map[core.TermName]bool{}
		ext.CollectConstNames(input, before)
		after := map[core.TermName]bool{}
		ext.CollectConstNames(normal, after)
		for name := range after {
			assert.True(t, before[name], "the normal form of %s names %s, which the input does not: %s",
				ext.PrintTerm(input), name, ext.PrintTerm(normal))
		}
	}
}

// TestPreCNFCacheOver pins a cache that stands in front of another: it
// answers as one that stands alone, and a term it does not hold comes
// from the cache behind it where that one holds the term under the same
// spelling, and is computed where it does not.
func TestPreCNFCacheOver(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeInd)
	b := Var("b", TypeInd)
	P := Var("P", MakeFun(TypeInd, TypeBool))
	Q := Var("Q", MakeFun(TypeInd, TypeBool))
	spelledA := ForAll(a)(P.Apply(a).Imply(Q.Apply(a))).Core()
	spelledB := ForAll(b)(P.Apply(b).Imply(Q.Apply(b))).Core()
	require.True(t, spelledA.AlphaEquals(spelledB))
	require.False(t, spelledA.Equals(spelledB))

	t.Run("a term the run holds under the same spelling is read", func(t *testing.T) {
		run := new(PreCNFCache)
		first := NewPreCNFCacheOver(run).NormalizeTerm(spelledA)
		assert.Equal(t, 1, run.TermCacheSize(), "what the front cache computes is kept behind it")
		second := NewPreCNFCacheOver(run).NormalizeTerm(spelledA)
		assert.Same(t, first, second, "the second front cache reads the run's normal form")
	})

	t.Run("a term the run holds under other bound names is computed", func(t *testing.T) {
		run := new(PreCNFCache)
		first := NewPreCNFCacheOver(run).NormalizeTerm(spelledA)
		other := NewPreCNFCacheOver(run).NormalizeTerm(spelledB)
		assert.NotSame(t, first, other)
		assert.True(t, Lhs(other).Equals(spelledB), "the equation is the asked spelling's own")
		alone := new(PreCNFCache).NormalizeTerm(spelledB)
		assert.True(t, Rhs(other).Equals(Rhs(alone)), "and is what a cache that stands alone computes")
		assert.Equal(t, 1, run.TermCacheSize())
	})

	t.Run("one front cache answers an α-equal term as a cache alone does", func(t *testing.T) {
		front := NewPreCNFCacheOver(new(PreCNFCache))
		first := front.NormalizeTerm(spelledA)
		assert.Same(t, first, front.NormalizeTerm(spelledB))
		alone := new(PreCNFCache)
		firstAlone := alone.NormalizeTerm(spelledA)
		assert.Same(t, firstAlone, alone.NormalizeTerm(spelledB))
	})

	t.Run("nothing behind is a cache that stands alone", func(t *testing.T) {
		front := NewPreCNFCacheOver(nil)
		first := front.NormalizeTerm(spelledA)
		assert.Same(t, first, front.NormalizeTerm(spelledA))
		assert.Equal(t, 1, front.TermCacheSize())
	})
}
