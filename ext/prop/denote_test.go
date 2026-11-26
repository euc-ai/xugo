package prop

import (
	"fmt"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

func TestDenoteRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	c := Var("c", TypeA)
	d := Var("d", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeBool, TypeBool, TypeBool))

	var x *ext.TermWrapper

	verifyForAllDenote := func(denote, s0, s1 *ext.TermWrapper) {
		assertRewrite(t, ForAllDenoteRewrite(denote), s0, s1)
		// It is possible that after UndenoteRewrite
		// the rhs is differ from the original term
		// by a deep beta, which is ok.
		assertPropAlphaEqual(t,
			ForAllUndenoteRewrite(s1).
				RewriteConclRhs(DeepBeta),
			testThm(s1.Eq(s0)))
	}
	verifyExistsDenote := func(denote, s0, s1 *ext.TermWrapper) {
		assertRewrite(t, ExistsDenoteRewrite(denote), s0, s1)
		// It is possible that after UndenoteRewrite
		// the rhs is differ from the original term
		// by a deep beta, which is ok.
		assertPropAlphaEqual(t,
			ExistsUndenoteRewrite(s1).
				RewriteConclRhs(DeepBeta),
			testThm(s1.Eq(s0)))
	}

	// Test 1: Subterm not present in the term, rewrite should return nil
	// Test expression: Q(b ⇒ P(c), b = P(c))
	// Attempt to rewrite: b ∧ P(c), this subterm is not in the original expression
	s := Q.Apply(b.Imply(P.Apply(c)), b.Eq(P.Apply(c)))
	assert.Nil(t, ForAllDenoteRewrite(b.And(P.Apply(c)))(s))
	assert.Nil(t, ExistsDenoteRewrite(b.And(P.Apply(c)))(s))

	// Test 2: Simple subterm rewrite
	// Test expression: Q(b ⇒ P(c), b = P(c))
	// Rewrite subterm: P(c)
	// forAllDenoteRewrite rewrites expression to ∀x.(x = P(c) ⇒ Q(b ⇒ x, b = x))
	// existsDenoteRewrite rewrites expression to ∃x.(x = P(c) ∧ Q(b ⇒ x, b = x))
	s = Q.Apply(b.Imply(P.Apply(c)), b.Eq(P.Apply(c)))
	x = Var("x", TypeBool)

	verifyForAllDenote(P.Apply(c), s,
		ForAll(x)(
			x.Eq(P.Apply(c)).
				Imply(Q.Apply(b.Imply(x), b.Eq(x)))))
	verifyExistsDenote(P.Apply(c), s,
		Exists(x)(
			x.Eq(P.Apply(c)).
				And(Q.Apply(b.Imply(x), b.Eq(x)))))

	// Test 3: More complex subterm rewrite
	// Test expression: Q(b ⇒ P(c), b ⇒ P(c))
	// Rewrite subterm: b ⇒ P(c)
	// forAllDenoteRewrite rewrites expression to ∀x.(x = (b ⇒ P(c)) ⇒ Q(x, x))
	// existsDenoteRewrite rewrites expression to ∃x.(x = (b ⇒ P(c)) ∧ Q(x, x))
	s = Q.Apply(b.Imply(P.Apply(c)), b.Imply(P.Apply(c)))
	x = Var("x", TypeBool)
	verifyForAllDenote(b.Imply(P.Apply(c)), s,
		ForAll(x)(
			x.Eq(b.Imply(P.Apply(c))).
				Imply(Q.Apply(x, x))))
	verifyExistsDenote(b.Imply(P.Apply(c)), s,
		Exists(x)(
			x.Eq(b.Imply(P.Apply(c))).
				And(Q.Apply(x, x))))

	// Test 4: Quantifier rewrite - Simple attempt
	// Test expression: Q(∀c.(b ⇒ P(c)), P(c))
	// Attempt to rewrite subterm: b ⇒ P(c),
	// direct attempt fails because the subterm is under quantifier
	s = Q.Apply(ForAll(c)(b.Imply(P.Apply(c))), P.Apply(c))
	assert.Nil(t, ForAllDenoteRewrite(b.Imply(P.Apply(c)))(s))

	// Test 5: Abstract subterm rewrite - λ expression
	// Test expression: Q(∀c.(b ⇒ P(c)), P(c))
	// Rewrite subterm: λc.(b ⇒ P(c)), corresponding to the quantifier
	// forAllDenoteRewrite rewrites to ∀x.(x = λc.(b ⇒ P(c)) ⇒ Q(∀c.x(c), P(c)))
	// existsDenoteRewrite rewrites to ∃x.(x = λc.(b ⇒ P(c)) ∧ Q(∀c.x(c), P(c)))
	x = Var("x", MakeFun(TypeA, TypeBool))
	verifyForAllDenote(c.To(b.Imply(P.Apply(c))), s,
		ForAll(x)(
			x.Eq(c.To(b.Imply(P.Apply(c)))).
				Imply(Q.Apply(ForAll(c)(x.Apply(c)), P.Apply(c)))))
	verifyExistsDenote(c.To(b.Imply(P.Apply(c))), s,
		Exists(x)(
			x.Eq(c.To(b.Imply(P.Apply(c)))).
				And(Q.Apply(ForAll(c)(x.Apply(c)), P.Apply(c)))))

	// Test 6: Subterm appears multiple times, using same abstraction replacement
	// Test expression: Q(∀c.(b ⇒ P(c)), b ⇒ P(c))
	// Rewrite subterm: λc.(b ⇒ P(c))
	// forAllDenoteRewrite: ∀x.(x = λc.(b ⇒ P(c)) ⇒ Q(∀c.x(c), x(c)))
	// existsDenoteRewrite: ∃x.(x = λc.(b ⇒ P(c)) ∧ Q(∀c.x(c), x(c)))
	// Note the last parameter x(c), representing function x applied to variable c
	s = Q.Apply(ForAll(c)(b.Imply(P.Apply(c))), b.Imply(P.Apply(c)))
	x = Var("x", MakeFun(TypeA, TypeBool))
	verifyForAllDenote(c.To(b.Imply(P.Apply(c))), s,
		ForAll(x)(
			x.Eq(c.To(b.Imply(P.Apply(c)))).
				Imply(Q.Apply(ForAll(c)(x.Apply(c)), ext.Apply(x, c)))))
	verifyExistsDenote(c.To(b.Imply(P.Apply(c))), s,
		Exists(x)(
			x.Eq(c.To(b.Imply(P.Apply(c)))).
				And(Q.Apply(ForAll(c)(x.Apply(c)), ext.Apply(x, c)))))

	// Test 7: Handling same abstraction in different quantifiers
	// Test expression: Q(∀b.(b ⇒ P(c)), ∃b.(b ⇒ P(c)))
	// Rewrite subterm: λb.(b ⇒ P(c))
	// Rewrites to: ∀x.(x = λb.(b ⇒ P(c)) ⇒ Q(∀b.x(b), ∃b.x(b)))
	// Or: ∃x.(x = λb.(b ⇒ P(c)) ∧ Q(∀b.x(b), ∃b.x(b)))
	s = Q.Apply(ForAll(b)(b.Imply(P.Apply(c))), Exists(b)(b.Imply(P.Apply(c))))
	x = Var("x", MakeFun(TypeBool, TypeBool))
	verifyForAllDenote(b.To(b.Imply(P.Apply(c))), s,
		ForAll(x)(
			x.Eq(b.To(b.Imply(P.Apply(c)))).
				Imply(Q.Apply(ForAll(b)(x.Apply(b)), Exists(b)(x.Apply(b))))))
	verifyExistsDenote(b.To(b.Imply(P.Apply(c))), s,
		Exists(x)(
			x.Eq(b.To(b.Imply(P.Apply(c)))).
				And(Q.Apply(ForAll(b)(x.Apply(b)), Exists(b)(x.Apply(b))))))

	// Test 8: Handling different quantifier variables
	// Test expression: Q(∀b.(b ⇒ P(c)), ∃c.(b ⇒ P(c)))
	// Rewrite subterm: λc.(b ⇒ P(c))
	// Note: First parameter ∀b.(b ⇒ P(c)) remains unchanged
	// because it contains different bound variable
	s = Q.Apply(ForAll(b)(b.Imply(P.Apply(c))), Exists(c)(b.Imply(P.Apply(c))))
	x = Var("x", MakeFun(TypeA, TypeBool))
	verifyForAllDenote(c.To(b.Imply(P.Apply(c))), s,
		ForAll(x)(
			x.Eq(c.To(b.Imply(P.Apply(c)))).
				Imply(Q.Apply(ForAll(b)(b.Imply(P.Apply(c))), Exists(c)(x.Apply(c))))))
	verifyExistsDenote(c.To(b.Imply(P.Apply(c))), s,
		Exists(x)(
			x.Eq(c.To(b.Imply(P.Apply(c)))).
				And(Q.Apply(ForAll(b)(b.Imply(P.Apply(c))), Exists(c)(x.Apply(c))))))

	// Test 9: Subterm rewrite in equations
	// Test expression: Q((P(c) ∧ a) = b, (P(c) ∧ a) = a)
	// Rewrite subterm: P(c) ∧ a
	// Rewrites to: ∀x.(x = (P(c) ∧ a) ⇒ Q(x = b, x = a))
	// Or: ∃x.(x = (P(c) ∧ a) ∧ Q(x = b, x = a))
	s = Q.Apply(P.Apply(c).And(a).Eq(b), P.Apply(c).And(a).Eq(a))
	x = Var("x", TypeBool)
	verifyForAllDenote(P.Apply(c).And(a), s,
		ForAll(x)(
			x.Eq(P.Apply(c).And(a)).
				Imply(Q.Apply(x.Eq(b), x.Eq(a)))))
	verifyExistsDenote(P.Apply(c).And(a), s,
		Exists(x)(
			x.Eq(P.Apply(c).And(a)).
				And(Q.Apply(x.Eq(b), x.Eq(a)))))

	// Test 10: Handling nested quantifiers
	// Test expression: ∀c.(Q(∃a.(Q(a, P(c))), ∃b.(Q(b, P(c)))))
	// Rewrite subterm: λc.(∃a.(Q(a, P(c))))
	// Rewrites to: ∀x.(x = λc.(∃a.(Q(a, P(c)))) ⇒ ∀c.(Q(x(c), x(c))))
	// Or: ∃x.(x = λc.(∃a.(Q(a, P(c)))) ∧ ∀c.(Q(x(c), x(c))))
	s = ForAll(c)(Q.Apply(Exists(a)(Q.Apply(a, P.Apply(c))), Exists(b)(Q.Apply(b, P.Apply(c)))))
	x = Var("x", MakeFun(TypeA, TypeBool))
	verifyForAllDenote(c.To(Exists(a)(Q.Apply(a, P.Apply(c)))), s,
		ForAll(x)(
			x.Eq(c.To(Exists(a)(Q.Apply(a, P.Apply(c))))).
				Imply(ForAll(c)(Q.Apply(x.Apply(c), x.Apply(c))))))
	verifyExistsDenote(c.To(Exists(a)(Q.Apply(a, P.Apply(c)))), s,
		Exists(x)(
			x.Eq(c.To(Exists(a)(Q.Apply(a, P.Apply(c))))).
				And(ForAll(c)(Q.Apply(x.Apply(c), x.Apply(c))))))

	// Test 11: Simple Abs: λa.λb.Q(a, b)
	// Test expression: ∀a,b.(b ⇒ P(c) ∧ Q(a, b))
	// Attempt to rewrite subterm: λa.λb.Q(a, b)
	// This rewrite itself is valid, but it creates essentially
	// redundant denotation.
	s = ForAll(a, b)(b.Imply(P.Apply(c)).And(Q.Apply(a, b)))
	x = Var("x", MakeFun(TypeBool, TypeBool, TypeBool))
	verifyForAllDenote(a.To(b.To(Q.Apply(a, b))), s,
		ForAll(x)(
			x.Eq(a.To(b.To(Q.Apply(a, b)))).
				Imply(ForAll(a, b)(b.Imply(P.Apply(c)).And(x.Apply(a, b))))))
	verifyExistsDenote(a.To(b.To(Q.Apply(a, b))), s,
		Exists(x)(
			x.Eq(a.To(b.To(Q.Apply(a, b)))).
				And(ForAll(a, b)(b.Imply(P.Apply(c)).And(x.Apply(a, b))))))

	// Test 12: Abstract rewrite in complex expressions
	// Test expression: ∀c.(P(c) ∧ a ∧ b) ∨ (P(d) ∧ b)
	// Rewrite subterm: λa.λc.(P(c) ∧ a)
	// Rewrites to: ∀x.(x = λa.λc.(P(c) ∧ a) ⇒ ∀c.(x(a, c) ∧ b) ∨ x(b, d))
	// Or: ∃x.(x = λa.λc.(P(c) ∧ a) ∧ ∀c.(x(a, c) ∧ b) ∨ x(b, d))
	s = ForAll(c)(P.Apply(c).And(a).And(b)).Or(P.Apply(d).And(b))
	x = Var("x", MakeFun(TypeBool, TypeA, TypeBool))
	verifyForAllDenote(a.To(c.To(P.Apply(c).And(a))), s,
		ForAll(x)(
			x.Eq(a.To(c.To(P.Apply(c).And(a)))).
				Imply(ForAll(c)(x.Apply(a, c).And(b)).Or(x.Apply(b, d)))))
	verifyExistsDenote(a.To(c.To(P.Apply(c).And(a))), s,
		Exists(x)(
			x.Eq(a.To(c.To(P.Apply(c).And(a)))).
				And(ForAll(c)(x.Apply(a, c).And(b)).Or(x.Apply(b, d)))))

	// Test 13: Single variable abstraction rewrite
	// Test expression: ∀c.(P(c) ∧ a ∧ b) ∨ (P(d) ∧ b)
	// Rewrite subterm: λc.(P(c) ∧ a)
	// Rewrites to: ∀x.(x = λc.(P(c) ∧ a) ⇒ ∀c.(x(c) ∧ b) ∨ (P(d) ∧ b))
	// Or: ∃x.(x = λc.(P(c) ∧ a) ∧ ∀c.(x(c) ∧ b) ∨ (P(d) ∧ b))
	x = Var("x", MakeFun(TypeA, TypeBool))
	verifyForAllDenote(c.To(P.Apply(c).And(a)), s,
		ForAll(x)(
			x.Eq(c.To(P.Apply(c).And(a))).
				Imply(ForAll(c)(x.Apply(c).And(b)).Or(P.Apply(d).And(b)))))
	verifyExistsDenote(c.To(P.Apply(c).And(a)), s,
		Exists(x)(
			x.Eq(c.To(P.Apply(c).And(a))).
				And(ForAll(c)(x.Apply(c).And(b)).Or(P.Apply(d).And(b)))))

	// Test 14: Multi-variable abstraction and variable binding effects
	// Test expression: ∀a,c.(P(c) ∧ a ∧ b) ∨ (P(d) ∧ a)
	// Rewrite subterm: λa.λc.(P(c) ∧ a)
	// Note the handling of variable a under quantifier constraint
	s = ForAll(a, c)(P.Apply(c).And(a).And(b)).Or(P.Apply(d).And(a))
	x = Var("x", MakeFun(TypeBool, TypeA, TypeBool))
	verifyForAllDenote(a.To(c.To(P.Apply(c).And(a))), s,
		ForAll(x)(
			x.Eq(a.To(c.To(P.Apply(c).And(a)))).
				Imply(ForAll(a, c)(x.Apply(a, c).And(b)).Or(x.Apply(a, d)))))
	verifyExistsDenote(a.To(c.To(P.Apply(c).And(a))), s,
		Exists(x)(
			x.Eq(a.To(c.To(P.Apply(c).And(a)))).
				And(ForAll(a, c)(x.Apply(a, c).And(b)).Or(x.Apply(a, d)))))

	// Test 15: Single variable abstraction in complex expression
	// Test expression: ∀a,c.(P(c) ∧ a ∧ b) ∨ (P(d) ∧ a)
	// Rewrite subterm: λc.(P(c) ∧ a)
	// Note that a is in free variable position, so first quantifier part remains unchanged
	x = Var("x", MakeFun(TypeA, TypeBool))
	verifyForAllDenote(c.To(P.Apply(c).And(a)), s,
		ForAll(x)(
			x.Eq(c.To(P.Apply(c).And(a))).
				Imply(ForAll(a, c)(P.Apply(c).And(a).And(b)).Or(x.Apply(d)))))
	verifyExistsDenote(c.To(P.Apply(c).And(a)), s,
		Exists(x)(
			x.Eq(c.To(P.Apply(c).And(a))).
				And(ForAll(a, c)(P.Apply(c).And(a).And(b)).Or(x.Apply(d)))))

}

// HilbertDenoteAt with a GIVEN name: a name the goal only binds — here
// by the ∀ the ε-term sits under, and by the ε itself — names the
// ε-term, and the binder of that name is renamed apart from it; a name
// free in `avoid` is refused, or declined under optionalName.
func TestHilbertDenoteAtAcceptsANameTheGoalOnlyBinds(t *testing.T) {
	defer goleak.VerifyNone(t)

	R := Var("R", MakeFun(TypeA, TypeBool))
	x := Var("x", TypeA)
	y := Var("y", TypeA)
	chosen := x.SuchThat(R.Apply(x)) // εx. R(x)
	// ∀x. R(x) ⇒ R(εx. R(x))
	goal := ForAll(x)(R.Apply(x).Imply(R.Apply(chosen)))

	simplify, existential, v := HilbertDenoteAt(goal.Core(), chosen.Core(), "x", []Term{goal.Core()}, false)
	assert.Equal(t, TermName("x"), v.Name())
	// x = εx. R(x) ⊢ (∀x. R(x) ⇒ R(εx. R(x))) = (∀y. R(y) ⇒ R(x))
	assertTermAlphaEqual(t, Rhs(simplify), ForAll(y)(R.Apply(y).Imply(R.Apply(x))))
	assert.False(t, Rhs(simplify).AlphaEquals(ForAll(x)(R.Apply(x).Imply(R.Apply(x)))),
		"the ∀ captured the name: %s", ext.PrintTerm(Rhs(simplify)))
	// x = εx. R(x) ⊢ (∃y. R(y)) ⇒ R(x)
	assertTermAlphaEqual(t, existential.Conclusion(), Exists(y)(R.Apply(y)).Imply(R.Apply(x)))

	_, _, declined := HilbertDenoteAt(goal.Core(), chosen.Core(), "y", []Term{goal.Core(), y.Core()}, true)
	assert.True(t, declined.IsZero(), "a name free in avoid declines under optionalName")
	func() {
		defer func() {
			r := recover()
			assert.NotNil(t, r, "a name free in avoid is refused")
			assert.Contains(t, fmt.Sprint(r), "already free in the goal")
		}()
		HilbertDenoteAt(goal.Core(), chosen.Core(), "y", []Term{goal.Core(), y.Core()}, false)
	}()
}

func TestUndenoteRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	c := Var("c", TypeA)
	d := Var("d", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))

	var x, s *ext.TermWrapper

	// ∀x.(x = (P(c) ∧ x))
	// ∃x.(x = (P(c) ∧ x))
	x = Var("x", TypeBool)
	s = ForAll(x)(x.Eq(P.Apply(c).And(x)))
	assert.Nil(t, ForAllUndenoteRewrite(s))
	s = Exists(x)(x.Eq(P.Apply(c).And(x)))
	assert.Nil(t, ExistsUndenoteRewrite(s))

	// ∀x.(x = P(c))
	// ∃x.(x = P(c))
	x = Var("x", TypeBool)
	s = ForAll(x)(x.Eq(P.Apply(c)))
	assert.Nil(t, ForAllUndenoteRewrite(s))
	s = Exists(x)(x.Eq(P.Apply(c)))
	assertRewrite(t, ExistsUndenoteRewrite, s, T)

	// ∀x.((x = c) ⇒ ¬¬(P(x)))
	// ∃x.((x = c) ∧ ¬¬(P(x)))
	x = Var("x", TypeA)
	s = ForAll(x)(x.Eq(c).Imply(Not(Not(P.Apply(x)))))
	assertRewrite(t, ForAllUndenoteRewrite, s, Not(Not(P.Apply(c))))
	s = Exists(x)(x.Eq(c).And(Not(Not(P.Apply(x)))))
	assertRewrite(t, ExistsUndenoteRewrite, s, Not(Not(P.Apply(c))))

	// ∀x.((x = P(c)) ⇒ P(d))
	// ∃x.((x = P(c)) ∧ P(d))
	// the denote variable is not free in the rest
	x = Var("x", TypeBool)
	s = ForAll(x)(x.Eq(P.Apply(c)).Imply(P.Apply(d)))
	assertRewrite(t, ForAllUndenoteRewrite, s, P.Apply(d))
	s = Exists(x)(x.Eq(P.Apply(c)).And(P.Apply(d)))
	assertRewrite(t, ExistsUndenoteRewrite, s, P.Apply(d))

	// ∀c.((c = d) ⇒ ¬(P(c) = P(d)))
	// ∃c.((c = d) ∧ ¬(P(c) = P(d)))
	s = ForAll(c)(c.Eq(d).Imply(Not(P.Apply(c).Eq(P.Apply(d)))))
	assertRewrite(t, ForAllUndenoteRewrite, s, Not(P.Apply(d).Eq(P.Apply(d))))
	s = Exists(c)(c.Eq(d).And(Not(P.Apply(c).Eq(P.Apply(d)))))
	assertRewrite(t, ExistsUndenoteRewrite, s, Not(P.Apply(d).Eq(P.Apply(d))))
}

func TestClauseFactorRewrite(t *testing.T) {
	defer goleak.VerifyNone(t)

	a := Var("a", TypeA)
	b := Var("b", TypeBool)
	c := Var("c", TypeA)
	d := Var("d", TypeA)
	P := Var("P", MakeFun(TypeA, TypeBool))
	Q := Var("Q", MakeFun(TypeBool, TypeBool, TypeBool))
	R := Var("R", MakeFun(TypeA, TypeA))
	x := Var("x", TypeBool)

	verify := func(s0 *ext.TermWrapper, s1 Term) {
		assertRewrite(t, ClauseFactorRewrite, s0, s1)
	}

	s := ForAll(x, c)(
		c.Neq(R.Apply(c)).Or(Q.Apply(b, b)))
	assert.Nil(t, ClauseFactorRewrite(s))

	s = ForAll(x, c)(
		R.Apply(c).Neq(c).Or(Q.Apply(b, b)))
	assert.Nil(t, ClauseFactorRewrite(s))

	s = ForAll(b)(b)
	verify(s, F)

	s = ForAll(x, c)(x.Xor(P.Apply(c)))
	verify(s, F)

	s = ForAll(x, c)(P.Apply(c).Xor(x))
	verify(s, F)

	s = ForAll(x, c)(
		x.Xor(P.Apply(c)).
			Or(Q.Apply(b.Imply(x), b.Eq(x))))
	verify(s, ForAll(c)(Q.Apply(b.Imply(P.Apply(c)), b.Eq(P.Apply(c)))))

	s = ForAll(x, c)(
		x.Xor(P.Apply(c)).
			Or(Not(Not(Q.Apply(b.Imply(x), b.Eq(x))))))
	verify(s, ForAll(c)(Not(Not(Q.Apply(b.Imply(P.Apply(c)), b.Eq(P.Apply(c)))))))

	s = ForAll(c, x)(
		x.Xor(P.Apply(c)).
			Or(Q.Apply(b.Imply(x), b.Eq(x))))
	verify(s, ForAll(c)(Q.Apply(b.Imply(P.Apply(c)), b.Eq(P.Apply(c)))))

	s = ForAll(c, x)(
		P.Apply(c).Xor(x).
			Or(Q.Apply(b.Imply(x), b.Eq(x))))
	verify(s, ForAll(c)(Q.Apply(b.Imply(P.Apply(c)), b.Eq(P.Apply(c)))))

	s = ForAll(c, x)(
		(Q.Apply(b.Imply(x), b.Eq(x))).Or(P.Apply(c).Xor(x)))
	verify(s, ForAll(c)(Q.Apply(b.Imply(P.Apply(c)), b.Eq(P.Apply(c)))))

	s = ForAll(x, c)(
		x.Imply(P.Apply(d)).Or(P.Apply(a).Or(P.Apply(c).Xor(x))))
	verify(s, ForAll(c)(P.Apply(c).Imply(P.Apply(d)).Or(P.Apply(a))))

	s = ForAll(x, d, c)(
		x.Imply(P.Apply(d)).Or(Not(c.Eq(R.Apply(a))).Or(P.Apply(c).Xor(x))))
	verify(s, ForAll(d)(P.Apply(R.Apply(a)).Imply(P.Apply(d))))

	s = ForAll(x)(Not(x))
	verify(s, ext.WrapTerm(F))

	s = ForAll(x, b)(Not(x).Or(Q.Apply(b, b).Eq(x)))
	verify(s, ForAll(b)(Q.Apply(b, b)))

	s = ForAll(x, b)(Q.Apply(b, b).Eq(x).Or(Not(x)))
	verify(s, ForAll(b)(Not(Not(Q.Apply(b, b)))))

	s = ForAll(x, b)(Q.Apply(b, b).Eq(x).Or(x))
	verify(s, ForAll(b)(Not(Q.Apply(b, b))))

	s = ForAll(x)(x.Xor(P.Apply(c)))
	verify(s, ext.WrapTerm(F))

	s = ForAll(x, b)(x.Xor(P.Apply(c)).Or(Q.Apply(b, b).Eq(x)))
	verify(s, ForAll(b)(Q.Apply(b, b).Eq(P.Apply(c))))

	s = ForAll(x, b)(x.Or(Q.Apply(x, b)))
	verify(s, ForAll(b)(Q.Apply(F, b)))

	s = ForAll(b, x)(Not(x).Or(Q.Apply(x, x)))
	verify(s, Q.Apply(T, T))

	s = ForAll(x, b)(x.Eq(Q.Apply(b, b)).Or(Q.Apply(x, x)))
	verify(s, ForAll(b)(Q.Apply(Not(Q.Apply(b, b)), Not(Q.Apply(b, b)))))

	s = ForAll(b, x)(Q.Apply(b, b).Eq(Not(x)).Or(Q.Apply(x, x)))
	verify(s, ForAll(b)(Q.Apply(Q.Apply(b, b), Q.Apply(b, b))))
}

// A denoted λ folds its instance under a binder that shadows an outer one
// when the name after it is an outer binder's too: the instance of
// λi. p(i) ∧ q(i) under the λi of ∀i. ∀j. h(i, j) ∧ g(λi. f(p(i) ∧ q(i))).
// The traversal enters the inner λ under a fresh name; were that name j,
// the next after i, which the environment already holds, the environment
// would hold it twice, the site would be read as under two binders where
// the λ abstracts one, and the instance would be left where it is — so a
// stage that denotes until nothing is left would choose it again.
func TestDenoteRewriteFoldsUnderAShadowingBinder(t *testing.T) {
	defer goleak.VerifyNone(t)

	i := Var("i", TypeA)
	next := Var(utils.NextName(i.Core().(VarTerm).Name()), TypeA)
	p := Var("p", MakeFun(TypeA, TypeBool))
	q := Var("q", MakeFun(TypeA, TypeBool))
	h := Var("h", MakeFun(TypeA, TypeA, TypeBool))
	f := Var("f", MakeFun(TypeBool, TypeInd))
	g := Var("g", MakeFun(MakeFun(TypeA, TypeInd), TypeBool))
	x := Var("x", MakeFun(TypeA, TypeBool))

	instance := p.Apply(i).And(q.Apply(i))
	under := func(outer ...Term) *ext.TermWrapper {
		return ForAll(outer...)(h.Apply(i, next).And(g.Apply(i.To(f.Apply(instance)))))
	}
	folded := func(outer ...Term) *ext.TermWrapper {
		return ForAll(outer...)(h.Apply(i, next).And(g.Apply(i.To(f.Apply(x.Apply(i))))))
	}
	denote := func(s0, s1 *ext.TermWrapper) {
		t.Helper()
		w := DenoteRewrite(x.Core().(VarTerm), i.To(instance))(s0)
		if assert.NotNil(t, w, "the instance under the λ is not folded in %s", ext.PrintTerm(s0)) {
			assertTermAlphaEqual(t, Rhs(w), s1)
		}
	}
	// The λ shadows ∀i and the next name is free: no collision.
	denote(under(i), folded(i))
	// The λ shadows ∀i and the next name is the other binder's.
	denote(under(i, next), folded(i, next))
	denote(under(next, i), folded(next, i))
}
