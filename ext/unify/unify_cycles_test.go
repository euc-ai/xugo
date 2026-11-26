package unify

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

// This function tests cases that could potentially lead to infinite loops or
// non-termination in the unification algorithm.
// It specifically checks situations where a variable would need to be
// instantiated with a term containing itself, creating a cyclic dependency.
// These tests are crucial to ensure the algorithm correctly detects and
// rejects cases that would otherwise cause infinite recursion.
func TestCycles(t *testing.T) {
	defer goleak.VerifyNone(t)

	ground := func(t ...*ext.TermWrapper) TermNamePredicate {
		s := VarList{}
		for _, v := range t {
			s.Add(v.AssertVar())
		}
		return s.HasName
	}

	unifyTerms := func(s, t Term, ground TermNamePredicate) []TermSubstsGroup {
		return UnifyTerms(context.Background(), s, t, ground)
	}

	x := Var("x", TypeA)
	f := Var("f", MakeFun(TypeA, TypeA, TypeBool))
	g := Var("g", MakeFun(TypeA, TypeA))
	h := Var("h", MakeFun(TypeA, TypeA))
	Q := Var("Q", MakeFun(MakeFun(TypeA, TypeA), TypeA))

	// Test case: Unify variable with its function application - TypeA version
	// Unifying x with h(x) where h is ground
	// This is the classic "occurs check" problem: x = h(x) has no finite solution
	// Expected: No valid substitution (nil)
	substs := unifyTerms(x, h.Apply(x), ground(h))
	assert.Nil(t, substs)

	// Test case: Unify nested function applications - TypeA version
	// Unifying f(x) with f(h(x)) where f and h are ground
	// This implies x = h(x), which has no finite solution
	// Expected: No valid substitution (nil)
	substs = unifyTerms(f.Apply(x), f.Apply(h.Apply(x)), ground(f, h))
	assert.Nil(t, substs)

	// Test case: Unify higher-order function with recursive application - TypeA version
	// Unifying Q(g) with g(x) where Q and x are ground
	// This would require g to be instantiated with a term containing g itself
	// Expected: No valid substitution (nil)
	substs = unifyTerms(Q.Apply(g), g.Apply(x), ground(Q, x))
	assert.Nil(t, substs)

	// The following tests repeat the same cases but with TypeInd instead of TypeA
	// to ensure the algorithm correctly handles cyclic dependencies with different types
	x = Var("x", TypeInd)
	f = Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
	g = Var("g", MakeFun(TypeInd, TypeInd))
	h = Var("h", MakeFun(TypeInd, TypeInd))
	Q = Var("Q", MakeFun(MakeFun(TypeInd, TypeInd), TypeInd))

	// Test case: Unify variable with its function application - TypeInd version
	// Unifying x with h(x) where h is ground
	// Expected: No valid substitution (nil)
	substs = unifyTerms(x, h.Apply(x), ground(h))
	assert.Nil(t, substs)

	// Test case: Unify nested function applications - TypeInd version
	// Unifying f(x) with f(h(x)) where f and h are ground
	// Expected: No valid substitution (nil)
	substs = unifyTerms(f.Apply(x), f.Apply(h.Apply(x)), ground(f, h))
	assert.Nil(t, substs)

	// Test case: Unify higher-order function with recursive application - TypeInd version
	// Unifying Q(g) with g(x) where Q and x are ground
	// Expected: No valid substitution (nil)
	substs = unifyTerms(Q.Apply(g), g.Apply(x), ground(Q, x))
	assert.Nil(t, substs)

	{
		a := Var("a", TypeInd)
		b := Var("b", TypeInd)
		alpha0 := Var("α₀", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd, TypeBool))
		f0 := Var("f_0", MakeFun(TypeInd, TypeInd, TypeBool))
		a0 := Var("a_0", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeBool))

		//  α₀(g, a₀), ¬α₀(ƒ₀(a), b)
		s0 := alpha0.Apply(g, a0)
		s1 := Not(alpha0.Apply(f0.Apply(a), b))

		substs := UnifyTerms(t.Context(), s0, s1, utils.EmptyPredicate)
		assert.NotNil(t, substs)
	}
	{
		f1 := Var("f₁", MakeFun(TypeInd, TypeInd))
		g := Var("g", MakeFun(TypeInd, TypeBool))
		a := Var("a", TypeInd)

		alpha0 := Var("α₀", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd, TypeBool))
		alpha1 := Var("α₁", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd, TypeInd))
		Suc := ext.TestConst("Suc", MakeFun(TypeInd, TypeInd))
		_0 := ext.TestConst("0", TypeInd)

		s0 := alpha0.Apply(a.To(T), Suc.Apply(f1.Apply(_0)))
		s1 := g.Apply(alpha1.Apply(g, a))

		substs := unifyTerms(s0, s1, utils.EmptyPredicate)
		assert.NotNil(t, substs)
	}
	{

		f := Var("f", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool), TypeInd))
		h0 := Var("h₀", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))
		f1 := Var("f₁", MakeFun(TypeInd, TypeInd))
		a := Var("a", TypeInd)

		alpha0 := Var("α₀", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd, TypeBool))
		Suc := ext.TestConst("Suc", MakeFun(TypeInd, TypeInd))
		_0 := ext.TestConst("0", TypeInd)
		P := ext.TestConst("P", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))

		//α₀(λa.α₀(ħ₀(a), a), Suc(0))
		//α₀(P(a), f(f₁(a), P(a)))
		s0 := alpha0.Apply(a.To(alpha0.Apply(h0.Apply(a), a)), Suc.Apply(_0))
		s1 := alpha0.Apply(P.Apply(a), f.Apply(f1.Apply(a), P.Apply(a)))

		substs := unifyTerms(s0, s1, utils.EmptyPredicate)
		assert.NotNil(t, substs)
	}
	{
		h := Var("h", MakeFun(TypeInd, TypeBool))
		f0 := Var("ƒ₀", MakeFun(TypeInd, TypeInd, TypeBool))
		g := Var("g", MakeFun(TypeInd, TypeBool))
		x := Var("x", TypeInd)
		z1 := Var("ƶ₁", TypeInd)
		alpha0 := Var("α₀", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd, TypeBool))
		_0 := ext.TestConst("0", TypeInd)
		P := ext.TestConst("P", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool)))

		// α₀(h, ẋ)
		s0 := alpha0.Apply(h, x)
		// α₀(λƶ₁.(ƒ₀(a₀) ≠ P(ƶ₁))) = g
		s1 := alpha0.Apply(z1.To(f0.Apply(_0).Neq(P.Apply(z1)))).Eq(g)
		substs := unifyTerms(s0, s1, utils.EmptyPredicate)
		assert.NotNil(t, substs)
	}
}
