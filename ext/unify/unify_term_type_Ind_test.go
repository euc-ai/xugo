package unify

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

// This test suite tests unification with variables of type TypeInd.
// The sister function TestUnifyTermTypeA tests the same cases but with TypeA variables.
// This distinction is important as different types can lead to different unification behaviors
// when interacting with other parts of the term structure.
func TestUnifyTermTypeInd(t *testing.T) {
	defer goleak.VerifyNone(t)

	ground := func(t ...*ext.TermWrapper) TermNamePredicate {
		s := VarList{}
		for _, v := range t {
			s.Add(v.AssertVar())
		}
		return s.HasName
	}
	allGround := utils.FullPredicate[TermName]
	allInstantiable := utils.EmptyPredicate[TermName]

	unifyTerms := func(s, t Term, ground TermNamePredicate) []TermSubstsGroup {
		return UnifyTerms(context.Background(), s, t, ground)
	}

	// Test case: Unify x with x
	// Unifying x with itself where all terms are ground
	// Expected: Empty substitution
	{
		x := Var("x", TypeInd)
		substs := unifyTerms(x, x, allGround)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{})
	}

	// Test case: Unify x with y
	// Unifying x with y where all terms are ground
	// Since x and y are both ground, they cannot be replaced
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		substs := unifyTerms(x, y, allGround)
		assert.Nil(t, substs)
	}

	// Test case: Unify NOT with NOT
	// Unifying NOT with itself where all terms are ground
	// Expected: Empty substitution
	{
		substs := unifyTerms(NOT, NOT, allGround)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{})
	}

	// Test case: Unify x with x
	// Unifying x with itself where all terms are instantiable
	// Expected: Empty substitution
	{
		x := Var("x", TypeInd)
		substs := unifyTerms(x, x, allInstantiable)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{})
	}

	// Test case: Unify x with y
	// Unifying x with y where all terms are instantiable
	// Expected: Substitution x ↦ y
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		substs := unifyTerms(x, y, allInstantiable)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, y)})
	}

	// Test case: Unify x with y
	// Unifying x with y where x is ground and y is instantiable
	// Expected: Substitution y ↦ x
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		substs := unifyTerms(x, y, ground(x))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, x)})
	}

	// Test case: Unify z=y with z=y
	// Unifying z=y with itself where y is ground
	// Expected: Empty substitution
	{
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		substs := unifyTerms(z.Eq(y), z.Eq(y), ground(y))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{})
	}

	// Test case: Unify h(x) with y
	// Unifying h(x) with y where h and y are ground
	// Since h is ground, it cannot be instantiated to yield y
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(h.Apply(x), y, ground(h, y))
		assert.Nil(t, substs)
	}

	// Test case: Unify h(x) with h(h(h(x)))
	// Unifying h(x) with h(h(h(x))) where x is ground
	// Expected: Three possible substitutions:
	// 1. h ↦ λz.z (identity function)
	// 2. h ↦ λz.x (constant function returning x)
	// 3. h ↦ λz.y (constant function returning y)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(h.Apply(x), h.Apply(h.Apply(h.Apply(x))), ground(x))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(h, z.To(z))},
			TermSubstsGroup{MakeTermSubst(h, z.To(x))},
			TermSubstsGroup{MakeTermSubst(h, z.To(y))})
	}

	// Test case: Unify λx.x with λx.x
	// Unifying λx.x with itself where all terms are ground
	// Expected: Empty substitution
	{
		x := Var("x", TypeInd)
		substs := unifyTerms(x.To(x), x.To(x), allGround)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{})
	}

	// Test case: Unify λx.x with λx.y
	// Unifying λx.x with λx.y where all terms are instantiable
	// These terms cannot be unified because x is bound in both terms but refers to
	// different things
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		substs := unifyTerms(x.To(x), x.To(y), allInstantiable)
		assert.Nil(t, substs)
	}

	// Test case: Unify λx.y with λx.x
	// Unifying λx.y with λx.x where all terms are instantiable
	// These terms cannot be unified because x is bound in both terms but refers to
	// different things
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		substs := unifyTerms(x.To(y), x.To(x), allInstantiable)
		assert.Nil(t, substs)
	}

	// Test case: Unify λx.y with λx.y
	// Unifying λx.y with itself where all terms are ground
	// Expected: Empty substitution
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		substs := unifyTerms(x.To(y), x.To(y), allGround)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{})
	}

	// Test case: Unify λx.y with λx.y
	// Unifying λx.y with itself where all terms are instantiable
	// Expected: Empty substitution
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		substs := unifyTerms(x.To(y), x.To(y), allInstantiable)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{})
	}

	// Test case: Unify λx.y with λx.z
	// Unifying λx.y with λx.z where z is ground
	// Expected: Substitution y ↦ z
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		substs := unifyTerms(x.To(y), x.To(z), ground(z))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, z)})
	}

	// Test case: Unify f(x, y) with f(z, w)
	// Unifying f(x, y) with f(z, w) where f is ground
	// Expected: Substitutions x ↦ z, y ↦ w
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		w := Var("w", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms((f.Apply(x, y)), (f.Apply(z, w)), ground(f))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, z),
				MakeTermSubst(y, w)})
	}

	// Test case: Unify f(x, y) with f(z, x)
	// Unifying f(x, y) with f(z, x) where f is ground
	// Expected: Substitutions x ↦ z, y ↦ z
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms((f.Apply(x, y)), (f.Apply(z, x)), ground(f))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, z),
				MakeTermSubst(y, z)})
	}

	// Test case: Unify f(x, y) with f(x, z)
	// Unifying f(x, y) with f(x, z) where f is ground
	// Expected: Substitution y ↦ z
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms((f.Apply(x, y)), (f.Apply(x, z)), ground(f))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, z)})
	}

	// Test case: Unify f(x, x) with f(y, y)
	// Unifying f(x, x) with f(y, y) where f is ground
	// Expected: Substitution x ↦ y
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms((f.Apply(x, x)), (f.Apply(y, y)), ground(f))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, y)})
	}

	// Test case: Unify P(x) with f(x, y)
	// Unifying P(x) with f(x, y) where x and y are ground
	// Expected: Three possible substitutions:
	// 1. P ↦ λx.p, f ↦ λx.λy.p where p is a fresh Boolean variable
	// 2. P ↦ λz.f(x, y)
	// 3. f ↦ λz.λy.P(x)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		P := Var("P", MakeFun(TypeInd, TypeBool))
		substs := unifyTerms(
			P.Apply(x),
			f.Apply(x, y),
			ground(x, y))
		p := Var("z", TypeBool)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(P, x.To(p)),
				MakeTermSubst(f, x.To(y.To(p)))},
			TermSubstsGroup{MakeTermSubst(P, z.To(f.Apply(x, y)))},
			TermSubstsGroup{MakeTermSubst(f, z.To(y.To(P.Apply(x))))})
	}

	// Test case: Unify P(y) with f(x, y)
	// Unifying P(y) with f(x, y) where x and y are ground
	// Expected: Two possible substitutions:
	// 1. P ↦ f(x)
	// 2. f ↦ λx.P
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		P := Var("P", MakeFun(TypeInd, TypeBool))
		substs := unifyTerms(
			P.Apply(y),
			f.Apply(x, y),
			ground(x, y))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(P, f.Apply(x))},
			TermSubstsGroup{MakeTermSubst(f, x.To(P))})
	}

	// Test case: Unify f(x, y) with P(y)
	// Unifying f(x, y) with P(y) where x and y are ground
	// Expected: Two possible substitutions:
	// 1. P ↦ f(x)
	// 2. f ↦ λx.P
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		P := Var("P", MakeFun(TypeInd, TypeBool))
		substs := unifyTerms(
			f.Apply(x, y),
			P.Apply(y),
			ground(x, y))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(P, f.Apply(x))},
			TermSubstsGroup{MakeTermSubst(f, x.To(P))})
	}

	// Test case: Unify λx.f(x, y) with λy.f(y, z)
	// Unifying λx.f(x, y) with λy.f(y, z) where f and z are ground
	// Expected: Substitution y ↦ z
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			x.To(f.Apply(x, y)),
			y.To(f.Apply(y, z)),
			ground(f, z))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, z)})
	}

	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			x.To(f.Apply(x, y)),
			y.To(f.Apply(y, x)),
			ground(f))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, x)})
	}

	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			x.To(f.Apply(x, z)),
			y.To(f.Apply(y, x)),
			ground(f, z))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, z)})
	}

	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			x.To(f.Apply(x, y)),
			y.To(f.Apply(y, x)),
			ground(f))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, x)})
	}

	// Test case: Unify f(y) with f(h(x))
	// Unifying f(y) with f(h(x)) where f, h, and x are ground
	// Expected: Substitution y ↦ h(x)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			f.Apply(y),
			f.Apply(h.Apply(x)),
			ground(f, h, x))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, h.Apply(x))})
	}

	// Test case: Unify f(y) with f(h(x))
	// Unifying f(y) with f(h(x)) where f and h are ground
	// Expected: Substitution y ↦ h(x)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(f.Apply(y), f.Apply(h.Apply(x)), ground(f, h))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, h.Apply(x))})
	}

	{
		x := Var("x", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		Q := Var("Q", MakeFun(MakeFun(TypeInd, TypeInd), TypeInd))
		substs := unifyTerms(Q.Apply(x.To(Q.Apply(g))), x, ground(Q, g))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, Q.Apply(x.To(Q.Apply(g))))})
	}

	// Test case: Unify g(x) with g(y)
	// Unifying g(x) with g(y) where all terms are instantiable
	// Expected: Two possible substitutions:
	// 1. x ↦ y
	// 2. g ↦ λx.p where p is a fresh variable
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(g.Apply(x), g.Apply(y), allInstantiable)
		p := Var("z", TypeInd)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, y)},
			TermSubstsGroup{MakeTermSubst(g, x.To(p))})
	}

	// Test case: Unify λx.g(x) with λy.h(y)
	// Unifying λx.g(x) with λy.h(y) where all terms are instantiable
	// Expected: Substitution g ↦ h
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(x.To(g.Apply(x)), y.To(h.Apply(y)), allInstantiable)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(g, h)})
	}

	// Test case: Unify g(x) with h(y)
	// Unifying g(x) with h(y) where all terms are instantiable
	// Expected: Four possible substitutions:
	// 1. g ↦ h, x ↦ y
	// 2. g ↦ λx.p, h ↦ λx.p where p is a fresh variable
	// 3. g ↦ λx.h(y)
	// 4. h ↦ λy.g(x)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(g.Apply(x), h.Apply(y), allInstantiable)
		p := Var("z", TypeInd)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(g, h),
				MakeTermSubst(x, y)},
			TermSubstsGroup{MakeTermSubst(g, x.To(p)),
				MakeTermSubst(h, x.To(p))},
			TermSubstsGroup{MakeTermSubst(g, x.To(h.Apply(y)))},
			TermSubstsGroup{MakeTermSubst(h, y.To(g.Apply(x)))})
	}

	// Test case: Unify g(x) with h(g(y))
	// Unifying g(x) with h(g(y)) where all terms are instantiable
	// Expected: Four possible substitutions, including g ↦ h, x ↦ g(y)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(g.Apply(x), h.Apply(g.Apply(y)), allInstantiable)
		p := Var("z", TypeInd)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, h.Apply(y)),
				MakeTermSubst(g, h)},
			TermSubstsGroup{MakeTermSubst(g, y.To(x)),
				MakeTermSubst(h, y.To(x))},
			TermSubstsGroup{MakeTermSubst(g, y.To(p)),
				MakeTermSubst(h, y.To(p))},
			TermSubstsGroup{MakeTermSubst(h, y.To(g.Apply(x)))})
	}

	// Test case: Unify g(x) with h(g(x))
	// Unifying g(x) with h(g(x)) where x is ground
	// Expected: Several possible substitutions
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(g.Apply(x), h.Apply(g.Apply(x)), ground(x))
		p := Var("y", TypeInd)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(g, x.To(x)),
				MakeTermSubst(h, x.To(x))},
			TermSubstsGroup{MakeTermSubst(g, z.To(x)),
				MakeTermSubst(h, z.To(x))},
			TermSubstsGroup{MakeTermSubst(g, x.To(p)),
				MakeTermSubst(h, x.To(p))},
			TermSubstsGroup{MakeTermSubst(h, y.To(g.Apply(x)))})
	}

	// Test case: Unify g(y) with g(g(x))
	// Unifying g(y) with g(g(x)) where x is ground
	// Expected: Three possible substitutions:
	// 1. y ↦ g(x)
	// 2. g ↦ λx.y
	// 3. g ↦ λx.p where p is a fresh variable
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(g.Apply(y), g.Apply(g.Apply(x)), ground(x))
		p := Var("z", TypeInd)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, g.Apply(x))},
			TermSubstsGroup{MakeTermSubst(g, x.To(y))},
			TermSubstsGroup{MakeTermSubst(g, x.To(p))})
	}

	// Test case: Unify f(x, y) with P(g(x))
	// Unifying f(x, y) with P(g(x)) where all terms are instantiable
	// Expected: Seven possible substitutions:
	// 1. y ↦ g(x), P ↦ f(x)
	// 2. y ↦ g(x), f ↦ λx.P
	// 3. g ↦ λx.y, P ↦ f(x)
	// 4. g ↦ λx.y, f ↦ λx.P
	// 5. P ↦ λx.p, f ↦ λx.λy.p where p is a fresh Boolean variable
	// 6. P ↦ λz.f(x, y)
	// 7. f ↦ λz.λy.P(g(x))
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		g := Var("g", MakeFun(TypeInd, TypeInd))
		P := Var("P", MakeFun(TypeInd, TypeBool))
		substs := unifyTerms(f.Apply(x, y), P.Apply(g.Apply(x)), allInstantiable)
		p := Var("uʹ", TypeBool)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, g.Apply(x)),
				MakeTermSubst(P, f.Apply(x))},
			TermSubstsGroup{MakeTermSubst(y, g.Apply(x)),
				MakeTermSubst(f, x.To(P))},
			TermSubstsGroup{MakeTermSubst(g, x.To(y)),
				MakeTermSubst(P, f.Apply(x))},
			TermSubstsGroup{MakeTermSubst(g, x.To(y)),
				MakeTermSubst(f, x.To(P))},
			TermSubstsGroup{MakeTermSubst(P, x.To(p)),
				MakeTermSubst(f, x.To(y.To(p)))},
			TermSubstsGroup{MakeTermSubst(P, z.To(f.Apply(x, y)))},
			TermSubstsGroup{MakeTermSubst(f, z.To(y.To(P.Apply(g.Apply(x)))))})
	}

	// Test case: Unify P(g(x)) with f(x, y)
	// Unifying P(g(x)) with f(x, y) where all terms are instantiable
	// Expected: Seven possible substitutions (same as previous test but reversed):
	// 1. y ↦ g(x), P ↦ f(x)
	// 2. y ↦ g(x), f ↦ λx.P
	// 3. g ↦ λx.y, P ↦ f(x)
	// 4. g ↦ λx.y, f ↦ λx.P
	// 5. P ↦ λx.p, f ↦ λx.λy.p where p is a fresh Boolean variable
	// 6. P ↦ λz.f(x, y)
	// 7. f ↦ λz.λy.P(g(x))
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		g := Var("g", MakeFun(TypeInd, TypeInd))
		P := Var("P", MakeFun(TypeInd, TypeBool))
		substs := unifyTerms(P.Apply(g.Apply(x)), f.Apply(x, y), allInstantiable)
		p := Var("z", TypeBool)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, g.Apply(x)),
				MakeTermSubst(P, f.Apply(x))},
			TermSubstsGroup{MakeTermSubst(y, g.Apply(x)),
				MakeTermSubst(f, x.To(P))},
			TermSubstsGroup{MakeTermSubst(g, x.To(y)),
				MakeTermSubst(P, f.Apply(x))},
			TermSubstsGroup{MakeTermSubst(g, x.To(y)),
				MakeTermSubst(f, x.To(P))},
			TermSubstsGroup{MakeTermSubst(P, x.To(p)),
				MakeTermSubst(f, x.To(y.To(p)))},
			TermSubstsGroup{MakeTermSubst(P, z.To(f.Apply(x, y)))},
			TermSubstsGroup{MakeTermSubst(f, z.To(y.To(P.Apply(g.Apply(x)))))})
	}

	// Test case: Unify f(g(x), g(z))=P(x) with f(g(y), w)=P(z)
	// Unifying f(g(x), g(z))=P(x) with f(g(y), w)=P(z) where f, P, y, w are ground
	// Expected: Substitutions x ↦ z, g ↦ λx.w
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		w := Var("w", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		g := Var("g", MakeFun(TypeInd, TypeInd))
		P := Var("P", MakeFun(TypeInd, TypeBool))
		substs := unifyTerms(
			f.Apply(g.Apply(x), g.Apply(z)).Eq(P.Apply(x)),
			f.Apply(g.Apply(y), w).Eq(P.Apply(z)),
			ground(f, P, y, w))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, z),
				MakeTermSubst(g, x.To(w))})
	}

	// Test case: Unify ∃x.f(x, y) with ∃x.f(x, z)
	// Unifying ∃x.f(x, y) with ∃x.f(x, z) where f and x are ground
	// Expected: Substitution y ↦ z
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			Exists(x)(f.Apply(x, y)),
			Exists(x)(f.Apply(x, z)),
			ground(f, x))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, z)})
	}

	// Test case: Unify ∃x.f(x, y) with ∃x.f(x, z)
	// Unifying ∃x.f(x, y) with ∃x.f(x, z) where all terms are ground
	// Since all terms including variables are ground, no substitution is possible
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			Exists(x)(f.Apply(x, y)),
			Exists(x)(f.Apply(x, z)),
			allGround)
		assert.Nil(t, substs)
	}

	// Test case: Unify ∃x.f(x, y) with ∀x.f(x, z)
	// Unifying ∃x.f(x, y) with ∀x.f(x, z) where f and x are ground
	// Since these are different quantifiers (existential vs universal), no valid substitution exists
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			Exists(x)(f.Apply(x, y)),
			ForAll(x)(f.Apply(x, z)),
			ground(f, x))
		assert.Nil(t, substs)
	}

	// Test case: Unify λx.C(x, y) with λy.C(y, x)
	// Unifying λx.C(x, y) with λy.C(y, x) where all terms are instantiable
	// Expected: Substitution y ↦ x
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		C := ext.TestConst("C", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			x.To(C.Apply(x, y)),
			y.To(C.Apply(y, x)),
			allInstantiable)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, x)})
	}

	// Test case: Unify λx.C(x, y) with λy.f(y, x)
	// Unifying λx.C(x, y) with λy.f(y, x) where f is ground
	// Since C is a constant and f is a variable but ground, no valid substitution exists
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		C := ext.TestConst("C", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			x.To(C.Apply(x, y)),
			y.To(f.Apply(y, x)),
			ground(f))
		assert.Nil(t, substs)
	}

	// Test case: Unify λx.C(x, y) with λy.f(y, x)
	// Unifying λx.C(x, y) with λy.f(y, x) where all terms are instantiable
	// Expected: Substitution f ↦ λx.λz.C(x, y)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		C := ext.TestConst("C", MakeFun(TypeInd, TypeInd, TypeBool))
		substs := unifyTerms(
			x.To(C.Apply(x, y)),
			y.To(f.Apply(y, x)),
			allInstantiable)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(f, x.To(z.To(C.Apply(x, y))))})
	}

	// Test case: Unify ∃x.P(g(g(x)))=P(g(z)) with ∃x.P(z)=P(g(y))
	// Unifying ∃x.P(g(g(x)))=P(g(z)) with ∃x.P(z)=P(g(y)) where P and y are ground
	// Expected: Two possible substitutions:
	// 1. g ↦ λx.z
	// 2. z ↦ y, g ↦ λx.y
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		P := Var("P", MakeFun(TypeInd, TypeBool))
		substs := unifyTerms(
			Exists(x)(P.Apply(g.Apply(g.Apply(x)))).Eq(P.Apply(g.Apply(z))),
			Exists(x)(P.Apply(z)).Eq(P.Apply(g.Apply(y))),
			ground(P, y))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(g, x.To(z))},
			TermSubstsGroup{MakeTermSubst(z, y),
				MakeTermSubst(g, x.To(y))})
	}

	// Test case: Unify h(x) with g(g(x))
	// Unifying h(x) with g(g(x)) where g is ground
	// Expected: Substitution h ↦ λz.g(g(x))
	{
		x := Var("x", TypeInd)
		z := Var("z", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			h.Apply(x),
			g.Apply(g.Apply(x)),
			ground(g))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(h, z.To(g.Apply(g.Apply(x))))})
	}

	// Test case: Unify h(g(x))=h(x) with g(g(x))=g(x)
	// Unifying h(g(x))=h(x) with g(g(x))=g(x) where g is ground
	// Expected: Substitution h ↦ g
	{
		x := Var("x", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			h.Apply(g.Apply(x)).Eq(h.Apply(x)),
			g.Apply(g.Apply(x)).Eq(g.Apply(x)),
			ground(g))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(h, g)})
	}

	// Test case: Unify g(h(x)) with g(g(x))
	// Unifying g(h(x)) with g(g(x)) where g is ground
	// Expected: Substitution h ↦ λz.g(x)
	{
		x := Var("x", TypeInd)
		z := Var("z", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			g.Apply(h.Apply(x)),
			g.Apply(g.Apply(x)),
			ground(g))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(h, z.To(g.Apply(x)))})
	}

	// Test case: Unify h(h(x)) with g(g(g(x)))
	// Unifying h(h(x)) with g(g(g(x))) where g is ground
	// Expected: Substitution h ↦ λz.g(g(g(x)))
	{
		x := Var("x", TypeInd)
		z := Var("z", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			h.Apply(h.Apply(x)),
			g.Apply(g.Apply(g.Apply(x))),
			ground(g))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(h, z.To(g.Apply(g.Apply(g.Apply(x)))))})
	}

	// Test case: Unify g(h(x)) with g(g(g(x)))
	// Unifying g(h(x)) with g(g(g(x))) where g is ground
	// Expected: Substitution h ↦ λz.g(g(x))
	{
		x := Var("x", TypeInd)
		z := Var("z", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			g.Apply(h.Apply(x)),
			g.Apply(g.Apply(g.Apply(x))),
			ground(g))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(h, z.To(g.Apply(g.Apply(x))))})
	}

	// Test case: Unify f(h(x), x) with f(y, z)
	// Unifying f(h(x), x) with f(y, z) where f, h, and z are ground
	// This test demonstrates unification with shared variables and function application
	// In the first term, x appears both as an argument to h and directly as second argument to f
	// For these terms to unify:
	//   1. x must be replaced by z (from matching second arguments)
	//   2. y must be replaced by h(z) (from matching first arguments, after x ↦ z)
	// This is a good example of how term structure and variable references are preserved during unification
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			f.Apply(h.Apply(x), x),
			f.Apply(y, z),
			ground(f, h, z))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, z),
				MakeTermSubst(y, h.Apply(z))})
	}

	// Test case: Unify f(x, h(x)) with f(z, y)
	// Unifying f(x, h(x)) with f(z, y) where f, h, and z are ground
	// Expected: Substitutions x ↦ z, y ↦ h(z)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			f.Apply(x, h.Apply(x)),
			f.Apply(z, y),
			ground(f, h, z))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, z),
				MakeTermSubst(y, h.Apply(z))})
	}

	// Test case: Unify x=y with y=z
	// Unifying x=y with y=z where z is ground
	// Expected: Substitutions x ↦ z, y ↦ z
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		substs := unifyTerms(x.Eq(y), y.Eq(z), ground(z))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, z),
				MakeTermSubst(y, z)})
	}

	// Test case: Unify z=y with y=x
	// Unifying z=y with y=x where x is ground
	// Expected: Substitutions y ↦ x, z ↦ x
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		substs := unifyTerms(z.Eq(y), y.Eq(x), ground(x))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, x),
				MakeTermSubst(z, x)})
	}

	// Test case: Unify z=y with y=x
	// Unifying z=y with y=x where z is ground
	// Expected: Substitutions x ↦ z, y ↦ z
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		substs := unifyTerms(z.Eq(y), y.Eq(x), ground(z))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, z),
				MakeTermSubst(y, z)})
	}

	// Test case: Unify x=y with x=z
	// Unifying x=y with x=z where y and z are ground
	// Since y and z are both ground, they cannot be replaced
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		substs := unifyTerms(x.Eq(y), x.Eq(z), ground(y, z))
		assert.Nil(t, substs)
	}

	// Test case: Unify x=y with z=x
	// Unifying x=y with z=x where y and z are ground
	// Since y and z are both ground, they cannot be replaced
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		substs := unifyTerms(x.Eq(y), z.Eq(x), ground(y, z))
		assert.Nil(t, substs)
	}

	// Test case: Unify Q(g)=Q(h) with g(x)=h(x)
	// Unifying Q(g)=Q(h) with g(x)=h(x) where g, h, and x are ground
	// Expected: Substitution Q ↦ λg.g(x)
	{
		x := Var("x", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		Q := Var("Q", MakeFun(MakeFun(TypeInd, TypeInd), TypeInd))
		substs := unifyTerms(
			Q.Apply(g).Eq(Q.Apply(h)),
			g.Apply(x).Eq(h.Apply(x)),
			ground(g, h, x))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(Q, g.To(g.Apply(x)))})
	}

	// Test case: Unify Q(g) with g(x)
	// Unifying Q(g) with g(x) where Q is ground
	// Expected: Substitutions x ↦ Q(λx.x), g ↦ λx.x (identity function)
	{
		x := Var("x", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		Q := Var("Q", MakeFun(MakeFun(TypeInd, TypeInd), TypeInd))
		substs := unifyTerms(Q.Apply(g), g.Apply(x), ground(Q))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, Q.Apply(x.To(x))),
				MakeTermSubst(g, x.To(x))})
	}

	// Test case: Unify x with R(g, h)
	// Unifying x with R(g, h) where R is ground
	// Expected: Substitution x ↦ R(g, h)
	{
		x := Var("x", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		R := Var("R", MakeFun(MakeFun(TypeInd, TypeInd), MakeFun(TypeInd, TypeInd), TypeInd))
		substs := unifyTerms(
			x, R.Apply(g, h),
			ground(R))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, R.Apply(g, h))})
	}

	// Test case: Unify f(x, g(x)) with f(R(g, h), g(R(g, h)))
	// Unifying f(x, g(x)) with f(R(g, h), g(R(g, h))) where R and f are ground
	// Expected substitutions:
	// 1. x ↦ R(g, h)
	// 2. x ↦ R(λz.p, h), g ↦ λz.p where p is a fresh variable
	{
		x := Var("x", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		R := Var("R", MakeFun(MakeFun(TypeInd, TypeInd), MakeFun(TypeInd, TypeInd), TypeInd))
		substs := unifyTerms(
			f.Apply(x, g.Apply(x)),
			f.Apply(R.Apply(g, h), g.Apply(R.Apply(g, h))),
			ground(R, f))
		p := Var("y", TypeInd)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, R.Apply(g, h))},
			TermSubstsGroup{MakeTermSubst(x, R.Apply(z.To(p), h)),
				MakeTermSubst(g, z.To(p))})
	}

	{
		// Test case: Unify P₀(y) with ¬P(h(x.{¬P(h(x))}))
		// Unifying a simple predicate application with a complex nested term involving negation and restricted variables
		// Expected: Four possible substitutions:
		// 1. y ↦ x.{¬P(h(x))}, P₀ ↦ λx.¬P(h(x))
		// 2. h ↦ λx.ħ₀(y), P₀ ↦ λx.¬P(ħ₀(x)) where ħ₀ is a fresh function variable
		// 3. P₀ ↦ λz.¬P(h(x.{¬P(h(x))}))
		{
			x := Var("x", TypeInd)
			y := Var("y", TypeInd)
			z := Var("z", TypeInd)
			h := Var("h", MakeFun(TypeInd, TypeInd))
			h0 := Var("ħ0_0", MakeFun(TypeInd, TypeInd))
			P0 := Var("P_0", MakeFun(TypeInd, TypeBool))
			P := Var("P", MakeFun(TypeInd, TypeBool))

			substs := UnifyTerms(t.Context(),
				P0.Apply(y), Not(P.Apply(h.Apply(x.SuchThat(Not(P.Apply(h.Apply(x))))))),
				ground(P))
			assertTermSubstsGroupEqual(t,
				substs,
				TermSubstsGroup{MakeTermSubst(y, x.SuchThat(Not(P.Apply(h.Apply(x))))),
					MakeTermSubst(P0, x.To(Not(P.Apply(Apply(h, x)))))},
				TermSubstsGroup{MakeTermSubst(h, x.To(z)),
					MakeTermSubst(P0, x.To(Not(P.Apply(z))))},
				TermSubstsGroup{MakeTermSubst(h, x.To(Apply(h0, y))),
					MakeTermSubst(P0, x.To(Not(P.Apply(Apply(h0, x)))))},
				TermSubstsGroup{MakeTermSubst(P0, z.To(Not(P.Apply(h.Apply(x.SuchThat(Not(P.Apply(h.Apply(x)))))))))},
			)
		}
	}

	// Test case: Unify f(x, g0(x)) with f(R(g, h), g(R(g, h)))
	// Unifying f(x, g0(x)) with f(R(g, h), g(R(g, h))) where R, f, and g0 are ground
	// Expected: Substitutions x ↦ R(g0, h), g ↦ g0
	{
		x := Var("x", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		R := Var("R", MakeFun(MakeFun(TypeInd, TypeInd), MakeFun(TypeInd, TypeInd), TypeInd))
		g0 := Var("g0", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			f.Apply(x, g0.Apply(x)),
			f.Apply(R.Apply(g, h), g.Apply(R.Apply(g, h))),
			ground(R, f, g0))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, R.Apply(g0, h)),
				MakeTermSubst(g, g0)})
	}

	// Test case: Unify f(x, g0(x)) with f(R(g, h), g0(R(g, h)))
	// Unifying f(x, g0(x)) with f(R(g, h), g0(R(g, h))) where R, f, and g0 are ground
	// Expected: Substitution x ↦ R(g, h)
	{
		x := Var("x", TypeInd)
		f := Var("f", MakeFun(TypeInd, TypeInd, TypeBool))
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		R := Var("R", MakeFun(MakeFun(TypeInd, TypeInd), MakeFun(TypeInd, TypeInd), TypeInd))
		g0 := Var("g0", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(
			f.Apply(x, g0.Apply(x)),
			f.Apply(R.Apply(g, h), g0.Apply(R.Apply(g, h))),
			ground(R, f, g0))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(x, R.Apply(g, h))})
	}

	// Test case: Unify R(λx.Q(h), h) with Q(g)
	// Unifying R(λx.Q(h), h) with Q(g) where no terms are ground
	// This tests higher-order unification with abstractions as arguments
	// Expected substitutions:
	// 1. g ↦ h, R ↦ λh.Q
	// 2. Q ↦ λh.p, R ↦ λh.λg.p where p is a fresh variable
	// 3. R ↦ λh.λh0.Q(g) where h0 is a fresh function variable
	{
		x := Var("x", TypeInd)
		g := Var("g", MakeFun(TypeInd, TypeInd))
		h := Var("h", MakeFun(TypeInd, TypeInd))
		Q := Var("Q", MakeFun(MakeFun(TypeInd, TypeInd), TypeInd))
		R := Var("R", MakeFun(MakeFun(TypeInd, TypeInd), MakeFun(TypeInd, TypeInd), TypeInd))
		h0 := Var("h0", MakeFun(TypeInd, TypeInd))
		substs := unifyTerms(R.Apply(x.To(Q.Apply(h)), h), Q.Apply(g), ground())
		p := Var("z", TypeInd)
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(g, h),
				MakeTermSubst(R, h.To(Q))},
			TermSubstsGroup{MakeTermSubst(Q, h.To(p)),
				MakeTermSubst(R, h.To(g.To(p)))},
			TermSubstsGroup{MakeTermSubst(R, h.To(h0.To(Q.Apply(g))))})
	}

	// Test case: Unify d(S(d,b))=u ∧ d=b with c(S(a,c))=u ∧ a=c
	// Unifying d(S(d,b))=u ∧ d=b with c(S(a,c))=u ∧ a=c where S is ground
	// This tests unification with conjunction and multiple equality constraints
	// Expected substitutions:
	// 1. a,b,c,d ↦ λx0.x where x is a fresh Boolean variable
	// 2. a,b,c,d ↦ λx0.y where y is a fresh Boolean variable
	// 3. b ↦ a, c ↦ a, d ↦ a
	{
		u := Var("u", TypeB)
		a := Var("a", MakeFun(TypeInd, TypeB))
		b := Var("b", MakeFun(TypeInd, TypeB))
		c := Var("c", MakeFun(TypeInd, TypeB))
		d := Var("d", MakeFun(TypeInd, TypeB))
		S := Var("S", MakeFun(MakeFun(TypeInd, TypeB), MakeFun(TypeInd, TypeB), TypeInd))
		substs := unifyTerms(
			d.Apply(S.Apply(d, b)).Eq(u).And(d.Eq(b)),
			c.Apply(S.Apply(a, c)).Eq(u).And(a.Eq(c)),
			ground(S))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(a, Var("x0", TypeInd).To(Var("x", TypeB))),
				MakeTermSubst(b, Var("x0", TypeInd).To(Var("x", TypeB))),
				MakeTermSubst(c, Var("x0", TypeInd).To(Var("x", TypeB))),
				MakeTermSubst(d, Var("x0", TypeInd).To(Var("x", TypeB)))},
			TermSubstsGroup{MakeTermSubst(a, Var("x0", TypeInd).To(Var("y", TypeB))),
				MakeTermSubst(b, Var("x0", TypeInd).To(Var("y", TypeB))),
				MakeTermSubst(c, Var("x0", TypeInd).To(Var("y", TypeB))),
				MakeTermSubst(d, Var("x0", TypeInd).To(Var("y", TypeB)))},
			TermSubstsGroup{MakeTermSubst(b, a),
				MakeTermSubst(c, a),
				MakeTermSubst(d, a)})
	}

	// Test case: Unify R(x, u.{R(x0, u)}) with R(g0(r), r(g0(r)))
	// Unifying R(x, u.{R(x0, u)}) with R(g0(r), r(g0(r))) where R, g0, and x0 are ground
	// This tests unification with restricted quantification and higher-order terms
	// Expected: Substitutions matching the complex structure with nested terms
	{
		x := Var("x", TypeInd)
		y := Var("y", TypeInd)
		u := Var("u", TypeB)
		r := Var("r", MakeFun(TypeInd, TypeB))
		x0 := WrapTerm(ext.BetaEtaNormalize(t.Context(), r).(AbsTerm).Var())
		R := Var("R", MakeFun(TypeInd, TypeB, TypeBool))
		g0 := Var("g0", MakeFun(MakeFun(TypeInd, TypeB), TypeInd))
		substs := unifyTerms(
			R.Apply(x, u.SuchThat(R.Apply(x0, u))),
			R.Apply(g0.Apply(r), r.Apply(g0.Apply(r))),
			ground(R, g0, x0))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{
				MakeTermSubst(x, ext.EtaCollapse(t.Context(), g0.Apply(y.To(u.SuchThat(R.Apply(x0, u)))))),
				MakeTermSubst(r, ext.EtaCollapse(t.Context(), y.To(u.SuchThat(R.Apply(x0, u)))))})
	}

	{
		x := Var("ẋ_0", TypeInd)
		y := Var("y", TypeInd)
		z := Var("z", TypeInd)
		f := Var("f", MakeFun(MakeFun(TypeInd, TypeBool), TypeInd, TypeInd))
		S := Var("S", MakeFun(TypeInd, TypeInd))

		// Test case: Unify y=S(z) with x=S(f(λz.⊤, x))
		// Unifying y=S(z) with x=S(f(λz.⊤, x)) where S, f, and x are ground
		// This tests unification with function application and equality
		// Expected: Substitutions y ↦ x, z ↦ f(λz.⊤, x)
		substs := unifyTerms(
			y.Eq(S.Apply(z)), x.Eq(S.Apply(f.Apply(z.To(T), x))),
			ground(S, f, x))
		assertTermSubstsGroupEqual(t,
			substs,
			TermSubstsGroup{MakeTermSubst(y, x),
				MakeTermSubst(z, f.Apply(z.To(T), x))})
	}
}
