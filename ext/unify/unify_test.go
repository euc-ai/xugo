package unify

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"go.uber.org/goleak"
)

func TestUnify(t *testing.T) {
	// This function tests the core unification algorithm with various type constraints.
	// It focuses specifically on higher-order unification with type substitutions,
	// demonstrating how the algorithm handles terms with different types.
	defer goleak.VerifyNone(t)

	allowedTypes := func(t ...core.TypeName) VarTypePredicate {
		if len(t) == 0 {
			return utils.FullPredicate
		}
		return func(v VarType) bool {
			return utils.Any(t, func(s core.TypeName) bool { return v.Name() == s })
		}
	}

	ground := func(t ...*ext.TermWrapper) TermNamePredicate {
		s := VarList{}
		for _, v := range t {
			s.Add(v.AssertVar())
		}
		return s.HasName
	}
	allInstantiable := utils.EmptyPredicate[TermName]

	typeSubst := func(t *ext.TermWrapper, substs SubstsTuple) *ext.TermWrapper {
		return WrapTerm(t.TypeSubstitute(substs.TypeSubsts...))
	}

	unify := func(s, t Term,
		instantiableTypes VarTypePredicate, ground TermNamePredicate) []SubstsTuple {
		return Unify(context.Background(), s, t, instantiableTypes, ground)
	}

	// Test case: Unify variables of different types with all types instantiable
	// Unifying x:TypeA with y:TypeInd where all types can be substituted
	// Tests basic cross-type unification
	// Expected: Valid substitution
	{
		x := Var("x", TypeA)
		y := Var("y", TypeInd)
		substs := unify(x, y, allowedTypes(), allInstantiable)
		assert.NotNil(t, substs)
	}

	// Test case: Unify variables of different types with type constraints
	// Unifying x:TypeA with y:TypeInd where only TypeB variables can be instantiated
	// Since neither TypeA nor TypeInd can be replaced, unification fails
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeA)
		y := Var("y", TypeInd)
		substs := unify(x, y, allowedTypes("B"), allInstantiable)
		assert.Nil(t, substs)
	}

	// Test case: Unify variables of different types
	// Unifying x:TypeA with w:TypeB where all types can be substituted
	// Expected: Valid substitution
	{
		x := Var("x", TypeA)
		w := Var("w", TypeB)
		substs := unify(x, w, allowedTypes(), allInstantiable)
		assert.NotNil(t, substs)
	}

	// Test case: Unify variables of different types with limited type instantiation
	// Unifying x:TypeA with w:TypeB where only TypeB can be instantiated
	// Expected: Substitution TypeB ↦ TypeA and x unified with the type-substituted w
	{
		x := Var("x", TypeA)
		w := Var("w", TypeB)
		substs := unify(x, w, allowedTypes("B"), allInstantiable)
		assert.NotNil(t, substs)
		assertTypeSubstEqual(t, substs[0].TypeSubsts, MakeTypeSubst(TypeB, TypeA))
		assertTermSubstEqual(t, substs[0].TermSubsts, MakeTermSubst(x, typeSubst(w, substs[0])))
	}

	// Test case: Unify terms with completely different types
	// Unifying x:TypeA with z:TypeBool where all types can be instantiated
	// Expected: Substitution TypeA ↦ TypeBool and the type-substituted x unified with z
	{
		x := Var("x", TypeA)
		z := Var("z", TypeBool)
		substs := unify(x, z, allowedTypes(), allInstantiable)
		assert.NotNil(t, substs)
		assertTypeSubstEqual(t, substs[0].TypeSubsts, MakeTypeSubst(TypeA, TypeBool))
		assertTermSubstEqual(t, substs[0].TermSubsts, MakeTermSubst(typeSubst(x, substs[0]), z))
	}

	// Test case: Unify terms of incompatible types
	// Unifying y:TypeInd with z:TypeBool where all types can be instantiated
	// Since TypeInd and TypeBool are both concrete types, they cannot be unified
	// Expected: No valid substitution (nil)
	{
		y := Var("y", TypeInd)
		z := Var("z", TypeBool)
		substs := unify(y, z, allowedTypes(), allInstantiable)
		assert.Nil(t, substs)
	}

	// Test case: Unify equality expressions with different base types
	// Unifying x=x with y=y where x:TypeA and y:TypeInd, all types instantiable
	// Expected: Substitution TypeA ↦ TypeInd and terms unified accordingly
	{
		x := Var("x", TypeA)
		y := Var("y", TypeInd)
		substs := unify(x.Eq(x), y.Eq(y), allowedTypes(), allInstantiable)
		assert.NotNil(t, substs)
		assertTypeSubstEqual(t, substs[0].TypeSubsts, MakeTypeSubst(TypeA, TypeInd))
		assertTermSubstEqual(t, substs[0].TermSubsts, MakeTermSubst(typeSubst(x, substs[0]), y))
	}

	// Test case: Unify complex expressions with type substitutions
	// Unifying λw.x[f(x,w)]=λw.x with the same expression after type substitution
	// (replacing TypeA with TypeBool)
	// Tests that unification works correctly with type substitutions on identical terms
	// Expected: Substitution TypeA ↦ TypeBool, with no term substitutions
	{
		x := Var("x", TypeA)
		w := Var("w", TypeB)
		f := Var("f", MakeFun(TypeA, TypeB, TypeBool))
		substs := unify(w.To(x.SuchThat(f.Apply(x, w))).Eq(w.To(x)),
			w.To(x.SuchThat(f.Apply(x, w))).Eq(w.To(x)).TypeSubstitute(
				MakeTypeSubst(TypeA, TypeBool)),
			utils.FullPredicate, utils.FullPredicate)
		assert.NotNil(t, substs)
		assertTypeSubstEqual(t, substs[0].TypeSubsts,
			MakeTypeSubst(TypeA, TypeBool))
		assert.Empty(t, substs[0].TermSubsts)
	}

	// Test case: Unify complex expressions with multiple type substitutions
	// Similar to the previous test but with two type substitutions:
	// TypeA ↦ TypeBool and TypeB ↦ TypeBool
	// Expected: Both type substitutions and no term substitutions
	{
		x := Var("x", TypeA)
		w := Var("w", TypeB)
		f := Var("f", MakeFun(TypeA, TypeB, TypeBool))
		substs := unify(w.To(x.SuchThat(f.Apply(x, w))).Eq(w.To(x)),
			w.To(x.SuchThat(f.Apply(x, w))).Eq(w.To(x)).TypeSubstitute(
				MakeTypeSubst(TypeA, TypeBool),
				MakeTypeSubst(TypeB, TypeBool)),
			utils.FullPredicate, utils.FullPredicate)
		assert.NotNil(t, substs)
		assertTypeSubstEqual(t, substs[0].TypeSubsts,
			MakeTypeSubst(TypeA, TypeBool),
			MakeTypeSubst(TypeB, TypeBool))
		assert.Empty(t, substs[0].TermSubsts)
	}

	// Test case: Unify function application with a variable
	// Unifying h(x) with y where h and y are ground
	// Since h is ground, it cannot be instantiated to yield y
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeA)
		y := Var("y", TypeInd)
		h := Var("h", MakeFun(TypeA, TypeA))
		substs := unify(h.Apply(x), y, allowedTypes(), ground(h, y))
		assert.Nil(t, substs)
	}

	// Test case: Unify lambda abstractions with different bodies
	// Unifying λx.x with λx.y where all terms are instantiable
	// Since x is bound in both terms but refers to different things, unification fails
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeA)
		y := Var("y", TypeInd)
		substs := unify(x.To(x), x.To(y), allowedTypes(), allInstantiable)
		assert.Nil(t, substs)
	}

	// Test case: Unify lambda abstractions with the same structure but different variable types
	// Unifying λx.x (where x:TypeA) with λy.y (where y:TypeInd), all types instantiable
	// Expected: Substitution TypeA ↦ TypeInd, with no term substitutions
	{
		x := Var("x", TypeA)
		y := Var("y", TypeInd)
		substs := unify(x.To(x), y.To(y), allowedTypes(), allInstantiable)
		assert.NotNil(t, substs)
		assertTypeSubstEqual(t, substs[0].TypeSubsts, MakeTypeSubst(TypeA, TypeInd))
		assert.Empty(t, substs[0].TermSubsts)
	}

	// Test case: Unify lambda abstractions with restricted type instantiation
	// Unifying λx.x with λy.y where only TypeB can be instantiated
	// Since TypeA and TypeInd cannot be unified with this restriction, unification fails
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeA)
		y := Var("y", TypeInd)
		substs := unify(x.To(x), y.To(y), allowedTypes("B"), allInstantiable)
		assert.Nil(t, substs)
	}

	// Test case: Unify lambda terms with different variable types and ground constraints
	// Unifying λx.y with λx.z where z is ground
	// Since y and z have different types and z is ground, unification fails
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeA)
		y := Var("y", TypeInd)
		z := Var("z", TypeBool)
		substs := unify(x.To(y), x.To(z), allowedTypes(), ground(z))
		assert.Nil(t, substs)
	}

	// Test case: Unify lambda terms with different but compatible types
	// Unifying λx.w (where w:TypeB) with λx.z (where z:TypeBool) where z is ground
	// Expected: Substitution TypeB ↦ TypeBool and appropriately unified terms
	{
		x := Var("x", TypeA)
		z := Var("z", TypeBool)
		w := Var("w", TypeB)
		substs := unify(x.To(w), x.To(z), allowedTypes(), ground(z))
		assert.NotNil(t, substs)
		assertTypeSubstEqual(t, substs[0].TypeSubsts, MakeTypeSubst(TypeB, TypeBool))
		assertTermSubstEqual(t, substs[0].TermSubsts,
			MakeTermSubst(typeSubst(w, substs[0]), z))
	}

	// Test case: Unify higher-order function application with function application
	// Unifying Q(g) with g(w) where Q is ground
	// This is a complex higher-order unification case
	// Expected: Type substitution TypeB ↦ TypeA and appropriate term substitutions
	{
		x := Var("x", TypeA)
		w := Var("w", TypeB)
		g := Var("g", MakeFun(TypeB, TypeA))
		Q := Var("Q", MakeFun(MakeFun(TypeB, TypeA), TypeA))
		substs := unify(Q.Apply(g), g.Apply(w), allowedTypes(), ground(Q))
		assert.NotNil(t, substs)
		assertTypeSubstEqual(t, substs[0].TypeSubsts, MakeTypeSubst(TypeB, TypeA))
		assertTermSubstEqual(t, substs[0].TermSubsts,
			MakeTermSubst(typeSubst(w, substs[0]), typeSubst(Q, substs[0]).Apply(x.To(x))),
			MakeTermSubst(typeSubst(g, substs[0]), x.To(x)))
	}

	// Test case: Unify lambda with constant and function application
	// Unifying λx.C(x,x) with λw.f(x,w) where all terms are instantiable
	// Expected: Type substitution TypeA ↦ TypeB and appropriate term substitutions
	{
		x := Var("x", TypeA)
		w := Var("w", TypeB)
		f := Var("f", MakeFun(TypeA, TypeB, TypeBool))
		C := ext.TestConst("C", MakeFun(TypeA, TypeA, TypeBool))
		substs := unify(
			x.To(C.Apply(x, x)),
			w.To(f.Apply(x, w)),
			allowedTypes(), allInstantiable)
		assert.NotNil(t, substs)
		assertTypeSubstEqual(t, substs[0].TypeSubsts, MakeTypeSubst(TypeA, TypeB))
		assertTermSubstEqual(t, substs[0].TermSubsts,
			MakeTermSubst(
				typeSubst(f, substs[0]),
				typeSubst(x, substs[0]).To(w.To(typeSubst(C, substs[0]).Apply(w, w)))))
	}

	// Test case: Unify variable with its own function application
	// Unifying x with h(x) where h is ground
	// This creates a cyclic dependency which cannot be resolved
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeA)
		h := Var("h", MakeFun(TypeA, TypeA))
		substs := unify(x, h.Apply(x), allowedTypes(), ground(h))
		assert.Nil(t, substs)
	}

	// Test case: Unify nested function applications
	// Unifying f(x) with f(h(x)) where f and h are ground
	// This also creates a cyclic dependency
	// Expected: No valid substitution (nil)
	{
		x := Var("x", TypeA)
		f := Var("f", MakeFun(TypeA, TypeB, TypeBool))
		h := Var("h", MakeFun(TypeA, TypeA))
		substs := unify(f.Apply(x), f.Apply(h.Apply(x)), allowedTypes(), ground(f, h))
		assert.Nil(t, substs)
	}

	// Test case: Unify higher-order function with its own application
	// Unifying Q(g) with g(w) where Q and w are ground
	// This creates a cyclic dependency that cannot be resolved
	// Expected: No valid substitution (nil)
	{
		w := Var("w", TypeB)
		g := Var("g", MakeFun(TypeB, TypeA))
		Q := Var("Q", MakeFun(MakeFun(TypeB, TypeA), TypeA))
		substs := unify(Q.Apply(g), g.Apply(w), allowedTypes(), ground(Q, w))
		assert.Nil(t, substs)
	}

	{
		// Regression for a19a6e23: Miller's RHS-meta fast path is sound for
		// an isolated pattern pair, but must not be the only branch when that
		// RHS meta-variable is constrained by another pending pair. This
		// clause-resolution shape needs the Huet fallback branch that solves
		// x := f0(h) and h := λu.choice(u), without instantiating ground f0.
		R := Var("R", MakeFun(TypeA, TypeB, TypeBool))
		f0 := Var("f_0", MakeFun(MakeFun(TypeA, TypeB), TypeA))
		x0 := Var("x_0", TypeA)
		y0 := Var("y_0", TypeB)
		g := Var("g", MakeFun(TypeA, TypeB))
		h := Var("h", MakeFun(TypeA, TypeB))
		x := Var("x", TypeA)
		a := Var("a", TypeB)

		lhs := R.Apply(f0.Apply(h), h.Apply(f0.Apply(h)))
		rhs := R.Apply(x, a.SuchThat(x.Eq(x0).Imply(a.Eq(y0)).
			And(x.Neq(x0).Imply(a.Eq(g.Apply(x))))))

		substs := unify(lhs, rhs, utils.EmptyPredicate, ground(R, f0, x0, y0, g))
		assert.NotNil(t, substs)

		foundClauseRefuteSubst := false
		for _, subst := range substs {
			assert.True(t,
				ext.BetaEtaEquals(
					t.Context(),
					lhs.Substitute(subst.TermSubsts...),
					rhs.Substitute(subst.TermSubsts...)),
				"unifier returned a substitution that does not unify the original terms")

			hasX, hasH := false, false
			for _, termSubst := range subst.TermSubsts {
				assert.False(t,
					ground(R, f0, x0, y0, g)(termSubst.VarTerm.Name()),
					"unifier instantiated ground variable %s",
					ext.PrintTerm(termSubst.VarTerm))
				hasX = hasX || termSubst.VarTerm.Equals(x.AssertVar())
				hasH = hasH || termSubst.VarTerm.Equals(h.AssertVar())
			}
			foundClauseRefuteSubst = foundClauseRefuteSubst || (hasX && hasH)
		}
		assert.True(t, foundClauseRefuteSubst)
	}

	{

		//	set_member(z, \y. r(y))  =~  set_member(y, alpha(m, n))
		//
		// where alpha is a variable term but is marked ground, while z, y, r,
		// m, n are instantiable meta-variables. A Huet projection/imitation branch
		// can synthesize helper-dependent bindings such as
		// r := \w. alpha(h0(w), h1(w), w), m := h0(y), n := h1(y), z := y,
		// which do not actually unify the original terms.

		in := ext.TestConst("set_member", MakeFun(TypeInd, MakeFun(TypeInd, TypeBool), TypeBool))
		alpha := Var("alpha", MakeFun(TypeInd, TypeInd, TypeInd, TypeBool))

		z := Var("z", TypeInd)
		y := Var("y", TypeInd)
		r := Var("r", MakeFun(TypeInd, TypeBool))
		m := Var("m", TypeInd)
		n := Var("n", TypeInd)

		lhs := in.Apply(z, y.To(r.Apply(y)))
		rhs := in.Apply(y, alpha.Apply(m, n))

		ground := VarList{}
		ground.Add(alpha.AssertVar())
		ground.Add(y.AssertVar())

		substs := unify(lhs, rhs, utils.EmptyPredicate, ground.HasName)
		assert.NotNil(t, substs)

		for _, subst := range substs {
			assert.True(t,
				ext.BetaEtaEquals(
					t.Context(),
					lhs.Substitute(subst.TermSubsts...),
					rhs.Substitute(subst.TermSubsts...)),
				"unifier returned a substitution that does not unify the original terms")
		}

	}
}
