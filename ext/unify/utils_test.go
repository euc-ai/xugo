package unify

import (
	"slices"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
)

func assertTermEqual(t *testing.T, t0, t1 Term) {
	assert.True(t, t0.Equals(t1))
}

func assertTermAlphaEqual(t *testing.T, t0, t1 Term) {
	assert.True(t, t0.AlphaEquals(t1))
}

func assertTypeSubstEqual(t *testing.T, substs0 []TypeSubst, substs1 ...TypeSubst) {
	assert.Equal(t, len(substs0), len(substs1))
	slices.SortStableFunc(substs1, func(subst0, subst1 TypeSubst) int {
		return subst0.VarType.CompareVar(subst1.VarType)
	})
	if len(substs0) == len(substs1) {
		for i := range substs0 {
			assert.True(t, substs0[i].VarType.Equals(substs1[i].VarType))
			assert.True(t, substs0[i].HolType.Equals(substs1[i].HolType))
		}
	}
}

func assertTermSubstEqual(t *testing.T, subst0 []TermSubst, subst1 ...TermSubst) {
	assert.Equal(t, len(subst0), len(subst1))
	slices.SortStableFunc(subst1, func(subst0, subst1 TermSubst) int {
		return subst0.VarTerm.Compare(subst1.VarTerm)
	})
	if len(subst0) == len(subst1) {
		for i := range subst0 {
			assertTermEqual(t, subst0[i].VarTerm, subst1[i].VarTerm)
			assertTermAlphaEqual(t, subst0[i].Term, subst1[i].Term)
		}
	}
}

func assertTermSubstsGroupEqual(t *testing.T, subst0 []TermSubstsGroup, subst1 ...TermSubstsGroup) {
	assert.Equal(t, len(subst0), len(subst1))
	compare := func(s0, s1 TermSubstsGroup) int {
		slices.SortStableFunc(s0, func(subst0, subst1 TermSubst) int {
			return subst0.VarTerm.Compare(subst1.VarTerm)
		})
		slices.SortStableFunc(s1, func(subst0, subst1 TermSubst) int {
			return subst0.VarTerm.Compare(subst1.VarTerm)
		})
		return slices.CompareFunc(s0, s1, func(e0, e1 TermSubst) int {
			if c := e0.VarTerm.Compare(e1.VarTerm); c != 0 {
				return c
			}
			return e0.Term.Compare(e1.Term)
		})
	}
	assert.True(t, slices.IsSortedFunc(subst0, compare))
	slices.SortStableFunc(subst1, compare)
	if len(subst0) == len(subst1) {
		for i := range subst0 {
			assertTermSubstEqual(t, subst0[i], subst1[i]...)
		}
	}
}

func TestAlignAbsVars(t *testing.T) {
	a := Var("a", TypeBool)
	b := Var("b", TypeBool)
	c := Var("c", TypeBool)
	f := Var("f", MakeFun(TypeBool, TypeBool))
	P := Var("P", MakeFun(TypeBool, TypeBool, TypeBool))

	s0, s1 := alignAbsVars(
		ext.BetaEtaNormalize(t.Context(), f),
		ext.BetaEtaNormalize(t.Context(), P.Apply(a)))
	assertTermEqual(t, s0.(AbsTerm).Var(), s1.(AbsTerm).Var())
	v := s0.(AbsTerm).Var()
	assertTermEqual(t, f.Apply(v), s0.(AbsTerm).Body())
	assertTermEqual(t, P.Apply(a, v), s1.(AbsTerm).Body())

	s0, s1 = alignAbsVars(
		ext.BetaEtaNormalize(t.Context(), a.To(f.Apply(a.Eq(b)))),
		ext.BetaEtaNormalize(t.Context(), c.To(P.Apply(c, a))))
	assertTermEqual(t, s0.(AbsTerm).Var(), s1.(AbsTerm).Var())
	v = s0.(AbsTerm).Var()
	assertTermEqual(t, f.Apply(Eq(v, b)), s0.(AbsTerm).Body())
	assertTermEqual(t, P.Apply(v, a), s1.(AbsTerm).Body())

	s0, s1 = alignAbsVars(
		ext.BetaEtaNormalize(t.Context(), a.To(P.Apply(a, b))),
		ext.BetaEtaNormalize(t.Context(), b.To(P.Apply(b, a))))
	assertTermEqual(t, s0.(AbsTerm).Var(), s1.(AbsTerm).Var())
	v = s0.(AbsTerm).Var()
	assertTermEqual(t, P.Apply(v, b), s0.(AbsTerm).Body())
	assertTermEqual(t, P.Apply(v, a), s1.(AbsTerm).Body())
}

func TestName(t *testing.T) {
	a := Var("a", TypeBool)
	b := Var(utils.Subscript(chooseName("a", a.HasName), 0), TypeBool)
	c := Var(utils.Subscript(chooseName("b", b.HasName), 0), TypeBool)
	assert.EqualValues(t, b.AssertVar().Name(), "b_0")
	assert.EqualValues(t, c.AssertVar().Name(), "c_0")

	a = Var("a_0", TypeBool)
	b = Var(chooseName("a_0", a.HasName), TypeBool)
	c = Var(chooseName("a_1", b.HasName), TypeBool)
	assert.EqualValues(t, b.AssertVar().Name(), "a_1")
	assert.EqualValues(t, c.AssertVar().Name(), "a_2")

	a = Var("aʹ_0", TypeBool)
	b = Var(chooseName("aʹ_0", a.HasName), TypeBool)
	c = Var(chooseName("aʹ_1", b.HasName), TypeBool)
	assert.EqualValues(t, b.AssertVar().Name(), "aʹ_1")
	assert.EqualValues(t, c.AssertVar().Name(), "aʹ_2")

	a = Var("aʹʹ", TypeBool)
	b = Var(chooseName("bʹʹ", a.HasName), TypeBool)
	c = Var(chooseName("cʹʹ", b.HasName), TypeBool)
	assert.EqualValues(t, b.AssertVar().Name(), "bʹʹ")
	assert.EqualValues(t, c.AssertVar().Name(), "cʹʹ")

	a = Var("aʹʹ0", TypeBool)
	b = Var(chooseName("aʹʹ0", a.HasName), TypeBool)
	c = Var(chooseName("aʹʹ1", b.HasName), TypeBool)
	assert.EqualValues(t, b.AssertVar().Name(), "aʹʹ1")
	assert.EqualValues(t, c.AssertVar().Name(), "aʹʹ2")
}
