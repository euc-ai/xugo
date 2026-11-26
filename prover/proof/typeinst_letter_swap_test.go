package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// TestTypeInst_LetterSwapShiftsNormalForm pins _TypeInstStep's close of
// a type instance that swaps two of the source's letters, σ = {B ↦ D, D
// ↦ B}: Normalize orders a clause's binders and literals by
// type-dependent keys, so the swapped instance normalizes in another
// order than the source, and the attempts that match the normal forms
// modulo that order must find σ although every letter it binds is a
// name the goal spells too.
func TestTypeInst_LetterSwapShiftsNormalForm(t *testing.T) {
	tB, tD := MakeVarType("B"), MakeVarType("D")
	x, y := Var("x", tB), Var("y", tD)
	f, g := Var("f", MakeFun(tB, TypeBool)), Var("g", MakeFun(tD, TypeBool))
	h := Var("h", MakeFun(tB, MakeFun(tD, TypeBool)))
	source := core.TestThm(ForAll(x, y)(f.Apply(x).And(g.Apply(y)).Imply(h.Apply(x).Apply(y))).Core())
	normSource, _ := Normalize(source)
	swap := []core.TypeSubst{core.MakeTypeSubst(tB, tD), core.MakeTypeSubst(tD, tB)}
	instance, _ := Normalize(core.PropTypeInst(source, swap...))
	require.False(t, core.PropTypeInst(normSource, swap...).AlphaEquals(instance),
		"the fixture must reorder under the swap, or it pins nothing")

	n := CreateGoalStack(MakeProp(instance.Conclusion()))
	require.True(t, n.runStep(_TypeInstStep{source: normSource}))
	require.True(t, n.Proved())

	// A clause at the swapped letters missing one of the source's
	// literals is no instance of it.
	xD, fD := Var("x", tD), Var("f", MakeFun(tD, TypeBool))
	yB := Var("y", tB)
	hDB := Var("h", MakeFun(tD, MakeFun(tB, TypeBool)))
	weaker, _ := Normalize(MakeProp(ForAll(xD, yB)(fD.Apply(xD).Imply(hDB.Apply(xD).Apply(yB))).Core()))
	m := CreateGoalStack(MakeProp(weaker.Conclusion()))
	require.False(t, m.runStep(_TypeInstStep{source: normSource}))
}
