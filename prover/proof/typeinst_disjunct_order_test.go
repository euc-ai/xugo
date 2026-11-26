package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// TestTypeInst_DisjunctOrderShiftedByInstance pins _TypeInstStep's close
// of a type instance whose normal form lists the source's literals in
// another order: Normalize sorts a clause's literals, as its ∀-prefix, by
// type-dependent keys, so ∀x:B. ∀y:D. f(x) ∧ g(y) ⇒ h(x)(y) normalizes at
// B := bool with ¬f(x) and ¬g(y) swapped.
func TestTypeInst_DisjunctOrderShiftedByInstance(t *testing.T) {
	tB, tD := MakeVarType("B"), MakeVarType("D")
	x, y := Var("x", tB), Var("y", tD)
	f, g := Var("f", MakeFun(tB, TypeBool)), Var("g", MakeFun(tD, TypeBool))
	h := Var("h", MakeFun(tB, MakeFun(tD, TypeBool)))
	source := core.TestThm(ForAll(x, y)(f.Apply(x).And(g.Apply(y)).Imply(h.Apply(x).Apply(y))).Core())
	normSource, _ := Normalize(source)
	atBool := core.MakeTypeSubst(tB, TypeBool)
	instance, _ := Normalize(core.PropTypeInst(source, atBool))
	require.False(t, core.PropTypeInst(normSource, atBool).AlphaEquals(instance),
		"the fixture must reorder under the instance, or it pins nothing")

	n := CreateGoalStack(MakeProp(instance.Conclusion()))
	require.True(t, n.runStep(_TypeInstStep{source: normSource}))
	require.True(t, n.Proved())

	// A clause missing one of the source's literals is no instance of it.
	xBool, fBool := Var("x", TypeBool), Var("f", MakeFun(TypeBool, TypeBool))
	hBool := Var("h", MakeFun(TypeBool, MakeFun(tD, TypeBool)))
	weaker, _ := Normalize(MakeProp(ForAll(xBool, y)(fBool.Apply(xBool).Imply(hBool.Apply(xBool).Apply(y))).Core()))
	m := CreateGoalStack(MakeProp(weaker.Conclusion()))
	require.False(t, m.runStep(_TypeInstStep{source: normSource}))
}
