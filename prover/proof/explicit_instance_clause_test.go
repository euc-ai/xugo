package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/assert"
)

// ExplicitInstanceClause is Script.AtTypes's install form for the
// instance a session names by its stated form: Normalize first, the
// types after. A sequent row folds its hypothesis; a two-variable row
// takes both types; a statement that is no type instance of the source
// panics.

func TestExplicitInstanceClause_IsTheTypedInstallForm(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)

	elem := core.MakeVarType("?83488")
	setT := MakeFun(elem, TypeBool)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("FIN", MakeFun(setT, TypeBool)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("CRD", MakeFun(setT, TypeBool)))
	FIN := ctx.Const("FIN", MakeFun(setT, TypeBool))
	CRD := ctx.Const("CRD", MakeFun(setT, TypeBool))
	s := Var("s", setT)
	row := core.TestThm(CRD.Apply(s), FIN.Apply(s))

	stated := core.PropTypeInst(row, core.MakeTypeSubst(elem, TypeInd))
	clause := ExplicitInstanceClause(row, stated)
	assert.True(t, clause.AlphaEquals(ctx.AtTypes(row, TypeInd)), "the sequent row's clause is AtTypes's install")
	assert.True(t, clause.Proved() || core.IsPromised(clause), "the clause is a theorem, derived from the row")
	assert.False(t, clause.AlphaEquals(stated), "Normalize folded the row's hypothesis")

	tvA, tvB := core.MakeVarType("?11"), core.MakeVarType("?22")
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("gg", MakeFun(tvB, tvA)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("qq", MakeFun(tvA, TypeBool)))
	g := ctx.Const("gg", MakeFun(tvB, tvA))
	q := ctx.Const("qq", MakeFun(tvA, TypeBool))
	b := Var("b", tvB)
	two := core.TestThm(q.Apply(g.Apply(b)))
	at := core.PropTypeInst(two, core.MakeTypeSubst(tvB, TypeBool), core.MakeTypeSubst(tvA, TypeInd))
	assert.True(t, ExplicitInstanceClause(two, at).AlphaEquals(ctx.AtTypes(two, TypeBool, TypeInd)),
		"both type variables are taken, by the instance's own types")
}

func TestExplicitInstanceClause_RefusesANonInstance(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	elem := core.MakeVarType("A")
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("PP", MakeFun(elem, TypeBool)))
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("QQ", MakeFun(elem, TypeBool)))
	P := ctx.Const("PP", MakeFun(elem, TypeBool))
	Q := ctx.Const("QQ", MakeFun(elem, TypeBool))
	x := Var("x", elem)
	row := core.TestThm(P.Apply(x))
	requirePanicContains(t, "is not a type instance of", func() {
		ExplicitInstanceClause(row, core.MakeProp(Q.Apply(x).Core()))
	})
}
