package proof

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A hypothesis naming a function value, `e = λj. g(a)`, reaches the
// name where it stands as an argument of an opaque head: the refuter
// extensionalizes the equation to its pointwise clause, which connects
// to applications of e alone, and recovers the equation itself as a
// naming equality (ext/clause, NamingEqSides) for the argument
// occurrence. Without it `Z = ec(R, e) ⊢ Z = ec(R, λj. g(a))` is
// irrefutable in the clause space — the search ends at once, nothing
// found. The set-valued naming, `s = λx. P(x) ∧ Q(x)` under `finite(s)`,
// is the iff-pair form of the same equation.
func TestCnfRefute_NamingEquationReachesAnArgumentOccurrence(t *testing.T) {
	env := makeStepTestEnv()
	M := core.MakeVarType("M")
	edge := core.MakeFun(ext.NumType, M)
	relT := core.MakeFun(edge, core.MakeFun(edge, core.TypeBool()))
	ecT := core.MakeFun(relT, core.MakeFun(edge, core.MakeFun(edge, core.TypeBool())))
	gT := core.MakeFun(M, M)
	ecMeta, gMeta := core.MakeConstMeta("zz_ec", ecT), core.MakeConstMeta("zz_g", gT)
	env.ProofService.LoadOrStoreConstMeta(ecMeta)
	env.ProofService.LoadOrStoreConstMeta(gMeta)
	ec, g := core.MakeConstTerm(ecMeta, ecT), core.MakeConstTerm(gMeta, gT)
	a, e := core.Var("a", M), core.Var("e", edge)
	rel := core.Var("R", relT)
	Z := core.Var("Z", core.MakeFun(edge, core.TypeBool()))
	value := ext.Var("j", ext.NumType).To(ext.WrapTerm(core.Apply(g, a))).Core()
	goal := prop.MakeProp(core.Eq(Z, ext.Apply(ec, rel, value)), core.Eq(Z, ext.Apply(ec, rel, e)), core.Eq(e, value))
	n := CreateGoalStack(goal)
	require.True(t, n.runStep(_CNFRefute{env: env, ctx: context.Background()}), "the function naming closes:\n%s", prop.PrintProp(goal))
	require.True(t, n.Proved())

	setT := core.MakeFun(M, core.TypeBool())
	finT := core.MakeFun(setT, core.TypeBool())
	finMeta := core.MakeConstMeta("zz_fin", finT)
	env.ProofService.LoadOrStoreConstMeta(finMeta)
	fin := core.MakeConstTerm(finMeta, finT)
	P, Q := core.Var("P", setT), core.Var("Q", setT)
	s := core.Var("s", setT)
	x := ext.Var("x", M)
	set := x.To(ext.WrapTerm(core.Apply(P, x.Core())).And(ext.WrapTerm(core.Apply(Q, x.Core())))).Core()
	setGoal := prop.MakeProp(core.Apply(fin, set), core.Apply(fin, s), core.Eq(s, set))
	n2 := CreateGoalStack(setGoal)
	require.True(t, n2.runStep(_CNFRefute{env: env, ctx: context.Background()}), "the set naming closes:\n%s", prop.PrintProp(setGoal))
	require.True(t, n2.Proved())
}
