package proof

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// The denote stage's fold (prover/tactic, foldNamed) through the goal
// stack: a leaf naming a function value by a hypothesis spelled as a
// redex, `e = (λx. λj. …)(f)`, and spelling the value reduced in its
// conclusion, `Z = ec(R, λj. …)`, is read with the value folded into e;
// the refuter closes the child from two of its hypotheses, and the
// fold's reconstruction — over the hypotheses the refutation used, not
// the child's whole list — proves the leaf.
func TestDenote_AFoldedNameClosesThroughTheRefuter(t *testing.T) {
	env := makeStepTestEnv()
	M := core.MakeVarType("M")
	edge := core.MakeFun(ext.NumType, M)
	relT := core.MakeFun(edge, core.MakeFun(edge, core.TypeBool()))
	ecT := core.MakeFun(relT, core.MakeFun(edge, core.MakeFun(edge, core.TypeBool())))
	gT := core.MakeFun(M, M)
	setT := core.MakeFun(edge, core.TypeBool())
	consts := map[string]core.HolType{"zz_ec": ecT, "zz_g": gT, "zz_simp": setT, "zz_mor": core.MakeFun(M, core.TypeBool())}
	terms := map[string]core.Term{}
	for name, ty := range consts {
		meta := core.MakeConstMeta(name, ty)
		env.ProofService.LoadOrStoreConstMeta(meta)
		terms[name] = core.MakeConstTerm(meta, ty)
	}
	ec, g, simp, mor := terms["zz_ec"], terms["zz_g"], terms["zz_simp"], terms["zz_mor"]
	f, e := core.Var("f", M), core.Var("e", edge)
	rel := core.Var("R", relT)
	Z := core.Var("Z", setT)
	j := ext.Var("j", ext.NumType)
	zero := ext.WrapTerm(core.Var("zero", ext.NumType))
	valueOf := func(x core.Term) core.Term {
		return j.To(ext.Cond(j.Eq(zero).Core(), x, core.Apply(g, x))).Core()
	}
	x := ext.Var("x", M)
	redex := core.Apply(x.To(ext.WrapTerm(valueOf(x.Core()))).Core(), f)
	goal := prop.MakeProp(core.Eq(Z, ext.Apply(ec, rel, valueOf(f))),
		core.Eq(Z, ext.Apply(ec, rel, e)), core.Eq(e, redex), core.Apply(mor, f), core.Apply(simp, e))
	n := CreateGoalStack(goal)
	require.True(t, n.runStep(_AutoDenote{sizeThreshold: _DENOTE_SIZE_THRES}), "the denote folds the value into its name")
	leaf := n.UnsolvedLeaves()[0]
	require.True(t, leaf.Goal.HasHyp(ext.Not(core.Eq(Z, ext.Apply(ec, rel, e))).Core()), "the negated conclusion spells the name:\n%s", prop.PrintProp(leaf.Goal))
	require.True(t, leaf.runStep(_CNFRefute{env: env, ctx: context.Background()}), "the refuter closes the folded child")
	require.True(t, n.Proved(), "the fold's reconstruction proves the leaf")
}
