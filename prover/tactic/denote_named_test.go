package tactic

import (
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
)

// A λ-abstraction the goal already names, `e = λj. COND(…)`, is denoted
// BY that name: the heuristic's candidate is folded into e wherever else
// it stands, and the naming hypothesis is kept as spelled — also where
// it spells the value as a redex, `e = (λf. λj. …)(a)`, since the
// heuristic reads values β-normal. A first-order named value is left to
// the refuter (and a named partial application to FUNEXT: TestDenoteTactic).
func TestDenote_AValueTheGoalNamesIsFoldedIntoItsName(t *testing.T) {
	M := core.MakeVarType("M")
	edge := MakeFun(dsl.NumType, M)
	relT := MakeFun(edge, MakeFun(edge, core.TypeBool()))
	ecT := MakeFun(relT, MakeFun(edge, MakeFun(edge, core.TypeBool())))
	gT := MakeFun(M, M)
	ec := core.MakeConstTerm(core.MakeConstMeta("zz_named_ec", ecT), ecT)
	g := core.MakeConstTerm(core.MakeConstMeta("zz_named_g", gT), gT)
	a, e := Var("a", M), Var("e", edge)
	rel := Var("R", relT)
	Z := Var("Z", MakeFun(edge, core.TypeBool()))
	j := ext.Var("j", dsl.NumType)
	zero := ext.WrapTerm(core.Var("zero", dsl.NumType))
	valueOf := func(x core.Term) core.Term {
		return j.To(ext.Cond(j.Eq(zero).Core(), x, core.Apply(g, core.Apply(g, core.Apply(g, x))))).Core()
	}
	value := valueOf(a)
	closes := func(t *testing.T, goal Prop, sg *SubGoals) {
		t.Helper()
		require.NotNil(t, sg, "the denote fires on\n%s", prop.PrintProp(goal))
		require.Equal(t, 1, sg.Size())
		child := sg.ChildGoal(0)
		require.True(t, child.HasHyp(Not(core.Eq(Z, ext.Apply(ec, rel, e)))), "the negated conclusion spells the name:\n%s", prop.PrintProp(child))
		require.False(t, child.AnyHyp(func(h core.Term) bool {
			l, r, ok := MatchesEQ(h)
			return ok && !l.Equals(e) && !r.Equals(e) && ext.FindTopSubTerm(h, value.AlphaEquals) != nil
		}), "the value stands nowhere but in its naming:\n%s", prop.PrintProp(child))
		thm := core.TestThm(child.Conclusion(), child.Hyps()...)
		require.True(t, sg.Reconstruct(thm.AsProp()).Conclusion().AlphaEquals(goal.Conclusion()), "the reconstruction proves the goal")
	}

	named := MakeProp(core.Eq(Z, ext.Apply(ec, rel, value)), core.Eq(Z, ext.Apply(ec, rel, e)), core.Eq(e, value))
	closes(t, named, DenoteTactic(8)(named))
	closes(t, named, DenoteTermTactic(value, "e")(named))

	redex := core.Apply(ext.Var("x", M).To(ext.WrapTerm(valueOf(Var("x", M)))).Core(), a)
	spelledAsRedex := MakeProp(core.Eq(Z, ext.Apply(ec, rel, value)), core.Eq(Z, ext.Apply(ec, rel, e)), core.Eq(e, redex))
	sg := DenoteTactic(8)(spelledAsRedex)
	closes(t, spelledAsRedex, sg)
	require.True(t, sg.ChildGoal(0).HasHyp(core.Eq(e, redex)), "the naming hypothesis stands as spelled")

	k := ext.Var("k", dsl.NumType)
	renamed := k.To(ext.Cond(k.Eq(zero).Core(), a, core.Apply(g, core.Apply(g, core.Apply(g, a))))).Core()
	require.False(t, renamed.Equals(value))
	spelledRenamed := MakeProp(core.Eq(Z, ext.Apply(ec, rel, value)), core.Eq(Z, ext.Apply(ec, rel, e)), core.Eq(e, renamed))
	closes(t, spelledRenamed, DenoteTactic(8)(spelledRenamed))

	h := core.MakeConstTerm(core.MakeConstMeta("zz_named_h", gT), gT)
	P := Var("P", MakeFun(M, core.TypeBool()))
	n := Var("n", M)
	deep := core.Term(a)
	for range 7 {
		deep = core.Apply(h, deep)
	}
	firstOrder := MakeProp(core.Apply(P, deep), core.Apply(P, n), core.Eq(n, deep))
	require.Nil(t, DenoteTactic(8)(firstOrder), "a first-order named value is the refuter's")
}
