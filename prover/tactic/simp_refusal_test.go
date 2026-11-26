package tactic

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"
)

// refusalVars: R a binary relation, G and Q predicates, on the fixture's A.
func refusalVars() (x, y, a, b, R, G, Q *ext.TermWrapper) {
	x = ext.WrapTerm(Var("x", TypeA))
	y = ext.WrapTerm(Var("y", TypeA))
	a = ext.WrapTerm(Var("a", TypeA))
	b = ext.WrapTerm(Var("b", TypeA))
	R = ext.WrapTerm(Var("R", MakeFun(TypeA, MakeFun(TypeA, TypeBool))))
	G = ext.WrapTerm(Var("G", MakeFun(TypeA, TypeBool)))
	Q = ext.WrapTerm(Var("Q", MakeFun(TypeA, TypeBool)))
	return
}

// A law read at a: its right side holds R(y, a), an instance of its left
// side under ∀y, so the driver refuses it. The refusal is named where the
// left side matches, whichever target that is, and nowhere else.
func TestSimpRefusal_NamesTheRuleWhereItsLeftSideMatches(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, y, a, b, R, _, Q := refusalVars()
	rule := testProp(ForAll(x)(R.Apply(x).Apply(a).Eq(ForAll(y)(R.Apply(y).Apply(a).And(Q.Apply(x))))).Core())
	redex := R.Apply(b).Apply(a).Core()

	matching := testProp(redex)
	require.Nil(t, SimpWithExpand(matching, []Prop{rule}))
	note := SimpRefusal(matching, []Prop{rule}, nil, matching.Conclusion())
	assert.Contains(t, note, "Refused as a rewrite")
	assert.Contains(t, note, "R(x, a)")

	apart := testProp(Q.Apply(b).Core())
	require.Nil(t, SimpWithExpand(apart, []Prop{rule}))
	assert.Empty(t, SimpRefusal(apart, []Prop{rule}, nil, apart.Conclusion()))

	atHyp := testProp(Q.Apply(b).Core(), redex)
	assert.Empty(t, SimpRefusal(atHyp, []Prop{rule}, nil, atHyp.Conclusion()))
	assert.NotEmpty(t, SimpRefusal(atHyp, []Prop{rule}, nil, redex))
}

// The same law under a side condition is a conditional rule: it fires at
// the binder-closed redex, which is why a law cited bare works, and there
// is no refusal to name.
func TestSimpRefusal_ConditionalTwinFires(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, y, a, b, R, G, Q := refusalVars()
	c := ext.WrapTerm(Var("c", TypeA))
	rule := testProp(ForAll(c)(G.Apply(c).Imply(ForAll(x)(R.Apply(x).Apply(c).Eq(
		ForAll(y)(R.Apply(y).Apply(c).And(Q.Apply(x))))))).Core())
	goal := testProp(R.Apply(b).Apply(a).Core(), G.Apply(a).Core())

	require.NotNil(t, SimpWithExpand(goal, []Prop{rule}))
	assert.Empty(t, SimpRefusal(goal, []Prop{rule}, nil, goal.Conclusion()))
}

// The refusal of a rule whose self-embedding only unification sees: f(h(x))
// on the right is the left side at x := h(x), and no syntactic subterm of
// the rule says so, so the guard that runs the rule twice is what refuses it.
func TestSimpRefusal_NamesAUnificationSelfEmbedding(t *testing.T) {
	defer goleak.VerifyNone(t)
	x, a, f, g, h, P, _ := simpVars()
	equation := f.Apply(x).Eq(g.Apply(f.Apply(h.Apply(x))))
	rule := testProp(ForAll(x)(equation).Core())

	l, r, ok := prop.MatchesEQ(equation.Core())
	require.True(t, ok)
	bound := x.Core().(core.VarTerm)
	require.False(t, ext.IsSub(ext.ReverseAbsVars(l, bound), ext.ReverseAbsVars(r, bound)),
		"the syntactic gate must pass this rule, or the test measures the wrong gate")

	goal := testProp(P.Apply(f.Apply(a)).Core())
	require.Nil(t, SimpWithExpand(goal, []Prop{rule}))
	assert.NotEmpty(t, SimpRefusal(goal, []Prop{rule}, nil, goal.Conclusion()))
}

// A ground rule takes the structural channel and its own gate, and is
// named on the same terms.
func TestSimpRefusal_NamesAGroundRule(t *testing.T) {
	defer goleak.VerifyNone(t)
	_, _, a, b, _, _, Q := refusalVars()
	h := ext.WrapTerm(Var("h", MakeFun(TypeA, TypeA)))
	rule := testProp(a.Eq(h.Apply(a)).Core())

	matching := testProp(Q.Apply(a).Core())
	require.Nil(t, SimpWithExpand(matching, []Prop{rule}))
	assert.NotEmpty(t, SimpRefusal(matching, []Prop{rule}, nil, matching.Conclusion()))

	apart := testProp(Q.Apply(b).Core())
	assert.Empty(t, SimpRefusal(apart, []Prop{rule}, nil, apart.Conclusion()))
}
