package proof

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/stretchr/testify/require"
)

// TestByArith_ACloseReadsTheLeafAtItsDefinitions: the arith closer's
// rounds on a leaf: `n = 2 * m` defines n, and `f(n) = h` is an equation
// at a type the deciders do not read. Where no decision settles the
// conclusion — `Q(g(f(2 * m)))`, a predicate no premise names — no firing
// but the leaf's reading is left; it reads `f(n) = h` as `f(2 * m) = h`
// and drops the definition. The close of `g(f(2 * m)) = g(h)` over the
// same premises then goes through, by the arguments of g and f
// (omega argument_congruence.go) or the simplifier between the rounds.
func TestByArith_ACloseReadsTheLeafAtItsDefinitions(t *testing.T) {
	num, A := dsl.NumType, core.MakeVarType("A")
	numVar := func(name string) core.Term { return ext.Var(core.TermName(name), num).Core() }
	times := func(x, y core.Term) core.Term { return ext.Apply(dsl.NatStarMeta.Term(), x, y) }
	n, m := numVar("n"), numVar("m")
	f := ext.Var("f", core.MakeFun(num, A)).Core()
	g := ext.Var("g", core.MakeFun(A, A)).Core()
	h := ext.Var("h", A).Core()
	Q := ext.Var("Q", core.MakeFun(A, core.TypeBool())).Core()
	twoM := times(omega.Numeral(2), m)
	definition, atN := core.Eq(n, twoM), core.Eq(ext.Apply(f, n), h)
	open := prop.MakeProp(ext.Apply(Q, ext.Apply(g, ext.Apply(f, twoM))), atN, definition)
	goal := prop.MakeProp(core.Eq(ext.Apply(g, ext.Apply(f, twoM)), ext.Apply(g, h)), atN, definition)

	sg, fired := tactic.ArithTacticPassingOver(open, omega.UnscopedArithPolicy(), nil, nil)
	require.NotNil(t, sg, "the leaf has its reading to fire")
	read := sg.ChildGoal(0)
	require.True(t, fired.Conclusion && read.HasHyp(core.Eq(ext.Apply(f, twoM), h)) && !read.HasHyp(atN) && !read.HasHyp(definition),
		"the firing reads the leaf at n's definition:\n%s", prop.PrintProp(read))

	step := residentByStep(makeStepTestEnv(), context.Background(), goal)
	step.arith = true
	require.Empty(t, failureOf(step, goal), "the rounds read the leaf and the simplifier closes it")
}
