package proof

import (
	"sync"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
)

// A choice constant is opened by Unfold like any other definition, with
// or without parameters: c becomes its ε-term, and with the existence
// `∃x. P(x)` resident the tidy closes the opened P(c) — "c is chosen
// among the x with P, and some x has P, so P(c)" is a Have of the
// existence and an Unfold, whichever shape the definition has.

// zz_chosen = εf:(num → num). ∀x:num. f(x) = x — a choice with no
// parameter.
const chosenTestConst = "zz_chosen"

// zz_pick(P) = εx:num. P(x) — a choice under a parameter.
const pickTestConst = "zz_pick"

var chosenTestDef = sync.OnceValue(func() core.ConstTerm {
	numType := ext.NumType
	f := Var("f", core.MakeFun(numType, numType))
	x := Var("x", numType)
	return core.NewConstDef(f.SuchThat(ForAll(x)(f.Apply(x).Eq(x).Core()).Core()).Core(), chosenTestConst)
})

var pickTestDef = sync.OnceValue(func() core.ConstTerm {
	numType := ext.NumType
	P := Var("P", core.MakeFun(numType, core.TypeBool()))
	y := Var("y", numType)
	return core.NewConstDef(P.To(y.SuchThat(P.Apply(y).Core())).Core(), pickTestConst)
})

// The two fixture constants as Unfold takes them.
var (
	chosenTestDefinition = mintedDefinition(chosenTestDef)
	pickTestDefinition   = mintedDefinition(pickTestDef)
)

func choiceTestScript() *Script {
	env := makeStepTestEnv()
	chosen := chosenTestDef()
	env.ProofService.LoadOrStoreConstMeta(chosen.Meta())
	pick := pickTestDef()
	env.ProofService.LoadOrStoreConstMeta(pick.Meta())
	ctx := NewScript(env)
	ctx.Const(chosenTestConst, chosen.Meta().AbsType())
	ctx.Const(pickTestConst, pick.Meta().AbsType())
	return ctx
}

// A choice under a parameter: the existence resident, Unfold closes.
func TestUnfoldChoice_UnderAParameter(t *testing.T) {
	ctx := choiceTestScript()
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("∀P:num → bool. (∃x:num. P(x)) ⇒ P("+pickTestConst+"(P))",
			func(a *Argument, P *ext.Expr[natSet], exists Fact) {
				a.Show("zz_pick(P) is chosen among the x with P", Unfold(pickTestDefinition))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// A choice with no parameter: the same two lines close.
func TestUnfoldChoice_NoParameter(t *testing.T) {
	ctx := choiceTestScript()
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("(∃f:num → num. ∀x:num. f(x) = x) ⇒ ∀x:num. "+chosenTestConst+"(x) = x",
			func(a *Argument, exists Fact) {
				a.Show("zz_chosen is chosen among the maps fixing every point", Unfold(chosenTestDefinition))
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// The session's def_expand records the same step: with the existence
// resident it closes the leaf as Unfold does.
func TestDefExpandChoice_NoParameter(t *testing.T) {
	ctx := choiceTestScript()
	sec := provesInHand(t, func() *GoalStackNode {
		return ctx.Theorem("(∃f:num → num. ∀x:num. f(x) = x) ⇒ ∀x:num. "+chosenTestConst+"(x) = x",
			func(a *Argument, exists Fact) {
				c := unfoldedConstant("TestDefExpandChoice", chosenTestDefinition)
				require.True(t, ApplyDefExpand(a.cur, c), "def_expand opens the choice")
				a.Show("the opened choice closed against the existence")
			})
	})
	require.True(t, sec != nil && sec.Proved())
}

// Without the existence the opened ε-goal stands, as it does for a
// choice under a parameter: proving the existence or denoting the
// ε-term is the author's next line.
func TestUnfoldChoice_NoParameter_WithoutTheExistence(t *testing.T) {
	ctx := choiceTestScript()
	requirePanicContains(t, "did not close the goal (1 unsolved leaf(ves))\n  leaf: ⊢ (εf.∀x.(f(x) = x))(x₀) = x₀", func() {
		ctx.Theorem("∀x:num. "+chosenTestConst+"(x) = x",
			func(a *Argument, x *ext.Expr[ext.Nat]) {
				a.Show("left open on purpose", Unfold(chosenTestDefinition))
			})
	})
}
