package proof

import (
	"fmt"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// calcLegChain runs the chain f(a) = f(b) = f(c) from a = b and b = c,
// each leg's proof the rewrite by its equation followed by tail, and
// returns the section.
func calcLegChain(tail ...Action) *GoalStackNode {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	fTy := MakeFun(TypeInd, TypeInd)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("calcLegF", fTy))
	f := ctx.Const("calcLegF", fTy)
	a, b, c := ext.WrapTerm(Var("a", TypeInd)), ext.WrapTerm(Var("b", TypeInd)), ext.WrapTerm(Var("c", TypeInd))
	// a = b ⇒ b = c ⇒ f(a) = f(c)
	sec := ctx.Section(prop.MakeProp(a.Eq(b).Imply(b.Eq(c).Imply(f.Apply(a).Eq(f.Apply(c)))).Core()))
	sec.Do(Derive(func(arg *Argument) {
		first := arg.Assume()
		second := arg.Assume()
		arg.Show("the chain through f(b)", CalcEq(
			Leg(f.Apply(b), "a is b", append([]Action{Simp(Fwd(first))}, tail...)...),
			FinalLeg("b is c", append([]Action{Simp(Fwd(second))}, tail...)...)))
	}))
	return sec
}

// A leg whose rewrite brings its two sides to one term is proved: the
// rewrite leaves `f(b) = f(b)`, which the leg closes.
func TestCalcEq_ALegRewrittenToOneTermIsClosed(t *testing.T) {
	require.True(t, calcLegChain().Proved())
}

// A rewrite after it that folds the equation leaves ⊤, which the leg
// closes as well.
func TestCalcEq_ALegRewrittenToTruthIsClosed(t *testing.T) {
	require.True(t, calcLegChain(CondRewrite()).Proved())
}

// A leg that closes itself is as it was: the closing step finds its leaf.
func TestCalcEq_ALegThatClosesItselfStands(t *testing.T) {
	require.True(t, calcLegChain(Refl()).Proved())
}

// A leg left on a leaf that is neither still fails, naming the leg and
// the leaf.
func TestCalcEq_ALegLeftOpenStillFails(t *testing.T) {
	env := makeStepTestEnv()
	ctx := NewScript(env)
	fTy := MakeFun(TypeInd, TypeInd)
	env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("calcLegG", fTy))
	g := ctx.Const("calcLegG", fTy)
	a, b, c := ext.WrapTerm(Var("a", TypeInd)), ext.WrapTerm(Var("b", TypeInd)), ext.WrapTerm(Var("c", TypeInd))
	sec := ctx.Section(prop.MakeProp(a.Eq(b).Imply(b.Eq(c).Imply(g.Apply(a).Eq(g.Apply(c)))).Core()))
	var failure string
	func() {
		defer func() { failure = fmt.Sprint(recover()) }()
		sec.Do(Derive(func(arg *Argument) {
			first := arg.Assume()
			arg.Assume()
			arg.Show("the chain through g(b)", CalcEq(
				Leg(g.Apply(b), "a is b", Simp(Fwd(first))),
				// The second leg rewrites by the first equation, which
				// leaves g(b) = g(c).
				FinalLeg("b is c", Simp(Fwd(first)))))
		}))
	}()
	require.Contains(t, failure, `leg "b is c"`)
	require.Contains(t, failure, "calcLegG(b) = calcLegG(c)")
}
