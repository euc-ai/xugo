package emit

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"go.uber.org/goleak"
	"google.golang.org/protobuf/types/known/emptypb"
)

// condRewriteSection is a member whose first step leaves goal, with a
// recorded `cond_rewrite` on goal whose residual a `basic` step takes;
// refuted says whether that `basic` leaves a residual of its own,
// closed by a refute, or closes the goal.
func condRewriteSection(goal core.Prop, refuted bool) *proof.DetailedProofProto {
	pb := ext.NewPoolBuilder()
	residual := pb.PropRef(prop.MakeProp(ext.Var("R", core.TypeBool()).Core()))
	rewritten := pb.PropRef(goal)
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(prop.MakeProp(ext.Var("G", core.TypeBool()).Core())),
			SubGoals: []*ext.HolPropProto{rewritten},
			Step:     &proof.StepProto_TrivialSimplify{TrivialSimplify: &emptypb.Empty{}},
		},
		{
			Goal:     rewritten,
			SubGoals: []*ext.HolPropProto{residual},
			Step:     &proof.StepProto_CondRewrite{CondRewrite: &emptypb.Empty{}},
		},
		{Goal: residual, Step: &proof.StepProto_Basic{Basic: &emptypb.Empty{}}},
	}
	if refuted {
		left := pb.PropRef(prop.MakeProp(ext.Var("S", core.TypeBool()).Core()))
		steps[2].SubGoals = []*ext.HolPropProto{left}
		steps = append(steps, &proof.StepProto{Goal: left, Step: &proof.StepProto_CnfRefute{CnfRefute: &emptypb.Empty{}}})
	}
	return detailed(pb, steps...)
}

// TestEmit_CondRewriteWithNoCondIsLeftToBasic: a recorded `cond_rewrite`
// whose goal holds no COND, whose residual a `basic` leaf closes and
// which Basic closes as it stands — the reflexive equation a rewrite
// left — renders as that `Basic()` alone. With a COND in the goal the
// step is the elimination it names and stays; it stays where the
// `basic` leaves a residual, the rule being for the closing leaf; and
// it stays on a goal Basic does not close by itself, where dropping it
// would hand the replay a line that does not close.
func TestEmit_CondRewriteWithNoCondIsLeftToBasic(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)

	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	c := ext.Var("c", core.TypeBool())
	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	plain := prop.MakeProp(core.Eq(P.Apply(x).Core(), P.Apply(x).Core()))
	open := prop.MakeProp(P.Apply(x).Core())
	withCond := prop.MakeProp(P.Apply(ext.Cond(c, x, y)).Core())

	src := emitMember(t, env, EmitOptions{FuncName: "BuildNoCond"}, condRewriteSection(plain, false)).Source
	if strings.Contains(src, "CondRewrite()") {
		t.Errorf("a cond_rewrite on a goal with no COND is rendered\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "Basic(),") {
		t.Errorf("the closing Basic() is not rendered\n--- source: ---\n%s", src)
	}

	src = emitMember(t, env, EmitOptions{FuncName: "BuildCond"}, condRewriteSection(withCond, false)).Source
	if !strings.Contains(src, "CondRewrite(),") || !strings.Contains(src, "Basic(),") {
		t.Errorf("a cond_rewrite on a goal with a COND must stay, before its Basic()\n--- source: ---\n%s", src)
	}

	src = emitMember(t, env, EmitOptions{FuncName: "BuildNoCondRefuted"}, condRewriteSection(plain, true)).Source
	if !strings.Contains(src, "CondRewrite(),") {
		t.Errorf("a cond_rewrite whose basic leaves a residual must stay\n--- source: ---\n%s", src)
	}

	src = emitMember(t, env, EmitOptions{FuncName: "BuildNoCondOpen"}, condRewriteSection(open, false)).Source
	if !strings.Contains(src, "CondRewrite(),") || !strings.Contains(src, "Basic(),") {
		t.Errorf("a cond_rewrite on a goal Basic does not close must stay\n--- source: ---\n%s", src)
	}
}
