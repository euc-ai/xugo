package emit

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// Probe: a specialize witness var that appears nowhere else must still
// get a local declaration.
func TestEmit_SpecializeStep_DeclaresWitnessVars(t *testing.T) {
	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	// zonly appears ONLY as a specialize witness.
	zonly := ext.Var("zonly", core.TypeA())
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.TypeBool()))))
	q := ext.Var("q", core.TypeBool())

	all := ext.ForAll(x, y)(R.Apply(x, y)).Core()
	goal := prop.MakeProp(q.Core(), all)

	pb := ext.NewPoolBuilder()
	goalRef := pb.PropRef(goal)
	after := prop.MakeProp(q.Core(), R.Apply(zonly, zonly).Core())
	afterRef := pb.PropRef(after)
	step := &proof.StepProto{
		Goal:     goalRef,
		SubGoals: []*ext.HolPropProto{afterRef},
		Step: &proof.StepProto_Specialize{
			Specialize: &proof.SpecializeProto{
				Hyps: []*proof.SpecializeProto_Hyp{{
					HypIndex:  0,
					Witnesses: []uint32{pb.TermRef(zonly.Core()), pb.TermRef(zonly.Core())},
				}},
			},
		},
	}
	closing := &proof.StepProto{Goal: afterRef, Step: &proof.StepProto_CnfRefute{}}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildDeclProbe"}, detailed(pb, step, closing)).Source
	if !strings.Contains(src, `zonly := ctx.Var("zonly"`) {
		t.Errorf("witness-only var not declared\n--- source: ---\n%s", src)
	}
}

// TestEmit_ABinderOfAGoTermRegistersNoName: a witness written as a Go
// term names the binders of its λs as locals, and such a local is
// built by `Var`: `ctx.Var("n", …)` would register n in the script's
// scope, the `n` every later text reads and the name no closure
// binding an `n` could then alias. A variable free in a goal is the
// proof's own and keeps `ctx.Var`.
func TestEmit_ABinderOfAGoTermRegistersNoName(t *testing.T) {
	env := makeTestEnv(t)
	fun := core.MakeFun(core.TypeA(), core.TypeA())
	x := ext.Var("x", fun)
	n := ext.Var("n", core.TypeA())
	free := ext.Var("free", core.TypeA())
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(fun, core.MakeFun(core.TypeA(), core.TypeBool()))))
	y := ext.Var("y", core.TypeA())
	q := ext.Var("q", core.TypeBool())

	all := ext.ForAll(x, y)(R.Apply(x, y)).Core()
	identity := ext.WrapTerm(core.Abs(n.Core().(core.VarTerm), n.Core()))
	goal := prop.MakeProp(q.Core(), all)
	after := prop.MakeProp(q.Core(), R.Apply(identity, free).Core())

	pb := ext.NewPoolBuilder()
	afterRef := pb.PropRef(after)
	step := &proof.StepProto{
		Goal:     pb.PropRef(goal),
		SubGoals: []*ext.HolPropProto{afterRef},
		Step: &proof.StepProto_Specialize{
			Specialize: &proof.SpecializeProto{
				Hyps: []*proof.SpecializeProto_Hyp{{
					HypIndex:  0,
					Witnesses: []uint32{pb.TermRef(identity.Core()), pb.TermRef(free.Core())},
				}},
			},
		},
	}
	closing := &proof.StepProto{Goal: afterRef, Step: &proof.StepProto_CnfRefute{}}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildBinderProbe"}, detailed(pb, step, closing)).Source
	if !strings.Contains(src, `n := Var("n", `) {
		t.Errorf("the λ's binder is not built by Var\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, `ctx.Var("n"`) {
		t.Errorf("the λ's binder is registered in the script's scope\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, `free := ctx.Var("free", `) {
		t.Errorf("the goal's own variable is not declared by ctx.Var\n--- source: ---\n%s", src)
	}
}
