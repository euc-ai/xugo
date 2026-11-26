package emit

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"go.uber.org/goleak"
)

// TestEmit_SpecializeStep guards the emit branch for the specialize
// composite ministep (proto tag 52): a Specialize StepProto must render
// as `Specialize(InstHyp(<idx>, <t>, …), …)` (or the
// …HypsKeep variant when keep_sources is set) with every witness term
// walked into the symbol table, and must not fall through to the
// unhandled-ministep path. emit only renders; it does not replay, so
// the synthetic goal need not be provable.
func TestEmit_SpecializeStep(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.TypeBool()))))
	q := ext.Var("q", core.TypeBool())

	all := ext.ForAll(x, y)(R.Apply(x, y)).Core()
	goal := prop.MakeProp(q.Core(), all)

	pb := ext.NewPoolBuilder()
	goalRef := pb.PropRef(goal)
	step := &proof.StepProto{
		Goal: goalRef,
		Step: &proof.StepProto_Specialize{
			Specialize: &proof.SpecializeProto{
				Hyps: []*proof.SpecializeProto_Hyp{{
					HypIndex:  0,
					Witnesses: []uint32{pb.TermRef(a.Core()), pb.TermRef(b.Core())},
				}},
			},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildSpecialize"}, detailed(pb, step)).Source
	if !strings.Contains(src, "Specialize(InstHyp(0, ") {
		t.Errorf("specialize ministep did not render as Specialize(InstHyp(…))\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "unhandled ministep") {
		t.Errorf("ministep fell through to unhandled placeholder\n--- source: ---\n%s", src)
	}
}

// TestEmit_SpecializeStep_Keep pins the keep_sources rendering variant.
func TestEmit_SpecializeStep_Keep(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	a := ext.Var("a", core.TypeA())
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	q := ext.Var("q", core.TypeBool())

	all := ext.ForAll(x)(P.Apply(x)).Core()
	goal := prop.MakeProp(q.Core(), all)

	pb := ext.NewPoolBuilder()
	goalRef := pb.PropRef(goal)
	step := &proof.StepProto{
		Goal: goalRef,
		Step: &proof.StepProto_Specialize{
			Specialize: &proof.SpecializeProto{
				Hyps: []*proof.SpecializeProto_Hyp{{
					HypIndex:  0,
					Witnesses: []uint32{pb.TermRef(a.Core())},
				}},
				KeepSources: true,
			},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildSpecializeKeep"}, detailed(pb, step)).Source
	if !strings.Contains(src, "SpecializeKeep(InstHyp(0, ") {
		t.Errorf("keep_sources variant did not render as SpecializeKeep\n--- source: ---\n%s", src)
	}
}

// TestEmit_SpecializeStep_MultiLine pins the readability transform: a
// Specialize with ≥2 InstHyp entries must render each entry on its own
// line so the mega-grounding case (has_size_funspace's 3×5-witness
// specialize) reads down the page instead of scrolling horizontally.
// Emit's `\n\t` continuation convention is re-anchored against the
// caller's own indent, so both the top-level `a.Do(...)` and Case-nested
// forms nest correctly (checked here via a successful parse plus the
// exact multi-line layout relative to the call's indent).
func TestEmit_SpecializeStep_MultiLine(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	y := ext.Var("y", core.TypeA())
	a := ext.Var("a", core.TypeA())
	b := ext.Var("b", core.TypeA())
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(core.TypeA(), core.MakeFun(core.TypeA(), core.TypeBool()))))
	q := ext.Var("q", core.TypeBool())

	allP := ext.ForAll(x)(P.Apply(x)).Core()
	allR := ext.ForAll(x, y)(R.Apply(x, y)).Core()
	goal := prop.MakeProp(q.Core(), allR, allP)
	// Locate indices in the canonically-sorted hyp list.
	pIdx, rIdx := -1, -1
	for i := 0; i < goal.NumHyps(); i++ {
		switch {
		case goal.Hyp(i).AlphaEquals(allP):
			pIdx = i
		case goal.Hyp(i).AlphaEquals(allR):
			rIdx = i
		}
	}
	if pIdx < 0 || rIdx < 0 {
		t.Fatalf("test setup: could not locate ∀-hyps in canonical goal")
	}

	pb := ext.NewPoolBuilder()
	goalRef := pb.PropRef(goal)
	step := &proof.StepProto{
		Goal: goalRef,
		Step: &proof.StepProto_Specialize{
			Specialize: &proof.SpecializeProto{
				Hyps: []*proof.SpecializeProto_Hyp{
					{HypIndex: int32(rIdx), Witnesses: []uint32{pb.TermRef(a.Core()), pb.TermRef(b.Core())}},
					{HypIndex: int32(pIdx), Witnesses: []uint32{pb.TermRef(a.Core())}},
				},
			},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildSpecializeMulti"}, detailed(pb, step)).Source
	// Each InstHyp entry on its own line one tab in from the call, with a
	// trailing comma before the closing paren at the call's own indent.
	const call = "Specialize(\n"
	at := strings.Index(src, call)
	if at < 0 {
		t.Fatalf("Specialize did not open a multi-line call\n--- source: ---\n%s", src)
	}
	indent := src[strings.LastIndex(src[:at], "\n")+1 : at]
	if strings.TrimLeft(indent, "\t") != "" {
		t.Fatalf("Specialize( is not at the start of its line\n--- source: ---\n%s", src)
	}
	entryLines := strings.Count(src, "\n"+indent+"\tInstHyp(")
	if entryLines != 2 {
		t.Errorf("expected 2 own-line InstHyp entries; got %d\n--- source: ---\n%s", entryLines, src)
	}
	if !strings.Contains(src[at:], "),\n"+indent+")") {
		t.Errorf("closing paren of multi-line Specialize should sit at caller indent\n--- source: ---\n%s", src)
	}
}
