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

// TestEmit_SimpWithStep guards the emit branch for the simp_with
// ministep: a SimpWith StepProto must render as `<ctx>.SimpWith(<rule>,
// …)` — the Script-level constructor whose apply is the SAME driver the
// recording engine dispatch ran (record/emit/replay-reuse) — with each
// recorded rule rendered through the LeanRw payload resolver (here the
// verbatim MakeProp fallback, since the synthetic rule resolves to no
// section), and must not fall through to the unhandled-ministep path.
// emit only renders; it does not replay, so the synthetic goal need not
// be simp_with-provable.
func TestEmit_SimpWithStep(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	f := ext.WrapTerm(ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA())))
	g := ext.WrapTerm(ext.Var("g", core.MakeFun(core.TypeA(), core.TypeA())))
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	a := ext.Var("a", core.TypeA())

	rule := prop.MakeProp(ext.ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core())

	pb := ext.NewPoolBuilder()
	goal := pb.PropRef(prop.MakeProp(P.Apply(f.Apply(a)).Core()))
	ruleRef := pb.PropRef(rule)

	step := &proof.StepProto{
		Goal: goal,
		Step: &proof.StepProto_SimpWith{
			SimpWith: &proof.SimpWithProto{Rules: []*ext.HolPropProto{ruleRef}},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildSimpWith"}, detailed(pb, step)).Source
	if !strings.Contains(src, "SimpWith(") {
		t.Errorf("SimpWith ministep did not render\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "unhandled ministep") {
		t.Errorf("ministep fell through to unhandled placeholder\n--- source: ---\n%s", src)
	}
}

// TestEmit_SimpWithFlipped: when the recorded step carries any flipped
// rule, emit must render the SimpWithFlipped variant (parallel bool
// slice), NOT the zero-flip SimpWith constructor — otherwise emitted
// code would silently fire the rule in the wrong direction at replay.
// A step with rule_flip empty (or all-false) still renders as
// SimpWith(…) — the byte-stable back-compat path for pre-flip snapshots.
func TestEmit_SimpWithFlipped(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	f := ext.WrapTerm(ext.Var("f", core.MakeFun(core.TypeA(), core.TypeA())))
	g := ext.WrapTerm(ext.Var("g", core.MakeFun(core.TypeA(), core.TypeA())))
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool())))
	a := ext.Var("a", core.TypeA())

	rule := prop.MakeProp(ext.ForAll(x)(f.Apply(x).Eq(g.Apply(x))).Core())

	pb := ext.NewPoolBuilder()
	goal := pb.PropRef(prop.MakeProp(P.Apply(g.Apply(a)).Core()))
	ruleRef := pb.PropRef(rule)

	step := &proof.StepProto{
		Goal: goal,
		Step: &proof.StepProto_SimpWith{
			SimpWith: &proof.SimpWithProto{
				Rules:    []*ext.HolPropProto{ruleRef},
				RuleFlip: []bool{true},
			},
		},
	}

	src := emitMember(t, env, EmitOptions{FuncName: "BuildSimpWithFlipped"}, detailed(pb, step)).Source
	if !strings.Contains(src, "SimpWithFlipped(") {
		t.Errorf("flipped SimpWith ministep did not render the SimpWithFlipped constructor\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, "[]bool{true}") {
		t.Errorf("emitted code missing the parallel flip slice\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "unhandled ministep") {
		t.Errorf("ministep fell through to unhandled placeholder\n--- source: ---\n%s", src)
	}
}

// A resident rule may rewrite without a separate rule-obligation child:
// a resident hypothesis assumed, or a claim with no hypotheses stating a
// hypothesis of the goal (a session's text rule spelling a Let or a
// Have). A named rule's child must not make that resident rule disappear
// from the fused Simp call, which spells it as the fact naming the
// hypothesis in its recorded orientation; unused named rules, and a
// claim the goal does not hold, are still omitted.
func TestEmit_SimpFusionKeepsResidentRulesBesideNamedRules(t *testing.T) {
	defer goleak.VerifyNone(t)
	for _, test := range []struct {
		name             string
		flipped, claimed bool
	}{
		{name: "assumed forward"},
		{name: "assumed reverse", flipped: true},
		{name: "claimed forward", claimed: true},
		{name: "claimed reverse", flipped: true, claimed: true},
	} {
		t.Run(test.name, func(t *testing.T) {
			env := makeTestEnv(t)
			P := ext.Var("P", core.TypeBool())
			Q := ext.Var("Q", core.TypeBool())
			R := ext.Var("R", core.TypeBool())
			U := ext.Var("U", core.TypeBool())
			V := ext.Var("V", core.TypeBool())
			residentEquation := P.Eq(Q).Core()
			if test.flipped {
				residentEquation = Q.Eq(P).Core()
			}
			resident := core.Prop(core.Assume(residentEquation))
			if test.claimed {
				resident = prop.MakeProp(residentEquation)
			}
			named := prop.MakeProp(Q.Eq(R).Core())
			unused := prop.MakeProp(U.Core())
			stray := prop.MakeProp(V.Core())
			goal := prop.MakeProp(P.Core(), residentEquation)
			residual := prop.MakeProp(R.Core(), residentEquation)
			pb := ext.NewPoolBuilder()
			steps := []*proof.StepProto{
				{
					Goal:     pb.PropRef(goal),
					SubGoals: []*ext.HolPropProto{pb.PropRef(named), pb.PropRef(residual)},
					Step: &proof.StepProto_SimpWith{SimpWith: &proof.SimpWithProto{
						Rules:    []*ext.HolPropProto{pb.PropRef(resident), pb.PropRef(named), pb.PropRef(unused), pb.PropRef(stray)},
						RuleFlip: []bool{test.flipped, false, false, false},
					}},
				},
				{Goal: pb.PropRef(named), Step: &proof.StepProto_TrivialSimplify{}},
				{Goal: pb.PropRef(residual), Step: &proof.StepProto_TrivialSimplify{}},
			}
			resolver := func(key core.PropKey) (ExternalLeaf, bool) {
				switch key {
				case named.AlphaKey():
					return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "RULE_NAMED"}, true
				case unused.AlphaKey():
					return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "RULE_UNUSED"}, true
				}
				return ExternalLeaf{}, false
			}
			src := emitMember(t, env, EmitOptions{FuncName: "BuildMixedSimp", ResolveExternalLeaf: resolver}, detailed(pb, steps...)).Source
			if !strings.Contains(src, `Fwd("RULE_NAMED")`) || strings.Contains(src, "RULE_UNUSED") {
				t.Fatalf("named rule selection changed:\n%s", src)
			}
			if strings.Contains(src, "SimpWith") {
				t.Fatalf("the unused claim was kept, and the Simp fusion declined:\n%s", src)
			}
			ctor := "Fwd"
			if test.flipped {
				ctor = "Rev"
			}
			if !strings.Contains(src, ctor+"(h)") {
				t.Fatalf("mixed Simp lost its resident rule or its orientation:\n%s", src)
			}
			wantFwd, wantRev := 2, 0
			if test.flipped {
				wantFwd, wantRev = 1, 1
			}
			if strings.Count(src, "Fwd(") != wantFwd || strings.Count(src, "Rev(") != wantRev {
				t.Fatalf("mixed Simp printed other rules than the resident and the named one:\n%s", src)
			}
		})
	}
}
