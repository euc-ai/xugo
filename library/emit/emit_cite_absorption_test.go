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

// TestEmit_CiteSpecializeFusesAtAbsorptionSite pins the content half of
// installedHypIndexStatic: a `lemma_preserve + known_thm + specialize`
// triple whose install netted SEVERAL hyps (the lemma's own, plus the
// clause-shaped goal's folded disjuncts) still fuses into ONE cite call.
//
// A pure before/after diff is ambiguous here; declining the fusion
// renders `Specialize(InstHyp(0, w…))`, whose bare index trips the gate
// suite's TestLintNoPositionalHypIndices.
// One session move must render as one thing.
func TestEmit_CiteSpecializeFusesAtAbsorptionSite(t *testing.T) {
	defer goleak.VerifyNone(t)

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	c := ext.Var("c", core.TypeA())
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool())))
	A := ext.Var("A", core.TypeBool())
	B := ext.Var("B", core.TypeBool())
	G := ext.Var("G", core.TypeBool())

	all := ext.ForAll(x)(R.Apply(x)).Core()
	// Clause-shaped goal, no hyps: the cite folds it.
	goal := prop.MakeProp(ext.Or(ext.Not(A), ext.Or(ext.Not(B), G)).Core())
	// Post-install state: the lemma's ∀-form AND the two absorbed
	// disjuncts arrive together. core.MakeProp content-sorts the hyp
	// list, so which index the ∀-hyp lands at is not ours to choose —
	// the test reads it back and records THAT as the specialize target,
	// exactly as a real recording would.
	installed := prop.MakeProp(G.Core(), all, A.Core(), B.Core())
	hypIdx := -1
	for i := range installed.NumHyps() {
		if installed.Hyp(i).AlphaEquals(all) {
			hypIdx = i
		}
	}
	if hypIdx < 0 {
		t.Fatalf("fixture: installed goal has no ∀-hyp")
	}
	if installed.NumHyps() != 3 {
		t.Fatalf("fixture must be an ABSORPTION site (3 net-new hyps); got %d",
			installed.NumHyps())
	}
	ground := prop.MakeProp(G.Core(), R.Apply(c).Core(), A.Core(), B.Core())

	pb := ext.NewPoolBuilder()
	lemmaProp := prop.MakeProp(all)
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(lemmaProp), pb.PropRef(installed)},
			Step:     &proof.StepProto_LemmaPreserve{LemmaPreserve: pb.PropRef(lemmaProp)},
		},
		{
			Goal: pb.PropRef(lemmaProp),
			Step: &proof.StepProto_KnownThm{
				KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(lemmaProp)},
			},
		},
		{
			Goal:     pb.PropRef(installed),
			SubGoals: []*ext.HolPropProto{pb.PropRef(ground)},
			Step: &proof.StepProto_Specialize{
				Specialize: &proof.SpecializeProto{
					Hyps: []*proof.SpecializeProto_Hyp{{
						HypIndex:  int32(hypIdx),
						Witnesses: []uint32{pb.TermRef(c.Core())},
					}},
				},
			},
		},
		{
			Goal: pb.PropRef(ground),
			Step: &proof.StepProto_TrivialSimplify{},
		},
	}

	lemmaKey := lemmaProp.AlphaKey()
	normalized, _ := proof.Normalize(lemmaProp)
	resolve := func(key core.PropKey) (ExternalLeaf, bool) {
		if key == lemmaKey || key == normalized.AlphaKey() {
			return ExternalLeaf{Key: key, Kind: LeafLibraryThm, ThmName: "ABSORB_LIKE"}, true
		}
		return ExternalLeaf{}, false
	}

	// The consolidated verb, dep by name, the witness a declared local.
	src := emitMember(t, env, EmitOptions{
		FuncName:            "BuildAbsorb",
		ResolveExternalLeaf: resolve,
	}, detailed(pb, steps...)).Source
	if !strings.Contains(src, `Cite("ABSORB_LIKE", c),`) {
		t.Errorf("absorption-site cite did not fuse into Cite(dep, w…)\n--- source: ---\n%s", src)
	}
	if !strings.Contains(src, `c := ctx.Var("c", `) {
		t.Errorf("the witness is not declared\n--- source: ---\n%s", src)
	}
	if strings.Contains(src, "InstHyp(") {
		t.Errorf("absorption-site cite still renders a positional InstHyp\n--- source: ---\n%s", src)
	}
}
