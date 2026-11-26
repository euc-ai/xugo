package emit

import (
	"os/exec"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// TestEmit_TypeDefAxiomLeafCompiles is the go-vet gate for a cite of a
// type definition's axiom: a statement the resolver classifies as
// LeafTypeDefAxiom renders as `ctx.TypeDefAxiom(<const>, <selector>)`,
// and the member must TYPE-CHECK — the selector is a name the rendered
// file has in scope, for each of the two axioms.
func TestEmit_TypeDefAxiomLeafCompiles(t *testing.T) {
	goBin, err := exec.LookPath("go")
	if err != nil {
		t.Skipf("go binary unavailable: %v", err)
	}

	env := makeTestEnv(t)

	x := ext.Var("x", core.TypeA())
	R := ext.Var("R", core.MakeFun(core.TypeA(), core.TypeBool()))
	C := ext.Var("C", core.TypeBool())
	lemma := prop.MakeProp(ext.ForAll(x)(R.Apply(x)).Core())
	goal := prop.MakeProp(C.Core())
	residual := prop.MakeProp(C.Core(), lemma.Conclusion())

	// A Lemma step whose lemma child closes by an α-equal KnownThm: the
	// cite resolves the lemma through the external-leaf resolver.
	mkSection := func() *proof.DetailedProofProto {
		pb := ext.NewPoolBuilder()
		steps := []*proof.StepProto{
			{
				Goal:     pb.PropRef(goal),
				SubGoals: []*ext.HolPropProto{pb.PropRef(lemma), pb.PropRef(residual)},
				Step:     &proof.StepProto_Lemma{Lemma: pb.PropRef(lemma)},
			},
			{
				Goal: pb.PropRef(lemma),
				Step: &proof.StepProto_KnownThm{
					KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(lemma)},
				},
			},
			{
				Goal: pb.PropRef(residual),
				Step: &proof.StepProto_TrivialSimplify{},
			},
		}
		return detailed(pb, steps...)
	}
	lemmaKey := lemma.AlphaKey()
	normalized, _ := proof.Normalize(lemma)
	normalizedKey := normalized.AlphaKey()

	for _, tc := range []struct {
		pkg string
		sel TypeDefAxiomSel
	}{
		{"typedefabsrepemit", TypeDefAbsRep},
		{"typedefpredrepemit", TypeDefPredRep},
	} {
		t.Run(tc.pkg, func(t *testing.T) {
			src := emitMember(t, env, EmitOptions{
				Family:   "tmp/" + tc.pkg,
				FuncName: "Build_TypeDefAxiomLeaf",
				ResolveExternalLeaf: func(key core.PropKey) (ExternalLeaf, bool) {
					if key == lemmaKey || key == normalizedKey {
						return ExternalLeaf{Key: key, Kind: LeafTypeDefAxiom, ConstName: "mk_probe", TypeDefWhich: tc.sel}, true
					}
					return ExternalLeaf{}, false
				},
			}, mkSection()).Source
			if !strings.Contains(src, `ctx.TypeDefAxiom("mk_probe", `) {
				t.Fatalf("fixture defeated: no ctx.TypeDefAxiom call emitted\n--- source: ---\n%s", src)
			}
			vetMember(t, goBin, tc.pkg, src)
		})
	}
}
