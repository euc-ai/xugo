package emit

// Tests for the rendering of an assert whose claim an earlier section
// of the member proves (emitter.planSectionCites) — the record a
// session `cite-node` of that section's root leaves: the claim branch
// is the section's proof again, and the member renders a cite of the
// section's node in its place.

import (
	"os/exec"
	"strings"
	"testing"

	"go.uber.org/goleak"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// citedSectionMember is a two-section member whose second section
// asserts the first's statement and proves the claim by the first
// section's own steps — under a `clear_hyps` of the citing goal's
// hypotheses the section does not carry. The first section's proof is
// one Symm and a CnfRefute, steps no other part of the member records.
func citedSectionMember(statement, goal core.Prop) []*proof.DetailedProofProto {
	turned := prop.MakeProp(ext.Var("zz_turned", core.TypeBool()).Core(), statement.Hyps()...)
	sectionSteps := func(pb *ext.PoolBuilder) []*proof.StepProto {
		return []*proof.StepProto{
			{
				Goal:     pb.PropRef(statement),
				SubGoals: []*ext.HolPropProto{pb.PropRef(turned)},
				Step:     &proof.StepProto_Symm{},
			},
			{Goal: pb.PropRef(turned), Step: &proof.StepProto_CnfRefute{}},
		}
	}
	lemmaPool := ext.NewPoolBuilder()
	lemma := detailed(lemmaPool, sectionSteps(lemmaPool)...)

	pb := ext.NewPoolBuilder()
	claim := prop.MakeProp(statement.Conclusion(), goal.Hyps()...)
	residual := prop.MakeProp(goal.Conclusion(), append(goal.Hyps(), statement.Conclusion())...)
	steps := []*proof.StepProto{{
		Goal:     pb.PropRef(goal),
		SubGoals: []*ext.HolPropProto{pb.PropRef(claim), pb.PropRef(residual)},
		Step:     &proof.StepProto_Assert{Assert: pb.PropRef(prop.MakeProp(statement.Conclusion()))},
	}}
	if !claim.AlphaEquals(statement) {
		var drop []int32
		for i := range claim.NumHyps() {
			if !statement.HasHyp(claim.Hyp(i)) {
				drop = append(drop, int32(i))
			}
		}
		steps = append(steps, &proof.StepProto{
			Goal:     pb.PropRef(claim),
			SubGoals: []*ext.HolPropProto{pb.PropRef(statement)},
			Step:     &proof.StepProto_ClearHyps{ClearHyps: &proof.ClearHypsProto{HypIndices: drop}},
		})
	}
	steps = append(steps, sectionSteps(pb)...)
	steps = append(steps, &proof.StepProto{Goal: pb.PropRef(residual), Step: &proof.StepProto_TrivialSimplify{}})
	return []*proof.DetailedProofProto{lemma, detailed(pb, steps...)}
}

// TestEmit_SectionCite: the cite of the lemma variable stands for the
// claim branch's copy of the section's proof, which the member renders
// once, as the lemma's body.
//
// Where the cite verb, run on the asserting goal, installs the
// section's statement and nothing else, the assert and its claim branch
// are ONE `Cite(lemma)` on the spine and the continuation follows it.
// Where the verb would do more — here the statement matches the goal's
// conclusion, and a cite would chain backward and close the goal — the
// assert keeps its rendering, and its claim branch closes on the lemma
// variable.
func TestEmit_SectionCite(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)
	goBin, lookErr := exec.LookPath("go")

	// The statements are closed: the cite verb generalizes a variable a
	// statement leaves free as it installs it, which an assert does not.
	predicate := core.MakeFun(TypeInd, core.TypeBool())
	constant := func(name string, ty core.HolType) *ext.TermWrapper {
		meta, _ := env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta(core.TermName(name), ty))
		return ext.Const(meta, ty)
	}
	holds, point := constant("zz_holds", predicate), constant("zz_point", TypeInd)
	x := ext.Var("x", TypeInd)
	P := ext.Var("P", core.TypeBool())
	G := ext.Var("G", core.TypeBool())
	everywhere := prop.MakeProp(ext.ForAll(x)(holds.Apply(x)).Core())

	const (
		onTheSpine = "\t\t\t\t\t\tCite(lemma1),\n\t\t\t\t\t\tTrivialSimplify(),\n"
		inTheClaim = "\t\t\t\t\t\t\t\tCite(lemma1),\n\t\t\t\t\t\t\t),\n"
	)
	for _, tc := range []struct {
		name, pkg       string
		statement, goal core.Prop
		spine           bool
	}{
		{"the statement installs as asserted, the citing goal's hypothesis cleared",
			"sectioncitespineemit", everywhere, prop.MakeProp(G.Core(), P.Core()), true},
		{"the statement matches the citing goal's conclusion",
			"sectioncitecaseemit", everywhere, prop.MakeProp(holds.Apply(point).Core(), P.Core()), false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			src := emitMember(t, env, EmitOptions{Family: "tmp/" + tc.pkg, FuncName: "Build_CitesItsLemma"},
				citedSectionMember(tc.statement, tc.goal)...).Source
			if got := strings.Contains(src, onTheSpine); got != tc.spine {
				t.Errorf("one Cite(lemma1) on the spine before the continuation: %v, want %v\n--- source: ---\n%s", got, tc.spine, src)
			}
			if got := strings.Contains(src, "AssertStep(") && strings.Contains(src, inTheClaim); got == tc.spine {
				t.Errorf("the assert kept, its claim branch the cite: %v, want %v\n--- source: ---\n%s", got, !tc.spine, src)
			}
			if got := strings.Count(src, "Cite(lemma1"); got != 1 {
				t.Errorf("the lemma variable is cited %d times, want once\n--- source: ---\n%s", got, src)
			}
			for _, step := range []string{"Symm(),", "CnfRefute(),"} {
				if got := strings.Count(src, step); got != 1 {
					t.Errorf("%s is rendered %d times — the cited section's proof is the lemma's body, once\n--- source: ---\n%s", step, got, src)
				}
			}
			if strings.Contains(src, "ClearHyps(") {
				t.Errorf("the weakening to the section's context is rendered — it belongs to the proof the cite stands for\n--- source: ---\n%s", src)
			}
			if strings.Index(src, "lemma1 := ctx.Lemma(") > strings.Index(src, "Cite(lemma1)") {
				t.Errorf("the lemma local is cited before it is declared\n--- source: ---\n%s", src)
			}
			if lookErr != nil {
				t.Skipf("go binary unavailable: %v", lookErr)
			}
			vetMember(t, goBin, tc.pkg, src)
		})
	}
}
