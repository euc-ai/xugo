package emit

import (
	"errors"
	"slices"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
)

// citingSection is a section stating statement, closed by citing cited
// — a cite of another section's statement renders as that section's
// node — or, with cited nil, closed citing nothing.
func citingSection(statement, cited core.Term) *proof.DetailedProofProto {
	pb := ext.NewPoolBuilder()
	step := &proof.StepProto{Goal: pb.PropRef(prop.MakeProp(statement)), Step: &proof.StepProto_TrivialSimplify{}}
	if cited != nil {
		step.Step = &proof.StepProto_KnownThm{KnownThm: &proof.KnownThmProto{StrongerGoal: pb.PropRef(prop.MakeProp(cited))}}
	}
	return detailed(pb, step)
}

// TestSectionOrder_EachAfterWhatItCites: the sections a member renders
// are read off their cites — each after the sections it cites, ties in
// the given order, the statement last — and, cited-only, the sections
// the statement does not reach are left out; kept, they are refused.
func TestSectionOrder_EachAfterWhatItCites(t *testing.T) {
	env := makeTestEnv(t)
	P, Q, R, S := ext.Var("P", core.TypeBool()).Core(), ext.Var("Q", core.TypeBool()).Core(),
		ext.Var("R", core.TypeBool()).Core(), ext.Var("S", core.TypeBool()).Core()
	sections := []*proof.DetailedProofProto{
		citingSection(P, Q),   // cites the next section
		citingSection(Q, nil), // cites no section
		citingSection(S, nil), // cited by no section
		citingSection(R, P),   // the member's statement
	}
	opts := EmitOptions{Family: emitTestFamily, FuncName: "Build_Ordered"}
	order, err := SectionOrder(sections, env.ProofService.LoadConstMeta, opts, true)
	if err != nil {
		t.Fatalf("SectionOrder: %v", err)
	}
	if want := []int{1, 0, 3}; !slices.Equal(order, want) {
		t.Fatalf("cited-only order %v, want %v", order, want)
	}
	_, err = SectionOrder(sections, env.ProofService.LoadConstMeta, opts, false)
	var refused *SectionOrderError
	if !errors.As(err, &refused) || !slices.Equal(refused.Uncited, []int{2}) {
		t.Fatalf("an uncited section kept: got %v, want it refused as Uncited [2]", err)
	}

	ordered := make([]*proof.DetailedProofProto, len(order))
	for k, i := range order {
		ordered[k] = sections[i]
	}
	src := emitMember(t, env, opts, ordered...).Source
	if !strings.Contains(src, "lemma1 := ctx.Lemma(") || !strings.Contains(src, "CiteNode(lemma1)") || !strings.Contains(src, "CiteNode(lemma2)") {
		t.Fatalf("the ordered member does not cite each section after declaring it:\n%s", src)
	}
}

// TestSectionOrder_RefusesACycle: two sections citing each other's
// statement have no order, and the refusal names them.
func TestSectionOrder_RefusesACycle(t *testing.T) {
	env := makeTestEnv(t)
	P, Q, R := ext.Var("P", core.TypeBool()).Core(), ext.Var("Q", core.TypeBool()).Core(), ext.Var("R", core.TypeBool()).Core()
	sections := []*proof.DetailedProofProto{
		citingSection(P, Q),
		citingSection(Q, P),
		citingSection(R, P),
	}
	_, err := SectionOrder(sections, env.ProofService.LoadConstMeta, EmitOptions{Family: emitTestFamily, FuncName: "Build_Cycle"}, true)
	var refused *SectionOrderError
	if !errors.As(err, &refused) || !slices.Equal(refused.Cycle, []int{0, 1}) {
		t.Fatalf("got %v, want the cycle [0 1] refused", err)
	}
}
