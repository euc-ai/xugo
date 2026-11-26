package emit

// Tests for the check on a headline's and a claim's text
// (emitter.surfaceText): the surface print is read back in the scope
// the emitted call parses it in, and a print that is not the statement
// it was printed from fails the emit.

import (
	"strings"
	"testing"

	"go.uber.org/goleak"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// nameClash is a statement no text spells: a free variable and a
// constant of one name and one type, under a predicate. Both print as
// the name, and the parser reads both occurrences as one of them — a
// statement that parses, and is another statement.
func nameClash(env *proof.ProverEnv) core.Prop {
	meta, _ := env.ProofService.LoadOrStoreConstMeta(core.MakeConstMeta("zz_clash", TypeInd))
	constant := ext.Const(meta, TypeInd)
	variable := ext.Var("zz_clash", TypeInd)
	holds := ext.Var("H", core.MakeFun(TypeInd, TypeInd, core.TypeBool()))
	return prop.MakeProp(holds.Apply(variable, constant).Core())
}

// assertNamesTheText checks an emit failure names the section, the text
// and both keys.
func assertNamesTheText(t *testing.T, err error, section, role, text string, statement core.Prop) {
	t.Helper()
	if err == nil {
		t.Fatalf("the emit returned a member for a %s text that does not read back", role)
	}
	msg := err.Error()
	for _, want := range []string{
		`section "` + section + `"`,
		"the " + role + " text",
		`"` + text + `"`,
		"does not read back",
		"the statement's key is " + string(registry.KeyOf(statement)),
		"it reads as the statement of key prop_",
	} {
		if !strings.Contains(msg, want) {
			t.Errorf("the failure does not say %q:\n%s", want, msg)
		}
	}
	if strings.Count(msg, string(registry.KeyOf(statement))) != 1 {
		t.Errorf("the two keys named are one key — the text read back:\n%s", msg)
	}
}

// TestEmit_HeadlineThatDoesNotReadBackFailsTheEmit: a section whose
// statement's print reads back as another statement is refused, with
// the section, the text and both keys.
func TestEmit_HeadlineThatDoesNotReadBackFailsTheEmit(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)
	goal := nameClash(env)

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{{Goal: pb.PropRef(goal), Step: &proof.StepProto_CnfRefute{}}}
	_, err := EmitMember([]*proof.DetailedProofProto{detailed(pb, steps...)}, env.ProofService.LoadConstMeta,
		EmitOptions{Family: emitTestFamily, FuncName: "Build_ClashingHeadline"})
	assertNamesTheText(t, err, "goal", "headline", "H(zz_clash, zz_clash)", goal)
}

// TestEmit_ClaimThatDoesNotReadBackFailsTheEmit: an asserted claim is
// held to the same check, and no Go-expression spelling of the claim
// is rendered in the text's place.
func TestEmit_ClaimThatDoesNotReadBackFailsTheEmit(t *testing.T) {
	defer goleak.VerifyNone(t)
	env := makeTestEnv(t)
	claim := nameClash(env)
	G := ext.Var("G", core.TypeBool())
	goal := prop.MakeProp(G.Core())
	residual := prop.MakeProp(G.Core(), claim.Conclusion())

	pb := ext.NewPoolBuilder()
	steps := []*proof.StepProto{
		{
			Goal:     pb.PropRef(goal),
			SubGoals: []*ext.HolPropProto{pb.PropRef(claim), pb.PropRef(residual)},
			Step:     &proof.StepProto_Assert{Assert: pb.PropRef(claim)},
		},
		{Goal: pb.PropRef(claim), Step: &proof.StepProto_TrivialSimplify{}},
		{Goal: pb.PropRef(residual), Step: &proof.StepProto_TrivialSimplify{}},
	}
	res, err := EmitMember([]*proof.DetailedProofProto{detailed(pb, steps...)}, env.ProofService.LoadConstMeta,
		EmitOptions{Family: emitTestFamily, FuncName: "Build_ClashingClaim"})
	assertNamesTheText(t, err, "goal", "claim", "H(zz_clash, zz_clash)", claim)
	if res.Source != "" {
		t.Errorf("a failed emit returned source:\n%s", res.Source)
	}
}
