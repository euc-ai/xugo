package proof

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestInstantiateAt_PolymorphicResidualBinderTypePreserved is the
// kernel-level invariant: instantiating a hyp's outer ∀-binder at a
// concrete witness must not touch the residual hyp's INNER ∀-binders'
// types, even when those inner binders are polymorphic.
//
// Setup:
//   - hyp `∀n:ind. ∀f:(A,B)→B. body` (the set_fold_stage-shaped pattern).
//   - instantiate at hyp_index=0, witness=_0:ind — peels ∀n.
//
// Asserts:
//   - residual hyp `∀f.body[n:=_0]` keeps f's binder type at (A,B)→B.
//   - free vars in the body keep their original types.
//
// This is the substitution kernel's contract. A binder type can also be
// collapsed on this shape one layer up (tryAdaptLemmaTypes's
// seedExistentialBinderSubsts — see prover/typematch); this test pins the
// kernel, so a regression here is told apart from one there.
func TestInstantiateAt_PolymorphicResidualBinderTypePreserved(t *testing.T) {
	A := core.TypeA()
	B := ext.TypeB
	AB_to_B := core.MakeFun(A, B, B)

	n := ext.Var("n", TypeInd)
	f := ext.Var("f", AB_to_B)
	x := ext.Var("x", A)
	z := ext.Var("z", B)
	y := ext.Var("y", B)

	fxz := ext.Apply(f.Core(), x.Core(), z.Core())
	body := ext.Exists(y)(ext.WrapTerm(core.Eq(fxz, y.Core())))
	lemmaConcl := ext.ForAll(n, f)(body).Core()

	t.Logf("lemma conclusion:        %s", ext.PrintTermWithPolyBinders(lemmaConcl))

	gx := ext.Var("g_x", core.TypeBool())
	goalConcl := core.Eq(gx.Core(), gx.Core())
	goalProp := prop.MakeProp(goalConcl, lemmaConcl)

	witness := ext.Var("_0", TypeInd).Core()

	sg := tactic.HypForallInstantiateTactic(witness)(goalProp)
	require.NotNil(t, sg, "instantiate at ∀n should produce SubGoals")
	require.Equal(t, 1, sg.Size())

	residualGoal := sg.ChildGoal(0)
	var partial core.Term
	for _, h := range residualGoal.Hyps() {
		if !h.AlphaEquals(lemmaConcl) {
			partial = h
			break
		}
	}
	require.NotNil(t, partial, "residual must have a new partial-∀ hyp")
	t.Logf("residual partial hyp:    %s", ext.PrintTermWithPolyBinders(partial))

	abs := ext.MatchesFORALL(partial)
	require.False(t, abs.IsZero(), "partial hyp must remain ∀-headed")

	gotType := abs.Var().Type()
	t.Logf("residual ∀f binder type: %s (want %s)",
		ext.FormatType(gotType), ext.FormatType(AB_to_B))

	assert.Truef(t, gotType.Equals(AB_to_B),
		"residual ∀f binder type collapsed: want %s, got %s",
		ext.FormatType(AB_to_B), ext.FormatType(gotType))

	for _, v := range abs.Body().Frees(nil) {
		switch v.Name() {
		case "x":
			assert.True(t, v.Type().Equals(A),
				"free var x type collapsed: want A, got %s", ext.FormatType(v.Type()))
		case "z":
			assert.True(t, v.Type().Equals(B),
				"free var z type collapsed: want B, got %s", ext.FormatType(v.Type()))
		}
	}
}
