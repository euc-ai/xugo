package engine

import (
	"context"
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// foldStageSucGoalText is the successor lemma of set_fold_stage, in its
// normalized shape.
const foldStageSucGoalText = "∀n:num. ∀f:(A → (B → B)). ∀s:set(A). ∀b:B. ∀z:B. ∀x:A. ∃w:B. ∃u:A. ∃y:A. " +
	"((¬(x ∈ s) ∨ ¬set_fold_stage(f, b, s, z, suc(n))) ∨ (u ≠ y ∧ f(u, f(y, w)) ≠ f(y, f(u, w)))) ∨ " +
	"(z = f(x, w) ∧ set_fold_stage(f, b, delete(s, x), w, n))"

// foldStageDefText is set_fold_stage's defining equations
// as one ∀-closed conjunction.
const foldStageDefText = "∀n:num. ∀f:(A → (B → B)). ∀s:set(A). ∀a:B. ∀b:B. " +
	"((a = b ∧ s = ∅) ⇔ set_fold_stage(f, b, s, a, 0)) ∧ " +
	"((∃c:B. ∃x:A. a = f(x, c) ∧ x ∈ s ∧ set_fold_stage(f, b, delete(s, x), c, n)) ⇔ set_fold_stage(f, b, s, a, suc(n)))"

// TestSetFoldStage_LemmaPlusInstantiate_PreservesPolyBinderType walks the
// set_fold_stage successor lemma:
//
//  1. Goal: the successor lemma (foldStageSucGoalText).
//  2. `apply lemma` inline with the set_fold_stage def-eq (foldStageDefText).
//     Hyp[0] is ∀n.∀f.∀s.∀a.∀b.(P_base ∧ P_step) where f's binder type is
//     polymorphic (A,B)→B.
//  3. `apply instantiate {hyp_index:0, const:"_0"}` — peels ∀n at 0.
//     Residual hyp[0] should be ∀f.∀s.∀a.∀b.(P_base ∧ P_step[n:=_0]),
//     with f STILL at (A,B)→B.
//  4. `apply instantiate` at hyp 0 with a witness of type (A,B)→B
//     succeeds. A binder collapsed to (A,A)→A refuses it: "term has type
//     ((var:A, var:B) → var:B) but expected ((var:A, var:A) → var:A)".
func TestSetFoldStage_LemmaPlusInstantiate_PreservesPolyBinderType(t *testing.T) {
	// Both statements are stated inline: the def-eq loads as a lemma by
	// its text, and its reproduction child is closed white-box.
	foldStageSucProp, err := parsePropTextInGoalScope(foldStageSucGoalText, prop.MakeProp(ext.T), nil)
	require.NoError(t, err)
	foldStageDefProp, err := parsePropTextInGoalScope(foldStageDefText, prop.MakeProp(ext.T), nil)
	require.NoError(t, err)
	t.Logf("goal (successor lemma): %s",
		ext.PrintTermWithPolyBinders(foldStageSucProp.Conclusion()))

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	s.AddGoal(foldStageSucProp)
	s.rebuildGoalIndex()

	var goalID string
	for id, ge := range s.goalIndex {
		if ge.sectionID == 0 {
			goalID = id
			break
		}
	}
	require.NotEmpty(t, goalID)

	// Step 1: strip_quant the goal so we have free vars to work with.
	resStrip, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "strip_quant"},
	})
	require.NoError(t, err)
	if !resStrip.Success {
		// strip might fail if the goal isn't ∀-headed at this point; the
		// scenario can still run on the original goal.
		t.Logf("strip_quant unsuccessful (carry on with raw goal)")
	}
	if resStrip.State != nil && len(resStrip.State.Goals) > 0 {
		goalID = resStrip.State.Goals[0].ID
	}

	// Step 2: apply lemma(set_fold_stage def-eq), inline; its reproduction child
	// is closed white-box.
	resLemma, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{
			Type:  "lemma",
			Lemma: foldStageDefProp,
		},
	})
	require.NoError(t, err)
	require.True(t, resLemma.Success, "lemma apply must succeed (diagnostics=%v)",
		resLemma.Diagnostics)
	closeReproductionChildrenTrusted(t, s, s.sections[0].root)
	lemState, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	require.NotEmpty(t, lemState.Goals, "lemma must leave at least one open goal")
	goalID = lemState.Goals[0].ID

	// Find the installed lemma hyp. It should be ∀-headed and contain
	// set_fold_stage.
	var lemmaHypIdx int = -1
	var preInstantiateHyp string
	for i, h := range lemState.Goals[0].Hypotheses {
		s := ext.PrintTermWithPolyBinders(h)
		if strings.HasPrefix(s, "∀n.") || strings.Contains(s, "∀n.∀f") {
			lemmaHypIdx = i
			preInstantiateHyp = s
			break
		}
	}
	require.GreaterOrEqualf(t, lemmaHypIdx, 0,
		"must find a ∀n.∀f-headed set_fold_stage hyp on the lemma-loaded goal; got hyps:\n%s",
		dumpHyps(lemState.Goals[0].Hypotheses))
	t.Logf("pre-instantiate hyp[%d]: %s", lemmaHypIdx, preInstantiateHyp)

	// Step 3: instantiate hyp[0] at "_0" (peel ∀n).
	resInst1, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{
			Type:     "instantiate",
			Const:    "_0",
			HypIndex: pIntForInstantiate(lemmaHypIdx),
		},
	})
	require.NoError(t, err)
	require.Truef(t, resInst1.Success,
		"first instantiate (n:=_0) failed: %v", resInst1.Diagnostics)
	require.NotNil(t, resInst1.State)
	require.NotEmpty(t, resInst1.State.Goals)
	goalID = resInst1.State.Goals[0].ID

	// Find the residual partial-∀ hyp on the post-instantiate state.
	var partialIdx int = -1
	var partialPrint string
	for i, h := range resInst1.State.Goals[0].Hypotheses {
		s := ext.PrintTermWithPolyBinders(h)
		// the partial should be ∀f-headed (∀n was peeled).
		if strings.HasPrefix(s, "∀f") {
			partialIdx = i
			partialPrint = s
			break
		}
	}
	require.GreaterOrEqualf(t, partialIdx, 0,
		"must find a ∀f-headed partial hyp post-instantiate; got hyps:\n%s",
		dumpHyps(resInst1.State.Goals[0].Hypotheses))
	t.Logf("post-instantiate(n:=_0) partial hyp[%d]: %s", partialIdx, partialPrint)

	// Invariant: the partial's ∀f must keep its (A,B)→B binder.
	// Before the fix the print contained `(var:A → (var:A → var:A))` —
	// B silently collapsed to A by tryAdaptLemmaTypes's
	// seedExistentialBinderSubsts when lemma's 2 ∃-binders (∃x:A.∃c:B)
	// got positionally paired with goal's first 2 ∃-binders (∃uʹ:A.∃y:A).
	const wantedShape = "(var:A → (var:B → var:B))"
	const collapsedShape = "(var:A → (var:A → var:A))"
	assert.NotContains(t, partialPrint, collapsedShape,
		"∀f binder collapsed (A,B)→B ⇒ (A,A)→A — the set_fold_stage tryAdapt bug")
	assert.Contains(t, partialPrint, wantedShape,
		"∀f binder must keep its (A,B)→B shape post-instantiate(n:=_0)")

	// End-to-end: a follow-up `instantiate` at an (A,B)→B-typed witness
	// must SUCCEED. A collapsed binder fails it with "term has type
	// ((var:A, var:B) → var:B) but expected ((var:A, var:A) → var:A)".
	resInst2, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		// Inline text-DSL witness with type annotation — doesn't depend
		// on the goal's local scope to find an f_0.
		Tactic: TacticReq{
			Type:     "instantiate",
			Const:    "(λx:var:A.λy:var:B. y)",
			HypIndex: pIntForInstantiate(partialIdx),
		},
	})
	require.NoError(t, err)
	assert.Truef(t, resInst2.Success,
		"second instantiate (f := λx:A.λy:B.y at (A,B)→B) must succeed; "+
			"failure indicates the set_fold_stage type-collapse bug returned. "+
			"diagnostics=%v",
		resInst2.Diagnostics)
}

func dumpHyps(hyps []core.Term) string {
	var b strings.Builder
	for i, h := range hyps {
		fmt.Fprintf(&b, "[%d] %s\n", i, ext.PrintTermWithPolyBinders(h))
	}
	return b.String()
}
