package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestSetTac_RecordProtoReplayRoundtrip is the acceptance test for the
// record/emit/replay-reuse design: ONE recorded SetTac ministep whose
// serialized proto carries the const list, and whose replay re-runs the
// SAME executor (proof.ApplySetTac) on the recorded goal.
//
//  1. record: engine dispatch applies set_tac → _SetTacStep ministep.
//  2. serialize: the section's DetailedProofProto through the wire.
//  3. decode: exactly one StepProto_SetTac, consts == DefaultSetTacConsts.
//  4. replay: rebuild the recorded goal from the proto pool and close it
//     via proof.ApplySetTac with the RECORDED consts — the identical
//     call collectSectionCNF (emit-time verification) and emitted Build_X
//     code (`Do(ctx.SetTac(...))` → same _SetTacStep.apply) execute.
func TestSetTac_RecordProtoReplayRoundtrip(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Roundtrip goal: a trivial hyp=concl tautology. set_tac falls
	// through to a bare CNF refute (the fixpoint unfolder is a no-op on a
	// goal with no set-vocab consts), the residual closes, and the
	// close-or-fail ministep gets recorded. This isolates the
	// record/emit/replay-reuse property under test from any specific
	// CNF-refute enhancement or set-vocabulary def_expand behavior.
	res := dsl.ParsePropText("a:num, b:num, a = b ⊢ a = b")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)
	s.rebuildGoalIndex()

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "set_tac"},
	})
	require.NoError(t, err)
	require.True(t, out.Success)

	// (2) Serialize the proof tree.
	detailed := sectionRecord(t, s.sections[0])

	// (3) Locate the SetTac ministep.
	var setTacSteps []*proof.StepProto
	for _, st := range detailed.Steps {
		if _, ok := st.Step.(*proof.StepProto_SetTac); ok {
			setTacSteps = append(setTacSteps, st)
		}
	}
	require.Len(t, setTacSteps, 1, "exactly one recorded SetTac ministep")
	recorded := setTacSteps[0]
	recordedConsts := recorded.Step.(*proof.StepProto_SetTac).SetTac.GetConsts()
	wantConsts := proof.DefaultSetTacConsts()
	require.Len(t, recordedConsts, len(wantConsts))
	for i, w := range wantConsts {
		assert.Equal(t, string(w), recordedConsts[i],
			"recorded const list must be the sorted default vocabulary")
	}

	// (4) Replay from the recorded proto: rebuild the goal, re-run the
	// shared executor with the RECORDED const list in the RECORDED mode.
	r := ext.NewPoolReader(detailed.Pool, e.env.ProofService.LoadConstMeta)
	// The bool is ClaimProved (recorded-state metadata), not decode success.
	g, _ := r.Prop(recorded.Goal)
	require.NotNil(t, g)
	consts := make([]core.TermName, len(recordedConsts))
	for i, c := range recordedConsts {
		consts[i] = core.TermName(c)
	}
	n := proof.CreateGoalStack(g)
	mode := recorded.Step.(*proof.StepProto_SetTac).SetTac.GetMode()
	require.True(t, proof.ApplySetTacMode(n, e.env, t.Context(), consts, mode, nil),
		"replaying the recorded SetTac step on the recorded goal must close")
	assert.True(t, n.Proved())
}

// TestSetTac_FailureSurfacesResiduals pins the failure-path ergonomics:
// a set_tac that cannot close reports WHICH residual leaves the refuter
// walled on (rendered goals in the tactic_failure diagnostic), instead of
// the bare "did not apply". Here the goal has no set-vocab consts, so the
// composite falls through to the bare refute on the goal itself and the
// unprovable `a = b` comes back as the residual.
func TestSetTac_FailureSurfacesResiduals(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("a:num, b:num ⊢ a = b")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "set_tac"},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	require.NotEmpty(t, out.Diagnostics)
	msg := out.Diagnostics[0].Message
	assert.Contains(t, msg, "residual",
		"failure diagnostic must mention the unrefuted residual leaves; got: %s", msg)
	assert.Contains(t, msg, "a = b",
		"failure diagnostic must render the residual leaf goal; got: %s", msg)
	assert.Contains(t, msg, "by {settac:true}",
		"and say what a failure here means: set_tac refutes its residuals bare, so a goal a conditioned "+
			"closer takes wanted the conditioning; got: %s", msg)
}

// TestSetTac_MinimalEqRewrite: a one-paramodulation-step goal with a
// function-typed equality hyp:
//
//	¬set_member(x_0, empty_set), s_0 = empty_set ⊢ ¬set_member(x_0, s_0)
//
// The set_tac ministep unfolds set_member/empty_set (its recorded vocabulary) and the
// closing CNF refute rewrites by the function-typed equality hypothesis.
func TestSetTac_MinimalEqRewrite(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText(
		"s_0:num→bool, x_0:num, ~set_member(x_0, empty_set), s_0 = empty_set ⊢ ~set_member(x_0, s_0)")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "set_tac"},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("set_tac diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success, "set_tac must close the fun-typed-equality goal")

	stateRes, gerr := e.InspectState(ctx, info.ID)
	require.NoError(t, gerr)
	assert.Equal(t, 0, stateRes.NumOpen,
		"session goal must be fully closed after set_tac")
}
