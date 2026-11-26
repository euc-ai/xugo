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

// autoCheckpointsSorted returns the auto_* checkpoints in the session's
// ListCheckpoints view, in the order the view lists them.
func autoCheckpointsSorted(t *testing.T, e *Engine, sessionID string) []CheckpointInfo {
	t.Helper()
	list, err := e.ListCheckpoints(context.Background(), sessionID)
	require.NoError(t, err)
	out := make([]CheckpointInfo, 0, len(list))
	for _, ci := range list {
		if strings.HasPrefix(ci.Name, autoCheckpointNamePrefix) {
			out = append(out, ci)
		}
	}
	return out
}

// applyAutoOnAllOpen runs a single "auto" tactic against every open goal in
// the current state view. Each call to ApplyStep is one RPC-boundary apply.
func applyAutoOnAllOpen(t *testing.T, e *Engine, sessionID string) {
	t.Helper()
	ctx := context.Background()
	state, err := e.InspectState(ctx, sessionID)
	require.NoError(t, err)
	for _, g := range state.Goals {
		_, err := e.ApplyStep(ctx, sessionID, &ApplyStepRequest{
			GoalID: g.ID,
			Tactic: TacticReq{Type: "auto"},
		})
		require.NoError(t, err)
	}
}

// TestAutoCheckpoint_SequentialNames verifies that a sequence of successful
// ApplyStep RPCs creates auto_1, auto_2, ... checkpoints in order.
func TestAutoCheckpoint_SequentialNames(t *testing.T) {
	env := testEnv()
	e := newEngine(env, WithAutoCheckpoint(10))
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Add three independent trivial goals so each ApplyStep is a separate
	// RPC-boundary apply (goals close on the first auto call).
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	r := ext.Var("r", core.TypeBool())
	s.AddGoal(prop.MakeProp(p.Imply(p)))
	s.AddGoal(prop.MakeProp(q.Imply(q)))
	s.AddGoal(prop.MakeProp(r.Imply(r)))

	// Should have 0 auto checkpoints before any apply.
	assert.Empty(t, autoCheckpointsSorted(t, e, info.ID), "no auto checkpoints before any apply")

	state, _ := e.InspectState(ctx, info.ID)
	require.Len(t, state.Goals, 3)
	names := make([]string, 0, 3)
	for _, g := range state.Goals {
		_, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: g.ID,
			Tactic: TacticReq{Type: "auto"},
		})
		require.NoError(t, err)
		list := autoCheckpointsSorted(t, e, info.ID)
		require.NotEmpty(t, list)
		names = append(names, list[len(list)-1].Name)
	}
	assert.Equal(t, []string{"auto_1", "auto_2", "auto_3"}, names,
		"auto checkpoints numbered monotonically per session")
}

// TestAutoCheckpoint_LRUEviction verifies that when the auto checkpoint
// count exceeds cap, the oldest auto_* entry is evicted at insertion time.
func TestAutoCheckpoint_LRUEviction(t *testing.T) {
	env := testEnv()
	cap := 3
	e := newEngine(env, WithAutoCheckpoint(cap))
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Fire five sequential ApplyStep calls (each on a fresh trivial goal so
	// each apply succeeds and produces one auto checkpoint).
	for i := 0; i < 5; i++ {
		v := ext.Var(ext.TermName(fmt.Sprintf("v%d", i)), core.TypeBool())
		s.AddGoal(prop.MakeProp(v.Imply(v)))
		state, _ := e.InspectState(ctx, info.ID)
		// Only apply to the newly-added open goal (the last one).
		g := state.Goals[len(state.Goals)-1]
		_, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: g.ID,
			Tactic: TacticReq{Type: "auto"},
		})
		require.NoError(t, err)
	}

	autos := autoCheckpointsSorted(t, e, info.ID)
	require.Len(t, autos, cap, "auto checkpoint count capped at %d", cap)
	// The oldest surviving name should be auto_3 (auto_1 and auto_2 were
	// evicted as the 4th and 5th were inserted).
	assert.Equal(t, "auto_3", autos[0].Name, "auto_1 and auto_2 evicted; auto_3 is now oldest")
	assert.Equal(t, "auto_5", autos[len(autos)-1].Name, "auto_5 is newest")
}

// TestAutoCheckpoint_UserCheckpointsStickyUnderLRU verifies that a
// user-named checkpoint (no auto_ prefix) is NEVER evicted by the LRU pass,
// even when many auto checkpoints are subsequently created.
func TestAutoCheckpoint_UserCheckpointsStickyUnderLRU(t *testing.T) {
	env := testEnv()
	cap := 2
	e := newEngine(env, WithAutoCheckpoint(cap))
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	s.AddGoal(prop.MakeProp(p.Imply(p)))

	// Manual user-named checkpoint first.
	userCpID, err := e.Checkpoint(ctx, info.ID, "user-snapshot")
	require.NoError(t, err)

	// Now fire more ApplyStep calls than cap. Each successful apply creates
	// an auto checkpoint; only auto_* entries should be evicted.
	for i := 0; i < 4; i++ {
		v := ext.Var(ext.TermName(fmt.Sprintf("w%d", i)), core.TypeBool())
		s.AddGoal(prop.MakeProp(v.Imply(v)))
		state, _ := e.InspectState(ctx, info.ID)
		g := state.Goals[len(state.Goals)-1]
		_, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: g.ID,
			Tactic: TacticReq{Type: "auto"},
		})
		require.NoError(t, err)
	}

	list, err := e.ListCheckpoints(ctx, info.ID)
	require.NoError(t, err)

	// The user-named checkpoint must still be present.
	foundUser := false
	autoCount := 0
	for _, ci := range list {
		if ci.ID == userCpID {
			foundUser = true
			assert.Equal(t, "user-snapshot", ci.Name)
		}
		if strings.HasPrefix(ci.Name, autoCheckpointNamePrefix) {
			autoCount++
		}
	}
	assert.True(t, foundUser, "user-named checkpoint must not be evicted by LRU")
	assert.Equal(t, cap, autoCount, "auto_* count capped at %d despite user checkpoint", cap)

	// And Restore to the user checkpoint should still work.
	require.NoError(t, e.Restore(ctx, info.ID, userCpID))
}

// TestAutoCheckpoint_Disabled verifies that cap == 0 turns the feature off:
// no auto checkpoints are created no matter how many ApplyStep calls fire.
func TestAutoCheckpoint_Disabled(t *testing.T) {
	env := testEnv()
	e := newEngine(env, WithAutoCheckpoint(0))
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	s.AddGoal(prop.MakeProp(p.Imply(p)))
	q := ext.Var("q", core.TypeBool())
	s.AddGoal(prop.MakeProp(q.Imply(q)))

	state, _ := e.InspectState(ctx, info.ID)
	for _, g := range state.Goals {
		_, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: g.ID,
			Tactic: TacticReq{Type: "auto"},
		})
		require.NoError(t, err)
	}
	assert.Empty(t, autoCheckpointsSorted(t, e, info.ID),
		"cap==0 should suppress all auto checkpoints")
}

// TestAutoCheckpoint_DefaultIsOn verifies that a bare NewEngine (no option)
// enables auto-checkpointing at DefaultAutoCheckpointCap.
func TestAutoCheckpoint_DefaultIsOn(t *testing.T) {
	env := testEnv()
	e := newEngine(env)
	assert.Equal(t, DefaultAutoCheckpointCap, e.autoCheckpointCap,
		"default engine should have auto-checkpoint enabled at DefaultAutoCheckpointCap")

	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	p := ext.Var("p", core.TypeBool())
	s.AddGoal(prop.MakeProp(p.Imply(p)))

	applyAutoOnAllOpen(t, e, info.ID)
	assert.NotEmpty(t, autoCheckpointsSorted(t, e, info.ID),
		"default engine should auto-checkpoint on ApplyStep")
}

// TestAutoCheckpoint_OffOption: WithAutoCheckpointOff() is cap 0, the
// state TestAutoCheckpoint_Disabled runs.
func TestAutoCheckpoint_OffOption(t *testing.T) {
	assert.Equal(t, 0, newEngine(testEnv(), WithAutoCheckpointOff()).autoCheckpointCap)
}

// TestAutoCheckpoint_BatchApplyInnerSkipped verifies that BatchApply does
// NOT trigger auto-checkpoint creation on its inner iterations. Only
// ApplyStep (the RPC-boundary single-apply) should auto-checkpoint.
func TestAutoCheckpoint_BatchApplyInnerSkipped(t *testing.T) {
	env := testEnv()
	e := newEngine(env, WithAutoCheckpoint(10))
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	p := ext.Var("p", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.Imply(p)))

	// Sanity: no auto checkpoint yet.
	require.Empty(t, autoCheckpointsSorted(t, e, info.ID))

	// BatchApply in FirstSuccess mode with a couple of tactics. This is
	// one RPC call; even if it commits internally, our hook lives in
	// ApplyStep, not BatchApply, so no auto checkpoint should appear.
	_, err = e.BatchApply(ctx, info.ID, &BatchApplyRequest{
		GoalID: goalID,
		Mode:   FirstSuccess,
		Tactics: []TacticReq{
			{Type: "auto"},
		},
	})
	require.NoError(t, err)

	assert.Empty(t, autoCheckpointsSorted(t, e, info.ID),
		"BatchApply must NOT auto-checkpoint (only ApplyStep does)")
}

// TestAutoCheckpoint_FailedApplyDoesNotCheckpoint verifies that a failed
// tactic (returning !Success) does not create an auto checkpoint — the
// early-return path in ApplyStep skips the hook. The pre-apply snapshot
// (ensurePreApplyCheckpointLocked) is taken before the attempt and
// holds the unchanged state, so it alone may be present.
func TestAutoCheckpoint_FailedApplyDoesNotCheckpoint(t *testing.T) {
	env := testEnv()
	e := newEngine(env, WithAutoCheckpoint(10))
	ctx := context.Background()

	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Use a non-trivial goal so "auto" alone does not close it. If auto
	// happens to close the goal, the test still passes (we just assert
	// that unsuccessful applies do not add checkpoints — one successful
	// apply is fine).
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	goalID := s.AddGoal(prop.MakeProp(p.Imply(q)))

	// Deliberately-broken tactic: "known" without a valid key. This
	// should fail with Success:false.
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: goalID,
		Tactic: TacticReq{Type: "known", LemmaKey: "definitely_not_a_real_key_xxx"},
	})
	require.NoError(t, err)
	require.False(t, res.Success, "known with bogus key should fail")
	// The pre-apply snapshot (auto_0, the state BEFORE the attempt —
	// which is still the state) is the only checkpoint: a failed apply
	// takes no post-apply one.
	for _, ci := range autoCheckpointsSorted(t, e, info.ID) {
		assert.Equal(t, "auto_0", ci.Name, "failed ApplyStep must not create a post-apply auto checkpoint")
	}
}

// TestAutoCheckpoint_PreApplySnapshot: the state before the FIRST apply
// is held by auto_0, so a first move taken the wrong way restores; an
// add-goal after applies outdates the newest snapshot, and the next
// apply refreshes it under the same name before committing, so the
// added section survives a restore to it.
func TestAutoCheckpoint_PreApplySnapshot(t *testing.T) {
	env := testEnv()
	e := newEngine(env, WithAutoCheckpoint(10))
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	p := ext.Var("p", core.TypeBool())
	trivial := prop.MakeProp(p.Imply(p))
	first := s.AddGoal(trivial)
	require.Empty(t, autoCheckpointsSorted(t, e, info.ID), "nothing is snapshotted before the first apply")

	_, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: first, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	names := func() []string {
		var out []string
		for _, ci := range autoCheckpointsSorted(t, e, info.ID) {
			out = append(out, ci.Name)
		}
		return out
	}
	assert.Equal(t, []string{"auto_0", "auto_1"}, names(), "the first apply takes auto_0 before it and auto_1 after")

	// Restoring auto_0 undoes the first move: the goal is open again.
	var auto0 string
	for _, ci := range autoCheckpointsSorted(t, e, info.ID) {
		if ci.Name == "auto_0" {
			auto0 = ci.ID
		}
	}
	require.NoError(t, e.Restore(ctx, info.ID, auto0))
	state, err := e.InspectState(ctx, info.ID)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1, "the first apply is undone")

	// An apply from the restored state: auto_0 still holds it, so it is
	// kept, and the apply's own snapshot is auto_2.
	_, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	assert.Equal(t, []string{"auto_0", "auto_1", "auto_2"}, names())

	// A section added now is in no snapshot; the next apply refreshes
	// auto_2 to include it, so restoring auto_2 keeps the section.
	q := ext.Var("q", core.TypeBool())
	second := s.AddGoal(prop.MakeProp(q.Imply(q)))
	before := autoCheckpointsSorted(t, e, info.ID)
	_, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: second, Tactic: TacticReq{Type: "auto"}})
	require.NoError(t, err)
	after := autoCheckpointsSorted(t, e, info.ID)
	assert.Equal(t, []string{"auto_0", "auto_1", "auto_2", "auto_3"}, names())
	var stale, fresh string
	for _, ci := range before {
		if ci.Name == "auto_2" {
			stale = ci.ID
		}
	}
	for _, ci := range after {
		if ci.Name == "auto_2" {
			fresh = ci.ID
		}
	}
	require.NotEqual(t, stale, fresh, "auto_2 was replaced by a snapshot that holds the added section")
	require.NoError(t, e.Restore(ctx, info.ID, fresh))
	require.Len(t, s.sections, 2, "the section added before apply 3 survives a restore to auto_2")
}
