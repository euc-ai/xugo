package engine

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
)

// TestSetDriver_DeMorganBothDoors: the de Morgan leaf
// `⋃T ∖ ⋂f = ⋃image(λc. ⋃T ∖ c, f)` closes through both doors of the
// membership-mode set driver in an unbound session — the session `by
// {settac:true}` with no premises and the bare `set_tac` — each in a
// session of its own. Run with -count=N to repeat the measurement.
func TestSetDriver_DeMorganBothDoors(t *testing.T) {
	const goal = "∀T:set(set(A)). ∀f:set(set(A)). ⋃T ∖ ⋂f = ⋃image(λc:set(A). ⋃T ∖ c, f)"
	doors := []struct {
		name   string
		tactic TacticReq
	}{
		{"by_settac", TacticReq{Type: "by", Settac: true}},
		{"set_tac", TacticReq{Type: "set_tac"}},
	}
	for _, door := range doors {
		t.Run(door.name, func(t *testing.T) {
			e := newEngine(statedSessionEnv())
			ctx := context.Background()
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			addTextGoal(t, s, goal)
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
			state, err := e.InspectState(ctx, s.ID)
			require.NoError(t, err)
			require.Len(t, state.Goals, 1)
			t0 := time.Now()
			res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: door.tactic})
			require.NoError(t, err)
			require.True(t, res.Success, "%s left the leaf open; diagnostics: %v", door.name, res.Diagnostics)
			require.True(t, s.sections[0].root.Proved())
			t.Logf("%s closed in %v", door.name, time.Since(t0).Round(time.Millisecond))
		})
	}
}
