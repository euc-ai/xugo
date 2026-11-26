package engine

import (
	"context"
	"fmt"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
)

// TestSetDriver_ProductSetInclusionUnderRecordProjection: the inclusion
// between two sets of products, `{R.mul(m, n) | m ∈ M ∧ n ∈ N} ⊆
// {R.mul(m, n) | m ∈ M' ∧ n ∈ N'}` from `M ⊆ M' ∧ N ⊆ N'`, closes under
// the session's `by {settac:true}` when the product is a record
// projection applied to the record variable, exactly as it does when the
// product is a function variable `f`. Each statement runs in a session
// of its own; the function-variable statement is the control.
func TestSetDriver_ProductSetInclusionUnderRecordProjection(t *testing.T) {
	const body = "∀M M' N N':set(A). M ⊆ M' ∧ N ⊆ N' ⇒ " +
		"{%[1]s(m, n) | m:A, n:A | m ∈ M ∧ n ∈ N} ⊆ {%[1]s(m, n) | m:A, n:A | m ∈ M' ∧ n ∈ N'}"
	cases := []struct {
		name      string
		statement string
	}{
		{"function variable", "∀f:(A → A → A). " + fmt.Sprintf(body, "f")},
		{"record projection", "∀R:ring_ops(A). " + fmt.Sprintf(body, "R.mul")},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			e := newEngine(statedSessionEnv())
			ctx := context.Background()
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			addDoorGoal(t, s, tc.statement)
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
			state, err := e.InspectState(ctx, s.ID)
			require.NoError(t, err)
			require.Len(t, state.Goals, 1)
			t0 := time.Now()
			res, err := e.ApplyStep(ctx, s.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: TacticReq{Type: "by", Settac: true}})
			require.NoError(t, err)
			require.True(t, res.Success, "by {settac:true} left the leaf open; diagnostics: %v", diagnosticMessages(res))
			require.True(t, s.sections[0].root.Proved())
			t.Logf("closed in %v", time.Since(t0).Round(time.Millisecond))
		})
	}
}
