package engine

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// A case_split on a term that is the goal's conclusion, or its
// negation, does not apply, and the response says so: success false
// and a diagnostic naming the no-op and the move to make instead. A
// client that reads success alone sees the refusal; nothing about the
// goal changes.
func TestApplyStep_CaseSplitOnTheConclusionIsRefusedWithTheReason(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	p := ext.Var("p", core.TypeBool())
	q := ext.Var("q", core.TypeBool())
	for _, tc := range []struct {
		goal core.Prop
		want string
	}{
		{prop.MakeProp(q, p), "the (positive) term q is already the goal's conclusion — the split is a no-op"},
		{prop.MakeProp(ext.Not(q), p), "the goal's conclusion is ¬q — the split is a no-op"},
	} {
		goalID := s.AddGoal(tc.goal)
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "case_split", Const: ext.PrintTerm(q)},
		})
		require.NoError(t, err)
		require.False(t, res.Success, "the split on the conclusion applied")
		require.Len(t, res.Diagnostics, 1)
		require.Contains(t, res.Diagnostics[0].Message, tc.want)
		require.Equal(t, goalID, res.Diagnostics[0].GoalID)
	}
}
