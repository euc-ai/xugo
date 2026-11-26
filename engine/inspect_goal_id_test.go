package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestInspect_GoalIDListsThatGoalAlone: with two open goals, an inspect
// naming one lists that goal alone under Goals — its hypotheses at
// goals[0] are the named goal's — while NumOpen stays the session's
// count; an inspect naming none lists both.
func TestInspect_GoalIDListsThatGoalAlone(t *testing.T) {
	P := ext.WrapTerm(ext.Var("P", core.MakeFun(TypeInd, core.TypeBool())))
	Q := ext.WrapTerm(ext.Var("Q", core.MakeFun(TypeInd, core.TypeBool())))
	R := ext.WrapTerm(ext.Var("R", core.MakeFun(TypeInd, core.TypeBool())))
	a := ext.Var("a", TypeInd)
	b := ext.Var("b", TypeInd)
	// P(a) ⊢ Q(a) and P(b), R(b) ⊢ Q(b): two hypothesis lists of
	// different length, so the named goal's list is told from the other's.
	narrow := prop.MakeProp(Q.Apply(a).Core(), P.Apply(a).Core())
	wide := prop.MakeProp(Q.Apply(b).Core(), P.Apply(b).Core(), R.Apply(b).Core())

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	narrowID := s.AddGoal(narrow)
	wideID := s.AddGoal(wide)

	all, err := e.Inspect(ctx, info.ID, &InspectRequest{})
	require.NoError(t, err)
	require.Len(t, all.Goals, 2, "no goal named: every open goal is listed")
	assert.Equal(t, 2, all.NumOpen)
	assert.Empty(t, all.FocusedGoalID)

	for _, want := range []struct {
		id   string
		hyps int
	}{{narrowID, 1}, {wideID, 2}} {
		res, err := e.Inspect(ctx, info.ID, &InspectRequest{GoalID: want.id})
		require.NoError(t, err)
		require.Len(t, res.Goals, 1, "goal %s named: it is listed alone", want.id)
		assert.Equal(t, want.id, res.Goals[0].ID)
		assert.Equal(t, want.id, res.FocusedGoalID)
		assert.Len(t, res.Goals[0].Hypotheses, want.hyps, "the listed hypotheses are the named goal's")
		assert.Equal(t, 2, res.NumOpen, "num_open stays the session's count")
	}
}
