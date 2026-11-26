package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A tactic's parameter term is read in the goal's own dialect: an
// operator at a structure's carrier lowers to the field of the record
// the resident structure fact is stated at, exactly as `parse-term`
// reads the same goal — `y + x` under a resident `comm_ring(R)` is
// `R.add(y, x)`, one dialect for the goal and its parameters.
func TestTacticParam_OperatorLowersOffResidentStructure(t *testing.T) {
	scope := &dsl.ParseScope{ConstResolver: registryConstResolver, Syntax: constSyntax()}
	// The conclusion is deliberately not a ring law, so nothing closes
	// the goal before the step under test runs.
	res := dsl.ParsePropTextInScope(
		"∀R:ring_ops(A). ∀x y:A. comm_ring(R) ⇒ R.add(x, y) = R.add(y, R.mul(R.one, x))", scope)
	require.Empty(t, res.Errors, "the goal text must parse: %v", res.Errors)

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(res.Prop)

	// Open the binders and make the structure fact resident.
	for i := 0; i < 8; i++ {
		entry := s.goalIndex[goalID]
		if ext.MatchesFORALL(entry.node.Goal.Conclusion()).IsZero() {
			break
		}
		step, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "strip_quant"}})
		require.NoError(t, err)
		require.True(t, step.Success)
		goalID = s.focusedGoalIDForTest()
		require.NotEmpty(t, goalID)
	}
	step, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "strip_imp"}})
	require.NoError(t, err)
	require.True(t, step.Success)
	focused := s.focusedGoalIDForTest()
	require.NotEmpty(t, focused, "the goal must still be open after the fact is made resident")

	// The middle term spelled with the OPERATOR, not the component.
	step, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: focused, Tactic: TacticReq{Type: "trans", Const: "y + x"}})
	require.NoError(t, err, "`y + x` must lower off the resident comm_ring, as parse-term does")
	assert.True(t, step.Success, "trans at `y + x` did not succeed: %+v", step)
}

// `by` reads by_hyps; keep_hyp_indices / drop_hyp_indices are
// auto_with's. They are declared on the shared tactic struct, so the
// wire door cannot refuse them by name — `by` refuses them itself
// instead of dropping them and blaming a missing premise one failure
// later.
func TestBy_RefusesAutoWithFields(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	target := prop.MakeProp(P.Apply(x).Core(), P.Apply(x).Core())
	zero := 0
	err := applyToSingleGoalExpectErr(t, target, TacticReq{
		Type:           "by",
		ByHyps:         []ByHypSpec{{HypIndex: &zero}},
		KeepHypIndices: []int{0},
	})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "auto_with")
	assert.Contains(t, err.Error(), "by_hyps")
}

// A PROVED section is found by the identity the sibling auto-match
// closes on; an unproved one is not a candidate.
func TestProvedSectionStating(t *testing.T) {
	x := ext.Var("x", core.TypeA())
	P := ext.Var("P", core.MakeFun(core.TypeA(), core.TypeBool()))
	target := prop.MakeProp(P.Apply(x).Core(), P.Apply(x).Core())

	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	goalID := s.AddGoal(target)
	assert.Equal(t, -1, s.ProvedSectionStating(target), "an open section is not a candidate")

	step, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: goalID, Tactic: TacticReq{Type: "assumption"}})
	require.NoError(t, err)
	require.True(t, step.State.Complete)
	assert.Equal(t, 0, s.ProvedSectionStating(target), "the proved section states the goal")
}

// An apply with no goal_id names the missing field, instead of
// reporting the empty string as a goal it could not find.
func TestApply_RequiresGoalID(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	_, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{Tactic: TacticReq{Type: "strip_quant"}})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "requires goal_id")
	assert.Contains(t, err.Error(), "focused_goal_id")
}
