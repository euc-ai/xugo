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

// A session claim reads its type positions against the registry's type
// vocabulary: set(τ) is τ → bool, a type no registered constant
// mentions is refused at the parse, and a set(…) binder applied as a
// function is refused too.
func TestAssertClaimText_TypeVocabulary(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)
	x := ext.Var("x", ext.NumType)
	goalID := s.AddGoal(prop.MakeProp(core.Eq(x, x)))

	assertClaim := func(claim string) *StepResult {
		t.Helper()
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
			GoalID: goalID,
			Tactic: TacticReq{Type: "assert", ClaimText: claim},
		})
		require.NoError(t, err)
		return res
	}

	res := assertClaim("∀n:nat. n = n")
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, `unknown type "nat"`)

	res = assertClaim("∀s:set(num). s(x)")
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	assert.Contains(t, res.Diagnostics[0].Message, "a set is used with ∈")

	// Last: an accepted assert opens the claim beside the goal.
	res = assertClaim("∀s:set(num). ∀n:num. n ∈ s ⇒ n ∈ s")
	require.True(t, res.Success, "set(num) must parse: %v", res.Diagnostics)
}
