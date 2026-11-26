package proof

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"
	"go.uber.org/goleak"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
)

// denoteThenBasicLeaf is a leaf the conditioning stage denotes and then
// settles: its set-builder is named, and the Basic() after the denote
// splits the disjunction the hypotheses carry.
func denoteThenBasicLeaf(t *testing.T) Prop {
	t.Helper()
	return prop.MakeProp(
		parseMotiveRedex(t, "R(h, {x:num | P(x)})"),
		[]core.Term{
			parseMotiveRedex(t, "P(0) ∨ P(1)"),
			parseMotiveRedex(t, "fin({x:num | P(x)})"),
		}...)
}

// TestConditionLeaf_BasicAfterDenoteRunsUnderTheContext: the Basic() the
// conditioning stage runs after a denote runs under the door's context.
// Under one that never ends it runs to its fixpoint and the stage
// reports no cut; under one that is done it is abandoned, the leaf is
// left as the denote left it, and the stage names the cut.
func TestConditionLeaf_BasicAfterDenoteRunsUnderTheContext(t *testing.T) {
	defer goleak.VerifyNone(t)
	opts := conditionOpts{denote: true}

	whole := CreateGoalStack(denoteThenBasicLeaf(t))
	c := &conditioner{env: makeStepTestEnv(), ctx: t.Context(), s4: &byS4State{}}
	c.conditionLeaf(whole, opts)
	require.Empty(t, c.cut, "the stage ran to its end")
	settled := byWorkingLeaves(whole, nil)
	require.Len(t, settled, 2, "Basic() splits the disjunction after the denote; open:\n%s", openLeaves(whole))

	done, cancel := context.WithCancel(t.Context())
	cancel()
	stopped := CreateGoalStack(denoteThenBasicLeaf(t))
	c = &conditioner{env: makeStepTestEnv(), ctx: done, s4: &byS4State{}}
	c.conditionLeaf(stopped, opts)
	require.Equal(t, "inside the conditioning stage's Basic(), after its denote", c.cut)
	left := byWorkingLeaves(stopped, nil)
	require.Len(t, left, 1, "an abandoned Basic() leaves the leaf as the denote left it; open:\n%s", openLeaves(stopped))
	require.NotEqual(t, denoteThenBasicLeaf(t).AlphaKey(), left[0].Goal.AlphaKey(), "the denote fired before the cut")

	// The next leaf the conditioner is run on starts with no cut.
	c.ctx = t.Context()
	c.conditionLeaf(CreateGoalStack(denoteThenBasicLeaf(t)), opts)
	require.Empty(t, c.cut)
}

// TestAutoConditionedRefute_DeclinesACutStage: the auto door's
// conditioned attempt, its stage cut by a done context, declines the
// leaf and does not go on to close the half-conditioned one.
func TestAutoConditionedRefute_DeclinesACutStage(t *testing.T) {
	defer goleak.VerifyNone(t)
	done, cancel := context.WithCancel(t.Context())
	cancel()
	root := CreateGoalStack(denoteThenBasicLeaf(t))
	ok, _ := autoConditionedRefute(makeStepTestEnv(), done, root)
	require.False(t, ok)
	require.False(t, root.Proved())
}

// TestByClosesUnderBasic_ReadsOneLeafOffTheTree: the MISS diagnostic's
// oracle answers for the By's one open leaf and leaves the tree as it
// was; a leaf Basic() only splits is not closed by it.
func TestByClosesUnderBasic_ReadsOneLeafOffTheTree(t *testing.T) {
	defer goleak.VerifyNone(t)
	root := CreateGoalStack(denoteThenBasicLeaf(t))
	require.False(t, byClosesUnderBasic(t.Context(), root, nil))
	left := byWorkingLeaves(root, nil)
	require.Len(t, left, 1, "the oracle runs no step on the By's tree")
	require.Equal(t, denoteThenBasicLeaf(t).AlphaKey(), left[0].Goal.AlphaKey())

	done, cancel := context.WithCancel(t.Context())
	cancel()
	closes := CreateGoalStack(alphaHypGoal(t))
	require.True(t, byClosesUnderBasic(t.Context(), closes, nil))
	require.False(t, closes.Proved(), "the oracle runs no step on the By's tree")
	require.True(t, byClosesUnderBasic(done, CreateGoalStack(alphaHypGoal(t)), nil),
		"a leaf closed by its first step is closed before the deadline is polled")
}
