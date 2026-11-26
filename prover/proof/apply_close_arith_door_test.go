// apply_close_arith_door_test.go — the apply rung's arithmetic door
// (closeByArith) decides an antecedent or leaves it as it found it: the
// rungs after it run on the same bare leaf. An antecedent whose leaf the
// decider only simplifies is then closed by the head that applies to
// it; before, the door committed the simplification on the leaf and the
// head's commit ran on a node that already held a ministep.
package proof

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/require"
)

// The head `n + 1 ≤ n + 1 ∧ (∀i. i ≤ n + 1 ∧ ¬(i = n + 1) ⇒ P(i)) ⇒ Q`
// applies to the goal Q. Its first antecedent the decider decides; the
// second opens to the leaf `i ≤ n + 1, ¬(i = n + 1), … ⊢ P(i)`, where
// the decider only folds the `n + 1 ≤ n + 1` inside the resident head
// (P(i) is not arithmetic), and which the resident `∀i. P(i)` closes.
func TestApplyClose_ArithDoorThatOnlySimplifiesLeavesTheLeafToTheHeads(t *testing.T) {
	res := dsl.ParsePropTextInScope("(∀i:num. P(i)) ⇒ (n + 1 ≤ n + 1 ∧ (∀i:num. i ≤ n + 1 ∧ ¬(i = n + 1) ⇒ P(i)) ⇒ Q) ⇒ Q", lawScope())
	require.Empty(t, res.Errors, "%v", res.Errors)
	sec := NewScript(makeStepTestEnv()).Section(res.Prop)
	sec.Do(StripImp())
	sec.Do(StripImp())
	var claims []*GoalStackNode
	closed, miss := applyClose(sec, &claims, nil, rungOpts{depth: antecedentApplies, arith: true})
	require.True(t, closed, "the head applies and the context closes its antecedent: %s", miss)
	require.True(t, sec.Proved())
}

// TestApplyClose_ArithDoorIsCutOffByTheDoorsContext: the decision the
// arithmetic door runs on an antecedent polls the door's context. The
// head `n ≤ m ⇒ Q` applies to the goal Q, and its antecedent is not in
// the context as written: the decider proves it from `n + 1 ≤ m`. Under
// a context that is done the trial raises a utils.Cut inside the
// decision and the leaf is left as it was, open and with no step
// committed; under one that never ends, and with none, the rung closes
// the leaf. A door that decided under no context closed it in each
// case, however long the decision ran.
func TestApplyClose_ArithDoorIsCutOffByTheDoorsContext(t *testing.T) {
	leaf := func() *GoalStackNode {
		res := dsl.ParsePropTextInScope("n + 1 ≤ m ⇒ (n ≤ m ⇒ Q) ⇒ Q", lawScope())
		require.Empty(t, res.Errors, "%v", res.Errors)
		sec := NewScript(makeStepTestEnv()).Section(res.Prop)
		sec.Do(StripImp())
		sec.Do(StripImp())
		return sec.UnsolvedLeaves()[0]
	}
	rung := func(ctx context.Context) rungOpts {
		return rungOpts{depth: antecedentApplies, arith: true, ctx: ctx}
	}

	done, cancel := context.WithCancel(t.Context())
	cancel()
	n := leaf()
	var claims []*GoalStackNode
	raised := func() (r any) {
		defer func() { r = recover() }()
		applyClose(n, &claims, nil, rung(done))
		return nil
	}()
	cut, isCut := utils.AsCut(raised)
	require.True(t, isCut, "the rung under a done context raised %v", raised)
	require.Contains(t, cut.Where, "inside an arith decision")
	require.ErrorIs(t, cut.Cause, context.Canceled)
	require.False(t, n.Proved())
	require.Empty(t, n.Children(), "a cut trial commits nothing on the leaf")

	for name, ctx := range map[string]context.Context{"a context that never ends": t.Context(), "no context": nil} {
		n := leaf()
		closed, miss := applyClose(n, &claims, nil, rung(ctx))
		require.True(t, closed, "%s: the decider supplies the antecedent: %s", name, miss)
		require.True(t, n.Proved(), name)
	}
}
