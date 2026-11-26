package engine

// def_expand(iterated_op) on a goal whose fold summand carries a COND
// returns.
//
// The post-expansion residual is tidied by TrivialNormalize, which
// composes CondElimRewrite and CondSwapRewrite. The two feed each other
// by nesting — swap pushes a COND outward, elim eliminates one, and the
// rescan of either's output can expose a fresh redex for the other — and
// under the fold's λ a swap that fired on a COND whose condition the
// binder captures would never stop: the serve would grow until killed,
// taking every concurrent session with it. The swap declines there
// (condSwapRewriteImpl; ext/prop's TestCondSwap_UnderBinder_Terminates
// holds the rewrite itself), and this test holds the production shape
// that reaches it, through the session's move.
//
// The summand is spelled with the vector chapters' own constants.

import (
	"context"
	"github.com/euc-ai/xugo/library/registry"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/stretchr/testify/require"
)

// condFoldGoalText is the stripped form of the trigger goal — SpanMember's
// Kronecker combination, `COND(i = j, R.one, R.zero)` as the coefficient
// under the fold, the ring's fields spelled by their projections. Replacing
// the COND by the bare scalar `R.one` makes the same def_expand return in
// milliseconds on the unpatched engine, which is what isolates the COND as
// the load-bearing ingredient.
const condFoldGoalText = "R:ring_ops(var:A), e:(num → (num → var:A)), j:num, k:num, j < k, comm_ring(R) ⊢ e(j) = iterated_op(vec_add(ring_add(R)), {i:num | i < k}, λi:num. vec_scalar_mul(ring_mul(R), COND(i = j, ring_one(R), ring_zero(R)), e(i)))"

func TestDefExpandIterate_CondSummandTerminates(t *testing.T) {
	for _, c := range []string{"iterated_op", "vec_add", "vec_scalar_mul", "comm_ring"} {
		_, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(c))
		require.True(t, ok, "%s is not minted: the fixture names a constant the corpus no longer has", c)
	}
	e, s, sid := ematchSessionWithGoal(t, condFoldGoalText)
	leafID := ematchOpenLeafID(t, s)

	// The divergence was unbounded allocation inside one call, so a
	// deadline on the CALL is the assertion — not on the test binary,
	// which `go test -timeout` would kill without a failing test name.
	type result struct {
		out *StepResult
		err error
	}
	done := make(chan result, 1)
	go func() {
		out, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{
			GoalID: leafID, Tactic: TacticReq{Type: "def_expand", Const: "iterated_op"}})
		done <- result{out, err}
	}()
	select {
	case r := <-done:
		require.NoError(t, r.err)
		require.NotNil(t, r.out)
		// Whether the residual stays open or the expansion closes the goal
		// is not the property under test; RETURNING is.
	case <-time.After(30 * time.Second):
		t.Fatal("def_expand(iterated_op) did not return within 30s on a fold whose summand carries a COND — " +
			"the TrivialNormalize COND rewrite is diverging")
	}
}
