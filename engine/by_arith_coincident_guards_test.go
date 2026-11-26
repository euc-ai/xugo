package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestByArith_CoincidentSplitGuards drives `by {arith:true}` with a cited
// lemma on an odd number and a bound that is false at 1, end to end on the
// real corpus with the production bundles installed. The leaf stays open, so
// the rounds ground the lemma's recursion clause up the successors of n, and
// the decision of the atom `0 = nat_mod(n, 2)` runs with `0 ≠ 0` among its
// hypotheses, a split whose two guards are both `0 < 0`. The close answers
// as a goal the closer did not close, and no step of it is one the kernel
// layer refuses.
func TestByArith_CoincidentSplitGuards(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	const stmt = "∀n:num. nat_odd(n) ⇒ 2 ≤ n"
	parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors, "add-goal %q", stmt)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range []string{"strip_quant", "strip_imp"} {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err, "strip %s", typ)
		require.Len(t, res.Produced, 1, "strip %s", typ)
		gid = res.Produced[0].GoalID
	}
	hyp := 0
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "by", Arith: true,
		ByHyps:     []ByHypSpec{{HypIndex: &hyp}},
		WithLemmas: []LemmaWithSpec{{Key: "nat_parity.NatOdd"}},
	}})
	require.NoError(t, err)
	require.False(t, res.Success, "nat_odd(n) ⊢ 2 ≤ n closed, and it is false at n = 1")
	for _, d := range res.Diagnostics {
		require.NotContains(t, d.Message, "Should not happen", "the closer built a step the kernel layer refuses")
	}
}
