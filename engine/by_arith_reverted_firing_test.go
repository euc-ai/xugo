package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestByArith_ContradictionBehindARevertedFiring drives `by {arith:true}`
// on a goal one of whose conjuncts, `p ≠ 2`, closes by contradiction: the
// context holds `nat_odd(p₀)`, `p₀ = 2` and `1 = nat_mod(p₀, 2)`, and the
// contradiction shows as that last hypothesis rewriting to ⊥ once the
// redundant `nat_odd(p₀)`, which implies it, is dropped. Ahead of the drop
// stands a rewrite the mop-up undoes every round, `2 ∣ n₀` to
// `2 ∣ (2 * m₀)` and back by `n₀ = 2 * m₀`; the rounds pass it over. End
// to end on the corpus and the production bundles, the premises those of a
// chapter's step.
func TestByArith_ContradictionBehindARevertedFiring(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	const stmt = "∀n p m:num. n = p * m ⇒ (nat_prime(p) ∧ p ∣ n) ⇒ (nat_odd(p) ∧ nat_odd(m)) ⇒ " +
		"nat_prime(p) ∧ p ≠ 2 ∧ nat_odd(p) ∧ nat_odd(m) ∧ n = p * m ∧ m < n"
	parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors, "add-goal %q", stmt)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range []string{"strip_quant", "strip_imp", "strip_imp", "strip_imp"} {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err, "strip %s", typ)
		require.Len(t, res.Produced, 1, "strip %s", typ)
		gid = res.Produced[0].GoalID
	}
	idx := func(i int) *int { return &i }
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "by", Arith: true,
		ByHyps: []ByHypSpec{{HypIndex: idx(0)}, {HypIndex: idx(1)}, {HypIndex: idx(2)}},
		WithLemmas: []LemmaWithSpec{
			{Key: "nat_parity.OddIffModTwoOne", TermSpecialize: map[string]string{"n": "p₀"}},
			{Key: "nat_parity.OddIffModTwoOne", TermSpecialize: map[string]string{"n": "m₀"}},
			{Key: "nat_prime.PrimeAtLeastTwo", TermSpecialize: map[string]string{"p": "p₀"}},
			{Key: "nat_order.LessEqMulMono", TermSpecialize: map[string]string{"m": "m₀", "n": "2", "p": "p₀"}},
		},
	}})
	require.NoError(t, err)
	require.Equal(t, "close", res.Effect, "the close stopped behind the reverted firing: %v", res.Diagnostics)
}
