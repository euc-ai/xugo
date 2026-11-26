package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/require"
)

// TestByArith_ContradictionBehindAnUndoneConclusionRewrite drives
// `by {arith:true}` on a leaf whose context is contradictory in a way
// only a hypothesis firing shows — `nat_odd(p₀)`, `p₀ = 2` and
// `1 = nat_mod(p₀, 2)`, the last rewriting to ⊥ once the first is dropped
// — and whose conclusion holds a product under an absolute value. The
// conclusion's rewrite, `|x * y|` to `|x| * |y|`, decides nothing, and
// the mop-up folds it back by the bridge equation the firing leaves
// beside it; fired every round it would keep every hypothesis from its
// turn. The rounds pass it over, and the close is the one the same
// context gives with nothing to push in the conclusion. Over ℝ, where the
// law is ℝ's own, and over ℂ, where it is the modulus's.
func TestByArith_ContradictionBehindAnUndoneConclusionRewrite(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	idx := func(i int) *int { return &i }
	for _, stmt := range []string{
		"∀p:num. ∀x y c:real. nat_odd(p) ∧ p = 2 ∧ 1 = nat_mod(p, 2) ⇒ |x| * |y| ≤ c",
		"∀p:num. ∀x y c:real. nat_odd(p) ∧ p = 2 ∧ 1 = nat_mod(p, 2) ⇒ |x * y| ≤ c",
		"∀p:num. ∀x y:complex. ∀c:real. nat_odd(p) ∧ p = 2 ∧ 1 = nat_mod(p, 2) ⇒ |x * y| ≤ c",
	} {
		t.Run(stmt, func(t *testing.T) {
			info, err := e.CreateSession(ctx)
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
				ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
				Syntax: constSyntax(),
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
			res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid,
				Tactic: TacticReq{Type: "by", Arith: true, ByHyps: []ByHypSpec{{HypIndex: idx(0)}}}})
			require.NoError(t, err)
			require.Equal(t, "close", res.Effect, "the close stopped behind the conclusion's undone rewrite: %v", res.Diagnostics)
		})
	}
}

// TestArithMove_NoProgressOnAFiringTheTidyTakesBack: the one-shot arith
// move on `⊢ |x * y| ≤ c`, which nothing decides. Its first pass leaves
// the bridge equation `|x * y| = |x| * |y|` among the hypotheses and the
// conclusion as it was, the tidy having folded the rewrite back; that is
// a changed leaf, and progress. From then on the firing is taken back
// whole: the move reports no progress and leaves the node the bare leaf
// it was handed, where it used to commit two steps that changed nothing
// and report progress on every pass.
func TestArithMove_NoProgressOnAFiringTheTidyTakesBack(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus and the production bundles")
	}
	byArithEngine(t)
	for _, state := range []string{
		"x_0:real, y_0:real, c_0:real ⊢ real_abs(x₀ * y₀) ≤ c₀",
		"x_0:complex, y_0:complex, c_0:real ⊢ complex_abs(x₀ * y₀) ≤ c₀",
	} {
		t.Run(state, func(t *testing.T) {
			res := dsl.ParsePropTextInScope(state, &dsl.ParseScope{Syntax: constSyntax(), ConstResolver: registryConstResolver})
			require.Empty(t, res.Errors, "parse: %v", res.Errors)
			node := proof.CreateGoalStack(res.Prop)

			require.True(t, proof.ApplyArithSimplify(t.Context(), node), "the first pass adds the bridge")
			leaves := node.UnsolvedLeaves()
			require.Len(t, leaves, 1)
			first := leaves[0]
			require.Equal(t, 1, first.Goal.NumHyps(), "the bridge equation is the one hypothesis")
			require.True(t, first.Goal.Conclusion().AlphaEquals(res.Prop.Conclusion()), "the conclusion is as it was")

			require.False(t, proof.ApplyArithSimplify(t.Context(), first), "the second pass changes nothing and says so")
			again := node.UnsolvedLeaves()
			require.Len(t, again, 1)
			require.Same(t, first, again[0], "the leaf handed over is still the open leaf: no step was committed on it")
		})
	}
}
