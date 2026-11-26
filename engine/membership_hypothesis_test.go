package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext/prop"
)

// The hypothesis-side moves read a membership in a set-builder through
// its predicate where the hypothesis is not the shape as written:
// `split_conj {hyp_index}` splits `a ∈ {y | P(y) ∧ K(y) ∧ y < n}` into
// its three conjuncts at the point, `strip_quant {hyp_index}` opens the
// ∃ of `a ∈ {y | ∃k. …}`, `split_disj {hyp_index}` splits the ∨ of
// `a ∈ {y | P(y) ∨ K(y)}`. Each renders as the Go it twins and the
// emitted member replays.
func TestMembershipHypothesis_SessionMovesReadThePredicate(t *testing.T) {
	zero := 0
	t.Run("split_conj", func(t *testing.T) {
		e, s := boundSession(t, "sets/set_basic")
		addTextGoal(t, s, "∀a n:num. ∀P K:num → bool. a ∈ {y:num | P(y) ∧ K(y) ∧ y < n} ⇒ K(a) ∨ a = n")
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "split_conj", HypIndex: &zero})
		require.Len(t, res.Produced, 1)
		assert.Equal(t, 3, res.Produced[0].Changes.HypsAdded, "one hypothesis per conjunct at the point")
		k := hypIndexPrinting(t, e, s.ID, "K₀(a₀)")
		hypIndexPrinting(t, e, s.ID, "P₀(a₀)")
		hypIndexPrinting(t, e, s.ID, "a₀ < n₀")
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(k)}, ByShape: &ByShapeReq{Normalized: true}})
		src := emitInto(t, e, s, "zzmembershipconjuncts", "ZzMembershipConjuncts")
		assert.Contains(t, src, ".Conjuncts(", "the move renders as a.Conjuncts:\n%s", src)
		replayEmitted(t, "zzmembershipconjuncts", "ZzMembershipConjuncts", src)
	})
	t.Run("strip_quant", func(t *testing.T) {
		e, s := boundSession(t, "sets/set_basic")
		addTextGoal(t, s, "∀a:num. ∀P K:num → bool. ∀f:num → num. a ∈ {y:num | ∃k:num. P(k) ∧ y = f(k)} ⇒ (∀k:num. P(k) ⇒ K(f(k))) ⇒ K(a)")
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		member := hypIndexPrinting(t, e, s.ID, "a₀ ∈ {y | ∃k.(P₀(k) ∧ (y = f₀(k)))}")
		res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant", HypIndex: &member})
		require.Len(t, res.Produced, 1)
		state, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		assert.False(t, strings.Contains(soleGoalText(t, e, s.ID), "∈ {"), "the membership is opened")
		instance := hypIndexWithPrefix(t, e, s.ID, state.Goals[0].ID, "P₀(k")
		law := hypIndexWithPrefix(t, e, s.ID, state.Goals[0].ID, "∀k")
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(law), hyp(instance)}})
		src := emitInto(t, e, s, "zzmembershipunpack", "ZzMembershipUnpack")
		replayEmitted(t, "zzmembershipunpack", "ZzMembershipUnpack", src)
	})
	t.Run("split_disj", func(t *testing.T) {
		e, s := boundSession(t, "sets/set_basic")
		addTextGoal(t, s, "∀a:num. ∀P K:num → bool. ∀Q:bool. a ∈ {y:num | P(y) ∨ K(y)} ⇒ (∀y:num. P(y) ⇒ Q) ⇒ (∀y:num. K(y) ⇒ Q) ⇒ Q")
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
		for range 3 {
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		}
		member := hypIndexPrinting(t, e, s.ID, "a₀ ∈ {y | P₀(y) ∨ K₀(y)}")
		ctx := context.Background()
		state, err := e.InspectState(ctx, s.ID)
		require.NoError(t, err)
		res, err := applyAt(t, e, s.ID, state.Goals[0].ID, TacticReq{Type: "split_disj", HypIndex: &member})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
		require.Len(t, res.Produced, 2, "one branch per disjunct")
		for _, branch := range res.Produced {
			state, err := e.InspectState(ctx, s.ID)
			require.NoError(t, err)
			var premises []ByHypSpec
			for _, g := range state.Goals {
				if g.ID != branch.GoalID {
					continue
				}
				for i := range g.Statement.NumHyps() {
					premises = append(premises, hyp(i))
				}
			}
			closed, err := applyAt(t, e, s.ID, branch.GoalID, TacticReq{Type: "by", ByHyps: premises})
			require.NoError(t, err)
			require.True(t, closed.Success, "diagnostics: %v", closed.Diagnostics)
		}
		src := emitInto(t, e, s, "zzmembershipsplitdisj", "ZzMembershipSplitDisj")
		replayEmitted(t, "zzmembershipsplitdisj", "ZzMembershipSplitDisj", src)
	})
	t.Run("a reading that is not the shape is refused with the reading named", func(t *testing.T) {
		e, s := boundSession(t, "sets/set_basic")
		addTextGoal(t, s, "∀a:num. ∀P:num → bool. a ∈ {y:num | P(y)} ⇒ P(a) ∨ a = 0")
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
		state, err := e.InspectState(context.Background(), s.ID)
		require.NoError(t, err)
		res, err := applyAt(t, e, s.ID, state.Goals[0].ID, TacticReq{Type: "split_conj", HypIndex: &zero})
		require.NoError(t, err)
		require.False(t, res.Success)
		assert.Contains(t, res.Diagnostics[0].Message, "(a₀ ∈ {y | P₀(y)}) is not A ∧ B, nor is its reading P₀(a₀)")
	})
}

// A hyp_index past the goal's hypotheses is input from outside: refused
// by name, never a panic.
func TestSimpWith_HypIndexOutOfRangeIsAnError(t *testing.T) {
	e, s := boundSession(t, "sets/set_basic")
	addTextGoal(t, s, "∀s:set(A). s ⊆ s")
	zero := 0
	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	res, err := applyAt(t, e, s.ID, state.Goals[0].ID, TacticReq{Type: "simp_with", HypIndex: &zero,
		WithLemmas: []LemmaWithSpec{{Key: "set_basic.SubsetDef"}}})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	msg := res.Diagnostics[0].Message
	assert.False(t, strings.Contains(msg, "panic"), "a refusal, not a recovered panic: %s", msg)
	assert.Contains(t, msg, "simp_with hyp_index 0 out of range [0, 0)")
}

// soleGoalText is the session's sole open goal, printed.
func soleGoalText(t *testing.T, e *Engine, sid string) string {
	t.Helper()
	state, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	return prop.PrintProp(state.Goals[0].Statement)
}
