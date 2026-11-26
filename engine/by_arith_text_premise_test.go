package engine

import (
	"context"
	"fmt"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// sphereHornFillText is the statement of homotopy_group.SphereHornFill as
// a session spells it in a `by` premise's text slot.
const sphereHornFillText = "∀X:simplicial_ops(A). kan_complex(X) ⇒ ∀x₀:A. ∀n k:num. ∀y:(num → A). " +
	"k ≤ n + 1 ∧ (∀i:num. i ≤ n + 1 ∧ ¬(i = k) ⇒ y(i) ∈ simplicial_sphere(X, x₀, n)) ⇒ " +
	"∃x:A. x ∈ simplicial_simplices(X, n + 1) ∧ faces_filler(simplicial_face(X), n, horn_faces(n, k), y, x)"

func goalIDs(state *StateView) []string {
	ids := make([]string, len(state.Goals))
	for i, g := range state.Goals {
		ids[i] = g.ID
	}
	return ids
}

func describeGoal(g GoalView) string {
	var b strings.Builder
	for i, h := range g.Hypotheses {
		fmt.Fprintf(&b, "  hyp %d: %s\n", i, ext.PrintTerm(h))
	}
	fmt.Fprintf(&b, "  ⊢ %s", prop.PrintProp(g.Statement))
	return b.String()
}

// TestBy_ArithWithATextPremiseAtAKanComplexLeaf replays the session
// moves that reach the leaf `… ⊢ ∃w. w ∈ X₀(n₀ + 1) ∧ faces_filler(d₀, n₀,
// horn_faces(n₀, n₀ + 1), h, w)` under a Kan complex, then the `by {arith}` the session
// answered with a bare "Should not happen": SphereHornFill as a text
// premise at k := n₀ + 1, y := h, with the kan_complex fact and the
// sphere fact resident. The apply rung applies the premise and supplies
// its antecedent `∀i. i ≤ n₀ + 1 ∧ ¬(i = n₀ + 1) ⇒ h(i) ∈ …` through the
// arithmetic door, which folds the `n₀ + 1 ≤ n₀ + 1` inside the resident
// head without deciding the leaf; the rung then closes the leaf by the
// sphere fact. The text premise is certified by no entry, which the
// answer names; the same premise by key closes the goal.
func TestBy_ArithWithATextPremiseAtAKanComplexLeaf(t *testing.T) {
	e, s := boundSession(t, "simplicial/homotopy_group")
	statement := "∀X:simplicial_ops(A). kan_complex(X) ⇒ ∀x₀:A. ∀n:num. x₀ ∈ X.simplices(0) ∧ 0 < n ⇒ " +
		"∀x:A. x ∈ simplicial_sphere(x₀, n) ⇒ ∃w:A. w ∈ X.simplices(n + 1) ∧ (∀i:num. i + 1 < n ⇒ X.d(n + 1, i, w) = base_simplex(x₀, n)) ∧ " +
		"X.d(n + 1, n - 1, w) = x ∧ X.d(n + 1, n, w) = base_simplex(x₀, n)"
	parsed := dsl.ParsePropTextInScope(statement, s.StatementDoorScope())
	require.Empty(t, parsed.Errors, "add-goal %q", statement)
	s.mu.Lock()
	s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for range 3 {
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
		applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	}
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "let", Const: "λi:num. COND(i = n₀ - 1, x₁, base_simplex(simplicial_degeneracy(X₀), x₀, n₀))", Name: "h"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "∀i:num. h(i) ∈ simplicial_sphere(X₀, x₀, n₀)"})
	// The claim: h by its definition, then the base sphere under the Kan
	// complex's simplicial set.
	claim := func(g core.Prop) bool { return strings.HasPrefix(ext.PrintTerm(g.Conclusion()), "∀i") }
	applyTo(t, e, s, claim, TacticReq{Type: "rw", HypIndex: hypAt(t, e, s, claim, "h = ")})
	applyTo(t, e, s, claim, TacticReq{Type: "by",
		WithLemmas: []LemmaWithSpec{{Key: "homotopy_group.BaseSphere", TermSpecialize: map[string]string{"n": "n₀", "x₀": "x₀"},
			ReadAt: &ReadAtSpec{Key: "kan_complex.KanSimplicialSet", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, claim, "kan_complex(")}}}},
		ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, claim, "(x₀ ∈")}, {HypIndex: hypAt(t, e, s, claim, "x₁ ∈")}}})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert",
		ClaimText: "∃w:A. w ∈ simplicial_simplices(X₀, n₀ + 1) ∧ faces_filler(simplicial_face(X₀), n₀, horn_faces(n₀, n₀ + 1), h, w)"})
	// The leaf is the asserted filler claim, not the goal it was asserted
	// in: both conclude with ∃w, the claim alone spells faces_filler.
	leaf := func(g core.Prop) bool {
		c := ext.PrintTerm(g.Conclusion())
		return strings.HasPrefix(c, "∃w") && strings.Contains(c, "faces_filler")
	}

	state, err := e.InspectState(context.Background(), s.ID)
	require.NoError(t, err)
	for _, g := range state.Goals {
		t.Logf("goal %s:\n%s", g.ID, describeGoal(g))
	}

	witnesses := map[string]string{"X": "X₀", "x₀": "x₀", "n": "n₀", "k": "n₀ + 1", "y": "h"}
	premises := []ByHypSpec{{HypIndex: hypAt(t, e, s, leaf, "kan_complex(")}, {HypIndex: hypAt(t, e, s, leaf, "∀i")}}
	target := openGoalWhere(t, e, s, leaf)
	res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: target.ID, Tactic: TacticReq{Type: "by", Arith: true,
		ByHyps:     premises,
		WithLemmas: []LemmaWithSpec{{Text: sphereHornFillText, TermSpecialize: witnesses}}}})
	require.NoError(t, err)
	require.False(t, res.Success, "a text premise no entry certifies does not close the goal")
	answer := fmt.Sprint(res.Diagnostics)
	require.NotContains(t, answer, "Should not happen", "the answer is the author's, not an engine assertion")
	require.Contains(t, answer, "premise claim(s) did not certify", "the answer names the uncertified text premise")

	res, err = e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{GoalID: target.ID, Tactic: TacticReq{Type: "by", Arith: true,
		ByHyps:     premises,
		WithLemmas: []LemmaWithSpec{{Key: "homotopy_group.SphereHornFill", TermSpecialize: witnesses}}}})
	require.NoError(t, err)
	require.True(t, res.Success, "the premise by key closes the goal: %v", res.Diagnostics)
	require.Equal(t, "close", res.Effect)
}
