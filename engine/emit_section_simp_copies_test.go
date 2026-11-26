package engine

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/require"
)

// TestEmitSection_ASimpRulesInertCopiesDeclareNothing: a session's
// simp_with of a polymorphic definition records, beside the rule, the
// copies its type adaptation reached — here the definition's body
// quantifies over the carrier, the unfolded residual quantifies over
// num, and a copy at `A := num` is recorded that nothing fires. The
// member prints the rule as its entry, `Fwd(SimplicialSet)`, and
// nothing of any copy, so the copy's vocabulary enters no declaration:
// `∈` stays a name the member holds at one instance, and a text that
// spells it passes no scope override.
func TestEmitSection_ASimpRulesInertCopiesDeclareNothing(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e, s := boundSession(t, "simplicial/simplicial_set")
	addTextGoal(t, s, "∀X:simplicial_ops(A). simplicial_set(X) ⇒ "+
		"simplicial_set(X) ∧ (∀n i:num. ∀x:A. x ∈ simplicial_simplices(X, n + 1) ∧ i ≤ n + 1 ⇒ simplicial_face(X, n + 1, i, x) ∈ simplicial_simplices(X, n))")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "split_conj"})
	// The first conjunct, the structure itself: unfolded on both sides
	// by the definition — the session's adaptation records the inert
	// copy with each unfold — and closed on the hypothesis.
	folded := func(g core.Prop) bool { return strings.HasPrefix(ext.PrintTerm(g.Conclusion()), "simplicial_set(") }
	definition := []LemmaWithSpec{{Key: "simplicial_set.SimplicialSet"}}
	applyTo(t, e, s, folded, TacticReq{Type: "simp_with", WithLemmas: definition})
	unfolded := func(g core.Prop) bool { return !strings.HasPrefix(ext.PrintTerm(g.Conclusion()), "∀n") }
	applyTo(t, e, s, unfolded, TacticReq{Type: "simp_with", WithLemmas: definition,
		HypIndex: hypAt(t, e, s, unfolded, "simplicial_set(")})
	applyTo(t, e, s, unfolded, TacticReq{Type: "by", ByHyps: hyp0()})
	// The second, one law of the structure: read under the hypothesis,
	// the bounds a resident premise the member spells as a text.
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by",
		ByHyps: []ByHypSpec{{HypIndex: hypAt(t, e, s, sole, "(x₀ ∈")}},
		WithLemmas: []LemmaWithSpec{{Key: "simplicial_set.FaceIn", ReadAt: &ReadAtSpec{HypIndex: hypAt(t, e, s, sole, "simplicial_set(")},
			TermSpecialize: map[string]string{"n": "n₀", "i": "i₀", "x": "x₀"}}}})
	src := emitSole(t, e, s, "Build_ZzInertCopies")
	require.Contains(t, src, "Simp(Fwd(SimplicialSet))", "--- source: ---\n%s", src)
	require.Contains(t, src, "i₀ ≤ n₀ + 1\")", "the bounds are a text with no scope override\n--- source: ---\n%s", src)
	require.NotContains(t, src, "set_member", "∈ is held at one instance: no override, no declaration\n--- source: ---\n%s", src)
	compilesInFamily(t, "../library/proofs/simplicial/simplicial_set", src)
}
