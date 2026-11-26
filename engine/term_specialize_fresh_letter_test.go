package engine

import (
	"context"
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext"
)

// A term_specialize witness that is a bare polymorphic constant — `∅`,
// `𝕌`, `identity_map` — is read with the constant's own fresh letters,
// and the binder it grounds says at which type it is meant: the fresh
// letters take the binder's type, as Go's TermAs reads the same text at
// its phantom's type. These tests are the three sightings' shapes.

// hypIndexWithPrefix finds the resident hypothesis printed with prefix;
// the kernel orders hypotheses, so a fact is found by its head.
func hypIndexWithPrefix(t *testing.T, e *Engine, sid, gid, prefix string) int {
	t.Helper()
	s, err := e.getSession(sid)
	require.NoError(t, err)
	goal := s.goalIndex[gid].node.Goal
	for i := range goal.NumHyps() {
		if strings.HasPrefix(ext.PrintTerm(goal.Hyp(i)), prefix) {
			return i
		}
	}
	t.Fatalf("no hypothesis printed with prefix %q", prefix)
	return -1
}

// TestByTactic_TermSpecializeReadsUniverseAtTheBinderType: InfiniteImage's
// `∀s:set(A)` grounded at `𝕌`, whose letter nothing in the text pins,
// reads 𝕌 at set(num) — the binder's type once f is grounded at
// f₀ : num → B — and the premise closes the leaf.
func TestByTactic_TermSpecializeReadsUniverseAtTheBinderType(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, "∀f:(num → B). injective_on(𝕌, f) ⇒ infinite(image(f, 𝕌))", "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by",
		ByHyps: []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{
			{Key: "finite_set.InfiniteImage", TermSpecialize: map[string]string{"f": "f₀", "s": "𝕌"}},
			{Key: "num_segment.Infinite"},
		}}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	require.Equal(t, "close", res.Effect)
}

// TestByTactic_TermSpecializeReadsEmptySetAtAReadingsBinder:
// IndependentZeroNotIn read at the resident module_on and grounded at
// `S := ∅`: the reading's `∀S:set(B)` carries the hypothesis's own B,
// fixed, and ∅'s fresh letter takes it.
func TestByTactic_TermSpecializeReadsEmptySetAtAReadingsBinder(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, "R:ring_ops(A), M:module_ops(A, B) ⊢ module_on(R, M) ⇒ R.one ≠ R.zero ⇒ "+
		"module_independent(R, M, ∅) ⇒ M.zero ∉ ∅", "strip_imp", "strip_imp", "strip_imp")
	structure := hypIndexWithPrefix(t, e, sid, gid, "module_on(")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by",
		ByHyps: []ByHypSpec{hyp(hypIndexWithPrefix(t, e, sid, gid, "ring_one(R) ≠")), hyp(hypIndexWithPrefix(t, e, sid, gid, "module_independent("))},
		WithLemmas: []LemmaWithSpec{{Key: "linear_independence.IndependentZeroNotIn",
			ReadAt: &ReadAtSpec{HypIndex: &structure}, TermSpecialize: map[string]string{"S": "∅"}}}}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	require.Equal(t, "close", res.Effect)
}

// TestByTactic_TermSpecializeReadsIdentityMapAtAReadingsBinder:
// ModuleSumIn read at the resident module_on, its index set grounded at
// s : set(B) and its family at `identity_map`: the binder `F:(D → B)`
// reads D at B from s, and identity_map's one letter takes B from both
// ends of the binder.
func TestByTactic_TermSpecializeReadsIdentityMapAtAReadingsBinder(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, "R:ring_ops(A), M:module_ops(A, B), s:set(B) ⊢ module_on(R, M) ⇒ finite(s) ⇒ "+
		"(∀x:B. x ∈ s ⇒ identity_map(x) ∈ M.carrier) ⇒ module_sum(M.add, M.zero, s, identity_map) ∈ M.carrier",
		"strip_imp", "strip_imp", "strip_imp")
	structure := hypIndexWithPrefix(t, e, sid, gid, "module_on(")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by",
		ByHyps: []ByHypSpec{hyp(hypIndexWithPrefix(t, e, sid, gid, "finite(")), hyp(hypIndexWithPrefix(t, e, sid, gid, "∀x."))},
		WithLemmas: []LemmaWithSpec{{Key: "module.ModuleSumIn",
			ReadAt: &ReadAtSpec{HypIndex: &structure}, TermSpecialize: map[string]string{"s": "s", "F": "identity_map"}}}}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	require.Equal(t, "close", res.Effect)
}

// TestByTactic_TermSpecializeRefusalNamesTheTie: a witness whose fresh
// letter the binder cannot take is refused naming the binder's type, the
// witness's, and the ⟨A:τ⟩ tie.
func TestByTactic_TermSpecializeRefusalNamesTheTie(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, "∀f:(num → B). injective_on(𝕌, f) ⇒ infinite(image(f, 𝕌))", "strip_quant", "strip_imp")
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "by",
		ByHyps: []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{
			{Key: "finite_set.InfiniteImage", TermSpecialize: map[string]string{"f": "f₀", "s": "identity_map"}},
		}}})
	require.NoError(t, err)
	require.False(t, res.Success)
	answer := fmt.Sprint(res.Diagnostics)
	require.Contains(t, answer, "binder s:(num → bool)", "the refusal names the binder's type: %s", answer)
	require.Contains(t, answer, `"identity_map" of type (var:?f1A → var:?f1A)`, "the refusal names the witness's type: %s", answer)
	require.Contains(t, answer, "identity_map⟨A:", "the refusal suggests the tie: %s", answer)
}
