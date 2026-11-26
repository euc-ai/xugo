package engine

import (
	"context"
	"go/format"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// emitProved renders section 0 of sid into family and checks it parses
// and is gofmt-clean; the member is written out as writeProbeMember says.
func emitProved(t *testing.T, e *Engine, sid, family, funcName string) string {
	t.Helper()
	out, err := e.EmitSection(&EmitSectionRequest{SessionID: sid, Section: 0, FuncName: funcName, Family: family})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	formatted, err := format.Source([]byte(out.Go))
	require.NoError(t, err)
	assert.Equal(t, string(formatted), out.Go, "the emitted member is not gofmt-clean")
	writeProbeMember(t, family, funcName, out.Go)
	return out.Go
}

// writeProbeMember writes an emitted member into its family's package
// as zz_probe_<name>.go when XUGO_EMIT_PROBE_HYPVERBS=1, for the
// compile-and-replay check a landing runs (record the family's CNF
// blob for <family>.<Name>, then XUGO_REPLAY_ONE=<family>.<Name>); the
// file is the caller's to delete.
func writeProbeMember(t *testing.T, family, funcName, src string) {
	t.Helper()
	if os.Getenv("XUGO_EMIT_PROBE_HYPVERBS") != "1" {
		return
	}
	name := strings.ToLower(strings.TrimPrefix(funcName, "Build_"))
	path := filepath.Join("..", "library", "proofs", filepath.FromSlash(family), "zz_probe_"+name+".go")
	require.NoError(t, os.WriteFile(path, []byte(src), 0o644))
	t.Logf("probe member written to %s", path)
}

// TestEmitSection_SplitConjAtAHypothesisIsConjuncts: a session's
// `split_conj {hyp_index}` renders as the verb it twins —
// `parts := a.Conjuncts(<fact>, labels…)`, one label per flat conjunct,
// the fact its Go value, here the antecedent's closure parameter — and
// the by that reads the conjuncts addresses them as the slice's
// elements. Neither the asserts nor their By closes are printed.
func TestEmitSection_SplitConjAtAHypothesisIsConjuncts(t *testing.T) {
	e, s := boundSession(t, "nat_num/nat_arith")
	addTextGoal(t, s, "∀P Q:bool. ∀f:(num → num). P ∧ Q ∧ f(0) = 0 ⇒ f(0) + 0 = 0")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	zero := 0
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "split_conj", HypIndex: &zero})
	fZero := hypIndexPrinting(t, e, s.ID, "f₀(0) = 0")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(fZero)},
		WithLemmas: []LemmaWithSpec{{Key: "nat_arith.AddZero"}}})
	src := emitSole(t, e, s, "Build_ZzConjunctsOfAnAssumption")
	writeProbeMember(t, "nat_num/nat_arith", "Build_ZzConjunctsOfAnAssumption", src)
	for _, want := range []string{
		" := a.Conjuncts(\n\t\t\t\th,\n\t\t\t\t\"P\",\n\t\t\t\t\"Q\",\n\t\t\t\t\"f(0) = 0\")\n",
		"[2], AddZero)",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"AssertStep(", ".Have(", "Normalized"} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
}

// TestEmitSection_DefExpandAtAHypothesisIsUnfolded: a session's
// `def_expand {const, hyp_index}` renders as `fact := a.Unfolded(<fact>,
// "<const>")`, the fact its Go value, here the antecedent's closure
// parameter, and the close that reads the unfolded statement addresses
// it by value.
func TestEmitSection_DefExpandAtAHypothesisIsUnfolded(t *testing.T) {
	e, s := boundSession(t, "sets/set_product")
	addTextGoal(t, s, "∀s:set(A). ∀t:set(B). ∀x:A. ∀y:B. (x, y) ∈ set_cross(s, t) ⇒ x ∈ s")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	zero := 0
	res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "def_expand", Const: "set_cross", HypIndex: &zero})
	require.Len(t, res.NewHyps, 1)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(res.NewHyps[0].Index)},
		WithLemmas: []LemmaWithSpec{{Key: "pairs.PairEq"}}})
	src := emitSole(t, e, s, "Build_ZzUnfoldedCrossMembership")
	writeProbeMember(t, "sets/set_product", "Build_ZzUnfoldedCrossMembership", src)
	for _, want := range []string{
		"fact1 := a.Unfolded(h, SetCrossDef)\n",
		"BySets(fact1, pairs.PairEq)",
	} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"Unfold(SetCrossDef)", "AssertStep(", ".Have("} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
}

// TestEmitSection_HaveThenVerbsReadTheHavesValue: a fact a Have of the
// block introduced is read by the verbs that follow as the Have's value:
// `fact := a.Have(…)`, then `a.Conjuncts(fact, …)` and `a.Unfolded`
// of a conjunct, `partsN[k]`.
func TestEmitSection_HaveThenVerbsReadTheHavesValue(t *testing.T) {
	e, s := boundSession(t, "sets/set_product")
	addTextGoal(t, s, "∀s:set(A). ∀t:set(B). ∀x:A. ∀y:B. ∀P:bool. P ∧ (x, y) ∈ set_cross(s, t) ⇒ x ∈ s")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	zero := 0
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "assert", ClaimText: "(x₀, y₀) ∈ set_cross(s₀, t₀) ∧ P₀"})
	applyOnGoalProving(t, e, s, "((x₀, y₀) ∈ set_cross(s₀, t₀)) ∧ P₀", TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(zero)},
		ByShape: &ByShapeReq{Normalized: true}})
	conj := hypIndexPrinting(t, e, s.ID, "((x₀, y₀) ∈ set_cross(s₀, t₀)) ∧ P₀")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "split_conj", HypIndex: &conj})
	cross := hypIndexPrinting(t, e, s.ID, "(x₀, y₀) ∈ set_cross(s₀, t₀)")
	opened := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "def_expand", Const: "set_cross", HypIndex: &cross})
	require.Len(t, opened.NewHyps, 1)
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "by", Settac: true, ByHyps: []ByHypSpec{hyp(opened.NewHyps[0].Index)},
		WithLemmas: []LemmaWithSpec{{Key: "pairs.PairEq"}}})
	src := emitSole(t, e, s, "Build_ZzHaveThenVerbs")
	writeProbeMember(t, "sets/set_product", "Build_ZzHaveThenVerbs", src)
	t.Logf("--- source: ---\n%s", src)
	for _, want := range []string{"fact1 := a.Have(", ".Conjuncts(\n\t\t\t\tfact1,\n", ".Unfolded(parts"} {
		assert.Contains(t, src, want, "--- source: ---\n%s", src)
	}
	for _, banned := range []string{"AssertStep(", "ResidentHyp(ctx.MakePropText(\"(x₀, y₀) ∈ set_cross"} {
		assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
	}
}

// ringRecord is the ∀-prefix binding a ring's record, so a member stated
// over it is closed and lands in the ring's family.
const ringRecord = "∀R:ring_ops(A). "

// readingLeaf opens a session on the statement `ringRecord comm_ring(R) ⇒
// body` — the record and the ring hypothesis stripped, then the strips
// given — and returns the session and the leaf.
func readingLeaf(t *testing.T, e *Engine, body string, strips ...string) (sid, gid string) {
	t.Helper()
	return bareArithLeaf(t, e, ringRecord+"comm_ring(R) ⇒ "+body,
		append([]string{"strip_quant", "strip_imp"}, strips...)...)
}

// hypIndexPrinting is the index, in the session's sole open goal, of
// the hypothesis printing as text.
func hypIndexPrinting(t *testing.T, e *Engine, sid, text string) int {
	t.Helper()
	state, err := e.InspectState(context.Background(), sid)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	for i := range state.Goals[0].Statement.NumHyps() {
		if ext.PrintTerm(state.Goals[0].Statement.Hyp(i)) == text {
			return i
		}
	}
	t.Fatalf("no hypothesis prints as %s", text)
	return -1
}

// The hypothesis the readings are under, as the members spell it: the
// Law door's handle.
const ringHypText = "h"

// TestEmitSection_LemmaReadAtRendersAsTheReadingCited: a session
// `lemma {key, read_at}` renders as the Go it twins, the cite of the
// reading — `Cite(Law.Read(h))` where it closed the goal and where it
// installed the reading for the moves that follow, `Cite(Law.Read(h),
// w…)` where a tuple grounded the install — the hypothesis the Law
// door's handle, as the existing `lemma` install of an entry renders
// `Cite(<entry>)`.
func TestEmitSection_LemmaReadAtRendersAsTheReadingCited(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	// A goal the left absorption law's install neither closes nor
	// rewrites into — its rewrite of the equation leaves a conjunct open
	// and is discarded by the preserving chain — and which closes from
	// the installed reading, the equation and the additive monoid.
	const absorbed = "∀c:A. R.zero * R.one = c ⇒ c = R.zero ∧ comm_monoid(R.add, R.zero)"
	closeByInstalled := func(t *testing.T, sid, gid string, installed int) {
		t.Helper()
		equation := hypIndexPrinting(t, e, sid, "ring_mul(R₀, ring_zero(R₀), ring_one(R₀)) = c₀")
		ring := ringHypIndex(t, e, sid)
		closed, err := applyAt(t, e, sid, gid, TacticReq{Type: "by", ByHyps: []ByHypSpec{hyp(installed), hyp(equation)},
			WithLemmas: []LemmaWithSpec{{Key: "comm_ring.AddMonoid", ReadAt: &ReadAtSpec{HypIndex: &ring}}},
			ByShape:    &ByShapeReq{Normalized: true}})
		require.NoError(t, err)
		require.True(t, closed.Success, "diagnostics: %+v", closed.Diagnostics)
	}

	t.Run("a close is a Cite of the reading", func(t *testing.T) {
		// Not the law itself, which is a landed member: the reading under
		// the ring closes a goal that holds one hypothesis more.
		sid, gid := readingLeaf(t, e, "∀c:A. c * c = c ⇒ ∀x:A. R.zero * x = R.zero", "strip_quant", "strip_imp")
		ring := ringHypIndex(t, e, sid)
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: &ring}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		src := emitProved(t, e, sid, "algebra/ring/comm_ring", "Build_ZzReadingClose")
		assert.Contains(t, src, "Cite(MulLeftZero.Read("+ringHypText+"))", "--- source: ---\n%s", src)
		for _, banned := range []string{"TODO", "CiteKnown("} {
			assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
		}
	})
	t.Run("an install is a Cite of the reading", func(t *testing.T) {
		sid, gid := readingLeaf(t, e, absorbed, "strip_quant", "strip_imp")
		ring := ringHypIndex(t, e, sid)
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: &ring}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		require.Len(t, res.NewHyps, 1)
		closeByInstalled(t, sid, res.Produced[0].GoalID, res.NewHyps[0].Index)
		src := emitProved(t, e, sid, "algebra/ring/comm_ring", "Build_ZzReadingInstall")
		for _, want := range []string{
			"Cite(MulLeftZero.Read(" + ringHypText + ")),\n",
			"By(Normalized, AddMonoid.Read(" + ringHypText + "), ResidentHyp(",
		} {
			assert.Contains(t, src, want, "--- source: ---\n%s", src)
		}
		for _, banned := range []string{"LemmaPreserve(", "TODO", "CiteKnown("} {
			assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
		}
	})
	t.Run("a grounded install is a Cite at the tuple", func(t *testing.T) {
		sid, gid := readingLeaf(t, e, absorbed, "strip_quant", "strip_imp")
		ring := ringHypIndex(t, e, sid)
		res, err := applyAt(t, e, sid, gid, TacticReq{Type: "lemma", LemmaKey: "comm_ring.MulLeftZero", ReadAt: &ReadAtSpec{HypIndex: &ring},
			TermSpecialize: map[string]string{"x": "R.one"}})
		require.NoError(t, err)
		require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
		require.Len(t, res.NewHyps, 1)
		closeByInstalled(t, sid, res.Produced[0].GoalID, res.NewHyps[0].Index)
		src := emitProved(t, e, sid, "algebra/ring/comm_ring", "Build_ZzReadingGrounded")
		assert.Contains(t, src, "Cite(MulLeftZero.Read("+ringHypText+"), a.TermAs[A](\"R.one\")),\n", "--- source: ---\n%s", src)
		for _, banned := range []string{"LemmaPreserve(", "Specialize(", "TODO", "CiteKnown("} {
			assert.NotContains(t, src, banned, "--- source: ---\n%s", src)
		}
	})
}
