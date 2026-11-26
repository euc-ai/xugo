package engine

import (
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestBy_ExactReadingCarriesGoClauseForm: a law read at an instance
// entry that keeps a type letter the instance does not fix, grounded at
// every binder — so the witnesses pin that letter and the premise is an
// explicit instance — carries the clause form Go's By gives the same
// premise (`At(Law.Read(Entry), w…)`, premiseClauseForm: the reading's
// NormalizedThm), at the instance's types. A guard the context does not
// supply as written then sends both to the clause install. The clause is
// a theorem, and the claim it leaves certifies from it. The premise is a
// session's (de3f959f, event 21): monoidal.OneTurn read at the integers'
// additive monoid, its element type pinned by the witnesses; with its
// guards resident, the close goes through as before.
func TestBy_ExactReadingCarriesGoClauseForm(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, "a:A, y:A, g:A → int, finite({y}) ∧ a ∉ {y} ⊢ "+
		"iterated_op(int_add, insert(a, {y}), g) = g(a) + iterated_op(int_add, {y}, g)")
	s, err := e.getSession(sid)
	require.NoError(t, err)
	law, at := "monoidal.OneTurn", &ReadAtSpec{Key: "int_real_lift.MonoidalAdd"}
	premise := LemmaWithSpec{Key: law, ReadAt: at, TermSpecialize: map[string]string{"s": "{y}", "x": "a", "f": "g"}}

	s.mu.Lock()
	entry, _, err := e.resolveFocusedGoal(s, gid)
	require.NoError(t, err)
	goal := entry.node.Goal
	specs, _, certs, err := e.byPremiseSpecs(s, goal, TacticReq{Type: "by", WithLemmas: []LemmaWithSpec{premise}})
	require.NoError(t, err)
	reading, rerr := e.resolveReading(s, goal, law, at)
	s.mu.Unlock()
	require.NoError(t, rerr)
	require.Len(t, specs, 1)
	require.True(t, specs[0].Exact, "the witnesses pin the reading's loose type letter: an explicit instance")

	subst, ok := prop.IsTypeMatchOf(reading.theorem, specs[0].Install, utils.FullPredicate[core.VarType])
	require.True(t, ok, "the install is a type instance of the reading")
	want := core.PropTypeInst(proof.NormalizedForm(reading.theorem), subst...)
	require.NotNil(t, specs[0].Clause, "the premise carries the clause form Go's By gives the reading")
	assert.True(t, specs[0].Clause.AlphaEquals(want), "clause %s, Go's %s", specs[0].Clause, want)
	assert.True(t, specs[0].Clause.Proved() || core.IsPromised(specs[0].Clause), "the clause is a derived theorem")
	found := false
	for _, c := range certs {
		found = found || c.AlphaEquals(specs[0].Clause)
	}
	assert.True(t, found, "the clause certifies the claim its install leaves")

	guards := 0
	out, err := e.ApplyStep(t.Context(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type: "by", ByHyps: []ByHypSpec{{HypIndex: &guards}}, WithLemmas: []LemmaWithSpec{premise},
	}})
	require.NoError(t, err)
	assert.True(t, out.Success, "with the guards resident the close goes through: %+v", out.Diagnostics)
}

// TestEmitSection_ExactReadingRecordsItsClause: the exact reading's
// clause form rides on the recorded By, so emit's CNF collection re-runs
// the step as the session ran it, and the section renders the reading
// as Go's `At(Law.Read(Entry), w…)`.
func TestEmitSection_ExactReadingRecordsItsClause(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	guards := 0
	src := emitReading(t, e, "int_num/int_real_lift",
		"∀a y:A. ∀g:A → int. finite({y}) ∧ a ∉ {y} ⇒ iterated_op(int_add, insert(a, {y}), g) = g(a) + iterated_op(int_add, {y}, g)",
		[]string{"strip_quant", "strip_imp"},
		TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &guards}}, WithLemmas: []LemmaWithSpec{{
			Key: "monoidal.OneTurn", ReadAt: &ReadAtSpec{Key: "int_real_lift.MonoidalAdd"},
			TermSpecialize: map[string]string{"s": "{y₀}", "x": "a₀", "f": "g₀"},
		}}})
	assert.Contains(t, src, "At(monoidal.OneTurn.Read(MonoidalAdd), ", "the family's own instance, unqualified\n--- source: ---\n%s", src)
}
