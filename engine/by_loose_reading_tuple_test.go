package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// looseReadingTupleLeaf opens, in topology/product_topology, the leaf
// `continuous_map(T₀, S₀, f₀) ⊢ continuous_map(product_topology(T₀, S₀),
// product_topology(S₀, S₀), λp. (f₀(fst(p)), identity_map(snd(p))))`.
// product_topology.ProductMapContinuous states `∀T S U V f g.
// continuous_map(T, U, f) ∧ continuous_map(S, V, g) ⇒ …`: read at the
// hypothesis it fixes T, U and f, which stand among S, V and g, and its
// letters B and D are fixed by no component, so a `by` cites it as the
// law beside the hypothesis.
func looseReadingTupleLeaf(t *testing.T) (*Engine, *Session) {
	t.Helper()
	e, s := boundSession(t, "topology/product_topology")
	addTextGoal(t, s, "∀T:set(set(A)). ∀S:set(set(B)). ∀f:(A → B). continuous_map(T, S, f) ⇒ "+
		"continuous_map(product_topology(T, S), product_topology(S, S), λp:prod(A, B). (f(fst(p)), identity_map(snd(p))))")
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "intro"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	return e, s
}

// looseReadingTupleBy is the `by` citing the law read at the hypothesis
// with table naming the reading's binders, beside the identity's
// continuity.
func looseReadingTupleBy(table map[string]string) TacticReq {
	zero := 0
	return TacticReq{
		Type:   "by",
		ByHyps: []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{
			{Key: "product_topology.ProductMapContinuous", ReadAt: &ReadAtSpec{HypIndex: &zero}, TermSpecialize: table},
			{Key: "continuous.Identity", TermSpecialize: map[string]string{"T": "S₀"}},
		},
	}
}

// TestBy_LooseReadingTupleGroundsTheLawAtItsOwnBinders: a term_specialize
// table on a reading cited as the law beside its hypothesis grounds the
// law with each component of the hypothesis at the binder the law
// states it at. The law's binders run T, S, U, V, f, g and the
// hypothesis fixes T, U, f: a tuple of the three components followed by
// the table's three witnesses put f₀ at U and S₀ at f.
func TestBy_LooseReadingTupleGroundsTheLawAtItsOwnBinders(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	whole := map[string]string{"S": "S₀", "V": "S₀", "g": "identity_map"}

	t.Run("the tuple runs in the law's order", func(t *testing.T) {
		e, s := looseReadingTupleLeaf(t)
		goal := s.goalIndex[soleGoal(t, e, s.ID).ID].node.Goal
		specs, _, _, err := e.byReadingPremises(s, goal, looseReadingTupleBy(whole).WithLemmas[0], nil)
		require.NoError(t, err)
		require.NotEmpty(t, specs)
		printed := make([]string, len(specs[0].Witnesses))
		for i, w := range specs[0].Witnesses {
			printed[i], _, _ = strings.Cut(ext.PrintTerm(w), "⟨")
		}
		assert.Equal(t, []string{"T₀", "S₀", "S₀", "S₀", "f₀", "identity_map"}, printed)
	})

	t.Run("the by closes and emits the reading at the table's witnesses", func(t *testing.T) {
		e, s := looseReadingTupleLeaf(t)
		res := applyOnSoleGoal(t, e, s.ID, looseReadingTupleBy(whole))
		require.Equal(t, "close", res.Effect)
		out, err := e.EmitSection(&EmitSectionRequest{SessionID: s.ID, Section: 0, FuncName: "Build_ZzLooseReadingTuple"})
		require.NoError(t, err)
		flat := strings.Join(strings.Fields(out.Go), " ")
		assert.Contains(t, flat, `At( ProductMapContinuous.Read(f), a.TermAs[Set[Set[B]]]("S"), a.TermAs[Set[Set[B]]]("S"), `+
			`a.TermAs[Fun[B, B]]("identity_map"))`, "the components are the reading's, and the rendering spells only the witnesses")
		replayEmittedInFamily(t, "topology/product_topology", "ZzLooseReadingTuple", out)
	})

	t.Run("a table through V reaches the last component", func(t *testing.T) {
		e, s := looseReadingTupleLeaf(t)
		res := applyOnSoleGoal(t, e, s.ID, looseReadingTupleBy(map[string]string{"S": "S₀", "V": "S₀"}))
		require.Equal(t, "close", res.Effect)
	})

	t.Run("a table that stops before a component is refused by name", func(t *testing.T) {
		e, s := looseReadingTupleLeaf(t)
		res, err := e.ApplyStep(context.Background(), s.ID, &ApplyStepRequest{
			GoalID: soleGoal(t, e, s.ID).ID, Tactic: looseReadingTupleBy(map[string]string{"S": "S₀"})})
		require.NoError(t, err)
		require.False(t, res.Success)
		require.NotEmpty(t, res.Diagnostics)
		assert.Contains(t, res.Diagnostics[0].Message, "the law binds T, S, U, V, f, g and the hypothesis fixes T, U, f")
		assert.Contains(t, res.Diagnostics[0].Message, "this one stops at V, stated before f — give the reading's binders through V")
	})
}

// TestBy_ReadingKeepsItsLawsBinderNamesAmongTheComponents: a reading is
// addressed by the names its law gives the binders it keeps, whatever
// the kernel renamed apart, and those are the law's binders without the
// hypothesis's — here S, V, g of T, S, U, V, f, g, not the law's last
// three. The goal's own S and g make the kernel hold the reading's
// under other names, Tʹ and h; the table spells them as the law states
// them.
func TestBy_ReadingKeepsItsLawsBinderNamesAmongTheComponents(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := bareArithLeaf(t, e, "T:set(set(A)), S:set(set(B)), g:(A → B) ⊢ continuous_map(T, S, g) ⇒ "+
		"continuous_map(product_topology(T, S), product_topology(S, S), λp:prod(A, B). (g(fst(p)), identity_map(snd(p))))",
		"strip_imp")
	s, err := e.getSession(sid)
	require.NoError(t, err)
	zero := 0
	reading, err := e.resolveReading(s, s.goalIndex[gid].node.Goal, "product_topology.ProductMapContinuous", &ReadAtSpec{HypIndex: &zero})
	require.NoError(t, err)
	assert.Equal(t, []string{"Tʹ", "V", "h"}, guardedForAllBinderOrder(reading.statement()))
	assert.Equal(t, map[string]string{"S": "Tʹ", "g": "h"}, reading.renamedBinders())

	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type:   "by",
		ByHyps: []ByHypSpec{hyp(0)},
		WithLemmas: []LemmaWithSpec{
			{Key: "product_topology.ProductMapContinuous", ReadAt: &ReadAtSpec{HypIndex: &zero},
				TermSpecialize: map[string]string{"S": "S", "V": "S", "g": "identity_map"}},
			{Key: "continuous.Identity", TermSpecialize: map[string]string{"T": "S"}},
		},
	}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	require.Equal(t, "close", res.Effect)
}
