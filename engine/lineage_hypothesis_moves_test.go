package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestLineage_ResumeReplaysTheHypothesisMoves: a session that splits a
// conjunctive hypothesis (`split_conj {hyp_index}`) and opens a
// definition in one hypothesis (`def_expand {const, hyp_index}`) is
// replayed from its lineage by a fresh engine along the recorded
// steps: the moves re-issue through the same dispatch, the section
// re-proves, and its record matches.
func TestLineage_ResumeReplaysTheHypothesisMoves(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	ctx := context.Background()

	a := lineageEngine(store, dir)
	info, err := a.CreateSession(ctx)
	require.NoError(t, err)
	sid := info.ID
	_, err = a.SetSessionFamily(sid, lineageFamily, nil)
	require.NoError(t, err)
	s, err := a.getSession(sid)
	require.NoError(t, err)
	_, err = a.Define(&DefineRequest{SessionID: sid, Recursive: &DefineRecursive{
		Name: "zz_lin_both", Type: "bool → bool → bool",
		Equations: []string{"∀p q:bool. zz_lin_both(p, q) ⇔ p ∧ q"},
	}})
	require.NoError(t, err)

	// hypsWhere lists the indices of the sole open goal's hypotheses the
	// predicate holds of their printed form.
	hypsWhere := func(holds func(string) bool) []int {
		state, err := a.InspectState(ctx, sid)
		require.NoError(t, err)
		require.Len(t, state.Goals, 1)
		var out []int
		for i := range state.Goals[0].Statement.NumHyps() {
			if holds(ext.PrintTerm(state.Goals[0].Statement.Hyp(i))) {
				out = append(out, i)
			}
		}
		return out
	}
	namesBoth := func(printed string) bool { return strings.Contains(printed, "zz_lin_both") }

	g := lineageText(t, s, "∀p q r:bool. zz_lin_both(p, q) ∧ r ⇒ r ∧ p")
	res := lineageApply(t, a, sid, g, "strip_quant")
	res = lineageApply(t, a, sid, res.Produced[0].GoalID, "strip_imp")
	zero := 0
	split, err := a.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: res.Produced[0].GoalID,
		Tactic: TacticReq{Type: "split_conj", HypIndex: &zero}})
	require.NoError(t, err)
	require.True(t, split.Success, "diagnostics: %+v", split.Diagnostics)
	require.Len(t, split.Produced, 1)
	// The conjunct holding the definition is the hypothesis to open; the
	// conjunction stays beside it.
	both := hypsWhere(func(printed string) bool { return namesBoth(printed) && !strings.Contains(printed, "∧") })
	require.Len(t, both, 1)
	opened, err := a.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: split.Produced[0].GoalID,
		Tactic: TacticReq{Type: "def_expand", Const: "zz_lin_both", HypIndex: &both[0]}})
	require.NoError(t, err)
	require.True(t, opened.Success, "diagnostics: %+v", opened.Diagnostics)
	require.Len(t, opened.NewHyps, 1)
	// The close reads the unfolded statement and the other conjunct.
	var premises []ByHypSpec
	for _, i := range hypsWhere(func(printed string) bool { return !namesBoth(printed) }) {
		idx := i
		premises = append(premises, ByHypSpec{HypIndex: &idx})
	}
	closed, err := a.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: opened.Produced[0].GoalID,
		Tactic: TacticReq{Type: "by", ByHyps: premises, ByShape: &ByShapeReq{Normalized: true}}})
	require.NoError(t, err)
	require.True(t, closed.Success, "diagnostics: %+v", closed.Diagnostics)
	require.Equal(t, 0, closed.State.NumOpen)

	b := lineageEngine(store, dir)
	resumed, err := b.ResumeSession(ctx, sid)
	require.NoError(t, err)
	if resumed.Diverged != nil {
		t.Fatalf("resume diverged at event %d (%s): %s", resumed.Diverged.Seq, resumed.Diverged.Kind, resumed.Diverged.Error)
	}
	assert.Equal(t, resumed.Events, resumed.Replayed)
	// The definition's section, then the theorem's.
	require.Len(t, resumed.Sections, 2)
	theorem := resumed.Sections[1]
	assert.True(t, theorem.Proved, "the section re-proves")
	if assert.NotNil(t, theorem.RecordMatches) {
		assert.True(t, *theorem.RecordMatches, "the section re-proves along the recorded steps")
	}
}
