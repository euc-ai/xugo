package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestLetTactic_DefinesANameForATerm: `let` is the session face of
// `a.Let` — the defining equation joins the hypotheses, the term's
// occurrences become the name, the goal keeps its form — and the
// section emits the definition as the step it is.
func TestLetTactic_DefinesANameForATerm(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	sid, gid := bareArithLeaf(t, e, "s:set(num), t:set(num), x:num ⊢ x ∈ s ⇒ x ∈ s ∪ t")

	res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "let", Name: "u", Const: "s ∪ t"}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
	require.Len(t, res.Produced, 1)

	s, err := e.getSession(sid)
	require.NoError(t, err)
	named := s.goalIndex[res.Produced[0].GoalID].node.Goal
	require.Equal(t, 1, named.NumHyps(), "the defining equation is the one new hypothesis")
	assert.Equal(t, "u = s ∪ t", s.Spelling().Term(named.Hyp(0)))
	assert.Equal(t, "x ∈ s ⇒ x ∈ u", s.Spelling().Term(named.Conclusion()),
		"the goal keeps its form, the term read by its name")
	assert.NotContains(t, ext.PrintTerm(named.Conclusion()), "union", "no occurrence of the term is left")

	// The name is a premise like any other: the close reads the
	// defining equation beside the membership.
	stripped, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: res.Produced[0].GoalID, Tactic: TacticReq{Type: "strip_imp"}})
	require.NoError(t, err)
	require.Len(t, stripped.Produced, 1)
	zero, one := 0, 1
	closed, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: stripped.Produced[0].GoalID, Tactic: TacticReq{
		Type: "by", Settac: true, ByHyps: []ByHypSpec{{HypIndex: &zero}, {HypIndex: &one}}}})
	require.NoError(t, err)
	require.True(t, closed.Success, "diagnostics: %+v", closed.Diagnostics)
}

// TestLetTactic_EmitsAsTheDefinitionStep: the recorded definition
// renders as the step that replays it.
func TestLetTactic_EmitsAsTheDefinitionStep(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	sid, gid := bareArithLeaf(t, e, "a:num, b:num ⊢ a + b ≤ (a + b) + 1")
	res, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "let", Name: "c", Const: "a + b"}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)
	closed, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: res.Produced[0].GoalID, Tactic: TacticReq{Type: "by", Arith: true}})
	require.NoError(t, err)
	require.True(t, closed.Success, "`c ≤ c + 1` is a fact of arithmetic alone: %+v", closed.Diagnostics)

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: sid, Section: 0, FuncName: "Build_LET", Family: "nat_num/nat_order"})
	require.NoError(t, err)
	assert.Contains(t, out.Go, `LetTerm("c", `, "--- source: ---\n%s", out.Go)
}

// TestLetTactic_Refusals: a definition is named, has a term, and takes
// a name the goal does not already use.
func TestLetTactic_Refusals(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	for _, row := range []struct {
		name   string
		tactic TacticReq
		want   string
	}{
		{"no name", TacticReq{Type: "let", Const: "s ∪ t"}, "requires `name`"},
		{"no term", TacticReq{Type: "let", Name: "u"}, "requires `name`"},
		{"a name the goal uses", TacticReq{Type: "let", Name: "x", Const: "s ∪ t"}, "is already free in the goal"},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := bareArithLeaf(t, e, "s:set(num), t:set(num), x:num ⊢ x ∈ s ⇒ x ∈ s ∪ t")
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: row.tactic})
			require.NoError(t, err)
			require.False(t, res.Success)
			require.NotEmpty(t, res.Diagnostics)
			assert.Contains(t, res.Diagnostics[0].Message, row.want)
		})
	}
}
