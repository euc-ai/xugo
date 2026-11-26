package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/prover/proof"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestByTactic_DenotedAsIsTheExplicitShaping: `by_shape.denoted_as`
// names the term and its variable — the Go `DenotedAs(name, term)` a
// chapter writes — so the session validates the shaping the file will
// carry. The record holds the term and the name, and emit renders the
// shaping as written.
func TestByTactic_DenotedAsIsTheExplicitShaping(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	e.env.ProofService.CNFStore = proof.NewMemoryCNFStore()
	const stmt = "f:(num → num), x:num, y:num ⊢ f(x + y) = 0 ⇒ f(x + y) + 1 = 1 + f(x + y)"

	sid, gid := bareArithLeaf(t, e, stmt, "strip_imp")
	zero := 0
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
		Type:       "by",
		ByHyps:     []ByHypSpec{{HypIndex: &zero}},
		WithLemmas: []LemmaWithSpec{{Key: "nat_arith.AddSym"}},
		ByShape:    &ByShapeReq{DenotedAs: &ByDenoteAsReq{Name: "d", Term: "f(x + y)"}},
	}})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %+v", res.Diagnostics)

	s, err := e.getSession(sid)
	require.NoError(t, err)
	var shape *proof.ByShapeProto
	for _, st := range s.sections[0].root.DetailedProofProto().GetSteps() {
		if by, ok := st.Step.(*proof.StepProto_By); ok {
			shape = by.By.GetShape()
		}
	}
	require.NotNil(t, shape, "the by composite records its shaping")
	assert.NotZero(t, shape.GetDenoteTerm(), "the term the shaping names")
	assert.Equal(t, "d", shape.GetDenoteName())
	assert.False(t, shape.GetDenoteHilbert())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: sid, Section: 0, FuncName: "Build_DENOTED", Family: "nat_num/nat_order"})
	require.NoError(t, err)
	assert.Contains(t, out.Go, `DenotedAs("d", `, "--- source: ---\n%s", out.Go)
}

// TestByTactic_DenotedAsRefusals: the explicit shaping needs both its
// parts, reads its term at the goal, and — as in Go — a By names at
// most one term.
func TestByTactic_DenotedAsRefusals(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	for _, row := range []struct {
		name  string
		shape ByShapeReq
		want  string
	}{
		{"no name", ByShapeReq{DenotedAs: &ByDenoteAsReq{Term: "x + y"}}, "both"},
		{"no term", ByShapeReq{DenotedAs: &ByDenoteAsReq{Name: "d"}}, "both"},
		{"a term the goal cannot read", ByShapeReq{DenotedAs: &ByDenoteAsReq{Name: "d", Term: "x + nowhere"}}, "by_shape.denoted_as.term"},
		{"two terms", ByShapeReq{
			DenotedAs:        &ByDenoteAsReq{Name: "d", Term: "x + y"},
			HilbertDenotedAs: &ByDenoteAsReq{Name: "h", Term: "x + y"}}, "two explicit denote"},
	} {
		t.Run(row.name, func(t *testing.T) {
			sid, gid := bareArithLeaf(t, e, "x:num, y:num ⊢ x + y = y + x")
			shape := row.shape
			res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{
				Type: "by", WithLemmas: []LemmaWithSpec{{Key: "nat_arith.AddSym"}}, ByShape: &shape}})
			require.NoError(t, err)
			require.False(t, res.Success)
			require.NotEmpty(t, res.Diagnostics)
			assert.Contains(t, res.Diagnostics[0].Message, row.want)
		})
	}
}
