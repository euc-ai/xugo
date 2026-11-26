package engine

import (
	"context"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/ext/dsl"
)

// TestHypothesisMove_ASetBuilderAtItsPointIsNamed: funext leaves an
// equation between set-builders pointwise, each side the set-builder
// applied to the point. A hypothesis of that form is no membership, and
// the move that names it is refused with the form and the way its
// content is taken.
func TestHypothesisMove_ASetBuilderAtItsPointIsNamed(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	stmt := "∀P K:(num → bool). ∀f:(num → num). " +
		"{y:num | ∃k:num. P(k) ∧ y = f(k)} = {y:num | ∃k:num. K(k) ∧ y = f(k)}"
	parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
		ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
		Syntax: constSyntax(),
	})
	require.Empty(t, parsed.Errors)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	for _, typ := range []string{"strip_quant", "funext", "strip_quant", "split_iff"} {
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: typ}})
		require.NoError(t, err, typ)
		require.NotEmpty(t, res.Produced, typ)
		gid = res.Produced[0].GoalID
	}
	hyp := 0
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "strip_quant", HypIndex: &hyp}})
	require.NoError(t, err)
	require.False(t, res.Success)
	require.NotEmpty(t, res.Diagnostics)
	refusal := res.Diagnostics[0].Message
	require.Contains(t, refusal, "is not ∃x. …")
	require.Contains(t, refusal, "a set-builder applied to its point, the form funext leaves of an equation between sets")
	require.Contains(t, refusal, "`simp_with` with `set_basic.Extension` in place of `funext`")
	require.Contains(t, refusal, "by {settac:true}")
}

// TestFunext_AnEquationBetweenSetBuildersSaysSo: funext is function
// extensionality, and of an equation between set-builders it leaves
// each builder applied to the point, which no move reads as a
// membership. The step applies and its answer says so, naming the
// rewrite that opens an equation between sets. An equation between
// predicates or between functions carries no such line: nothing in it
// says its sides are sets.
func TestFunext_AnEquationBetweenSetBuildersSaysSo(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	funext := func(t *testing.T, stmt string) *StepResult {
		t.Helper()
		info, err := e.CreateSession(ctx)
		require.NoError(t, err)
		s, err := e.getSession(info.ID)
		require.NoError(t, err)
		parsed := dsl.ParsePropTextInScope(stmt, &dsl.ParseScope{
			ConstResolver: envConstResolver(s.env), StrictResolution: true, FreshenMetaLetters: true,
			Syntax: constSyntax(),
		})
		require.Empty(t, parsed.Errors)
		s.mu.Lock()
		gid := s.AddGoal(parsed.Prop)
		s.mu.Unlock()
		res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "strip_quant"}})
		require.NoError(t, err)
		require.NotEmpty(t, res.Produced)
		res, err = e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: res.Produced[0].GoalID, Tactic: TacticReq{Type: "funext"}})
		require.NoError(t, err)
		require.True(t, res.Success, "funext on %s: %+v", stmt, res.Diagnostics)
		return res
	}
	said := func(res *StepResult) []Diagnostic {
		var out []Diagnostic
		for _, d := range res.Diagnostics {
			if d.Type == DiagSetEquation {
				out = append(out, d)
			}
		}
		return out
	}

	res := funext(t, "∀P K:(num → bool). {y:num | P(y) ∧ K(y)} = {y:num | K(y) ∧ P(y)}")
	lines := said(res)
	require.Len(t, lines, 1, "%+v", res.Diagnostics)
	require.Contains(t, lines[0].Message, "an equation between sets")
	require.Contains(t, lines[0].Message, "`simp_with` with `set_basic.Extension`")
	require.Equal(t, res.Produced[0].GoalID, lines[0].GoalID)

	for _, stmt := range []string{
		"∀P K:(num → bool). (∀n:num. P(n) ⇔ K(n)) ⇒ P = K",
		"∀f g:(num → num). (∀n:num. f(n) = g(n)) ⇒ f = g",
	} {
		res := funext(t, stmt)
		require.Empty(t, said(res), "%s: %+v", stmt, res.Diagnostics)
	}
}
