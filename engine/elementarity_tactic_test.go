package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_brouwer"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestElementarityTactic_FixedParameters: the session's `elementarity` call in
// the fixed-parameter form — PolynomialBrouwer's leaf, the source
// BrouwerSource, the facts by index and by entry, P as the parameter —
// closes the leaf as ONE ministep, and emit-section renders it back as
// ByElementarity(…).At(P), the entries declared as dependencies.
func TestElementarityTactic_FixedParameters(t *testing.T) {
	e := newEngine(statedSessionEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	stated := polynomial_brouwer.PolynomialBrouwer.Entry().Statement().Prop
	s.AddGoal(prop.MakeProp(stated.Conclusion()))
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_imp"})
	state, err := e.InspectState(ctx, s.ID)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	facts := []ElementarityRef{{Key: "real_closed_instance.RealClosed"}}
	for i := range s.sections[0].root.UnsolvedLeaves()[0].Goal.NumHyps() {
		facts = append(facts, ElementarityRef{HypIndex: &i})
	}
	// The family of coordinate polynomials, as strip_quant named it.
	param := ""
	for _, v := range s.sections[0].root.UnsolvedLeaves()[0].Goal.Conclusion().Frees(nil) {
		if x, ok := v.AsVar(); ok && strings.HasPrefix(string(x.Name()), "P") {
			param = string(x.Name())
		}
	}
	require.NotEmpty(t, param)
	tactic := TacticReq{
		Type:               "elementarity",
		ElementaritySource: &ElementarityRef{Key: "real_polynomial_geometry.BrouwerSource"},
		ElementarityFacts:  facts,
		Terms:              []string{param},
	}
	res, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: state.Goals[0].ID, Tactic: tactic})
	require.NoError(t, err)
	require.True(t, res.Success, "diagnostics: %v", res.Diagnostics)
	require.True(t, s.sections[0].root.Proved())

	out, err := e.EmitSection(&EmitSectionRequest{SessionID: info.ID, Section: 0, FuncName: "Build_Brouwer", Family: "algebra/field/polynomial_brouwer"})
	require.NoError(t, err)
	parsesAsGo(t, out.Go)
	assert.Contains(t, out.Go, ".At("+strings.ReplaceAll(param, "₀", "_0")+"),", "the parameter renders as the section's variable\n--- source: ---\n%s", out.Go)
	// xugo_fmt lays a call that does not fit out one fact to a line, so the
	// source is matched with its whitespace removed.
	assert.Contains(t, strings.Join(strings.Fields(out.Go), ""), "ByElementarity(real_polynomial_geometry.BrouwerSource,", "--- source: ---\n%s", out.Go)
	assert.Contains(t, out.DepNames, "real_polynomial_geometry.BrouwerSource")
	assert.Contains(t, out.DepNames, "real_closed_instance.RealClosed")
	assert.NotContains(t, out.Go, "TODO", "--- source: ---\n%s", out.Go)

	// A parameter the goal does not name is refused, and the leaf stays open.
	info2, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s2, err := e.getSession(info2.ID)
	require.NoError(t, err)
	s2.AddGoal(prop.MakeProp(stated.Conclusion()))
	applyOnSoleGoal(t, e, s2.ID, TacticReq{Type: "strip_quant"})
	applyOnSoleGoal(t, e, s2.ID, TacticReq{Type: "strip_imp"})
	state2, err := e.InspectState(ctx, s2.ID)
	require.NoError(t, err)
	tactic.Terms = []string{"Q_unbound"}
	res, err = e.ApplyStep(ctx, info2.ID, &ApplyStepRequest{GoalID: state2.Goals[0].ID, Tactic: tactic})
	if err == nil {
		require.False(t, res.Success)
		t.Logf("diagnostics: %v", res.Diagnostics)
	} else {
		t.Logf("refused: %v", err)
	}
	require.False(t, s2.sections[0].root.Proved())
}
