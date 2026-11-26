package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestSimpSet_BoundSessionReadsTheChapterRules: a session bound to a
// family whose chapter marked theorems Simp (registry.ProofEntry.Simp)
// rewrites with them under the bare `simp`, beside the definitions the
// bind installs, and the bind reports them as installed rules of shape
// "simp". nat_num/nat_arith marks its identity laws: `(m + 0) + 0 = m` is
// `m = m` after one bare simp (AddZero twice, in the driver's fixpoint),
// and refl closes it.
func TestSimpSet_BoundSessionReadsTheChapterRules(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	binding, err := e.SetSessionFamily(info.ID, "nat_num/nat_arith", nil)
	require.NoError(t, err)
	simp := map[string]bool{}
	for _, r := range binding.Installed {
		if r.Shape == "simp" {
			simp[r.Entry] = true
		}
	}
	for _, name := range []string{"nat_arith.AddZero", "nat_arith.MulOne", "nat_arith.OneMul", "nat_arith.MulZero"} {
		require.True(t, simp[name], "the bind must install %s as a simp rule; installed: %v", name, simp)
	}
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope("∀m:num. (m + 0) + 0 = m", &dsl.ParseScope{
		ConstResolver:      envConstResolver(s.env),
		StrictResolution:   true,
		FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	stripped, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: "strip_quant"}})
	require.NoError(t, err)
	require.Len(t, stripped.Produced, 1)
	simped, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: stripped.Produced[0].GoalID, Tactic: TacticReq{Type: "simp"}})
	require.NoError(t, err)
	require.True(t, simped.Success, "diagnostics: %+v", simped.Diagnostics)
	require.Len(t, simped.Produced, 1, "the used rules close by auto-match; the residual remains")
	closed, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{GoalID: simped.Produced[0].GoalID, Tactic: TacticReq{Type: "refl"}})
	require.NoError(t, err)
	require.Equal(t, "close", closed.Effect)
}
