package engine

// The session verbs the Lean-gap inventory added: `simp_with` / `simp` at a
// hypothesis (hyp_index), `simp_all`, `ring_nf` and `apply_search`.

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// leanGapsSession binds a session to nat_num/nat_arith and adds the goal.
func leanGapsSession(t *testing.T, e *Engine, family, text string) (string, string) {
	t.Helper()
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	if family != "" {
		_, err = e.SetSessionFamily(info.ID, family, nil)
		require.NoError(t, err)
	}
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
		ConstResolver:      envConstResolver(s.env),
		StrictResolution:   true,
		FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors, "goal %q", text)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	return info.ID, gid
}

func mustStep(t *testing.T, e *Engine, sid, gid string, req TacticReq) *StepResult {
	t.Helper()
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: req})
	require.NoError(t, err)
	require.True(t, res.Success, "%s: diagnostics %+v", req.Type, res.Diagnostics)
	return res
}

// TestSimpAtHypothesis: `simp_with` with hyp_index rewrites that hypothesis
// in its place and leaves the conclusion alone; the bare `simp` of a bound
// session does the same with its installed set.
func TestSimpAtHypothesis(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := leanGapsSession(t, e, "nat_num/nat_arith", "∀m:num. ∀n:num. m + 0 = n ⇒ m = n")
	stripped := mustStep(t, e, sid, gid, TacticReq{Type: "strip_quant"})
	imp := mustStep(t, e, sid, stripped.Produced[0].GoalID, TacticReq{Type: "strip_imp"})
	h0 := 0
	simped := mustStep(t, e, sid, imp.Produced[0].GoalID, TacticReq{Type: "simp", HypIndex: &h0})
	require.Len(t, simped.Produced, 1)
	require.Equal(t, 1, simped.Produced[0].Changes.HypsAdded, "the rewritten hypothesis: %+v", simped.Produced[0].Changes)
	require.Equal(t, 1, simped.Produced[0].Changes.HypsDropped, "the hypothesis as it was: %+v", simped.Produced[0].Changes)
	require.False(t, simped.Produced[0].Changes.ConclusionChanged, "the conclusion is untouched")
	closed := mustStep(t, e, sid, simped.Produced[0].GoalID, TacticReq{Type: "assumption"})
	require.Equal(t, "close", closed.Effect)
	// emit renders the hypothesis step through the fact that names it —
	// here the hypothesis came from the opening strip, which the closure
	// binds as its Fact parameter.
	emitted, err := e.EmitSection(&EmitSectionRequest{SessionID: sid, Section: 0, FuncName: "Build_Probe", Family: "nat_num/nat_arith"})
	require.NoError(t, err)
	require.Contains(t, emitted.Go, "func(a *Argument, m, n *Expr[Nat], h Fact) {", "emitted:\n%s", emitted.Go)
	require.Contains(t, emitted.Go, "h.Simp(Fwd(AddZero))", "emitted:\n%s", emitted.Go)
	require.NotContains(t, emitted.Go, "SimpAt(", "emitted:\n%s", emitted.Go)
}

// TestSimpAll: every target is rewritten — the conclusion and the
// hypothesis both carry an identity the installed set folds — and the
// residual is closed by the refuter (the driver may spell a rewritten
// equation in the normalizer's orientation, so `assumption` is not the
// test).
func TestSimpAll(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := leanGapsSession(t, e, "nat_num/nat_arith", "∀m:num. ∀n:num. m + 0 = n ⇒ (m + 0) + 0 = n")
	stripped := mustStep(t, e, sid, gid, TacticReq{Type: "strip_quant"})
	imp := mustStep(t, e, sid, stripped.Produced[0].GoalID, TacticReq{Type: "strip_imp"})
	all := mustStep(t, e, sid, imp.Produced[0].GoalID, TacticReq{Type: "simp_all"})
	require.Len(t, all.Produced, 1)
	require.True(t, all.Produced[0].Changes.ConclusionChanged, "the conclusion's (m + 0) + 0 folded")
	require.Equal(t, 1, all.Produced[0].Changes.HypsAdded, "the hypothesis's m + 0 folded: %+v", all.Produced[0].Changes)
	closed := mustStep(t, e, sid, all.Produced[0].GoalID, TacticReq{Type: "auto"})
	require.Equal(t, "close", closed.Effect)
}

// TestRingNf: the ring normal form as a session move — both sides of the
// comparison are spelled as sums of monomials, and the normalized goal
// closes by assumption against the normalized hypothesis.
func TestRingNf(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := leanGapsSession(t, e, "", "∀a:num. ∀b:num. ∀c:num. 2 * a + 2 * b <= c ⇒ (b + a) * 2 <= c")
	stripped := mustStep(t, e, sid, gid, TacticReq{Type: "strip_quant"})
	imp := mustStep(t, e, sid, stripped.Produced[0].GoalID, TacticReq{Type: "strip_imp"})
	nf := mustStep(t, e, sid, imp.Produced[0].GoalID, TacticReq{Type: "ring_nf"})
	require.Len(t, nf.Produced, 1)
	require.True(t, nf.Produced[0].Changes.ConclusionChanged)
	closed := mustStep(t, e, sid, nf.Produced[0].GoalID, TacticReq{Type: "assumption"})
	require.Equal(t, "close", closed.Effect)
}

// TestApplySearch: Lean's `exact?` — the goal IS a corpus member's
// statement (nat_arith.AddZero at the goal's own quantity), and the search
// closes it by that member, recorded as the lemma cite it is.
func TestApplySearch(t *testing.T) {
	if testing.Short() {
		t.Skip("needs the corpus")
	}
	e := byArithEngine(t)
	sid, gid := leanGapsSession(t, e, "", "∀m:num. m + 0 = m")
	res := mustStep(t, e, sid, gid, TacticReq{Type: "apply_search"})
	require.Equal(t, "close", res.Effect, "diagnostics %+v", res.Diagnostics)
}
