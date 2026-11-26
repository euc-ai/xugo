package engine

import (
	"context"
	json "encoding/json/v2"
	"testing"
	"unicode/utf8"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// natBundleForTest installs the corpus's ℕ bundle for t. auto_with runs
// the arith pass on every leaf with arithmetic content, and a goal over
// num reaches the bundle's theorems there: with none bound the leaf
// degrades, which a serve never meets and this binary answers as an
// engine fault.
func natBundleForTest(t *testing.T) {
	t.Helper()
	installTestNatBundle()
	t.Cleanup(func() { setTestNatBundle(nil) })
}

// TestAutoWith_DefaultHeuristic_ClearsForallHyp: a goal with a top-level
// ∀-hyp (noise) + an `a = b` hyp (needed) closes when the ∀-hyp is
// auto-cleared by the default heuristic + auto fires on the residual.
//
// Minimum feasibility check: clear → autoexpand → Proved().
func TestAutoWith_DefaultHeuristic_ClearsForallHyp(t *testing.T) {
	natBundleForTest(t)
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// `a:num, b:num, (∀x:num. x = x), a = b ⊢ a = b`.
	// Hyp 0: ∀ noise (clear target). Hyp 1: `a = b` (needed for concl).
	res := dsl.ParsePropText("a:num, b:num, (∀x:num. x = x), a = b ⊢ a = b")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "auto_with"},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("auto_with diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success)
	assert.Equal(t, 0, out.State.NumOpen,
		"goal must be fully closed (∀-hyp cleared, a=b ⊢ a=b closes)")
}

// TestAutoWith_DefaultHeuristic_FailsWhenForallNeeded: when the default
// heuristic clears a ∀-hyp that was actually needed, auto_with must
// surface a clean error and leave the session unchanged.
func TestAutoWith_DefaultHeuristic_FailsWhenForallNeeded(t *testing.T) {
	natBundleForTest(t)
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// The ∀-hyp IS the load-bearing one: `∀x. (x = a) ⇒ (x = b)`. Closing
	// `⊢ a = b` needs the ∀ instantiated at `a`. Clearing it makes the
	// goal unprovable, so auto_with must fail (and the session goal
	// must remain open since the clone is discarded).
	res := dsl.ParsePropText("a:num, b:num, (∀x:num. (x = a) => (x = b)) ⊢ a = b")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "auto_with"},
	})
	require.NoError(t, err, "ApplyStep itself succeeds; the failure is in StepResult")
	assert.False(t, out.Success, "auto_with on uncloseable post-clear must fail")

	// Session goal still open.
	stateRes, gerr := e.InspectState(ctx, info.ID)
	require.NoError(t, gerr)
	assert.Equal(t, 1, stateRes.NumOpen, "session goal must remain open after failed auto_with")
}

// TestAutoWith_KeepHypIndices_PreservesNeededForall verifies the keep
// list lets the agent preserve a ∀-hyp that the default heuristic
// would otherwise clear.
func TestAutoWith_KeepHypIndices_PreservesNeededForall(t *testing.T) {
	natBundleForTest(t)
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Same goal as the "fails when forall needed" test, but agent
	// explicitly keeps hyp 0 (the ∀-hyp). Now auto can use it.
	res := dsl.ParsePropText("a:num, b:num, (∀x:num. (x = a) => (x = b)) ⊢ a = b")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:           "auto_with",
			KeepHypIndices: []int{0},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("auto_with diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success)
	assert.Equal(t, 0, out.State.NumOpen)
}

// TestAutoWith_TextLemmaClosesWithItsClaim: a lemma given as text is
// installed with its claim to prove, and auto_with closes the goal and
// the claim in one move.
func TestAutoWith_TextLemmaClosesWithItsClaim(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("p:bool, q:bool, p ⊢ p ∨ q")
	require.Empty(t, res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "auto_with", WithLemmas: []LemmaWithSpec{{Text: "p ⇒ p ∨ q"}}},
	})
	require.NoError(t, err)
	require.True(t, out.Success, "diagnostics: %+v", out.Diagnostics)
	assert.Equal(t, 0, out.State.NumOpen)
}

// TestAutoWith_DropHypIndices_Explicit: agent supplies exactly which
// hyp indices to clear. Same provable goal as the default test but
// the agent says "drop hyp 2" (the ∀ noise) explicitly.
func TestAutoWith_DropHypIndices_Explicit(t *testing.T) {
	natBundleForTest(t)
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("a:num, b:num, (∀x:num. x = x), (∀y:num. y + 0 = y), a = b ⊢ a = b")
	require.Empty(t, res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:           "auto_with",
			DropHypIndices: []int{0, 1},
		},
	})
	require.NoError(t, err)
	if !out.Success {
		t.Logf("auto_with diagnostics: %+v", out.Diagnostics)
	}
	require.True(t, out.Success)
	assert.Equal(t, 0, out.State.NumOpen)
}

// TestAutoWith_FailureDiagnostic_NamesEverythingActionable: the failure
// message must name what auto_with saw + did + what's left open, so the
// agent can pick the right next move without an extra inspect round-trip.
// Validates the multi-line diagnostic shape introduced alongside the
// applyAutoMatchOnRoots fix.
func TestAutoWith_FailureDiagnostic_NamesEverythingActionable(t *testing.T) {
	natBundleForTest(t)
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Goal whose default heuristic clears the load-bearing ∀-hyp, so
	// auto_with can't close — same shape as the existing rollback test
	// but here we assert what the diagnostic SAYS.
	res := dsl.ParsePropText("a:num, b:num, (∀x:num. (x = a) => (x = b)) ⊢ a = b")
	require.Empty(t, res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "auto_with"},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	require.NotEmpty(t, out.Diagnostics)
	msg := out.Diagnostics[0].Message

	// Every diagnostic line that the agent will read for its next decision:
	assert.Contains(t, msg, "auto_with: did not close",
		"top-line label so the agent recognises which tactic failed")
	assert.Contains(t, msg, "Initial:",
		"pre-state hyp + ∀-count line")
	assert.Contains(t, msg, "Cleared:",
		"what the default heuristic dropped — needed to author keep_hyp_indices")
	assert.Contains(t, msg, "Installed:",
		"what scoped lemmas were tried (here: 0)")
	assert.Contains(t, msg, "Residual:",
		"what's still open after arith+auto")
	assert.Contains(t, msg, "Hint:",
		"one-line actionable suggestion")
	// The hint here should mention keep_hyp_indices, because the default
	// heuristic cleared the only ∀-hyp (which was load-bearing).
	assert.Contains(t, msg, "keep_hyp_indices",
		"specific hint for the all-cleared case")
}

// TestAutoWith_FailureDiagnostic_MarksContraposedLeaf: refutation-form
// normalization (ContrapositionTactic) flips a negated hypothesis's body
// into a residual leaf's conclusion. Unmarked, such a leaf reads as auto
// demanding an underivable new fact; the diagnostic must flag it as the
// equivalent proof-by-contradiction form instead.
func TestAutoWith_FailureDiagnostic_MarksContraposedLeaf(t *testing.T) {
	natBundleForTest(t)
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Unprovable goal with a negated hyp: contraposition rewrites
	// `¬(x = y) ⊢ ¬(a = b)` into `a = b ⊢ x = y`, so the residual leaf's
	// conclusion is the pre-auto hyp body `x = y`.
	res := dsl.ParsePropText("a:num, b:num, x:num, y:num, ¬(x = y) ⊢ ¬(a = b)")
	require.Empty(t, res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "auto_with"},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	require.NotEmpty(t, out.Diagnostics)
	msg := out.Diagnostics[0].Message

	assert.Contains(t, msg, "← contraposed hyp",
		"leaf whose concl is a pre-auto negated-hyp body must carry the marker")
	assert.Contains(t, msg, "NOT a new freestanding obligation",
		"explanatory note must accompany the marker")
}

// TestAutoWith_FailureDiagnostic_HintsMissingLemmasWhenEmpty: when the
// caller passes no with_lemmas and the goal needs a lemma to chain, the
// hint should call that out specifically.
func TestAutoWith_FailureDiagnostic_HintsMissingLemmasWhenEmpty(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	// Provable iff a chain lemma were given. Zero ∀-hyps, so default
	// heuristic clears nothing → hint should NOT suggest keep_hyp_indices.
	res := dsl.ParsePropText("p:bool, q:bool ⊢ p ∧ q")
	require.Empty(t, res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{Type: "auto_with"},
	})
	require.NoError(t, err)
	require.False(t, out.Success)
	require.NotEmpty(t, out.Diagnostics)
	msg := out.Diagnostics[0].Message

	assert.Contains(t, msg, "no with_lemmas given",
		"empty with_lemmas + non-closing residual must point at the hint")
	assert.NotContains(t, msg, "keep_hyp_indices",
		"no ∀-hyps were cleared → keep_hyp_indices hint must not fire")
}

// TestAutoWith_RejectsBothKeepAndDrop: input-validation guard.
func TestAutoWith_RejectsBothKeepAndDrop(t *testing.T) {
	e := newEngine(testEnv())
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	s, _ := e.getSession(info.ID)

	res := dsl.ParsePropText("a:num, b:num, (∀x:num. x = x), a = b ⊢ a = b")
	require.Empty(t, res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := e.ApplyStep(ctx, info.ID, &ApplyStepRequest{
		GoalID: gid,
		Tactic: TacticReq{
			Type:           "auto_with",
			KeepHypIndices: []int{0},
			DropHypIndices: []int{0},
		},
	})
	require.NoError(t, err, "ApplyStep returns nil error on tactic failure; surface is StepResult")
	assert.False(t, out.Success)
	require.NotEmpty(t, out.Diagnostics)
	assert.Contains(t, out.Diagnostics[0].Message, "mutually exclusive",
		"diagnostic must name the contradiction")
}

func TestAutoWith_AbbreviationKeepsDiagnosticsUTF8(t *testing.T) {
	msg := abbreviateTerm0("abc⟨A:var:B⟩ tail", 5)
	require.True(t, utf8.ValidString(msg), "abbreviated diagnostic must remain valid UTF-8: %q", msg)

	_, err := json.Marshal([]Diagnostic{{
		Type:    DiagTacticFailure,
		Message: msg,
	}})
	require.NoError(t, err, "diagnostic message must marshal through encoding/json/v2")
}
