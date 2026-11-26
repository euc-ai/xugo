package engine

import (
	"context"
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestRefute_AgentFacingDispatchIsRetired: the agent surface has no bare
// `refute` tactic, and `auto` is its CNF-refutation entry.
//
//   - `refute` = bare `_CNFRefute` (zero preprocessing). `auto` runs the full
//     AutoExpand pipeline, whose BasicTactic stage carries closure-checks
//     (h⊢h, h+¬h⊢⊥ via AlphaEquals, trivial-⊤) that CNFRefute lacks
//     entirely.
//   - So a goal of the form `H, ¬H ⊢ ⊥` for α-equal H closes under `auto` in
//     ~0ms and times out under a bare refute, which reads as "the engine
//     can't close matched atoms".
//
// The rejection is agent-surface only:
//
//   - `_CNFRefute` remains a proto-level ministep (record/emit/replay).
//   - `ApplyRefute` remains callable from Go for internal use (set_tac's
//     ladder, `CloseByCNFRefute` for stored Detailed steps).
//   - Only `runTacticOnClone` — the shared apply/probe entry point — rejects
//     `"refute"` with a typed error naming `auto` as the replacement.
//
// See ext/clause/cnf_test.go :: TestNegateGoalCNF_ExistsUnderLambdaAlphaDuplication.
func TestRefute_AgentFacingDispatchIsRetired(t *testing.T) {
	// Any goal will do — the rejection fires BEFORE tactic execution and
	// doesn't depend on refutability. Reuse the ematch scaffolding as the
	// cheapest way to get a live session + open goal.
	e, s, sid := ematchSessionWithGoal(t, "x:num ⊢ ¬empty_set(x)")
	ctx := context.Background()
	leafID := ematchOpenLeafID(t, s)

	// Apply path — the classical way an agent would have called refute.
	// ApplyStep's contract: runTacticOnClone errors are wrapped into
	// Diagnostics on a non-success StepResult, not surfaced as top-level err.
	out, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
		GoalID: leafID,
		Tactic: TacticReq{Type: "refute"},
	})
	require.NoError(t, err, "ApplyStep wraps rejection into Diagnostics, not top-level err")
	require.NotNil(t, out)
	assert.False(t, out.Success, "refute must not succeed — it's retired")
	require.NotEmpty(t, out.Diagnostics, "rejection must surface as a Diagnostic")
	joinedDiag := ""
	for _, d := range out.Diagnostics {
		joinedDiag += " " + d.Message
	}
	assert.Contains(t, strings.ToLower(joinedDiag), "retired",
		"diagnostic must name the retirement (so agents don't retry blindly): got %q", joinedDiag)
	assert.Contains(t, joinedDiag, "auto",
		"diagnostic must name `auto` as the replacement: got %q", joinedDiag)

	// Probe path — same rejection contract. Probe should surface the
	// rejection either as top-level err OR as a non-success ProbeResult
	// with the retirement mentioned in the diagnostic — accept either
	// (the exact channel is the probe layer's choice).
	probeOut, probeErr := e.Probe(ctx, sid, &ProbeRequest{
		GoalID:   leafID,
		Tactic:   TacticReq{Type: "refute"},
		BudgetMs: 100,
	})
	if probeErr != nil {
		assert.Contains(t, probeErr.Error(), "retired",
			"probe error must name the retirement: got %q", probeErr.Error())
	} else {
		require.NotNil(t, probeOut, "probe must return either err or a result")
		diagJoined := strings.ToLower(probeOut.Diagnostic + " " + string(probeOut.Reason))
		assert.Contains(t, diagJoined, "retired",
			"probe must surface the retirement in its diagnostic: %+v", probeOut)
	}

	// (Auto's continued functionality post-retirement is covered by every
	// other engine test; not asserted here — this test's job is the
	// retirement, not the surrogate.)
}

// TestCnfRefute_SpellingGetsTheSameGuidance pins the `cnf_refute`
// spelling onto the same rejection. It is the name of the Go Action
// (`CnfRefute()`), so an author who writes a proof session-first reaches
// for it directly; the generic "unknown tactic" path's repair hints say
// nothing about `auto` being the mapping.
//
// Deliberately NOT an alias to `auto`: `auto` also runs the arith
// fast-path, so a silent redirect would hand a foundation-resident
// target (one declaring no capabilities) a close it cannot replay. The
// error therefore also tells the caller to check for a recorded Arith().
func TestCnfRefute_SpellingGetsTheSameGuidance(t *testing.T) {
	e, s, sid := ematchSessionWithGoal(t, "x:num ⊢ ¬empty_set(x)")
	ctx := context.Background()
	leafID := ematchOpenLeafID(t, s)

	out, err := e.ApplyStep(ctx, sid, &ApplyStepRequest{
		GoalID: leafID,
		Tactic: TacticReq{Type: "cnf_refute"},
	})
	require.NoError(t, err, "ApplyStep wraps rejection into Diagnostics, not top-level err")
	require.NotNil(t, out)
	assert.False(t, out.Success, "cnf_refute must not succeed — it is not a session tactic")
	require.NotEmpty(t, out.Diagnostics, "rejection must surface as a Diagnostic")
	joined := ""
	for _, d := range out.Diagnostics {
		joined += " " + d.Message
	}
	assert.Contains(t, joined, "cnf_refute",
		"the diagnostic must name the spelling the caller actually used: got %q", joined)
	assert.Contains(t, joined, "auto",
		"the diagnostic must name `auto` as the replacement: got %q", joined)
	assert.Contains(t, joined, "Arith()",
		"the diagnostic must warn that auto may close via the arith fast-path: got %q", joined)
}
