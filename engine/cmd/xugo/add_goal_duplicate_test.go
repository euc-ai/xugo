package main

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// A text goal a PROVED section already states is refused at the door,
// naming the section and the `restore` recipe; `allow_duplicate:true`
// admits it. A section stating exactly what a proved sibling states
// would close on that sibling at its first step — the failure this
// door turns from silent into loud.
func TestServe_AddGoal_RefusesProvedDuplicate(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	res := rpcCall(t, base, map[string]any{"cmd": "session-create"})
	sessionID, ok := res["id"].(string)
	require.True(t, ok, "session-create should return id, got: %v", res)

	const stmt = "∀P:(num → bool). (∀k:num. P(k)) ⇒ P(0)"
	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"text": stmt},
	})
	goalID, ok := res["goal_id"].(string)
	require.True(t, ok, "first add-goal should return a goal_id, got: %v", res)

	// An OPEN section is not a duplicate: the same statement may be
	// added again while nothing proves it.
	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"text": stmt},
	})
	_, ok = res["goal_id"].(string)
	require.True(t, ok, "re-adding an OPEN statement is admitted, got: %v", res)

	// Prove section 0.
	for _, ty := range []string{"strip_quant", "strip_imp"} {
		res = rpcCall(t, base, map[string]any{
			"cmd": "apply", "session_id": sessionID, "goal_id": goalID,
			"tactic": map[string]any{"type": ty},
		})
		require.Empty(t, res["error"], "%s: %v", ty, res["error"])
		state, _ := res["state"].(map[string]any)
		if complete, _ := state["complete"].(bool); complete {
			break
		}
		goalID = openGoalInSection(t, base, sessionID, "s0_")
	}
	res = rpcCall(t, base, map[string]any{
		"cmd": "apply", "session_id": sessionID, "goal_id": goalID,
		"tactic": map[string]any{"type": "by", "by_hyps": []map[string]any{{"hyp_index": 0}}},
	})
	require.Empty(t, res["error"], "by: %v", res["error"])

	// Now the statement is stated by a PROVED section: refused, by name.
	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"text": stmt},
	})
	errMsg, _ := res["error"].(string)
	require.NotEmpty(t, errMsg, "a proved duplicate must be refused, got: %v", res)
	assert.Contains(t, errMsg, "section 0")
	assert.Contains(t, errMsg, "restore")
	assert.Contains(t, errMsg, "allow_duplicate")

	// And admitted on request.
	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"text": stmt, "allow_duplicate": true},
	})
	_, ok = res["goal_id"].(string)
	require.True(t, ok, "allow_duplicate:true should admit the goal, got: %v", res)
}

// openGoalInSection returns the open goal whose id carries the
// section's prefix; with two sections open, inspect names no single
// focused goal.
func openGoalInSection(t *testing.T, base, sessionID, prefix string) string {
	t.Helper()
	res := rpcCall(t, base, map[string]any{"cmd": "inspect", "session_id": sessionID})
	goals, _ := res["goals"].([]any)
	for _, g := range goals {
		m, _ := g.(map[string]any)
		if id, _ := m["id"].(string); strings.HasPrefix(id, prefix) {
			return id
		}
	}
	t.Fatalf("no open goal in section %s: %v", prefix, res)
	return ""
}

// A goal states a closed theorem: a text with hypotheses left of ⊢ is
// refused at the door, naming its closed spelling, and the session-less
// parse-prop preview of the door refuses it the same way; the closed
// spelling is admitted.
func TestServe_AddGoal_RefusesASequent(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	res := rpcCall(t, base, map[string]any{"cmd": "session-create"})
	sessionID, ok := res["id"].(string)
	require.True(t, ok, "session-create should return id, got: %v", res)

	const sequent = "P:num → bool, ∀k:num. P(k) ⊢ P(0)"
	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"text": sequent},
	})
	msg, _ := res["error"].(string)
	assert.Contains(t, msg, "a goal states a closed theorem", "add-goal admits a sequent: %v", res)
	closed := msg[strings.LastIndex(msg, ": ")+2:]
	assert.NotContains(t, closed, "⊢", "the named spelling is closed: %q", closed)

	res = rpcCall(t, base, map[string]any{"cmd": "parse-prop", "text": sequent})
	assert.Equal(t, false, res["ok"], "the preview admits what the door refuses: %v", res)

	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"text": closed},
	})
	_, ok = res["goal_id"].(string)
	assert.True(t, ok, "the named closed spelling is admitted, got: %v", res)
}
