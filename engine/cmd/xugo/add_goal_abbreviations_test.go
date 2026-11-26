package main

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// add-goal takes the goal's abbreviations beside its text, and the
// session then spells the names: the goal listing shows «R» where the
// term stands. A table that does not read is refused at the door.
func TestServe_AddGoal_Abbreviations(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	res := rpcCall(t, base, map[string]any{"cmd": "session-create"})
	sessionID, ok := res["id"].(string)
	require.True(t, ok, "session-create should return id, got: %v", res)

	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{
			"text":          "∀x:num. ∀P:(num → bool). (∀y:num. P(y)) ⇒ P(«R»)",
			"abbreviations": []map[string]any{{"name": "R", "text": "x + 1"}},
		},
	})
	_, ok = res["goal_id"].(string)
	require.True(t, ok, "add-goal with abbreviations should return a goal_id, got: %v", res)

	res = rpcCall(t, base, map[string]any{"cmd": "inspect", "session_id": sessionID})
	goals, _ := res["goals"].([]any)
	require.Len(t, goals, 1, "%v", res)
	goal, _ := goals[0].(map[string]any)
	statement, _ := goal["statement"].(string)
	assert.Contains(t, statement, "«R»", "the goal is served spelling its abbreviation")

	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{
			"text":          "∀x:num. P(«R»)",
			"abbreviations": []map[string]any{{"name": "R", "text": "«S» + 1"}},
		},
	})
	errMsg, _ := res["error"].(string)
	assert.Contains(t, errMsg, "«R» spells «S», which is not declared before it")

	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"text": "∀x:num. x = «R»"},
	})
	errMsg, _ = res["error"].(string)
	assert.Contains(t, errMsg, "no abbreviation table is in scope")
}

// add-goal with `entry` states a registry member as its author did,
// text and abbreviations from the member.
func TestServe_AddGoal_Entry(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	var card *registry.ProofEntry
	for _, entry := range registry.All() {
		if entry.IsCard() && entry.Build.Headline != "" && entry.Family() != nil {
			card = entry
			break
		}
	}
	require.NotNil(t, card, "the corpus holds a card to attack")

	res := rpcCall(t, base, map[string]any{"cmd": "session-create", "family": card.Family().Name})
	sessionID, ok := res["id"].(string)
	require.True(t, ok, "%v", res)

	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"entry": card.Name},
	})
	_, ok = res["goal_id"].(string)
	require.True(t, ok, "add-goal {entry} should return a goal_id, got: %v", res)

	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"entry": card.Name, "text": "p ⇒ p"},
	})
	errMsg, _ := res["error"].(string)
	assert.True(t, strings.Contains(errMsg, "drop 'text'"), "%v", res)

	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"entry": "no_such_family.NoSuchMember"},
	})
	errMsg, _ = res["error"].(string)
	assert.Contains(t, errMsg, "no registry member is named")
}

// A session bound to a chapter with a table (registry.Family.WithAbbrev)
// spells the chapter's names in a goal's text without declaring them,
// is served the goal spelling them, and refuses a goal's own table that
// redeclares one. The chapter and the card are the corpus's: the first
// card whose statement spells one of its chapter's names.
func TestServe_AddGoal_ChapterAbbreviations(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)

	var card *registry.ProofEntry
	var chapterName string
	for _, entry := range registry.All() {
		if !entry.IsCard() || entry.Family() == nil || len(entry.Family().Abbrev()) == 0 {
			continue
		}
		for _, name := range dsl.AbbreviationNames(entry.Build.Headline) {
			if entry.Family().AbbrevTable().Has(name) {
				card, chapterName = entry, name
				break
			}
		}
		if card != nil {
			break
		}
	}
	require.NotNil(t, card, "the corpus holds a card spelling its chapter's table")

	res := rpcCall(t, base, map[string]any{"cmd": "session-create", "family": card.Family().Name})
	sessionID, ok := res["id"].(string)
	require.True(t, ok, "%v", res)

	// The card's text, spelled as its author did, declaring nothing.
	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{"text": card.Build.Headline},
	})
	_, ok = res["goal_id"].(string)
	require.True(t, ok, "a goal spelling the chapter's «%s» needs no table of its own, got: %v", chapterName, res)

	res = rpcCall(t, base, map[string]any{"cmd": "inspect", "session_id": sessionID})
	goals, _ := res["goals"].([]any)
	require.Len(t, goals, 1, "%v", res)
	goal, _ := goals[0].(map[string]any)
	statement, _ := goal["statement"].(string)
	assert.Contains(t, statement, "«"+chapterName+"»", "the goal is served spelling the chapter's name")

	// A goal's own entry spells the chapter's; one redeclaring a chapter
	// name is refused.
	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{
			"text":            card.Build.Headline,
			"abbreviations":   []map[string]any{{"name": "zzOwn", "text": "«" + chapterName + "»"}},
			"allow_duplicate": true,
		},
	})
	_, ok = res["goal_id"].(string)
	require.True(t, ok, "a goal's own entry spells the chapter's, got: %v", res)

	res = rpcCall(t, base, map[string]any{
		"cmd": "add-goal", "session_id": sessionID,
		"goal": map[string]any{
			"text":            card.Build.Headline,
			"abbreviations":   []map[string]any{{"name": chapterName, "text": "x"}},
			"allow_duplicate": true,
		},
	})
	errMsg, _ := res["error"].(string)
	assert.Contains(t, errMsg, "one name, one meaning", "%v", res)
}
