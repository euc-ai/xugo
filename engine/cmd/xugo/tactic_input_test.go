package main

import (
	json "encoding/json/v2"
	"testing"

	"github.com/euc-ai/xugo/engine"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// TestTacticReqFromInput_Clear pins the wire→engine mapping for the
// `clear` tactic: `hyp_indices` is its only hyp param (required and
// forwarded as a set; a single drop is `[i]`). There is no hyp_index
// form for clear.
func TestTacticReqFromInput_Clear(t *testing.T) {
	req, err := tacticReqFromInput(TacticJSON{Type: "clear", HypIndices: []int{3, 5}})
	require.NoError(t, err)
	assert.Equal(t, "clear", req.Type)
	assert.Equal(t, []int{3, 5}, req.HypIndices)
	assert.Nil(t, req.HypIndex, "clear must not populate hyp_index")

	// Single drop is just a one-element set.
	req, err = tacticReqFromInput(TacticJSON{Type: "clear", HypIndices: []int{3}})
	require.NoError(t, err)
	assert.Equal(t, []int{3}, req.HypIndices)

	// Missing hyp_indices is a typed error at the wire layer.
	_, err = tacticReqFromInput(TacticJSON{Type: "clear"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "hyp_indices")
}

// TestTacticReqFromInput_Rw pins the wire→engine mapping for the `rw`
// tactic: hyp_index is required (typed error at the wire layer when
// missing, like subst/clear) and the flip flag is forwarded faithfully.
func TestTacticReqFromInput_Rw(t *testing.T) {
	idx := 1
	req, err := tacticReqFromInput(TacticJSON{Type: "rw", HypIndex: &idx, Flip: true})
	require.NoError(t, err)
	assert.Equal(t, "rw", req.Type)
	require.NotNil(t, req.HypIndex)
	assert.Equal(t, 1, *req.HypIndex)
	assert.True(t, req.Flip, "flip must be forwarded, not dropped")

	// flip defaults to false when omitted.
	req, err = tacticReqFromInput(TacticJSON{Type: "rw", HypIndex: &idx})
	require.NoError(t, err)
	assert.False(t, req.Flip)

	// Missing hyp_index is a typed error at the wire layer.
	_, err = tacticReqFromInput(TacticJSON{Type: "rw"})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "hyp_index")
}

// TestTacticReqFromInput_DefaultArm: a tactic the wire door has no arm
// for reaches the engine with its type, const and hyp_index as sent — an
// omitted hyp_index nil, which the engine tells from an explicit 0.
func TestTacticReqFromInput_DefaultArm(t *testing.T) {
	idx := func(i int) *int { return &i }
	for _, tc := range []struct {
		name  string
		input TacticJSON
	}{
		{"congr_arg with its function and index", TacticJSON{Type: "congr_arg", Const: "dest_prod", HypIndex: idx(2)}},
		{"congr_fun with its argument and index 0", TacticJSON{Type: "congr_fun", Const: "x", HypIndex: idx(0)}},
		{"congr_arg without an index", TacticJSON{Type: "congr_arg", Const: "f"}},
		{"def_expand", TacticJSON{Type: "def_expand", Const: "FOO"}},
		{"witness", TacticJSON{Type: "witness", Const: "n"}},
		{"trans", TacticJSON{Type: "trans", Const: "b"}},
		{"intro, no parameter", TacticJSON{Type: "intro"}},
	} {
		t.Run(tc.name, func(t *testing.T) {
			req, err := tacticReqFromInput(tc.input)
			require.NoError(t, err)
			assert.Equal(t, tc.input.Type, req.Type)
			assert.Equal(t, tc.input.Const, req.Const)
			assert.Equal(t, tc.input.HypIndex, req.HypIndex)
		})
	}
}

// TestTacticReqFromInput_ForwardsWhatTheEngineRefuses: `by` and
// `by_induction` carry the fields they do not read to the engine, which
// refuses each by name; dropped at this door, the request would run as
// if they had not been sent.
func TestTacticReqFromInput_ForwardsWhatTheEngineRefuses(t *testing.T) {
	zero := 0
	by, err := tacticReqFromInput(TacticJSON{
		Type:           "by",
		ByHyps:         []engine.ByHypSpec{{HypIndex: &zero}},
		KeepHypIndices: []int{0},
		DropHypIndices: []int{1},
	})
	require.NoError(t, err)
	assert.Equal(t, []int{0}, by.KeepHypIndices)
	assert.Equal(t, []int{1}, by.DropHypIndices)

	induction, err := tacticReqFromInput(TacticJSON{
		Type:   "by_induction",
		Lemma:  &PropInput{Key: "prop_abc"},
		Arith:  true,
		Settac: true,
	})
	require.NoError(t, err)
	assert.True(t, induction.Arith)
	assert.True(t, induction.Settac)
}

// TestTacticReqFromInput_LemmaTermSpecialize_KeyPath pins the wire→engine
// mapping for term_specialize beside a lemma named by key, under `lemma`
// and under `lean_rw`, which share the arm: the map reaches the engine
// as sent. Dropped here, the load succeeds with the wide ∀-hypothesis
// installed.
func TestTacticReqFromInput_LemmaTermSpecialize_KeyPath(t *testing.T) {
	for _, typ := range []string{"lemma", "lean_rw"} {
		t.Run(typ, func(t *testing.T) {
			req, err := tacticReqFromInput(TacticJSON{
				Type:           typ,
				Lemma:          &PropInput{Key: "prop_f99a6cb3a0090c9a"},
				TermSpecialize: map[string]string{"x": "&1", "y": "&1"},
			})
			require.NoError(t, err)
			assert.Equal(t, typ, req.Type)
			assert.Equal(t, "prop_f99a6cb3a0090c9a", req.LemmaKey)
			assert.Equal(t, map[string]string{"x": "&1", "y": "&1"}, req.TermSpecialize)
		})
	}
}

// TestTacticReqFromInput_LemmaTermSpecialize_TextPath checks the
// parallel path via LemmaText. term_specialize must forward through
// both lemma sources.
func TestTacticReqFromInput_LemmaTermSpecialize_TextPath(t *testing.T) {
	req, err := tacticReqFromInput(TacticJSON{
		Type:           "lemma",
		Lemma:          &PropInput{Text: "∀x:real. P(x)"},
		TermSpecialize: map[string]string{"x": "a"},
	})
	require.NoError(t, err)
	assert.Equal(t, "lemma", req.Type)
	assert.Equal(t, "∀x:real. P(x)", req.LemmaText)
	assert.Equal(t, map[string]string{"x": "a"}, req.TermSpecialize)
}

// TestTacticReqFromInput_CiteNode pins the wire→engine mapping for the
// `cite-node` tactic: `node_id` is required and must be forwarded onto
// engine.TacticReq.NodeID unchanged. This is a REGRESSION test for a
// silent-drop bug (fixed alongside this test) where TacticJSON lacked
// a NodeID field entirely and the default arm forwarded only Type /
// Const / HypIndex — so `{"type":"cite-node","node_id":"..."}` silently
// stripped node_id at the JSON layer and the engine dispatch errored
// with `cite-node requires 'node_id'` regardless of what the caller
// passed. The bug was invisible to engine-level tests
// (`TestDerivationPool_CrossSessionGraft` and siblings) because they
// build TacticReq directly and bypass the wire layer. This test closes
// the RPC-level gap; the lesson is that a default arm which forwards
// the fields it knows and drops the rest is a defensive fallback, and
// a defensive fallback hides the failure a refusal would have shown.
func TestTacticReqFromInput_CiteNode(t *testing.T) {
	// Happy path: the wire layer forwards node_id onto req.NodeID and
	// leaves the other tactic fields empty (cite-node has no other
	// parameters — no HypIndex, no Const, no lemma text).
	req, err := tacticReqFromInput(TacticJSON{
		Type:   "cite-node",
		NodeID: "s0_c1234abcd",
	})
	require.NoError(t, err)
	assert.Equal(t, "cite-node", req.Type)
	assert.Equal(t, "s0_c1234abcd", req.NodeID,
		"node_id must be forwarded to req.NodeID, not silently dropped")
	assert.Empty(t, req.Const, "cite-node must not populate Const")
	assert.Nil(t, req.HypIndex, "cite-node must not populate HypIndex")

	// The wire layer accepts the three format spectrums documented on
	// engine.TacticReq.NodeID (session-local closed_subtrees id, pool
	// 16-char prefix from any session's post-close goal id, full
	// AlphaKey) — it forwards the string verbatim and lets the engine
	// resolve. The wire test just pins forwarding.
	for _, id := range []string{
		"s0_c1234abcd",                                  // session-local closed subtree
		"s0_gprop_abcdef0123456789",                     // pool prefix (post-close goal id)
		"prop_abcdef0123456789abcdef0123456789abcdef01", // full AlphaKey
	} {
		req, err := tacticReqFromInput(TacticJSON{Type: "cite-node", NodeID: id})
		require.NoError(t, err)
		assert.Equal(t, id, req.NodeID, "verbatim forward of format %q", id)
	}

	// Missing node_id is a typed error at the wire layer (same pattern
	// as subst / rw / clear — required-field checks belong here so a
	// mis-composed request surfaces immediately instead of silently
	// dropping the field and reporting a downstream error that misleads
	// about which layer is wrong).
	_, err = tacticReqFromInput(TacticJSON{Type: "cite-node"})
	require.Error(t, err, "missing node_id must error at the wire layer")
	assert.Contains(t, err.Error(), "node_id",
		"error must name the offending field")
	assert.Contains(t, err.Error(), "closed_subtrees",
		"error should document the accepted format spectrum")
}

// TestTacticReqFromInput_CiteNodeTermSpecialize pins that `cite-node`
// forwards the optional `term_specialize` map (same silent-drop class as
// the LemmaTermSpecialize wire tests). The engine's cite-node dispatch
// consumes it via resolveTermSpecializeWitnesses + the shared
// applyLemmaTermSpecializeChain to install the cited node's ∀-closed
// conclusion already ground-instantiated — a wire-layer drop would
// silently degrade it back to the graft-then-instantiate ladder.
func TestTacticReqFromInput_CiteNodeTermSpecialize(t *testing.T) {
	req, err := tacticReqFromInput(TacticJSON{
		Type:           "cite-node",
		NodeID:         "s0_gprop_abcdef0123456789",
		TermSpecialize: map[string]string{"a": "a_0", "s": "s_0"},
	})
	require.NoError(t, err)
	assert.Equal(t, "cite-node", req.Type)
	assert.Equal(t, "s0_gprop_abcdef0123456789", req.NodeID)
	assert.Equal(t, map[string]string{"a": "a_0", "s": "s_0"}, req.TermSpecialize,
		"cite-node must forward term_specialize — wire-layer drop would silently degrade the graft to the instantiate ladder")

	// Omitted term_specialize forwards as nil/empty (opt-in only).
	req2, err := tacticReqFromInput(TacticJSON{Type: "cite-node", NodeID: "s0_c1234abcd"})
	require.NoError(t, err)
	assert.Empty(t, req2.TermSpecialize, "absent term_specialize must not fabricate a map")
}

// TestTacticReqFromInput_AutoWith pins the wire→engine mapping for the
// `auto_with` tactic: with_lemmas, keep_hyp_indices, drop_hyp_indices
// must all reach the engine TacticReq unchanged. A drop of any field
// here would silently degrade the scoped-lemma or hyp-scoping behavior
// and surface as a confusing "auto didn't close" downstream.
func TestTacticReqFromInput_AutoWith(t *testing.T) {
	req, err := tacticReqFromInput(TacticJSON{
		Type: "auto_with",
		WithLemmas: []engine.LemmaWithSpec{
			{Key: "prop_deadbeef"},
			{Text: "x = x", TypeSpecialize: map[string]string{"A": "num"}},
		},
		KeepHypIndices: []int{0, 2},
	})
	require.NoError(t, err)
	assert.Equal(t, "auto_with", req.Type)
	require.Len(t, req.WithLemmas, 2, "with_lemmas must be forwarded, not dropped")
	assert.Equal(t, "prop_deadbeef", req.WithLemmas[0].Key)
	assert.Equal(t, "x = x", req.WithLemmas[1].Text)
	assert.Equal(t, map[string]string{"A": "num"}, req.WithLemmas[1].TypeSpecialize)
	assert.Equal(t, []int{0, 2}, req.KeepHypIndices)
	assert.Nil(t, req.DropHypIndices)

	// drop_hyp_indices path — mirror.
	req, err = tacticReqFromInput(TacticJSON{
		Type:           "auto_with",
		WithLemmas:     []engine.LemmaWithSpec{{Key: "prop_cafe"}},
		DropHypIndices: []int{1},
	})
	require.NoError(t, err)
	assert.Equal(t, []int{1}, req.DropHypIndices)
	assert.Nil(t, req.KeepHypIndices)
}

// TestTacticReqFromInput_SimpWith pins the wire→engine mapping for the
// `simp_with` tactic: with_lemmas must reach the engine TacticReq
// unchanged. This is the regression guard for the bug where
// with_lemmas silently fell through the `default:` arm — every RPC
// carrying a non-empty rule set surfaced "simp_with requires a
// non-empty with_lemmas list" because the field never made it into
// req.WithLemmas. The engine-side simp_with_test.go bypasses the wire
// layer entirely (builds TacticReq directly), so this test closes the
// RPC-level gap.
//
// simp_with reads ONLY with_lemmas — hyp keep/drop is not a
// simp_with parameter (rules discharge side conditions against the
// resident goal hyps as-is). See engine/engine.go `case "simp_with"`.
func TestTacticReqFromInput_SimpWith(t *testing.T) {
	req, err := tacticReqFromInput(TacticJSON{
		Type: "simp_with",
		WithLemmas: []engine.LemmaWithSpec{
			{Key: "prop_add_0"},
			{Text: "0 + x = x"},
		},
	})
	require.NoError(t, err)
	assert.Equal(t, "simp_with", req.Type)
	require.Len(t, req.WithLemmas, 2,
		"with_lemmas must be forwarded — silent drop is the exact bug this test guards")
	assert.Equal(t, "prop_add_0", req.WithLemmas[0].Key)
	assert.Equal(t, "0 + x = x", req.WithLemmas[1].Text)

	// simp_with does NOT consume hyp keep/drop; the wire layer must
	// not populate them either — a drift here would be a code smell
	// that the case forwards more than the engine reads.
	assert.Nil(t, req.KeepHypIndices, "simp_with must not populate keep_hyp_indices")
	assert.Nil(t, req.DropHypIndices, "simp_with must not populate drop_hyp_indices")

	// Per-entry type_specialize / term_specialize ride through
	// LemmaWithSpec — verify one representative combination.
	req, err = tacticReqFromInput(TacticJSON{
		Type: "simp_with",
		WithLemmas: []engine.LemmaWithSpec{{
			Key:            "prop_poly",
			TypeSpecialize: map[string]string{"A": "num"},
			TermSpecialize: map[string]string{"x": "&1"},
		}},
	})
	require.NoError(t, err)
	require.Len(t, req.WithLemmas, 1)
	assert.Equal(t, map[string]string{"A": "num"}, req.WithLemmas[0].TypeSpecialize)
	assert.Equal(t, map[string]string{"x": "&1"}, req.WithLemmas[0].TermSpecialize)
}

// TestRpcApply_RejectsTypeSpecializeInsideLemmaObject is the regression
// test for the "silent no-op type_specialize" footgun. Wire schema puts
// `type_specialize` at the TOP of TacticInput — not inside the nested
// `lemma` PropInput. Without RejectUnknownMembers on the rpcApply
// unmarshal, a request that misplaces `type_specialize` inside the
// lemma object gets silently accepted: `omitempty` drops the unknown
// field on PropInput, tactic.TypeSpecialize stays empty, the engine
// installs the lemma at default polymorphic types, and the caller sees
// a bewildering "type_specialize did nothing" outcome (against
// set_basic.InImage: the hyp installs at polymorphic A/B instead of the
// requested prod(A,A→B) / A→B pair).
// With RejectUnknownMembers the misplacement surfaces as a hard parse
// error naming the field and its JSON path (`/tactic/lemma`) so the
// caller sees exactly what to move.
func TestRpcApply_RejectsTypeSpecializeInsideLemmaObject(t *testing.T) {
	body := []byte(`{
		"cmd": "apply",
		"session_id": "s0",
		"goal_id": "g0",
		"tactic": {
			"type": "lemma",
			"lemma": {
				"key": "prop_eb4efd14d1227a80",
				"type_specialize": {"A": "num", "B": "bool"}
			}
		}
	}`)

	var in ApplyInput
	err := decodeRPCInput(body, &in)
	require.Error(t, err,
		"parse must reject `type_specialize` nested inside the lemma object; "+
			"silent acceptance is the exact footgun that silently drops the "+
			"specialization and makes the lemma install at default polymorphic types")
	assert.Contains(t, err.Error(), "type_specialize",
		"the error must name the misplaced field so the caller sees what to move")
	assert.Contains(t, err.Error(), "/tactic/lemma",
		"the error must include the JSON path so the caller sees the location")
	assert.Contains(t, err.Error(), "SIBLING of `lemma`",
		"and say where the field goes: the bare refusal reads as \"this tactic takes no specialize\"")
}

// TestRpcApply_RejectsTermSpecializeInsideLemmaObject is the term-level
// twin, with the same repair in the refusal; a member the lemma object
// never had gets no such hint.
func TestRpcApply_RejectsTermSpecializeInsideLemmaObject(t *testing.T) {
	var in ApplyInput
	err := decodeRPCInput([]byte(`{"cmd":"apply","session_id":"s0","goal_id":"g0",
		"tactic":{"type":"lemma","lemma":{"key":"nat_order.LessEqRefl","term_specialize":{"n":"n_0"}}}}`), &in)
	require.Error(t, err)
	assert.Contains(t, err.Error(), `"term_specialize":{…}`)
	assert.Contains(t, err.Error(), "SIBLING of `lemma`")

	err = decodeRPCInput([]byte(`{"cmd":"apply","session_id":"s0","goal_id":"g0",
		"tactic":{"type":"lemma","lemma":{"key":"nat_order.LessEqRefl","no_such_member":1}}}`), &in)
	require.Error(t, err)
	assert.NotContains(t, err.Error(), "SIBLING")
}

// TestRpcApply_AcceptsTypeSpecializeAtTacticTopLevel is the positive
// twin: the CORRECT placement (top-level on the tactic) must still
// parse cleanly through the strict door. Guards against an
// over-strict guard that rejects the documented shape. Only the
// parse layer is exercised — the engine call is deliberately not run
// (the test package has no live engine wired up).
func TestRpcApply_AcceptsTypeSpecializeAtTacticTopLevel(t *testing.T) {
	body := []byte(`{
		"cmd": "apply",
		"session_id": "s0",
		"goal_id": "g0",
		"tactic": {
			"type": "lemma",
			"lemma": {"key": "prop_eb4efd14d1227a80"},
			"type_specialize": {"A": "num", "B": "bool"}
		}
	}`)

	// rpcApply's own parse step, in isolation. If the door wrongly
	// rejected the correct placement, this would fail.
	var in ApplyInput
	err := decodeRPCInput(body, &in)
	require.NoError(t, err,
		"the correct placement must parse cleanly through RejectUnknownMembers")
	assert.Equal(t, map[string]string{"A": "num", "B": "bool"}, in.Tactic.TypeSpecialize,
		"type_specialize at the tactic top-level must reach the TacticInput field")
}

// TestTacticReqFromInput_SimpWithForwardsHypIndex: `simp_with` at a
// hypothesis (Lean's `simp at h`) reads hyp_index; dropped on the way
// in, the step rewrites the conclusion instead and says nothing.
func TestTacticReqFromInput_SimpWithForwardsHypIndex(t *testing.T) {
	two := 2
	req, err := tacticReqFromInput(TacticJSON{
		Type:       "simp_with",
		HypIndex:   &two,
		WithLemmas: []engine.LemmaWithSpec{{Key: "fam.Name"}},
	})
	require.NoError(t, err)
	require.NotNil(t, req.HypIndex)
	assert.Equal(t, 2, *req.HypIndex)
	assert.Len(t, req.WithLemmas, 1)
}

// TestTacticReqFromInput_SimpAllForwardsItsRules: `simp_all` takes the
// installed simp set plus any with_lemmas.
func TestTacticReqFromInput_SimpAllForwardsItsRules(t *testing.T) {
	req, err := tacticReqFromInput(TacticJSON{
		Type:       "simp_all",
		WithLemmas: []engine.LemmaWithSpec{{Key: "fam.Name", Flip: true}},
	})
	require.NoError(t, err)
	require.Len(t, req.WithLemmas, 1)
	assert.True(t, req.WithLemmas[0].Flip)
}

// TestTacticReqFromInput_Let: the definition move needs both the name
// and the term, and forwards both.
func TestTacticReqFromInput_Let(t *testing.T) {
	req, err := tacticReqFromInput(TacticJSON{Type: "let", Name: "L", Const: "s ∪ t"})
	require.NoError(t, err)
	assert.Equal(t, "let", req.Type)
	assert.Equal(t, "L", req.Name)
	assert.Equal(t, "s ∪ t", req.Const)

	_, err = tacticReqFromInput(TacticJSON{Type: "let", Const: "s ∪ t"})
	require.Error(t, err, "a definition is for the reader: it is named")
	_, err = tacticReqFromInput(TacticJSON{Type: "let", Name: "L"})
	require.Error(t, err)
}

func TestTacticReqFromInput_ByInduction(t *testing.T) {
	zero := 0
	req, err := tacticReqFromInput(TacticJSON{
		Type:           "by_induction",
		Lemma:          &PropInput{Key: "nat_order.StrongInduction"},
		TermSpecialize: map[string]string{"P": "λn:num. Q(n)"},
		ByHyps:         []engine.ByHypSpec{{HypIndex: &zero}},
		ByShape:        &engine.ByShapeReq{Normalized: true},
	})
	require.NoError(t, err)
	assert.Equal(t, "by_induction", req.Type)
	assert.Equal(t, "nat_order.StrongInduction", req.LemmaKey)
	assert.Equal(t, map[string]string{"P": "λn:num. Q(n)"}, req.TermSpecialize)
	require.Len(t, req.ByHyps, 1, "the extras travel")
	require.NotNil(t, req.ByShape)
	assert.True(t, req.ByShape.Normalized)

	_, err = tacticReqFromInput(TacticJSON{Type: "by_induction", TermSpecialize: map[string]string{"P": "Q"}})
	require.Error(t, err, "the principle is named under lemma")
	_, err = tacticReqFromInput(TacticJSON{Type: "by_induction", Lemma: &PropInput{Text: "∀P. P(0) ⇒ ∀n. P(n)"}})
	require.Error(t, err, "and by key")
}

// TestTacticReqFromInput_ByChase pins the wire→engine mapping for the
// diagram-chase closer: `by {chase:{depth:k}}` reaches the engine with
// its depth, and the JSON door accepts the member — a TacticJSON
// without the field refused the whole request as an unknown member.
func TestTacticReqFromInput_ByChase(t *testing.T) {
	var tactic TacticJSON
	require.NoError(t, json.Unmarshal([]byte(`{"type":"by","chase":{"depth":2},"by_hyps":[{"hyp_index":0}]}`), &tactic,
		json.RejectUnknownMembers(true)))
	req, err := tacticReqFromInput(tactic)
	require.NoError(t, err)
	assert.Equal(t, "by", req.Type)
	require.NotNil(t, req.Chase, "chase must be forwarded, not dropped")
	assert.Equal(t, 2, req.Chase.Depth)
	require.Len(t, req.ByHyps, 1)
}

// TestRpcApply_RejectsInstalled: `installed` is a parameter of no simp
// verb — simp_with fires only the rules its with_lemmas name, as the Go
// Simp it renders to does, and the bound families' definitions fire
// under the bare simp and simp_all — so a request carrying it is
// refused by name at the wire, never dropped: a silent drop would let
// an agent believe it chose a rule set.
func TestRpcApply_RejectsInstalled(t *testing.T) {
	for _, value := range []string{"false", "true"} {
		body := []byte(`{
			"cmd": "apply",
			"session_id": "s0",
			"goal_id": "g0",
			"tactic": {
				"type": "simp_with",
				"with_lemmas": [{"key": "list.ReverseAppend"}],
				"installed": ` + value + `
			}
		}`)
		var in ApplyInput
		err := decodeRPCInput(body, &in)
		require.Error(t, err, "installed:%s must be refused", value)
		assert.Contains(t, err.Error(), "installed")
		assert.Contains(t, err.Error(), "/tactic")
	}
}

// TestRpcApply_LemmaReadAt: the `lemma` envelope takes `read_at` beside
// the law's `key`, as a `by` premise and a `simp_with` rule do — the
// Go `Law.Read(instance)` cited — in its three instance forms, and the
// decoded request forwards it to the engine. The envelope was refused
// before (`unknown object member name "read_at" within "/tactic/lemma"`).
func TestRpcApply_LemmaReadAt(t *testing.T) {
	decode := func(t *testing.T, tactic string) engine.TacticReq {
		t.Helper()
		var in ApplyInput
		require.NoError(t, decodeRPCInput([]byte(`{"cmd":"apply","session_id":"s0","goal_id":"g0","tactic":`+tactic+`}`), &in))
		req, err := tacticReqFromInput(in.Tactic)
		require.NoError(t, err)
		return req
	}
	req := decode(t, `{"type":"lemma","lemma":{"key":"comm_ring.MulLeftZero","read_at":{"hyp_index":0}}}`)
	assert.Equal(t, "lemma", req.Type)
	assert.Equal(t, "comm_ring.MulLeftZero", req.LemmaKey)
	require.NotNil(t, req.ReadAt, "read_at must be forwarded, not dropped")
	require.NotNil(t, req.ReadAt.HypIndex)
	assert.Equal(t, 0, *req.ReadAt.HypIndex)

	req = decode(t, `{"type":"lemma","lemma":{"key":"comm_ring.MulLeftZero","read_at":{"key":"real_ring.CommRing"}},"term_specialize":{"x":"x"}}`)
	assert.Equal(t, "real_ring.CommRing", req.ReadAt.Key)
	assert.Equal(t, map[string]string{"x": "x"}, req.TermSpecialize)

	req = decode(t, `{"type":"lemma","lemma":{"key":"comm_ring.MulLeftZero","read_at":{"key":"field.Ring","read_at":{"hyp_index":1}}}}`)
	assert.Equal(t, "field.Ring", req.ReadAt.Key)
	require.NotNil(t, req.ReadAt.ReadAt)
	assert.Equal(t, 1, *req.ReadAt.ReadAt.HypIndex)

	for name, tactic := range map[string]TacticJSON{
		"lean_rw":      {Type: "lean_rw", Lemma: &PropInput{Key: "a.B", ReadAt: &engine.ReadAtSpec{Key: "c.D"}}},
		"by_induction": {Type: "by_induction", Lemma: &PropInput{Key: "a.B", ReadAt: &engine.ReadAtSpec{Key: "c.D"}}},
		"type_inst":    {Type: "type_inst", Lemma: &PropInput{Key: "a.B", ReadAt: &engine.ReadAtSpec{Key: "c.D"}}},
		"no key":       {Type: "lemma", Lemma: &PropInput{Text: "P ⇒ P", ReadAt: &engine.ReadAtSpec{Key: "c.D"}}},
	} {
		t.Run(name+" refuses read_at", func(t *testing.T) {
			_, err := tacticReqFromInput(tactic)
			require.Error(t, err)
			assert.Contains(t, err.Error(), "read_at")
		})
	}
	_, err := propFromInput(PropInput{Text: "P ⇒ P", ReadAt: &engine.ReadAtSpec{Key: "c.D"}})
	require.Error(t, err, "a statement takes no read_at")
	assert.Contains(t, err.Error(), "read_at")
}

// TestRpcApply_HypIndexOnSplitConjAndDefExpand: `split_conj` and
// `def_expand` forward a `hyp_index` — the hypothesis the move acts on
// (Go: a.Conjuncts, a.Unfolded) — and its absence stays absent.
func TestRpcApply_HypIndexOnSplitConjAndDefExpand(t *testing.T) {
	var in ApplyInput
	require.NoError(t, decodeRPCInput([]byte(`{"cmd":"apply","session_id":"s0","goal_id":"g0","tactic":{"type":"split_conj","hyp_index":2}}`), &in))
	req, err := tacticReqFromInput(in.Tactic)
	require.NoError(t, err)
	require.NotNil(t, req.HypIndex)
	assert.Equal(t, 2, *req.HypIndex)

	require.NoError(t, decodeRPCInput([]byte(`{"cmd":"apply","session_id":"s0","goal_id":"g0","tactic":{"type":"def_expand","const":"set_cross","hyp_index":0}}`), &in))
	req, err = tacticReqFromInput(in.Tactic)
	require.NoError(t, err)
	assert.Equal(t, "set_cross", req.Const)
	require.NotNil(t, req.HypIndex)
	assert.Equal(t, 0, *req.HypIndex)

	req, err = tacticReqFromInput(TacticJSON{Type: "def_expand", Const: "set_cross"})
	require.NoError(t, err)
	assert.Nil(t, req.HypIndex)
}

// TestTacticReqFromInput_Elementarity pins the wire→engine mapping for the
// `elementarity` tactic: the source, the facts and the fixed-parameter
// terms reach the engine TacticReq; the embedding mode sends no source.
func TestTacticReqFromInput_Elementarity(t *testing.T) {
	zero, two := 0, 2
	req, err := tacticReqFromInput(TacticJSON{
		Type:   "elementarity",
		Source: &engine.ElementarityRef{Key: "ax_grothendieck.AlgebraicallyClosedAxProperty"},
		Facts:  []engine.ElementarityRef{{HypIndex: &zero}, {Key: "real_closed_instance.RealClosed"}},
		Terms:  []string{"n", "d"},
	})
	require.NoError(t, err)
	assert.Equal(t, "elementarity", req.Type)
	require.NotNil(t, req.ElementaritySource, "source must be forwarded, not dropped")
	assert.Equal(t, "ax_grothendieck.AlgebraicallyClosedAxProperty", req.ElementaritySource.Key)
	require.Len(t, req.ElementarityFacts, 2)
	require.NotNil(t, req.ElementarityFacts[0].HypIndex)
	assert.Equal(t, 0, *req.ElementarityFacts[0].HypIndex)
	assert.Equal(t, "real_closed_instance.RealClosed", req.ElementarityFacts[1].Key)
	assert.Equal(t, []string{"n", "d"}, req.Terms)

	// The embedding mode: no source, facts only.
	var wire TacticJSON
	require.NoError(t, json.Unmarshal([]byte(`{"type":"elementarity","facts":[{"hyp_index":2}]}`), &wire))
	req, err = tacticReqFromInput(wire)
	require.NoError(t, err)
	assert.Nil(t, req.ElementaritySource)
	require.Len(t, req.ElementarityFacts, 1)
	assert.Equal(t, two, *req.ElementarityFacts[0].HypIndex)
}
