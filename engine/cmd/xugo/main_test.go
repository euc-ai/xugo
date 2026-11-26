package main

import (
	"context"
	"encoding/json/jsontext"
	json "encoding/json/v2"
	"os"
	"os/exec"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/euc-ai/xugo/engine"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/solver/omega"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

var testEngineBundles = sync.OnceFunc(installEngineBundles)

// initTestEngine gives each transport test fresh caches and sessions. The
// process-wide bundles are installed once; TestInitEngine_RealArithLive
// exercises the full production startup, including the dependency manifest.
func initTestEngine() {
	opts := initSessionEnv("")
	testEngineBundles()
	eng = engine.NewEngine(proverEnv, opts...)
}

// resetTrace clears global trace state between tests.
func resetTrace() {
	traceLogPath = ""
	traceStart = time.Time{}
	traceEntry = TraceEntry{}
	stdinCached = false
	stdinData = nil
}

// TestCaptureStdin_TruncatesTheTraceCopyAtAGlyph: the input is read
// once and returned whole. The trace keeps its first 8192 bytes, cut
// back to the last whole glyph so the entry marshals as JSON, and a
// second call answers from the first's read.
func TestCaptureStdin_TruncatesTheTraceCopyAtAGlyph(t *testing.T) {
	resetTrace()
	t.Cleanup(resetTrace)
	// 8191 one-byte letters, then a two-byte glyph across the cut.
	input := strings.Repeat("x", 8191) + "é" + strings.Repeat("y", 100)
	r, w, err := os.Pipe()
	require.NoError(t, err)
	stdin := os.Stdin
	os.Stdin = r
	t.Cleanup(func() {
		os.Stdin = stdin
		r.Close()
	})
	go func() {
		w.WriteString(input)
		w.Close()
	}()

	assert.Equal(t, input, string(captureStdin()), "the command reads the whole input")
	assert.Equal(t, strings.Repeat("x", 8191)+"...(truncated)", traceEntry.InputRaw)

	// stdin is at its end: a second call answers from the first read.
	assert.Equal(t, input, string(captureStdin()))
}

func TestWriteTrace_WritesJSONLine(t *testing.T) {
	resetTrace()
	tmp := t.TempDir()
	logFile := tmp + "/trace.jsonl"

	traceLogPath = logFile
	traceStart = time.Now()
	traceEntry = TraceEntry{
		Command:   "check",
		InputRaw:  "p => p",
		ParseMs:   1,
		EngineMs:  5,
		DiagCount: 0,
		ExitCode:  0,
		Output:    map[string]bool{"valid": true},
	}

	writeTrace()

	data, err := os.ReadFile(logFile)
	require.NoError(t, err)

	lines := strings.Split(strings.TrimSpace(string(data)), "\n")
	require.Len(t, lines, 1, "should write exactly one line")

	var entry TraceEntry
	err = json.Unmarshal([]byte(lines[0]), &entry)
	require.NoError(t, err)

	assert.Equal(t, "check", entry.Command)
	assert.Equal(t, "p => p", entry.InputRaw)
	assert.Equal(t, 1, entry.ParseMs)
	assert.Equal(t, 5, entry.EngineMs)
	assert.Equal(t, 0, entry.ExitCode)
	assert.NotEmpty(t, entry.Timestamp)
	assert.GreaterOrEqual(t, entry.TotalMs, 0) // computed at write time
}

func TestWriteTrace_AppendsMultipleEntries(t *testing.T) {
	resetTrace()
	tmp := t.TempDir()
	logFile := tmp + "/trace.jsonl"
	traceLogPath = logFile

	// Write two entries.
	traceStart = time.Now()
	traceEntry = TraceEntry{Command: "check", InputRaw: "p => p"}
	writeTrace()

	traceStart = time.Now()
	traceEntry = TraceEntry{Command: "check-consistency", InputRaw: "{}"}
	writeTrace()

	data, err := os.ReadFile(logFile)
	require.NoError(t, err)

	lines := strings.Split(strings.TrimSpace(string(data)), "\n")
	assert.Len(t, lines, 2, "should have two lines")

	var e1, e2 TraceEntry
	require.NoError(t, json.Unmarshal([]byte(lines[0]), &e1))
	require.NoError(t, json.Unmarshal([]byte(lines[1]), &e2))
	assert.Equal(t, "check", e1.Command)
	assert.Equal(t, "check-consistency", e2.Command)
}

func TestWriteTrace_ErrorEntry(t *testing.T) {
	resetTrace()
	tmp := t.TempDir()
	logFile := tmp + "/trace.jsonl"

	traceLogPath = logFile
	traceStart = time.Now()
	traceEntry = TraceEntry{
		Command:  "check-derivation",
		InputRaw: "bad json",
		ExitCode: 1,
		Error:    "parse input: invalid character 'b'",
	}

	writeTrace()

	data, err := os.ReadFile(logFile)
	require.NoError(t, err)

	var entry TraceEntry
	require.NoError(t, json.Unmarshal([]byte(strings.TrimSpace(string(data))), &entry))

	assert.Equal(t, 1, entry.ExitCode)
	assert.Contains(t, entry.Error, "parse input")
	assert.Equal(t, "check-derivation", entry.Command)
}

func TestWriteTrace_OmitsEmptyOptionalFields(t *testing.T) {
	resetTrace()
	tmp := t.TempDir()
	logFile := tmp + "/trace.jsonl"

	traceLogPath = logFile
	traceStart = time.Now()
	traceEntry = TraceEntry{
		Command:  "check",
		InputRaw: "p => p",
		// InputParsed, ParseError, Output, Error all zero-value
	}

	writeTrace()

	data, err := os.ReadFile(logFile)
	require.NoError(t, err)

	raw := strings.TrimSpace(string(data))
	// Fields with omitempty should not appear when empty/nil.
	assert.NotContains(t, raw, "input_parsed")
	assert.NotContains(t, raw, "parse_error")
	assert.NotContains(t, raw, `"error"`)
}

func TestWriteJSON_CapturesOutput(t *testing.T) {
	resetTrace()

	// Redirect stdout to discard.
	oldStdout := os.Stdout
	os.Stdout, _ = os.Open(os.DevNull)
	defer func() { os.Stdout = oldStdout }()

	output := map[string]bool{"valid": true}
	writeJSON(output)

	// traceEntry.Output should be set.
	assert.NotNil(t, traceEntry.Output)

	// Verify it round-trips as expected.
	data, err := json.Marshal(traceEntry.Output)
	require.NoError(t, err)
	assert.Contains(t, string(data), `"valid"`)
}

func TestTraceEntry_JSONSchema(t *testing.T) {
	// Verify the TraceEntry serializes with expected field names.
	entry := TraceEntry{
		Timestamp:   "2026-04-02T10:00:00Z",
		Command:     "check",
		InputRaw:    "p => p",
		InputParsed: "p ⇒ p",
		Output:      map[string]bool{"valid": true},
		ParseMs:     2,
		EngineMs:    10,
		TotalMs:     15,
		DiagCount:   0,
		ExitCode:    0,
	}

	data, err := json.Marshal(entry)
	require.NoError(t, err)

	// Verify all expected fields are present.
	var raw map[string]jsontext.Value
	require.NoError(t, json.Unmarshal(data, &raw))

	expectedKeys := []string{"ts", "cmd", "input_raw", "input_parsed", "output", "parse_ms", "engine_ms", "total_ms", "diag_count", "exit_code"}
	for _, k := range expectedKeys {
		assert.Contains(t, raw, k, "missing key: %s", k)
	}

	// Optional fields should not appear when empty.
	assert.NotContains(t, raw, "parse_error")
	assert.NotContains(t, raw, "error")
}

// TestTacticReqFromInput_Subst_RequiresHypIndex pins the wire-level
// validation: subst with an absent hyp_index must fail rather than
// silently default to hyp 0. Using *int in TacticJSON makes JSON
// omission distinguishable from explicit 0; the required-field check
// is in tacticReqFromInput.
func TestTacticReqFromInput_Subst_RequiresHypIndex(t *testing.T) {
	t.Run("absent hyp_index fails", func(t *testing.T) {
		// Decode `{"type":"subst"}` — the way an agent would issue it.
		var tac TacticJSON
		require.NoError(t, json.Unmarshal([]byte(`{"type":"subst"}`), &tac))
		require.Nil(t, tac.HypIndex, "absent hyp_index must decode to nil, not 0")

		_, err := tacticReqFromInput(tac)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "subst requires the 'hyp_index' field")
	})

	t.Run("explicit hyp_index=0 succeeds", func(t *testing.T) {
		var tac TacticJSON
		require.NoError(t, json.Unmarshal([]byte(`{"type":"subst","hyp_index":0}`), &tac))
		require.NotNil(t, tac.HypIndex)
		assert.Equal(t, 0, *tac.HypIndex)

		req, err := tacticReqFromInput(tac)
		require.NoError(t, err)
		assert.Equal(t, "subst", req.Type)
		require.NotNil(t, req.HypIndex)
		assert.Equal(t, 0, *req.HypIndex)
	})

	t.Run("explicit hyp_index=2 round-trips", func(t *testing.T) {
		var tac TacticJSON
		require.NoError(t, json.Unmarshal([]byte(`{"type":"subst","hyp_index":2}`), &tac))
		req, err := tacticReqFromInput(tac)
		require.NoError(t, err)
		require.NotNil(t, req.HypIndex)
		assert.Equal(t, 2, *req.HypIndex)
	})
}

// TestTacticReqFromInput_LeanAliases verifies the alias dispatch in
// tacticReqFromInput rewrites LEAN-style names to their canonical
// XuGo forms AND preserves every field the canonical form needs.
// Without per-alias field-forwarding tests, a typo in
// tacticReqFromInput could drop e.g. `const` for `use` (mapped to
// witness) and the engine would only see `witness` with no parameter
// — silently failing.
func TestTacticReqFromInput_LeanAliases(t *testing.T) {
	cases := []struct {
		name      string
		input     TacticJSON // wire input as the agent would send it
		wantType  string     // expected canonical engine type
		wantConst string     // expected Const field after normalization
		wantKey   string     // expected LemmaKey field after normalization
	}{
		{
			name:     "apply forwards lemma.key to lemma",
			input:    TacticJSON{Type: "apply", Lemma: &PropInput{Key: "prop_abc123"}},
			wantType: "lemma",
			wantKey:  "prop_abc123",
		},
		{
			name:      "unfold forwards const to def_expand",
			input:     TacticJSON{Type: "unfold", Const: "list_map"},
			wantType:  "def_expand",
			wantConst: "list_map",
		},
		{
			name:      "use forwards const to witness",
			input:     TacticJSON{Type: "use", Const: "suc(n)"},
			wantType:  "witness",
			wantConst: "suc(n)",
		},
		{
			name:      "specialize forwards const to instantiate",
			input:     TacticJSON{Type: "specialize", Const: "x"},
			wantType:  "instantiate",
			wantConst: "x",
		},
		{
			name:     "simp passes through as its own verb (the session simp set)",
			input:    TacticJSON{Type: "simp"},
			wantType: "simp",
		},
		{
			name:      "cases forwards const to case_split",
			input:     TacticJSON{Type: "cases", Const: "(x = y)"},
			wantType:  "case_split",
			wantConst: "(x = y)",
		},
		{
			name:     "rfl maps to refl (no params)",
			input:    TacticJSON{Type: "rfl"},
			wantType: "refl",
		},
		{
			name:     "cite_node (the table's snake_case) folds to the hyphenated cite-node",
			input:    TacticJSON{Type: "cite_node", NodeID: "s0_cabc"},
			wantType: "cite-node",
		},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			req, err := tacticReqFromInput(tc.input)
			require.NoError(t, err)
			assert.Equal(t, tc.wantType, req.Type, "alias type rewrite")
			assert.Equal(t, tc.wantConst, req.Const, "Const must survive alias normalization")
			assert.Equal(t, tc.wantKey, req.LemmaKey, "LemmaKey must survive alias normalization")
		})
	}
}

// TestTacticReqFromInput_LeanRwForwardsFields verifies that lean_rw
// (a real engine-level dispatcher, NOT a CLI alias) routes its lemma
// payload through correctly. The engine then runs its
// equality-precondition check on the resolved lemma.
func TestTacticReqFromInput_LeanRwForwardsFields(t *testing.T) {
	t.Run("lean_rw with lemma.key", func(t *testing.T) {
		req, err := tacticReqFromInput(TacticJSON{
			Type:  "lean_rw",
			Lemma: &PropInput{Key: "prop_eqlemma"},
		})
		require.NoError(t, err)
		assert.Equal(t, "lean_rw", req.Type)
		assert.Equal(t, "prop_eqlemma", req.LemmaKey)
	})

	t.Run("lemma with lemma.text forwards raw to LemmaText", func(t *testing.T) {
		req, err := tacticReqFromInput(TacticJSON{
			Type:  "lemma",
			Lemma: &PropInput{Text: "p ⇒ p"},
		})
		require.NoError(t, err)
		assert.Equal(t, "lemma", req.Type)
		assert.Nil(t, req.Lemma, "text form must not be parsed at the wire layer")
		assert.Equal(t, "p ⇒ p", req.LemmaText, "text is forwarded raw for in-engine scope-aware parsing")
	})

	t.Run("lemma with both text and key fails", func(t *testing.T) {
		_, err := tacticReqFromInput(TacticJSON{
			Type:  "lemma",
			Lemma: &PropInput{Text: "p", Key: "prop_xx"},
		})
		require.Error(t, err)
		assert.Contains(t, err.Error(), "exactly one of 'text' or 'key'")
	})

	t.Run("lean_rw without lemma fails", func(t *testing.T) {
		_, err := tacticReqFromInput(TacticJSON{Type: "lean_rw"})
		require.Error(t, err)
		assert.Contains(t, err.Error(), "requires a 'lemma' field")
	})

	t.Run("lemma without lemma fails", func(t *testing.T) {
		_, err := tacticReqFromInput(TacticJSON{Type: "lemma"})
		require.Error(t, err)
		assert.Contains(t, err.Error(), "requires a 'lemma' field")
	})
}

// TestTacticReqFromInput_AssertForwardsClaim verifies the `assert`
// case in tacticReqFromInput. The claim's `text` form is NOT parsed
// here — it is forwarded raw on engine.TacticReq.ClaimText so the
// engine layer (runTacticOnClone) can parse it against the live goal's
// scope (which is what lets a bare session free-var resolve without a
// `n_0:num ⊢ …` prefix). This test only exercises the wire-side dispatch.
func TestTacticReqFromInput_AssertForwardsClaim(t *testing.T) {
	t.Run("assert with claim.text forwards raw to ClaimText", func(t *testing.T) {
		req, err := tacticReqFromInput(TacticJSON{
			Type:  "assert",
			Claim: &PropInput{Text: "p ⇒ p"},
		})
		require.NoError(t, err)
		assert.Equal(t, "assert", req.Type)
		assert.Nil(t, req.Claim, "text form must not be parsed at the wire layer")
		assert.Equal(t, "p ⇒ p", req.ClaimText, "text is forwarded raw for in-engine scope-aware parsing")
	})

	t.Run("assert without claim fails", func(t *testing.T) {
		_, err := tacticReqFromInput(TacticJSON{Type: "assert"})
		require.Error(t, err)
		assert.Contains(t, err.Error(), "requires a 'claim' field")
	})

	t.Run("assert with a key in claim fails", func(t *testing.T) {
		_, err := tacticReqFromInput(TacticJSON{
			Type:  "assert",
			Claim: &PropInput{Text: "p", Key: "prop_xx"},
		})
		require.Error(t, err)
		assert.Contains(t, err.Error(), "claim is given as 'text'")
	})
}

// TestPropFromInput_TextPath covers the agent-authored text DSL path
// through the JSON envelope. This is the primary ingress for ad-hoc
// propositions in stateless verification (check-derivation,
// check-consistency) and exploratory session goals.
func TestPropFromInput_TextPath(t *testing.T) {
	t.Run("simple tautology", func(t *testing.T) {
		got, err := propFromInput(PropInput{Text: "p ⇒ p"})
		require.NoError(t, err)
		require.NotNil(t, got)
	})

	t.Run("with hypotheses", func(t *testing.T) {
		got, err := propFromInput(PropInput{Text: "P:A→bool, P(x) ⊢ P(x) ∨ q"})
		require.NoError(t, err)
		require.NotNil(t, got)
		assert.Equal(t, 1, got.NumHyps())
	})

	t.Run("ASCII normalized to Unicode", func(t *testing.T) {
		got, err := propFromInput(PropInput{Text: `~(p /\ q) <=> (~p \/ ~q)`})
		require.NoError(t, err)
		require.NotNil(t, got)
	})

	t.Run("polymorphic types via var: prefix", func(t *testing.T) {
		// Multi-letter type variable — must use var:Repty to disambiguate.
		got, err := propFromInput(PropInput{Text: "p:var:Repty→bool ⊢ ∀x:var:Repty. p(x) ⇒ p(x)"})
		require.NoError(t, err)
		require.NotNil(t, got)
	})

	t.Run("parse error surfaces", func(t *testing.T) {
		_, err := propFromInput(PropInput{Text: "p ⇒ ⇒ q"})
		require.Error(t, err)
		assert.Contains(t, err.Error(), "parse text")
	})
}

// A statement is given as text: a key is refused, with or without a
// text beside it, and so is an empty input.
func TestPropFromInput_RefusesAKey(t *testing.T) {
	for _, in := range []PropInput{{Key: "prop_xx"}, {Text: "p", Key: "prop_xx"}} {
		_, err := propFromInput(in)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "a statement is given as 'text'")
	}
}

func TestPropFromInput_RejectsEmpty(t *testing.T) {
	_, err := propFromInput(PropInput{})
	require.Error(t, err)
	assert.Contains(t, err.Error(), "must set 'text'")
}

// TestInitEngine_RealArithLive pins the production wiring: initEngine must
// install the corpus RealLemmaBundle (alongside the nat bundle) so the engine
// `arith` / `auto` path is live for real goals. Two assertions:
//
//  1. omega.RealArithEnabled() == true — the in-package gate (RealLemmaBundle
//     present) the `arith` shape-gate (goalHasArithContent, engine/structural.go)
//     ANDs with omega.IsRealArithContent. Without this, real-only goals are
//     filtered out before dispatch.
//  2. The engine's `arith` move closes a representative real goal through a
//     production session — proves dispatch reaches real atoms end-to-end (the
//     real linarith path + the real norm_num bridge), not just that the bundle
//     is present.
//
// Mirrors engine/arith_test.go::TestApplyStep_Arith_ClosesRealGoals at the
// production-wiring layer (initEngine, not a hand-installed bundle in a test).
func TestInitEngine_RealArithLive(t *testing.T) {
	if os.Getenv("XUGO_TEST_ENGINE_INIT_CHILD") == "" {
		cmd := exec.CommandContext(t.Context(), os.Args[0], "-test.run=^TestInitEngine_RealArithLive$", "-test.v", "-test.timeout=1m")
		cmd.Env = append(os.Environ(), "XUGO_TEST_ENGINE_INIT_CHILD=1")
		out, err := cmd.CombinedOutput()
		t.Logf("%s", out)
		require.NoError(t, err, "production startup in a fresh process")
		return
	}
	initEngine("")

	require.True(t, omega.RealArithEnabled(),
		"initEngine must install serve.RealLemmaBundle so real arith dispatch is live")

	ctx := context.Background()
	info, err := eng.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = eng.CloseSession(ctx, info.ID) })

	s, err := eng.GetSession(info.ID)
	require.NoError(t, err)

	// A linear-order real goal: needs the real linarith leaves (transitivity
	// + pairwise-sum / scale primitives) the real bundle now binds. A nat-only build
	// (RealArithEnabled=false) would not even offer `arith` on this goal —
	// goalHasArithContent rejects pure-real content when the gate is off.
	res := dsl.ParsePropText("x:real, y:real, z:real, x <= y, y <= z ⊢ x <= z")
	require.Empty(t, res.Errors, "parse: %v", res.Errors)
	gid := s.AddGoal(res.Prop)

	out, err := eng.ApplyStep(ctx, info.ID, &engine.ApplyStepRequest{
		GoalID: gid,
		Tactic: engine.TacticReq{Type: "arith"},
	})
	require.NoError(t, err)
	require.True(t, out.Success,
		"production-wired `arith` must close the real transitivity goal")
	require.NotNil(t, out.State)
	require.True(t, out.State.Complete,
		"real `arith` should fully close the goal under the production initEngine wiring")
}
