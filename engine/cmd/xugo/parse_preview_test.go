package main

import (
	"context"
	json "encoding/json/v2"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// dispatchRPCJSON is a thin helper: marshal `in`, call the named RPC,
// round-trip the result through JSON, and return it as map[string]any.
// This exercises the exact wire shape agents see, so a wire-level
// regression is caught here too (not just the Go-side struct).
func dispatchRPCJSON(t *testing.T, fn func([]byte) (any, error), in any) map[string]any {
	t.Helper()
	body, err := json.Marshal(in)
	require.NoError(t, err)
	got, err := fn(body)
	require.NoError(t, err)
	raw, err := json.Marshal(got)
	require.NoError(t, err)
	var out map[string]any
	require.NoError(t, json.Unmarshal(raw, &out))
	return out
}

// TestRpcParseProp_BareMode pins the behavior of parse-prop when only
// `text` is supplied: no session scoping, the statement-door scope
// (strict resolution + the registry resolver when attached), the same
// fields (ok / normalized_input / statement_text / warnings / errors)
// an agent has always seen. The preview mirrors add-goal's text door,
// so previewed acceptance matches the door's.
func TestRpcParseProp_BareMode(t *testing.T) {
	// Each RPC test has its own engine and session state.
	initTestEngine()

	t.Run("well-formed text parses ok", func(t *testing.T) {
		out := dispatchRPCJSON(t, rpcParseProp, map[string]any{
			"text": "∀p:bool. p ⇒ p",
		})
		require.Equal(t, true, out["ok"], "bare-mode parse of tautology must succeed: %v", out)
		require.NotEmpty(t, out["statement_text"])
		require.NotEmpty(t, out["normalized_input"])
		_, hasErrors := out["errors"]
		require.False(t, hasErrors, "no errors on well-formed input")
	})

	t.Run("a declaration prefix in ASCII parses ok", func(t *testing.T) {
		out := dispatchRPCJSON(t, rpcParseProp, map[string]any{
			"text": "P:A->bool ⊢ forall x:A. P(x) => P(x)",
		})
		require.Equal(t, true, out["ok"], "%v", out)
		require.NotEmpty(t, out["statement_text"])
		require.NotEmpty(t, out["normalized_input"])
	})

	t.Run("bare polymorphic head is a strict-mint error", func(t *testing.T) {
		// The class-2 shape: ∅ and 𝕌 both freeze the abstract letter A;
		// no binder mentions it, no ⟨⟩ tie names it — the door rejects
		// instead of accepting a statement about an unintended instance.
		out := dispatchRPCJSON(t, rpcParseProp, map[string]any{
			"text": "∅ = 𝕌",
		})
		require.Equal(t, false, out["ok"], "bare polymorphic heads must not parse at the door: %v", out)
		errs, ok := out["errors"].([]any)
		require.True(t, ok, "errors field must be a list, got %T", out["errors"])
		first, _ := errs[0].(map[string]any)
		msg, _ := first["message"].(string)
		require.Contains(t, msg, "strict mint")
		require.Contains(t, msg, "⟨")
	})

	t.Run("undeclared free is a strict-resolution error", func(t *testing.T) {
		// The statement door rejects silent freshening: a bare `p`
		// does not parse as a fresh bool variable, and the error
		// names the name and the repair.
		out := dispatchRPCJSON(t, rpcParseProp, map[string]any{
			"text": "p ⇒ p",
		})
		require.Equal(t, false, out["ok"], "undeclared free must not parse: %v", out)
		errs, ok := out["errors"].([]any)
		require.True(t, ok, "errors field must be a list, got %T", out["errors"])
		first, _ := errs[0].(map[string]any)
		msg, _ := first["message"].(string)
		require.Contains(t, msg, "strict resolution")
		require.Contains(t, msg, `"p"`)
	})

	t.Run("malformed text returns errors", func(t *testing.T) {
		out := dispatchRPCJSON(t, rpcParseProp, map[string]any{
			"text": "p ⇒ ⇒ q",
		})
		require.Equal(t, false, out["ok"], "malformed input must not report ok=true: %v", out)
		errs, ok := out["errors"].([]any)
		require.True(t, ok, "errors field must be a list, got %T", out["errors"])
		require.NotEmpty(t, errs, "at least one error entry on bad parse")
	})
}

// TestRpcParseProp_ScopedMode exercises the new session-scoped path: a
// bare free-var `n` that would be rejected as untyped in bare mode
// resolves to the goal's num type when session_id is supplied.
func TestRpcParseProp_ScopedMode(t *testing.T) {
	initTestEngine()
	ctx := context.Background()

	info, err := eng.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = eng.CloseSession(ctx, info.ID) })

	s, err := eng.GetSession(info.ID)
	require.NoError(t, err)

	// Goal: ⊢ n = n  (n free, type num). Text-DSL "n = n" against this
	// goal must resolve n's type via goalFreeVarTypes.
	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	n := ext.Var("n", numType)
	goalID := s.AddGoal(prop.MakeProp(core.Eq(n, n)))

	t.Run("scoped: bare free-var resolves to num", func(t *testing.T) {
		out := dispatchRPCJSON(t, rpcParseProp, map[string]any{
			"text":       "n = n",
			"session_id": info.ID,
			"goal_id":    goalID,
		})
		require.Equal(t, true, out["ok"],
			"scoped parse of 'n = n' against ⊢ n = n (n:num) must succeed: %v", out)
		require.NotEmpty(t, out["statement_text"])
	})

	t.Run("scoped: goal_id omitted falls back to focused", func(t *testing.T) {
		out := dispatchRPCJSON(t, rpcParseProp, map[string]any{
			"text":       "n = n",
			"session_id": info.ID,
		})
		require.Equal(t, true, out["ok"], "focused-goal fallback must succeed: %v", out)
	})

	t.Run("bare mode over the same text still fails (no scope)", func(t *testing.T) {
		out := dispatchRPCJSON(t, rpcParseProp, map[string]any{
			"text": "n = n",
		})
		require.Equal(t, false, out["ok"],
			"bare-mode parse of untyped free-var must fail (no scope): %v", out)
	})

	t.Run("missing session_id lookup surfaces as ok:false", func(t *testing.T) {
		out := dispatchRPCJSON(t, rpcParseProp, map[string]any{
			"text":       "n = n",
			"session_id": "no-such-session",
		})
		require.Equal(t, false, out["ok"],
			"session-lookup failure must surface as ok:false, not RPC error: %v", out)
	})
}

// TestRpcParseTerm_Basic pins the goal-scoped term-DSL preview: a term
// naming a goal-local free var parses without an explicit type
// annotation, and returns a printed term_text.
func TestRpcParseTerm_Basic(t *testing.T) {
	initTestEngine()
	ctx := context.Background()

	info, err := eng.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = eng.CloseSession(ctx, info.ID) })

	s, err := eng.GetSession(info.ID)
	require.NoError(t, err)

	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	n := ext.Var("n", numType)
	// Goal ⊢ n = n so `n` is a goal-local free var of type num.
	_ = s.AddGoal(prop.MakeProp(core.Eq(n, n)))

	out := dispatchRPCJSON(t, rpcParseTerm, map[string]any{
		"text":       "n",
		"session_id": info.ID,
	})
	require.Equal(t, true, out["ok"], "term-preview of goal-local n must succeed: %v", out)
	require.NotEmpty(t, out["term_text"])
}

// TestRpcParseTerm_ExpectedType: `expected_type: "bool"` admits a
// boolean expression and refuses a term of another type.
func TestRpcParseTerm_ExpectedType(t *testing.T) {
	initTestEngine()
	ctx := context.Background()

	info, err := eng.CreateSession(ctx)
	require.NoError(t, err)
	t.Cleanup(func() { _ = eng.CloseSession(ctx, info.ID) })

	s, err := eng.GetSession(info.ID)
	require.NoError(t, err)

	numType := core.MakeCompositeType(core.MakeMetaType("num", 0))
	m := ext.Var("m", numType)
	nn := ext.Var("n", numType)
	_ = s.AddGoal(prop.MakeProp(core.Eq(m, nn)))

	out := dispatchRPCJSON(t, rpcParseTerm, map[string]any{
		"text":          "m = n",
		"session_id":    info.ID,
		"expected_type": "bool",
	})
	require.Equal(t, true, out["ok"], "term-preview of 'm = n' against expected bool must succeed: %v", out)
	require.NotEmpty(t, out["term_text"])

	// The constraint is read: a term of another type is refused.
	out = dispatchRPCJSON(t, rpcParseTerm, map[string]any{
		"text":          "m",
		"session_id":    info.ID,
		"expected_type": "bool",
	})
	require.Equal(t, false, out["ok"], "m : num against expected bool: %v", out)
}

// TestRpcParseTerm_MissingSession verifies the required-field guard.
// A bare term without a session has no type scope, and preview would
// be misleading — the RPC returns an error rather than "succeeding"
// against a nil scope.
func TestRpcParseTerm_MissingSession(t *testing.T) {
	initTestEngine()
	body, err := json.Marshal(map[string]any{"text": "n"})
	require.NoError(t, err)
	_, rpcErr := rpcParseTerm(body)
	require.Error(t, rpcErr,
		"parse-term without session_id must return an error, not a silent scope-blind parse")
	assert.Contains(t, rpcErr.Error(), "session_id")
}
