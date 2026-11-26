package main

import (
	"testing"

	"github.com/euc-ai/xugo/library/registry"
	"github.com/stretchr/testify/require"
)

// The query and add-goal handlers agree on a member's family scope and
// served text. These cases cover distinct input forms; the exhaustive
// member census and round-trip check belong to TestServedStatementSurface
// in library/integrity/gates.
func TestAddGoal_ReadsServedStatementTyped(t *testing.T) {
	initTestEngine()
	base := startTestServer(t)
	for _, tc := range []struct{ name, member, fragment string }{
		{"polymorphic_set_builder", "set_image.SimpleImageGen", "{f(x):B | x:A | P(x)}"},
		{"chapter_notation", "euclidean.NormTriangle", "‖u + v‖_n"},
		{"implicit_structure", "euclidean.LinearBasisBound", "vec_linear(f)"},
		{"numeric_domain", "euclidean.NormNonneg", "&0"},
		{"computed_definition", "set_basic.UnionDef", "s ∪ t"},
		{"induction_principle", "list.Induction", "∀P:(list(A) → bool)"},
		{"authored_set_binder", "tor_ext.TensorComplex", "∀S:(num → set(I))"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			entry, ok := registry.ByName(tc.member)
			require.True(t, ok, "%s is registered", tc.member)

			member := rpcCall(t, base, map[string]any{
				"cmd": "query", "what": "member", "member": tc.member,
			})
			require.NotContains(t, member, "error")
			require.Equal(t, entry.Family().Name, member["family"])
			typed, ok := member["statement_typed"].(string)
			require.True(t, ok, "%s serves statement_typed", tc.member)
			require.Contains(t, typed, tc.fragment, "the fixture exercises its input form")

			created := rpcCall(t, base, map[string]any{
				"cmd": "session-create", "family": member["family"],
			})
			require.NotContains(t, created, "error")
			sid, ok := created["id"].(string)
			require.True(t, ok)
			t.Cleanup(func() { require.NoError(t, eng.CloseSession(t.Context(), sid)) })

			added := rpcCall(t, base, map[string]any{
				"cmd": "add-goal", "session_id": sid,
				"goal": map[string]any{"text": typed},
			})
			require.NotContains(t, added, "error", "%s: %s", tc.member, typed)
			goalID, ok := added["goal_id"].(string)
			require.True(t, ok)

			// Observe the stored proposition without enumerating structural
			// tactics, which are independent of the text-input contract.
			state, err := eng.InspectState(t.Context(), sid)
			require.NoError(t, err)
			require.Len(t, state.Goals, 1)
			require.Equal(t, goalID, state.Goals[0].ID)
			require.Equal(t, entry.Statement().Prop.AlphaKey(), state.Goals[0].Statement.AlphaKey(),
				"%s: the pasted text states the member's proposition", tc.member)
		})
	}
}
