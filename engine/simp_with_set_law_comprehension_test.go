package engine

import (
	"context"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/stretchr/testify/require"
)

// TestSimpWith_SetLawAtSetsOfFunctionsFiresOnAComprehension: the union
// law `s ∪ t ⊆ u ⇔ s ⊆ u ∧ t ⊆ u`, read at sets of prod(B, C) → A —
// sets of FUNCTIONS — fires on a union whose left member is a
// comprehension, whatever the comprehension's body spells. The rule's
// variable s stands for a set of functions, so the unifier's η-long form
// applies it to an η-expanded bound variable (λp. x(p)); read modulo η
// that is the pattern `s(x)`, solved at once. Read as no pattern, the
// pair fell to the imitation chain, whose skeleton applies every helper
// to every enclosing binder and crossed the substitution size cut on the
// deeper body (a tied constant applied to two function arguments) while
// the shallower body (a bare constant) completed. The same tied body at
// an atomic element type is the negative control: sets of A, where the
// bound variable is bare and the pattern was always read.
func TestSimpWith_SetLawAtSetsOfFunctionsFiresOnAComprehension(t *testing.T) {
	const fnPrefix = "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀t w:set(prod(B, C) → A). " +
		"{r:(prod(B, C) → A) | ∃u:B. ∃v:C. u ∈ M.carrier ∧ v ∈ N.carrier ∧ r = "
	const atomPrefix = "∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). ∀t w:set(A). " +
		"{r:A | ∃u:B. ∃v:C. u ∈ M.carrier ∧ v ∈ N.carrier ∧ r = "
	const tied = "fun_add⟨D:prod(B, C)⟩(R.add, delta_at(R.zero, R.one, (u, v)), delta_at(R.zero, R.one, (u, v)))"
	for _, tc := range []struct{ name, goal string }{
		{"functions, bare constant", fnPrefix + "delta_at(R.zero, R.one, (u, v))} ∪ t ⊆ w"},
		{"functions, tied constant", fnPrefix + tied + "} ∪ t ⊆ w"},
		{"atomic element, tied constant", atomPrefix + tied + "((u, v))} ∪ t ⊆ w"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			e := newEngine(statedSessionEnv())
			info, err := e.CreateSession(context.Background())
			require.NoError(t, err)
			s, err := e.getSession(info.ID)
			require.NoError(t, err)
			parsed := dsl.ParsePropTextInScope(tc.goal, s.StatementDoorScope())
			require.Empty(t, parsed.Errors)
			s.AddGoal(parsed.Prop)
			applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "strip_quant"})
			res := applyOnSoleGoal(t, e, s.ID, TacticReq{Type: "simp_with",
				WithLemmas: []LemmaWithSpec{{Key: "set_order.UnionSubset"}}})
			state, err := e.InspectState(context.Background(), s.ID)
			require.NoError(t, err)
			require.Len(t, state.Goals, 1, "diagnostics: %v", res.Diagnostics)
			require.Contains(t, prop.PrintProp(state.Goals[0].Statement), "⊆ w₀) ∧ (t₀ ⊆ w₀)",
				"the union rewrites to the two inclusions; diagnostics: %v", res.Diagnostics)
		})
	}
}
