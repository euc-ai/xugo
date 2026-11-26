package engine

import (
	"strings"
	"testing"

	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/require"
)

// TestEmitSection_BySourceSurvivesClauseCertification emits a named
// entry's cite when its exact instance certifies through a derived
// clause whose quantifier sharing differs from the entry's statement:
// the premise's recorded source key names the entry, and the emitted
// member replays.
func TestEmitSection_BySourceSurvivesClauseCertification(t *testing.T) {
	const coalesced = "∀R:comm_ring_on(A). ∀S:set(A). ∀V:module_ops(A, A). ∀f:(A → A). subring(R, S) ∧ module_homomorphism(restrict_ring(R, S), V, V, f) ⇒ module_homomorphism(R, scalar_extension(restrict_ring(R, S), R, V), scalar_extension(restrict_ring(R, S), R, V), scalar_extension_map(restrict_ring(R, S), R, V, V, f)) ∧ (∀a x:A. a ∈ R.carrier ∧ x ∈ V.carrier ⇒ scalar_extension_map(restrict_ring(R, S), R, V, V, f)(tensor(restrict_ring(R, S), regular_module(R), V, a, x)) = tensor(restrict_ring(R, S), regular_module(R), V, a, f(x)))"
	nested := strings.NewReplacer("comm_ring_on(A)", "comm_ring_on(set(A))", "∀S:set(A)", "∀S:set(set(A))", "module_ops(A, A)", "module_ops(set(A), B)", "(A → A)", "(B → B)", "∀a x:A.", "∀a:set(A). ∀x:B.").Replace(coalesced)
	for _, tc := range []struct{ name, goal string }{{"coalesced", coalesced}, {"nested_scalars", nested}} {
		t.Run(tc.name, func(t *testing.T) {
			e, s := boundSession(t, "algebra/module/scalar_extension")
			parsed := dsl.ParsePropTextAtDoor(tc.goal, s.StatementDoorScope())
			require.Empty(t, parsed.Errors)
			s.AddGoal(parsed.Prop)
			for _, tactic := range []string{"strip_quant", "strip_imp", "strip_quant", "strip_imp"} {
				applyOnSoleGoal(t, e, s.ID, TacticReq{Type: tactic})
			}
			applyOnSoleGoal(t, e, s.ID, TacticReq{
				Type:    "by",
				ByHyps:  []ByHypSpec{hyp(0), hyp(1)},
				ByShape: &ByShapeReq{Normalized: true},
				WithLemmas: []LemmaWithSpec{{Key: "scalar_extension.ScalarExtensionMapSpec", TermSpecialize: map[string]string{
					"R": "R₀", "S": "S₀", "V": "V₀", "W": "V₀", "f": "f₀",
				}}},
			})
			out, err := e.EmitSection(&EmitSectionRequest{
				SessionID: s.ID, Section: 0, Family: "algebra/module/scalar_extension", FuncName: "Build_ZzBySourceClause",
			})
			require.NoError(t, err)
			require.NotContains(t, out.Go, "TODO: unresolved lemma")
			require.Contains(t, out.DepNames, "scalar_extension.ScalarExtensionMapSpec")
			replayEmittedInFamily(t, "algebra/module/scalar_extension", "ZzBySourceClause", out)
		})
	}
}
