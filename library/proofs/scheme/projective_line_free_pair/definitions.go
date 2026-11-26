// definitions.go — the free pairs on the projective line: the sums of the
// O(N(e)) · e along field elements e.

package projective_line_free_pair

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/laurent_polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

// ProjectiveLineFreePairDef — `projective_line_free_pair(L, k, t, E, N)`,
// the sum of the O(N(e)) · e over e in E: chart 0 the k[t]-span of E,
// chart 1 the k[1/t]-span of the t^N(e) · e.
var ProjectiveLineFreePairDef = projectiveLineFreePairDefThm{family.Define(registry.DefEntry{
	Name:     "ProjectiveLineFreePairDef",
	Key:      "prop_4eea868b78277618",
	Const:    "projective_line_free_pair",
	Type:     "field_ops(A) → set(A) → A → set(A) → (A → int) → prod(set(A), set(A))",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀t:A. ∀E:set(A). ∀N:(A → int). " +
			"    projective_line_free_pair(F, k, t, E, N) = " +
			"    (module_span(restrict_ring(field_ring(F), polynomial_image(field_ring(F), k, t)), " +
			"            regular_module(field_ring(F)), " +
			"            E), " +
			"        module_span(restrict_ring(field_ring(F), polynomial_image(field_ring(F), k, F.inv(t))), " +
			"            regular_module(field_ring(F)), " +
			"            {F.mul(laurent_monomial(F.mul, F.one, F.inv, t, N(e)), e) | e:A | e ∈ E}))",
	},
	Deps: []registry.EntryLike{},
})}
