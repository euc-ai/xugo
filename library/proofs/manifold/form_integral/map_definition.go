// Oriented diffeomorphisms have positive coordinate Jacobians on chart preimages.

package form_integral

import (
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/registry"
)

var OrientedDiffeomorphismDef = orientedDiffeomorphismDefThm{family.Define(registry.DefEntry{
	Name:  "OrientedDiffeomorphismDef",
	Key:   "prop_8e3cb12981794d72",
	Const: "oriented_diffeomorphism",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"bool",
	Dim:  "n",
	Deps: []registry.EntryLike{OrientedManifoldDef, PositiveChartDef},
	Reading: "The forward map is a homeomorphism and both it and its carrier " +
		"inverse are smooth. Positivity is checked on open chart-preimage domains; " +
		"an entire source chart need not map into one target chart. The inverse has " +
		"arbitrary values off the target carrier, which the predicate does not use.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"    oriented_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f) ⇔ " +
			"    oriented_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    oriented_manifold⟨n⟩(S, ℬ) ∧ " +
			"    smooth_manifold_map⟨n, n⟩(T, 𝒜, S, ℬ, f) ∧ " +
			"    homeomorphic_map(T, S, f) ∧ " +
			"    smooth_manifold_map⟨n, n⟩(S, ℬ, T, 𝒜, inverse_on(⋃T, f)) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀d:prod(set(B), B → num → real). " +
			"        positive_manifold_chart⟨n⟩(T, 𝒜, c) ∧ positive_manifold_chart⟨n⟩(S, ℬ, d) ⇒ " +
			"        (∀y:(num → real). " +
			"            y ∈ «map domain»(c, d, f) ⇒ " +
			"            &0 < vec_jacobian_determinant⟨n⟩(«coordinate map»(c, d, f), y)))",
	},
})}
