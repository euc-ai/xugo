// Immersions have injective coordinate differentials; embeddings also carry the image topology.

package smooth_manifold

import (
	"github.com/euc-ai/xugo/library/registry"
)

var ImmersionDef = immersionDefThm{family.Define(registry.DefEntry{
	Name:  "ImmersionDef",
	Key:   "prop_e1e47ecf4cee5aa3",
	Const: "smooth_manifold_immersion",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"bool",
	Dimensions: []string{"n", "m"},
	Reading: "An immersion is a smooth map whose coordinate Jacobian acts injectively on the " +
		"normalized source vectors at every active chart pair. Both manifold structures and carrier " +
		"continuity are included; no condition is imposed on Jacobians outside an active chart domain.",
	Deps: []registry.EntryLike{SmoothMapDef, CompatibleChartDef},
	Equations: []string{
		"∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"    smooth_manifold_immersion⟨n, m⟩(T, 𝒜, S, ℬ, f) ⇔ " +
			"    smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀d:prod(set(B), B → num → real). ∀x:A. " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"        compatible_chart⟨m⟩(S, ℬ, d) ∧ " +
			"        x ∈ fst(c) ∧ " +
			"        f(x) ∈ fst(d) ⇒ " +
			"        injective_on({y:num → real | vec⟨n⟩(y)}, " +
			"            matrix_act⟨n⟩(vec_jacobian_matrix⟨n, m⟩(«coordinate map»(c, d, f), snd(c)(x)))))",
	},
})}

var EmbeddingDef = embeddingDefThm{family.Define(registry.DefEntry{
	Name:  "EmbeddingDef",
	Key:   "prop_ec012f995831e8d8",
	Const: "smooth_manifold_embedding",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"bool",
	Dimensions: []string{"n", "m"},
	Reading: "The topological condition is a homeomorphism from the source " +
		"carrier to its image with the subspace topology. A smooth injective map " +
		"need not be an immersion or an embedding; both requirements are retained.",
	Deps: []registry.EntryLike{ImmersionDef},
	Equations: []string{
		"∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"    smooth_manifold_embedding⟨n, m⟩(T, 𝒜, S, ℬ, f) ⇔ " +
			"    smooth_manifold_immersion⟨n, m⟩(T, 𝒜, S, ℬ, f) ∧ embedding_map(T, S, f)",
	},
})}
