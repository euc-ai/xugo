// The two product projections and pairing of maps express the smooth
// universal property using the concatenated product charts.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var SmoothProductProjections = smoothProductProjectionsThm{family.Add(registry.ProofEntry{
	Name: "SmoothProductProjections",
	Key:  "prop_2c76fad9e43dcfae",
	Deps: []registry.EntryLike{
		ProductManifold,
		ProductAtlasDef,
		CompatibleTransition,
		product_topology.PairedContinuousIff,
		vec_smooth.LinearSmoothMap,
		vec_smooth.SmoothMapCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "smooth_manifold⟨m⟩(S, ℬ)"},
		Conclusion: "smooth_manifold_map⟨n + m, n⟩(product_topology(T, S), " +
			"    smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"    T, " +
			"    𝒜, " +
			"    fst) ∧ " +
			"smooth_manifold_map⟨n + m, m⟩(product_topology(T, S), " +
			"    smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"    S, " +
			"    ℬ, " +
			"    snd)",
	},
		"The projections are continuous in the product topology. In aligned product charts they are the "+
			"two padded linear block projections; in any other target chart they compose with a smooth "+
			"factor transition on its overlap. LinearSmoothMap and smooth composition give both chart tests."),
})}

var SmoothProductPair = smoothProductPairThm{family.Add(registry.ProofEntry{
	Name: "SmoothProductPair",
	Key:  "prop_2f80f8dd11227b33",
	Reading: "The source chart is injective on its domain. Thus the coordinate image of " +
		"the intersection of the two factor preimages equals the intersection of their " +
		"coordinate images; the coordinate tests can be restricted to this common open domain.",
	Deps: []registry.EntryLike{
		ProductManifold,
		ProductAtlasDef,
		SmoothMapDef,
		product_topology.PairedContinuousIff,
		vec_smooth.SmoothSubset,
	},
	Build: family.Card(Statement{
		Binders: "∀k n m:num. " +
			"∀R:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(C → A). " +
			"∀g:(C → B).",
		Hypotheses: []string{
			"smooth_manifold_map⟨k, n⟩(R, 𝒞, T, 𝒜, f)",
			"smooth_manifold_map⟨k, m⟩(R, 𝒞, S, ℬ, g)",
		},
		Conclusion: "smooth_manifold_map⟨k, n + m⟩(R, " +
			"    𝒞, " +
			"    product_topology(T, S), " +
			"    smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"    λx:C. (f(x), g(x)))",
	},
		"Pairing continuous maps gives a continuous map into the product. The preimage "+
			"of a product chart is the intersection of the two factor-chart preimages; on "+
			"it the concatenated coordinate functions are the smooth coordinates of f and "+
			"g restricted to this open intersection, with the required zero tail."),
})}
