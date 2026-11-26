// Compatible factor charts give compatible product charts.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ProductCompatibleChart = productCompatibleChartThm{family.Add(registry.ProofEntry{
	Name: "ProductCompatibleChart",
	Key:  "prop_1e5e7b8a39949c6e",
	Reading: "The factors may be any compatible charts, not just members of the two original " +
		"atlases. Their product uses the same padded coordinate order as ProductAtlasDef.",
	Deps: []registry.EntryLike{
		ProductManifold,
		CompatibleChartDef,
		CompatibleTransition,
		ChartDef,
		vec_smooth.SmoothMapCompose,
		vec_smooth.LinearSmoothMap,
		product_topology.PairedContinuousIff,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀d:prod(set(B), B → num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"compatible_chart⟨m⟩(S, ℬ, d)",
		},
		Conclusion: "compatible_chart⟨n + m⟩(product_topology(T, S), " +
			"    smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"    «product chart»(c, d))",
	},
		"The product of the two chart homeomorphisms is a chart on the product open domain. Its "+
			"transitions with original product charts are block pairs of the compatible factor transitions, "+
			"hence smooth in both directions. This includes empty chart domains and zero-dimensional factors."),
})}
