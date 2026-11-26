// Restriction, completion by compatible charts, and smaller covering
// atlases all preserve the same smooth coordinate changes.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ChartRestrict = chartRestrictThm{family.Add(registry.ProofEntry{
	Name: "ChartRestrict",
	Key:  "prop_9460a8927168f2a4",
	Deps: []registry.EntryLike{
		ChartDef,
		continuous.HomeomorphismSubtopologies,
		continuous.HomeomorphismIffOpenBijection,
		topological_space.OpenInOpenSubtopology,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀c:prod(set(A), A → num → real). ∀U:set(A).",
		Hypotheses: []string{"manifold_chart⟨n⟩(T, c)", "U ∈ T", "U ⊆ fst(c)"},
		Conclusion: "manifold_chart⟨n⟩(T, (U, snd(c)))",
	},
		"Restrict the chart homeomorphism to U. Its image is open in the chart "+
			"image and hence in Euclidean space, and subtopology transitivity "+
			"identifies the source and target topologies of the restriction."),
})}

var AtlasMemberCompatible = atlasMemberCompatibleThm{family.Add(registry.ProofEntry{
	Name: "AtlasMemberCompatible",
	Key:  "prop_dd807c9224d7d1fc",
	Deps: []registry.EntryLike{AtlasDef, CompatibleChartDef},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real).",
		Hypotheses: []string{"smooth_atlas⟨n⟩(T, 𝒜)", "c ∈ 𝒜"},
		Conclusion: "compatible_chart⟨n⟩(T, 𝒜, c)",
	},
		"The atlas condition supplies the chart and each transition in both orders. "+
			"These are exactly the compatibility conditions with every member of the atlas."),
})}

var CompatibleTransition = compatibleTransitionThm{family.Add(registry.ProofEntry{
	Name: "CompatibleTransition",
	Key:  "prop_7b755040f834cbc2",
	Reading: "The covering condition is essential: compatibility with an " +
		"empty, noncovering chart family would impose no smoothness. No " +
		"Hausdorff or countability assumption is needed for this local argument.",
	Deps: []registry.EntryLike{
		CompatibleChartDef,
		AtlasDef,
		continuous.HomeomorphismInverse,
		functions.InverseOnLeft,
		functions.InverseOnRight,
		vec_smooth.SmoothMapCompose,
		vec_smooth.SmoothLocal,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c d:prod(set(A), A → num → real).",
		Hypotheses: []string{
			"smooth_atlas⟨n⟩(T, 𝒜)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"compatible_chart⟨n⟩(T, 𝒜, d)",
		},
		Conclusion: "«overlap»(c, d) ∈ euclidean_topology(n) ∧ " +
			"«overlap»(d, c) ∈ euclidean_topology(n) ∧ " +
			"vec_diffeomorphic_map⟨n⟩(«overlap»(c, d), «overlap»(d, c), «transition»(c, d))",
	},
		"At each overlap point choose an atlas chart containing the corresponding manifold point. On "+
			"the resulting open triple overlap, the transition factors through two smooth transitions; "+
			"local smoothness and agreement on open sets glue these expressions. Interchanging c and d "+
			"gives a smooth inverse, with the inverse identities supplied by inverse_on on the chart images."),
})}

var CompatibleAtlas = compatibleAtlasThm{family.Add(registry.ProofEntry{
	Name: "CompatibleAtlas",
	Key:  "prop_2f4b435695525063",
	Deps: []registry.EntryLike{AtlasMemberCompatible, CompatibleTransition, AtlasDef},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_atlas⟨n⟩(T, 𝒜)"},
		Conclusion: "smooth_atlas⟨n⟩(T, «compatible atlas»)",
	},
		"Every original chart lies in the compatible family, so it still "+
			"covers the space. CompatibleTransition supplies smooth transitions "+
			"for every pair in that family; each member is a chart by definition."),
})}

var CompatibleAtlasInvariant = compatibleAtlasInvariantThm{family.Add(registry.ProofEntry{
	Name: "CompatibleAtlasInvariant",
	Key:  "prop_da1bd0fc193c4598",
	Deps: []registry.EntryLike{AtlasMemberCompatible, CompatibleTransition, CompatibleChartDef},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real).",
		Hypotheses: []string{"smooth_atlas⟨n⟩(T, 𝒜)"},
		Conclusion: "compatible_chart⟨n⟩(T, «compatible atlas», c) ⇔ compatible_chart⟨n⟩(T, 𝒜, c)",
	},
		"Compatibility with all compatible charts implies compatibility with the "+
			"original subfamily. Conversely, CompatibleTransition gives both smooth "+
			"transition directions between any two charts compatible with the original atlas."),
})}

var AtlasSubcover = atlasSubcoverThm{family.Add(registry.ProofEntry{
	Name: "AtlasSubcover",
	Key:  "prop_78461a9024f648a4",
	Deps: []registry.EntryLike{AtlasDef, CompatibleTransition, AtlasMemberCompatible},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜 ℬ:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_atlas⟨n⟩(T, 𝒜)", "ℬ ⊆ 𝒜", "⋃image(fst, ℬ) = ⋃T"},
		Conclusion: "smooth_atlas⟨n⟩(T, ℬ) ∧ " +
			"{c:prod(set(A), A → num → real) | compatible_chart⟨n⟩(T, ℬ, c)} = «compatible atlas»",
	},
		"The subcover inherits charts and transitions, so it is an atlas. Every original "+
			"chart is compatible with this subatlas; applying CompatibleTransition relative to "+
			"the subatlas shows that any chart compatible with it is compatible with the original "+
			"atlas. The reverse inclusion follows by restriction of the compatibility tests."),
})}

var CountableAtlas = countableAtlasThm{family.Add(registry.ProofEntry{
	Name: "CountableAtlas",
	Key:  "prop_eb6d8c3c85c0f3d",
	Reading: "Countability is of the selected charts, not just of their domains. " +
		"Choice selects one original chart above each domain in a countable subcover; " +
		"duplicate domains cause no problem. The empty carrier admits the empty subatlas.",
	Deps: []registry.EntryLike{
		ManifoldDef,
		AtlasSubcover,
		countability.SecondCountableImpLindelof,
		countability.LindelofSpaceDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "∃ℬ:set(prod(set(A), A → num → real)). " +
			"    ℬ ⊆ 𝒜 ∧ " +
			"    countable(ℬ) ∧ " +
			"    smooth_atlas⟨n⟩(T, ℬ) ∧ " +
			"    {c:prod(set(A), A → num → real) | compatible_chart⟨n⟩(T, ℬ, c)} = «compatible atlas»",
	},
		"Second countability gives Lindelofness, which selects countably many chart "+
			"domains covering the carrier. Choose one original chart for each selected "+
			"domain, then apply AtlasSubcover to retain precisely the same compatible charts."),
})}
