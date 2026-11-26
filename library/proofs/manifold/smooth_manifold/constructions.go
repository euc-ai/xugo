// Euclidean open sets, the empty space, open submanifolds and products
// satisfy the manifold carrier conditions, including dimension zero.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var EuclideanManifold = euclideanManifoldThm{family.Add(registry.ProofEntry{
	Name: "EuclideanManifold",
	Key:  "prop_dd67c0060d896f69",
	Deps: []registry.EntryLike{
		EuclideanAtlasDef,
		ManifoldDef,
		continuous.HomeomorphismIdentity,
		euclidean_topology.EuclideanTopology,
		euclidean_topology.EuclideanHausdorff,
		euclidean_topology.EuclideanSecondCountable,
		countability.SecondCountableSubtopology,
		topological_space.HausdorffSubtopology,
		vec_smooth.LinearSmoothMap,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀U:set(num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)"},
		Conclusion: "smooth_manifold⟨n⟩(subtopology(euclidean_topology(n), U), euclidean_atlas(U))",
	},
		"Use the identity chart on U. Its transition agrees with the identity on U and is "+
			"smooth there; Euclidean Hausdorffness and second countability pass to the subtopology. "+
			"This includes the empty open set and the singleton zero-dimensional Euclidean space."),
})}

var EmptyManifold = emptyManifoldThm{family.Add(registry.ProofEntry{
	Name: "EmptyManifold",
	Key:  "prop_f784427d2ccd6160",
	Deps: []registry.EntryLike{ManifoldDef, AtlasDef, countability.SecondCountableSpaceDef},
	Build: family.Card(
		"∀n:num. smooth_manifold⟨n⟩({∅⟨A:A⟩}, ∅⟨A:prod(set(A), A → num → real)⟩)",
		"The topology containing only the empty set has empty carrier, is Hausdorff and has an empty "+
			"countable base. The empty atlas covers it and all chart and transition conditions are vacuous."),
})}

var OpenSubmanifold = openSubmanifoldThm{family.Add(registry.ProofEntry{
	Name: "OpenSubmanifold",
	Key:  "prop_ef4c68439fdf7d8e",
	Deps: []registry.EntryLike{
		OpenAtlasDef,
		ChartRestrict,
		CompatibleTransition,
		AtlasMemberCompatible,
		countability.SecondCountableSubtopology,
		topological_space.HausdorffSubtopology,
		topological_space.OpenInOpenSubtopology,
		vec_smooth.SmoothSubset,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U:set(A).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T"},
		Conclusion: "smooth_manifold⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U))",
	},
		"Restrict each original chart to its intersection with U. The restricted inverse "+
			"agrees on its image with the original inverse, so smoothness on these open subsets "+
			"makes the restricted chart compatible. These charts cover U; CompatibleTransition "+
			"gives all transitions, and Hausdorffness and second countability pass to the subspace."),
})}

var OpenCompatibleChart = openCompatibleChartThm{family.Add(registry.ProofEntry{
	Name: "OpenCompatibleChart",
	Key:  "prop_2e2be595cc77797e",
	Reading: "U must be open in T: only then is a submanifold chart domain " +
		"also open in the original space. The formula uses exactly the same chart " +
		"pair and makes no choice of an extension of its coordinate function.",
	Deps: []registry.EntryLike{
		OpenSubmanifold,
		OpenAtlasDef,
		CompatibleTransition,
		ChartRestrict,
		topological_space.OpenInOpenSubtopology,
		vec_smooth.SmoothLocal,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀c:prod(set(A), A → num → real).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T"},
		Conclusion: "compatible_chart⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), c) ⇔ " +
			"compatible_chart⟨n⟩(T, 𝒜, c) ∧ fst(c) ⊆ U",
	},
		"A compatible chart of the submanifold has domain in U, and its overlaps with "+
			"original charts can be tested against their restrictions to U. Conversely a chart "+
			"compatible with the original atlas and lying in U is a chart of the subspace and "+
			"has smooth transitions with every member of its atlas by CompatibleTransition."),
})}

var ProductManifold = productManifoldThm{family.Add(registry.ProofEntry{
	Name: "ProductManifold",
	Key:  "prop_e79967ba29691c68",
	Reading: "Product coordinates have a separate zero guard after " +
		"n+m. No nonempty or positive-dimension hypothesis is needed; " +
		"the product atlas may be empty when a factor has empty carrier.",
	Deps: []registry.EntryLike{
		ProductAtlasDef,
		ManifoldDef,
		product_topology.ProductTopology,
		product_topology.HausdorffProduct,
		product_topology.SecondCountableProduct,
		product_topology.PairedContinuousIff,
		euclidean_topology.ContinuousIffCoordinates,
		vec_smooth.SmoothMapCompose,
		vec_smooth.LinearSmoothMap,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "smooth_manifold⟨m⟩(S, ℬ)"},
		Conclusion: "smooth_manifold⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ))",
	},
		"Concatenation and its two padded coordinate projections identify the product of "+
			"Euclidean chart images with an open set in R^(n+m); they are continuous linear maps in "+
			"coordinates. Each product transition is the pair of the factor transitions, so its "+
			"coordinates are smooth compositions with the block projections. Chart pairs cover the "+
			"product, and the existing product theorems supply Hausdorffness and second countability."),
})}
