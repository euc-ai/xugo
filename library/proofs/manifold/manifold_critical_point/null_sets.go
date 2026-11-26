// Smooth coordinate changes preserve chartwise nullity, including the zero-dimensional convention.

package manifold_critical_point

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_null"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var NullEmpty = nullEmptyThm{family.Add(registry.ProofEntry{
	Name: "NullEmpty",
	Key:  "prop_400441cd88079b44",
	Deps: []registry.EntryLike{NullSetDef, vec_null.NullEmpty},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
		},
		Conclusion: "manifold_null_set⟨n⟩(T, 𝒜, ∅)",
	},
		"Every chart image of the empty set is empty. Apply NullEmpty "+
			"in Euclidean coordinates and the carrier clause of NullSetDef."),
})}

var NullSubset = nullSubsetThm{family.Add(registry.ProofEntry{
	Name: "NullSubset",
	Key:  "prop_8bd9a90b9bf7337c",
	Deps: []registry.EntryLike{NullSetDef, vec_null.NullSubset},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀K L:set(A).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"K ⊆ L",
			"manifold_null_set⟨n⟩(T, 𝒜, L)",
		},
		Conclusion: "manifold_null_set⟨n⟩(T, 𝒜, K)",
	},
		"The carrier inclusion and each chart-image inclusion follow from K being "+
			"a subset of L. Apply Euclidean NullSubset in every compatible chart."),
})}

var NullCountableUnion = nullCountableUnionThm{family.Add(registry.ProofEntry{
	Name: "NullCountableUnion",
	Key:  "prop_c980cc326355cb76",
	Reading: "Countability is of the family of sets; no countability of " +
		"individual members is required. The empty family gives the empty null set.",
	Deps: []registry.EntryLike{NullSetDef, vec_null.NullCountableUnion},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀𝒦:set(set(A)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"countable(𝒦)",
			"∀K:set(A). K ∈ 𝒦 ⇒ manifold_null_set⟨n⟩(T, 𝒜, K)",
		},
		Conclusion: "manifold_null_set⟨n⟩(T, 𝒜, ⋃𝒦)",
	},
		"Intersect with a chart domain and take its image to commute these operations with the union. "+
			"The resulting family of coordinate sets is countable, so Euclidean NullCountableUnion applies."),
})}

var NullAtlasCriterion = nullAtlasCriterionThm{family.Add(registry.ProofEntry{
	Name: "NullAtlasCriterion",
	Key:  "prop_98e25d82ceaa7094",
	Reading: "The original atlas may be uncountable. Second countability selects a " +
		"countable covering subatlas before the union argument; the all-compatible-chart " +
		"definition cannot be replaced by an arbitrary uncountable union argument.",
	Deps: []registry.EntryLike{
		NullSetDef,
		smooth_manifold.AtlasMemberCompatible,
		smooth_manifold.CountableAtlas,
		smooth_manifold.CompatibleTransition,
		vec_smooth.ContinuouslyDifferentiableLocallyLipschitz,
		vec_null.LocallyLipschitzPreservesNull,
		vec_null.NullSubset,
		vec_null.NullCountableUnion,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀K:set(A).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
		},
		Conclusion: "manifold_null_set⟨n⟩(T, 𝒜, K) ⇔ " +
			"K ⊆ ⋃T ∧ (∀c:prod(set(A), A → num → real). c ∈ 𝒜 ⇒ vec_null_set⟨n⟩(image(snd(c), K ∩ fst(c))))",
	},
		"The forward implication uses AtlasMemberCompatible. Choose a countable subatlas for the "+
			"converse; each part of a compatible chart image is the image of a null coordinate subset "+
			"under a smooth transition, hence null by ContinuouslyDifferentiableLocallyLipschitz and "+
			"LocallyLipschitzPreservesNull. Assemble the countably many parts by NullCountableUnion."),
})}

var NullAtlasInvariant = nullAtlasInvariantThm{family.Add(registry.ProofEntry{
	Name: "NullAtlasInvariant",
	Key:  "prop_55e2dd2858eb5a34",
	Reading: "The second family must itself be a covering smooth atlas. An empty " +
		"noncovering family would not determine the same null sets on a nonempty carrier.",
	Deps: []registry.EntryLike{
		NullAtlasCriterion,
		smooth_manifold.CompatibleTransition,
		smooth_manifold.CompatibleChartDef,
		vec_smooth.SmoothLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ℬ:set(prod(set(A), A → num → real)). " +
			"∀K:set(A).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨n⟩(T, ℬ)",
			"∀c:prod(set(A), A → num → real). c ∈ ℬ ⇒ compatible_chart⟨n⟩(T, 𝒜, c)",
		},
		Conclusion: "manifold_null_set⟨n⟩(T, 𝒜, K) ⇔ manifold_null_set⟨n⟩(T, ℬ, K)",
	},
		"The positive direction tests the covering atlas ℬ by NullAtlasCriterion. Compatibility "+
			"with the covering family ℬ implies compatibility with 𝒜 by locally factoring "+
			"transitions through its charts; the reverse implication then uses the same criterion."),
})}

var NullOpenRestrict = nullOpenRestrictThm{family.Add(registry.ProofEntry{
	Name: "NullOpenRestrict",
	Key:  "prop_39a68e77cadf00c3",
	Reading: "K must lie inside the open U. The atlas is the ambient compatible " +
		"atlas restricted to U; no independent smooth structure is substituted.",
	Deps: []registry.EntryLike{
		NullSetDef,
		smooth_manifold.OpenSubmanifold,
		smooth_manifold.OpenCompatibleChart,
		smooth_manifold.ChartRestrict,
		vec_null.NullSubset,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U K:set(A).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"K ⊆ U",
		},
		Conclusion: "manifold_null_set⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), K) ⇔ " +
			"manifold_null_set⟨n⟩(T, 𝒜, K)",
	},
		"OpenCompatibleChart identifies the submanifold charts with ambient "+
			"compatible charts lying in U. Restrict any ambient chart to its intersection "+
			"with U; its image of K is unchanged there, giving both implications."),
})}

var NullEuclidean = nullEuclideanThm{family.Add(registry.ProofEntry{
	Name: "NullEuclidean",
	Key:  "prop_fa2fcc6c685e9e5c",
	Deps: []registry.EntryLike{
		NullAtlasCriterion,
		smooth_manifold.EuclideanManifold,
		smooth_manifold.EuclideanAtlasDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U K:set(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"K ⊆ U",
		},
		Conclusion: "manifold_null_set⟨n⟩(subtopology(euclidean_topology(n), U), " +
			"    euclidean_atlas(U), " +
			"    K) ⇔ " +
			"vec_null_set⟨n⟩(K)",
	},
		"Apply NullAtlasCriterion to the single identity chart of the "+
			"Euclidean open U. Its image of K is K by the given inclusion."),
})}

var NullZeroDimension = nullZeroDimensionThm{family.Add(registry.ProofEntry{
	Name: "NullZeroDimension",
	Key:  "prop_cdb62e708d4037e2",
	Reading: "The zero-dimensional convention does not declare isolated " +
		"points null. This conclusion also includes the empty manifold.",
	Deps: []registry.EntryLike{
		NullSetDef,
		NullEmpty,
		smooth_manifold.AtlasDef,
		vec_null.NullZeroDimension,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀K:set(A).",
		Hypotheses: []string{
			"smooth_manifold⟨0⟩(T, 𝒜)",
		},
		Conclusion: "manifold_null_set⟨0⟩(T, 𝒜, K) ⇔ K = ∅",
	},
		"Euclidean NullZeroDimension makes the image of K in each chart "+
			"empty. The chart domains cover the carrier and NullSetDef excludes "+
			"exterior points, so K is empty; NullEmpty proves the converse."),
})}

var NullOpenIffEmpty = nullOpenIffEmptyThm{family.Add(registry.ProofEntry{
	Name: "NullOpenIffEmpty",
	Key:  "prop_5df04d1bee94cad8",
	Reading: "This holds in dimension zero as well as positive " +
		"dimension, using the explicit zero-dimensional null convention.",
	Deps: []registry.EntryLike{
		NullSetDef,
		NullEmpty,
		NullZeroDimension,
		smooth_manifold.ChartRestrict,
		vec_null.OpenNonemptyNotNull,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U:set(A).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
		},
		Conclusion: "manifold_null_set⟨n⟩(T, 𝒜, U) ⇔ U = ∅",
	},
		"For a nonempty open U choose a chart through one of its points. Its image of U intersected "+
			"with the chart domain is a nonempty Euclidean open set, contradicting OpenNonemptyNotNull "+
			"when n is positive; NullZeroDimension handles n zero. NullEmpty supplies the converse."),
})}

var NullDiffeomorphism = nullDiffeomorphismThm{family.Add(registry.ProofEntry{
	Name: "NullDiffeomorphism",
	Key:  "prop_c782368237eed7b3",
	Reading: "The source and target dimensions agree and f has a smooth inverse. No " +
		"orientation or compactness is required; no assertion is made for arbitrary " +
		"dimension-changing smooth maps. The carrier restriction on K is needed to recover " +
		"it through the carrier inverse; chart tests cannot control exterior points.",
	Deps: []registry.EntryLike{
		NullAtlasCriterion,
		smooth_manifold.CountableAtlas,
		smooth_manifold.DiffeomorphismDef,
		smooth_manifold.DiffeomorphismInverse,
		smooth_manifold.SmoothMapCompatibleCharts,
		vec_smooth.ContinuouslyDifferentiableLocallyLipschitz,
		vec_null.LocallyLipschitzPreservesNull,
		vec_null.NullSubset,
		vec_null.NullCountableUnion,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀K:set(A).",
		Hypotheses: []string{
			"smooth_manifold_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)",
			"K ⊆ ⋃T",
		},
		Conclusion: "manifold_null_set⟨n⟩(S, ℬ, image(f, K)) ⇔ manifold_null_set⟨n⟩(T, 𝒜, K)",
	},
		"Choose countable source charts and work inside each target-chart preimage. Coordinate "+
			"expressions are smooth maps of equal dimensions and preserve null subsets by local "+
			"Lipschitzness. Use the carrier inverse and DiffeomorphismInverse for the reverse implication."),
})}
