// Smoothness is independent of atlas completion and is local on the
// source. Maps are total functions with conditions only on the carrier.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var SmoothMapCompatibleCharts = smoothMapCompatibleChartsThm{family.Add(registry.ProofEntry{
	Name: "SmoothMapCompatibleCharts",
	Key:  "prop_75fba6f65a011217",
	Reading: "Each coordinate expression is tested on the source chart restricted by the target " +
		"chart's preimage. A whole source chart need not map into any one target chart. Continuity makes " +
		"these domains open, so smooth local agreement ignores arbitrary inverse_on values elsewhere.",
	Deps: []registry.EntryLike{
		SmoothMapDef,
		AtlasMemberCompatible,
		CompatibleTransition,
		vec_smooth.SmoothMapCompose,
		vec_smooth.SmoothLocal,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "smooth_manifold⟨m⟩(S, ℬ)"},
		Conclusion: "smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f) ⇔ " +
			"continuous_map(T, S, f) ∧ " +
			"(∀c:prod(set(A), A → num → real). ∀d:prod(set(B), B → num → real). " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ∧ compatible_chart⟨m⟩(S, ℬ, d) ⇒ " +
			"    vec_smooth_map_on⟨n, m⟩(«map domain»(c, d, f), «coordinate map»(c, d, f)))",
	},
		"Near each source point choose original source and target charts containing "+
			"the point and its image. The new coordinate expression is a composition of "+
			"two compatible transitions with the original coordinate expression, on an "+
			"open neighbourhood where all three are defined. Locality yields smoothness on "+
			"the full chart preimage; the converse tests only the original atlas members."),
})}

var SmoothMapIdentity = smoothMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "SmoothMapIdentity",
	Key:  "prop_508f2c9eea280a12",
	Deps: []registry.EntryLike{SmoothMapDef, AtlasDef, continuous.Identity},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "smooth_manifold_map⟨n, n⟩(T, 𝒜, T, 𝒜, identity_map)",
	},
		"The identity is continuous and its expression between two charts is exactly "+
			"their transition on the overlap image. AtlasDef supplies its smoothness."),
})}

var SmoothMapCompose = smoothMapComposeThm{family.Add(registry.ProofEntry{
	Name: "SmoothMapCompose",
	Key:  "prop_a24950b04f0c1862",
	Deps: []registry.EntryLike{
		SmoothMapDef,
		continuous.Compose,
		functions.InverseOnLeft,
		vec_smooth.SmoothMapCompose,
		vec_smooth.SmoothLocal,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀R:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀f:(A → B). " +
			"∀g:(B → C).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"smooth_manifold_map⟨m, k⟩(S, ℬ, R, 𝒞, g)",
		},
		Conclusion: "smooth_manifold_map⟨n, k⟩(T, 𝒜, R, 𝒞, g ∘ f)",
	},
		"Continuity composes. Locally choose an intermediate chart containing f(x); the "+
			"coordinate expression of g∘f agrees with the composite of the two coordinate "+
			"expressions on an open neighbourhood. SmoothMapCompose and SmoothLocal then "+
			"give the required expression on each source/target chart preimage."),
})}

var SmoothMapConstant = smoothMapConstantThm{family.Add(registry.ProofEntry{
	Name: "SmoothMapConstant",
	Key:  "prop_cd7384cb1b0dfb07",
	Deps: []registry.EntryLike{
		SmoothMapDef,
		continuous.Constant,
		vec_smooth.SmoothConst,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀b:B.",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "smooth_manifold⟨m⟩(S, ℬ)", "b ∈ ⋃S"},
		Conclusion: "smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, λx:A. b)",
	},
		"The constant carrier map is continuous. For a target chart containing b its coordinate "+
			"expression is the constant coordinate vector of b on the source chart image; for other "+
			"target charts the tested domain is empty. SmoothConst handles every coordinate."),
})}

var SmoothMapCongruence = smoothMapCongruenceThm{family.Add(registry.ProofEntry{
	Name: "SmoothMapCongruence",
	Key:  "prop_9070af64bc20570f",
	Deps: []registry.EntryLike{
		SmoothMapDef,
		continuous.Eq,
		functions.InverseOnIn,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f g:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"∀x:A. x ∈ ⋃T ⇒ f(x) = g(x)",
		},
		Conclusion: "smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, g)",
	},
		"Carrier agreement preserves continuity and every chart preimage domain. On that open "+
			"domain the chosen chart inverse lies in the carrier, so the coordinate expressions "+
			"agree; smoothness is preserved by open-domain congruence in every coordinate."),
})}

var SmoothMapRestrict = smoothMapRestrictThm{family.Add(registry.ProofEntry{
	Name: "SmoothMapRestrict",
	Key:  "prop_19e80147b40ffe8f",
	Deps: []registry.EntryLike{
		SmoothMapCompatibleCharts,
		OpenSubmanifold,
		OpenCompatibleChart,
		continuous.FromSubtopology,
		continuous.IntoSubtopology,
		vec_smooth.SmoothSubset,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀U:set(A). " +
			"∀V:set(B).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"U ∈ T",
			"V ∈ S",
			"image(f, U) ⊆ V",
		},
		Conclusion: "smooth_manifold_map⟨n, m⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    subtopology(S, V), " +
			"    open_submanifold_atlas⟨m⟩(S, ℬ, V), " +
			"    f)",
	},
		"The restricted carrier map is continuous into the target subspace. "+
			"OpenCompatibleChart identifies both restricted chart families with "+
			"compatible original charts, so SmoothMapCompatibleCharts supplies "+
			"the same coordinate expressions on their restricted open domains."),
})}

var SmoothMapLocal = smoothMapLocalThm{family.Add(registry.ProofEntry{
	Name: "SmoothMapLocal",
	Key:  "prop_993fc5d37a08f50f",
	Deps: []registry.EntryLike{
		SmoothMapCompatibleCharts,
		OpenCompatibleChart,
		ChartRestrict,
		continuous.OpenPasting,
		vec_smooth.SmoothLocal,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"∀x:A. " +
				"    x ∈ ⋃T ⇒ " +
				"    ∃U:set(A). " +
				"        U ∈ T ∧ " +
				"        x ∈ U ∧ " +
				"        smooth_manifold_map⟨n, m⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), S, ℬ, f)",
		},
		Conclusion: "smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
	},
		"The open neighbourhoods in the hypothesis cover the carrier, so OpenPasting gives "+
			"global continuity. Restrict each original source chart to these neighbourhoods; the "+
			"local smooth-map hypotheses give smooth coordinate expressions on the corresponding "+
			"open pieces. SmoothLocal in each target coordinate yields the global chart test."),
})}

var SmoothOpenInclusion = smoothOpenInclusionThm{family.Add(registry.ProofEntry{
	Name: "SmoothOpenInclusion",
	Key:  "prop_90ced164a84dc851",
	Deps: []registry.EntryLike{
		OpenSubmanifold,
		OpenCompatibleChart,
		CompatibleTransition,
		continuous.FromSubtopology,
		continuous.Identity,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U:set(A).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T"},
		Conclusion: "smooth_manifold_map⟨n, n⟩(subtopology(T, U), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"    T, " +
			"    𝒜, " +
			"    identity_map)",
	},
		"Subspace inclusion is continuous. Its coordinate expressions "+
			"are transitions from the compatible charts lying in U to the "+
			"original atlas charts, which are smooth by CompatibleTransition."),
})}

var SmoothMapEuclidean = smoothMapEuclideanThm{family.Add(registry.ProofEntry{
	Name: "SmoothMapEuclidean",
	Key:  "prop_ccdb22f19a6355d9",
	Reading: "The explicit image condition is retained even when the target dimension is " +
		"zero. Arbitrary function values outside U do not affect either side because U is open.",
	Deps: []registry.EntryLike{
		EuclideanManifold,
		SmoothMapDef,
		euclidean_topology.ContinuousIffCoordinates,
		continuous.IntoSubtopology,
		functions.InverseOnLeft,
		vec_smooth.ContinuouslyDifferentiableCongruence,
	},
	Build: family.Card(Statement{
		Binders:    "∀n m:num. ∀U V:set(num → real). ∀f:((num → real) → num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)", "V ∈ euclidean_topology(m)"},
		Conclusion: "smooth_manifold_map⟨n, m⟩(subtopology(euclidean_topology(n), U), " +
			"    euclidean_atlas(U), " +
			"    subtopology(euclidean_topology(m), V), " +
			"    euclidean_atlas(V), " +
			"    f) ⇔ " +
			"vec_smooth_map_on⟨n, m⟩(U, f) ∧ image(f, U) ⊆ V",
	},
		"With the two identity charts the coordinate expression agrees with f on U. Smooth coordinate "+
			"functions give continuity into Euclidean space, and the image condition gives continuity "+
			"into V; conversely the manifold map supplies the image condition and the sole chart test on "+
			"all of U. In target dimension zero continuity follows from the singleton target carrier."),
})}
