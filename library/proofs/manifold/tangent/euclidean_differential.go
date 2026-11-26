// Euclidean-target differentials are linear on fibers and smooth on the total tangent bundle.

package tangent

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var EuclideanDifferentialCoordinate = euclideanDifferentialCoordinateThm{family.Add(registry.ProofEntry{
	Name: "EuclideanDifferentialCoordinate",
	Key:  "prop_8a95c749d9f6596c",
	Deps: []registry.EntryLike{
		EuclideanDifferentialDef,
		DifferentialCoordinate,
		smooth_manifold.EuclideanManifold,
		smooth_manifold.AtlasMemberCompatible,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real). " +
			"∀c:prod(set(A), A → num → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"tangent_vector_on⟨n⟩(T, 𝒜, x, v)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
		},
		Conclusion: "manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(x, v) = " +
			"matrix_act⟨n⟩(vec_jacobian_matrix⟨n, N⟩(i ∘ inverse_on(fst(c), snd(c)), snd(c)(x)), v(c))",
	},
		"Apply DifferentialCoordinate with the target global identity chart. Its coordinate "+
			"function is identity, so the coordinate map reduces to i after the inverse source chart."),
})}

var EuclideanDifferentialLinear = euclideanDifferentialLinearThm{family.Add(registry.ProofEntry{
	Name: "EuclideanDifferentialLinear",
	Key:  "prop_c18b15db7a77ca20",
	Reading: "The source carrier consists of normalized tangent families and the target " +
		"carrier of normalized N-vectors. Linearity is not asserted on arbitrary chart families.",
	Deps: []registry.EntryLike{
		EuclideanDifferentialDef,
		DifferentialLinear,
		TangentChartIsomorphism,
		module_homomorphism.HomCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀x:A.",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"x ∈ ⋃T",
		},
		Conclusion: "module_homomorphism(real_ring, " +
			"    tangent_module⟨n⟩(T, 𝒜, x), " +
			"    function_module(regular_module(real_ring), {j:num | j < N}), " +
			"    manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(x))",
	},
		"Compose DifferentialLinear with evaluation in the global identity "+
			"chart of Euclidean space. TangentChartIsomorphism identifies this "+
			"evaluation with an isomorphism to the normalized N-vector module."),
})}

var EuclideanDifferentialInjective = euclideanDifferentialInjectiveThm{family.Add(registry.ProofEntry{
	Name: "EuclideanDifferentialInjective",
	Key:  "prop_a76da709e055d147",
	Reading: "The immersion hypothesis is required: a constant map can kill " +
		"every nonzero tangent vector. Zero-dimensional source fibers are singletons.",
	Deps: []registry.EntryLike{
		EuclideanDifferentialDef,
		ImmersionDifferentialIff,
		TangentChartIsomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀x:A.",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"x ∈ ⋃T",
		},
		Conclusion: "injective_on(tangent_module⟨n⟩(T, 𝒜, x).carrier, " +
			"    manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(x))",
	},
		"ImmersionDifferentialIff gives injectivity of the intrinsic differential. Compose "+
			"it with the injective evaluation isomorphism in the global Euclidean chart."),
})}

var EuclideanDifferentialBundleSmooth = euclideanDifferentialBundleSmoothThm{family.Add(registry.ProofEntry{
	Name: "EuclideanDifferentialBundleSmooth",
	Key:  "prop_b236050d2937dc8c",
	Deps: []registry.EntryLike{
		EuclideanDifferentialDef,
		TangentMapSmooth,
		TangentManifold,
		TangentChartImage,
		TangentChartInverse,
		smooth_manifold.SmoothMapCompose,
		smooth_manifold.SmoothMapEuclidean,
		vec_smooth.LinearSmoothMap,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀i:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
		},
		Conclusion: "smooth_manifold_map⟨2 * n, N⟩(tangent_topology⟨n⟩(T, 𝒜), " +
			"    tangent_atlas⟨n⟩(T, 𝒜), " +
			"    euclidean_topology(N), " +
			"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
			"    (λp:prod(A, prod(set(A), A → num → real) → num → real). " +
			"        manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(fst(p), snd(p))))",
	},
		"TangentMapSmooth gives a smooth map to the Euclidean tangent bundle. Its "+
			"global lifted identity chart identifies the fiber evaluation with projection "+
			"onto the second coordinate block, a linear smooth map; compose these maps."),
})}
