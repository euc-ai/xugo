// Coordinate compatibility gives a positive tangent pairing and metrics induced by immersions.

package riemannian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var PairingChart = pairingChartThm{family.Add(registry.ProofEntry{
	Name: "PairingChart",
	Key:  "prop_8c4e29deebc30341",
	Deps: []registry.EntryLike{
		PairingDef,
		MetricDef,
		tangent.TangentVectorDef,
		smooth_manifold.AtlasSubcover,
	},
	Reading: "The chart must contain x and both vectors must be tangent " +
		"at x. These guards remove the choice and the totalization branch; " +
		"arbitrary component functions do not satisfy this coordinate formula.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀x:A. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀v w:(prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{
			"riemannian_metric⟨n⟩(T, 𝒜, g)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
			"tangent_vector_on⟨n⟩(T, 𝒜, x, v)",
			"tangent_vector_on⟨n⟩(T, 𝒜, x, w)",
		},
		Conclusion: "riemannian_pairing⟨n⟩(T, 𝒜, g, x, v, w) = " +
			"⟪v(c), matrix_act⟨n⟩(g(c, snd(c)(x)), w(c))⟫_n",
	},
		"Choose the chart used in PairingDef and compare it with c on their overlap. "+
			"The metric transforms by Jacobian congruence and both tangent components "+
			"transform by the same Jacobian, so the scalar contractions agree."),
})}

var PairingBilinearSymmetric = pairingBilinearSymmetricThm{family.Add(registry.ProofEntry{
	Name: "PairingBilinearSymmetric",
	Key:  "prop_ca49ea5df096ac26",
	Reading: "No membership of x in the manifold is asked: off the carrier the " +
		"tangent module at x has an empty carrier, and both claims are vacuous there.",
	Deps: []registry.EntryLike{
		PairingChart,
		MetricDef,
		tangent.TangentModule,
		tangent.TangentChartIsomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀x:A.",
		Hypotheses: []string{"riemannian_metric⟨n⟩(T, 𝒜, g)"},
		Conclusion: "bilinear_map(real_ring, " +
			"    tangent_module⟨n⟩(T, 𝒜, x), " +
			"    tangent_module⟨n⟩(T, 𝒜, x), " +
			"    regular_module(real_ring), " +
			"    riemannian_pairing⟨n⟩(T, 𝒜, g, x)) ∧ " +
			"(∀v w:(prod(set(A), A → num → real) → num → real). " +
			"    tangent_vector_on⟨n⟩(T, 𝒜, x, v) ∧ tangent_vector_on⟨n⟩(T, 𝒜, x, w) ⇒ " +
			"    riemannian_pairing⟨n⟩(T, 𝒜, g, x, v, w) = riemannian_pairing⟨n⟩(T, 𝒜, g, x, w, v))",
	},
		"Evaluate all tangent vectors in one active chart. Matrix contraction is bilinear with the fiber "+
			"pointwise operations, and symmetry of the coordinate metric interchanges the two arguments."),
})}

var PairingPositive = pairingPositiveThm{family.Add(registry.ProofEntry{
	Name: "PairingPositive",
	Key:  "prop_3a9d18407257f687",
	Deps: []registry.EntryLike{PairingChart, MetricDef, tangent.TangentChartReconstruct},
	Reading: "At dimension zero the fiber contains only its zero vector. A " +
		"base point outside the manifold carrier cannot satisfy the tangent premise.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{"riemannian_metric⟨n⟩(T, 𝒜, g)", "tangent_vector_on⟨n⟩(T, 𝒜, x, v)"},
		Conclusion: "&0 ≤ riemannian_pairing⟨n⟩(T, 𝒜, g, x, v, v) ∧ " +
			"(riemannian_pairing⟨n⟩(T, 𝒜, g, x, v, v) = &0 ⇔ v = «zero tangent»)",
	},
		"In any active chart the quadratic form is strictly positive on a nonzero "+
			"coordinate vector. Reconstruction makes that coordinate vector zero exactly "+
			"when the whole tangent family is zero; the zero vector has pairing zero."),
})}

var MetricConvexCombination = metricConvexCombinationThm{family.Add(registry.ProofEntry{
	Name: "MetricConvexCombination",
	Key:  "prop_60617da1353d6229",
	Deps: []registry.EntryLike{
		MetricDef,
		vec_smooth.SmoothConst,
		vec_smooth.SmoothAdd,
		vec_smooth.SmoothMul,
	},
	Reading: "The interpolation parameter in this statement is a fixed real number. " +
		"Positivity of the two endpoint metrics is needed even when the manifold is not compact.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀h:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀t:real.",
		Hypotheses: []string{
			"riemannian_metric⟨n⟩(T, 𝒜, g)",
			"riemannian_metric⟨n⟩(T, 𝒜, h)",
			"&0 ≤ t",
			"t ≤ &1",
		},
		Conclusion: "riemannian_metric⟨n⟩(T, " +
			"    𝒜, " +
			"    (λc:prod(set(A), A → num → real). λy:(num → real). λi:num. λj:num. " +
			"        (&1 - t) * g(c, y, i, j) + t * h(c, y, i, j)))",
	},
		"Normalization, smoothness, symmetry and the Jacobian compatibility law are preserved "+
			"by the weighted sum. On a nonzero vector both quadratic values are positive and the "+
			"nonnegative coefficients sum to one, including the endpoint parameters."),
})}

var ImmersionMetric = immersionMetricThm{family.Add(registry.ProofEntry{
	Name: "ImmersionMetric",
	Key:  "prop_8fc7852ae0fda81a",
	Deps: []registry.EntryLike{
		InducedMetricDef,
		MetricDef,
		smooth_manifold.ImmersionDef,
		smooth_manifold.SmoothMapEuclidean,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothSum,
		vec_smooth.SmoothMul,
		vec_smooth.JacobianChain,
	},
	Reading: "An injective map alone is insufficient; injectivity of its differential is the " +
		"positive-definiteness hypothesis. Source dimension zero and empty manifolds are included.",
	Build: family.Card(Statement{
		Binders: "∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    f)",
		},
		Conclusion: "riemannian_metric⟨n⟩(T, 𝒜, riemannian_induced_metric⟨n, N⟩(T, 𝒜, f))",
	},
		"Smooth coordinate partials make the Gram entries smooth, and the chain rule gives "+
			"covariant compatibility. The quadratic value is the squared Euclidean norm of the "+
			"coordinate differential applied to v, which is positive for nonzero v by immersion."),
})}

var CompactMetricExists = compactMetricExistsThm{family.Add(registry.ProofEntry{
	Name: "CompactMetricExists",
	Key:  "prop_b464ac35fb85f484",
	Deps: []registry.EntryLike{
		ImmersionMetric,
		manifold_embedding.CompactSmoothEmbedding,
		smooth_manifold.EmbeddingDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
		Conclusion: "∃g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"    riemannian_metric⟨n⟩(T, 𝒜, g)",
	},
		"Take a Euclidean embedding of the compact manifold and its immersion "+
			"metric. Only this existence argument uses the embedding; all subsequent "+
			"frame and connection laws apply to an arbitrary supplied metric."),
})}
