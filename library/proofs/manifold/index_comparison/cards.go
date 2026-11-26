package index_comparison

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/bott_operator"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/manifold/analytic_index"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_cotangent"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	"github.com/euc-ai/xugo/library/proofs/manifold/riemannian"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/sobolev_section"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/manifold/topological_index"
	"github.com/euc-ai/xugo/library/proofs/manifold/torus_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/registry"
)

var OpenTangentTransport = openTangentTransportThm{family.Add(registry.ProofEntry{
	Name: "OpenTangentTransport",
	Key:  "prop_3d384b1a2c9ca079",
	Deps: []registry.EntryLike{
		k_compact_support.OpenExtensionHomomorphism,
		k_compact_support.ProperPullback,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{"smooth_manifold_embedding⟨n, n⟩(T, 𝒜, S, ℬ, f)", "image(f, ⋃T) ∈ S"},
		Conclusion: "image(tangent_map⟨n, n⟩(T, 𝒜, S, ℬ, f), tangent_bundle⟨n⟩(T, 𝒜)) ∈ " +
			"tangent_topology⟨n⟩(S, ℬ) ∧ " +
			"homeomorphic_map(tangent_topology⟨n⟩(T, 𝒜), " +
			"    subtopology(tangent_topology⟨n⟩(S, ℬ), " +
			"        image(tangent_map⟨n, n⟩(T, 𝒜, S, ℬ, f), tangent_bundle⟨n⟩(T, 𝒜))), " +
			"    tangent_map⟨n, n⟩(T, 𝒜, S, ℬ, f)) ∧ " +
			"group_homomorphism(kc_group(tangent_topology⟨n⟩(T, 𝒜)), " +
			"    kc_group(tangent_topology⟨n⟩(S, ℬ)), " +
			"    tangent_open_push(n, T, 𝒜, S, ℬ, f))",
	},
		"An equal-dimensional smooth open embedding is a local diffeomorphism; its "+
			"differential is a bundle isomorphism onto the open tangent image. "+
			"Transport through its proper inverse and open extension give the group map."),
})}

var EuclideanTangentCoordinates = euclideanTangentCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "EuclideanTangentCoordinates",
	Key:  "prop_8f671eaf0f2b099f",
	Deps: []registry.EntryLike{
		smooth_manifold.EuclideanManifold,
		smooth_manifold.AtlasMemberCompatible,
		tangent.TangentManifold,
		tangent.TangentChartImage,
		tangent.TangentChartInverse,
		tangent.TangentChartReconstruct,
		tangent.TangentFromChart,
		product_topology.IndexedProductCarrier,
		complex_topology.CoordinateRealHomeomorphism,
		continuous.HomeomorphismCompose,
		continuous.HomeomorphismInverse,
		continuous.ImageCompact,
	},
	Build: family.Card(
		"∀n:num. "+
			"    homeomorphic_map(tangent_topology⟨n⟩(euclidean_topology(n), "+
			"            euclidean_atlas({x:(num → real) | vec⟨n⟩(&0, x)})), "+
			"        complex_coordinate_topology(n), "+
			"        euclidean_tangent_coordinates(n)) ∧ "+
			"    kc_proper_map(tangent_topology⟨n⟩(euclidean_topology(n), "+
			"            euclidean_atlas({x:(num → real) | vec⟨n⟩(&0, x)})), "+
			"        complex_coordinate_topology(n), "+
			"        euclidean_tangent_coordinates(n))",
		"The identity chart is compatible (EuclideanManifold, AtlasMemberCompatible) and defined "+
			"everywhere, so its tangent chart is a homeomorphism of the whole tangent bundle onto "+
			"ℝ²ⁿ (TangentManifold, TangentChartImage, TangentChartInverse), a tangent vector being "+
			"its identity-chart component (TangentChartReconstruct, TangentFromChart). The hard step "+
			"is ℝ²ⁿ ≅ ℂⁿ, complex_topology.CoordinateRealHomeomorphism; the map is the composite "+
			"(HomeomorphismCompose). Properness is a corollary: the preimage of a compact set is its "+
			"image under the continuous inverse (HomeomorphismInverse, ImageCompact)."),
})}

var TangentIndexMetricIndependent = tangentIndexMetricIndependentThm{family.Add(registry.ProofEntry{
	Name: "TangentIndexMetricIndependent",
	Key:  "prop_3290de445b6a3864",
	Deps: []registry.EntryLike{
		manifold_cotangent.MetricIdentification,
		analytic_index.IndexClassIndependent,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
			"riemannian_metric⟨n⟩(T, 𝒜, g)",
			"a ∈ (kc_group(tangent_topology⟨n⟩(T, 𝒜))).carrier",
		},
		Conclusion: "tangent_analytic_index(n, T, 𝒜, a) = " +
			"analytic_index(n, " +
			"    T, " +
			"    𝒜, " +
			"    kc_pullback(cotangent_topology(n, T, 𝒜), " +
			"        inverse_on(tangent_bundle⟨n⟩(T, 𝒜), cotangent_metric_flat(n, T, 𝒜, g)), " +
			"        a))",
	},
		"Convex interpolation between positive metrics gives inverse bundle maps with "+
			"uniform bounds over the compact base and parameter interval. Their pullbacks of "+
			"a fixed compact support form one compact homotopy, so the symbol classes agree."),
})}

var AmbientIndexHomomorphism = ambientIndexHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "AmbientIndexHomomorphism",
	Key:  "prop_da255e2d17cf5c78",
	Deps: []registry.EntryLike{
		OpenTangentTransport,
		EuclideanTangentCoordinates,
		TangentIndexMetricIndependent,
		analytic_index.AnalyticIndexHomomorphism,
		torus_manifold.ClosedTorus,
		torus_manifold.EuclideanOpenEmbedding,
		riemannian.CompactMetricExists,
	},
	Build: family.Card(
		"∀n:num. "+
			"    group_homomorphism(kc_group(complex_coordinate_topology(n)), "+
			"        additive_group(int_ring), "+
			"        euclidean_analytic_index(n))",
		"Transport to the open tangent chart of the closed "+
			"torus and use additivity of the analytic index."),
})}

var BottEmbeddingIndex = bottEmbeddingIndexThm{family.Add(registry.ProofEntry{
	Name: "BottEmbeddingIndex",
	Key:  "prop_364f6cdc4335df7e",
	Deps: []registry.EntryLike{
		TangentIndexMetricIndependent,
		analytic_index.SymbolClassRealization,
		analytic_index.AnalyticIndexOnOperators,
		analytic_index.OrderReduction,
		bott_operator.BottFredholmIndex,
		bott_operator.HermiteCorrespondence,
		bott_operator.HermiteIntertwining,
		bott_operator.GaussianPoincare,
		bott_operator.OrthogonalDomain,
		bott_operator.OrthogonalOperatorCommutes,
		bott_operator.GroundFrameIndependent,
		riemannian.CompactMetricExists,
		sobolev_section.LocalizationExists,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀h:(prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex) → num → complex). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({x:(num → real) | vec⟨N⟩(&0, x)}), " +
				"    f)",
			"index_tangent_tube(n, N, T, 𝒜, f, h)",
			"a ∈ (kc_group(tangent_topology⟨n⟩(T, 𝒜))).carrier",
		},
		Conclusion: "euclidean_analytic_index(N, " +
			"    kc_tubular_pushforward(tangent_topology⟨n⟩(T, 𝒜), " +
			"        complex_coordinate_topology(N), " +
			"        index_tangent_normal(n, N, T, 𝒜, f), " +
			"        h, " +
			"        a)) = " +
			"tangent_analytic_index(n, T, 𝒜, a)",
	},
		"Use orthogonal normal frames to descend the full Bott graph-domain operator, whose "+
			"Gaussian kernel line is fixed. Lift the base operator with the induced normal "+
			"connection and form the graded product. Unify orders before clutching along the "+
			"annulus, where the position term is invertible, and extend by identity on the torus. "+
			"The Gaussian spectral gap controls the curvature and cutoff errors for large scaling; "+
			"the resulting index is the base index. Its symbol is the Koszul Thom pushforward with "+
			"the chosen z convention; analytic excision identifies the tubular realization."),
})}

var PointAnalyticIndex = pointAnalyticIndexThm{family.Add(registry.ProofEntry{
	Name: "PointAnalyticIndex",
	Key:  "prop_2bcaff0416365631",
	Deps: []registry.EntryLike{
		TangentIndexMetricIndependent,
		analytic_index.AnalyticIndexOnOperators,
		manifold_embedding.PointEmbedding,
		riemannian.CompactMetricExists,
		sobolev_section.LocalizationExists,
	},
	Build: family.Card(
		"tangent_analytic_index(0, "+
			"    euclidean_topology(0), "+
			"    euclidean_atlas({x:(num → real) | vec⟨0⟩(&0, x)}), "+
			"    kc_class(tangent_topology⟨0⟩(euclidean_topology(0), "+
			"            euclidean_atlas({x:(num → real) | vec⟨0⟩(&0, x)})), "+
			"        (projection_trivial(tangent_topology⟨0⟩(euclidean_topology(0), "+
			"                    euclidean_atlas({x:(num → real) | vec⟨0⟩(&0, x)})), "+
			"                1), "+
			"            projection_trivial(tangent_topology⟨0⟩(euclidean_topology(0), "+
			"                    euclidean_atlas({x:(num → real) | vec⟨0⟩(&0, x)})), "+
			"                0), "+
			"            λp:prod((num → real), "+
			"                    prod(set(num → real), (num → real) → num → real) → num → real). "+
			"            λi:num. "+
			"            λj:num. "+
			"                complex_of_real(&0)))) = "+
			"int_of_num(1)",
		"A point has one-dimensional sections of the trivial line and an empty punctured "+
			"cotangent space, so every symbol is elliptic. The zero operator from the trivial line to "+
			"the zero bundle realizes this class, whatever the metric, and its Fredholm index is one."),
})}

var AmbientBottNormalization = ambientBottNormalizationThm{family.Add(registry.ProofEntry{
	Name: "AmbientBottNormalization",
	Key:  "prop_226d0967778a24cf",
	Deps: []registry.EntryLike{
		BottEmbeddingIndex,
		PointAnalyticIndex,
		manifold_embedding.PointEmbedding,
		topological_index.TangentTubeExists,
		topological_index.PointPushforward,
	},
	Build: family.Card(
		"∀n:num. "+
			"    euclidean_analytic_index(n, "+
			"        kc_class(complex_coordinate_topology(n), index_bott_triple(n))) = "+
			"    int_of_num(1)",
		"Embed a point at the origin and choose a tube. The Bott embedding index equates "+
			"the ambient index of the pushed unit class with the index of the unit class on "+
			"the point, which is one, and the pushed unit class is the Bott generator."),
})}

var AtiyahSingerIndex = atiyahSingerIndexThm{family.Add(registry.ProofEntry{
	Name: "AtiyahSingerIndex",
	Key:  "prop_3f25b61762f241c3",
	Deps: []registry.EntryLike{
		BottEmbeddingIndex,
		AmbientBottNormalization,
		AmbientIndexHomomorphism,
		TangentIndexMetricIndependent,
		topological_index.TopologicalIndexOnEmbedding,
		topological_index.EmbeddingIndexDefined,
		topological_index.TangentTubeExists,
		manifold_embedding.CompactSmoothEmbedding,
		riemannian.CompactMetricExists,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
			"a ∈ (kc_group(cotangent_topology(n, T, 𝒜))).carrier",
		},
		Conclusion: "analytic_index(n, T, 𝒜, a) = topological_index(n, T, 𝒜, a)",
	},
		"Choose a Euclidean embedding and a metric. Embedding compatibility identifies the analytic "+
			"index with the ambient index of its Thom pushforward. That class is the Bott multiple of "+
			"the topological index; additivity and point normalization evaluate it to the same integer."),
})}
