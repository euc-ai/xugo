package topological_index

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/manifold/embedding_normal"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_diagonal"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/proofs/topology/k_pushforward"
	"github.com/euc-ai/xugo/library/proofs/topology/k_theory"
	"github.com/euc-ai/xugo/library/proofs/topology/k_thom"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var NormalProjectionSmooth = normalProjectionSmoothThm{family.Add(registry.ProofEntry{
	Name: "NormalProjectionSmooth",
	Key:  "prop_a9a15c1e89b62d87",
	Deps: []registry.EntryLike{
		embedding_normal.NormalProjectionChart,
		embedding_normal.NormalProjectionSpec,
		smooth_manifold.SmoothMapCompatibleCharts,
		vec_smooth.SmoothPartial,
		tangent.EuclideanDifferentialInjective,
		determinant.DeterminantZeroIffDependent,
		vec_smooth.SmoothMatrixInverse,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothSum,
		vec_smooth.SmoothSub,
		smooth_manifold.FunctionConstant,
		smooth_manifold.FunctionContinuous,
		complex_topology.ContinuousIffParts,
		smooth_projection_bundle.SmoothBundleContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold_immersion⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:(num → real) | vec⟨N⟩(&0, y)}), " +
				"    f)",
		},
		Conclusion: "smooth_projection_bundle(n, N, T, 𝒜, snd(embedding_normal_bundle(n, N, T, 𝒜, f))) ∧ " +
			"continuous_projection_bundle(T, embedding_normal_bundle(n, N, T, 𝒜, f))",
	},
		"In each compatible chart the normal projection is I − J(JᵀJ)⁻¹Jᵀ, J the chart Jacobian of f "+
			"(embedding_normal.NormalProjectionChart), and NormalProjectionSpec gives its symmetry, "+
			"idempotence and padding. J's entries are smooth (SmoothMapCompatibleCharts, SmoothPartial) "+
			"and JᵀJ is invertible by immersion (EuclideanDifferentialInjective, "+
			"DeterminantZeroIffDependent), so SmoothMatrixInverse with SmoothMul, SmoothSum and "+
			"SmoothSub makes the real parts smooth; the imaginary parts are zero (FunctionConstant), and "+
			"the smooth bundle is a continuous one (smooth_projection_bundle.SmoothBundleContinuous)."),
	Reading: "An immersion is enough: smoothness needs only that df has " +
		"constant rank n, and that f be a homeomorphism onto its image is never used.",
})}

var TangentEmbeddingProper = tangentEmbeddingProperThm{family.Add(registry.ProofEntry{
	Name: "TangentEmbeddingProper",
	Key:  "prop_673ec8d0f95e2469",
	Deps: []registry.EntryLike{
		tangent.TangentManifold,
		tangent.TangentProjection,
		tangent.EuclideanDifferentialBundleSmooth,
		product_topology.IndexedContinuousIff,
		product_topology.IndexedProjectionContinuous,
		product_topology.IndexedHausdorff,
		complex_topology.ContinuousIffParts,
		complex_topology.ComplexHausdorff,
		complex_topology.ComplexCompactIff,
		complex_topology.CoordinateLocallyCompact,
		manifold_diagonal.CompactEmbeddedTangentDisk,
		compact.CompactClosed,
		compact.ClosedSubsetCompact,
		continuous.ImageCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
			"smooth_manifold_immersion⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:(num → real) | vec⟨N⟩(&0, y)}), " +
				"    f)",
		},
		Conclusion: "kc_proper_map(tangent_topology⟨n⟩(T, 𝒜), " +
			"    complex_coordinate_topology(N), " +
			"    index_tangent_embedding(n, N, T, 𝒜, f)) ∧ " +
			"closed_in(complex_coordinate_topology(N), " +
			"    image(index_tangent_embedding(n, N, T, 𝒜, f), tangent_bundle⟨n⟩(T, 𝒜)))",
	},
		"The map is continuous coordinatewise (IndexedContinuousIff, ContinuousIffParts), its "+
			"parts being f after the projection (TangentProjection) and the coordinates of df "+
			"(EuclideanDifferentialBundleSmooth). A compact K of complex N-space is closed "+
			"(IndexedHausdorff, CompactClosed) with bounded coordinates (IndexedProjectionContinuous, "+
			"ImageCompact, ComplexCompactIff), so its preimage is a closed subset of a disk {‖df‖ ≤ "+
			"δ}, compact by manifold_diagonal.CompactEmbeddedTangentDisk. A point of the image's "+
			"closure has a compact neighbourhood K (CoordinateLocallyCompact) meeting the image in "+
			"the compact, hence closed, image of the preimage of K."),
	Reading: "Compactness of the base is load-bearing: for the inclusion of (0, 1) in ℝ the " +
		"preimage of [0, 1] + i[−1, 1] is (0, 1) × [−1, 1], not compact. Injectivity of f is never " +
		"used; the closed image follows from properness into the locally compact Hausdorff ℂᴺ.",
})}

var TangentNormalComplexOrientation = tangentNormalComplexOrientationThm{family.Add(registry.ProofEntry{
	Name: "TangentNormalComplexOrientation",
	Key:  "prop_1af65c3efd67da2d",
	Deps: []registry.EntryLike{
		NormalProjectionSmooth,
		embedding_normal.NormalProjectionChart,
		embedding_normal.NormalProjectionSpec,
		module_dimension.IdempotentTraceIsRank,
		module_dimension.AnnihilatorDimension,
		module_dimension.TraceFromBasis,
		tangent.EuclideanDifferentialLinear,
		tangent.EuclideanDifferentialInjective,
		tangent.TangentChartIsomorphism,
		module_dimension.IsomorphismDim,
		module_dimension.FreeModuleDim,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:(num → real) | vec⟨N⟩(&0, y)}), " +
				"    f)",
		},
		Conclusion: "continuous_projection_bundle(tangent_topology⟨n⟩(T, 𝒜), " +
			"    index_tangent_normal(n, N, T, 𝒜, f)) ∧ " +
			"(∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"    p ∈ tangent_bundle⟨n⟩(T, 𝒜) ⇒ " +
			"    projection_rank(index_tangent_normal(n, N, T, 𝒜, f), p) + n = N)",
	},
		"Differentiate the real tubular map. Its normal quotient is the pullback of ν⊕ν; pairing "+
			"its two real summands gives the stated complexification, with rank N−n: its trace at "+
			"the point, that of the real projection ν read in the coordinate basis of ℝ^N "+
			"(TraceFromBasis), is the dimension of its image (IdempotentTraceIsRank), the orthogonal "+
			"complement of the tangent image (NormalProjectionSpec), of dimension N less that of the "+
			"image (AnnihilatorDimension). The tangent image has dimension n: the differential is "+
			"linear and injective (EuclideanDifferentialLinear, EuclideanDifferentialInjective) on "+
			"the tangent module, isomorphic to ℝⁿ (TangentChartIsomorphism, IsomorphismDim, "+
			"FreeModuleDim); so the trace is N − n, and the choice in projection_rank picks it."),
})}

var TangentTubeExists = tangentTubeExistsThm{family.Add(registry.ProofEntry{
	Name: "TangentTubeExists",
	Key:  "prop_c9924a16383377b8",
	Deps: []registry.EntryLike{
		NormalProjectionSmooth,
		TangentEmbeddingProper,
		TangentNormalComplexOrientation,
		embedding_normal.NormalProjectionSpec,
		embedding_normal.NormalProjectionChart,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:(num → real) | vec⟨N⟩(&0, y)}), " +
				"    f)",
		},
		Conclusion: "∃h:(prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex) → " +
			"        num → " +
			"        complex). " +
			"    index_tangent_tube(n, N, T, 𝒜, f, h)",
	},
		"The tangent of the real normal tubular map has the displayed germ, including "+
			"dPν(v)u. A uniform tubular radius exists over the compact base; compress the "+
			"complex normal fibre into that disk while keeping a smaller disk fixed."),
})}

var EuclideanBottNormalization = euclideanBottNormalizationThm{family.Add(registry.ProofEntry{
	Name: "EuclideanBottNormalization",
	Key:  "prop_5edd25a5727bdc18",
	Deps: []registry.EntryLike{
		k_thom.CompactThomIsomorphism,
		k_theory.PointNormalization,
		projection_bundle.TrivialBundle,
		product_topology.IndexedProductCarrier,
		compact.FiniteCompact,
		compact.CompactImpLocallyCompact,
		k_compact_support.HomeomorphismPullbackIsomorphism,
		k_compact_support.CompactComparison,
		k_compact_support.CompactToKDescends,
		k_compact_support.PullbackDescends,
		k_thom.ThomMapDescends,
		k_thom.TrivialExterior,
		k_compact_support.AbelianGroup,
		group_homomorphism.MapPow,
		group_homomorphism.MapInv,
	},
	Build: family.Card(
		"∀N:num. "+
			"    group_isomorphism(additive_group(int_ring), "+
			"        kc_group(complex_coordinate_topology(N)), "+
			"        index_bott_multiple(N))",
		"The Thom isomorphism over a point. complex_coordinate_topology(0) is one point "+
			"(IndexedProductCarrier, FiniteCompact, CompactImpLocallyCompact), compact and Hausdorff, "+
			"so kc_group(pt) ≅ K(pt) (k_compact_support.CompactComparison) ≅ ℤ by rank "+
			"(k_theory.PointNormalization), and over pt the trivial rank-N bundle gives kc_group(pt) ≅ "+
			"kc_group(E) (k_thom.CompactThomIsomorphism). Each of these maps is read on a class through "+
			"a triple of it (CompactToKDescends, ThomMapDescends, PullbackDescends): 1 is the class of "+
			"u = (trivial line, rank-0 bundle, 0), and its Thom product is the Koszul triple exactly. z "+
			"↦ (pt, z) is a homeomorphism of complex N-space onto E, whose pullback is an isomorphism "+
			"(HomeomorphismPullbackIsomorphism) carrying the Koszul triple to index_bott_triple(N) term "+
			"for term (TrivialExterior); the composite sends 1 to the Bott class, so it is k ↦ k·β "+
			"(group_homomorphism.MapPow, MapInv for negative k), N = 0 included."),
})}

var EmbeddingIndexDefined = embeddingIndexDefinedThm{family.Add(registry.ProofEntry{
	Name: "EmbeddingIndexDefined",
	Key:  "prop_4a22d5516f446369",
	Deps: []registry.EntryLike{
		EuclideanBottNormalization,
		k_pushforward.PushforwardHomomorphism,
		complex_topology.CoordinateLocallyCompact,
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
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:(num → real) | vec⟨N⟩(&0, y)}), " +
				"    f)",
			"index_tangent_tube(n, N, T, 𝒜, f, h)",
			"a ∈ (kc_group(tangent_topology⟨n⟩(T, 𝒜))).carrier",
		},
		Conclusion: "index_bott_multiple(N, embedding_topological_index(n, N, T, 𝒜, f, h, a)) = " +
			"kc_tubular_pushforward(tangent_topology⟨n⟩(T, 𝒜), " +
			"    complex_coordinate_topology(N), " +
			"    index_tangent_normal(n, N, T, 𝒜, f), " +
			"    h, " +
			"    a)",
	},
		"The pushforward lies in the Euclidean compact-support group "+
			"(k_pushforward.PushforwardHomomorphism, complex N-space being locally compact by "+
			"CoordinateLocallyCompact), and the Bott multiple map is bijective (EuclideanBottNormalization)."),
})}

var PointPushforward = pointPushforwardThm{family.Add(registry.ProofEntry{
	Name: "PointPushforward",
	Key:  "prop_733708a1fec788be",
	Deps: []registry.EntryLike{
		EmbeddingIndexDefined,
		embedding_normal.NormalProjectionChart,
		k_thom.TrivialExterior,
		k_pushforward.TubeRestrictionIndependent,
		k_compact_support.Excision,
		complex_topology.CoordinateLocallyCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀N:num. " +
			"∀h:(prod(prod((num → real), prod(set(num → real), (num → real) → num → real) → num → real), " +
			"            num → complex) → " +
			"        num → " +
			"        complex).",
		Hypotheses: []string{
			"index_tangent_tube(0, " +
				"    N, " +
				"    euclidean_topology(0), " +
				"    euclidean_atlas({y:(num → real) | vec⟨0⟩(&0, y)}), " +
				"    λy:(num → real). λi:num. &0, " +
				"    h)",
		},
		Conclusion: "kc_tubular_pushforward(tangent_topology⟨0⟩(euclidean_topology(0), " +
			"        euclidean_atlas({y:(num → real) | vec⟨0⟩(&0, y)})), " +
			"    complex_coordinate_topology(N), " +
			"    index_tangent_normal(0, " +
			"        N, " +
			"        euclidean_topology(0), " +
			"        euclidean_atlas({y:(num → real) | vec⟨0⟩(&0, y)}), " +
			"        λy:(num → real). λi:num. &0), " +
			"    h, " +
			"    kc_class(tangent_topology⟨0⟩(euclidean_topology(0), " +
			"            euclidean_atlas({y:(num → real) | vec⟨0⟩(&0, y)})), " +
			"        (projection_trivial(tangent_topology⟨0⟩(euclidean_topology(0), " +
			"                    euclidean_atlas({y:(num → real) | vec⟨0⟩(&0, y)})), " +
			"                1), " +
			"            projection_trivial(tangent_topology⟨0⟩(euclidean_topology(0), " +
			"                    euclidean_atlas({y:(num → real) | vec⟨0⟩(&0, y)})), " +
			"                0), " +
			"            λp:prod((num → real), " +
			"                    prod(set(num → real), (num → real) → num → real) → num → real). " +
			"            λi:num. " +
			"            λj:num. " +
			"                complex_of_real(&0)))) = " +
			"kc_class(complex_coordinate_topology(N), index_bott_triple(N))",
	},
		"The normal projection of the origin is the identity (embedding_normal.NormalProjectionChart "+
			"at n = 0), so the Koszul triple over the point is the Bott triple (TrivialExterior), and "+
			"the trivial line is the unit of the product. Near the zero section the tube is the germ, "+
			"which at a point is the identity of complex N-space; shrinking the Thom support "+
			"(TubeRestrictionIndependent, complex N-space locally compact by CoordinateLocallyCompact) "+
			"and excision identify the open extension with the Bott class."),
})}

var TubularChoiceIndependent = tubularChoiceIndependentThm{family.Add(registry.ProofEntry{
	Name: "TubularChoiceIndependent",
	Key:  "prop_49931fa2c154bcb2",
	Deps: []registry.EntryLike{
		EmbeddingIndexDefined,
		k_pushforward.TubeRestrictionIndependent,
		complex_topology.CoordinateLocallyCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀h k:(prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex) → num → complex). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:(num → real) | vec⟨N⟩(&0, y)}), " +
				"    f)",
			"index_tangent_tube(n, N, T, 𝒜, f, h)",
			"index_tangent_tube(n, N, T, 𝒜, f, k)",
			"a ∈ (kc_group(tangent_topology⟨n⟩(T, 𝒜))).carrier",
		},
		Conclusion: "embedding_topological_index(n, N, T, 𝒜, f, h, a) = " +
			"embedding_topological_index(n, N, T, 𝒜, f, k, a)",
	},
		"Both tubular maps agree with the same tangent germ near the zero section; "+
			"shrinking the Thom support and excision compare their pushforwards."),
})}

var TopologicalIndexOnEmbedding = topologicalIndexOnEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "TopologicalIndexOnEmbedding",
	Key:  "prop_a366a335a08e17ed",
	Deps: []registry.EntryLike{TubularChoiceIndependent, TangentTubeExists, EuclideanBottNormalization},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
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
				"    euclidean_atlas({y:(num → real) | vec⟨N⟩(&0, y)}), " +
				"    f)",
			"riemannian_metric⟨n⟩(T, 𝒜, g)",
			"index_tangent_tube(n, N, T, 𝒜, f, h)",
			"a ∈ (kc_group(cotangent_topology(n, T, 𝒜))).carrier",
		},
		Conclusion: "topological_index(n, T, 𝒜, a) = " +
			"embedding_topological_index(n, " +
			"    N, " +
			"    T, " +
			"    𝒜, " +
			"    f, " +
			"    h, " +
			"    kc_pullback(tangent_topology⟨n⟩(T, 𝒜), cotangent_metric_flat(n, T, 𝒜, g), a))",
	},
		"Join two embeddings after adding ambient dimensions, use a stabilized embedding "+
			"isotopy, and apply Thom direct-sum and homotopy compatibility. Convex interpolation "+
			"of metrics gives a uniformly proper bundle homotopy on compact supports."),
})}

var TopologicalIndexHomomorphism = topologicalIndexHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "TopologicalIndexHomomorphism",
	Key:  "prop_4f3946bbceb212cf",
	Deps: []registry.EntryLike{
		TopologicalIndexOnEmbedding,
		EuclideanBottNormalization,
		TangentTubeExists,
		k_pushforward.PushforwardHomomorphism,
		k_compact_support.ProperPullback,
		complex_topology.CoordinateLocallyCompact,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
		Conclusion: "group_homomorphism(kc_group(cotangent_topology(n, T, 𝒜)), " +
			"    additive_group(int_ring), " +
			"    topological_index(n, T, 𝒜))",
	},
		"Fix one Euclidean embedding, metric and tube. The defining map is a "+
			"composite of group homomorphisms and the inverse Bott isomorphism."),
})}
