package cohomological_index

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/chern_thom"
	"github.com/euc-ai/xugo/library/proofs/manifold/chern_weil"
	"github.com/euc-ai/xugo/library/proofs/manifold/compact_chern"
	"github.com/euc-ai/xugo/library/proofs/manifold/compact_de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	"github.com/euc-ai/xugo/library/proofs/manifold/embedding_normal"
	"github.com/euc-ai/xugo/library/proofs/manifold/index_comparison"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_cotangent"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/manifold/topological_index"
	"github.com/euc-ai/xugo/library/registry"
)

var CotangentOrientation = cotangentOrientationThm{family.Add(registry.ProofEntry{
	Name: "CotangentOrientation",
	Reading: "The block and interleaved atlases have exactly the same compatible " +
		"smooth charts, so their normalized form spaces and compact cohomology carriers " +
		"coincide. The chosen orientations can differ by the displayed permutation sign.",
	Key:  "prop_83d79be98c6048b0",
	Deps: []registry.EntryLike{manifold_cotangent.CotangentManifold},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "oriented_manifold⟨2 * n⟩(cotangent_topology(n, T, 𝒜), cotangent_atlas(n, T, 𝒜)) ∧ " +
			"oriented_manifold⟨2 * n⟩(cotangent_topology(n, T, 𝒜), cotangent_symplectic_atlas(n, T, 𝒜))",
	},
		"The cotangent transition has diagonal Jacobian blocks J and "+
			"inverse-transpose J, so their determinant product is positive. The "+
			"fixed coordinate permutation gives the symplectic oriented atlas."),
})}

var ComplexTangent = complexTangentThm{family.Add(registry.ProofEntry{
	Name: "ComplexTangent",
	Key:  "prop_4d405d8f3c991cc5",
	Deps: []registry.EntryLike{
		topological_index.NormalProjectionSmooth,
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
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀N:num. " +
			"∀f:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({x:(num → real) | vec⟨N⟩(&0, x)}), " +
				"    f)",
		},
		Conclusion: "smooth_projection_bundle(n, " +
			"    N, " +
			"    T, " +
			"    𝒜, " +
			"    snd(embedding_complex_tangent(n, N, T, 𝒜, f))) ∧ " +
			"(∀x:A. x ∈ ⋃T ⇒ projection_rank(embedding_complex_tangent(n, N, T, 𝒜, f), x) = n) ∧ " +
			"projection_isomorphic(T, " +
			"    projection_sum(embedding_complex_tangent(n, N, T, 𝒜, f), " +
			"        embedding_normal_bundle(n, N, T, 𝒜, f)), " +
			"    projection_trivial(T, N))",
	},
		"The differential identifies the real tangent bundle with the orthogonal tangent image. "+
			"Complexification gives the displayed projection, orthogonal to the complexified normal "+
			"projection. Its trace at the point, that of the real projection read in the coordinate basis "+
			"of ℝ^N (TraceFromBasis), is the dimension of its image (IdempotentTraceIsRank), the "+
			"complement of the normal image (NormalProjectionSpec): the tangent image, of dimension n, the "+
			"differential being linear and injective (EuclideanDifferentialLinear, "+
			"EuclideanDifferentialInjective) on the tangent module, isomorphic to ℝⁿ "+
			"(TangentChartIsomorphism, IsomorphismDim, FreeModuleDim), while the normal image has "+
			"dimension N less that (AnnihilatorDimension); the choice in projection_rank picks the trace n."),
})}

var EmbeddedTangentIsomorphic = embeddedTangentIsomorphicThm{family.Add(registry.ProofEntry{
	Name: "EmbeddedTangentIsomorphic",
	Key:  "prop_53913de2cb009180",
	Deps: []registry.EntryLike{
		ComplexTangent,
		topological_index.NormalProjectionSmooth,
		embedding_normal.NormalProjectionSpec,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀N M:num. " +
			"∀f g:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({x:(num → real) | vec⟨N⟩(&0, x)}), " +
				"    f)",
			"smooth_manifold_embedding⟨n, M⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(M), " +
				"    euclidean_atlas({x:(num → real) | vec⟨M⟩(&0, x)}), " +
				"    g)",
		},
		Conclusion: "projection_isomorphic(T, " +
			"    embedding_complex_tangent(n, N, T, 𝒜, f), " +
			"    embedding_complex_tangent(n, M, T, 𝒜, g))",
	},
		"At each point the differential of f is injective with image the range of its tangent "+
			"projection. The differential of g composed with the left inverse of the differential of "+
			"f that vanishes on the normal space carries one tangent image onto the other; in charts "+
			"both are smooth matrix formulas, so it and its reverse are continuous. Complexify both."),
})}

var TangentToddOnEmbedding = tangentToddOnEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "TangentToddOnEmbedding",
	Key:  "prop_dc4e0c10e0c16708",
	Deps: []registry.EntryLike{ComplexTangent, EmbeddedTangentIsomorphic, chern_weil.ToddIsomorphism},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀N k:num. " +
			"∀f:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({x:(num → real) | vec⟨N⟩(&0, x)}), " +
				"    f)",
		},
		Conclusion: "tangent_todd_class(n, T, 𝒜, k) = " +
			"todd_class(n, T, 𝒜, embedding_complex_tangent(n, N, T, 𝒜, f), k)",
	},
		"The given embedding witnesses the choice in the definition. Any "+
			"two embedded tangent projections are smooth and isomorphic, and "+
			"isomorphic smooth projections have equal Todd classes."),
})}

var NormalToddCorrection = normalToddCorrectionThm{family.Add(registry.ProofEntry{
	Name: "NormalToddCorrection",
	Key:  "prop_c0596fa451b37c2d",
	Deps: []registry.EntryLike{
		ComplexTangent,
		TangentToddOnEmbedding,
		topological_index.NormalProjectionSmooth,
		chern_weil.ToddDirectSum,
		chern_weil.ToddIsomorphism,
		chern_weil.ToddTrivial,
		chern_thom.InverseTodd,
		de_rham_product.WedgeClass,
		de_rham_product.WedgeBilinear,
		de_rham_product.WedgeAssociative,
		de_rham_product.WedgeGradedCommutative,
		de_rham_product.WedgeUnit,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀N k:num. " +
			"∀f:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({x:(num → real) | vec⟨N⟩(&0, x)}), " +
				"    f)",
		},
		Conclusion: "inverse_todd_class(n, " +
			"    T, " +
			"    𝒜, " +
			"    projection_dual(embedding_normal_bundle(n, N, T, 𝒜, f)), " +
			"    k) = " +
			"tangent_todd_class(n, T, 𝒜, k)",
	},
		"The normal projection has real entries, so it is its own dual. Tangent and normal sum to the "+
			"trivial projection, whose Todd class is the unit, so by multiplicativity the tangent Todd "+
			"class inverts the normal one; inverses are unique in the commutative even-degree de Rham ring."),
})}

var IntegrandCarrier = integrandCarrierThm{family.Add(registry.ProofEntry{
	Name: "IntegrandCarrier",
	Key:  "prop_6c111cc1181e0a8e",
	Deps: []registry.EntryLike{
		TangentToddOnEmbedding,
		ComplexTangent,
		manifold_embedding.CompactSmoothEmbedding,
		chern_weil.GrassmannConnection,
		chern_weil.ToddClosed,
		de_rham.ClassMember,
		de_rham.PullbackHom,
		manifold_cotangent.ProjectionSmooth,
		compact_chern.CharacterCarrier,
		compact_de_rham.ProductClass,
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
		Conclusion: "index_character_class(n, T, 𝒜, a) ∈ " +
			"(compact_de_rham_module(2 * n, " +
			"        cotangent_topology(n, T, 𝒜), " +
			"        cotangent_atlas(n, T, 𝒜), " +
			"        2 * n)).carrier",
	},
		"Compactness gives a Euclidean embedding, so each tangent Todd component is the "+
			"class of a closed Todd form of an embedded tangent projection. Each summand is "+
			"then a compact Chern class times a pulled-back ordinary class, of total degree 2n."),
})}

var AtiyahSingerCohomological = atiyahSingerCohomologicalThm{family.Add(registry.ProofEntry{
	Name: "AtiyahSingerCohomological",
	Key:  "prop_bcf0ea479c686ec",
	Deps: []registry.EntryLike{
		index_comparison.AtiyahSingerIndex,
		NormalToddCorrection,
		CotangentOrientation,
		IntegrandCarrier,
		chern_thom.ChernThom,
		topological_index.TopologicalIndexOnEmbedding,
		topological_index.EuclideanBottNormalization,
		compact_de_rham.IntegralClass,
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
		Conclusion: "real_of_int(analytic_index(n, T, 𝒜, a)) = cohomological_index(n, T, 𝒜, a)",
	},
		"The analytic index equals the topological index. Evaluate the latter by the Chern–Thom "+
			"comparison on the normal pushforward, integrated through the oriented tubular identification "+
			"and open extension: the Euclidean Bott character contributes (-1)^N and the complex normal "+
			"rank (-1)^(N-n), and the inverse normal Todd factor is the tangent Todd class."),
})}
