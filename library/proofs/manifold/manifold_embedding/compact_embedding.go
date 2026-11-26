// Compact manifolds embed in finite Euclidean space and admit the weak Whitney dimension bounds.

package manifold_embedding

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_null"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var CompactSmoothEmbedding = compactSmoothEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "CompactSmoothEmbedding",
	Key:  "prop_44bfa9f92a8f3e8e",
	Reading: "The target dimension is only required to be finite. The partition " +
		"supports lie inside chart domains, so the coordinate products extend smoothly by " +
		"zero across the chart boundaries. Empty and zero-dimensional manifolds are included.",
	Deps: []registry.EntryLike{
		smooth_manifold.PartitionOfUnity,
		smooth_manifold.FunctionExtendZero,
		smooth_manifold.ImmersionAtlasCriterion,
		smooth_manifold.CompactInjectiveImmersion,
		smooth_manifold.SmoothMapCompatibleCharts,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothCoordinate,
		vec_smooth.SmoothLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "∃N:num. ∃i:(A → num → real). " +
			"    smooth_manifold_embedding⟨n, N⟩(T, " +
			"        𝒜, " +
			"        euclidean_topology(N), " +
			"        euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
			"        i)",
	},
		"Take a finite chart cover and a subordinate finite partition of unity, and form "+
			"the blocks ρ and ρ times each chart coordinate, extended by zero. At a point with "+
			"ρ>0 the block ratios recover its coordinates, separating points, while the "+
			"differential of the ρ block together with the ρ-coordinate blocks forces a killed "+
			"tangent vector to vanish. The resulting injective immersion is an embedding by "+
			"CompactInjectiveImmersion; the empty manifold is handled by the map to zero-space."),
})}

var PointEmbedding = pointEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "PointEmbedding",
	Key:  "prop_6ca06fb696098b55",
	Deps: []registry.EntryLike{
		smooth_manifold.EuclideanManifold,
		smooth_manifold.SmoothMapConstant,
		smooth_manifold.CompactInjectiveImmersion,
	},
	Build: family.Card(
		"∀N:num. "+
			"    smooth_manifold⟨0⟩(euclidean_topology(0), euclidean_atlas({y:num → real | vec⟨0⟩(y)})) ∧ "+
			"    compact_in(euclidean_topology(0), ⋃euclidean_topology(0)) ∧ "+
			"    smooth_manifold_embedding⟨0, N⟩(euclidean_topology(0), "+
			"        euclidean_atlas({y:num → real | vec⟨0⟩(y)}), "+
			"        euclidean_topology(N), "+
			"        euclidean_atlas({y:num → real | vec⟨N⟩(y)}), "+
			"        λy:(num → real). λi:num. &0)",
		"Zero-dimensional Euclidean space is the single zero vector, a compact manifold with its "+
			"global chart. The constant map at the origin is smooth and injective, its differential on "+
			"the zero tangent space is injective, and a compact injective immersion is an embedding."),
})}

var EmbeddingProjectionStep = embeddingProjectionStepThm{family.Add(registry.ProofEntry{
	Name: "EmbeddingProjectionStep",
	Key:  "prop_cba331db692377d5",
	Reading: "The dimension inequality makes N positive, so the punctured Euclidean carrier is " +
		"a nonempty open set from which to choose the direction. This also handles an empty source, " +
		"whose bad cones are empty; it does not rely on zero belonging to a cone. The resulting map " +
		"is linear on the whole host and sends normalized N-vectors to normalized (N−1)-vectors.",
	Deps: []registry.EntryLike{
		smooth_manifold.EmbeddingDef,
		smooth_manifold.ImmersionAtlasCriterion,
		smooth_manifold.CompactInjectiveImmersion,
		vec_null.LowerDimensionalImageNull,
		vec_null.NullCountableUnion,
		vec_null.OpenNonemptyNotNull,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothMul,
		vec_smooth.ContinuouslyDifferentiableLocallyLipschitz,
		vec_smooth.LinearSmoothMap,
		vec_smooth.JacobianChain,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀i:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"compact_in(T, ⋃T)",
			"2 * n + 1 < N",
		},
		Conclusion: "∃L:((num → real) → num → real). " +
			"    vec_linear(L) ∧ " +
			"    (∀u:(num → real). vec⟨N⟩(u) ⇒ vec⟨N - 1⟩(L(u))) ∧ " +
			"    smooth_manifold_embedding⟨n, N - 1⟩(T, " +
			"        𝒜, " +
			"        euclidean_topology(N - 1), " +
			"        euclidean_atlas({y:num → real | vec⟨N - 1⟩(y)}), " +
			"        L ∘ i)",
	},
		"In finitely many chart pairs, the secant cone t(i(x)−i(y)) has parameter dimension 2n+1; in "+
			"each chart the tangent cone Di(x)v has dimension 2n. Their images are null by "+
			"LowerDimensionalImageNull and local Lipschitz regularity. Choose a nonzero direction outside "+
			"their union, project along it, identify its perpendicular hyperplane linearly with normalized "+
			"(N−1)-space, and use CompactInjectiveImmersion for the resulting injective immersion."),
})}

var ImmersionProjectionStep = immersionProjectionStepThm{family.Add(registry.ProofEntry{
	Name: "ImmersionProjectionStep",
	Key:  "prop_9ed969d67a04e994",
	Reading: "The dimension inequality makes N positive, so the punctured Euclidean carrier " +
		"is a nonempty open set from which to choose the direction. This also handles an empty " +
		"source, whose bad cones are empty; it does not rely on zero belonging to a cone. The " +
		"resulting map is linear on the whole host and sends normalized N-vectors to normalized " +
		"(N−1)-vectors. No compactness is read: a countable atlas gives countably many cones.",
	Deps: []registry.EntryLike{
		smooth_manifold.ImmersionAtlasCriterion,
		smooth_manifold.CountableAtlas,
		vec_null.LowerDimensionalImageNull,
		vec_null.NullCountableUnion,
		vec_null.OpenNonemptyNotNull,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothMul,
		vec_smooth.ContinuouslyDifferentiableLocallyLipschitz,
		vec_smooth.LinearSmoothMap,
		vec_smooth.JacobianChain,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀i:(A → num → real).",
		Hypotheses: []string{
			"smooth_manifold_immersion⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"2 * n < N",
		},
		Conclusion: "∃L:((num → real) → num → real). " +
			"    vec_linear(L) ∧ " +
			"    (∀u:(num → real). vec⟨N⟩(u) ⇒ vec⟨N - 1⟩(L(u))) ∧ " +
			"    smooth_manifold_immersion⟨n, N - 1⟩(T, " +
			"        𝒜, " +
			"        euclidean_topology(N - 1), " +
			"        euclidean_atlas({y:num → real | vec⟨N - 1⟩(y)}), " +
			"        L ∘ i)",
	},
		"The chartwise tangent cone Di(x)v is the image of a smooth map on an open subset of "+
			"normalized 2n-space, hence is null in N-space by LowerDimensionalImageNull. A nonzero "+
			"direction outside the countable union of these cones gives a linear projection with "+
			"injective coordinate differentials; identify the perpendicular hyperplane with normalized "+
			"(N−1)-space. No avoidance of secants or injectivity of the point map is required."),
})}

var WhitneyEmbedding = whitneyEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "WhitneyEmbedding",
	Key:  "prop_4c83cff2aaaf0d19",
	Reading: "This is the compact weak Whitney bound 2n+1, including n=0 and the " +
		"empty manifold. No proper embedding theorem for noncompact manifolds is asserted.",
	Deps: []registry.EntryLike{
		CompactSmoothEmbedding,
		EmbeddingProjectionStep,
		smooth_manifold.CompactInjectiveImmersion,
		smooth_manifold.ImmersionCompose,
		vec_smooth.LinearSmoothMap,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "∃i:(A → num → real). " +
			"    smooth_manifold_embedding⟨n, 2 * n + 1⟩(T, " +
			"        𝒜, " +
			"        euclidean_topology(2 * n + 1), " +
			"        euclidean_atlas({y:num → real | vec⟨2 * n + 1⟩(y)}), " +
			"        i)",
	},
		"Start with CompactSmoothEmbedding. If its dimension exceeds 2n+1, repeatedly apply "+
			"EmbeddingProjectionStep; if it is smaller, include it by zero padding, which is an injective "+
			"linear immersion. CompactInjectiveImmersion supplies the image topology after padding."),
})}

var WhitneyImmersion = whitneyImmersionThm{family.Add(registry.ProofEntry{
	Name: "WhitneyImmersion",
	Key:  "prop_44002b958d0a3805",
	Reading: "The point map need not be injective. In dimension zero this " +
		"distinction allows any compact zero-manifold to immerse in zero-space.",
	Deps: []registry.EntryLike{
		CompactSmoothEmbedding,
		smooth_manifold.EmbeddingDef,
		ImmersionProjectionStep,
		smooth_manifold.ImmersionCompose,
		vec_smooth.LinearSmoothMap,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "∃i:(A → num → real). " +
			"    smooth_manifold_immersion⟨n, 2 * n⟩(T, " +
			"        𝒜, " +
			"        euclidean_topology(2 * n), " +
			"        euclidean_atlas({y:num → real | vec⟨2 * n⟩(y)}), " +
			"        i)",
	},
		"Discard the topological clause of CompactSmoothEmbedding and lower the target "+
			"dimension with ImmersionProjectionStep until it is 2n. If necessary, zero padding "+
			"reaches that dimension from below. For n=0 the result may identify all points in the "+
			"singleton zero-space, which still has injective maps between the zero tangent spaces."),
})}
