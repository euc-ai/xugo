package torus_manifold

import (
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ClosedTorus = closedTorusThm{family.Add(registry.ProofEntry{
	Name: "ClosedTorus",
	Key:  "prop_42c4f08ab19fda71",
	Deps: []registry.EntryLike{
		product_topology.IndexedProductCarrier,
		product_topology.Tychonoff,
		complex_topology.CircleCompact,
		product_topology.IndexedContinuousIff,
		product_topology.IndexedProjectionContinuous,
		continuous.ImageCompact,
		compact.CompactInSubtopology,
		product_topology.IndexedHausdorff,
		complex_topology.ComplexHausdorff,
		topological_space.HausdorffSubtopology,
		metric_space.CountableProductMetricTopology,
		metric_space.MetricTopologySubspace,
		countability.CompactImpLindelof,
		metric_space.MetricLindelofIffSecondCountable,
		product_topology.IndexedCylinderOpen,
		complex_topology.OpenDiffFinite,
		complex_topology.ContinuousIffParts,
		euclidean_topology.ContinuousIffCoordinates,
		vec_smooth.SmoothReciprocal,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothAdd,
		vec_smooth.SmoothSub,
	},
	Build: family.Card(
		"∀n:num. "+
			"    smooth_manifold⟨n⟩(smooth_torus_topology(n), smooth_torus_atlas(n)) ∧ "+
			"    compact_in(smooth_torus_topology(n), ⋃smooth_torus_topology(n)) ∧ "+
			"    ⋃smooth_torus_topology(n) = smooth_torus_carrier(n)",
		"The carrier is the product of n unit circles (IndexedProductCarrier): compact by Tychonoff "+
			"over CircleCompact carried in by the identity (IndexedContinuousIff, ImageCompact, "+
			"CompactInSubtopology), Hausdorff (IndexedHausdorff, HausdorffSubtopology), and second "+
			"countable as a compact metric subspace of the countable product distance "+
			"(CountableProductMetricTopology, MetricTopologySubspace, CompactImpLindelof, "+
			"MetricLindelofIffSecondCountable). The chart at c sends z to t_j = im(c̄_j z_j)/(1 + "+
			"re(c̄_j z_j)) with inverse t ↦ c_j(1 + it)/(1 − it), both continuous (ContinuousIffParts, "+
			"ContinuousIffCoordinates), on a domain open by IndexedCylinderOpen and OpenDiffFinite, and "+
			"covering since c_j ≠ −c_j. With u = c̄'_j c_j = a + ib the transition is s = (b(1 − t²) + "+
			"2at)/(1 + t² + a(1 − t²) − 2bt), its denominator (1 + t²)(1 + re(w)) positive on the "+
			"overlap, so smooth (SmoothReciprocal, SmoothMul, SmoothAdd, SmoothSub); n = 0 is one point."),
})}

var CubeDiffeomorphism = cubeDiffeomorphismThm{family.Add(registry.ProofEntry{
	Name: "CubeDiffeomorphism",
	Key:  "prop_14efc8fb1e7db758",
	Deps: []registry.EntryLike{
		vec_smooth.SmoothCoordinate,
		vec_smooth.SmoothConst,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothAdd,
		vec_smooth.SmoothSub,
		vec_smooth.SmoothSqrt,
		vec_smooth.SmoothReciprocal,
		euclidean_topology.EuclideanTopology,
		euclidean_topology.EuclideanSpace,
		euclidean_topology.OpenBoxOpen,
		real_sqrt.SqrtPos,
		real_sqrt.SqrtPowTwo,
		real_sqrt.SqrtUnique,
		real_trigonometry.PiBounds,
	},
	Build: family.Card(
		"∀n:num. "+
			"    vec_diffeomorphic_map⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, "+
			"        torus_small_box(n), "+
			"        torus_cube_map(n))",
		"Each coordinate t ↦ (π/2)t/√(1 + t²) is smooth on ℝⁿ, open by EuclideanTopology "+
			"and EuclideanSpace (SmoothCoordinate, SmoothConst, SmoothMul, SmoothAdd, "+
			"SmoothSqrt, SmoothReciprocal), and below π/2 in size since t² < 1 + t² "+
			"(SqrtPowTwo, SqrtPos, PiBounds). The inverse is s ↦ σ/√(1 − σ²) with σ = 2s/π, "+
			"smooth on the box euclidean_open_box(−π/2, π/2), open by OpenBoxOpen (SmoothSub); "+
			"the two undo each other by SqrtUnique, 1 − σ² being 1/(1 + t²) at σ = t/√(1 + t²)."),
})}

var EuclideanOpenEmbedding = euclideanOpenEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "EuclideanOpenEmbedding",
	Key:  "prop_ba58231130b3a7de",
	Deps: []registry.EntryLike{ClosedTorus, CubeDiffeomorphism},
	Build: family.Card(
		"∀n:num. "+
			"    smooth_manifold_embedding⟨n, n⟩(euclidean_topology(n), "+
			"        euclidean_atlas({x:(num → real) | vec⟨n⟩(&0, x)}), "+
			"        smooth_torus_topology(n), "+
			"        smooth_torus_atlas(n), "+
			"        torus_euclidean_map(n)) ∧ "+
			"    image(torus_euclidean_map(n), {x:(num → real) | vec⟨n⟩(&0, x)}) ∈ smooth_torus_topology(n)",
		"The angular exponential is a diffeomorphism from the half-period cube onto the "+
			"product of positive-real semicircles; compose with the cube diffeomorphism."),
})}
