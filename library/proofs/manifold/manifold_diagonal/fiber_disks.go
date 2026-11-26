// Coordinate fiber disks are open convex neighbourhoods and embed smoothly into the tangent bundle.

package manifold_diagonal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/topology/path_connected"
	"github.com/euc-ai/xugo/library/proofs/vector/convex"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var EmbeddedTangentFiberDiskCoordinate = embeddedTangentFiberDiskCoordinateThm{family.Add(registry.ProofEntry{
	Name: "EmbeddedTangentFiberDiskCoordinate",
	Key:  "prop_d09588030343d647",
	Reading: "The formula uses the embedded differential norm, which can " +
		"be only a seminorm when i is not an immersion, so a positive disk " +
		"may be unbounded. This coordinate identity holds for every radius.",
	Deps: []registry.EntryLike{
		embeddedTangentFiberDiskDef,
		EmbeddedTangentDiskDef,
		tangent.TangentFromChart,
		tangent.EuclideanDifferentialCoordinate,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀δ:real.",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
		},
		Conclusion: "«diagonal fiber disk»(c) = " +
			"{u:num → real | " +
			"    vec⟨n⟩(u) ∧ " +
			"    ‖matrix_act⟨n⟩(vec_jacobian_matrix⟨n, N⟩(i ∘ inverse_on(fst(c), snd(c)), snd(c)(x)), u)‖_N < " +
			"    δ}",
	},
		"TangentFromChart gives a genuine tangent vector whose c component "+
			"is u. EuclideanDifferentialCoordinate identifies its image with "+
			"the displayed Jacobian action; unfold the two disk definitions."),
})}

var EmbeddedTangentFiberDiskGeometry = embeddedTangentFiberDiskGeometryThm{family.Add(registry.ProofEntry{
	Name: "EmbeddedTangentFiberDiskGeometry",
	Key:  "prop_512e78676ba09c18",
	Reading: "No immersion or compactness is needed. Positivity of the radius is used for the zero " +
		"point and nonemptiness. In dimension zero the disk is the singleton normalized zero vector.",
	Deps: []registry.EntryLike{
		EmbeddedTangentFiberDiskCoordinate,
		matrix.MatrixActLinear,
		euclidean_topology.NormContinuous,
		euclidean.NormTriangle,
		euclidean.NormSmul,
		convex.ConvexDef,
		path_connected.PathConnectedInDef,
		path_connected.PathConnectedConnected,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀δ:real.",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
			"&0 < δ",
		},
		Conclusion: "«diagonal fiber disk»(c) ∈ euclidean_topology(n) ∧ " +
			"convex(«diagonal fiber disk»(c)) ∧ " +
			"(λj:num. &0) ∈ «diagonal fiber disk»(c) ∧ " +
			"connected_in(subtopology(euclidean_topology(n), «diagonal fiber disk»(c)), " +
			"    «diagonal fiber disk»(c))",
	},
		"EmbeddedTangentFiberDiskCoordinate is the inverse image of a strict norm ball under a "+
			"fixed linear map. Norm continuity gives openness, and linearity with NormTriangle and "+
			"NormSmul gives convexity; the positive radius includes zero. Straight segments stay in the "+
			"set and give paths in its subspace topology, so PathConnectedConnected gives connectedness."),
})}

var TangentFiberInclusionSmooth = tangentFiberInclusionSmoothThm{family.Add(registry.ProofEntry{
	Name: "TangentFiberInclusionSmooth",
	Key:  "prop_b3330c6fc8ec4302",
	Reading: "The base point is fixed and retained in the total-space pair. Smoothness is " +
		"asserted on normalized n-vectors; no arbitrary family of tangent components is admitted.",
	Deps: []registry.EntryLike{
		tangent.TangentFromChart,
		tangent.TangentChartInverse,
		tangent.TangentChartImage,
		tangent.TangentManifold,
		smooth_manifold.SmoothMapCompatibleCharts,
		vec_smooth.LinearSmoothMap,
		vec_smooth.SmoothConst,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A.",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
		},
		Conclusion: "smooth_manifold_map⟨n, 2 * n⟩(euclidean_topology(n), " +
			"    euclidean_atlas({y:num → real | vec⟨n⟩(y)}), " +
			"    tangent_topology⟨n⟩(T, 𝒜), " +
			"    tangent_atlas⟨n⟩(T, 𝒜), " +
			"    λu:(num → real). (x, tangent_from_chart⟨n⟩(T, 𝒜, c, x, u)))",
	},
		"In the lifted c chart the map has coordinates u↦(c(x),u). This affine map is "+
			"smooth and lands in the lifted chart image; TangentChartInverse identifies "+
			"its inverse-coordinate expression with the displayed total-space map."),
})}
