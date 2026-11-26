// Compact Euclidean embeddings admit smooth neighbourhood retractions.

package manifold_embedding

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix_norm"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var CompactTubularRetraction = compactTubularRetractionThm{family.Add(registry.ProofEntry{
	Name: "CompactTubularRetraction",
	Key:  "prop_517778396784318e",
	Reading: "The conclusion gives a neighbourhood retraction for the supplied " +
		"embedding, not merely a locally invertible endpoint map. The global " +
		"injectivity argument uses compactness and embedding injectivity. No " +
		"closest-point minimization property or normal-bundle object is asserted.",
	Deps: []registry.EntryLike{
		smooth_manifold.EmbeddingDef,
		smooth_manifold.ImmersionDimensionBound,
		smooth_manifold.ImmersionAtlasCriterion,
		vec_smooth.SmoothInverseFunction,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothSqrt,
		vec_smooth.SmoothReciprocal,
		matrix_norm.CompactInjectiveMatrixBounds,
		smooth_manifold.SmoothMapLocal,
		smooth_manifold.SmoothMapRestrict,
		smooth_manifold.SmoothMapEuclidean,
		continuous.ImageCompact,
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
		},
		Conclusion: "∃U:set(num → real). ∃r:((num → real) → A). " +
			"    U ∈ euclidean_topology(N) ∧ " +
			"    image(i, ⋃T) ⊆ U ∧ " +
			"    smooth_manifold_map⟨n, N⟩(T, " +
			"        𝒜, " +
			"        subtopology(euclidean_topology(N), U), " +
			"        euclidean_atlas(U), " +
			"        i) ∧ " +
			"    smooth_manifold_map⟨N, n⟩(subtopology(euclidean_topology(N), U), " +
			"        euclidean_atlas(U), " +
			"        T, " +
			"        𝒜, " +
			"        r) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x)",
	},
		"Construct smooth local orthonormal normal frames by Gram–Schmidt on complements of the "+
			"injective coordinate Jacobian; the normal endpoint map i(x)+w has invertible derivative "+
			"at zero, so SmoothInverseFunction gives local smooth inverses. Compactness provides a "+
			"uniform small normal radius with invertible differentials and excludes collisions: "+
			"otherwise two base-point subsequences converge to the same point by injectivity of i, "+
			"contradicting one local inverse. The endpoint image is open, and its inverse base "+
			"component glues to the required retraction; for an empty source choose U empty."),
})}

var CompactEuclideanRetract = compactEuclideanRetractThm{family.Add(registry.ProofEntry{
	Name: "CompactEuclideanRetract",
	Key:  "prop_7ea002b8f526e924",
	Reading: "This supplies the full retraction data consumed by compact " +
		"cohomology theorems. Neither a homotopy equivalence of the ambient " +
		"open set with the manifold nor an isometric embedding is needed.",
	Deps: []registry.EntryLike{CompactSmoothEmbedding, CompactTubularRetraction},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "∃N:num. ∃i:(A → num → real). ∃U:set(num → real). ∃r:((num → real) → A). " +
			"    U ∈ euclidean_topology(N) ∧ " +
			"    image(i, ⋃T) ⊆ U ∧ " +
			"    smooth_manifold_map⟨n, N⟩(T, " +
			"        𝒜, " +
			"        subtopology(euclidean_topology(N), U), " +
			"        euclidean_atlas(U), " +
			"        i) ∧ " +
			"    smooth_manifold_map⟨N, n⟩(subtopology(euclidean_topology(N), U), " +
			"        euclidean_atlas(U), " +
			"        T, " +
			"        𝒜, " +
			"        r) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x)",
	},
		"Choose the finite-dimensional Euclidean embedding of CompactSmoothEmbedding and apply "+
			"CompactTubularRetraction to it. Retain the open neighbourhood, smooth corestriction "+
			"and smooth retraction together with their identity on the source carrier."),
})}
