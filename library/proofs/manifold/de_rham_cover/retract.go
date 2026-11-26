// A smooth retraction splits pullback; compact Euclidean retracts, and so compact manifolds, inherit
// finiteness from box unions.

package de_rham_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

var RetractCohomology = retractCohomologyThm{family.Add(registry.ProofEntry{
	Name: "RetractCohomology",
	Key:  "prop_309a19740a73c0e6",
	Reading: "Only r∘i=id is assumed. The ambient manifold need " +
		"not retract by a homotopy, and no equality i∘r=id is claimed.",
	Deps: []registry.EntryLike{
		de_rham.PullbackHom,
		de_rham.PullbackCompose,
		de_rham.PullbackIdentity,
		de_rham.PullbackCongruence,
		smooth_manifold.SmoothMapCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀i:(A → B). " +
			"∀r:(B → A).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, i)",
			"smooth_manifold_map⟨m, n⟩(S, ℬ, T, 𝒜, r)",
			"∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x",
		},
		Conclusion: "(∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier ⇒ " +
			"    de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, i)(de_rham_pullback⟨m, n⟩(S, ℬ, T, 𝒜, k, r)(s)) = " +
			"    s) ∧ " +
			"injective_on(de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier, " +
			"    de_rham_pullback⟨m, n⟩(S, ℬ, T, 𝒜, k, r)) ∧ " +
			"image(de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, i), " +
			"    de_rham_cohomology_module⟨m⟩(S, ℬ, k).carrier) = " +
			"de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier",
	},
		"Contravariance identifies i* after r* with pullback by r after i, which "+
			"agrees with the identity on the source carrier. The induced identity "+
			"gives the displayed splitting. Since both pullbacks preserve their "+
			"cohomology carriers, a left inverse makes r* injective and i* surjective."),
})}

var RetractFiniteCohomology = retractFiniteCohomologyThm{family.Add(registry.ProofEntry{
	Name: "RetractFiniteCohomology",
	Key:  "prop_75a8dac5c96c2a83",
	Reading: "The dimension comparison is stated only when the ambient cohomology is " +
		"finite-dimensional; module_dim is a choice value without an infinite-dimensional interpretation.",
	Deps: []registry.EntryLike{RetractCohomology, de_rham.PullbackHom, module_dimension.ImageDim},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀i:(A → B). " +
			"∀r:(B → A).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, i)",
			"smooth_manifold_map⟨m, n⟩(S, ℬ, T, 𝒜, r)",
			"∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x",
			"finite_dimensional(real_ring, de_rham_cohomology_module⟨m⟩(S, ℬ, k))",
		},
		Conclusion: "finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k)) ∧ " +
			"module_dim(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k)) ≤ " +
			"module_dim(real_ring, de_rham_cohomology_module⟨m⟩(S, ℬ, k))",
	},
		"RetractCohomology makes i* a surjection onto the source cohomology. Apply "+
			"the finite-dimensional image theorem to this homomorphism; its image is the "+
			"full target carrier, so its image module is that cohomology module itself."),
})}

var CompactEuclideanRetractFiniteCohomology = compactEuclideanRetractFiniteCohomologyThm{family.Add(registry.ProofEntry{
	Name: "CompactEuclideanRetractFiniteCohomology",
	Key:  "prop_df1aaf1ce34dbd17",
	Reading: "U need not be homotopy equivalent to the manifold. The proof surrounds the image " +
		"by a finite union of boxes inside U, and neither that union nor its box intersections with " +
		"the image need be contractible. The retraction identity supplies the split cohomology " +
		"maps; the existence of an embedding and tubular retraction is a separate geometric input.",
	Deps: []registry.EntryLike{
		RetractFiniteCohomology,
		FiniteBoxUnionFiniteCohomology,
		euclidean_topology.CompactOpenBoxCover,
		smooth_manifold.SmoothMapRestrict,
		smooth_manifold.SmoothMapEuclidean,
		continuous.ImageCompact,
		compact.CompactInSubtopology,
	},
	Build: family.Card(Statement{
		Binders: "∀n N k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(num → real). " +
			"∀i:(A → num → real). " +
			"∀r:((num → real) → A).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, N⟩(T, 𝒜, subtopology(euclidean_topology(N), U), euclidean_atlas(U), i)",
			"smooth_manifold_map⟨N, n⟩(subtopology(euclidean_topology(N), U), euclidean_atlas(U), T, 𝒜, r)",
			"compact_in(T, ⋃T)",
			"U ∈ euclidean_topology(N)",
			"∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x",
		},
		Conclusion: "finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k))",
	}, "The image i(M) is compact in Euclidean space. Choose a finite box union V with "+
		"i(M)⊆V⊆U, then corestrict i to V and restrict r to V; the smooth identity between the "+
		"restricted and canonical Euclidean atlases gives the required maps. Their composite "+
		"on M remains the identity. Finiteness of H^k(V) transfers along this retraction."),
})}

var CompactManifoldFiniteCohomology = compactManifoldFiniteCohomologyThm{family.Add(registry.ProofEntry{
	Name: "CompactManifoldFiniteCohomology",
	Key:  "prop_a4f711c450bb1c33",
	Reading: "Compact smooth manifolds may be empty or disconnected and need no orientation. " +
		"The Euclidean retraction is obtained from compactness, rather than included as an input.",
	Deps: []registry.EntryLike{
		manifold_embedding.CompactEuclideanRetract,
		CompactEuclideanRetractFiniteCohomology,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k))",
	},
		"CompactEuclideanRetract supplies a smooth map into an open Euclidean neighbourhood "+
			"and a smooth retraction of that neighbourhood whose composite with it is the "+
			"identity. Apply CompactEuclideanRetractFiniteCohomology to this data in degree k."),
})}
