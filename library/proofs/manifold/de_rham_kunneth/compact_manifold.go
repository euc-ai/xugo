// Compactness supplies the geometric retraction for homogeneous bases and self-product Künneth.

package de_rham_kunneth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	"github.com/euc-ai/xugo/library/registry"
)

var CompactManifoldHomogeneousBasis = compactManifoldHomogeneousBasisThm{family.Add(registry.ProofEntry{
	Name: "CompactManifoldHomogeneousBasis",
	Key:  "prop_2c96b8aaa81ce666",
	Deps: []registry.EntryLike{de_rham_cover.CompactManifoldFiniteCohomology, HomogeneousBasisExists},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "∃E:set(prod(num, " +
			"            set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))). " +
			"    de_rham_homogeneous_basis⟨n⟩(T, 𝒜, E)",
	},
		"Apply CompactManifoldFiniteCohomology in every degree and then HomogeneousBasisExists. "+
			"The vanishing above the manifold dimension makes the degree-tagged union finite."),
})}

var CompactManifoldKunnethComparison = compactManifoldKunnethComparisonThm{family.Add(registry.ProofEntry{
	Name: "CompactManifoldKunnethComparison",
	Key:  "prop_bc6dd08f9c82cf01",
	Reading: "Only the first factor is assumed compact. The second factor can be any smooth " +
		"manifold with the supplied finite homogeneous cohomology basis, including the empty one.",
	Deps: []registry.EntryLike{
		manifold_embedding.CompactEuclideanRetract,
		CompactEuclideanRetractKunneth,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀E:set(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
			"de_rham_homogeneous_basis⟨m⟩(S, ℬ, E)",
		},
		Conclusion: "module_isomorphism(real_ring, " +
			"    de_rham_kunneth_module⟨n⟩(T, 𝒜, k, E), " +
			"    de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        k), " +
			"    de_rham_kunneth_map⟨n, m⟩(T, 𝒜, S, ℬ, k, E))",
	},
		"Choose the first factor’s Euclidean neighbourhood retraction with "+
			"CompactEuclideanRetract. CompactEuclideanRetractKunneth then "+
			"applies to that data and the supplied basis of the second factor."),
})}

var CompactManifoldKunneth = compactManifoldKunnethThm{family.Add(registry.ProofEntry{
	Name: "CompactManifoldKunneth",
	Key:  "prop_a40df6d04203cd5c",
	Reading: "The span denotes finite linear combinations, so this is the finite-product " +
		"expansion of every self-product class. Both factor degrees are explicit nonnegative " +
		"numbers summing to k. No orientation, connectedness or supplied embedding is " +
		"required. A spanning product is the class of a wedge of projection pullbacks of " +
		"closed representatives of its factors, by ExternalProductClass and ClassRepresentative.",
	Deps: []registry.EntryLike{
		manifold_embedding.CompactEuclideanRetract,
		CompactEuclideanRetractSelfProductSpan,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "de_rham_cohomology_module⟨n + n⟩(product_topology(T, T), " +
			"    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
			"    k).carrier = " +
			"module_span(real_ring, " +
			"    de_rham_cohomology_module⟨n + n⟩(product_topology(T, T), " +
			"        smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
			"        k), " +
			"    {z:set(prod(set(prod(A, A)), prod(A, A) → num → real) → " +
			"            (num → real) → " +
			"            (num → num → real) → " +
			"            real) | " +
			"        ∃p q:num. " +
			"        ∃s t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"            p + q = k ∧ " +
			"            s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier ∧ " +
			"            t ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, q).carrier ∧ " +
			"            z = de_rham_external_product⟨n, n⟩(T, 𝒜, T, 𝒜, p, q, s, t)})",
	},
		"Choose the Euclidean neighbourhood retraction with CompactEuclideanRetract "+
			"and apply CompactEuclideanRetractSelfProductSpan to it."),
})}
