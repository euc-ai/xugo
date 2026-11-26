// Cohomology isomorphisms make the Euler characteristic invariant under atlas changes and smooth homotopy equivalence.

package de_rham_betti

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

var EulerCohomologyIsomorphic = eulerCohomologyIsomorphicThm{family.Add(registry.ProofEntry{
	Name: "EulerCohomologyIsomorphic",
	Key:  "prop_e40334193bdb8fbc",
	Reading: "The manifold dimensions can differ, so the two defining sums need a common " +
		"bound before comparison. All high-degree terms vanish on the corresponding manifold. " +
		"The finiteness hypothesis makes both sides ordinary Euler characteristics; without " +
		"it the equation would rest on the one value module_dim takes off finite bases.",
	Deps: []registry.EntryLike{BettiIsomorphic, EulerFiniteRange, real_sum.Congruence},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"∀q:num. finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, q))",
			"∀k:num. " +
				"    module_isomorphic(real_ring, " +
				"        de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"        de_rham_cohomology_module⟨m⟩(S, ℬ, k))",
		},
		Conclusion: "(∀q:num. finite_dimensional(real_ring, de_rham_cohomology_module⟨m⟩(S, ℬ, q))) ∧ " +
			"de_rham_euler⟨n⟩(T, 𝒜) = de_rham_euler⟨m⟩(S, ℬ)",
	},
		"BettiIsomorphic transfers finiteness and equality in every degree. Extend both "+
			"Euler sums to the common bound n+m by EulerFiniteRange and compare termwise."),
})}

var EulerDiffeomorphism = eulerDiffeomorphismThm{family.Add(registry.ProofEntry{
	Name: "EulerDiffeomorphism",
	Key:  "prop_e809080f27f951d5",
	Reading: "No orientation is required. Finite cohomology on the source makes " +
		"both sides ordinary Euler characteristics, the pullback isomorphisms " +
		"carrying it to the target; compactness is one way to supply that hypothesis.",
	Deps: []registry.EntryLike{
		EulerCohomologyIsomorphic,
		de_rham.PullbackHom,
		de_rham.PullbackCompose,
		de_rham.PullbackIdentity,
		de_rham.PullbackCongruence,
		smooth_manifold.DiffeomorphismDef,
		smooth_manifold.DiffeomorphismInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)",
			"∀q:num. finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, q))",
		},
		Conclusion: "de_rham_euler⟨n⟩(T, 𝒜) = de_rham_euler⟨n⟩(S, ℬ)",
	},
		"Pullback by f and its carrier inverse are mutually inverse on each cohomology carrier, by "+
			"composition and carrier congruence. Apply EulerCohomologyIsomorphic to these isomorphisms."),
})}

var EulerHomotopyEquivalence = eulerHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "EulerHomotopyEquivalence",
	Key:  "prop_54962c601c609aec",
	Reading: "Both composites are homotopic to their respective identities; a one-sided " +
		"retraction alone is insufficient. The homotopies are smooth on an open time " +
		"neighbourhood of the full unit interval, and the two manifold dimensions may differ.",
	Deps: []registry.EntryLike{
		EulerCohomologyIsomorphic,
		de_rham.HomotopyInvariance,
		de_rham.PullbackHom,
		de_rham.PullbackCompose,
		de_rham.PullbackIdentity,
		de_rham.PullbackCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀g:(B → A). " +
			"∀J:set(num → real). " +
			"∀H:(prod(A, num → real) → A). " +
			"∀K:(prod(B, num → real) → B).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"smooth_manifold_map⟨m, n⟩(S, ℬ, T, 𝒜, g)",
			"∀q:num. finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, q))",
			"J ∈ euclidean_topology(1)",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ «time point»(t) ∈ J",
			"smooth_manifold_map⟨n + 1, n⟩(«cylinder topology», «cylinder atlas», T, 𝒜, H)",
			"smooth_manifold_map⟨m + 1, m⟩(product_topology(S, subtopology(euclidean_topology(1), J)), " +
				"    smooth_product_atlas⟨m, 1⟩(ℬ, euclidean_atlas(J)), " +
				"    S, " +
				"    ℬ, " +
				"    K)",
			"∀x:A. x ∈ ⋃T ⇒ H((x, «time point»(&0))) = g(f(x)) ∧ H((x, «time point»(&1))) = x",
			"∀y:B. y ∈ ⋃S ⇒ K((y, «time point»(&0))) = f(g(y)) ∧ K((y, «time point»(&1))) = y",
		},
		Conclusion: "de_rham_euler⟨n⟩(T, 𝒜) = de_rham_euler⟨m⟩(S, ℬ)",
	},
		"Apply HomotopyInvariance to both supplied homotopies. Contravariant composition "+
			"makes f* and g* inverse on every cohomology carrier. EulerCohomologyIsomorphic "+
			"then transfers finite dimensionality and compares the Euler sums."),
})}
