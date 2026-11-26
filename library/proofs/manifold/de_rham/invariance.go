// Smoothly homotopic maps induce the same map on each de Rham cohomology module.

package de_rham

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

var HomotopyInvariance = homotopyInvarianceThm{family.Add(registry.ProofEntry{
	Name: "HomotopyInvariance",
	Key:  "prop_4c452818e41e33ca",
	Reading: "The homotopy is smooth on the product with an open time set containing " +
		"[0,1]. Endpoint equations are only on the base carrier, and equality of induced " +
		"maps is only claimed on actual cohomology classes; no compactness assumption is " +
		"needed. Endpoint composition and carrier congruence give smoothness of f and g, " +
		"while PullbackHom puts the class pulled back along H in the cylinder carrier.",
	Deps: []registry.EntryLike{
		Complex,
		EndpointSmooth,
		EndpointCochainHomotopy,
		PullbackCochain,
		PullbackDef,
		CohomologyModuleDef,
		PullbackHom,
		PullbackCompose,
		PullbackCongruence,
		smooth_manifold.SmoothMapCompose,
		smooth_manifold.SmoothMapCongruence,
		chain_complex.HomotopicSameCohomologyMap,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀k:num. " +
			"∀J:set(num → real). " +
			"∀H:(prod(A, num → real) → B). " +
			"∀f g:(A → B). " +
			"∀s:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"J ∈ euclidean_topology(1)",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ «time point»(t) ∈ J",
			"smooth_manifold_map⟨n + 1, m⟩(«cylinder topology», «cylinder atlas», S, ℬ, H)",
			"∀x:A. x ∈ ⋃T ⇒ H((x, «time point»(&0))) = f(x) ∧ H((x, «time point»(&1))) = g(x)",
			"s ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, k).carrier",
		},
		Conclusion: "de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)(s) = " +
			"de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, g)(s)",
	},
		"The two endpoint pullbacks agree on the cylinder cohomology by EndpointCochainHomotopy and "+
			"HomotopicSameCohomologyMap. Apply them to the pullback of s along H and use contravariant "+
			"composition. Smoothness of the canonical endpoint maps and carrier agreement with f and g "+
			"give their smoothness and identify their induced maps by PullbackCongruence."),
})}
