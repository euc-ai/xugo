package smooth_singular

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/singular_cohomology"
	"github.com/euc-ai/xugo/library/registry"
)

var HomotopyChainHomotopy = homotopyChainHomotopyThm{family.Add(registry.ProofEntry{
	Name: "HomotopyChainHomotopy",
	Key:  "prop_63e1563cbf177b8d",
	Deps: []registry.EntryLike{SmoothSingularMap, ChainComplexDef},
	Reading: "The homotopy is smooth on an open time neighbourhood of [0, 1]. No " +
		"compactness of the source manifold is required; every prism is compact separately.",
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀m:num. " +
				"∀S:set(set(B)). " +
				"∀ℬ:set(prod(set(B), B → num → real)). " +
				"∀f g:(A → B). " +
				"∀J:set(num → real). " +
				"∀H:(prod(A, num → real) → B).",
			Hypotheses: []string{
				"smooth_manifold⟨n⟩(T, 𝒜)",
				"J ∈ euclidean_topology(1)",
				"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ (λj:num. COND(j = 0, t, &0)) ∈ J",
				"smooth_manifold_map⟨n+1, m⟩(product_topology(T, subtopology(euclidean_topology(1), J)), " +
					"    smooth_product_atlas⟨n, 1⟩(𝒜, euclidean_atlas(J)), " +
					"    S, " +
					"    ℬ, " +
					"    H)",
				"∀x:A. " +
					"    x ∈ ⋃T ⇒ " +
					"    H((x, (λj:num. COND(j = 0, &0, &0)))) = f(x) ∧ H((x, (λj:num. COND(j = 0, &1, &0)))) = g(x)",
			},
			Conclusion: "∃h:(num → (((num → real) → A) → real) → ((num → real) → B) → real). " +
				"    chain_homotopy(real_ring, " +
				"        smooth_singular_complex⟨n⟩(T, 𝒜), " +
				"        smooth_singular_complex⟨m⟩(S, ℬ), " +
				"        (λj:num. free_pushforward(real_ring, singular_map(f, j))), " +
				"        (λj:num. free_pushforward(real_ring, singular_map(g, j))), " +
				"        h)",
		},
		"Triangulate each simplex prism and compose its affine pieces with the "+
			"smooth cylinder homotopy. The oriented prism boundary gives the chain "+
			"homotopy formula, including the degree-zero endpoint difference."),
})}

var HomotopyInvariance = homotopyInvarianceThm{family.Add(registry.ProofEntry{
	Name: "HomotopyInvariance",
	Key:  "prop_d303b83583a982cb",
	Deps: []registry.EntryLike{HomotopyChainHomotopy, singular_cohomology.UniversalCoefficient},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀m:num. " +
				"∀S:set(set(B)). " +
				"∀ℬ:set(prod(set(B), B → num → real)). " +
				"∀f:(A → B). " +
				"∀g:(A → B). " +
				"∀J:set(num → real). " +
				"∀H:(prod(A, num → real) → B). " +
				"∀k:num. " +
				"∀s:set(((num → real) → B) → real).",
			Hypotheses: []string{
				"smooth_manifold⟨n⟩(T, 𝒜)",
				"J ∈ euclidean_topology(1)",
				"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ (λj:num. COND(j = 0, t, &0)) ∈ J",
				"smooth_manifold_map⟨n + 1, m⟩(product_topology(T, subtopology(euclidean_topology(1), J)), " +
					"    smooth_product_atlas⟨n, 1⟩(𝒜, euclidean_atlas(J)), " +
					"    S, " +
					"    ℬ, " +
					"    H)",
				"∀x:A. " +
					"    x ∈ ⋃T ⇒ " +
					"    H((x, (λj:num. COND(j = 0, &0, &0)))) = f(x) ∧ H((x, (λj:num. COND(j = 0, &1, &0)))) = g(x)",
				"s ∈ smooth_singular_cohomology_module⟨m⟩(S, ℬ, k).carrier",
			},
			Conclusion: "smooth_singular_cohomology_pullback⟨n⟩(T, 𝒜, f, k, s) = " +
				"smooth_singular_cohomology_pullback⟨n⟩(T, 𝒜, g, k, s)",
		},
		"The prism triangulation gives a chain homotopy between the endpoint "+
			"maps. Its constituent maps compose a smooth simplex extension with "+
			"the smooth cylinder homotopy; dualizing gives the cochain homotopy."),
})}
