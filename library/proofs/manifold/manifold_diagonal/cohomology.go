// The two projections of a tangent-disk diagonal neighbourhood induce the same cohomology pullback.

package manifold_diagonal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

var DiagonalNeighbourhoodCohomology = diagonalNeighbourhoodCohomologyThm{family.Add(registry.ProofEntry{
	Name: "DiagonalNeighbourhoodCohomology",
	Key:  "prop_f54f08ca7b9f9ee7",
	Reading: "The equality uses the actual restricted product atlas of the " +
		"chosen neighbourhood W. It is only an equality on cohomology carriers, and " +
		"the same δ,W and retraction data as the geometric construction are retained.",
	Deps: []registry.EntryLike{
		DiagonalHomotopy,
		de_rham.HomotopyInvariance,
		smooth_manifold.DiffeomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀U:set(num → real). " +
			"∀r:((num → real) → A). " +
			"∀δ:real. " +
			"∀W:set(prod(A, A)). " +
			"∀k:num. " +
			"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"U ∈ euclidean_topology(N)",
			"image(i, ⋃T) ⊆ U",
			"smooth_manifold_map⟨N, n⟩(subtopology(euclidean_topology(N), U), euclidean_atlas(U), T, 𝒜, r)",
			"∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x",
			"&0 < δ",
			"W ∈ product_topology(T, T)",
			"smooth_manifold_diffeomorphism⟨2 * n⟩( " +
				"    subtopology(tangent_topology⟨n⟩(T, 𝒜), embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ)), " +
				"    open_submanifold_atlas⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), " +
				"        tangent_atlas⟨n⟩(T, 𝒜), " +
				"        embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ)), " +
				"    subtopology(product_topology(T, T), W), " +
				"    open_submanifold_atlas⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), W), " +
				"    diagonal_neighbourhood_map⟨n, N⟩(T, 𝒜, i, r))",
			"∀p:prod(A, prod(set(A), A → num → real) → num → real). ∀t:(num → real). " +
				"    p ∈ embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ) ∧ " +
				"    t ∈ {τ:num → real | vec⟨1⟩(τ) ∧ -&1 < τ(0) ∧ τ(0) < &2} ⇒ " +
				"    (λj:num. " +
				"        i(fst(p), j) + " +
				"        t(0) * manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(fst(p), snd(p))(j)) ∈ " +
				"    U",
			"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier",
		},
		Conclusion: "de_rham_pullback⟨2 * n, n⟩(subtopology(product_topology(T, T), W), " +
			"    open_submanifold_atlas⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), W), " +
			"    T, " +
			"    𝒜, " +
			"    k, " +
			"    fst)(s) = " +
			"de_rham_pullback⟨2 * n, n⟩(subtopology(product_topology(T, T), W), " +
			"    open_submanifold_atlas⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), W), " +
			"    T, " +
			"    𝒜, " +
			"    k, " +
			"    snd)(s)",
	},
		"DiagonalHomotopy gives a smooth homotopy on the product with the open strip (−1,2), "+
			"with endpoints the two projections. Apply HomotopyInvariance to the genuine degree-k "+
			"class s; the strip is open and contains every normalized time point in [0,1]."),
})}
