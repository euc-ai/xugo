// Scaling the affine tangent step gives a smooth homotopy between the neighbourhood projections.

package manifold_diagonal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var DiagonalHomotopy = diagonalHomotopyThm{family.Add(registry.ProofEntry{
	Name: "DiagonalHomotopy",
	Key:  "prop_91b0661119de7f98",
	Reading: "Once the disk diffeomorphism and strip containment are supplied, no " +
		"compactness is needed. Endpoint equations are only on W, and the time domain is an open " +
		"Euclidean one-set containing the entire closed unit interval. The inverse is evaluated " +
		"only on its actual target W. The endpoints use r after i equal to the identity and the " +
		"diagonal map after its inverse equal to the identity; no identity i after r is required.",
	Deps: []registry.EntryLike{
		diagonalHomotopyDef,
		diagonalMapDef,
		tangent.EuclideanDifferentialBundleSmooth,
		tangent.TangentProjection,
		smooth_manifold.DiffeomorphismDef,
		smooth_manifold.SmoothProductProjections,
		smooth_manifold.SmoothProductPair,
		smooth_manifold.SmoothMapCompose,
		smooth_manifold.SmoothMapRestrict,
		smooth_manifold.SmoothMapEuclidean,
		vec_smooth.SmoothAdd,
		vec_smooth.SmoothMul,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀U:set(num → real). " +
			"∀r:((num → real) → A). " +
			"∀δ:real. " +
			"∀W:set(prod(A, A)).",
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
			"smooth_manifold_diffeomorphism⟨2 * n⟩(«disk topology»(δ), " +
				"    «disk atlas»(δ), " +
				"    «diagonal target topology»(W), " +
				"    «diagonal target atlas»(W), " +
				"    diagonal_neighbourhood_map⟨n, N⟩(T, 𝒜, i, r))",
			"∀p:prod(A, prod(set(A), A → num → real) → num → real). ∀t:(num → real). " +
				"    p ∈ embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ) ∧ t ∈ «diagonal time strip» ⇒ " +
				"    (λj:num. " +
				"        i(fst(p), j) + " +
				"        t(0) * manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(fst(p), snd(p))(j)) ∈ " +
				"    U",
		},
		Conclusion: "smooth_manifold_map⟨2 * n + 1, n⟩(product_topology(«diagonal target topology»(W), " +
			"        subtopology(euclidean_topology(1), «diagonal time strip»)), " +
			"    smooth_product_atlas⟨2 * n, 1⟩(«diagonal target atlas»(W), " +
			"        euclidean_atlas(«diagonal time strip»)), " +
			"    T, " +
			"    𝒜, " +
			"    diagonal_neighbourhood_homotopy⟨n, N⟩(T, 𝒜, i, r, δ)) ∧ " +
			"(∀z:prod(A, A). " +
			"    z ∈ W ⇒ " +
			"    diagonal_neighbourhood_homotopy⟨n, N⟩(T, 𝒜, i, r, δ)((z, (λj:num. &0))) = fst(z) ∧ " +
			"    diagonal_neighbourhood_homotopy⟨n, N⟩(T, 𝒜, i, r, δ)((z, (λj:num. COND(j = 0, &1, &0)))) = " +
			"    snd(z))",
	},
		"Compose the inverse diagonal diffeomorphism with the smooth base projection and "+
			"Euclidean differential, then form the affine step using the time coordinate. The "+
			"explicit strip containment allows smooth corestriction into U and composition "+
			"with r. At time zero the retraction identity gives the first projection, and at "+
			"time one the inverse equation for the diagonal map gives the second."),
})}
