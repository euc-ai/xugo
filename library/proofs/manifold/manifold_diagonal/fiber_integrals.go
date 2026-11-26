// Diagonal fiber maps preserve orientation and the integral of forms supported inside their image.

package manifold_diagonal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var DiagonalFiberOrientedDiffeomorphism = diagonalFiberOrientedDiffeomorphismThm{family.Add(registry.ProofEntry{
	Name: "DiagonalFiberOrientedDiffeomorphism",
	Key:  "prop_1e541ffe64d53519",
	Reading: "The chosen base chart must be positive. The fiber disk is connected and " +
		"the map is a diffeomorphism throughout it, so the determinant cannot change sign " +
		"from its value one at zero. The target positive open atlas retains the orientation " +
		"while sharing the ordinary open atlas's smooth compatibility class. The conclusion " +
		"uses the given δ and W and does not orient the total product manifold.",
	Deps: []registry.EntryLike{
		DiagonalFiberDiffeomorphism,
		EmbeddedTangentFiberDiskGeometry,
		DiagonalFiberMapZeroJacobian,
		DiagonalFiberMapZero,
		form_integral.OrientedEuclidean,
		form_integral.OrientedOpenSubmanifold,
		form_integral.PositiveChartRestrict,
		form_integral.DiffeomorphismOrientationAtPoint,
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
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A.",
		Hypotheses: []string{
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"U ∈ euclidean_topology(N)",
			"image(i, ⋃T) ⊆ U",
			"smooth_manifold_map⟨N, n⟩(subtopology(euclidean_topology(N), U), euclidean_atlas(U), T, 𝒜, r)",
			"∀z:A. z ∈ ⋃T ⇒ r(i(z)) = z",
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
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
		},
		Conclusion: "oriented_diffeomorphism⟨n⟩( " +
			"    subtopology(euclidean_topology(n), «diagonal fiber disk»(c)), " +
			"    euclidean_atlas(«diagonal fiber disk»(c)), " +
			"    subtopology(T, «diagonal slice»(x, W)), " +
			"    oriented_open_atlas⟨n⟩(T, 𝒜, «diagonal slice»(x, W)), " +
			"    «diagonal fiber map»(c))",
	},
		"DiagonalFiberDiffeomorphism gives the smooth diffeomorphism, and OrientedOpenSubmanifold "+
			"supplies the positive target atlas. EmbeddedTangentFiberDiskGeometry gives a connected "+
			"source containing zero, while DiagonalFiberMapZeroJacobian has positive determinant "+
			"there in the chosen positive chart. Apply DiffeomorphismOrientationAtPoint, using a "+
			"target-chart restriction near x if the entire fiber image does not lie in c."),
})}

var DiagonalFiberIntegral = diagonalFiberIntegralThm{family.Add(registry.ProofEntry{
	Name: "DiagonalFiberIntegral",
	Key:  "prop_f7f2e2b5fd5670c4",
	Reading: "The entire compact support must lie in the actual slice W at x. This support includes " +
		"its ambient closure and is then compact also in the slice. A fiber map need not be proper as a " +
		"map into the whole manifold; compact pullback support follows here from the slice " +
		"diffeomorphism and this containment. The equality has positive sign and includes dimension zero.",
	Deps: []registry.EntryLike{
		DiagonalFiberOrientedDiffeomorphism,
		form_integral.IntegralRestriction,
		form_integral.IntegralDiffeomorphism,
		form_integral.DiffeomorphismPullbackSupport,
		form_integral.OrientedOpenSubmanifold,
		differential_form.PullbackCompose,
		differential_form.PullbackOpenInclusion,
		differential_form.SupportRestrict,
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
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_embedding⟨n, N⟩(T, " +
				"    𝒜, " +
				"    euclidean_topology(N), " +
				"    euclidean_atlas({y:num → real | vec⟨N⟩(y)}), " +
				"    i)",
			"U ∈ euclidean_topology(N)",
			"image(i, ⋃T) ⊆ U",
			"smooth_manifold_map⟨N, n⟩(subtopology(euclidean_topology(N), U), euclidean_atlas(U), T, 𝒜, r)",
			"∀z:A. z ∈ ⋃T ⇒ r(i(z)) = z",
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
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ «diagonal slice»(x, W)",
		},
		Conclusion: "compact_in(subtopology(euclidean_topology(n), «diagonal fiber disk»(c)), " +
			"    manifold_form_support⟨n⟩(subtopology(euclidean_topology(n), «diagonal fiber disk»(c)), " +
			"        euclidean_atlas(«diagonal fiber disk»(c)), " +
			"        manifold_form_pullback⟨n, n⟩( " +
			"            subtopology(euclidean_topology(n), «diagonal fiber disk»(c)), " +
			"            euclidean_atlas(«diagonal fiber disk»(c)), " +
			"            T, " +
			"            𝒜, " +
			"            n, " +
			"            «diagonal fiber map»(c), " +
			"            ω))) ∧ " +
			"manifold_form_integral⟨n⟩(subtopology(euclidean_topology(n), «diagonal fiber disk»(c)), " +
			"    euclidean_atlas(«diagonal fiber disk»(c)), " +
			"    manifold_form_pullback⟨n, n⟩(subtopology(euclidean_topology(n), «diagonal fiber disk»(c)), " +
			"        euclidean_atlas(«diagonal fiber disk»(c)), " +
			"        T, " +
			"        𝒜, " +
			"        n, " +
			"        «diagonal fiber map»(c), " +
			"        ω)) = " +
			"manifold_form_integral⟨n⟩(T, 𝒜, ω)",
	},
		"Use IntegralRestriction to move the compactly supported target form to the slice. "+
			"DiagonalFiberOrientedDiffeomorphism and IntegralDiffeomorphism identify its integral "+
			"with the fiber-coordinate pullback integral, and DiffeomorphismPullbackSupport gives "+
			"compact pullback support. PullbackCompose with PullbackOpenInclusion identifies this "+
			"restricted pullback with the displayed pullback from the whole manifold."),
})}
