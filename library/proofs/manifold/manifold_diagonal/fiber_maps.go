// The diagonal map restricts to a fiber diffeomorphism with identity derivative at zero.

package manifold_diagonal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var DiagonalFiberMapZero = diagonalFiberMapZeroThm{family.Add(registry.ProofEntry{
	Name: "DiagonalFiberMapZero",
	Key:  "prop_fdfb10dfd300d752",
	Reading: "Only the retraction equation at x is read. The chart need not be compatible or " +
		"contain x: the chart reconstruction of the zero vector is the zero tangent either way.",
	Deps: []registry.EntryLike{
		diagonalFiberMapDef,
		tangent.TangentFromChartDef,
		DiagonalMapZeroSection,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀r:((num → real) → A). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A.",
		Hypotheses: []string{"r(i(x)) = x"},
		Conclusion: "«diagonal fiber map»(c)((λj:num. &0)) = x",
	},
		"TangentFromChartDef reconstructs the zero tangent from the zero coordinate "+
			"vector in either branch of its guard. DiagonalMapZeroSection sends its "+
			"total-space pair to (x,x), so diagonalFiberMapDef gives the result."),
})}

var DiagonalFiberMapZeroJacobian = diagonalFiberMapZeroJacobianThm{family.Add(registry.ProofEntry{
	Name: "DiagonalFiberMapZeroJacobian",
	Key:  "prop_b46bc80ea2d35f97",
	Reading: "The output chart is the same chart used to identify the tangent fiber. " +
		"The Jacobian claim is local near zero; it does not assume every ambient step lies " +
		"in U or every image point lies in c. The empty matrix has determinant one at n=0.",
	Deps: []registry.EntryLike{
		diagonalFiberMapDef,
		DiagonalFiberMapZero,
		tangent.EuclideanDifferentialCoordinate,
		tangent.TangentFromChart,
		tangent.DifferentialCompose,
		tangent.DifferentialIdentity,
		vec_smooth.JacobianChain,
		vec_smooth.PartialDerivativeLocal,
		determinant.DeterminantIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀U:set(num → real). " +
			"∀r:((num → real) → A). " +
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
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
		},
		Conclusion: "vec_jacobian_matrix⟨n, n⟩(snd(c) ∘ «diagonal fiber map»(c), (λj:num. &0)) = " +
			"matrix_identity(real_ring, n) ∧ " +
			"vec_jacobian_determinant⟨n⟩(snd(c) ∘ «diagonal fiber map»(c), (λj:num. &0)) = &1",
	},
		"Near zero the ambient tangent step remains in U and the retracted point remains in c. "+
			"EuclideanDifferentialCoordinate identifies the affine step derivative with di at x; "+
			"differentiating the retraction identity r after i gives the identity in chart c. The chain rule "+
			"therefore gives the identity coordinate matrix, and DeterminantIdentity gives determinant one."),
})}

var DiagonalFiberDiffeomorphism = diagonalFiberDiffeomorphismThm{family.Add(registry.ProofEntry{
	Name: "DiagonalFiberDiffeomorphism",
	Key:  "prop_fcba6a456386d5c3",
	Reading: "The supplied disk diffeomorphism fixes the precise δ and W; no compactness is needed " +
		"after those data are supplied. Its first-coordinate identity is essential for restricting its " +
		"inverse to the same fiber. Both open submanifold atlases are the actual ambient restrictions.",
	Deps: []registry.EntryLike{
		diagonalFiberMapDef,
		embeddedTangentFiberDiskDef,
		TangentFiberInclusionSmooth,
		tangent.TangentFromChart,
		tangent.TangentChartReconstruct,
		DiagonalFiberMapZero,
		tangent.TangentChartInverse,
		smooth_manifold.DiffeomorphismDef,
		smooth_manifold.SmoothMapRestrict,
		smooth_manifold.SmoothMapCompose,
		smooth_manifold.SmoothProductPair,
		smooth_manifold.SmoothMapConstant,
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
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"x ∈ fst(c)",
		},
		Conclusion: "«diagonal slice»(x, W) ∈ T ∧ " +
			"x ∈ «diagonal slice»(x, W) ∧ " +
			"image(«diagonal fiber map»(c), «diagonal fiber disk»(c)) = «diagonal slice»(x, W) ∧ " +
			"smooth_manifold_diffeomorphism⟨n⟩(subtopology(euclidean_topology(n), «diagonal fiber disk»(c)), " +
			"    euclidean_atlas(«diagonal fiber disk»(c)), " +
			"    subtopology(T, «diagonal slice»(x, W)), " +
			"    open_submanifold_atlas⟨n⟩(T, 𝒜, «diagonal slice»(x, W)), " +
			"    «diagonal fiber map»(c))",
	},
		"The first component of the diagonal map is the base point, so its bijection restricts "+
			"to a bijection between the coordinate fiber disk and the slice W at x. "+
			"TangentFiberInclusionSmooth and the forward diagonal map give smoothness; the inverse "+
			"on the slice is y↦snd(inverse_on(D,Φ,(x,y)))(c), smooth in lifted tangent coordinates. "+
			"The slice is open by the product topology, and DiagonalFiberMapZero supplies x in it."),
})}
