// A compact embedded manifold has a uniform tangent-disk model of a diagonal neighbourhood.

package manifold_diagonal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/tangent"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var DiagonalMapZeroSection = diagonalMapZeroSectionThm{family.Add(registry.ProofEntry{
	Name: "DiagonalMapZeroSection",
	Key:  "prop_57e1fb89fc8d5f43",
	Reading: "An identity of the definitions: only the retraction equation " +
		"at x is read. The Euclidean differential of the zero tangent is the " +
		"zero vector whether or not x lies in the manifold or i is smooth.",
	Deps: []registry.EntryLike{
		diagonalMapDef,
		tangent.EuclideanDifferentialDef,
		tangent.DifferentialDef,
		tangent.ZeroSectionDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀r:((num → real) → A). " +
			"∀x:A.",
		Hypotheses: []string{"r(i(x)) = x"},
		Conclusion: "diagonal_neighbourhood_map⟨n, N⟩(T, 𝒜, i, r)(tangent_zero_section(x)) = (x, x)",
	},
		"DifferentialDef evaluates a Jacobian on the zero coordinate vector or returns zero "+
			"outright, so the Euclidean differential of the zero tangent is zero. diagonalMapDef "+
			"then reduces the second coordinate to r(i(x)), which is x by the retraction equation."),
})}

var DiagonalMapLocalDiffeomorphism = diagonalMapLocalDiffeomorphismThm{family.Add(registry.ProofEntry{
	Name: "DiagonalMapLocalDiffeomorphism",
	Key:  "prop_1ce83d9f532ee1e1",
	Reading: "No compactness is required for the local assertion. Both tangent and product " +
		"manifolds have dimension 2n; the zero-dimensional block matrix is the empty invertible matrix.",
	Deps: []registry.EntryLike{
		diagonalMapDef,
		DiagonalMapZeroSection,
		tangent.EuclideanDifferentialCoordinate,
		tangent.EuclideanDifferentialBundleSmooth,
		tangent.DifferentialCompose,
		tangent.DifferentialIdentity,
		tangent.TangentChartInverse,
		tangent.TangentChartTransition,
		smooth_manifold.ProductCompatibleChart,
		smooth_manifold.DiffeomorphismDef,
		vec_smooth.SmoothInverseFunction,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀U:set(num → real). " +
			"∀r:((num → real) → A). " +
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
			"∀y:A. y ∈ ⋃T ⇒ r(i(y)) = y",
			"x ∈ ⋃T",
		},
		Conclusion: "∃O:set(prod(A, prod(set(A), A → num → real) → num → real)). ∃V:set(prod(A, A)). " +
			"    O ∈ tangent_topology⟨n⟩(T, 𝒜) ∧ " +
			"    V ∈ product_topology(T, T) ∧ " +
			"    tangent_zero_section(x) ∈ O ∧ " +
			"    smooth_manifold_diffeomorphism⟨2 * n⟩(subtopology(tangent_topology⟨n⟩(T, 𝒜), O), " +
			"        open_submanifold_atlas⟨2 * n⟩(tangent_topology⟨n⟩(T, 𝒜), tangent_atlas⟨n⟩(T, 𝒜), O), " +
			"        subtopology(product_topology(T, T), V), " +
			"        open_submanifold_atlas⟨2 * n⟩(product_topology(T, T), " +
			"            smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
			"            V), " +
			"        diagonal_neighbourhood_map⟨n, N⟩(T, 𝒜, i, r))",
	},
		"In a lifted source chart and the paired target chart at (x,x), differentiate the diagonal map "+
			"at the zero tangent. The retraction identity gives dr after di equal to the identity, so the "+
			"block derivative is (a,b)↦(a,a+b), hence invertible. SmoothInverseFunction gives the local "+
			"inverse after restricting to ambient steps in U; transport it through the compatible charts."),
})}

var DiagonalNeighbourhood = diagonalNeighbourhoodThm{family.Add(registry.ProofEntry{
	Name: "DiagonalNeighbourhood",
	Key:  "prop_afaf1c805663faea",
	Reading: "The same positive radius gives the diffeomorphism and the full open time " +
		"strip (−1,2). Lifted-chart product neighbourhoods and a local lower bound for the " +
		"embedding differential put every sufficiently small fiber over each base patch in " +
		"one injective local inverse domain. A finite base cover gives one radius; equal " +
		"images have equal bases and hence lie in a common inverse domain. Shrinking twice " +
		"the radius into a uniform ambient neighbourhood of the compact image gives the time " +
		"strip. No identity i after r is used; empty bases give empty disks and neighbourhoods.",
	Deps: []registry.EntryLike{
		DiagonalMapLocalDiffeomorphism,
		DiagonalMapZeroSection,
		EmbeddedTangentDiskOpen,
		EmbeddedTangentDiskZeroSection,
		CompactZeroSectionDisk,
		tangent.EuclideanDifferentialCoordinate,
		smooth_manifold.InjectiveImmersionDiffeomorphism,
		smooth_manifold.ImmersionLocal,
		continuous.ImageCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀i:(A → num → real). " +
			"∀U:set(num → real). " +
			"∀r:((num → real) → A).",
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
			"compact_in(T, ⋃T)",
		},
		Conclusion: "∃δ:real. ∃W:set(prod(A, A)). " +
			"    &0 < δ ∧ " +
			"    W ∈ product_topology(T, T) ∧ " +
			"    image((λx:A. (x, x)), ⋃T) ⊆ W ∧ " +
			"    image(diagonal_neighbourhood_map⟨n, N⟩(T, 𝒜, i, r), " +
			"        embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ)) = " +
			"    W ∧ " +
			"    smooth_manifold_diffeomorphism⟨2 * n⟩(«disk topology»(δ), " +
			"        «disk atlas»(δ), " +
			"        «diagonal target topology»(W), " +
			"        «diagonal target atlas»(W), " +
			"        diagonal_neighbourhood_map⟨n, N⟩(T, 𝒜, i, r)) ∧ " +
			"    (∀p:prod(A, prod(set(A), A → num → real) → num → real). ∀t:(num → real). " +
			"        p ∈ embedded_tangent_disk⟨n, N⟩(T, 𝒜, i, δ) ∧ t ∈ «diagonal time strip» ⇒ " +
			"        (λj:num. " +
			"            i(fst(p), j) + " +
			"            t(0) * manifold_euclidean_differential⟨n, N⟩(T, 𝒜, i)(fst(p), snd(p))(j)) ∈ " +
			"        U)",
	},
		"Use DiagonalMapLocalDiffeomorphism on the compact zero section and shrink to a uniform "+
			"embedded tangent radius. The first coordinate fixes the base point, and finitely many base "+
			"patches put each sufficiently small fiber in a common local inverse neighbourhood, giving "+
			"injectivity; the local inverses then glue on the open image. Shrink the radius again so "+
			"every step i(x)+t di_x(v), for −1<t<2, remains in the given U, using compactness of i(M)."),
})}
