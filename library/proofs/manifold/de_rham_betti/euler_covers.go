// The finite Mayer–Vietoris dimension sum gives Euler additivity for two-open covers.

package de_rham_betti

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

var EulerMayerVietoris = eulerMayerVietorisThm{family.Add(registry.ProofEntry{
	Name: "EulerMayerVietoris",
	Key:  "prop_331a79f069ce05b5",
	Reading: "The short-exact cover complex is supplied explicitly; this does not assume a general " +
		"noncompact partition theorem. Finiteness of both opens and their intersection is essential. The " +
		"degree-zero start and vanishing tail eliminate the end terms without using a negative degree.",
	Deps: []registry.EntryLike{
		EulerDef,
		BettiDef,
		de_rham_cover.MayerVietorisMaps,
		de_rham_cover.MayerVietorisExact,
		de_rham_cover.MayerVietorisStart,
		de_rham.CohomologyAboveDimension,
		de_rham.CohomologyModule,
		smooth_manifold.OpenSubmanifold,
		module_dimension.DimProduct,
		module_dimension.RankNullity,
		module_dimension.ImageDim,
		module_dimension.SubmoduleDim,
		module_dimension.DimFiniteOfKernelAndImage,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"«cover exact»",
			"∀q:num. " +
				"    finite_dimensional(real_ring, «open cohomology»(U, q)) ∧ " +
				"    finite_dimensional(real_ring, «open cohomology»(V, q))",
			"∀q:num. finite_dimensional(real_ring, «open cohomology»(U ∩ V, q))",
		},
		Conclusion: "(∀q:num. finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, q))) ∧ " +
			"de_rham_euler⟨n⟩(T, 𝒜) + " +
			"de_rham_euler⟨n⟩(subtopology(T, U ∩ V), open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V)) = " +
			"de_rham_euler⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U)) + " +
			"de_rham_euler⟨n⟩(subtopology(T, V), open_submanifold_atlas⟨n⟩(T, 𝒜, V))",
	},
		"In degree zero the restriction map is injective into a finite-dimensional product. In "+
			"each higher degree its kernel is the image of the preceding connecting map, and its "+
			"image lies in a finite-dimensional product, giving finiteness of the middle cohomology. "+
			"Apply rank-nullity along the long exact sequence: internal image dimensions cancel in "+
			"the alternating sum, the start is injective, and cohomology vanishes above n."),
})}

var EulerDisjointOpenUnion = eulerDisjointOpenUnionThm{family.Add(registry.ProofEntry{
	Name: "EulerDisjointOpenUnion",
	Key:  "prop_2dd52a8428a40b48",
	Reading: "These are disjoint open submanifolds of one fixed-dimensional " +
		"manifold. No orientation or compactness is required, but both pieces must " +
		"have finite-dimensional cohomology. Empty pieces are allowed. The normalized " +
		"indicators of these clopen pieces have support inside their respective opens.",
	Deps: []registry.EntryLike{
		EulerMayerVietoris,
		EulerEmpty,
		de_rham.EmptyCohomology,
		de_rham_cover.MayerVietoris,
		smooth_manifold.FunctionLocal,
		smooth_manifold.FunctionConstant,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"U ∩ V = ∅",
			"∀q:num. " +
				"    finite_dimensional(real_ring, «open cohomology»(U, q)) ∧ " +
				"    finite_dimensional(real_ring, «open cohomology»(V, q))",
		},
		Conclusion: "(∀q:num. finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, q))) ∧ " +
			"de_rham_euler⟨n⟩(T, 𝒜) = " +
			"de_rham_euler⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U)) + " +
			"de_rham_euler⟨n⟩(subtopology(T, V), open_submanifold_atlas⟨n⟩(T, 𝒜, V))",
	},
		"Each member of the disjoint open cover is also closed in the manifold. Its indicator "+
			"is a normalized smooth function with support in that open, and the two indicators "+
			"sum to one. MayerVietoris supplies the cover exactness; the intersection has zero "+
			"cohomology by EmptyCohomology, so EulerMayerVietoris and EulerEmpty give additivity."),
})}
