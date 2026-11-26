// Multiplication by a global class commutes with the cover connecting map with the degree sign fixed by its side.

package de_rham_kunneth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

var ConnectingWedgeClassRight = connectingWedgeClassRightThm{family.Add(registry.ProofEntry{
	Name: "ConnectingWedgeClassRight",
	Key:  "prop_c1d630e62101116d",
	Reading: "The cover difference is U-minus-V. With the global class on the " +
		"right, the connecting map commutes with multiplication without an extra sign.",
	Deps: []registry.EntryLike{
		de_rham_product.WedgeClass,
		de_rham.ClassRepresentative,
		de_rham.PullbackClass,
		de_rham_cover.MayerVietorisMaps,
		differential_form.PullbackOpenInclusion,
		smooth_manifold.SmoothOpenInclusion,
		de_rham_cover.ConnectingWedgeRight,
	},
	Build: family.Card(Statement{
		Binders: "∀n k p:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀s t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"«cover exact»",
			"s ∈ «open cohomology»(U ∩ V, k).carrier",
			"t ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier",
		},
		Conclusion: "de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k + p, " +
			"    de_rham_wedge⟨n⟩(subtopology(T, U ∩ V), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
			"        k, " +
			"        p, " +
			"        s, " +
			"        «global class restriction»(U ∩ V, p, t))) = " +
			"de_rham_wedge⟨n⟩(T, 𝒜, k + 1, p, de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k, s), t)",
	},
		"Choose closed representatives of s and t and of the connecting image of s, whose "+
			"carrier membership follows from MayerVietorisMaps. Identify restriction pullback "+
			"with normalized form restriction, then apply ConnectingWedgeRight and WedgeClass."),
})}

var ConnectingWedgeClassLeft = connectingWedgeClassLeftThm{family.Add(registry.ProofEntry{
	Name: "ConnectingWedgeClassLeft",
	Key:  "prop_241797d441a08ffe",
	Reading: "The sign is the degree p of the fixed global class, not the degree k " +
		"of the intersection class. The connecting map raises k by one, including k=0.",
	Deps: []registry.EntryLike{
		de_rham_product.WedgeClass,
		de_rham.ClassRepresentative,
		de_rham.PullbackClass,
		de_rham_cover.MayerVietorisMaps,
		differential_form.PullbackOpenInclusion,
		smooth_manifold.SmoothOpenInclusion,
		de_rham_cover.ConnectingWedgeLeft,
		de_rham.ClassScale,
	},
	Build: family.Card(Statement{
		Binders: "∀n k p:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀s t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"«cover exact»",
			"s ∈ «open cohomology»(U ∩ V, k).carrier",
			"t ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier",
		},
		Conclusion: "de_rham_connecting⟨n⟩(T, 𝒜, U, V)(p + k, " +
			"    de_rham_wedge⟨n⟩(subtopology(T, U ∩ V), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
			"        p, " +
			"        k, " +
			"        «global class restriction»(U ∩ V, p, t), " +
			"        s)) = " +
			"de_rham_cohomology_module⟨n⟩(T, 𝒜, p + k + 1).smul((-&1)^p, " +
			"    de_rham_wedge⟨n⟩(T, 𝒜, p, k + 1, t, de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k, s)))",
	},
		"Choose closed representatives as for right multiplication and apply "+
			"ConnectingWedgeLeft. WedgeClass identifies both quotient products and "+
			"ClassScale moves the factor (-1)^p onto the target cohomology class."),
})}
