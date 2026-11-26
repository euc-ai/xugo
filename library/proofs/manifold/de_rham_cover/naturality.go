// Pullback compares the cover sequences, while multiplication by a closed form controls the degree sign.

package de_rham_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

var CoverPullbackSquares = coverPullbackSquaresThm{family.Add(registry.ProofEntry{
	Name: "CoverPullbackSquares",
	Key:  "prop_abb4928358f8c70f",
	Reading: "Only image containment is required: the designated source opens need not be the " +
		"full inverse images of the target opens, and neither pair need cover its manifold. " +
		"Equalities are on degree carriers because normalized forms depend on their ambient open atlas.",
	Deps: []registry.EntryLike{
		CoverCochain,
		de_rham.PullbackCochain,
		CoverRestrictionDef,
		CoverDifferenceDef,
		differential_form.PullbackCompose,
		differential_form.PullbackOpenInclusion,
		differential_form.PullbackLinear,
		smooth_manifold.SmoothMapRestrict,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀U V:set(A). " +
			"∀U' V':set(B). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"U ∈ T",
			"V ∈ T",
			"U' ∈ S",
			"V' ∈ S",
			"image(f, U) ⊆ U'",
			"image(f, V) ⊆ V'",
		},
		Conclusion: "cochain_map(real_ring, " +
			"    de_rham_cover_complex⟨m⟩(S, ℬ, U', V'), " +
			"    de_rham_cover_complex⟨n⟩(T, 𝒜, U, V), " +
			"    (λq:num. " +
			"    λz:prod(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real, " +
			"            prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"        (manifold_form_pullback⟨n, m⟩(subtopology(T, U), " +
			"                open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"                subtopology(S, U'), " +
			"                open_submanifold_atlas⟨m⟩(S, ℬ, U'), " +
			"                q, " +
			"                f)(fst(z)), " +
			"            manifold_form_pullback⟨n, m⟩(subtopology(T, V), " +
			"                open_submanifold_atlas⟨n⟩(T, 𝒜, V), " +
			"                subtopology(S, V'), " +
			"                open_submanifold_atlas⟨m⟩(S, ℬ, V'), " +
			"                q, " +
			"                f)(snd(z))))) ∧ " +
			"(∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"    ω ∈ de_rham_complex⟨m⟩(S, ℬ).terms(k) ⇒ " +
			"    (λq:num. " +
			"    λz:prod(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real, " +
			"            prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"        (manifold_form_pullback⟨n, m⟩(subtopology(T, U), " +
			"                open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"                subtopology(S, U'), " +
			"                open_submanifold_atlas⟨m⟩(S, ℬ, U'), " +
			"                q, " +
			"                f)(fst(z)), " +
			"            manifold_form_pullback⟨n, m⟩(subtopology(T, V), " +
			"                open_submanifold_atlas⟨n⟩(T, 𝒜, V), " +
			"                subtopology(S, V'), " +
			"                open_submanifold_atlas⟨m⟩(S, ℬ, V'), " +
			"                q, " +
			"                f)(snd(z))))(k, de_rham_cover_restriction⟨m⟩(S, ℬ, U', V')(ω)) = " +
			"    de_rham_cover_restriction⟨n⟩(T, 𝒜, U, V)( " +
			"        manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)(ω))) ∧ " +
			"(∀z:prod(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real, " +
			"        prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"    z ∈ de_rham_cover_complex⟨m⟩(S, ℬ, U', V').terms(k) ⇒ " +
			"    manifold_form_pullback⟨n, m⟩(subtopology(T, U ∩ V), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
			"        subtopology(S, U' ∩ V'), " +
			"        open_submanifold_atlas⟨m⟩(S, ℬ, U' ∩ V'), " +
			"        k, " +
			"        f)(de_rham_cover_difference⟨m⟩(S, ℬ, U', V')(z)) = " +
			"    de_rham_cover_difference⟨n⟩(T, 𝒜, U, V)((λq:num. " +
			"        λz:prod(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real, " +
			"                prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"            (manifold_form_pullback⟨n, m⟩(subtopology(T, U), " +
			"                    open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"                    subtopology(S, U'), " +
			"                    open_submanifold_atlas⟨m⟩(S, ℬ, U'), " +
			"                    q, " +
			"                    f)(fst(z)), " +
			"                manifold_form_pullback⟨n, m⟩(subtopology(T, V), " +
			"                    open_submanifold_atlas⟨n⟩(T, 𝒜, V), " +
			"                    subtopology(S, V'), " +
			"                    open_submanifold_atlas⟨m⟩(S, ℬ, V'), " +
			"                    q, " +
			"                    f)(snd(z))))(k, z)))",
	}, "Restrict f to each designated open and to their intersection. Pullback "+
		"composition with open inclusions identifies restriction after pullback with "+
		"pullback after restriction. Componentwise pullback is a cochain map; its "+
		"linearity makes the difference square commute with the same U-minus-V convention."),
})}

var ConnectingNaturality = connectingNaturalityThm{family.Add(registry.ProofEntry{
	Name: "ConnectingNaturality",
	Key:  "prop_f7f3e25ce3fb4046",
	Reading: "This is contravariant naturality, including restrictions and " +
		"projections. Both exact sequences are hypotheses; existence of unrelated " +
		"long exact sequences alone would not give this commuting square.",
	Deps: []registry.EntryLike{
		ConnectingDef,
		CoverPullbackSquares,
		de_rham.PullbackCochain,
		de_rham.PullbackDef,
		chain_complex.CoconnectingNaturality,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀U V:set(A). " +
			"∀U' V':set(B). " +
			"∀f:(A → B). " +
			"∀s:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"U ∈ T",
			"V ∈ T",
			"U' ∈ S",
			"V' ∈ S",
			"U ∪ V = ⋃T",
			"U' ∪ V' = ⋃S",
			"image(f, U) ⊆ U'",
			"image(f, V) ⊆ V'",
			"«cover exact»",
			"short_exact_cochain_complexes(real_ring, " +
				"    de_rham_complex⟨m⟩(S, ℬ), " +
				"    de_rham_cover_complex⟨m⟩(S, ℬ, U', V'), " +
				"    de_rham_complex⟨m⟩(subtopology(S, U' ∩ V'), open_submanifold_atlas⟨m⟩(S, ℬ, U' ∩ V')), " +
				"    (λq:num. de_rham_cover_restriction⟨m⟩(S, ℬ, U', V')), " +
				"    (λq:num. de_rham_cover_difference⟨m⟩(S, ℬ, U', V')))",
			"s ∈ " +
				"de_rham_cohomology_module⟨m⟩(subtopology(S, U' ∩ V'), " +
				"    open_submanifold_atlas⟨m⟩(S, ℬ, U' ∩ V'), " +
				"    k).carrier",
		},
		Conclusion: "de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k + 1, f)( " +
			"    de_rham_connecting⟨m⟩(S, ℬ, U', V')(k, s)) = " +
			"de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k, " +
			"    de_rham_pullback⟨n, m⟩(subtopology(T, U ∩ V), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
			"        subtopology(S, U' ∩ V'), " +
			"        open_submanifold_atlas⟨m⟩(S, ℬ, U' ∩ V'), " +
			"        k, " +
			"        f)(s))",
	},
		"Use the cochain pullbacks and the two carrierwise commuting squares of "+
			"CoverPullbackSquares as a morphism of the short exact sequences. Generic coconnecting "+
			"naturality gives the square at degree k+1, with the intersection pullback at degree k."),
})}

var ConnectingWedgeRight = connectingWedgeRightThm{family.Add(registry.ProofEntry{
	Name: "ConnectingWedgeRight",
	Key:  "prop_801aeecbc3068763",
	Reading: "This is the sign-free square used for a product-basis map α ↦ π₁*α∧π₂*γ. " +
		"The product with γ stays on the right, and no negative-degree complex is used.",
	Deps: []registry.EntryLike{
		ConnectingClass,
		de_rham.ClassEqualSucc,
		differential_form.WedgeForm,
		differential_form.RestrictionWedge,
		differential_form.ExteriorDerivativeLeibniz,
		chain_complex.CocycleLiftPullback,
	},
	Build: family.Card(Statement{
		Binders: "∀n k p:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀γ ω η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"«cover exact»",
			"γ ∈ de_rham_complex⟨n⟩(T, 𝒜).terms(p)",
			"de_rham_complex⟨n⟩(T, 𝒜).d(p)(γ) = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"ω ∈ «open complex»(U ∩ V).terms(k)",
			"«open complex»(U ∩ V).d(k)(ω) = «open complex»(U ∩ V).zero",
			"η ∈ de_rham_complex⟨n⟩(T, 𝒜).terms(k + 1)",
			"de_rham_complex⟨n⟩(T, 𝒜).d(k + 1)(η) = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k, " +
				"    de_rham_class⟨n⟩(subtopology(T, U ∩ V), open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), k, ω)) = " +
				"de_rham_class⟨n⟩(T, 𝒜, k + 1, η)",
		},
		Conclusion: "de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k + p, " +
			"    de_rham_class⟨n⟩(subtopology(T, U ∩ V), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
			"        k + p, " +
			"        manifold_form_wedge⟨n⟩(subtopology(T, U ∩ V), " +
			"            open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
			"            k, " +
			"            p, " +
			"            ω, " +
			"            manifold_form_restrict⟨n⟩(T, 𝒜, U ∩ V, γ)))) = " +
			"de_rham_class⟨n⟩(T, 𝒜, k + 1 + p, manifold_form_wedge⟨n⟩(T, 𝒜, k + 1, p, η, γ))",
	},
		"Choose a lift of ω and glue its derivative to a representative η₀ of δ[ω]. "+
			"Right multiplication of the lift by γ has derivative d(lift)∧γ because "+
			"dγ=0, so ConnectingClass gives [η₀∧γ]. Since η−η₀ is exact in the positive "+
			"degree k+1, the Leibniz rule shows its right product with γ is exact too."),
})}

var ConnectingWedgeLeft = connectingWedgeLeftThm{family.Add(registry.ProofEntry{
	Name: "ConnectingWedgeLeft",
	Key:  "prop_d801af12978cb599",
	Reading: "The factor (-1)^p belongs to the connecting square for left " +
		"multiplication. It is not present for right multiplication; using one " +
		"convention consistently gives the commuting ladder required by the five lemma.",
	Deps: []registry.EntryLike{
		ConnectingClass,
		de_rham.ClassEqualSucc,
		differential_form.WedgeForm,
		differential_form.RestrictionWedge,
		differential_form.ExteriorDerivativeLeibniz,
		chain_complex.CocycleLiftPullback,
	},
	Build: family.Card(Statement{
		Binders: "∀n k p:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀γ ω η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"«cover exact»",
			"γ ∈ de_rham_complex⟨n⟩(T, 𝒜).terms(p)",
			"de_rham_complex⟨n⟩(T, 𝒜).d(p)(γ) = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"ω ∈ «open complex»(U ∩ V).terms(k)",
			"«open complex»(U ∩ V).d(k)(ω) = «open complex»(U ∩ V).zero",
			"η ∈ de_rham_complex⟨n⟩(T, 𝒜).terms(k + 1)",
			"de_rham_complex⟨n⟩(T, 𝒜).d(k + 1)(η) = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"de_rham_connecting⟨n⟩(T, 𝒜, U, V)(k, " +
				"    de_rham_class⟨n⟩(subtopology(T, U ∩ V), open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), k, ω)) = " +
				"de_rham_class⟨n⟩(T, 𝒜, k + 1, η)",
		},
		Conclusion: "de_rham_connecting⟨n⟩(T, 𝒜, U, V)(p + k, " +
			"    de_rham_class⟨n⟩(subtopology(T, U ∩ V), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
			"        p + k, " +
			"        manifold_form_wedge⟨n⟩(subtopology(T, U ∩ V), " +
			"            open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
			"            p, " +
			"            k, " +
			"            manifold_form_restrict⟨n⟩(T, 𝒜, U ∩ V, γ), " +
			"            ω))) = " +
			"de_rham_cohomology_module⟨n⟩(T, 𝒜, p + (k + 1)).smul((-&1) ^ p, " +
			"    de_rham_class⟨n⟩(T, 𝒜, p + (k + 1), manifold_form_wedge⟨n⟩(T, 𝒜, p, k + 1, γ, η)))",
	},
		"Multiply a lift of ω on the left by the closed p-form γ. The Leibniz rule gives "+
			"d(γ∧lift)=(-1)^p γ∧d(lift), fixing the connecting representative and its sign. Changing that "+
			"representative by an exact form changes its product with γ by an exact form, again by Leibniz."),
})}
