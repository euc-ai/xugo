// Local agreement glues forms; a subordinate pair of scalar weights supplies the final surjection.

package de_rham_cover

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var CoverGluing = coverGluingThm{family.Add(registry.ProofEntry{
	Name: "CoverGluing",
	Key:  "prop_9720562efbcead06",
	Reading: "Components of a chart meeting both opens are reconstructed from " +
		"its two restricted charts. Simply choosing α(c) or β(c) would be wrong: " +
		"both can vanish at an ambient chart whose whole domain lies in neither open.",
	Deps: []registry.EntryLike{
		de_rham.ComplexDef,
		CoverRestrictionDef,
		differential_form.FormExt,
		differential_form.FormRestrict,
		smooth_manifold.OpenCompatibleChart,
		vec_smooth.SmoothLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"α ∈ «open complex»(U).terms(k)",
			"β ∈ «open complex»(V).terms(k)",
			"«open restriction»(U, U ∩ V, α) = «open restriction»(V, U ∩ V, β)",
		},
		Conclusion: "∃ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    ω ∈ de_rham_complex⟨n⟩(T, 𝒜).terms(k) ∧ " +
			"    de_rham_cover_restriction⟨n⟩(T, 𝒜, U, V)(ω) = (α, β) ∧ " +
			"    (∀η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        η ∈ de_rham_complex⟨n⟩(T, 𝒜).terms(k) ∧ " +
			"        de_rham_cover_restriction⟨n⟩(T, 𝒜, U, V)(η) = (α, β) ⇒ " +
			"        η = ω)",
	}, "For each ambient compatible chart, use its restrictions to U and V to read the two "+
		"local coefficients. The overlap equality and chart transition laws identify them; local "+
		"smoothness glues these values on the coordinate image. Normalize outside that image and at "+
		"incompatible charts; the same local argument gives all transition equations and uniqueness."),
})}

var CoverCochain = coverCochainThm{family.Add(registry.ProofEntry{
	Name:    "CoverCochain",
	Key:     "prop_6d7c852e3258796d",
	Reading: "No covering or partition is required for these maps to be cochain maps.",
	Deps: []registry.EntryLike{
		de_rham.Complex,
		CoverComplexDef,
		CoverRestrictionDef,
		CoverDifferenceDef,
		de_rham.PullbackCochain,
		differential_form.PullbackOpenInclusion,
		differential_form.RestrictionExteriorDerivative,
		differential_form.ExteriorDerivativeLinear,
		smooth_manifold.OpenSubmanifold,
		module_homomorphism.ProductModuleOn,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T", "V ∈ T"},
		Conclusion: "cochain_complex(real_ring, de_rham_cover_complex⟨n⟩(T, 𝒜, U, V)) ∧ " +
			"cochain_map(real_ring, " +
			"    de_rham_complex⟨n⟩(T, 𝒜), " +
			"    de_rham_cover_complex⟨n⟩(T, 𝒜, U, V), " +
			"    (λq:num. de_rham_cover_restriction⟨n⟩(T, 𝒜, U, V))) ∧ " +
			"cochain_map(real_ring, " +
			"    de_rham_cover_complex⟨n⟩(T, 𝒜, U, V), " +
			"    «open complex»(U ∩ V), " +
			"    (λq:num. de_rham_cover_difference⟨n⟩(T, 𝒜, U, V)))",
	},
		"Each degree of the middle complex is the product of the two form modules, and its "+
			"differential acts componentwise. Open-inclusion pullback gives linear restrictions "+
			"commuting with d; subtraction preserves both properties, giving the two cochain maps."),
})}

var CoverDifferenceSurjective = coverDifferenceSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "CoverDifferenceSurjective",
	Key:  "prop_233d9b4e401ed7b0",
	Reading: "The weights need not be nonnegative or compactly supported. Closed " +
		"scalar support contained in its designated open is essential; the support of " +
		"a form merely closed in the intersection would not justify either extension. " +
		"For ψω its intersection-relative support lies in the U-closed set U ∩ " +
		"supp(ψ), itself contained in U ∩ V; hence the form support is closed in U.",
	Deps: []registry.EntryLike{
		CoverCochain,
		CoverDifferenceDef,
		differential_form.WeightForm,
		differential_form.WeightSupport,
		differential_form.ExtendZeroForm,
		differential_form.ExtendZeroRestrict,
		smooth_manifold.FunctionRestrict,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀φ ψ:(A → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"smooth_manifold_function⟨n⟩(T, 𝒜, φ)",
			"smooth_manifold_function⟨n⟩(T, 𝒜, ψ)",
			"function_support(T, &0, φ) ⊆ U",
			"function_support(T, &0, ψ) ⊆ V",
			"∀x:A. x ∈ ⋃T ⇒ φ(x) + ψ(x) = &1",
		},
		Conclusion: "image(de_rham_cover_difference⟨n⟩(T, 𝒜, U, V), " +
			"    de_rham_cover_complex⟨n⟩(T, 𝒜, U, V).terms(k)) = " +
			"«open complex»(U ∩ V).terms(k)",
	},
		"For an intersection form ω, extend ψω by zero into U and extend −φω by "+
			"zero into V. The scalar support of ψ lies in V and is closed in the "+
			"ambient manifold, so its intersection with U controls the first extension; "+
			"the other is symmetric. Their difference on the intersection is (ψ+φ)ω = ω."),
})}

var MayerVietoris = mayerVietorisThm{family.Add(registry.ProofEntry{
	Name: "MayerVietoris",
	Key:  "prop_d8f88bcc2a33f586",
	Reading: "The scalar partition is supplied explicitly. No " +
		"general partition theorem on a noncompact manifold is assumed.",
	Deps: []registry.EntryLike{
		CoverCochain,
		CoverGluing,
		CoverDifferenceSurjective,
		chain_complex.ShortExactCochainComplexes,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U V:set(A). " +
			"∀φ ψ:(A → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"U ∈ T",
			"V ∈ T",
			"U ∪ V = ⋃T",
			"smooth_manifold_function⟨n⟩(T, 𝒜, φ)",
			"smooth_manifold_function⟨n⟩(T, 𝒜, ψ)",
			"function_support(T, &0, φ) ⊆ U",
			"function_support(T, &0, ψ) ⊆ V",
			"∀x:A. x ∈ ⋃T ⇒ φ(x) + ψ(x) = &1",
		},
		Conclusion: "«cover exact»",
	},
		"The paired restrictions are injective by unique gluing, and their image is precisely the pairs "+
			"with equal intersection restrictions. The difference is surjective by the subordinate scalar "+
			"weights. Together with the two cochain-map laws this is the short exact sequence of complexes."),
})}

var EuclideanProductMayerVietoris = euclideanProductMayerVietorisThm{family.Add(registry.ProofEntry{
	Name: "EuclideanProductMayerVietoris",
	Key:  "prop_7cb57bfc2ee8e398",
	Reading: "The second factor need not be compact or oriented. Supports " +
		"are closed in (O₁∪O₂)×W, not necessarily in the full Euclidean " +
		"ambient space. The empty opens and an empty second factor are allowed.",
	Deps: []registry.EntryLike{
		MayerVietoris,
		vec_smooth.SmoothPartitionOfUnityOpen,
		smooth_manifold.EuclideanManifold,
		smooth_manifold.ProductManifold,
		smooth_manifold.SmoothProductProjections,
		smooth_manifold.FunctionLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀N m:num. " +
			"∀O₁ O₂:set(num → real). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)).",
		Hypotheses: []string{
			"O₁ ∈ euclidean_topology(N)",
			"O₂ ∈ euclidean_topology(N)",
			"smooth_manifold⟨m⟩(S, ℬ)",
		},
		Conclusion: "short_exact_cochain_complexes(real_ring, " +
			"    de_rham_complex⟨N + m⟩(product_topology(subtopology(euclidean_topology(N), O₁ ∪ O₂), S), " +
			"        smooth_product_atlas⟨N, m⟩(euclidean_atlas(O₁ ∪ O₂), ℬ)), " +
			"    de_rham_cover_complex⟨N + m⟩( " +
			"        product_topology(subtopology(euclidean_topology(N), O₁ ∪ O₂), S), " +
			"        smooth_product_atlas⟨N, m⟩(euclidean_atlas(O₁ ∪ O₂), ℬ), " +
			"        set_cross(O₁, ⋃S), " +
			"        set_cross(O₂, ⋃S)), " +
			"    de_rham_complex⟨N + m⟩(subtopology( " +
			"            product_topology(subtopology(euclidean_topology(N), O₁ ∪ O₂), S), " +
			"            set_cross(O₁, ⋃S) ∩ set_cross(O₂, ⋃S)), " +
			"        open_submanifold_atlas⟨N + m⟩( " +
			"            product_topology(subtopology(euclidean_topology(N), O₁ ∪ O₂), S), " +
			"            smooth_product_atlas⟨N, m⟩(euclidean_atlas(O₁ ∪ O₂), ℬ), " +
			"            set_cross(O₁, ⋃S) ∩ set_cross(O₂, ⋃S))), " +
			"    (λq:num. " +
			"        de_rham_cover_restriction⟨N + m⟩( " +
			"            product_topology(subtopology(euclidean_topology(N), O₁ ∪ O₂), S), " +
			"            smooth_product_atlas⟨N, m⟩(euclidean_atlas(O₁ ∪ O₂), ℬ), " +
			"            set_cross(O₁, ⋃S), " +
			"            set_cross(O₂, ⋃S))), " +
			"    (λq:num. " +
			"        de_rham_cover_difference⟨N + m⟩( " +
			"            product_topology(subtopology(euclidean_topology(N), O₁ ∪ O₂), S), " +
			"            smooth_product_atlas⟨N, m⟩(euclidean_atlas(O₁ ∪ O₂), ℬ), " +
			"            set_cross(O₁, ⋃S), " +
			"            set_cross(O₂, ⋃S))))",
	},
		"Choose the two-open-set Euclidean partition and compose each weight with the first "+
			"projection, setting it to zero outside the product carrier. Product charts give smoothness; "+
			"its support is contained in the inverse image of the corresponding closed relative "+
			"Euclidean support. Apply MayerVietoris on the product with the restricted open atlases."),
})}
