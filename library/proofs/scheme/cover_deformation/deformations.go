package cover_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_deformation"
	"github.com/euc-ai/xugo/library/registry"
)

var coverDeformationDatumDef = coverDeformationDatumDefThm{family.Define(registry.DefEntry{
	Name:  "coverDeformationDatumDef",
	Key:   "prop_5bbe3d6a6ed0c93",
	Const: "cover_deformation_datum",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → F → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(set(num) → set(num) → B) → " +
		"(set(num) → A → D) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(F). " +
			"∀p₀:(A → F). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀u:(set(num) → F → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀t:(set(num) → set(num) → B). " +
			"∀ι:(set(num) → A → D). " +
			"    cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, ι) ⇔ " +
			"    cover_datum(R₀, S, u, N, g, v, t) ∧ " +
			"    ring_homomorphism(R, R₀, p₀) ∧ " +
			"    image(p₀, R.carrier) = R₀.carrier ∧ " +
			"    (∀x y:A. " +
			"        x ∈ ring_kernel(R₀.zero, R.carrier, p₀) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, p₀) ⇒ " +
			"        R.mul(x, y) = R.zero) ∧ " +
			"    (∀σ:set(num). " +
			"        σ ∈ intersection_indices ⇒ " +
			"        module_homomorphism(R₀, " +
			"            thickening_kernel(R, R₀, p₀), " +
			"            scalar_restriction(u(σ), N(σ)), " +
			"            ι(σ))) ∧ " +
			"    (∀σ τ:set(num). " +
			"        σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
			"        (∀j:A. j ∈ ring_kernel(R₀.zero, R.carrier, p₀) ⇒ v(σ, τ, ι(σ, j)) = ι(τ, j)))",
	},
	Deps: []registry.EntryLike{coverDatumDef},
	Reading: "A square-zero base thickening, a cover over its reduction, " +
		"and compatible coefficient maps from the thickening ideal."})}

var coverDeformationComparisonsDef = coverDeformationComparisonsDefThm{family.Define(registry.DefEntry{
	Name:  "coverDeformationComparisonsDef",
	Key:   "prop_7423ee51bce6846c",
	Const: "cover_deformation_comparisons",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → F → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(set(num) → A → D) → " +
		"set(prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"        prod(set(num), set(num)) → B → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(F). " +
			"∀p₀:(A → F). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀u:(set(num) → F → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀ι:(set(num) → A → D). " +
			"    cover_deformation_comparisons(R, R₀, p₀, S, u, N, g, v, ι) = " +
			"    {q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"            prod(set(num), set(num)) → B → D) | " +
			"        q ∈ cover_comparison_codes(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v) ∧ " +
			"        (∀σ:set(num). " +
			"            σ ∈ intersection_indices ⇒ " +
			"            (∀j:A. j ∈ ring_kernel(R₀.zero, R.carrier, p₀) ⇒ snd(snd(fst(q, σ)), j) = ι(σ, j)))}",
	},
	Deps:    []registry.EntryLike{coverComparisonCodesDef},
	Reading: "Impose the prescribed rho values on the thickening ideal at every intersection."})}

var coverDeformationCodesDef = coverDeformationCodesDefThm{family.Define(registry.DefEntry{
	Name:  "coverDeformationCodesDef",
	Key:   "prop_e144a633d9476244",
	Const: "cover_deformation_codes",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → F → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(set(num) → A → D) → " +
		"set(prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"        prod(set(num), set(num)) → B → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(F). " +
			"∀p₀:(A → F). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀u:(set(num) → F → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀ι:(set(num) → A → D). " +
			"    cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι) = " +
			"    {q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"            prod(set(num), set(num)) → B → D) | " +
			"        q ∈ cover_extension_codes(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v) ∧ " +
			"        (∀σ:set(num). " +
			"            σ ∈ intersection_indices ⇒ " +
			"            (∀j:A. j ∈ ring_kernel(R₀.zero, R.carrier, p₀) ⇒ snd(snd(fst(q, σ)), j) = ι(σ, j)))}",
	},
	Deps:    []registry.EntryLike{coverExtensionCodesDef},
	Reading: "Impose the prescribed rho values on the thickening ideal at every intersection."})}

var coverLocalDeformationsDef = coverLocalDeformationsDefThm{family.Define(registry.DefEntry{
	Name:  "coverLocalDeformationsDef",
	Key:   "prop_f5a0c2abd13dc24d",
	Const: "cover_local_deformations",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → F → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → A → D) → " +
		"set(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(F). " +
			"∀p₀:(A → F). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀u:(set(num) → F → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀ι:(set(num) → A → D). " +
			"    cover_local_deformations(R, R₀, p₀, S, u, N, ι) = " +
			"    {z:(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))) | " +
			"        z ∈ " +
			"        indexed_functions(intersection_indices, " +
			"            λσ:set(num). factor_set_ambient(R, S(σ), N(σ)).one, " +
			"            λσ:set(num). factor_set_ambient(R, S(σ), N(σ)).carrier) ∧ " +
			"        (∀σ:set(num). " +
			"            σ ∈ intersection_indices ⇒ " +
			"            z(σ) ∈ deformation_codes(R, R₀, p₀, S(σ), u(σ), N(σ), ι(σ)))}",
	},
	Deps: []registry.EntryLike{},
	Reading: "Independent local deformation codes; there " +
		"are no overlap maps or compatibility assumptions."})}

var coverInflateDef = coverInflateDefThm{family.Define(registry.DefEntry{
	Name:  "coverInflateDef",
	Key:   "prop_375b8a7ae23b25",
	Const: "cover_inflate",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → module_ops(B, D)) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, F → D)), " +
		"    prod(set(num), set(num)) → B → D) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"    prod(set(num), set(num)) → B → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(F). " +
			"∀p₀:(A → F). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, F → D)), " +
			"        prod(set(num), set(num)) → B → D). " +
			"    cover_inflate(R, R₀, p₀, S, N)(q) = " +
			"    (λσ:set(num). " +
			"        COND(σ ∈ intersection_indices, " +
			"            (fst(fst(q, σ)), " +
			"                (fst(snd(fst(q, σ))), " +
			"                    λa:A. COND(a ∈ R.carrier, snd(snd(fst(q, σ)), p₀(a)), N(σ).zero))), " +
			"            factor_set_ambient(R, S(σ), N(σ)).one), " +
			"    snd(q))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Inflate only the rho component along the base " +
		"surjection; arrow shears and other defects are unchanged."})}

var CoverDeformationCodesCoset = coverDeformationCodesCosetThm{family.Add(registry.ProofEntry{
	Name: "CoverDeformationCodesCoset",
	Key:  "prop_618ae653fc156cf7",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p₀:(A → F). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀u:(set(num) → F → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀ι:(set(num) → A → D).",
			Hypotheses: []string{"cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, ι)"},
			Conclusion: "closed_in(cover_code_topology(R, S, N), " +
				"    cover_deformation_comparisons(R, R₀, p₀, S, u, N, g, v, ι)) ∧ " +
				"closed_in(cover_code_topology(R, S, N), cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι)) ∧ " +
				"(∀q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D). " +
				"    q ∈ cover_deformation_comparisons(R, R₀, p₀, S, u, N, g, v, ι) ⇒ " +
				"    cover_deformation_comparisons(R, R₀, p₀, S, u, N, g, v, ι) = " +
				"    left_coset(cover_code_ambient(R, S, N).mul, " +
				"        q, " +
				"        image(cover_inflate(R, R₀, p₀, S, N), cover_comparison_codes(R₀, S, u, N, g, v)))) ∧ " +
				"(∀q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D). " +
				"    q ∈ cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι) ⇒ " +
				"    cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι) = " +
				"    left_coset(cover_code_ambient(R, S, N).mul, " +
				"        q, " +
				"        image(cover_inflate(R, R₀, p₀, S, N), cover_extension_codes(R₀, S, u, N, g, v)))) ∧ " +
				"image(cover_inflate(R, R₀, p₀, S, N), cover_boundaries(R₀, S, u, N, g, v)) = " +
				"cover_boundaries(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v)",
		},
		"The local affine rho equations are closed. Differences descend through the base "+
			"surjection, with arrow shears unchanged, by DeformationKernelIsReducedBase. "+
			"Composition is preserved under descent and inflation."),
	Deps: []registry.EntryLike{
		coverDeformationCodesDef,
		coverDeformationComparisonsDef,
		coverInflateDef,
		definable_deformation.DeformationKernelIsReducedBase,
		CoverExtensionCodesClosed,
	},
	Reading: "The local affine rho equations are closed. Differences descend through the " +
		"base surjection, with arrow shears unchanged, by DeformationKernelIsReducedBase. " +
		"Composition is preserved under descent and inflation.",
})}

var CoverDeformationsTorsor = coverDeformationsTorsorThm{family.Add(registry.ProofEntry{
	Name: "CoverDeformationsTorsor",
	Key:  "prop_a9dab3131c12bfe3",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p₀:(A → F). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀u:(set(num) → F → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀ι:(set(num) → A → D). " +
				"∀q r:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D).",
			Hypotheses: []string{
				"cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, ι)",
				"q ∈ cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι)",
				"r ∈ cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι)",
			},
			Conclusion: "∃e:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, F → D)), " +
				"        prod(set(num), set(num)) → B → D). " +
				"    e ∈ cover_extension_codes(R₀, S, u, N, g, v) ∧ " +
				"    cover_code_ambient(R, S, N).mul(r, " +
				"        cover_code_ambient(R, S, N).inv( " +
				"            cover_code_ambient(R, S, N).mul(q, cover_inflate(R, R₀, p₀, S, N)(e)))) ∈ " +
				"    cover_boundaries(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v) ∧ " +
				"    (∀e₁:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, F → D)), " +
				"            prod(set(num), set(num)) → B → D). " +
				"        e₁ ∈ cover_extension_codes(R₀, S, u, N, g, v) ∧ " +
				"        cover_code_ambient(R, S, N).mul(r, " +
				"            cover_code_ambient(R, S, N).inv( " +
				"                cover_code_ambient(R, S, N).mul(q, cover_inflate(R, R₀, p₀, S, N)(e₁)))) ∈ " +
				"        cover_boundaries(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v) ⇒ " +
				"        cover_code_ambient(R₀, S, N).mul(e, cover_code_ambient(R₀, S, N).inv(e₁)) ∈ " +
				"        cover_boundaries(R₀, S, u, N, g, v))",
		},
		"Translate by the fixed deformation, use the inflation isomorphism onto the difference "+
			"subgroup, and pass to actual boundary subgroups. This gives existence and uniqueness "+
			"of the reduced-base extension class acting between two deformation classes."),
	Deps: []registry.EntryLike{CoverDeformationCodesCoset, CoverExtensionIsoIffBoundary},
	Reading: "Translate by the fixed deformation, use the inflation isomorphism onto the " +
		"difference subgroup, and pass to actual boundary subgroups. This gives existence and " +
		"uniqueness of the reduced-base extension class acting between two deformation classes.",
})}

var coverLocalObstructionDef = coverLocalObstructionDefThm{family.Define(registry.DefEntry{
	Name:  "coverLocalObstructionDef",
	Key:   "prop_24e0bef2aecbf207",
	Const: "cover_local_obstruction",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → F → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(set(num) → A → D) → " +
		"set(prod(num, num → num) → set(U → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(F). " +
			"∀p₀:(A → F). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀u:(set(num) → F → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀ι:(set(num) → A → D). " +
			"    cover_local_obstruction(R, R₀, p₀, S, u, N, g, v, ι) = " +
			"    left_coset(intersection_cech_complex(R₀, " +
			"            cover_aq_module⟨U:U⟩(R₀, S, u, N, 2), " +
			"            cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 2)).add, " +
			"        λw:prod(num, num → num). " +
			"            COND(w ∈ ordered_cech_indices(0), " +
			"                algebra_deformation_obstruction⟨U:U⟩(R, " +
			"                    R₀, " +
			"                    p₀, " +
			"                    S(cech_support(w)), " +
			"                    u(cech_support(w)), " +
			"                    N(cech_support(w)), " +
			"                    ι(cech_support(w))), " +
			"                cover_aq_module⟨U:U⟩(R₀, S, u, N, 2, cech_support(w)).zero), " +
			"        coboundaries(intersection_cech_complex(R₀, " +
			"                cover_aq_module⟨U:U⟩(R₀, S, u, N, 2), " +
			"                cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 2)), " +
			"            0))",
	},
	Deps:    []registry.EntryLike{coverAQModuleDef, coverAQRestrictionDef},
	Reading: "The local algebra deformation obstructions as a degree-zero Cech class."})}

var CoverLocalObstruction = coverLocalObstructionThm{family.Add(registry.ProofEntry{
	Name: "CoverLocalObstruction",
	Key:  "prop_30639068aa3932cf",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p₀:(A → F). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀u:(set(num) → F → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀ι:(set(num) → A → D).",
			Hypotheses: []string{
				"cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, ι)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:U⟩)",
			},
			Conclusion: "cover_local_obstruction⟨U:U⟩(R, R₀, p₀, S, u, N, g, v, ι) ∈ " +
				"cohomology(intersection_cech_complex(R₀, " +
				"        cover_aq_module⟨U:U⟩(R₀, S, u, N, 2), " +
				"        cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 2)), " +
				"    0) ∧ " +
				"(cover_local_obstruction⟨U:U⟩(R, R₀, p₀, S, u, N, g, v, ι) = " +
				"    coboundaries(intersection_cech_complex(R₀, " +
				"            cover_aq_module⟨U:U⟩(R₀, S, u, N, 2), " +
				"            cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 2)), " +
				"        0) ⇔ " +
				"    ¬(cover_local_deformations(R, R₀, p₀, S, u, N, ι) = ∅))",
		},
		"Naturality of the transitivity connecting map makes the local "+
			"obstruction classes compatible. DeformationCodesNonemptyIffObstruction "+
			"gives exactly the criterion for independent local deformations."),
	Deps: []registry.EntryLike{
		coverLocalObstructionDef,
		coverLocalDeformationsDef,
		definable_deformation.DeformationCodesNonemptyIffObstruction,
	},
	Reading: "Naturality of the transitivity connecting map makes the local " +
		"obstruction classes compatible. DeformationCodesNonemptyIffObstruction " +
		"gives exactly the criterion for independent local deformations.",
})}

var coverMatchingCochainDef = coverMatchingCochainDefThm{family.Define(registry.DefEntry{
	Name:  "coverMatchingCochainDef",
	Key:   "prop_45a27d46a867c8d2",
	Const: "cover_matching_cochain",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → F → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(set(num) → set(num) → B) → " +
		"(set(num) → A → D) → " +
		"(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))) → " +
		"prod(num, num → num) → " +
		"set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(F). " +
			"∀p₀:(A → F). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀u:(set(num) → F → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀t:(set(num) → set(num) → B). " +
			"∀ι:(set(num) → A → D). " +
			"∀z:(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))). " +
			"∀w:prod(num, num → num). " +
			"    cover_matching_cochain(R, R₀, p₀, S, u, N, g, v, t, ι, z, w) = " +
			"    COND(w ∈ ordered_cech_indices(1), " +
			"        εc:set(U → D). " +
			"            c ∈ cover_aq_module⟨U:U⟩(R₀, S, u, N, 1, cech_support(w)).carrier ∧ " +
			"            square_zero_class⟨U:U⟩(R, " +
			"                S(cech_support(w)), " +
			"                λa:A. u(cech_support(w), p₀(a)), " +
			"                N(cech_support(w)), " +
			"                square_zero_localization(N({snd(w, 1)}), " +
			"                    S(cech_support(w)), " +
			"                    g({snd(w, 1)}, cech_support(w)), " +
			"                    N(cech_support(w)), " +
			"                    v({snd(w, 1)}, cech_support(w)), " +
			"                    factor_set_extension(S({snd(w, 1)}), " +
			"                        λa:A. u({snd(w, 1)}, p₀(a)), " +
			"                        N({snd(w, 1)}), " +
			"                        z({snd(w, 1)})), " +
			"                    (N({snd(w, 1)}).zero, t({snd(w, 1)}, cech_support(w))))) = " +
			"            cotangent_cohomology⟨U:U⟩(R, " +
			"                S(cech_support(w)), " +
			"                λa:A. u(cech_support(w), p₀(a)), " +
			"                S(cech_support(w)), " +
			"                λy:B. y, " +
			"                N(cech_support(w)), " +
			"                1).add(square_zero_class⟨U:U⟩(R, " +
			"                    S(cech_support(w)), " +
			"                    λa:A. u(cech_support(w), p₀(a)), " +
			"                    N(cech_support(w)), " +
			"                    square_zero_localization(N({snd(w, 0)}), " +
			"                        S(cech_support(w)), " +
			"                        g({snd(w, 0)}, cech_support(w)), " +
			"                        N(cech_support(w)), " +
			"                        v({snd(w, 0)}, cech_support(w)), " +
			"                        factor_set_extension(S({snd(w, 0)}), " +
			"                            λa:A. u({snd(w, 0)}, p₀(a)), " +
			"                            N({snd(w, 0)}), " +
			"                            z({snd(w, 0)})), " +
			"                        (N({snd(w, 0)}).zero, t({snd(w, 0)}, cech_support(w))))), " +
			"                co_transitivity_left_map(R, " +
			"                    R₀, " +
			"                    p₀, " +
			"                    S(cech_support(w)), " +
			"                    u(cech_support(w)), " +
			"                    N(cech_support(w)), " +
			"                    1, " +
			"                    c)), " +
			"        cover_aq_module⟨U:U⟩(R₀, S, u, N, 1, cech_support(w)).zero)",
	},
	Deps: []registry.EntryLike{coverAQModuleDef},
	Reading: "The unique reduced-base torsor difference between the two localized " +
		"local deformations on each ordered pair. Inactive coordinates are zero."})}

var coverMatchingObstructionDef = coverMatchingObstructionDefThm{family.Define(registry.DefEntry{
	Name:  "coverMatchingObstructionDef",
	Key:   "prop_fe92069dd697ef81",
	Const: "cover_matching_obstruction",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → F → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(set(num) → set(num) → B) → " +
		"(set(num) → A → D) → " +
		"set(prod(num, num → num) → set(U → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀R₀:ring_ops(F). " +
			"∀p₀:(A → F). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀u:(set(num) → F → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀t:(set(num) → set(num) → B). " +
			"∀ι:(set(num) → A → D). " +
			"    cover_matching_obstruction(R, R₀, p₀, S, u, N, g, v, t, ι) = " +
			"    left_coset(intersection_cech_complex(R₀, " +
			"            cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
			"            cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)).add, " +
			"        cover_matching_cochain⟨U:U⟩(R, R₀, p₀, S, u, N, g, v, t, ι)(εz:(set(num) → " +
			"                    prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))). " +
			"                z ∈ cover_local_deformations(R, R₀, p₀, S, u, N, ι)), " +
			"        coboundaries(intersection_cech_complex(R₀, " +
			"                cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
			"                cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)), " +
			"            1))",
	},
	Deps: []registry.EntryLike{
		coverAQModuleDef,
		coverAQRestrictionDef,
		coverLocalDeformationsDef,
		coverMatchingCochainDef,
	},
	Reading: "Choose independent local deformation codes and take the class " +
		"of their matching cochain. Used only when the local obstruction vanishes."})}

var CoverMatchingObstruction = coverMatchingObstructionThm{family.Add(registry.ProofEntry{
	Name: "CoverMatchingObstruction",
	Key:  "prop_9c222a4ebcd0548",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p₀:(A → F). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀u:(set(num) → F → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀ι:(set(num) → A → D). " +
				"∀z:(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D))).",
			Hypotheses: []string{
				"cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, ι)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:U⟩)",
				"z ∈ cover_local_deformations(R, R₀, p₀, S, u, N, ι)",
			},
			Conclusion: "cover_matching_cochain⟨U:U⟩(R, R₀, p₀, S, u, N, g, v, t, ι)(z) ∈ " +
				"cocycles(intersection_cech_complex(R₀, " +
				"        cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
				"        cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)), " +
				"    1) ∧ " +
				"cover_matching_obstruction⟨U:U⟩(R, R₀, p₀, S, u, N, g, v, t, ι) = " +
				"left_coset(intersection_cech_complex(R₀, " +
				"        cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
				"        cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)).add, " +
				"    cover_matching_cochain⟨U:U⟩(R, R₀, p₀, S, u, N, g, v, t, ι)(z), " +
				"    coboundaries(intersection_cech_complex(R₀, " +
				"            cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
				"            cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)), " +
				"        1)) ∧ " +
				"(cover_matching_obstruction⟨U:U⟩(R, R₀, p₀, S, u, N, g, v, t, ι) = " +
				"    coboundaries(intersection_cech_complex(R₀, " +
				"            cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
				"            cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)), " +
				"        1) ⇔ " +
				"    ¬(cover_deformation_comparisons(R, R₀, p₀, S, u, N, g, v, ι) = ∅))",
		},
		"The torsor difference telescopes on triples. Changing the local deformation family "+
			"changes this cochain by a Cech coboundary. Killing it gives compatible local "+
			"deformation classes, which admit individual actual maps and hence comparison codes."),
	Deps: []registry.EntryLike{
		coverMatchingObstructionDef,
		CoverLocalClasses,
		algebra_deformation.DeformationsTorsor,
		algebra_deformation.DeformationLocalizes,
	},
	Reading: "The torsor difference telescopes on triples. Changing the local deformation " +
		"family changes this cochain by a Cech coboundary. Killing it gives compatible local " +
		"deformation classes, which admit individual actual maps and hence comparison codes.",
})}

var CoverThirdObstruction = coverThirdObstructionThm{family.Add(registry.ProofEntry{
	Name: "CoverThirdObstruction",
	Key:  "prop_cfce64fc1cb72d76",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p₀:(A → F). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀u:(set(num) → F → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀ι:(set(num) → A → D). " +
				"∀q r:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D).",
			Hypotheses: []string{
				"cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, ι)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:U⟩)",
				"q ∈ cover_deformation_comparisons(R, R₀, p₀, S, u, N, g, v, ι)",
				"r ∈ cover_deformation_comparisons(R, R₀, p₀, S, u, N, g, v, ι)",
			},
			Conclusion: "cover_triple_defect(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v)(q) ∈ " +
				"cocycles(intersection_cech_complex(R₀, " +
				"        cover_derivation_module(R₀, S, u, N), " +
				"        cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"    2) ∧ " +
				"cohomology_module(intersection_cech_complex(R₀, " +
				"        cover_derivation_module(R₀, S, u, N), " +
				"        cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"    2).add(left_coset(intersection_cech_complex(R₀, " +
				"            cover_derivation_module(R₀, S, u, N), " +
				"            cover_derivation_restriction(R₀, S, u, N, g, v)).add, " +
				"        cover_triple_defect(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v)(r), " +
				"        coboundaries(intersection_cech_complex(R₀, " +
				"                cover_derivation_module(R₀, S, u, N), " +
				"                cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"            2)), " +
				"    cohomology_module(intersection_cech_complex(R₀, " +
				"            cover_derivation_module(R₀, S, u, N), " +
				"            cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"        2).neg(left_coset(intersection_cech_complex(R₀, " +
				"                cover_derivation_module(R₀, S, u, N), " +
				"                cover_derivation_restriction(R₀, S, u, N, g, v)).add, " +
				"            cover_triple_defect(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v)(q), " +
				"            coboundaries(intersection_cech_complex(R₀, " +
				"                    cover_derivation_module(R₀, S, u, N), " +
				"                    cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"                2)))) ∈ " +
				"image(cover_d2⟨U:U⟩(R₀, S, u, N, g, v), " +
				"    cohomology(intersection_cech_complex(R₀, " +
				"            cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
				"            cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)), " +
				"        0)) ∧ " +
				"(¬(cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι) = ∅) ⇔ " +
				"    left_coset(intersection_cech_complex(R₀, " +
				"            cover_derivation_module(R₀, S, u, N), " +
				"            cover_derivation_restriction(R₀, S, u, N, g, v)).add, " +
				"        cover_triple_defect(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v)(q), " +
				"        coboundaries(intersection_cech_complex(R₀, " +
				"                cover_derivation_module(R₀, S, u, N), " +
				"                cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"            2)) ∈ " +
				"    image(cover_d2⟨U:U⟩(R₀, S, u, N, g, v), " +
				"        cohomology(intersection_cech_complex(R₀, " +
				"                cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
				"                cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)), " +
				"            0)))",
		},
		"The difference of two comparison deformation codes descends to reduced-base comparison data. "+
			"Their triple classes differ by d2 of its local class. A global deformation exists exactly "+
			"when some such change kills the triple class and allows the pair maps to be corrected."),
	Deps: []registry.EntryLike{
		CoverDeformationCodesCoset,
		CoverD2WellDefined,
		CoverExtensionExactSequence,
	},
	Reading: "The choice-independent third obstruction lives in H2(Der) modulo image(d2). " +
		"For a fixed compatible local family the unquotiented triple class must vanish.",
})}

var SmoothCoverDeformationObstruction = smoothCoverDeformationObstructionThm{family.Add(registry.ProofEntry{
	Name: "SmoothCoverDeformationObstruction",
	Key:  "prop_d44dc016adb02bc5",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀R₀:ring_ops(F). " +
				"∀p₀:(A → F). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀u:(set(num) → F → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀ι:(set(num) → A → D).",
			Hypotheses: []string{
				"cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, ι)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:U⟩)",
				"∀σ:set(num). " +
					"    σ ∈ intersection_indices ⇒ " +
					"    cover_aq_module⟨U:U⟩(R₀, S, u, N, 1, σ).carrier = " +
					"    {cover_aq_module⟨U:U⟩(R₀, S, u, N, 1, σ).zero} ∧ " +
					"    cover_aq_module⟨U:U⟩(R₀, S, u, N, 2, σ).carrier = " +
					"    {cover_aq_module⟨U:U⟩(R₀, S, u, N, 2, σ).zero}",
			},
			Conclusion: "¬(cover_deformation_comparisons(R, R₀, p₀, S, u, N, g, v, ι) = ∅) ∧ " +
				"(∀q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D). " +
				"    q ∈ cover_deformation_comparisons(R, R₀, p₀, S, u, N, g, v, ι) ⇒ " +
				"    (¬(cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι) = ∅) ⇔ " +
				"        cover_triple_defect(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v)(q) ∈ " +
				"        coboundaries(intersection_cech_complex(R₀, " +
				"                cover_derivation_module(R₀, S, u, N), " +
				"                cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"            2)))",
		},
		"Vanishing T2 removes the first obstruction and vanishing T1 removes "+
			"the matching obstruction and the image of d2. The remaining "+
			"obstruction is the canonical H2(Der) class, which need not vanish."),
	Deps: []registry.EntryLike{
		CoverLocalObstruction,
		CoverMatchingObstruction,
		CoverThirdObstruction,
	},
	Reading: "Vanishing T2 removes the first obstruction and vanishing T1 " +
		"removes the matching obstruction and the image of d2. The remaining " +
		"obstruction is the canonical H2(Der) class, which need not vanish.",
})}
