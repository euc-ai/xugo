package cover_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var coverPathDefectDef = coverPathDefectDefThm{family.Define(registry.DefEntry{
	Name:  "coverPathDefectDef",
	Key:   "prop_ddd84b144855c518",
	Const: "cover_path_defect",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"    prod(set(num), set(num)) → B → D) → " +
		"set(num) → " +
		"set(num) → " +
		"set(num) → " +
		"B → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"        prod(set(num), set(num)) → B → D). " +
			"∀σ τ υ:set(num). " +
			"    cover_path_defect(R, S, f, N, g, v, p, σ, τ, υ) = " +
			"    localized_derivation(R, " +
			"        S(σ), " +
			"        f(σ), " +
			"        S(υ), " +
			"        g(σ, υ), " +
			"        N(υ), " +
			"        λx:B. " +
			"            N(υ).add(N(υ).add(v(τ, υ, snd(p, (σ, τ), x)), snd(p, (τ, υ), g(σ, τ, x))), " +
			"                N(υ).neg(snd(p, (σ, υ), x))))",
	},
	Deps: []registry.EntryLike{localizedDerivationDef},
	Reading: "The difference of the two actual maps from sigma to upsilon, " +
		"uniquely extended as a derivation on the terminal intersection."})}

var coverTripleDefectDef = coverTripleDefectDefThm{family.Define(registry.DefEntry{
	Name:  "coverTripleDefectDef",
	Key:   "prop_6e8ca3e219caf75c",
	Const: "cover_triple_defect",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"    prod(set(num), set(num)) → B → D) → " +
		"prod(num, num → num) → " +
		"B → " +
		"D",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"        prod(set(num), set(num)) → B → D). " +
			"∀w:prod(num, num → num). " +
			"∀x:B. " +
			"    cover_triple_defect(R, S, f, N, g, v)(p, w, x) = " +
			"    COND(w ∈ ordered_cech_indices(2), " +
			"        N(cech_support(w)).add(N(cech_support(w)).add(N(cech_support(w)).add(N( " +
			"                        cech_support(w)).add(N(cech_support(w)).add(cover_path_defect(R, " +
			"                                S, " +
			"                                f, " +
			"                                N, " +
			"                                g, " +
			"                                v, " +
			"                                p, " +
			"                                {snd(w, 0)}, " +
			"                                {snd(w, 0), snd(w, 1)}, " +
			"                                cech_support(w), " +
			"                                x), " +
			"                            N(cech_support(w)).neg(cover_path_defect(R, " +
			"                                    S, " +
			"                                    f, " +
			"                                    N, " +
			"                                    g, " +
			"                                    v, " +
			"                                    p, " +
			"                                    {snd(w, 1)}, " +
			"                                    {snd(w, 0), snd(w, 1)}, " +
			"                                    cech_support(w), " +
			"                                    x))), " +
			"                        cover_path_defect(R, " +
			"                            S, " +
			"                            f, " +
			"                            N, " +
			"                            g, " +
			"                            v, " +
			"                            p, " +
			"                            {snd(w, 1)}, " +
			"                            {snd(w, 1), snd(w, 2)}, " +
			"                            cech_support(w), " +
			"                            x)), " +
			"                    N(cech_support(w)).neg(cover_path_defect(R, " +
			"                            S, " +
			"                            f, " +
			"                            N, " +
			"                            g, " +
			"                            v, " +
			"                            p, " +
			"                            {snd(w, 2)}, " +
			"                            {snd(w, 1), snd(w, 2)}, " +
			"                            cech_support(w), " +
			"                            x))), " +
			"                N(cech_support(w)).neg(cover_path_defect(R, " +
			"                        S, " +
			"                        f, " +
			"                        N, " +
			"                        g, " +
			"                        v, " +
			"                        p, " +
			"                        {snd(w, 0)}, " +
			"                        {snd(w, 0), snd(w, 2)}, " +
			"                        cech_support(w), " +
			"                        x))), " +
			"            cover_path_defect(R, " +
			"                S, " +
			"                f, " +
			"                N, " +
			"                g, " +
			"                v, " +
			"                p, " +
			"                {snd(w, 2)}, " +
			"                {snd(w, 0), snd(w, 2)}, " +
			"                cech_support(w), " +
			"                x)), " +
			"        N(cech_support(w)).zero)",
	},
	Deps: []registry.EntryLike{coverPathDefectDef},
	Reading: "The six path defects around a triangle. This is the actual " +
		"failure of pair comparison maps to satisfy the cocycle equation."})}

var coverLocalClassDef = coverLocalClassDefThm{family.Define(registry.DefEntry{
	Name:  "coverLocalClassDef",
	Key:   "prop_5062d3b49743dd7",
	Const: "cover_local_class",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"    prod(set(num), set(num)) → B → D) → " +
		"set(prod(num, num → num) → set(U → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"        prod(set(num), set(num)) → B → D). " +
			"    cover_local_class(R, S, f, N, g, v, p) = " +
			"    left_coset(intersection_cech_complex(R, " +
			"            cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
			"            cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)).add, " +
			"        λw:prod(num, num → num). " +
			"            COND(w ∈ ordered_cech_indices(0), " +
			"                square_zero_class⟨U:U⟩(R, " +
			"                    S(cech_support(w)), " +
			"                    f(cech_support(w)), " +
			"                    N(cech_support(w)), " +
			"                    factor_set_extension(S(cech_support(w)), " +
			"                        f(cech_support(w)), " +
			"                        N(cech_support(w)), " +
			"                        fst(p, cech_support(w)))), " +
			"                cover_aq_module⟨U:U⟩(R, S, f, N, 1, cech_support(w)).zero), " +
			"        coboundaries(intersection_cech_complex(R, " +
			"                cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
			"                cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)), " +
			"            0))",
	},
	Deps:    []registry.EntryLike{coverAQModuleDef, coverAQRestrictionDef},
	Reading: "The compatible singleton extension classes, read as a degree-zero Cech class."})}

var coverLocalKernelDef = coverLocalKernelDefThm{family.Define(registry.DefEntry{
	Name:  "coverLocalKernelDef",
	Key:   "prop_1ab1f21e6949d047",
	Const: "cover_local_kernel",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"set(prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"        prod(set(num), set(num)) → B → D))",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"    cover_local_kernel(R, S, f, N, g, v) = " +
			"    {p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"            prod(set(num), set(num)) → B → D) | " +
			"        p ∈ cover_comparison_codes(R, S, f, N, g, v) ∧ " +
			"        (∀σ:set(num). " +
			"            σ ∈ intersection_indices ⇒ fst(p, σ) ∈ factor_set_boundaries(R, S(σ), f(σ), N(σ)))}",
	},
	Deps: []registry.EntryLike{coverComparisonCodesDef},
	Reading: "Comparison data with locally split classes; " +
		"arrow comparison choices remain in the kernel."})}

var coverD2Def = coverD2DefThm{family.Define(registry.DefEntry{
	Name:  "coverD2Def",
	Key:   "prop_564182ada41cd537",
	Const: "cover_d2",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"set(prod(num, num → num) → set(U → D)) → " +
		"set(prod(num, num → num) → B → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀a:set(prod(num, num → num) → set(U → D)). " +
			"    cover_d2(R, S, f, N, g, v, a) = " +
			"    left_coset(intersection_cech_complex(R, " +
			"            cover_derivation_module(R, S, f, N), " +
			"            cover_derivation_restriction(R, S, f, N, g, v)).add, " +
			"        cover_triple_defect(R, S, f, N, g, v)(εp:prod( " +
			"                    set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
			"                    prod(set(num), set(num)) → B → D). " +
			"                p ∈ cover_comparison_codes(R, S, f, N, g, v) ∧ " +
			"                cover_local_class⟨U:U⟩(R, S, f, N, g, v)(p) = a), " +
			"        coboundaries(intersection_cech_complex(R, " +
			"                cover_derivation_module(R, S, f, N), " +
			"                cover_derivation_restriction(R, S, f, N, g, v)), " +
			"            2))",
	},
	Deps: []registry.EntryLike{
		coverComparisonCodesDef,
		coverDerivationModuleDef,
		coverDerivationRestrictionDef,
		coverLocalClassDef,
		coverTripleDefectDef,
	},
	Reading: "Choose concrete comparison data for the given compatible local classes and take " +
		"its triple-defect class. Independence and existence of witnesses are theorem statements."})}

var coverAnchorDef = coverAnchorDefThm{family.Define(registry.DefEntry{
	Name:      "coverAnchorDef",
	Key:       "prop_3f1c9f3280b71ab9",
	Const:     "cover_anchor",
	Type:      "set(num) → num",
	Equations: []string{"∀σ:set(num). cover_anchor(σ) = (εi:num. i ∈ σ ∧ (∀j:num. j ∈ σ ⇒ i ≤ j))"},
	Deps:      []registry.EntryLike{},
	Reading:   "The least chart index of a finite nonempty intersection."})}

var coverGlueCodeDef = coverGlueCodeDefThm{family.Define(registry.DefEntry{
	Name:  "coverGlueCodeDef",
	Key:   "prop_969d12530e2b0457",
	Const: "cover_glue_code",
	Type: "ring_ops(A) → " +
		"(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(prod(num, num → num) → B → D) → " +
		"prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
		"    prod(set(num), set(num)) → B → D)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀c:(prod(num, num → num) → B → D). " +
			"    cover_glue_code(R, S, f, N, g, v)(c) = " +
			"    (λσ:set(num). factor_set_ambient(R, S(σ), N(σ)).one, " +
			"    λa:prod(set(num), set(num)). λx:B. " +
			"        COND(a ∈ cover_arrows ∧ " +
			"            x ∈ S(fst(a)).carrier ∧ " +
			"            ¬(cover_anchor(snd(a)) = cover_anchor(fst(a))), " +
			"            cover_derivation_restriction(R, S, f, N, g, v)( " +
			"                {cover_anchor(snd(a)), cover_anchor(fst(a))}, " +
			"                snd(a), " +
			"                c((1, " +
			"                        λk:num. " +
			"                            COND(k = 0, " +
			"                                cover_anchor(snd(a)), " +
			"                                COND(k = 1, cover_anchor(fst(a)), 0)))), " +
			"                g(fst(a), snd(a), x)), " +
			"            N(snd(a)).zero))",
	},
	Deps: []registry.EntryLike{coverAnchorDef, coverArrowsDef, coverDerivationRestrictionDef},
	Reading: "Glue split local extensions using the cocycle between the least index of each " +
		"intersection and that of its parent. The cocycle identity gives strict composition."})}

var CoverTripleDefectCocycle = coverTripleDefectCocycleThm{family.Add(registry.ProofEntry{
	Name: "CoverTripleDefectCocycle",
	Key:  "prop_eacb580aff4a467f",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"p ∈ cover_comparison_codes(R, S, f, N, g, v)",
			},
			Conclusion: "cover_triple_defect(R, S, f, N, g, v)(p) ∈ " +
				"cocycles(intersection_cech_complex(R, " +
				"        cover_derivation_module(R, S, f, N), " +
				"        cover_derivation_restriction(R, S, f, N, g, v)), " +
				"    2) ∧ " +
				"(p ∈ cover_extension_codes(R, S, f, N, g, v) ⇒ " +
				"    cover_triple_defect(R, S, f, N, g, v)(p) = " +
				"    intersection_cech_complex(R, " +
				"        cover_derivation_module(R, S, f, N), " +
				"        cover_derivation_restriction(R, S, f, N, g, v)).zero)",
		},
		"Each path defect is a derivation; compare the four compositions around a quadruple intersection "+
			"to obtain the alternating cocycle identity. Strictly compositional data have zero path defects."),
	Deps: []registry.EntryLike{
		coverPathDefectDef,
		coverTripleDefectDef,
		DerivationLocalizationUnique,
		coverExtensionCodesDef,
	},
	Reading: "Each path defect is a derivation; compare the four " +
		"compositions around a quadruple intersection to obtain the alternating " +
		"cocycle identity. Strictly compositional data have zero path defects.",
})}

var CoverLocalClasses = coverLocalClassesThm{family.Add(registry.ProofEntry{
	Name: "CoverLocalClasses",
	Key:  "prop_f8e5e5a53b02cb95",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:U⟩)",
			},
			Conclusion: "group_homomorphism( " +
				"    restrict_group(cover_code_ambient(R, S, N), cover_comparison_codes(R, S, f, N, g, v)), " +
				"    module_additive_group(cohomology_module(intersection_cech_complex(R, " +
				"                cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
				"                cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)), " +
				"            0)), " +
				"    cover_local_class⟨U:U⟩(R, S, f, N, g, v)) ∧ " +
				"image(cover_local_class⟨U:U⟩(R, S, f, N, g, v), cover_comparison_codes(R, S, f, N, g, v)) = " +
				"cohomology(intersection_cech_complex(R, " +
				"        cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
				"        cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)), " +
				"    0) ∧ " +
				"{p:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D) | " +
				"    p ∈ cover_comparison_codes(R, S, f, N, g, v) ∧ " +
				"    cover_local_class⟨U:U⟩(R, S, f, N, g, v)(p) = " +
				"    coboundaries(intersection_cech_complex(R, " +
				"            cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
				"            cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)), " +
				"        0)} = " +
				"cover_local_kernel(R, S, f, N, g, v)",
		},
		"Individual extension maps identify localized classes. Conversely realize each intersection "+
			"class, and choose maps on individual arrows using equality of classes; there is no "+
			"composition constraint. Vanishing singleton classes forces every intersection class to vanish."),
	Deps: []registry.EntryLike{
		coverLocalClassDef,
		coverLocalKernelDef,
		AQPresheaf,
		definable_deformation.FactorSetRealization,
		definable_deformation.FactorSetIsoIffBoundary,
		square_zero_classification.ExtensionRealizeClass,
		square_zero_classification.ExtensionClassWellDefined,
		algebra_deformation.SquareZeroLocalizationClass,
	},
	Reading: "The assertion is algebraic and does not assume the quotient groups are Polish.",
})}

var CoverD2WellDefined = coverD2WellDefinedThm{family.Add(registry.ProofEntry{
	Name: "CoverD2WellDefined",
	Key:  "prop_a760976b8d59d242",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B). " +
				"∀p q:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"        prod(set(num), set(num)) → B → D).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:U⟩)",
				"p ∈ cover_comparison_codes(R, S, f, N, g, v)",
				"q ∈ cover_comparison_codes(R, S, f, N, g, v)",
				"cover_local_class⟨U:U⟩(R, S, f, N, g, v)(p) = cover_local_class⟨U:U⟩(R, S, f, N, g, v)(q)",
			},
			Conclusion: "intersection_cech_complex(R, " +
				"    cover_derivation_module(R, S, f, N), " +
				"    cover_derivation_restriction(R, S, f, N, g, v)).add( " +
				"    cover_triple_defect(R, S, f, N, g, v)(p), " +
				"    intersection_cech_complex(R, " +
				"        cover_derivation_module(R, S, f, N), " +
				"        cover_derivation_restriction(R, S, f, N, g, v)).neg( " +
				"        cover_triple_defect(R, S, f, N, g, v)(q))) ∈ " +
				"coboundaries(intersection_cech_complex(R, " +
				"        cover_derivation_module(R, S, f, N), " +
				"        cover_derivation_restriction(R, S, f, N, g, v)), " +
				"    2) ∧ " +
				"cover_d2⟨U:U⟩(R, S, f, N, g, v)(cover_local_class⟨U:U⟩(R, S, f, N, g, v)(p)) = " +
				"left_coset(intersection_cech_complex(R, " +
				"        cover_derivation_module(R, S, f, N), " +
				"        cover_derivation_restriction(R, S, f, N, g, v)).add, " +
				"    cover_triple_defect(R, S, f, N, g, v)(p), " +
				"    coboundaries(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        2))",
		},
		"Choose local marked isomorphisms between the two representatives. Changing the pair comparison "+
			"maps gives a derivation 1-cochain, whose Cech boundary is the change in the triple defect."),
	Deps: []registry.EntryLike{
		CoverTripleDefectCocycle,
		CoverLocalClasses,
		coverD2Def,
		definable_deformation.FactorSetIsoIffBoundary,
	},
	Reading: "Choose local marked isomorphisms between the two " +
		"representatives. Changing the pair comparison maps gives a derivation " +
		"1-cochain, whose Cech boundary is the change in the triple defect.",
})}

var CoverExtensionExactSequence = coverExtensionExactSequenceThm{family.Add(registry.ProofEntry{
	Name: "CoverExtensionExactSequence",
	Key:  "prop_f818f01936ca3fa0",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:U⟩)",
			},
			Conclusion: "group_homomorphism(module_additive_group(cohomology_module( " +
				"            intersection_cech_complex(R, " +
				"                cover_derivation_module(R, S, f, N), " +
				"                cover_derivation_restriction(R, S, f, N, g, v)), " +
				"            1)), " +
				"    quotient_group( " +
				"        restrict_group(cover_code_ambient(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"        cover_boundaries(R, S, f, N, g, v)), " +
				"    induced_map(λc:(prod(num, num → num) → B → D). " +
				"            left_coset(cover_code_ambient(R, S, N).mul, " +
				"                cover_glue_code(R, S, f, N, g, v)(c), " +
				"                cover_boundaries(R, S, f, N, g, v)))) ∧ " +
				"injective_on(cohomology(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        1), " +
				"    induced_map(λc:(prod(num, num → num) → B → D). " +
				"            left_coset(cover_code_ambient(R, S, N).mul, " +
				"                cover_glue_code(R, S, f, N, g, v)(c), " +
				"                cover_boundaries(R, S, f, N, g, v)))) ∧ " +
				"group_homomorphism(quotient_group( " +
				"        restrict_group(cover_code_ambient(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"        cover_boundaries(R, S, f, N, g, v)), " +
				"    module_additive_group(cohomology_module(intersection_cech_complex(R, " +
				"                cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
				"                cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)), " +
				"            0)), " +
				"    induced_map(cover_local_class⟨U:U⟩(R, S, f, N, g, v))) ∧ " +
				"group_homomorphism(module_additive_group(cohomology_module(intersection_cech_complex(R, " +
				"                cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
				"                cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)), " +
				"            0)), " +
				"    module_additive_group(cohomology_module(intersection_cech_complex(R, " +
				"                cover_derivation_module(R, S, f, N), " +
				"                cover_derivation_restriction(R, S, f, N, g, v)), " +
				"            2)), " +
				"    cover_d2⟨U:U⟩(R, S, f, N, g, v)) ∧ " +
				"image(induced_map(λc:(prod(num, num → num) → B → D). " +
				"            left_coset(cover_code_ambient(R, S, N).mul, " +
				"                cover_glue_code(R, S, f, N, g, v)(c), " +
				"                cover_boundaries(R, S, f, N, g, v))), " +
				"    cohomology(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        1)) = " +
				"{c:set(prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"            prod(set(num), set(num)) → B → D)) | " +
				"    c ∈ " +
				"    left_cosets(cover_code_ambient(R, S, N).mul, " +
				"        cover_extension_codes(R, S, f, N, g, v), " +
				"        cover_boundaries(R, S, f, N, g, v)) ∧ " +
				"    induced_map(cover_local_class⟨U:U⟩(R, S, f, N, g, v))(c) = " +
				"    coboundaries(intersection_cech_complex(R, " +
				"            cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
				"            cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)), " +
				"        0)} ∧ " +
				"image(induced_map(cover_local_class⟨U:U⟩(R, S, f, N, g, v)), " +
				"    left_cosets(cover_code_ambient(R, S, N).mul, " +
				"        cover_extension_codes(R, S, f, N, g, v), " +
				"        cover_boundaries(R, S, f, N, g, v))) = " +
				"{a:set(prod(num, num → num) → set(U → D)) | " +
				"    a ∈ " +
				"    cohomology(intersection_cech_complex(R, " +
				"            cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
				"            cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)), " +
				"        0) ∧ " +
				"    cover_d2⟨U:U⟩(R, S, f, N, g, v)(a) = " +
				"    coboundaries(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        2)}",
		},
		"Split local extensions glue by derivation cocycles; changing local splittings gives "+
			"exactly a boundary. A compatible local family glues exactly when its triple defect is "+
			"a boundary, which can be killed by changing the pair comparison maps. The least-index "+
			"construction converts the resulting gluing to an actual finite-intersection diagram."),
	Deps: []registry.EntryLike{
		coverGlueCodeDef,
		CoverD2WellDefined,
		CoverExtensionIsoIffBoundary,
		CoverExtensionExtraction,
	},
	Reading: "This is 0→H1(Der)→Exal→H0(T1)→H2(Der); no surjectivity of the last map is asserted.",
})}

var CoverLocalClassesPolishCover = coverLocalClassesPolishCoverThm{family.Add(registry.ProofEntry{
	Name: "CoverLocalClassesPolishCover",
	Key:  "prop_d5482901ece1cb28",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"countable(R.carrier)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ countable(S(σ).carrier) ∧ countable(N(σ).carrier)",
			},
			Conclusion: "polish_cover_on( " +
				"    restrict_group(cover_code_ambient(R, S, N), cover_comparison_codes(R, S, f, N, g, v)), " +
				"    subtopology(cover_code_topology(R, S, N), cover_comparison_codes(R, S, f, N, g, v)), " +
				"    cover_local_kernel(R, S, f, N, g, v))",
		},
		"Present the kernel by simultaneous normalized gauges and arbitrary derivations "+
			"on proper inclusion arrows, with zero shears on identity arrows. The formula "+
			"is the gauge coboundary plus an arrow derivation; it is a continuous "+
			"homomorphism from a product of closed Polish groups onto the kernel."),
	Deps: []registry.EntryLike{
		CoverExtensionCodesPolishCover,
		coverLocalKernelDef,
		DerivationPresheafPolish,
		polish_group.ContinuousHomImagePolishable,
	},
	Reading: "The witness-rich source is a cover for H0(T1). No Q3 " +
		"assertion is made for the generally non-Polish T1 quotients.",
})}

var CoverSequenceDefinable = coverSequenceDefinableThm{family.Add(registry.ProofEntry{
	Name: "CoverSequenceDefinable",
	Key:  "prop_c864a6e6e13640f",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{
				"cover_datum(R, S, f, N, g, v, t)",
				"countable(R.carrier)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ countable(S(σ).carrier) ∧ countable(N(σ).carrier)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ cotangent_universe(S(σ), 𝕌⟨A:U⟩)",
			},
			Conclusion: "borel_cover_map(cocycle_group(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        1), " +
				"    cocycle_topology(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        intersection_cech_topologies(cover_derivation_module(R, S, f, N), " +
				"            λσ:set(num). " +
				"                subtopology(cover_derivation_topology(S, N, σ), " +
				"                    cover_derivation_module(R, S, f, N, σ).carrier)), " +
				"        1), " +
				"    coboundaries(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        1), " +
				"    restrict_group(cover_code_ambient(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"    subtopology(cover_code_topology(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"    cover_boundaries(R, S, f, N, g, v), " +
				"    induced_map(λc:(prod(num, num → num) → B → D). " +
				"            left_coset(cover_code_ambient(R, S, N).mul, " +
				"                cover_glue_code(R, S, f, N, g, v)(c), " +
				"                cover_boundaries(R, S, f, N, g, v)))) ∧ " +
				"borel_cover_map( " +
				"    restrict_group(cover_code_ambient(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"    subtopology(cover_code_topology(R, S, N), cover_extension_codes(R, S, f, N, g, v)), " +
				"    cover_boundaries(R, S, f, N, g, v), " +
				"    restrict_group(cover_code_ambient(R, S, N), cover_comparison_codes(R, S, f, N, g, v)), " +
				"    subtopology(cover_code_topology(R, S, N), cover_comparison_codes(R, S, f, N, g, v)), " +
				"    cover_local_kernel(R, S, f, N, g, v), " +
				"    induced_map(λp:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"                prod(set(num), set(num)) → B → D). " +
				"            left_coset(cover_code_ambient(R, S, N).mul, " +
				"                p, " +
				"                cover_local_kernel(R, S, f, N, g, v)))) ∧ " +
				"borel_cover_map( " +
				"    restrict_group(cover_code_ambient(R, S, N), cover_comparison_codes(R, S, f, N, g, v)), " +
				"    subtopology(cover_code_topology(R, S, N), cover_comparison_codes(R, S, f, N, g, v)), " +
				"    cover_local_kernel(R, S, f, N, g, v), " +
				"    cocycle_group(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        2), " +
				"    cocycle_topology(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        intersection_cech_topologies(cover_derivation_module(R, S, f, N), " +
				"            λσ:set(num). " +
				"                subtopology(cover_derivation_topology(S, N, σ), " +
				"                    cover_derivation_module(R, S, f, N, σ).carrier)), " +
				"        2), " +
				"    coboundaries(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        2), " +
				"    induced_map(λp:prod(set(num) → prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)), " +
				"                prod(set(num), set(num)) → B → D). " +
				"            left_coset(intersection_cech_complex(R, " +
				"                    cover_derivation_module(R, S, f, N), " +
				"                    cover_derivation_restriction(R, S, f, N, g, v)).add, " +
				"                cover_triple_defect(R, S, f, N, g, v)(p), " +
				"                coboundaries(intersection_cech_complex(R, " +
				"                        cover_derivation_module(R, S, f, N), " +
				"                        cover_derivation_restriction(R, S, f, N, g, v)), " +
				"                    2))))",
		},
		"The three lifts are the explicit split gluing map, inclusion of strictly "+
			"compositional codes into comparison codes, and the six-term triple defect. "+
			"Each is continuous and additive. CoverLocalClasses identifies the middle "+
			"target with H0(T1), and CoverD2WellDefined identifies the last map with d2."),
	Deps: []registry.EntryLike{
		CoverExtensionExactSequence,
		CoverLocalClassesPolishCover,
		DerivationPresheafPolish,
		CoverExtensionCodesPolishCover,
		polish_group.BorelLiftModuloSubgroup,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "The three lifts are the explicit split gluing map, inclusion of " +
		"strictly compositional codes into comparison codes, and the six-term triple " +
		"defect. Each is continuous and additive. CoverLocalClasses identifies the middle " +
		"target with H0(T1), and CoverD2WellDefined identifies the last map with d2.",
})}

var CoverExtensionAutomorphisms = coverExtensionAutomorphismsThm{family.Add(registry.ProofEntry{
	Name: "CoverExtensionAutomorphisms",
	Key:  "prop_3962d519087c2036",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:(set(num) → ring_ops(B)). " +
				"∀f:(set(num) → A → B). " +
				"∀N:(set(num) → module_ops(B, D)). " +
				"∀g:(set(num) → set(num) → B → B). " +
				"∀v:(set(num) → set(num) → D → D). " +
				"∀t:(set(num) → set(num) → B).",
			Hypotheses: []string{"cover_datum(R, S, f, N, g, v, t)"},
			Conclusion: "group_isomorphism(restrict_group(cover_gauge_group(S, N), " +
				"        {h:(set(num) → B → D) | " +
				"            h ∈ cover_gauge_group(S, N).carrier ∧ " +
				"            cover_coboundary(R, S, f, N, g, v)(h) = cover_code_ambient(R, S, N).one}), " +
				"    cocycle_group(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        0), " +
				"    λh:(set(num) → B → D). λw:prod(num, num → num). " +
				"        COND(w ∈ ordered_cech_indices(0), " +
				"            h(cech_support(w)), " +
				"            cover_derivation_module(R, S, f, N)(cech_support(w)).zero))",
		},
		"The kernel of the simultaneous gauge action consists of derivations "+
			"compatible with all restrictions. Restrict to singleton charts to get a Cech "+
			"zero cocycle; extend uniquely to every intersection for the inverse. These "+
			"shears are precisely the marked automorphisms of any extension diagram."),
	Deps: []registry.EntryLike{
		coverCoboundaryDef,
		coverDerivationModuleDef,
		DerivationPresheaf,
		definable_deformation.FactorSetShear,
	},
	Reading: "The kernel of the simultaneous gauge action consists of derivations " +
		"compatible with all restrictions. Restrict to singleton charts to get a Cech " +
		"zero cocycle; extend uniquely to every intersection for the inverse. These " +
		"shears are precisely the marked automorphisms of any extension diagram.",
})}
