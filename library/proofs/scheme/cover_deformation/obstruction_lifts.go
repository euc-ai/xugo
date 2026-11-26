package cover_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_andre_quillen"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/registry"
)

var coverThickeningTopologyDef = coverThickeningTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "coverThickeningTopologyDef",
	Key:   "prop_c15b8fb19ff33ab2",
	Const: "cover_thickening_topology",
	Type: "ring_ops(A) → " +
		"ring_ops(F) → " +
		"(A → F) → " +
		"(set(num) → module_ops(B, D)) → " +
		"set(set(set(num) → A → D))",
	Equations: []string{
		"∀R:ring_ops(A). ∀R₀:ring_ops(F). ∀p₀:(A → F). ∀N:(set(num) → module_ops(B, D)). " +
			"    cover_thickening_topology(R, R₀, p₀, N) = " +
			"    indexed_product_topology(intersection_indices, " +
			"        λσ:set(num). λa:A. N(σ).zero, " +
			"        λσ:set(num). " +
			"            indexed_discrete_topology(ring_kernel(R₀.zero, R.carrier, p₀), " +
			"                λa:A. N(σ).zero, " +
			"                λa:A. N(σ).carrier))",
	},
	Deps: []registry.EntryLike{},
	Reading: "The pointwise topology on compatible thickening-ideal " +
		"coefficient maps; values off the ideal and inactive intersections are zero."})}

var CoverLocalObstructionBorelLift = coverLocalObstructionBorelLiftThm{family.Add(registry.ProofEntry{
	Name: "CoverLocalObstructionBorelLift",
	Key:  "prop_909e00e462491b9b",
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
				"countable(R.carrier)",
				"countable(R₀.carrier)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ countable(S(σ).carrier) ∧ countable(N(σ).carrier)",
			},
			Conclusion: "∃H:((set(num) → A → D) → set(num) → U → D). " +
				"    borel_map(subtopology(cover_thickening_topology(R, R₀, p₀, N), " +
				"            {j:(set(num) → A → D) | " +
				"                j ∈ ⋃cover_thickening_topology(R, R₀, p₀, N) ∧ " +
				"                cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, j)}), " +
				"        indexed_product_topology(intersection_indices, " +
				"            λσ:set(num). λx:U. N(σ).zero, " +
				"            λσ:set(num). " +
				"                cocycle_topology(cotangent_cochain⟨U:U⟩(R₀, S(σ), u(σ), S(σ), λy:B. y, N(σ)), " +
				"                    aq_topologies(R₀, S(σ), N(σ)), " +
				"                    2)), " +
				"        H) ∧ " +
				"    (∀j:(set(num) → A → D). " +
				"        j ∈ " +
				"        {j:(set(num) → A → D) | " +
				"            j ∈ ⋃cover_thickening_topology(R, R₀, p₀, N) ∧ " +
				"            cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, j)} ⇒ " +
				"        (∀σ:set(num). " +
				"            σ ∈ intersection_indices ⇒ " +
				"            left_coset(cotangent_cochain⟨U:U⟩(R₀, S(σ), u(σ), S(σ), λy:B. y, N(σ)).add, " +
				"                H(j, σ), " +
				"                coboundaries(cotangent_cochain⟨U:U⟩(R₀, S(σ), u(σ), S(σ), λy:B. y, N(σ)), 2)) = " +
				"            algebra_deformation_obstruction⟨U:U⟩(R, R₀, p₀, S(σ), u(σ), N(σ), j(σ))))",
		},
		"Push the fixed thickening extension along the varying coefficient maps, using "+
			"finite-coordinate conormal evaluation, then use the Borel transitivity connecting lift at "+
			"each chart. The countable product of these lifts represents the compatible first obstruction."),
	Deps: []registry.EntryLike{
		coverThickeningTopologyDef,
		CoverLocalObstruction,
		definable_andre_quillen.AQTransitivityDefinable,
		definable_deformation.FactorSetAQDefinableIso,
	},
	Reading: "The target is a product of actual AQ cocycle groups. " +
		"No topology is assigned directly to the quotient T2 sections.",
})}

var CoverMatchingObstructionBorelLift = coverMatchingObstructionBorelLiftThm{family.Add(registry.ProofEntry{
	Name: "CoverMatchingObstructionBorelLift",
	Key:  "prop_f0c5ef69e4b0357f",
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
				"countable(R.carrier)",
				"countable(R₀.carrier)",
				"∀σ:set(num). σ ∈ intersection_indices ⇒ countable(S(σ).carrier) ∧ countable(N(σ).carrier)",
			},
			Conclusion: "∃H:((set(num) → A → D) → prod(num, num → num) → U → D). " +
				"    borel_map(subtopology(cover_thickening_topology(R, R₀, p₀, N), " +
				"            {j:(set(num) → A → D) | " +
				"                j ∈ " +
				"                {j:(set(num) → A → D) | " +
				"                    j ∈ ⋃cover_thickening_topology(R, R₀, p₀, N) ∧ " +
				"                    cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, j)} ∧ " +
				"                ¬(cover_local_deformations(R, R₀, p₀, S, u, N, j) = ∅)}), " +
				"        indexed_product_topology(ordered_cech_indices(1), " +
				"            λw:prod(num, num → num). λx:U. N(cech_support(w)).zero, " +
				"            λw:prod(num, num → num). " +
				"                cocycle_topology(cotangent_cochain⟨U:U⟩(R₀, " +
				"                        S(cech_support(w)), " +
				"                        u(cech_support(w)), " +
				"                        S(cech_support(w)), " +
				"                        λy:B. y, " +
				"                        N(cech_support(w))), " +
				"                    aq_topologies(R₀, S(cech_support(w)), N(cech_support(w))), " +
				"                    1)), " +
				"        H) ∧ " +
				"    (∀j:(set(num) → A → D). " +
				"        j ∈ " +
				"        {j:(set(num) → A → D) | " +
				"            j ∈ " +
				"            {j:(set(num) → A → D) | " +
				"                j ∈ ⋃cover_thickening_topology(R, R₀, p₀, N) ∧ " +
				"                cover_deformation_datum(R, R₀, p₀, S, u, N, g, v, t, j)} ∧ " +
				"            ¬(cover_local_deformations(R, R₀, p₀, S, u, N, j) = ∅)} ⇒ " +
				"        (λw:prod(num, num → num). " +
				"            left_coset(cotangent_cochain⟨U:U⟩(R₀, " +
				"                    S(cech_support(w)), " +
				"                    u(cech_support(w)), " +
				"                    S(cech_support(w)), " +
				"                    λy:B. y, " +
				"                    N(cech_support(w))).add, " +
				"                H(j, w), " +
				"                coboundaries(cotangent_cochain⟨U:U⟩(R₀, " +
				"                        S(cech_support(w)), " +
				"                        u(cech_support(w)), " +
				"                        S(cech_support(w)), " +
				"                        λy:B. y, " +
				"                        N(cech_support(w))), " +
				"                    1))) ∈ " +
				"        cocycles(intersection_cech_complex(R₀, " +
				"                cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
				"                cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)), " +
				"            1) ∧ " +
				"        left_coset(intersection_cech_complex(R₀, " +
				"                cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
				"                cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)).add, " +
				"            λw:prod(num, num → num). " +
				"                left_coset(cotangent_cochain⟨U:U⟩(R₀, " +
				"                        S(cech_support(w)), " +
				"                        u(cech_support(w)), " +
				"                        S(cech_support(w)), " +
				"                        λy:B. y, " +
				"                        N(cech_support(w))).add, " +
				"                    H(j, w), " +
				"                    coboundaries(cotangent_cochain⟨U:U⟩(R₀, " +
				"                            S(cech_support(w)), " +
				"                            u(cech_support(w)), " +
				"                            S(cech_support(w)), " +
				"                            λy:B. y, " +
				"                            N(cech_support(w))), " +
				"                        1)), " +
				"            coboundaries(intersection_cech_complex(R₀, " +
				"                    cover_aq_module⟨U:U⟩(R₀, S, u, N, 1), " +
				"                    cover_aq_restriction⟨U:U⟩(R₀, S, u, N, g, v, 1)), " +
				"                1)) = " +
				"        cover_matching_obstruction⟨U:U⟩(R, R₀, p₀, S, u, N, g, v, t, j))",
		},
		"The map sending local factor-set codes to their rho values on the thickening ideal "+
			"is a continuous homomorphism. Its image is Polishable, with the trace Borel sets, so "+
			"choose Borel local deformation lifts. Localize and subtract the chosen factor-set "+
			"codes. Their difference has zero rho on the thickening ideal, so the continuous "+
			"inverse of DeformationKernelIsReducedBase descends it to the reduced base; the "+
			"forward factor-set-to-AQ lift then gives an AQ cocycle. CoverMatchingObstruction "+
			"proves the resulting Cech class is independent of the choices."),
	Deps: []registry.EntryLike{
		CoverMatchingObstruction,
		CoverLocalObstructionBorelLift,
		CoverDeformationCodesCoset,
		definable_deformation.DeformationKernelIsReducedBase,
		definable_deformation.LocalizedCodeContinuous,
		polish_group.ContinuousHomImagePolishable,
		polish_group.ContinuousSurjectionBorelSection,
	},
	Reading: "The second lift is defined on the Borel locus where the first " +
		"obstruction vanishes. It lifts the matching cochain to actual local AQ " +
		"cocycles; its Cech class is the choice-independent obstruction.",
})}

var CoverDeformationGluingFiber = coverDeformationGluingFiberThm{family.Add(registry.ProofEntry{
	Name: "CoverDeformationGluingFiber",
	Key:  "prop_e86dd63d44a389bd",
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
				"q ∈ cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι)",
				"r ∈ cover_deformation_codes(R, R₀, p₀, S, u, N, g, v, ι)",
				"cover_local_class⟨U:U⟩(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v)(q) = " +
					"cover_local_class⟨U:U⟩(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v)(r)",
			},
			Conclusion: "∃c:(prod(num, num → num) → B → D). " +
				"    c ∈ " +
				"    cocycles(intersection_cech_complex(R₀, " +
				"            cover_derivation_module(R₀, S, u, N), " +
				"            cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"        1) ∧ " +
				"    cover_code_ambient(R, S, N).mul(r, " +
				"        cover_code_ambient(R, S, N).inv(cover_code_ambient(R, S, N).mul(q, " +
				"                cover_inflate(R, R₀, p₀, S, N)(cover_glue_code(R₀, S, u, N, g, v)(c))))) ∈ " +
				"    cover_boundaries(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v) ∧ " +
				"    (∀d:(prod(num, num → num) → B → D). " +
				"        d ∈ " +
				"        cocycles(intersection_cech_complex(R₀, " +
				"                cover_derivation_module(R₀, S, u, N), " +
				"                cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"            1) ∧ " +
				"        cover_code_ambient(R, S, N).mul(r, " +
				"            cover_code_ambient(R, S, N).inv(cover_code_ambient(R, S, N).mul(q, " +
				"                    cover_inflate(R, R₀, p₀, S, N)(cover_glue_code(R₀, S, u, N, g, v)(d))))) ∈ " +
				"        cover_boundaries(R, S, λσ:set(num). λa:A. u(σ, p₀(a)), N, g, v) ⇒ " +
				"        intersection_cech_complex(R₀, " +
				"            cover_derivation_module(R₀, S, u, N), " +
				"            cover_derivation_restriction(R₀, S, u, N, g, v)).add(c, " +
				"            intersection_cech_complex(R₀, " +
				"                cover_derivation_module(R₀, S, u, N), " +
				"                cover_derivation_restriction(R₀, S, u, N, g, v)).neg(d)) ∈ " +
				"        coboundaries(intersection_cech_complex(R₀, " +
				"                cover_derivation_module(R₀, S, u, N), " +
				"                cover_derivation_restriction(R₀, S, u, N, g, v)), " +
				"            1))",
		},
		"The reduced-base extension class relating two deformations has trivial local classes. "+
			"Exactness identifies it with exactly one H1(Der) class, represented by the split gluing code."),
	Deps: []registry.EntryLike{
		CoverDeformationsTorsor,
		CoverExtensionExactSequence,
		coverGlueCodeDef,
	},
	Reading: "The full torsor is under cover Exal over R₀; after fixing a " +
		"compatible local family, each nonempty gluing fiber is a torsor under H1(Der).",
})}
