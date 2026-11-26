package cover_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/borel_subgroup"
	"github.com/euc-ai/xugo/library/proofs/topology/cech_cohomology"
	"github.com/euc-ai/xugo/library/registry"
)

var coverRepeatedDef = coverRepeatedDefThm{family.Define(registry.DefEntry{
	Name:  "coverRepeatedDef",
	Key:   "prop_d6fc274dd5468016",
	Const: "cover_repeated",
	Type: "(set(num) → ring_ops(B)) → " +
		"(set(num) → A → B) → " +
		"(set(num) → module_ops(B, D)) → " +
		"(set(num) → set(num) → B → B) → " +
		"(set(num) → set(num) → D → D) → " +
		"(num → num) → " +
		"bool",
	Equations: []string{
		"∀S:(set(num) → ring_ops(B)). " +
			"∀f:(set(num) → A → B). " +
			"∀N:(set(num) → module_ops(B, D)). " +
			"∀g:(set(num) → set(num) → B → B). " +
			"∀v:(set(num) → set(num) → D → D). " +
			"∀r:(num → num). " +
			"    cover_repeated(S, f, N, g, v, r) ⇔ " +
			"    (∀σ:set(num). " +
			"        σ ∈ intersection_indices ⇒ " +
			"        S(σ) = S(image(r, σ)) ∧ f(σ) = f(image(r, σ)) ∧ N(σ) = N(image(r, σ))) ∧ " +
			"    (∀σ τ:set(num). " +
			"        σ ∈ intersection_indices ∧ τ ∈ intersection_indices ∧ σ ⊆ τ ⇒ " +
			"        g(σ, τ) = g(image(r, σ), image(r, τ)) ∧ v(σ, τ) = v(image(r, σ), image(r, τ)))",
	},
	Deps:    []registry.EntryLike{},
	Reading: "Strictly repeated chart data indexed by a retraction of num onto a finite set."})}

var TwoChartCoverExact = twoChartCoverExactThm{family.Add(registry.ProofEntry{
	Name: "TwoChartCoverExact",
	Key:  "prop_945b6ff0ebcdf7ea",
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
				"cover_repeated(S, f, N, g, v, λi:num. COND(i = 0, 0, 1))",
			},
			Conclusion: "cohomology(intersection_cech_complex(R, " +
				"        cover_derivation_module(R, S, f, N), " +
				"        cover_derivation_restriction(R, S, f, N, g, v)), " +
				"    2) = " +
				"{coboundaries(intersection_cech_complex(R, " +
				"            cover_derivation_module(R, S, f, N), " +
				"            cover_derivation_restriction(R, S, f, N, g, v)), " +
				"        2)} ∧ " +
				"image(induced_map(cover_local_class⟨U:U⟩(R, S, f, N, g, v)), " +
				"    left_cosets(cover_code_ambient(R, S, N).mul, " +
				"        cover_extension_codes(R, S, f, N, g, v), " +
				"        cover_boundaries(R, S, f, N, g, v))) = " +
				"cohomology(intersection_cech_complex(R, " +
				"        cover_aq_module⟨U:U⟩(R, S, f, N, 1), " +
				"        cover_aq_restriction⟨U:U⟩(R, S, f, N, g, v, 1)), " +
				"    0)",
		},
		"FiniteRepeatedCoverVanishing kills H2(Der); CoverExtensionExactSequence then makes the "+
			"local-class map onto. Its kernel remains H1(Der), giving the two-chart short exact sequence."),
	Deps: []registry.EntryLike{
		coverRepeatedDef,
		cech_cohomology.FiniteRepeatedCoverVanishing,
		CoverExtensionExactSequence,
	},
	Reading: "FiniteRepeatedCoverVanishing kills H2(Der); CoverExtensionExactSequence then makes " +
		"the local-class map onto. Its kernel remains H1(Der), giving the two-chart short exact sequence.",
})}

var CoverExalCountableOrContinuum = coverExalCountableOrContinuumThm{family.Add(registry.ProofEntry{
	Name: "CoverExalCountableOrContinuum",
	Key:  "prop_2746b6fafc8c7b38",
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
			Conclusion: "(countable(left_cosets(cover_code_ambient(R, S, N).mul, " +
				"            cover_extension_codes(R, S, f, N, g, v), " +
				"            cover_boundaries(R, S, f, N, g, v))) ⇔ " +
				"    cover_boundaries(R, S, f, N, g, v) ∈ " +
				"    subtopology(cover_code_topology(R, S, N), cover_extension_codes(R, S, f, N, g, v))) ∧ " +
				"(countable(left_cosets(cover_code_ambient(R, S, N).mul, " +
				"            cover_extension_codes(R, S, f, N, g, v), " +
				"            cover_boundaries(R, S, f, N, g, v))) ∨ " +
				"    card_le(𝕌⟨A:set(num)⟩, " +
				"        left_cosets(cover_code_ambient(R, S, N).mul, " +
				"            cover_extension_codes(R, S, f, N, g, v), " +
				"            cover_boundaries(R, S, f, N, g, v))))",
		},
		"Apply the common Polish-cover countability and "+
			"Baire dichotomy to the actual extension code cover."),
	Deps: []registry.EntryLike{
		CoverExtensionCodesPolishCover,
		borel_subgroup.PolishCoverCountableIffOpen,
	},
	Reading: "Apply the common Polish-cover countability " +
		"and Baire dichotomy to the actual extension code cover.",
})}
