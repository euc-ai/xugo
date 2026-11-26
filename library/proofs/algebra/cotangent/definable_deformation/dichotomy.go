package definable_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/borel_subgroup"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/registry"
)

var ExalCountableOrContinuum = exalCountableOrContinuumThm{family.Add(registry.ProofEntry{
	Name: "ExalCountableOrContinuum",
	Key:  "prop_1e43295dff76726f",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
			},
			Conclusion: "(countable(left_cosets(factor_set_group(R, S, f, N).mul, " +
				"            factor_set_group(R, S, f, N).carrier, " +
				"            factor_set_boundaries(R, S, f, N))) ⇔ " +
				"    factor_set_boundaries(R, S, f, N) ∈ " +
				"    subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N))) ∧ " +
				"(countable(left_cosets(factor_set_group(R, S, f, N).mul, " +
				"            factor_set_group(R, S, f, N).carrier, " +
				"            factor_set_boundaries(R, S, f, N))) ∨ " +
				"    card_le(𝕌⟨A:set(num)⟩, " +
				"        left_cosets(factor_set_group(R, S, f, N).mul, " +
				"            factor_set_group(R, S, f, N).carrier, " +
				"            factor_set_boundaries(R, S, f, N))))",
		},
		"Read PolishCoverCountableIffOpen on FactorSetCodesPolishCover. "+
			"FactorSetAQDefinableIso identifies these classes with AQ degree one."),
	Deps: []registry.EntryLike{
		FactorSetCodesPolishCover,
		borel_subgroup.PolishCoverCountableIffOpen,
	},
	Reading: "Read PolishCoverCountableIffOpen on FactorSetCodesPolishCover. " +
		"FactorSetAQDefinableIso identifies these classes with AQ degree one.",
})}

var ExalClosedBoundaryPolish = exalClosedBoundaryPolishThm{family.Add(registry.ProofEntry{
	Name: "ExalClosedBoundaryPolish",
	Key:  "prop_707e8ff176772fc3",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
				"closed_in(subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
					"    factor_set_boundaries(R, S, f, N))",
			},
			Conclusion: "polish_abelian_group( " +
				"    quotient_group(factor_set_group(R, S, f, N), factor_set_boundaries(R, S, f, N)), " +
				"    quotient_topology(subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"        λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"            left_coset(factor_set_group(R, S, f, N).mul, z, factor_set_boundaries(R, S, f, N))))",
		},
		"Apply ClosedCoverQuotientPolish to the actual boundary subgroup."),
	Deps:    []registry.EntryLike{FactorSetCodesPolishCover, borel_subgroup.ClosedCoverQuotientPolish},
	Reading: "Apply ClosedCoverQuotientPolish to the actual boundary subgroup.",
})}

var FiniteCoefficientExalCompact = finiteCoefficientExalCompactThm{family.Add(registry.ProofEntry{
	Name: "FiniteCoefficientExalCompact",
	Key:  "prop_8a910ecfd0150bdb",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). ∀S:ring_ops(B). ∀f:(A → B). ∀N:module_ops(B, D).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"finite(N.carrier)",
			},
			Conclusion: "compact_in(subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    factor_set_codes(R, S, f, N)) ∧ " +
				"compact_in(subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    factor_set_boundaries(R, S, f, N)) ∧ " +
				"closed_in(subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    factor_set_boundaries(R, S, f, N)) ∧ " +
				"polish_abelian_group( " +
				"    quotient_group(factor_set_group(R, S, f, N), factor_set_boundaries(R, S, f, N)), " +
				"    quotient_topology(subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"        λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"            left_coset(factor_set_group(R, S, f, N).mul, z, factor_set_boundaries(R, S, f, N))))",
		},
		"All coefficient factors are finite discrete compact spaces. Codes and "+
			"normalized gauges are closed in their products; the continuous coboundary "+
			"image is compact, hence closed, and ExalClosedBoundaryPolish applies."),
	Deps: []registry.EntryLike{
		FactorSetCodesClosed,
		FactorSetCoboundaryContinuous,
		ExalClosedBoundaryPolish,
	},
	Reading: "All coefficient factors are finite discrete compact spaces. Codes " +
		"and normalized gauges are closed in their products; the continuous coboundary " +
		"image is compact, hence closed, and ExalClosedBoundaryPolish applies.",
})}
