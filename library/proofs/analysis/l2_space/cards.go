package l2_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/analysis/lp_space"
	"github.com/euc-ai/xugo/library/proofs/measure/complex_measure_integral"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/registry"
)

var L2SemiInner = l2SemiInnerThm{family.Add(registry.ProofEntry{
	Name: "L2SemiInner",
	Deps: []registry.EntryLike{
		complex_measure_integral.SquareProductIntegrable,
		complex_measure_integral.ComplexIntegralLinear,
		complex_measure_integral.ComplexIntegralConjugate,
	},
	Key: "prop_56bd5694a010cee0",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)"},
		Conclusion: "complex_semi_inner(lp_function_module(Ω, S, μ, &2), l2_function_inner(Ω, S, μ)) ∧ " +
			"(∀f:(A → complex). " +
			"    f ∈ lp_functions(Ω, S, μ, &2) ⇒ " +
			"    hilbert_norm(l2_function_inner(Ω, S, μ), f) = lp_seminorm(Ω, S, μ, &2, f))",
	},
		"First use the scalar square-product estimate to establish integrability. Integral linearity, "+
			"conjugation and positivity give the semidefinite form; its diagonal is the squared L2 seminorm."),
})}

var L2Hilbert = l2HilbertThm{family.Add(registry.ProofEntry{
	Name:    "L2Hilbert",
	Reading: "It holds for any measure; no finiteness or sigma-finiteness is read.",
	Deps: []registry.EntryLike{
		L2SemiInner,
		hilbert_space.SemiInnerQuotient,
		lp_space.LpBanach,
		lp_space.LpSeminorm,
	},
	Key: "prop_66beaec5858278d",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)"},
		Conclusion: "complex_hilbert_space(lp_module(Ω, S, μ, &2), l2_inner(Ω, S, μ)) ∧ " +
			"(∀Q:set(A → complex). " +
			"    Q ∈ lp_module(Ω, S, μ, &2).carrier ⇒ " +
			"    hilbert_norm(l2_inner(Ω, S, μ), Q) = lp_norm(Ω, S, μ, &2, Q))",
	},
		"Descend the semi-inner product through its seminorm kernel, which is exactly the "+
			"common null submodule. Lp completeness at p=2 supplies the Hilbert completeness."),
})}

var L2InnerClasses = l2InnerClassesThm{family.Add(registry.ProofEntry{
	Name: "L2InnerClasses",
	Deps: []registry.EntryLike{L2SemiInner, equivalence.InducedMapClass},
	Key:  "prop_6e518947df8abb52",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → complex).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"f ∈ lp_functions(Ω, S, μ, &2)",
			"g ∈ lp_functions(Ω, S, μ, &2)",
		},
		Conclusion: "l2_inner(Ω, S, μ, ae_class(Ω, S, μ, f), ae_class(Ω, S, μ, g)) = " +
			"l2_function_inner(Ω, S, μ, f, g)",
	}, "Use induced-map evaluation in each variable of the quotient inner product."),
})}
