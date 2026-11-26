package complex_measure_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var ComplexIntegralLinear = complexIntegralLinearThm{family.Add(registry.ProofEntry{
	Name: "ComplexIntegralLinear",
	Deps: []registry.EntryLike{ComplexMeasurableScale, ComplexMeasurableAdd, ComplexMeasurableAbs},
	Key:  "prop_ed60d09031971aa3",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f g:(A → complex). " +
			"∀c:complex.",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"complex_integrable(Ω, S, μ, f)",
			"complex_integrable(Ω, S, μ, g)",
		},
		Conclusion: "complex_integrable(Ω, S, μ, λx:A. c * f(x) + g(x)) ∧ " +
			"complex_measure_integral(Ω, S, μ, λx:A. c * f(x) + g(x)) = " +
			"c * complex_measure_integral(Ω, S, μ, f) + complex_measure_integral(Ω, S, μ, g)",
	}, "Use absolute-value domination for integrability and real linearity on both components."),
})}

var ComplexIntegralConjugate = complexIntegralConjugateThm{family.Add(registry.ProofEntry{
	Name: "ComplexIntegralConjugate",
	Key:  "prop_13fe51ec778d9e9c",
	Deps: []registry.EntryLike{
		ComplexMeasurableConj,
		measure_integral.IntegralNeg,
		complex_field.PartsConj,
		complex_abs.AbsConj,
		complex_field.ConjAdd,
		complex_field.ConjMul,
		complex_field.ConjOfReal,
		complex_field.ConjI,
	},
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → complex).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "complex_integrable(Ω, S, μ, f)"},
		Conclusion: "complex_integrable(Ω, S, μ, λx:A. complex_conj(f(x))) ∧ " +
			"complex_measure_integral(Ω, S, μ, λx:A. complex_conj(f(x))) = " +
			"complex_conj(complex_measure_integral(Ω, S, μ, f))",
	},
		"Conjugation fixes the real part and negates the imaginary part (PartsConj), "+
			"so the conjugate is measurable (ComplexMeasurableConj), its modulus is that "+
			"of f (AbsConj), and the imaginary integral changes sign (IntegralNeg)."),
})}

var ComplexIntegralBound = complexIntegralBoundThm{family.Add(registry.ProofEntry{
	Name: "ComplexIntegralBound",
	Deps: []registry.EntryLike{ComplexIntegralLinear},
	Key:  "prop_8417c6f23f45819d",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → complex).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "complex_integrable(Ω, S, μ, f)"},
		Conclusion: "|complex_measure_integral(Ω, S, μ, f)| ≤ measure_integral(Ω, S, μ, λx:A. |f(x)|)",
	},
		"Multiply by a unit scalar making the integral nonnegative "+
			"real and compare real parts pointwise with the modulus."),
})}

var ComplexIntegralAE = complexIntegralAEThm{family.Add(registry.ProofEntry{
	Name: "ComplexIntegralAE",
	Deps: []registry.EntryLike{measure_integral.IntegrableAE, ComplexMeasurableAbs},
	Key:  "prop_3aee4521ec88b219",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → complex).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"complex_measurable(Ω, S, f)",
			"complex_measurable(Ω, S, g)",
			"measure_ae_eq(Ω, S, μ, f, g)",
		},
		Conclusion: "(complex_integrable(Ω, S, μ, f) ⇔ complex_integrable(Ω, S, μ, g)) ∧ " +
			"complex_measure_integral(Ω, S, μ, f) = complex_measure_integral(Ω, S, μ, g)",
	}, "Apply real a.e. invariance to both components and the modulus."),
})}

var SquareProductIntegrable = squareProductIntegrableThm{family.Add(registry.ProofEntry{
	Name: "SquareProductIntegrable",
	Deps: []registry.EntryLike{ComplexMeasurableConj, ComplexMeasurableMul, ComplexMeasurableAbs},
	Key:  "prop_4c8f7b7e02c1bbd2",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → complex).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"complex_measurable(Ω, S, f)",
			"complex_measurable(Ω, S, g)",
			"real_integrable(Ω, S, μ, λx:A. |f(x)| * |f(x)|)",
			"real_integrable(Ω, S, μ, λx:A. |g(x)| * |g(x)|)",
		},
		Conclusion: "complex_integrable(Ω, S, μ, λx:A. f(x) * complex_conj(g(x)))",
	},
		"The scalar estimate 2 |f| |g| ≤ |f|² + |g|² gives "+
			"integrability before any Hilbert-space structure is used."),
})}

var ComplexRealEmbedding = complexRealEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "ComplexRealEmbedding",
	Key:  "prop_af9b6deab52d563e",
	Deps: []registry.EntryLike{
		measurable_function.RealMeasurableConst,
		nonneg_integral.NonnegIntegralZero,
		complex_abs.AbsOfReal,
		complex_field.PartsOfReal,
		measurable_function.RealMeasurableAbs,
	},
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "real_integrable(Ω, S, μ, f)"},
		Conclusion: "complex_integrable(Ω, S, μ, λx:A. complex_of_real(f(x))) ∧ " +
			"complex_measure_integral(Ω, S, μ, λx:A. complex_of_real(f(x))) = " +
			"complex_of_real(measure_integral(Ω, S, μ, f))",
	},
		"The real part is f, the imaginary part is zero, and the complex modulus "+
			"is the real absolute value (AbsOfReal). The zero part is measurable "+
			"(RealMeasurableConst) and integrates to zero (NonnegIntegralZero)."),
})}

var ComplexDominatedConvergenceAE = complexDominatedConvergenceAEThm{family.Add(registry.ProofEntry{
	Name: "ComplexDominatedConvergenceAE",
	Deps: []registry.EntryLike{
		integral_convergence.DominatedConvergenceAE,
		ComplexMeasurableAbs,
	},
	Key: "prop_c9c84417b3908b1b",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(num → A → complex). " +
			"∀g:(A → complex). " +
			"∀h:(A → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"∀n:num. complex_measurable(Ω, S, f(n))",
			"complex_measurable(Ω, S, g)",
			"real_integrable(Ω, S, μ, h)",
			"measure_ae(Ω, S, μ, λx:A. real_converges_to(λn:num. |f(n, x) - g(x)|, &0))",
			"∀n:num. measure_ae(Ω, S, μ, λx:A. |f(n, x)| ≤ h(x))",
		},
		Conclusion: "complex_integrable(Ω, S, μ, g) ∧ " +
			"(∀n:num. complex_integrable(Ω, S, μ, f(n))) ∧ " +
			"real_converges_to( " +
			"    λn:num. |complex_measure_integral(Ω, S, μ, f(n)) - complex_measure_integral(Ω, S, μ, g)|, &0)",
	},
		"Apply real dominated convergence to the real and imaginary components and combine their limits."),
})}
