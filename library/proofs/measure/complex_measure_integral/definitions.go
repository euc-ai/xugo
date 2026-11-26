package complex_measure_integral

import (
	"github.com/euc-ai/xugo/library/registry"
)

var ComplexMeasurableDef = complexMeasurableDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexMeasurableDef",
	Key:   "prop_2cf3c70e57175fc9",
	Const: "complex_measurable",
	Type:  "set(A) → set(set(A)) → (A → complex) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → complex). " +
			"    complex_measurable(Ω, S, f) ⇔ " +
			"    real_measurable(Ω, S, λx:A. re(f(x))) ∧ real_measurable(Ω, S, λx:A. im(f(x)))",
	},
})}

var ComplexIntegrableDef = complexIntegrableDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexIntegrableDef",
	Key:   "prop_7b6735ddb9eaee1e",
	Const: "complex_integrable",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → (A → complex) → bool",
	Deps:  []registry.EntryLike{ComplexMeasurableDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → complex). " +
			"    complex_integrable(Ω, S, μ, f) ⇔ " +
			"    complex_measurable(Ω, S, f) ∧ real_integrable(Ω, S, μ, λx:A. |f(x)|)",
	},
})}

var ComplexIntegralDef = complexIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexIntegralDef",
	Key:   "prop_dcc966034cbcc2e8",
	Const: "complex_measure_integral",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → (A → complex) → complex",
	Reading: "This is a total function with the conventions of the real integral " +
		"on each component. Its linear and norm laws are asserted on integrable functions.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → complex). " +
			"    complex_measure_integral(Ω, S, μ, f) = " +
			"    complex_of_real(measure_integral(Ω, S, μ, λx:A. re(f(x)))) + " +
			"    complex_i * complex_of_real(measure_integral(Ω, S, μ, λx:A. im(f(x))))",
	},
})}
