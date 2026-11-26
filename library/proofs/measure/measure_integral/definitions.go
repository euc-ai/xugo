package measure_integral

import (
	"github.com/euc-ai/xugo/library/registry"
)

var RealIntegrableDef = realIntegrableDefThm{family.Define(registry.DefEntry{
	Name:  "RealIntegrableDef",
	Key:   "prop_fc36964771203865",
	Const: "real_integrable",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → (A → real) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real). " +
			"    real_integrable(Ω, S, μ, f) ⇔ " +
			"    real_measurable(Ω, S, f) ∧ " +
			"    nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|f(x)|)) ≠ extended_infinity",
	},
})}

var RealIntegralDef = realIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "RealIntegralDef",
	Key:   "prop_7742df1fe8f8eb4a",
	Const: "measure_integral",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → (A → real) → real",
	Reading: "The embedding clamps negative inputs to zero. Infinite " +
		"positive or negative integrals are read as zero by extended_to_real; " +
		"algebraic integral laws therefore carry integrability assumptions.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real). " +
			"    measure_integral(Ω, S, μ, f) = " +
			"    extended_to_real(nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x)))) - " +
			"    extended_to_real(nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x))))",
	},
})}
