package conditional_expectation

import (
	"github.com/euc-ai/xugo/library/registry"
)

var IsCondExpDef = isCondExpDefThm{family.Define(registry.DefEntry{
	Name:  "IsCondExpDef",
	Key:   "prop_b5dbe2a4a10bed2",
	Const: "is_cond_exp",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(set(A)) → " +
		"(A → real) → " +
		"(A → real) → " +
		"bool",
	Reading: "Both inputs are genuinely measurable and integrable on S; " +
		"the output is genuinely G-measurable. Arbitrary a.e.-equal replacements " +
		"need not preserve that last requirement on an incomplete sigma algebra.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G:set(set(A)). ∀X Y:(A → real). " +
			"    is_cond_exp(Ω, S, μ, G, X, Y) ⇔ " +
			"    measure_on(Ω, S, μ) ∧ " +
			"    sigma_algebra_on(Ω, G) ∧ " +
			"    G ⊆ S ∧ " +
			"    real_integrable(Ω, S, μ, X) ∧ " +
			"    real_integrable(Ω, S, μ, Y) ∧ " +
			"    real_measurable(Ω, G, Y) ∧ " +
			"    (∀E:set(A). E ∈ G ⇒ event_integral(Ω, S, μ, E, X) = event_integral(Ω, S, μ, E, Y))",
	},
})}
