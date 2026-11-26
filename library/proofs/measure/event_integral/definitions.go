package event_integral

import (
	"github.com/euc-ai/xugo/library/registry"
)

var EventIntegralDef = eventIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "EventIntegralDef",
	Key:   "prop_dec5fedf8d60148d",
	Const: "event_integral",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → set(A) → (A → real) → real",
	Reading: "The integrand is cut to E by a conditional and integrated over Ω, so " +
		"only its values on Ω ∩ E are read. E is any set: where it is not an event of S " +
		"the cut need not be measurable, and the laws that need measurability ask E ∈ S.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀E:set(A). ∀f:(A → real). " +
			"    event_integral(Ω, S, μ, E, f) = measure_integral(Ω, S, μ, λx:A. COND(x ∈ E, f(x), &0))",
	},
})}
