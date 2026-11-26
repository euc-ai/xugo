package outer_measure

import (
	"github.com/euc-ai/xugo/library/registry"
)

var OuterMeasureOn = outerMeasureOnThm{family.DefineStructure(registry.DefEntry{
	Name:  "OuterMeasureOn",
	Key:   "prop_55e8c6b8f00f80d5",
	Const: "outer_measure_on",
	Type:  "set(A) → (set(A) → extended_nonneg_real) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀μ:(set(A) → extended_nonneg_real). " +
			"    outer_measure_on(Ω, μ) ⇔ " +
			"    μ(∅) = &0 ∧ " +
			"    (∀s t:set(A). s ⊆ t ∧ t ⊆ Ω ⇒ μ(s) ≤ μ(t)) ∧ " +
			"    (∀a:(num → set(A)). (∀n:num. a(n) ⊆ Ω) ⇒ μ(⋃image(a, 𝕌)) ≤ extended_series(λn:num. μ(a(n))))",
	},
})}
