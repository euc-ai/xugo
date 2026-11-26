package l2_martingale

import (
	"github.com/euc-ai/xugo/library/registry"
)

var L2MartingaleDef = l2MartingaleDefThm{family.Define(registry.DefEntry{
	Name:  "L2MartingaleDef",
	Key:   "prop_53fb171a66292b30",
	Const: "l2_martingale_on",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(num → set(set(A))) → " +
		"(num → A → real) → " +
		"bool",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"    l2_martingale_on(Ω, S, μ, F, M) ⇔ " +
			"    martingale_on(Ω, S, μ, F, M) ∧ (∀n:num. real_integrable(Ω, S, μ, λx:A. M(n, x) * M(n, x)))",
	},
})}
