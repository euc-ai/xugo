package nonneg_integral

import (
	"github.com/euc-ai/xugo/library/registry"
)

var NonnegIntegralDef = nonnegIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "NonnegIntegralDef",
	Key:   "prop_a217670c192611e",
	Const: "nonneg_integral",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(A → extended_nonneg_real) → " +
		"extended_nonneg_real",
	Reading: "This is a lower integral even without measurability. Values outside " +
		"the carrier have no effect; infinite values and an infinite integral are allowed.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → extended_nonneg_real). " +
			"    nonneg_integral(Ω, S, μ, f) = " +
			"    extended_sup({r:extended_nonneg_real | " +
			"            ∃s:(A → real). " +
			"                measure_simple(Ω, S, s) ∧ " +
			"                (∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ f(x)) ∧ " +
			"                r = measure_simple_integral(Ω, μ, s)})",
	},
})}
