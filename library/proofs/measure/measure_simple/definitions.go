package measure_simple

import (
	"github.com/euc-ai/xugo/library/registry"
)

var NonnegSimpleDef = nonnegSimpleDefThm{family.Define(registry.DefEntry{
	Name:  "NonnegSimpleDef",
	Key:   "prop_396bbab067ae78c1",
	Const: "measure_simple",
	Type:  "set(A) → set(set(A)) → (A → real) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀f:(A → real). " +
			"    measure_simple(Ω, S, f) ⇔ " +
			"    real_measurable(Ω, S, f) ∧ finite(image(f, Ω)) ∧ (∀x:A. x ∈ Ω ⇒ &0 ≤ f(x))",
	},
})}

var SimpleIntegralDef = simpleIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "SimpleIntegralDef",
	Key:   "prop_26128352ed05ae0a",
	Const: "measure_simple_integral",
	Type:  "set(A) → (set(A) → extended_nonneg_real) → (A → real) → extended_nonneg_real",
	Reading: "The sum is intended for finite-image functions; its zero term " +
		"contributes zero even when the corresponding level set has infinite measure.",
	Equations: []string{
		"∀Ω:set(A). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real). " +
			"    measure_simple_integral(Ω, μ, f) = " +
			"    Σ_{y∈image(f, Ω)} extended_of_real(y) * μ({x:A | x ∈ Ω ∧ f(x) = y})",
	},
})}
