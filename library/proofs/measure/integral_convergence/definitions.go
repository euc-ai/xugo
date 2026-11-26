package integral_convergence

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ConvergesInMeasureDef — `converges_in_measure(Ω, μ, Y, Z)`: for every
// ε > 0 the measure of the points of Ω where Y(n) lies farther than ε
// from Z is eventually below any δ > 0. On a probability space this is
// convergence in probability.
var ConvergesInMeasureDef = convergesInMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "ConvergesInMeasureDef",
	Key:   "prop_7a658fdf06ae336",
	Const: "converges_in_measure",
	Type:  "set(A) → (set(A) → extended_nonneg_real) → (num → A → real) → (A → real) → bool",
	Reading: "The measures are compared with a bound δ in ⟦0, ∞⟧ and never read as " +
		"reals, so a set of infinite measure is not mistaken for a small one. No σ-algebra " +
		"is named: μ is read at the sets {x ∈ Ω | ε < |Y(n, x) − Z(x)|} as they are.",
	Equations: []string{
		"∀Ω:set(A). ∀μ:(set(A) → extended_nonneg_real). ∀Y:(num → A → real). ∀Z:(A → real). " +
			"    converges_in_measure(Ω, μ, Y, Z) ⇔ " +
			"    (∀ε δ:real. " +
			"        &0 < ε ∧ &0 < δ ⇒ " +
			"        (∃N:num. ∀n:num. N ≤ n ⇒ μ({x:A | x ∈ Ω ∧ ε < |Y(n, x) - Z(x)|}) ≤ extended_of_real(δ)))",
	},
})}
