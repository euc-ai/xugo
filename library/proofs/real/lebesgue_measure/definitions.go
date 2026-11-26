// definitions.go — the chapter's definitional layer: the Lebesgue outer
// measure of a set of reals.
//
// A countable cover of a set s by open intervals is a pair of sequences
// of interval ends a, b : num → real, every point of s lying in some
// ⟬a(n), b(n)⟭. Its total length is the ⟦0, ∞⟧ sum of the lengths
// b(n) - a(n); an interval with b(n) ≤ a(n) is empty, and it counts 0,
// extended_of_real clamping a negative real to 0.

package lebesgue_measure

import (
	"github.com/euc-ai/xugo/library/registry"
)

// LebesgueOuterMeasureDef — `lebesgue_outer_measure(s)`: the infimum,
// over the countable covers of s by open intervals, of their total
// length.
var LebesgueOuterMeasureDef = lebesgueOuterMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "LebesgueOuterMeasureDef",
	Key:   "prop_ee019b68923bf790",
	Const: "lebesgue_outer_measure",
	Type:  "set(real) → extended_nonneg_real",
	Equations: []string{
		"∀s:set(real). " +
			"    lebesgue_outer_measure(s) = " +
			"    extended_inf({m:extended_nonneg_real | " +
			"            ∃a b:(num → real). " +
			"                (∀x:real. x ∈ s ⇒ ∃n:num. a(n) < x ∧ x < b(n)) ∧ " +
			"                m = extended_series(λn:num. extended_of_real(b(n) - a(n)))})",
	},
	Reading: "Every set of reals has a cover, the intervals ⟬-n - 1, n " +
		"+ 1⟭ covering the line, so the infimum runs over a nonempty set of " +
		"lengths and is ∞ exactly when every cover has infinite total length.",
})}
