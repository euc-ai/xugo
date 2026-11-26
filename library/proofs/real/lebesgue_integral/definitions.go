// definitions.go — the chapter's definitional layer: measurable
// functions, the nonnegative simple functions and their integral, and
// the integral of a nonnegative function as the supremum of the
// integrals of the simple functions below it.
//
// A simple function takes finitely many values, and its integral sums
// each value times the measure of the set where it is taken. The sum is
// in ⟦0, ∞⟧, where 0 · ∞ = 0, so the value 0 taken on a set of infinite
// measure adds nothing. A real-valued function f is integrated through
// its positive and negative parts, max(f, 0) and max(-f, 0), each a
// nonnegative function.

package lebesgue_integral

import (
	"github.com/euc-ai/xugo/library/registry"
)

// LebesgueMeasurableFunctionDef — `lebesgue_measurable_function(f)`:
// the set where f exceeds any given value is Lebesgue measurable.
var LebesgueMeasurableFunctionDef = lebesgueMeasurableFunctionDefThm{family.Define(registry.DefEntry{
	Name:  "LebesgueMeasurableFunctionDef",
	Key:   "prop_b477b8442d7e438b",
	Const: "lebesgue_measurable_function",
	Type:  "(real → real) → bool",
	Equations: []string{
		"∀f:(real → real). " +
			"    lebesgue_measurable_function(f) ⇔ ∀c:real. lebesgue_measurable({x:real | c < f(x)})",
	},
})}

// lebesgueSimpleDef — `lebesgue_simple(f)`: f is a nonnegative simple
// function, measurable with finitely many values.
var lebesgueSimpleDef = lebesgueSimpleDefThm{family.Define(registry.DefEntry{
	Name:  "lebesgueSimpleDef",
	Key:   "prop_38e45bebeba203a8",
	Const: "lebesgue_simple",
	Type:  "(real → real) → bool",
	Equations: []string{
		"∀f:(real → real). " +
			"    lebesgue_simple(f) ⇔ " +
			"    lebesgue_measurable_function(f) ∧ finite(image(f, 𝕌)) ∧ (∀x:real. &0 ≤ f(x))",
	},
	Deps: []registry.EntryLike{LebesgueMeasurableFunctionDef},
})}

// LebesgueSimpleIntegralDef — `lebesgue_simple_integral(f)`: the sum,
// over the values y of f, of y times the measure of the set where f
// takes the value y.
var LebesgueSimpleIntegralDef = lebesgueSimpleIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "LebesgueSimpleIntegralDef",
	Key:   "prop_dbe7bbbc4391d0c1",
	Const: "lebesgue_simple_integral",
	Type:  "(real → real) → extended_nonneg_real",
	Equations: []string{
		"∀f:(real → real). " +
			"    lebesgue_simple_integral(f) = " +
			"    Σ_{y∈image(f, 𝕌)} extended_of_real(y) * lebesgue_outer_measure({x:real | f(x) = y})",
	},
	Reading: "The equation reads at every function, and it is meant at the simple ones: there the " +
		"values form a finite set, the level sets are measurable, and each value is nonnegative, so " +
		"extended_of_real takes it as it is. A value 0 on a set of infinite measure contributes 0 · ∞ = 0.",
})}

// LebesgueNonnegIntegralDef — `lebesgue_nonneg_integral(f)`: the
// supremum, in ⟦0, ∞⟧, of the integrals of the simple functions lying
// below f.
var LebesgueNonnegIntegralDef = lebesgueNonnegIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "LebesgueNonnegIntegralDef",
	Key:   "prop_547cda1a0b65bdc9",
	Const: "lebesgue_nonneg_integral",
	Type:  "(real → real) → extended_nonneg_real",
	Equations: []string{
		"∀f:(real → real). " +
			"    lebesgue_nonneg_integral(f) = " +
			"    extended_sup({m:extended_nonneg_real | " +
			"            ∃s:(real → real). " +
			"                lebesgue_simple(s) ∧ (∀x:real. s(x) ≤ f(x)) ∧ m = lebesgue_simple_integral(s)})",
	},
	Deps: []registry.EntryLike{lebesgueSimpleDef, LebesgueSimpleIntegralDef},
	Reading: "The integral is meant at nonnegative functions. A simple function is " +
		"nonnegative everywhere, so where f is negative at some point none lies below " +
		"it, and the supremum of the empty set makes the integral 0. Measurability of f " +
		"is not asked: at a nonmeasurable f this is the lower integral.",
})}

// LebesgueIntegrableDef — `lebesgue_integrable(f)`: f is measurable and
// the integral of |f| is finite.
var LebesgueIntegrableDef = lebesgueIntegrableDefThm{family.Define(registry.DefEntry{
	Name:  "LebesgueIntegrableDef",
	Key:   "prop_ed4f02df8578f459",
	Const: "lebesgue_integrable",
	Type:  "(real → real) → bool",
	Equations: []string{
		"∀f:(real → real). " +
			"    lebesgue_integrable(f) ⇔ " +
			"    lebesgue_measurable_function(f) ∧ " +
			"    lebesgue_nonneg_integral(λx:real. |f(x)|) ≠ extended_infinity",
	},
	Deps: []registry.EntryLike{LebesgueMeasurableFunctionDef, LebesgueNonnegIntegralDef},
})}

// LebesgueIntegralDef — `lebesgue_integral(f)`: the integral of the
// positive part of f less the integral of its negative part.
var LebesgueIntegralDef = lebesgueIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "LebesgueIntegralDef",
	Key:   "prop_7fab6f16488c01c6",
	Const: "lebesgue_integral",
	Type:  "(real → real) → real",
	Equations: []string{
		"∀f:(real → real). " +
			"    lebesgue_integral(f) = " +
			"    extended_to_real(lebesgue_nonneg_integral(λx:real. max(f(x), &0))) - " +
			"    extended_to_real(lebesgue_nonneg_integral(λx:real. max(-f(x), &0)))",
	},
	Deps: []registry.EntryLike{LebesgueNonnegIntegralDef},
	Reading: "The value is meant at an integrable f, where both parts have finite " +
		"integrals. Where a part's integral is ∞, extended_to_real reads it as 0, so the value is " +
		"no integral, and a statement about lebesgue_integral(f) carries lebesgue_integrable(f).",
})}
