// definitions.go — the product of two measures, read off the sections:
// the mass of a set of pairs is the integral, against the first measure,
// of the second measure of its sections.

package product_measure

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ProductMeasureDef — `product_measure(Ω, S, μ, ν)`: a set E of pairs has
// mass ∫ ν(E_x) μ(dx), E_x = {y | (x, y) ∈ E} its section at x. The
// formula is defined for every set; that it is a measure on the product
// σ-algebra, with the product mass on rectangles, is the chapter's
// theorem for σ-finite ν.
var ProductMeasureDef = productMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "ProductMeasureDef",
	Key:   "prop_975c96a744814c8",
	Const: "product_measure",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(set(B) → extended_nonneg_real) → " +
		"set(prod(A, B)) → " +
		"extended_nonneg_real",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀ν:(set(B) → extended_nonneg_real). " +
			"∀E:set(prod(A, B)). " +
			"    product_measure(Ω, S, μ, ν, E) = nonneg_integral(Ω, S, μ, λx:A. ν({y:B | (x, y) ∈ E}))",
	},
})}
