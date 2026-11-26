// definitions.go — the chapter's definitional layer: a curve finite over
// the projective line, held by the coordinate rings of its two charts
// inside its function field, and its genus.

package algebraic_curve

import (
	"github.com/euc-ai/xugo/library/registry"
)

// CurveOverLineDef — `curve_over_line(L, k, t, A₀, A₁, A₀₁)`: L is a
// function field over the subfield k with t transcendental over k; A₀
// and A₁ are the coordinate rings of the two charts, A₀ containing k[t]
// and free of finite rank over it, A₁ containing k[1/t] and free of
// finite rank over it; A₀₁ is their overlap, A₀[1/t] = A₁[t] inside L;
// the only functions regular on both charts are the constants; and L is
// the field of fractions of A₀.
var CurveOverLineDef = curveOverLineDefThm{family.Define(registry.DefEntry{
	Name: "CurveOverLineDef",
	Key:  "prop_2bbb1e4f44342f2",
	Reading: "Inside L the overlap is A₀[1/t]: the biaffine clause gives A₀₁ " +
		"⊆ A₀[1/t], and A₀ ⊆ A₀₁ with inv(t) ∈ A₁ ⊆ A₀₁, a ring, gives the converse.",
	Const:    "curve_over_line",
	Type:     "field_ops(A) → set(A) → A → set(A) → set(A) → set(A) → bool",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀F:field_ops(A). ∀k:set(A). ∀t:A. ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). " +
			"    curve_over_line(F, k, t, A₀, A₁, A₀₁) ⇔ " +
			"    subfield(F, k) ∧ " +
			"    t ∈ F.carrier ∧ " +
			"    ¬algebraic_over(F, k, t) ∧ " +
			"    A₀₁ ⊆ F.carrier ∧ " +
			"    biaffine(restrict_ring(field_ring(F), A₀₁), A₀, A₁, t, F.inv(t)) ∧ " +
			"    polynomial_image(field_ring(F), k, t) ⊆ A₀ ∧ " +
			"    polynomial_image(field_ring(F), k, F.inv(t)) ⊆ A₁ ∧ " +
			"    (∃E:set(A). " +
			"        finite(E) ∧ " +
			"        module_basis(restrict_ring(field_ring(F), polynomial_image(field_ring(F), k, t)), " +
			"            restrict_module(regular_module(field_ring(F)), A₀), " +
			"            E)) ∧ " +
			"    (∃E:set(A). " +
			"        finite(E) ∧ " +
			"        module_basis( " +
			"            restrict_ring(field_ring(F), polynomial_image(field_ring(F), k, F.inv(t))), " +
			"            restrict_module(regular_module(field_ring(F)), A₁), " +
			"            E)) ∧ " +
			"    A₀ ∩ A₁ = k ∧ " +
			"    fraction_field_carrier(field_ring(F), A₀)",
	},
})}

// CurveGenusDef — `curve_genus(L, k, A₀, A₁, A₀₁)`, written g: the
// dimension over k of H¹ of the structure pair (A₀, A₁).
var CurveGenusDef = curveGenusDefThm{family.Define(registry.DefEntry{
	Name:     "CurveGenusDef",
	Key:      "prop_92d1675ae8859e04",
	Const:    "curve_genus",
	Type:     "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → num",
	Implicit: []string{},
	Bundles:  []string{},
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). " +
			"    curve_genus(R, k, A₀, A₁, A₀₁) = " +
			"    lattice_pair_h1_dim(restrict_ring(R, A₀₁), k, regular_module(R), (A₀, A₁))",
	},
})}
