// definitions.go — splitting, separability and the Wronskian of
// polynomials over a ring.

package separable_polynomial

import (
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialSplitsDef — `polynomial_splits(R, p)`: p splits over R,
// every irreducible factor of it over R being linear. Over a field, a
// nonzero polynomial that splits is a constant times a product of linear
// factors; every irreducible polynomial divides the zero polynomial,
// so it splits only over a field whose irreducible polynomials are all
// linear.
var PolynomialSplitsDef = polynomialSplitsDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialSplitsDef",
	Key:   "prop_e7641b392f7766e3",
	Const: "polynomial_splits",
	Type:  "ring_ops(A) → (num → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀p:(num → A). " +
			"    polynomial_splits(R, p) ⇔ " +
			"    (∀q:(num → A). " +
			"        polynomial_irreducible(R, q) ∧ polynomial_divides(R, q, p) ⇒ " +
			"        polynomial_degree(R.zero, q) = 1)",
	},
})}

// PolynomialSeparableDef — `polynomial_separable(R, p)`: p is coprime
// over R to its derivative, some combination of the two with
// coefficients in R's carrier being the one polynomial. Over a field this says p
// has no repeated root in any field holding R's carrier.
var PolynomialSeparableDef = polynomialSeparableDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialSeparableDef",
	Key:   "prop_cf6ea6bc94e14047",
	Const: "polynomial_separable",
	Type:  "ring_ops(A) → (num → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀p:(num → A). " +
			"    polynomial_separable(R, p) ⇔ " +
			"    (∃u v:(num → A). " +
			"        polynomial_over(R.zero, R.carrier, u) ∧ " +
			"        polynomial_over(R.zero, R.carrier, v) ∧ " +
			"        vec_add(R.add, " +
			"            polynomial_mul(R.add, R.zero, R.mul, u, p), " +
			"            polynomial_mul(R.add, " +
			"                R.zero, " +
			"                R.mul, " +
			"                v, " +
			"                polynomial_derivative(R.add, R.zero, R.mul, R.one, p))) = " +
			"        basis_vector(R.zero, R.one, 0))",
	},
})}

// PolynomialWronskianDef — `polynomial_wronskian(p, q)`: the Wronskian
// p q' − p' q of two polynomials. It vanishes when p and q are
// proportional, it is divisible by each common divisor of p and p', and
// it vanishes from deg p + deg q on; the Mason–Stothers theorem is read
// off these three.
var PolynomialWronskianDef = polynomialWronskianDefThm{family.Define(registry.DefEntry{
	Name:     "PolynomialWronskianDef",
	Key:      "prop_c10b82d6c9c60f42",
	Const:    "polynomial_wronskian",
	Type:     "(A → A → A) → A → (A → A → A) → A → (A → A → A) → (num → A) → (num → A) → num → A",
	Implicit: []string{"add", "zero", "mul", "one", "sub"},
	Equations: []string{
		"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀one:A. ∀sub:(A → A → A). ∀p q:(num → A). " +
			"    polynomial_wronskian(add, zero, mul, one, sub, p, q) = " +
			"    vec_sub(sub, " +
			"        polynomial_mul(add, zero, mul, p, polynomial_derivative(add, zero, mul, one, q)), " +
			"        polynomial_mul(add, zero, mul, polynomial_derivative(add, zero, mul, one, p), q))",
	},
})}
