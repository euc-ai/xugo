// definitions.go — divisibility, irreducibility and coprimality of
// polynomials over a ring, each read through the ring record.

package polynomial_division

import (
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialDividesDef — `polynomial_divides(R, p, q)`: q is p times a
// polynomial with coefficients in R's carrier.
var PolynomialDividesDef = polynomialDividesDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialDividesDef",
	Key:   "prop_c618009930361698",
	Const: "polynomial_divides",
	Type:  "ring_ops(A) → (num → A) → (num → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀p q:(num → A). " +
			"    polynomial_divides(R, p, q) ⇔ " +
			"    ∃r:(num → A). " +
			"        polynomial_over(R.zero, R.carrier, r) ∧ q = polynomial_mul(R.add, R.zero, R.mul, p, r)",
	},
})}

// PolynomialIrreducibleDef — `polynomial_irreducible(R, p)`: p has
// coefficients in R's carrier and positive degree, and every factorization of it
// into polynomials over R has a factor of degree zero. Over a field
// the polynomials of degree zero other than the zero polynomial are the
// units, so this is irreducibility.
var PolynomialIrreducibleDef = polynomialIrreducibleDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialIrreducibleDef",
	Key:   "prop_78de13cf06b1c82",
	Const: "polynomial_irreducible",
	Type:  "ring_ops(A) → (num → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀p:(num → A). " +
			"    polynomial_irreducible(R, p) ⇔ " +
			"    polynomial_over(R.zero, R.carrier, p) ∧ " +
			"    0 < polynomial_degree(R.zero, p) ∧ " +
			"    (∀q r:(num → A). " +
			"        polynomial_over(R.zero, R.carrier, q) ∧ " +
			"        polynomial_over(R.zero, R.carrier, r) ∧ " +
			"        p = polynomial_mul(R.add, R.zero, R.mul, q, r) ⇒ " +
			"        polynomial_degree(R.zero, q) = 0 ∨ polynomial_degree(R.zero, r) = 0)",
	},
})}

// PolynomialCoprimeDef — `polynomial_coprime(R, p, q)`: p and q are
// coprime over R, some combination of them by polynomials over R being
// the one polynomial. It is Bézout's identity taken as the definition,
// as `int_coprime` is for the integers, so it says coprimality with no
// greatest common divisor and holds over any ring R.
var PolynomialCoprimeDef = polynomialCoprimeDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialCoprimeDef",
	Key:   "prop_32bc84da534a7837",
	Const: "polynomial_coprime",
	Type:  "ring_ops(A) → (num → A) → (num → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀p q:(num → A). " +
			"    polynomial_coprime(R, p, q) ⇔ " +
			"    (∃u v:(num → A). " +
			"        polynomial_over(R.zero, R.carrier, u) ∧ " +
			"        polynomial_over(R.zero, R.carrier, v) ∧ " +
			"        vec_add(R.add, " +
			"            polynomial_mul(R.add, R.zero, R.mul, u, p), " +
			"            polynomial_mul(R.add, R.zero, R.mul, v, q)) = " +
			"        basis_vector(R.zero, R.one, 0))",
	},
})}
