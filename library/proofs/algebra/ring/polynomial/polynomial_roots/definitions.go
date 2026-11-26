// definitions.go — the roots of a polynomial in a set of points.

package polynomial_roots

import (
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialRootsDef — `polynomial_roots(c, p)`: the roots of p in c,
// the points of c at which p takes the value zero. The set c is any set
// of points, not only the carrier of the ring whose operations evaluate
// p: the roots in a subfield M of L are `polynomial_roots(M, p)` under L.
var PolynomialRootsDef = polynomialRootsDefThm{family.Define(registry.DefEntry{
	Name:     "PolynomialRootsDef",
	Key:      "prop_aa45c1bc79c68573",
	Const:    "polynomial_roots",
	Type:     "(A → A → A) → A → (A → A → A) → A → set(A) → (num → A) → set(A)",
	Implicit: []string{"add", "zero", "mul", "one"},
	Equations: []string{
		"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀one:A. ∀c:set(A). ∀p:(num → A). " +
			"    polynomial_roots(add, zero, mul, one, c, p) = " +
			"    {x:A | x ∈ c ∧ polynomial_eval(add, zero, mul, one, p, x) = zero}",
	},
})}
