// definitions.go — the powers of an element t of a field at integer
// exponents, and the coefficients of a Laurent polynomial in t over a
// subfield k, read off a chosen finite expansion.

package laurent_polynomial

import (
	"github.com/euc-ai/xugo/library/registry"
)

// LaurentMonomialDef — `laurent_monomial(t, n)`, written tⁿ: the power of
// t at the integer n, tⁿ for n ≥ 0 and (t⁻¹)⁻ⁿ below.
var LaurentMonomialDef = laurentMonomialDefThm{family.Define(registry.DefEntry{
	Name:     "LaurentMonomialDef",
	Key:      "prop_bb2405bf53edf689",
	Const:    "laurent_monomial",
	Type:     "(A → A → A) → A → (A → A) → A → int → A",
	Implicit: []string{"mul", "one", "inv"},
	Equations: []string{
		"∀mul:(A → A → A). ∀one:A. ∀inv:(A → A). ∀t:A. ∀n:int. " +
			"    laurent_monomial(mul, one, inv, t, n) = " +
			"    COND(&0 ≤ n, " +
			"        monoid_pow(mul, one, t, num_of_int(n)), " +
			"        monoid_pow(mul, one, inv(t), num_of_int(-n)))",
	},
})}

// LaurentPolynomialCoefficientDef — `laurent_polynomial_coefficient(k, t,
// f, i)`: the coefficient of tⁱ in f, read off an expansion of f as a
// finite sum Σ a(j) · tʲ with coefficients in k, chosen. A member of
// k[t, 1/t] has such an expansion, and only one when t is transcendental
// over k; elsewhere the coefficient is a value nothing is said about.
var LaurentPolynomialCoefficientDef = laurentPolynomialCoefficientDefThm{family.Define(registry.DefEntry{
	Name:     "LaurentPolynomialCoefficientDef",
	Key:      "prop_30c2bc7b69fc95d3",
	Const:    "laurent_polynomial_coefficient",
	Type:     "(A → A → A) → A → (A → A → A) → A → (A → A) → set(A) → A → A → int → A",
	Implicit: []string{"add", "zero", "mul", "one", "inv"},
	Equations: []string{
		"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀one:A. ∀inv:(A → A). ∀k:set(A). ∀t f:A. ∀i:int. " +
			"    laurent_polynomial_coefficient(add, zero, mul, one, inv, k, t, f, i) = " +
			"    (εa:(int → A). " +
			"        finite(fun_support(zero, a)) ∧ " +
			"        (∀j:int. a(j) ∈ k) ∧ " +
			"        f = " +
			"        module_sum(add, " +
			"            zero, " +
			"            fun_support(zero, a), " +
			"            λj:int. mul(a(j), laurent_monomial(mul, one, inv, t, j))))(i)",
	},
	Deps: []registry.EntryLike{LaurentMonomialDef},
})}
