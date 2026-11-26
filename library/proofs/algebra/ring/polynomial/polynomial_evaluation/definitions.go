// definitions.go — the value of a polynomial at a point: the sum of
// p(i) * x ^ i over its support; and a field over which every polynomial of
// odd degree has a root.

package polynomial_evaluation

import (
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialEvalDef — `polynomial_eval(p, x)`: the sum of p(i) * x ^ i
// over the indices where p is not zero.
var PolynomialEvalDef = polynomialEvalDefThm{family.Define(registry.DefEntry{
	Name:     "PolynomialEvalDef",
	Key:      "prop_bf7c64563782d42a",
	Const:    "polynomial_eval",
	Type:     "(A → A → A) → A → (A → A → A) → A → (num → A) → A → A",
	Implicit: []string{"add", "zero", "mul", "one"},
	Equations: []string{
		"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀one:A. ∀p:(num → A). ∀x:A. " +
			"    polynomial_eval(add, zero, mul, one, p, x) = " +
			"    module_sum(add, zero, fun_support(zero, p), λi:num. mul(p(i), monoid_pow(mul, one, x, i)))",
	},
})}

// OddDegreeRootsDef — `odd_degree_roots(F)`: every polynomial of odd degree
// over the field has a root in it.
var OddDegreeRootsDef = oddDegreeRootsDefThm{family.Define(registry.DefEntry{
	Name: "OddDegreeRootsDef", Const: "odd_degree_roots", Type: "field_ops(A) → bool",
	Key: "prop_f391399795b3fa74",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    odd_degree_roots(F) ⇔ " +
			"    ∀p:(num → A). " +
			"        polynomial_over(F.zero, F.carrier, p) ∧ " +
			"        (∃j:num. polynomial_degree(F.zero, p) = 2 * j + 1) ⇒ " +
			"        ∃x:A. x ∈ F.carrier ∧ polynomial_eval(F.add, F.zero, F.mul, F.one, p, x) = F.zero",
	},
	Deps: []registry.EntryLike{PolynomialEvalDef},
})}
