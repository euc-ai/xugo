// definitions.go — the Hermite polynomials and the Hermite functions on ℝⁿ.

package hermite_function

import (
	"github.com/euc-ai/xugo/library/registry"
)

// HermitePolynomialDef — `hermite_polynomial(k, x)`: the physicists' Hermite
// polynomial Hₖ by its explicit sum.
var HermitePolynomialDef = hermitePolynomialDefThm{family.Define(registry.DefEntry{
	Name:  "HermitePolynomialDef",
	Key:   "prop_a3f2dc06066d1043",
	Const: "hermite_polynomial",
	Type:  "num → real → real",
	Equations: []string{
		"∀k:num. ∀x:real. " +
			"    hermite_polynomial(k, x) = " +
			"    &(factorial(k)) * " +
			"    real_sum({j:num | 2 * j ≤ k}, " +
			"        λj:num. " +
			"            real_pow(-&1, j) * " +
			"            real_pow(&2 * x, k - 2 * j) / " +
			"            (&(factorial(j)) * &(factorial(k - 2 * j))))",
	},
	Reading: "The physicists' convention: the leading coefficient is " +
		"2ᵏ and the weight is exp(−x²), so H₀ = 1, H₁ = 2x, H₂ = 4x² − 2.",
})}

// HermiteFunctionDef — `hermite_function(n, α, x)`: the normalized Hermite
// function h_α on ℝⁿ, the product over the coordinates i < n of
// H_{α(i)}(x(i)) exp(−x(i)²/2) / √(2^{α(i)} α(i)! √π).
var HermiteFunctionDef = hermiteFunctionDefThm{family.Define(registry.DefEntry{
	Name:  "HermiteFunctionDef",
	Key:   "prop_d68697aaaf959041",
	Deps:  []registry.EntryLike{HermitePolynomialDef},
	Const: "hermite_function",
	Type:  "num → (num → num) → (num → real) → real",
	Equations: []string{
		"∀n:num. ∀α:(num → num). ∀x:(num → real). " +
			"    hermite_function(n, α, x) = " +
			"    module_sum(real_mul, " +
			"        &1, " +
			"        {i:num | i < n}, " +
			"        λi:num. " +
			"            hermite_polynomial(α(i), x(i)) * " +
			"            real_exp(-real_pow(x(i), 2) / &2) / " +
			"            real_sqrt(real_pow(&2, α(i)) * &(factorial(α(i))) * real_sqrt(pi)))",
	},
	Reading: "Only α(i) and x(i) for i < n are read, so h_α is h_β " +
		"whenever α and β agree below n. On ℝ⁰ it is the empty product 1.",
})}
