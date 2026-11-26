// polynomials.go — the Hermite polynomials of one variable: the
// three-term recurrence, the derivative, and their orthogonality against
// the Gaussian weight.

package hermite_function

import (
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

// HermiteRecurrence — H₀ = 1, H₁ = 2x and the three-term recurrence.
var HermiteRecurrence = hermiteRecurrenceThm{family.Add(registry.ProofEntry{
	Name: "HermiteRecurrence",
	Key:  "prop_13967107be7cc2c8",
	Reading: "In the coefficient comparison only one side has a term at " +
		"j = 0 (H_k has no (j − 1)-th term there) and at 2j = k + 2 (H_{k+1} " +
		"has none); the identity (k + 2) = (k + 2 − 2j) + 2j covers both ends.",
	Build: family.Card(
		"∀k:num. ∀x:real. "+
			"    hermite_polynomial(0, x) = &1 ∧ "+
			"    hermite_polynomial(1, x) = &2 * x ∧ "+
			"    hermite_polynomial(k + 2, x) = "+
			"    &2 * x * hermite_polynomial(k + 1, x) - &2 * &(k + 1) * hermite_polynomial(k, x)",
		"compare the coefficients of (2x)^{k+2−2j} in the explicit sums: the j-th term of "+
			"H_{k+2} is the j-th term of 2x·H_{k+1} minus the (j − 1)-th term of 2(k + 1)·H_k, an "+
			"identity of factorial quotients, (k + 2)!/(j!(k + 2 − 2j)!) = (k + 1)!/(j!(k + 1 − "+
			"2j)!) + 2(k + 1)·k!/((j − 1)!(k + 2 − 2j)!), Pascal's rule after clearing denominators"),
})}

// HermiteDerivative — H_k′ = 2k·H_{k−1}.
var HermiteDerivative = hermiteDerivativeThm{family.Add(registry.ProofEntry{
	Name:    "HermiteDerivative",
	Key:     "prop_2a75a6ad7b82bc63",
	Reading: "At k = 0 the derivative is 0, the right side's factor &2 * &0.",
	Build: family.Card(
		"∀k:num. ∀x:real. "+
			"    real_derivative_at(hermite_polynomial(k), x, &2 * &k * hermite_polynomial(k - 1, x))",
		"differentiate the explicit sum term by term, a polynomial: the j-th "+
			"term k!(−1)ʲ(2x)^{k−2j}/(j!(k − 2j)!) has derivative 2k times the j-th "+
			"term of H_{k−1} when 2j < k, and the constant term (2j = k) drops out"),
})}

// HermiteOrthogonality — the Hermite polynomials are orthogonal against
// exp(−x²), with squared norms 2ᵏ·k!·√π.
var HermiteOrthogonality = hermiteOrthogonalityThm{family.Add(registry.ProofEntry{
	Name: "HermiteOrthogonality",
	Key:  "prop_225447436c480265",
	Reading: "The integrability conjunct is a claim, lebesgue_integral " +
		"being total. At j = k = 0 it is the Gaussian integral √π.",
	Deps: []registry.EntryLike{
		HermiteRecurrence,
		HermiteDerivative,
		lebesgue_riemann.GaussianIntegral,
		vec_integral.IntegralPartialZero,
		vec_integral.IntegralSum,
		vec_integral.IntegralScale,
	},
	Build: family.Card(
		"∀j k:num. "+
			"    lebesgue_integrable(λx:real. "+
			"            hermite_polynomial(j, x) * hermite_polynomial(k, x) * real_exp(-real_pow(x, 2))) ∧ "+
			"    lebesgue_integral(λx:real. "+
			"            hermite_polynomial(j, x) * hermite_polynomial(k, x) * real_exp(-real_pow(x, 2))) = "+
			"    COND(j = k, real_pow(&2, k) * &(factorial(k)) * real_sqrt(pi), &0)",
		"Rodrigues: H_k(x)·exp(−x²) = (−1)ᵏ (d/dx)ᵏ exp(−x²), by induction from the recurrence and "+
			"the derivative rule (HermiteRecurrence, HermiteDerivative: d/dx(H_k e^{−x²}) = (2kH_{k−1} − "+
			"2xH_k)e^{−x²} = −H_{k+1}e^{−x²}). The integrand is a polynomial times exp(−x²), continuous "+
			"and of rapid decay, so integrable. For j ≤ k integrate by parts k times, the boundary terms "+
			"vanishing against the Gaussian (vec_integral.IntegralPartialZero at n = 1, with IntegralSum "+
			"and IntegralScale): all k derivatives move onto H_j, whose k-th derivative is 0 for j < k "+
			"and the constant 2ᵏ·k! for j = k (HermiteDerivative). This leaves 0 for j < k and "+
			"2ᵏ·k!·∫exp(−x²) = 2ᵏ·k!·√π (lebesgue_riemann.GaussianIntegral) for j = k; j > k by symmetry"),
})}
