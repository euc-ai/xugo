// functions.go — the Hermite functions on ℝⁿ: orthonormal, and the ladder
// relations of the coordinate and its partial derivative.

package hermite_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// HermiteOrthonormal — the Hermite functions on ℝⁿ are orthonormal.
var HermiteOrthonormal = hermiteOrthonormalThm{family.Add(registry.ProofEntry{
	Name: "HermiteOrthonormal",
	Key:  "prop_da25194b16cddbd5",
	Reading: "α and β are compared below n only, the indices the " +
		"functions read. On ℝ⁰ both functions are 1 and the integral is 1.",
	Deps: []registry.EntryLike{HermiteOrthogonality, vec_integral.IntegralProduct},
	Build: family.Card(
		"∀n:num. ∀α β:(num → num). "+
			"    vec_integral⟨n⟩(λx:(num → real). hermite_function(n, α, x) * hermite_function(n, β, x)) = "+
			"    COND(∀i:num. i < n ⇒ α(i) = β(i), &1, &0)",
		"h_α·h_β is the product over i < n of the one-variable functions "+
			"H_{α(i)}(t)H_{β(i)}(t)exp(−t²)/√(2^{α(i)}α(i)!√π·2^{β(i)}β(i)!√π), each integrable "+
			"with integral [α(i) = β(i)] by HermiteOrthogonality; vec_integral.IntegralProduct "+
			"turns the integral of the product into the product of the integrals"),
})}

// HermiteLadder — multiplication by the coordinate xᵢ minus or plus the
// partial derivative ∂ᵢ raises or lowers the i-th Hermite index.
var HermiteLadder = hermiteLadderThm{family.Add(registry.ProofEntry{
	Name: "HermiteLadder",
	Key:  "prop_1a1019b3ba980edf",
	Reading: "i < n is load-bearing: for i ≥ n the derivative is 0 and the shifted functions " +
		"are h_α, so the first equation would say x(i)·h_α = √(2(α(i) + 1))·h_α, false at n = 0, " +
		"x = 0. At α(i) = 0 the lowering weight √(2·0) is 0 and the index α(i) − 1 is 0 again. " +
		"No hypothesis on x: h_α(x + t·eᵢ) changes only through the factor at i, vector or not.",
	Deps: []registry.EntryLike{
		HermiteRecurrence,
		HermiteDerivative,
		vec_smooth.PartialDerivativeValue,
		vec_smooth.PartialDerivativeMul,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀α:(num → num). ∀i:num. ∀x:(num → real).",
		Hypotheses: []string{"i < n"},
		Conclusion: "x(i) * hermite_function(n, α, x) - " +
			"partial_derivative(hermite_function(n, α), i, x) = " +
			"real_sqrt(&2 * &(suc(α(i)))) * hermite_function(n, λj:num. COND(j = i, suc(α(j)), α(j)), x) ∧ " +
			"x(i) * hermite_function(n, α, x) + partial_derivative(hermite_function(n, α), i, x) = " +
			"real_sqrt(&2 * &(α(i))) * hermite_function(n, λj:num. COND(j = i, α(j) - 1, α(j)), x)",
	},
		"one variable first: (t − d/dt)(H_k(t)e^{−t²/2}) = (2tH_k − H_k′)e^{−t²/2} = "+
			"H_{k+1}e^{−t²/2} and (t + d/dt)(H_k(t)e^{−t²/2}) = H_k′e^{−t²/2} = 2kH_{k−1}e^{−t²/2} "+
			"(HermiteDerivative, HermiteRecurrence: 2tH_k − 2kH_{k−1} = H_{k+1}); the normalizations "+
			"√(2ᵏk!√π) turn the factors 1 and 2k into √(2(k + 1)) and √(2k). On ℝⁿ only the factor "+
			"at i depends on x(i), so the partial derivative along i is the other factors times that "+
			"factor's derivative (vec_smooth.PartialDerivativeMul, PartialDerivativeValue)"),
})}
