# hermite_function — the Hermite polynomials and the Hermite functions on ℝⁿ

The Hermite polynomial Hₖ is given by its explicit sum, $H_k(x) = k! \sum_{2j \le k} (-1)^j (2x)^{k-2j} / (j! (k-2j)!)$, in the physicists' normalization: leading coefficient 2ᵏ, weight exp(−x²). The Hermite function h_α on ℝⁿ is the product over the coordinates i < n of $H_{\alpha(i)}(x_i) e^{-x_i^2/2} / \sqrt{2^{\alpha(i)} \alpha(i)! \sqrt{\pi}}$. The chapter states the one-variable algebra first: the three-term recurrence and the derivative rule. From them, and the Gaussian integral of vector/vec_integral, it states the orthogonality of the polynomials against exp(−x²). The functions on ℝⁿ are orthonormal for vec_integral, the integral over ℝⁿ, because an integral of a product of functions of separate coordinates factors. A coordinate minus or plus its partial derivative raises or lowers one Hermite index, with the weights $\sqrt{2(\alpha_i + 1)}$ and $\sqrt{2\alpha_i}$.

The Schwartz class, completeness and the synthesis of rapidly decreasing coefficients are stated in analysis/bott_operator, beside the Schwartz class that chapter defines.

## Definitions (definitions.go)

| Member | Statement or role |
|---|---|
| `HermitePolynomialDef` | Definition of `hermite_polynomial` |
| `HermiteFunctionDef` | Definition of `hermite_function` |

## The polynomials (polynomials.go)

| Member | Statement |
|---|---|
| `HermiteRecurrence` | H₀ = 1, H₁ = 2x and $H_{k+2}(x) = 2x H_{k+1}(x) - 2(k+1) H_k(x)$ — card |
| `HermiteDerivative` | $H_k'(x) = 2k H_{k-1}(x)$ — card |
| `HermiteOrthogonality` | $\int H_j(x) H_k(x) e^{-x^2} dx = [j = k] 2^k k! \sqrt{\pi}$, the integrand Lebesgue integrable — card |

## The functions on ℝⁿ (functions.go)

| Member | Statement |
|---|---|
| `HermiteOrthonormal` | the integral over ℝⁿ of h_α·h_β is 1 when α and β agree below n and 0 otherwise — card |
| `HermiteLadder` | for i < n, $(x_i - \partial_i) h_\alpha = \sqrt{2(\alpha_i + 1)} h_{\alpha + e_i}$ and $(x_i + \partial_i) h_\alpha = \sqrt{2\alpha_i} h_{\alpha - e_i}$ — card |
