# complex_cpow — complex powers z^w by the principal logarithm, and their laws at a positive real base

`complex_cpow(z, w)` is z to the complex power w: `exp(w·log z)` with the
principal logarithm, and at the base 0 the values of `real_rpow`, 0 and
at the exponent 0 the value 1. `CpowZeroExponent` holds for every base.
At a positive real base x, the principal logarithm is the real one and
the power is `exp(w·log x)`. That is the
power a Dirichlet series is written with, $n^{-s}$, and at such a base the
power behaves as the real power does: it turns sums of exponents into
products, and products of positive bases into products. At any nonzero
complex base the exponent addition law also follows from the exponential
formula. For multiplication of complex bases, the principal logarithm
can change the sum of the logarithms by a multiple of 2πi.

## The definition (definitions.go)

| constant | reading |
|---|---|
| `complex_cpow(z, w)` | `exp(w * log(z))` for z ≠ 0; at z = 0 it is 0, and 1 when w = 0 |

## Laws of complex powers (laws.go)

The laws at a positive real base use the real logarithm
(`CpowPositiveReal`). The
modulus of x^w is x to the real part of w (`AbsCpow`), which is why a
Dirichlet series converges on half-planes; for x ≥ 1 and σ ≤ Re s it
gives $\lvert x^{-s} \rvert \le x^{-\sigma}$ (`AbsCpowNegLessEq`). The exponent laws are the
functional equation of exp; the power of a product of two positive reals
is the product of the powers because the real logarithm is additive.

| member | statement |
|---|---|
| `CpowPositiveReal` | `∀x:real. ∀w:complex. &0 < x ⇒ complex_cpow(&x, w) = exp(w * &log(x))` |
| `CpowRealExponent` | `∀x a:real. &0 < x ⇒ complex_cpow(&x, &a) = &real_rpow(x, a)` |
| `AbsCpow` | `∀x:real. ∀w:complex. &0 < x ⇒ \|complex_cpow(&x, w)\| = real_rpow(x, re(w))` |
| `AbsCpowNegLessEq` | `∀x σ:real. ∀s:complex. &1 ≤ x ∧ σ ≤ re(s) ⇒ \|complex_cpow(&x, -s)\| ≤ real_rpow(x, -σ)` |
| `CpowZeroExponent` | `∀z:complex. complex_cpow(z, &0) = &1` |
| `CpowOneBase` | `∀w:complex. complex_cpow(&1, w) = &1` |
| `CpowAdd` | `∀x:real. ∀v w:complex. &0 < x ⇒ complex_cpow(&x, v + w) = complex_cpow(&x, v) * complex_cpow(&x, w)` |
| `CpowNeg` | `∀x:real. ∀w:complex. &0 < x ⇒ complex_cpow(&x, -w) = complex_inv(complex_cpow(&x, w))` — card |
| `CpowNat` | `∀x:real. ∀n:num. &0 < x ⇒ complex_cpow(&x, &n) = &(x ^ n)` — card |
| `CpowMulPositive` | `∀x y:real. ∀w:complex. &0 < x ∧ &0 < y ⇒ complex_cpow(&(x * y), w) = complex_cpow(&x, w) * complex_cpow(&y, w)` |
| `CpowNonzero` | `∀x:real. ∀w:complex. &0 < x ⇒ complex_cpow(&x, w) ≠ &0` — card |

## Derivatives, and differences of powers (laws.go)

At a positive real base x, the power is entire in its exponent w,
with derivative x^w·log x. Along the positive reals u ↦ u^w has velocity $w \cdot u^{w-1}$; the
base stays real, so the slit of the principal logarithm never enters.
Integrating that velocity bounds the difference of two powers:
`CpowDifferenceBound`, at y = x + 1, is the estimate
$\lvert n^{-s} - (n+1)^{-s} \rvert \le \lvert s \rvert \cdot n^{-\operatorname{Re} s - 1}$ on which the convergence of ζ's
regularized series and of conditionally convergent Dirichlet series
rests. The tangent remainder of $u \mapsto u^{1-s}$ over a unit step is bounded
the same way,
$\lvert (n+1)^{1-s} - n^{1-s} - (1-s) \cdot n^{-s} \rvert \le \lvert s-1 \rvert \cdot \lvert s \rvert \cdot n^{-\operatorname{Re} s - 1}$
for Re s ≥ −1 (`CpowTangentRemainderBound`): the bound on the terms of
ζ's regularized series.

| member | statement |
|---|---|
| `CpowDerivativeExponent` | `∀x:real. ∀w:complex. &0 < x ⇒ complex_derivative_at(λv:complex. complex_cpow(&x, v), w, complex_cpow(&x, w) * &log(x))` |
| `CpowHolomorphicExponent` | `∀x:real. &0 < x ⇒ holomorphic_on(𝕌, λz:complex. complex_cpow(&x, z))` |
| `CpowPathDerivative` | `∀x:real. ∀w:complex. &0 < x ⇒ path_derivative_at(λu:real. complex_cpow(&u, w), x, w * complex_cpow(&x, w - &1))` |
| `CpowDifferenceBound` | `∀x y:real. ∀s:complex. &0 < x ∧ x ≤ y ∧ -&1 ≤ re(s) ⇒ \|complex_cpow(&x, -s) - complex_cpow(&y, -s)\| ≤ \|s\| * (y - x) * real_rpow(x, -re(s) - &1)` |
| `CpowTangentRemainderBound` | `∀s:complex. ∀n:num. -&1 ≤ re(s) ∧ 0 < n ⇒ \|(s - &1) * complex_cpow(&n, -s) - (complex_cpow(&n, &1 - s) - complex_cpow(&(n + 1), &1 - s))\| ≤ \|s - &1\| * \|s\| * real_rpow(&n, -re(s) - &1)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
