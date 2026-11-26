# real_rpow — real powers of positive reals

For x > 0 and real a, x to the power a is exp(a · log x). At 0 the power is 0, except that 0 to the power 0 is 1. The chapter proves the power laws, the monotonicity of the power in its base and in its exponent, its derivatives, and that it agrees with the natural power where both are defined.

For a positive base the definition's first branch is the whole story
(`RpowExp`): every law of the power is a law of exp and log, read
through x^a = exp(a·log x). The exponent laws are the functional
equation of exp, the power of a product is that of log, the natural
power is `ExpNatMul`, and the square root is the nonnegative number the
power 1/2 squares back to (`SqrtUnique`). At the base 0 the definition's
values (0^a = 0 for a ≠ 0, x⁰ = 1) are checked case by case.
Monotonicity in the base and in the exponent is exp and log being
increasing. At a negative exponent, the power is strictly decreasing
in its positive base: the positive opposite powers increase, and
reciprocals reverse their order (`RpowLessBaseNegative`); at a
nonpositive exponent the power does not increase in its positive base,
and at a base at least 1 it does not decrease in its exponent. The derivatives
are the chain rule through exp: near a
positive x the power y ↦ y^a is y ↦ exp(a·log y), and a derivative sees
only a ball (`real_derivative.DerivativeLocal`); at a fixed positive
base, b ↦ x^b is b ↦ exp(b·log x) everywhere. For x > 1 the integral of
$t \mapsto M \cdot \delta \cdot x^{-\delta t}$ over ⟦0, 1⟧ is $\frac{M \cdot (1 - x^{-\delta})}{\log x}$.

## Members

| entry | statement |
|---|---|
| `RealRpowDef` | `real_rpow(x, a) = if &0 < x then real_exp(a · real_log(x)) else if a = &0 then &1 else &0` |
| `RpowExp` | `&0 < x ⇒ real_rpow(x, a) = real_exp(a · real_log(x))` |
| `RpowPositive` | `&0 < x ⇒ &0 < real_rpow(x, a)` |
| `RpowNonneg` | `&0 ≤ real_rpow(x, a)` |
| `RpowZeroExponent` | `real_rpow(x, &0) = &1` |
| `RpowZeroBase` | `a ≠ &0 ⇒ real_rpow(&0, a) = &0` |
| `RpowEqZero` | `&0 ≤ x ∧ a ≠ &0 ⇒ (real_rpow(x, a) = &0 ⇔ x = &0)` |
| `RpowOneExponent` | `&0 ≤ x ⇒ real_rpow(x, &1) = x` |
| `RpowOneBase` | `real_rpow(&1, a) = &1` |
| `RpowAdd` | `&0 < x ⇒ real_rpow(x, a + b) = real_rpow(x, a) · real_rpow(x, b)` |
| `RpowAddOne` | `&0 ≤ x ∧ &0 ≤ a ⇒ real_rpow(x, a + &1) = x · real_rpow(x, a)` |
| `RpowNeg` | `&0 < x ⇒ real_rpow(x, −a) = real_inv(real_rpow(x, a))` |
| `RpowInvBase` | `&0 ≤ x ⇒ real_rpow(real_inv(x), a) = real_inv(real_rpow(x, a))` |
| `LogRpow` | `&0 < x ⇒ real_log(real_rpow(x, a)) = a · real_log(x)` |
| `RpowNat` | `&0 ≤ x ⇒ real_rpow(x, &n) = real_pow(x, n)` |
| `RpowRpow` | `&0 ≤ x ⇒ real_rpow(real_rpow(x, a), b) = real_rpow(x, a · b)` |
| `RpowMulBase` | `&0 ≤ x ∧ &0 ≤ y ⇒ real_rpow(x · y, a) = real_rpow(x, a) · real_rpow(y, a)` |
| `RpowSqrt` | `&0 ≤ x ⇒ real_rpow(x, &1 / &2) = real_sqrt(x)` |
| `RpowLessBase` | `&0 ≤ x ∧ x < y ∧ &0 < a ⇒ real_rpow(x, a) < real_rpow(y, a)` |
| `RpowLessBaseNegative` | `&0 < x ∧ x < y ∧ a < &0 ⇒ real_rpow(y, a) < real_rpow(x, a)` |
| `RpowLessEqBaseNonpos` | `&0 < x ∧ x ≤ y ∧ a ≤ &0 ⇒ real_rpow(y, a) ≤ real_rpow(x, a)` |
| `RpowLessExponent` | `&1 < x ∧ a < b ⇒ real_rpow(x, a) < real_rpow(x, b)` |
| `RpowLessEqExponent` | `&1 ≤ x ∧ a ≤ b ⇒ real_rpow(x, a) ≤ real_rpow(x, b)` |
| `RpowDerivativeBase` | `&0 < x ⇒ real_derivative_at(λy. real_rpow(y, a), x, a · real_rpow(x, a − &1))` |
| `RpowDerivativeExponent` | `&0 < x ⇒ real_derivative_at(λb. real_rpow(x, b), a, real_rpow(x, a) · real_log(x))` |
| `RpowExponentIntegral` | `&1 < x ⇒ real_has_integral(λt. M · δ · real_rpow(x, −δ · t), &0, &1, M · (&1 − real_rpow(x, −δ)) / real_log(x))` |

## Sums and growth of powers (sums.go)

The mean value theorem squeezes the step between consecutive negative
powers $n^{-x}$; summing that squeeze bounds the tail of $\sum n^{-x-1}$ by
$\frac{N^{-x}}{x}$. Its estimates for increments of positive powers n^x give the
head bound $N^x \cdot (1/N + 1/x)$ for $\sum n^{x-1}$. So $\sum n^{-\sigma}$
converges for σ > 1. The logarithm is below every positive power, which
makes $\frac{\log n}{n^\varepsilon}$ tend to 0 and $\sum \log n \cdot n^{-\sigma}$ converge for σ > 1.

| member | statement |
|---|---|
| `RpowStepBounds` | `∀x:real. ∀n:num. &0 < x ∧ 0 < n ⇒ x * real_rpow(&(n + 1), -x - &1) ≤ real_rpow(&n, -x) - real_rpow(&(n + 1), -x) ∧ real_rpow(&n, -x) - real_rpow(&(n + 1), -x) ≤ x * real_rpow(&n, -x - &1)` |
| `RpowTailSumBound` | `∀x:real. ∀N M:num. &0 < x ∧ 0 < N ⇒ Σ_{n∈N + 1 .. M} real_rpow(&n, -x - &1) ≤ real_rpow(&N, -x) / x` |
| `RpowHeadSumBound` | `∀x:real. ∀N:num. &0 < x ∧ 0 < N ⇒ Σ_{n∈1 .. N} real_rpow(&n, x - &1) ≤ real_rpow(&N, x) * (&1 / &N + &1 / x)` |
| `RpowSeriesConverges` | `∀σ:real. &1 < σ ⇒ ∃t:real. real_sums(λn:num. real_rpow(&(n + 1), -σ), t) ∧ t ≤ &1 + &1 / (σ - &1)` |
| `LogLessEqRpow` | `∀ε x:real. &0 < ε ∧ &1 ≤ x ⇒ log(x) ≤ real_rpow(x, ε) / ε` |
| `LogOverRpowTendsToZero` | `∀ε:real. &0 < ε ⇒ (λn:num. log(&(n + 1)) / real_rpow(&(n + 1), ε)) ⟶ &0` |
| `RpowNegTendsToZero` | `∀δ:real. &0 < δ ⇒ (λn:num. real_rpow(&(n + 1), -δ)) ⟶ &0` |
| `LogRpowSeriesConverges` | `∀σ:real. &1 < σ ⇒ ∃t:real. real_sums(λn:num. log(&(n + 1)) * real_rpow(&(n + 1), -σ), t)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
