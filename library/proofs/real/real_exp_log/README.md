# real_exp_log — the exponential function and the logarithm

The exponential function is the sum of its power series, `real_exp(x)`
the `s` with `real_sums(λn. xⁿ / n!, s)`, and the logarithm is its
inverse on the positive reals, `real_log(y)` the `x` with
`real_exp(x) = y`. Both are choices; the chapter's theorems are what
make each choice the one such value. The series gives exp its value at
0, a lower bound and a bound near 0; everything else about exp is read
off the functional equation, which is the Cauchy product of the series
at `x` and at `y`; and everything about log is read off exp.

**The series and the functional equation (exp.go).** The series
converges by the ratio test: past an index `N ≥ 2|x|` each term is at
most half the one before, so `real_exp(x)` is its sum (`ExpSums`). At
0 the series is 1, 0, 0, …, so `exp(0) = 1`. The binomial theorem
divided by `n!` says that the `n`-th term of the Cauchy product of the
series at `x` and at `y` is `(x + y)ⁿ / n!`; both series converge
absolutely — the sizes of the terms at `x` are the terms at `|x|` — so
the Cauchy product (`real_series`) sums to `exp(x)·exp(y)`, and a series
has one sum: `exp(x + y) = exp(x)·exp(y)`. This is the route through
the product of series rather than through differentiating the series
term by term; the derivative comes afterwards, from the functional
equation. Read at `x` and `−x` it makes `exp(−x)` the reciprocal of
`exp(x)`, and by induction on `n` it turns `exp(n·x)` into `exp(x)ⁿ`.

**Order (exp_order.go).** At a nonnegative `x` every term of the
series is nonnegative, so the partial sum `1 + x` is at most the sum:
exp lies above its tangent line at 0 there. `exp(x)` is the square of
`exp(x/2)`, and `exp(x/2)` is not 0 — its product with `exp(−x/2)` is
`exp(0) = 1` — so exp is positive. For `u < v`,
`exp(v) = exp(u)·exp(v − u)` with `exp(v − u) ≥ 1 + (v − u) > 1`, so exp is
strictly increasing, and so it takes each value once.

**The derivative (exp_derivative.go).** `real_series.SumsOffset` removes
the first two terms, 1 and `h`. The remaining series at `h` is dominated for `|h| ≤ 1` by `h²/2` times the
geometric series of `1/2`, since `(n + 2)! ≥ 2ⁿ⁺¹`: `exp(h)` is `1 + h`
to within `h²`. The functional equation carries that bound to every
point: `exp(c + h) − exp(c) − exp(c)·h = exp(c)·(exp(h) − 1 − h)`, at
most `exp(c)·h²` in size for `|h| < 1`, and a first-order approximation
with a quadratic error on a ball is a derivative (`real_derivative`'s
`DerivativeFromQuadraticRemainder`), so exp is its own derivative.
Having a derivative everywhere, exp is continuous, and a `y ≥ 1` lies
between `exp(0) = 1` and `exp(y − 1) ≥ y`: the intermediate value
theorem on `⟦0, y − 1⟧` reaches it, and a positive `y < 1` is `exp(−x)`
where `exp(x) = 1/y`. So the values of exp are exactly the positive
reals.

**The logarithm (log.go).** `log(exp(x))` is a chosen `u` with
`exp(u) = exp(x)`; `x` is one, and exp takes each value once, so
`log(exp(x)) = x`. For positive `y` the choice defining `log(y)`
succeeds, `y` being a value of exp, so `exp(log(y)) = y`. Every law of
log is then a law of exp read backwards: `x·y = exp(log x + log y)`,
`1/x = exp(−log x)`, `xⁿ = exp(n·log x)`, and log undoes exp — and a
quotient is a product with a reciprocal; exp orders `log x` and `log y`
as they stand, so log is strictly increasing, and nonnegative from 1
on. Continuity is the order
again: `y = exp(log y)` lies strictly between `exp(log y − ε)` and
`exp(log y + ε)`, and a point within `y`'s distance to the nearer of the
two lies between them too, so its logarithm is within `ε` of `log y`.
The derivative is the inverse-function rule of `real_derivative`: exp
has derivative `exp(log y) = y ≠ 0` at `log y`, log is continuous at
`y`, and on the ball of radius `y` about `y` exp undoes log — so
`log′(y) = 1/y`. The sequence `1/log(n + 1)` tends to 0.

## Members

| entry | statement |
|---|---|
| `RealExpDef` | `real_exp(x) = εs. real_sums(λn. real_pow(x, n) / &factorial(n), s)` |
| `RealLogDef` | `real_log(y) = εx. real_exp(x) = y` |
| `ExpSums` | `real_sums(λn. real_pow(x, n) / &factorial(n), real_exp(x))` |
| `ExpZero` | `real_exp(&0) = &1` |
| `ExpProductTerm` | `Σ_{k∈0 .. n} real_pow(x, k) / &factorial(k) · (real_pow(y, n − k) / &factorial(n − k)) = real_pow(x + y, n) / &factorial(n)` |
| `ExpAdd` | `real_exp(x + y) = real_exp(x) · real_exp(y)` |
| `ExpNeg` | `real_exp(−x) = real_inv(real_exp(x))` |
| `ExpNatMul` | `real_exp(&n · x) = real_pow(real_exp(x), n)` |
| `ExpLowerBound` | `&0 ≤ x ⇒ &1 + x ≤ real_exp(x)` |
| `ExpPositive` | `&0 < real_exp(x)` |
| `ExpLessIff` | `real_exp(x) < real_exp(y) ⇔ x < y` |
| `ExpInjective` | `real_exp(x) = real_exp(y) ⇔ x = y` |
| `ExpNegMulBound` | `&0 ≤ x ⇒ x * exp(-x) ≤ &1` |
| `ExpQuadraticBound` | `real_abs(h) ≤ &1 ⇒ real_abs(real_exp(h) − &1 − h) ≤ real_pow(h, 2)` |
| `ExpDerivative` | `real_derivative_at(real_exp, c, real_exp(c))` |
| `ExpContinuous` | `real_continuous_on(𝕌, exp)` |
| `ExponentialQuadraticContinuous` | `real_continuous_on(𝕌, λx. c * exp(b * ((x - m) * (x - m))))` |
| `ExpSurjective` | `&0 < y ⇒ ∃x. real_exp(x) = y` |
| `LogExp` | `real_log(real_exp(x)) = x` |
| `ExpLog` | `&0 < y ⇒ real_exp(real_log(y)) = y` |
| `LogOne` | `real_log(&1) = &0` |
| `LogMul` | `&0 < x ∧ &0 < y ⇒ real_log(x · y) = real_log(x) + real_log(y)` |
| `LogInv` | `&0 < x ⇒ real_log(real_inv(x)) = −real_log(x)` |
| `LogDiv` | `&0 < x ∧ &0 < y ⇒ real_log(x / y) = real_log(x) − real_log(y)` |
| `LogPow` | `&0 < x ⇒ real_log(real_pow(x, n)) = &n · real_log(x)` |
| `LogProduct` | `finite(k) ∧ (∀i. i ∈ k ⇒ &0 < x(i)) ⇒ &0 < Π_{i∈k} x(i) ∧ real_log(Π_{i∈k} x(i)) = Σ_{i∈k} real_log(x(i))` |
| `LogLessIff` | `&0 < x ∧ &0 < y ⇒ (real_log(x) < real_log(y) ⇔ x < y)` |
| `LogNonneg` | `&1 ≤ x ⇒ &0 ≤ real_log(x)` |
| `LogPowerLessEq` | for naturals a, b ≥ 1, `a ^ k ≤ b ^ l ⇒ &k * log(&a) ≤ &l * log(&b)` |
| `LogContinuous` | `&0 < y ⇒ real_continuous_at(real_log, y)` |
| `LogDerivative` | `&0 < y ⇒ real_derivative_at(real_log, y, real_inv(y))` |
| `ReciprocalLogTendsToZero` | `(λn. &1 / real_log(&(n + 1))) ⟶ &0` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
