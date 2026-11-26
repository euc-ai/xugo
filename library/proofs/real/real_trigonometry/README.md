# real_trigonometry — the sine, the cosine and π

The cosine and the sine are sums of power series, `cos(x)` the `s`
with `real_sums(λn. (−1)ⁿ·x²ⁿ/(2n)!, s)` and `sin(x)` the `s` with
`real_sums(λn. (−1)ⁿ·x²ⁿ⁺¹/(2n+1)!, s)` — the even and the odd terms of
the exponential series with alternating signs. Both are choices, as
`real_exp` is; the chapter's theorems are what make each choice the one
sum. Everything else is read off the two series in three places: the
addition formulas, which are the Cauchy product of the series with the
binomial theorem split by the parity of its index; the Taylor bounds,
which are the alternating-series estimate; and the derivatives, which
follow from the addition formulas and the bounds near 0, with no
termwise differentiation anywhere — the exponential chapter's route. π
is twice the zero of the cosine between 0 and 2: the cosine is 1 at 0,
negative at 2, and its derivative −sin is negative in between, so it
has exactly one zero there.

Write $c_k(x) = (-1)^k \cdot \frac{x^{2k}}{(2k)!}$ and $s_k(x) = (-1)^k \cdot \frac{x^{2k+1}}{(2k+1)!}$ for the
terms of the two series.

**The series (series.go).** The size of cₙ(x) is $\frac{(x \cdot x)^n}{(2n)!}$, and n! ≤
(2n)!, so it is at most $\frac{(x \cdot x)^n}{n!}$, the n-th term of the exponential
series at x·x; the sine's term is at most |x| times such a term. So both
series converge absolutely, by comparison with the exponential series,
and hence converge — the comparison test read against the series of
their own sizes — and the two choices are their sums. At 0 every partial
sum of the cosine series is its first term, 1. An even power forgets the
sign and an odd one keeps it, so the series at −x is the series at x for
the cosine and its negative for the sine: the cosine is even and the
sine odd, and sin 0 = −sin 0 = 0.

**The addition formulas (addition.go).** The Cauchy product of two of
the series has as its n-th term a sum Σ_{k∈0 .. n} of products of their
terms. The binomial theorem divided by N! writes $\frac{(x+y)^N}{N!}$ as the sum
of the terms $\frac{x^j}{j!} \cdot \frac{y^{N-j}}{(N-j)!}$, and split by the parity of j
(`iterate/real/real_sum`'s `IntervalEvenOdd`; the binomial theorem divided by
N! is `real_exp_log`'s `ExpProductTerm`) that sum is two such Cauchy
terms, up to signs: at N = 2n + 1 the even j give the product of the
cosine series at x with the sine series at y and the odd j the product
of the sine series at x with the cosine series at y, each carrying the
sign (−1)ⁿ (`SinProductTerm`); at N = 2(n + 1) the even j give the
(n+1)-th term of the product of the two cosine series and the odd j,
with the opposite sign, the n-th term of the product of the two sine
series (`CosProductTerm`). Both series converge absolutely, so the
Cauchy products sum to the products of the sums (`real_series`'s
`CauchyProduct`), and a series has one sum: sin(x + y) = sin x·cos y +
cos x·sin y. For the cosine the indices are one apart — the n-th term of
the sine product has degree 2n + 2 — so the series are shifted: the
cosine series at x + y from its second term on, plus the sine product,
is the cosine product from its second term on, and that series has the
two sums cos(x + y) − 1 + sin x·sin y and cos x·cos y − 1. Read at x and
−x, the cosine's formula is the circle: 1 = cos 0 = cos x·cos(−x) − sin
x·sin(−x) = cos²x + sin²x; so neither value is larger than 1 in size.

**The estimates (estimates.go).** Past its first term the sine series
at x ∈ ⟦0, 2⟧ is alternating, and its terms do not increase — each is
the one before times $\frac{x^2}{(2n+2)(2n+3)} \le 1$ — so the alternating-series
bound (`real_series`'s `AlternatingBound`) puts x − sin x between 0 and
the first of them, x³/6. `real_series.SumsOffset` removes the first two
terms of the cosine series; at |x| ≤ 2 the tail is alternating in the
same way, which puts cos x − (1 − x²/2)
between 0 and x⁴/24. At 2 the upper bound is 1 − 2 + 16/24 = −1/3, so
cos 2 < 0; on ⟬0, 2⟭ the lower bound x − x³/6 is positive, so is the
sine. Near 0 the two bounds make cos h equal to 1 and sin h equal to h,
each to within h².

**The derivatives (derivative.go).** The addition formula writes the
increment sin(c + h) − sin c less its linear part cos c·h as sin c·(cos
h − 1) + cos c·(sin h − h); for |h| < 1 each term is at most h² in size,
since |sin c|, |cos c| ≤ 1 and the two remainders are at most h² by the
bounds near 0. So the increment is cos c·h to within 2h² on the unit
ball, and the quadratic-remainder criterion of `real_derivative` (a
first-order approximation with an error at most K·h² on a ball is a
derivative) makes cos c the derivative. The cosine's increment exceeds
its linear part −sin c·h by cos c·(cos h − 1) − sin c·(sin h − h), at
most 2h² in size in the same way, so cos′ = −sin.

**π (pi.go).** The cosine has a derivative everywhere, so it is
continuous; it is 1 at 0 and negative at 2, so the intermediate value
theorem gives it a zero in ⟦0, 2⟧, and π/2 is the chosen one. Its
derivative −sin is negative on ⟬0, 2⟭, so it falls strictly on ⟦0, 2⟧:
it has no other zero there, and the zero is neither end, so
0 < π < 4. At π/2 the sine's square is 1 − 0 and the sine is positive,
so sin(π/2) = 1; the addition formulas at π/2 and π/2 give cos π = −1
and sin π = 0, and at x and π they give sin(x + π) = −sin x and
cos(x + π) = −cos x; twice over, both have period 2π.

## Members

| entry | statement |
|---|---|
| `RealCosDef` | `cos(x) = εs. real_sums(λn. real_pow(−&1, n) · real_pow(x, 2·n) / &factorial(2·n), s)` |
| `RealSinDef` | `sin(x) = εs. real_sums(λn. real_pow(−&1, n) · real_pow(x, 2·n + 1) / &factorial(2·n + 1), s)` |
| `PiDef` | `π = &2 · (εx. &0 ≤ x ∧ x ≤ &2 ∧ cos(x) = &0)` |
| `CosAbsolutelyConvergent` | `∃s. real_sums(λn. real_abs(cₙ(x)), s)` |
| `SinAbsolutelyConvergent` | `∃s. real_sums(λn. real_abs(sₙ(x)), s)` |
| `CosSums` | `real_sums(λn. cₙ(x), cos(x))` |
| `SinSums` | `real_sums(λn. sₙ(x), sin(x))` |
| `CosZero` | `cos(&0) = &1` |
| `CosNeg` | `cos(−x) = cos(x)` |
| `SinNeg` | `sin(−x) = −sin(x)` |
| `SinZero` | `sin(&0) = &0` |
| `SinProductTerm` | `Σ_{k∈0 .. n} cₖ(x)·sₙ₋ₖ(y) + Σ_{k∈0 .. n} sₖ(x)·cₙ₋ₖ(y) = sₙ(x + y)` |
| `SinAdd` | `sin(x + y) = sin(x) · cos(y) + cos(x) · sin(y)` |
| `CosProductTerm` | `Σ_{k∈0 .. n + 1} cₖ(x)·cₙ₊₁₋ₖ(y) − Σ_{k∈0 .. n} sₖ(x)·sₙ₋ₖ(y) = cₙ₊₁(x + y)` |
| `CosAdd` | `cos(x + y) = cos(x) · cos(y) − sin(x) · sin(y)` |
| `SinSquareAddCosSquare` | `real_pow(sin(x), 2) + real_pow(cos(x), 2) = &1` |
| `SinAbsLessEqOne` | `real_abs(sin(x)) ≤ &1` |
| `CosAbsLessEqOne` | `real_abs(cos(x)) ≤ &1` |
| `CosTaylorBounds` | `real_abs(x) ≤ &2 ⇒ &1 − real_pow(x, 2) / &2 ≤ cos(x) ∧ cos(x) ≤ &1 − real_pow(x, 2) / &2 + real_pow(x, 4) / &24` |
| `SinTaylorBounds` | `&0 ≤ x ∧ x ≤ &2 ⇒ x − real_pow(x, 3) / &6 ≤ sin(x) ∧ sin(x) ≤ x` |
| `CosTwoNegative` | `cos(&2) < &0` |
| `SinPositive` | `&0 < x ∧ x < &2 ⇒ &0 < sin(x)` |
| `CosQuadraticBound` | `real_abs(h) ≤ &1 ⇒ real_abs(cos(h) − &1) ≤ real_pow(h, 2)` |
| `SinQuadraticBound` | `real_abs(h) ≤ &1 ⇒ real_abs(sin(h) − h) ≤ real_pow(h, 2)` |
| `SinDerivative` | `real_derivative_at(sin, c, cos(c))` |
| `CosDerivative` | `real_derivative_at(cos, c, −sin(c))` |
| `CosStrictlyDecreasing` | `&0 ≤ x ∧ x < y ∧ y ≤ &2 ⇒ cos(y) < cos(x)` |
| `PiHalfZero` | `&0 ≤ π / &2 ∧ π / &2 ≤ &2 ∧ cos(π / &2) = &0` |
| `CosEqZeroIff` | `&0 ≤ x ∧ x ≤ &2 ⇒ (cos(x) = &0 ⇔ x = π / &2)` |
| `PiBounds` | `&0 < π ∧ π < &4` |
| `SinPiHalf` | `sin(π / &2) = &1` |
| `CosPi` | `cos(π) = −&1` |
| `SinPi` | `sin(π) = &0` |
| `SinAddPi` | `sin(x + π) = −sin(x)` |
| `CosAddPi` | `cos(x + π) = −cos(x)` |
| `SinPeriodic` | `sin(x + &2 · π) = sin(x)` |
| `CosPeriodic` | `cos(x + &2 · π) = cos(x)` |

In the table cₖ(x) and sₖ(x) abbreviate the terms written out above;
the members state them in full.

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.

## The circle (circle.go)

The derivatives make the sine and the cosine continuous at every point,
so each is a continuous map of the line to itself, and so continuous on
every set of reals. On ⟬0, π⟭ the sine is
positive: below 2 by the Taylor bound, and from 2 on by the symmetry
sin x = sin(π − x), which puts π − x in ⟬0, 2⟭. Every integer multiple of
2π is a period of both — a natural multiple one period at a time, a
negative one read back from x + 2πk — so at an integer multiple of 2π the
cosine is 1 and the sine 0. Conversely, if cos x = 1, write x = 2h + 2πm
with m the integer part of $\frac{x}{2\pi}$ and 0 ≤ h < π: then 1 = cos 2h =
1 − 2·sin²h and the sine is positive on ⟬0, π⟭, so h = 0 and $\frac{x}{2\pi}$ is an
integer. The subtraction formulas carry this to two points: cos s = cos t
and sin s = sin t exactly when s − t is an integer multiple of 2π, so
t ↦ (cos t, sin t) is injective on ⟦0, 2π⟭. It is also onto the unit
circle: given a² + b² = 1, the cosine falls from 1 to −1 on ⟦0, π⟧ and
takes the value a at some t there, where sin t = ±b; if not b, then
t ≠ 0 and 2π − t has the cosine of t and the opposite sine.

| member | statement |
|---|---|
| `CosContinuous` | `continuous_map(real_topology, real_topology, cos)` |
| `SinContinuous` | `continuous_map(real_topology, real_topology, sin)` |
| `SinContinuousOn` | `real_continuous_on(s, sin)` |
| `CosContinuousOn` | `real_continuous_on(s, cos)` |
| `SinPositivePi` | `&0 < x ∧ x < π ⇒ &0 < sin(x)` |
| `CosPeriodicInteger` | `integer(k) ⇒ cos(x + &2 · π · k) = cos(x)` |
| `SinPeriodicInteger` | `integer(k) ⇒ sin(x + &2 · π · k) = sin(x)` |
| `CosOneSinZeroIff` | `cos(x) = &1 ∧ sin(x) = &0 ⇔ integer(x / (&2 · π))` |
| `CosSub` | `cos(x − y) = cos(x) · cos(y) + sin(x) · sin(y)` |
| `SinSub` | `sin(x − y) = sin(x) · cos(y) − cos(x) · sin(y)` |
| `CosSinEqIff` | `cos(s) = cos(t) ∧ sin(s) = sin(t) ⇔ integer((s − t) / (&2 · π))` |
| `CosSinInjective` | `−π < s ∧ s ≤ π ∧ −π < t ∧ t ≤ π ∧ cos(s) = cos(t) ∧ sin(s) = sin(t) ⇒ s = t` |
| `CircleParametrization` | `a · a + b · b = &1 ⇒ ∃t. &0 ≤ t ∧ t < &2 · π ∧ cos(t) = a ∧ sin(t) = b` |

## The quarter turn (quarter.go)

At π/2 the subtraction formulas exchange the two functions:
cos(π/2 − x) = sin x and sin(π/2 − x) = cos x. On ⟬−π/2, π/2⟭ the
cosine is therefore the sine at π/2 − x, a point of ⟬0, π⟭, so it is
positive, and on ⟦−π/2, π/2⟧ it is nonnegative. The cosine is the sine's derivative, so the sine rises
strictly on ⟦−π/2, π/2⟧, from −1 to 1, and the intermediate value
theorem makes every value of ⟦−1, 1⟧ a value there. At π/4, which is
π/2 − π/4, the sine and the cosine agree.

| member | statement |
|---|---|
| `CosSubHalfPi` | `cos(π / &2 − x) = sin(x)` |
| `SinSubHalfPi` | `sin(π / &2 − x) = cos(x)` |
| `CosPositiveHalfPi` | `−(π / &2) < x ∧ x < π / &2 ⇒ &0 < cos(x)` |
| `CosNonnegHalfPi` | `−(π / &2) ≤ t ∧ t ≤ π / &2 ⇒ &0 ≤ cos(t)` |
| `SinStrictlyIncreasingHalfPi` | `−(π / &2) ≤ x ∧ x < y ∧ y ≤ π / &2 ⇒ sin(x) < sin(y)` |
| `SinSurjectiveHalfPi` | `real_abs(y) ≤ &1 ⇒ ∃x. −(π / &2) ≤ x ∧ x ≤ π / &2 ∧ sin(x) = y` |
| `SinEqCosPiQuarter` | `sin(π / &4) = cos(π / &4)` |
