# real_inverse_trigonometry — the tangent, the arctangent and the arcsine

The tangent is the sine over the cosine. It maps the open interval ⟬−π/2, π/2⟭ increasingly onto the line, and the sine maps ⟦−π/2, π/2⟧ increasingly onto ⟦−1, 1⟧. Their inverses, the arctangent and the arcsine, are differentiable where the derivative of the forward function is nonzero. Comparing the derivative of the arctangent with the derivatives of the partial sums of its series on ⟦0, 1⟧ gives Leibniz's series for π/4.

## The movements

**The definitions (definitions.go).** The tangent is sin/cos at every
point; where the cosine vanishes it is a division by 0 that no theorem
depends on. The arctangent and the arcsine are choices, as π is: arctan y is
a point of ⟬−π/2, π/2⟭ where the tangent is y, and arcsin y is a point
of ⟦−π/2, π/2⟧ where the sine is y.

**The tangent (tangent.go).** It is odd. By the quotient rule its
derivative where cos ≠ 0 is $\frac{\cos^2 + \sin^2}{\cos^2} = 1 + \tan^2$. The cosine
is positive on ⟬−π/2, π/2⟭, so the tangent has a derivative at every
point of a closed interval inside it, is continuous there, and rises
strictly, 1 + tan² being positive. It takes every value y: with
$h = \frac{\pi}{8(\lvert y \rvert + 1)}$, tan(π/2 − h) = cos h / sin h, where sin h ≤ h and
cos h > 1/2, so the tangent exceeds |y| at π/2 − h and, being odd, is
below −|y| at −(π/2 − h); the intermediate value theorem finds y between
the two. And tan(π/4) = 1, the sine and the cosine agreeing there.

**The arctangent (arctangent.go).** The tangent takes every value, so
the chosen point exists: arctan y lies in ⟬−π/2, π/2⟭ and
tan(arctan y) = y. The tangent rises strictly, so arctan(tan x) = x on
the interval, arctan 0 = 0 and arctan 1 = π/4. The derivative of the inverse is
`real_derivative.DerivativeInverse`: the tangent has derivative
1 + y² ≠ 0 at arctan y, and the arctangent is continuous at y by
`real_continuous.MonotoneInverseContinuous`, the tangent being strictly
increasing on the open interval, which holds a ball about arctan y.

**The arcsine (arcsine.go).** The same choice argument on ⟦−π/2, π/2⟧
gives the bounds, sin(arcsin y) = y for |y| ≤ 1, and arcsin(sin x) = x.
For |y| < 1, arcsin y is neither end, the sine being ±1 there, so the
cosine is positive at arcsin y and, its square being 1 − y², equals
√(1 − y²). `DerivativeInverse` applies on the ball of radius 1 − |y|
about y, continuity again from `MonotoneInverseContinuous`.

**Leibniz's series (leibniz.go).** The partial sum P of the arctangent series, $\sum_{k \le n} (-1)^k \frac{t^{2k+1}}{2k+1}$,
has derivative $\sum_{k \le n} (-t^2)^k$ (`real_derivative.DerivativeSum`), so the remainder R = arctan − P has
derivative $\frac{1}{1+t^2} - \sum_{k \le n} (-t^2)^k$, which the geometric sum makes
$\frac{(-t^2)^{n+1}}{1+t^2}$: at most $t^{2n+2}$ in size, the derivative of
$G(t) = \frac{t^{2n+3}}{2n+3}$. A function whose derivative is bounded in size
by another's changes by no more than that one does (g − f and g + f both
rise: `real_derivative.MeanValueComparison`), so on ⟦0, 1⟧, $\lvert R(1) - R(0) \rvert \le G(1) - G(0) = \frac{1}{2n+3}$. With
R(0) = 0 and $R(1) = \pi/4 - \sum_{k \le n} \frac{(-1)^k}{2k+1}$, each partial sum lies
within $\frac{1}{2n+3}$ of π/4, and the series sums to π/4.

## Members

| entry | statement |
|---|---|
| `RealTanDef` | `real_tan(x) = real_sin(x) / real_cos(x)` |
| `RealArctanDef` | `real_arctan(y) = εx. −(pi / &2) < x ∧ x < pi / &2 ∧ real_tan(x) = y` |
| `RealArcsinDef` | `real_arcsin(y) = εx. −(pi / &2) ≤ x ∧ x ≤ pi / &2 ∧ real_sin(x) = y` |
| `TanNeg` | `real_tan(−x) = −real_tan(x)` |
| `TanDerivative` | `real_cos(c) ≠ &0 ⇒ real_derivative_at(real_tan, c, &1 + real_pow(real_tan(c), 2))` |
| `TanDerivativeHalfPi` | `−(pi / &2) < t ∧ t < pi / &2 ⇒ real_derivative_at(real_tan, t, &1 + real_pow(real_tan(t), 2))` |
| `TanContinuousOn` | `−(pi / &2) < a ∧ b < pi / &2 ⇒ real_continuous_on(⟦a, b⟧, real_tan)` |
| `TanStrictlyIncreasing` | `−(pi / &2) < x ∧ x < y ∧ y < pi / &2 ⇒ real_tan(x) < real_tan(y)` |
| `TanSurjective` | `∃x. −(pi / &2) < x ∧ x < pi / &2 ∧ real_tan(x) = y` |
| `TanPiQuarter` | `real_tan(pi / &4) = &1` |
| `ArctanSpec` | `−(pi / &2) < real_arctan(y) ∧ real_arctan(y) < pi / &2 ∧ real_tan(real_arctan(y)) = y` |
| `ArctanBounds` | `−(pi / &2) < real_arctan(y) ∧ real_arctan(y) < pi / &2` |
| `TanArctan` | `real_tan(real_arctan(y)) = y` |
| `ArctanTan` | `−(pi / &2) < x ∧ x < pi / &2 ⇒ real_arctan(real_tan(x)) = x` |
| `ArctanOne` | `real_arctan(&1) = pi / &4` |
| `ArctanZero` | `real_arctan(&0) = &0` |
| `ArctanDerivative` | `real_derivative_at(real_arctan, y, real_inv(&1 + real_pow(y, 2)))` |
| `ArcsinSpec` | `real_abs(y) ≤ &1 ⇒ −(pi / &2) ≤ real_arcsin(y) ∧ real_arcsin(y) ≤ pi / &2 ∧ real_sin(real_arcsin(y)) = y` |
| `ArcsinBounds` | `real_abs(y) ≤ &1 ⇒ −(pi / &2) ≤ real_arcsin(y) ∧ real_arcsin(y) ≤ pi / &2` |
| `SinArcsin` | `real_abs(y) ≤ &1 ⇒ real_sin(real_arcsin(y)) = y` |
| `ArcsinSin` | `−(pi / &2) ≤ x ∧ x ≤ pi / &2 ⇒ real_arcsin(real_sin(x)) = x` |
| `ArcsinDerivative` | `real_abs(y) < &1 ⇒ real_derivative_at(real_arcsin, y, real_inv(real_sqrt(&1 − real_pow(y, 2))))` |
| `LeibnizPartialDerivative` | `real_derivative_at(λt. Σ_{k∈0 .. n} real_pow(−&1, k) · real_pow(t, 2k + 1) / &(2k + 1), x, Σ_{k∈0 .. n} real_pow(−real_pow(x, 2), k))` |
| `LeibnizRemainderBound` | `real_abs(pi / &4 − Σ_{k∈0 .. n} real_pow(−&1, k) / &(2k + 1)) ≤ real_inv(&(2n + 3))` |
| `LeibnizPi` | `real_sums(λn. real_pow(−&1, n) / &(2n + 1), pi / &4)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
