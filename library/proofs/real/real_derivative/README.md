# real_derivative — the derivative of a real function

A function `f : ℝ → ℝ` has derivative `l` at `c` when its difference
quotient `(f(x) − f(c)) / (x − c)` tends to `l` at `c`:

`real_derivative_at(f, c, l) ⇔ (λx. (f(x) − f(c)) / (x − c)) ⟶ l (at c)`.

The quotient is never looked at in `c` itself — a limit's ball is
punctured — so its value there, a division by zero, plays no part. This
is the chapter where the limits of `real_function_limits` and the
continuity of `real_continuous` become calculus: the rules that compute
a derivative are the algebra of limits applied to difference quotients,
and what a derivative says about its function — Rolle's theorem, the
mean value theorem, the sign of the derivative as a test of
monotonicity — comes from the extreme value theorem through Fermat's
observation that a function has derivative 0 where it is largest.

## How the chapter is organized

**The relation is the object.** `real_derivative_at(f, c, l)` is a
three-place relation, as `real_limit_at` is: every statement names the
derivative it is about, and none carries a side condition that a
derivative exists. There is no `f′` operator and no
`real_differentiable_at`: a theorem about a function that has a
derivative at every point of an interval names the derivative as a
FUNCTION among its variables — `(∀x. a < x ∧ x < b ⇒
real_derivative_at(f, x, f'(x)))` — so the proof has the derivative at
each point in hand, with no existential to open and no uniqueness step
to identify two witnesses.

**Local hypotheses are stated on a given radius**, as in
`real_function_limits`: a local maximum at `c` is `&0 < d ∧ (∀x.
|x − c| < d ⇒ f(x) ≤ f(c))`, the radius an outer variable.

**Continuity on an interval is relative.** Continuity on `⟦a, b⟧` is
`real_continuous_on(⟦a, b⟧, f)`, the relative continuity
of `real_continuous`, so what `f` does outside the interval does not
matter; differentiability is asked only at the interior points.

## The movements

**1. The derivative.** A function has at most one derivative at a
point — two limits of one quotient are one number. A function with a
derivative at `c` is continuous there: `f(x) = f(c) + q(x)·(x − c)` at
every `x`, where `q` is the difference quotient (at `c` itself the factor
`x − c` is 0, whatever `q(c)` is), and the right-hand side tends to
`f(c) + l·0`. So a function with a derivative at every point of a set
is continuous on the set — the form the interval arguments below, and
the chapters above this one, read it in. And a first-order
approximation with a quadratic error bound is a derivative: if
`f(c + h) − f(c)` is `L·h` to within `K·h²` for `|h| < d`, then `L` is
the derivative of `f` at `c` — given `ε`, the radius $\min\left(d, \frac{\varepsilon}{K+1}\right)$
keeps the remainder quotient $\frac{f(x) - f(c) - L \cdot (x-c)}{x-c}$ at
most `K·|x − c| < ε` in size (`K + 1` rather than `K` so nothing divides
by 0; `K` is nonnegative, the bound at `d/2` forcing it). This is the
criterion `exp`, `sin` and `cos` meet from their series bounds. A derivative is
local: two functions that agree on a ball about `c` agree at `c`, so
their difference quotients agree on the punctured ball, and a limit
sees only that ball (`DerivativeLocal`). Equivalently, the derivative is the linear approximation whose error is
small against the distance: `f` has derivative `l` at `c` exactly when,
for every ε > 0, near `c` the increment lies within `ε·|x − c|` of
`l·(x − c)` (`DerivativeIncrement`) — the quotient's distance from `l`
is that error over `|x − c|`.

**2. The rules.** A constant has derivative 0 — its quotient is 0 at
every point — and the identity has derivative 1, its quotient being 1
off the centre. The sum, negative, difference and scalar multiple each
rearrange the quotient into the same operation on the quotients, and the
limit law for that operation finishes; a finite sum $\sum_{k \le n} F(k)$
differentiates term by term, by induction on n with the sum rule
(`DerivativeSum`). The product rule splits the
quotient of `f·g` as `f(x)` times `g`'s quotient plus `g(c)` times `f`'s;
`f(x)` tends to `f(c)` because `f` is continuous at `c`, and the limits
give `l·g(c) + f(c)·m`. The reciprocal rule works on the ball where `g`
stays away from 0 — `g` is continuous at `c` and `g(c) ≠ 0` — on which
the quotient of `1/g` is `−(1/g(c))` times `g`'s quotient times `1/g(x)`;
that tends to $-\frac{m}{g(c)^2}$ by the limit of a reciprocal, and a limit sees
only the ball. The quotient rule is the product of `f` and `1/g`. The
power rule is an induction: $x^{n+1}$ is $x \cdot x^n$, so the product rule
takes $(n+1) \cdot c^n$ to $(n+2) \cdot c^{n+1}$; `x⁰` is the constant 1, and
$n \cdot c^{n-1}$ covers both, the coefficient 0 absorbing the truncated
exponent.

**3. Carathéodory, the chain rule and the inverse.** `f` has derivative
`l` at `c` exactly when its increment factors through a slope continuous
at `c`: `f(x) − f(c) = φ(x)·(x − c)` with `φ` continuous at `c` and
`φ(c) = l`. Off the centre the factorization says `φ(x)` IS the
difference quotient, and a limit at `c` ignores the value at `c` — so
the quotient tends to `l` exactly when `φ` does, which is `φ`'s
continuity once `φ(c) = l`; forward, `φ` is the quotient patched at the
centre with `l`. The chain rule is read through it: the slopes `ψ` of
`g` at `c` and `φ` of `f` at `g(c)` compose,
`f(g(x)) − f(g(c)) = φ(g(x))·ψ(x)·(x − c)`, and the slope `φ(g(x))·ψ(x)`
is continuous at `c` — a composite and a product of continuous functions
— with value `l·m`. No division by `g(x) − g(c)` is ever made, which is
what the naive proof trips on where `g` takes the value `g(c)` near `c`.
The derivative of an inverse function is read through Carathéodory too:
where `f` undoes `g` on a ball about `y`, `f`'s factorization at `g(x)`
reads `x − y = φ(g(x))·(g(x) − g(y))`, so off the centre `φ(g(x))` times
`g`'s difference quotient is `1` — the quotient is `1/φ(g(x))`, and that
`φ(g(x)) ≠ 0` there needs no separate argument. The slope `x ↦ φ(g(x))`
is continuous at `y`, since `g` is, with value `l ≠ 0`, so the quotient
tends to `1/l`.

**4. Local extrema.** Where the derivative is positive, the function
lies below its value just to the left of the point and above it just to
the right: the quotient tends to a positive number, so it is positive on
some punctured ball (`LimitAtPositive`), and the increment
`f(x) − f(c)` is the quotient times `x − c`. A negative derivative is the
mirror, read through `−f`. Fermat's theorem follows: at a point where
`f` is largest on a ball, the derivative is neither positive — a point
just to the right would be higher — nor negative — a point just to the
left would be — so it is 0; at a smallest value, the same for `−f`.

**5. Rolle and the mean value theorem.** A function continuous on
`⟦a, b⟧`, with a derivative strictly between `a` and `b` and
`f(a) = f(b)`, has derivative 0 somewhere strictly between them. The
extreme value theorem hands a point where `f` is largest on `⟦a, b⟧` and
one where it is least; if either is strictly inside, Fermat's theorem
applies there — the ball of radius `min(z − a, b − z)` lies inside
`⟦a, b⟧`. If both are ends, `f` takes the one value `f(a) = f(b)` at
each, so every value on `⟦a, b⟧` is at most `f(a)` and at least `f(a)`:
`f` is largest at every point, the midpoint among them, and Fermat's
theorem applies there. The mean
value theorem tilts `f` by the slope `k` of its chord: `f(x) − k·x` takes
equal values at `a` and `b`, is continuous on `⟦a, b⟧` — the line
`x ↦ k·x` has a derivative everywhere, so is continuous — and has
derivative `f'(x) − k` inside, so Rolle's theorem finds `z` with
`f'(z) = k`, that is `f(b) − f(a) = f'(z)·(b − a)`. Read between any two
points of `⟦a, b⟧` — the interval between them lies in `⟦a, b⟧`, where
continuity and the derivative are inherited — it is the form the
monotonicity criteria use. With the derivative at most `K` in size on an
open interval, the mean value theorem between two of its points bounds
the change of `f` by `K` times their distance (`MeanValueInequality`); with
the derivative within `K` of a slope `d`, the change less `d` times the
step is at most `K` times the step (`MeanValueNearSlope`). Read between two points of an
interval at every point of which f has a derivative, the mean value
theorem is the form the convexity tests use (`MeanValueOnInterval`).

**6. Monotonicity.** Between two points `x < y` of `⟦a, b⟧` the mean
value theorem writes `f(y) − f(x)` as `f'(z)·(y − x)`, so the sign of the
derivative strictly between `a` and `b` decides the order of the values:
nonnegative, `f` is increasing on `⟦a, b⟧`; positive, strictly increasing.
The decreasing criteria are these for `−f`, whose derivative is `−f'`,
and a derivative that is 0 is both nonnegative and nonpositive, so `f` is
constant. The converse is local: a function increasing on a ball about
`c` has a nonnegative derivative there, since its difference quotient is
nonnegative on the punctured ball — the increment and the offset
`x − c` have the same sign on both sides of `c` — and limits respect
`≤`. On an open interval where `f` has a derivative everywhere the two
directions meet: `f` is increasing exactly when `f'` is nonnegative. With
|f′| at most the derivative g′ of a second function, g − f and g + f
both rise on ⟦a, b⟧, so |f(b) − f(a)| ≤ g(b) − g(a)
(`MeanValueComparison`).

## Members

| entry | statement |
|---|---|
| `RealDerivativeAtDef` | `real_derivative_at(f, c, l) ⇔ (λx. (f(x) − f(c)) / (x − c)) ⟶ l (at c)` |
| `DerivativeUnique` | `real_derivative_at(f, c, l) ∧ real_derivative_at(f, c, m) ⇒ l = m` |
| `DerivativeContinuous` | `real_derivative_at(f, c, l) ⇒ real_continuous_at(f, c)` |
| `DerivativeContinuousOn` | `(∀x. x ∈ s ⇒ real_derivative_at(f, x, f'(x))) ⇒ real_continuous_on(s, f)` |
| `DerivativeFromQuadraticRemainder` | `&0 < d ∧ (∀h. real_abs(h) < d ⇒ real_abs(f(c + h) − f(c) − L·h) ≤ K·real_pow(h, 2)) ⇒ real_derivative_at(f, c, L)` |
| `DerivativeIncrement` | `real_derivative_at(f, c, l) ⇔ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x. &0 < real_abs(x − c) ∧ real_abs(x − c) < δ ⇒ real_abs(f(x) − f(c) − l · (x − c)) < ε · real_abs(x − c)` |
| `DerivativeLocal` | `&0 < d ∧ (∀x. real_abs(x − c) < d ⇒ f(x) = g(x)) ∧ real_derivative_at(g, c, l) ⇒ real_derivative_at(f, c, l)` |
| `DerivativeConst` | `real_derivative_at(λx. k, c, &0)` |
| `DerivativeId` | `real_derivative_at(λx. x, c, &1)` |
| `DerivativeAdd` | `real_derivative_at(f, c, l) ∧ real_derivative_at(g, c, m) ⇒ real_derivative_at(λx. f(x) + g(x), c, l + m)` |
| `DerivativeSum` | `(∀k. k ≤ n ⇒ real_derivative_at(F(k), x, G(k))) ⇒ real_derivative_at(λt. Σ_{k∈0 .. n} F(k)(t), x, Σ_{k∈0 .. n} G(k))` |
| `DerivativeNeg` | `real_derivative_at(f, c, l) ⇒ real_derivative_at(λx. −f(x), c, −l)` |
| `DerivativeSub` | `real_derivative_at(f, c, l) ∧ real_derivative_at(g, c, m) ⇒ real_derivative_at(λx. f(x) − g(x), c, l − m)` |
| `DerivativeScale` | `real_derivative_at(f, c, l) ⇒ real_derivative_at(λx. k · f(x), c, k · l)` |
| `DerivativeMul` | `real_derivative_at(f, c, l) ∧ real_derivative_at(g, c, m) ⇒ real_derivative_at(λx. f(x) · g(x), c, l · g(c) + f(c) · m)` |
| `DerivativeInv` | `real_derivative_at(g, c, m) ∧ g(c) ≠ &0 ⇒ real_derivative_at(λx. real_inv(g(x)), c, −m / real_pow(g(c), 2))` |
| `DerivativeDiv` | `real_derivative_at(f, c, l) ∧ real_derivative_at(g, c, m) ∧ g(c) ≠ &0 ⇒ real_derivative_at(λx. f(x) / g(x), c, (l · g(c) − f(c) · m) / real_pow(g(c), 2))` |
| `DerivativePowSuc` | `real_derivative_at(λx. real_pow(x, n + 1), c, &(n + 1) · real_pow(c, n))` |
| `DerivativePow` | `real_derivative_at(λx. real_pow(x, n), c, &n · real_pow(c, n − 1))` |
| `DerivativeCaratheodory` | `real_derivative_at(f, c, l) ⇔ ∃φ. (∀x. f(x) − f(c) = φ(x) · (x − c)) ∧ real_continuous_at(φ, c) ∧ φ(c) = l` |
| `DerivativeChain` | `real_derivative_at(g, c, m) ∧ real_derivative_at(f, g(c), l) ⇒ real_derivative_at(f ∘ g, c, l · m)` |
| `DerivativeInverse` | `real_derivative_at(f, g(y), l) ∧ l ≠ &0 ∧ real_continuous_at(g, y) ∧ &0 < d ∧ (∀x. real_abs(x − y) < d ⇒ f(g(x)) = x) ⇒ real_derivative_at(g, y, real_inv(l))` |
| `PositiveDerivativeRises` | `real_derivative_at(f, c, l) ∧ &0 < l ⇒ ∃d. &0 < d ∧ (∀x. c − d < x ∧ x < c ⇒ f(x) < f(c)) ∧ (∀x. c < x ∧ x < c + d ⇒ f(c) < f(x))` |
| `NegativeDerivativeFalls` | `real_derivative_at(f, c, l) ∧ l < &0 ⇒ ∃d. &0 < d ∧ (∀x. c − d < x ∧ x < c ⇒ f(c) < f(x)) ∧ (∀x. c < x ∧ x < c + d ⇒ f(x) < f(c))` |
| `LocalMaxDerivativeZero` | `&0 < d ∧ (∀x. real_abs(x − c) < d ⇒ f(x) ≤ f(c)) ∧ real_derivative_at(f, c, l) ⇒ l = &0` |
| `LocalMinDerivativeZero` | `&0 < d ∧ (∀x. real_abs(x − c) < d ⇒ f(c) ≤ f(x)) ∧ real_derivative_at(f, c, l) ⇒ l = &0` |
| `Rolle` | `a < b ∧ f(a) = f(b) ∧ real_continuous_on(⟦a, b⟧, f) ∧ (∀x. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x))) ⇒ ∃z. a < z ∧ z < b ∧ f'(z) = &0` |
| `MeanValue` | `a < b ∧ real_continuous_on(⟦a, b⟧, f) ∧ (∀x. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x))) ⇒ ∃z. a < z ∧ z < b ∧ f(b) − f(a) = f'(z) · (b − a)` |
| `MeanValueBetween` | `real_continuous_on(⟦a, b⟧, f) ∧ (∀t. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))) ⇒ ∀x y. a ≤ x ∧ x < y ∧ y ≤ b ⇒ ∃z. x < z ∧ z < y ∧ f(y) − f(x) = f'(z) · (y − x)` |
| `MeanValueOnInterval` | `real_interval(s) ∧ (∀t. t ∈ s ⇒ real_derivative_at(f, t, f'(t))) ∧ x ∈ s ∧ y ∈ s ∧ x < y ⇒ ∃z. x < z ∧ z < y ∧ f(y) − f(x) = f'(z) · (y − x)` |
| `MeanValueInequality` | `(∀t. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))) ∧ (∀t. a < t ∧ t < b ⇒ real_abs(f'(t)) ≤ K) ∧ a < x ∧ x < b ∧ a < y ∧ y < b ⇒ real_abs(f(y) − f(x)) ≤ K · real_abs(y − x)` |
| `MeanValueNearSlope` | `(∀t. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))) ∧ (∀t. a < t ∧ t < b ⇒ real_abs(f'(t) − d) ≤ K) ∧ a < x ∧ x < b ∧ a < y ∧ y < b ⇒ real_abs(f(y) − f(x) − d · (y − x)) ≤ K · real_abs(y − x)` — f tilted by the line of slope d |
| `MeanValueComparison` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ∧ real_continuous_on(⟦a, b⟧, g) ∧ (∀t. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))) ∧ (∀t. a < t ∧ t < b ⇒ real_derivative_at(g, t, g'(t))) ∧ (∀t. a < t ∧ t < b ⇒ real_abs(f'(t)) ≤ g'(t)) ⇒ real_abs(f(b) − f(a)) ≤ g(b) − g(a)` |
| `BoundedSecondDerivativeGrowth` | `(∀t. real_derivative_at(f, t, g(t))) ∧ (∀t. real_derivative_at(g, t, h(t))) ∧ (∀t. \|h(t)\| ≤ M) ⇒ ∃K. &0 ≤ K ∧ (∀x. \|f(x)\| ≤ K * (&1 + x * x) ∧ \|g(x)\| ≤ K * (&1 + \|x\|))` |
| `DerivativeNonnegIncreasing` | `real_continuous_on(⟦a, b⟧, f) ∧ (∀t. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))) ∧ (∀t. a < t ∧ t < b ⇒ &0 ≤ f'(t)) ⇒ ∀x y. a ≤ x ∧ x ≤ y ∧ y ≤ b ⇒ f(x) ≤ f(y)` |
| `DerivativePositiveStrictlyIncreasing` | … `(∀t. a < t ∧ t < b ⇒ &0 < f'(t)) ⇒ ∀x y. a ≤ x ∧ x < y ∧ y ≤ b ⇒ f(x) < f(y)` |
| `DerivativeNonposDecreasing` | … `(∀t. a < t ∧ t < b ⇒ f'(t) ≤ &0) ⇒ ∀x y. a ≤ x ∧ x ≤ y ∧ y ≤ b ⇒ f(y) ≤ f(x)` |
| `DerivativeNegativeStrictlyDecreasing` | … `(∀t. a < t ∧ t < b ⇒ f'(t) < &0) ⇒ ∀x y. a ≤ x ∧ x < y ∧ y ≤ b ⇒ f(y) < f(x)` |
| `DerivativeZeroConstant` | `real_continuous_on(⟦a, b⟧, f) ∧ (∀t. a < t ∧ t < b ⇒ real_derivative_at(f, t, &0)) ⇒ ∀x. a ≤ x ∧ x ≤ b ⇒ f(x) = f(a)` |
| `IncreasingDerivativeNonneg` | `&0 < d ∧ real_increasing_on(⟬c − d, c + d⟭, f) ∧ real_derivative_at(f, c, l) ⇒ &0 ≤ l` |
| `DecreasingDerivativeNonpos` | `&0 < d ∧ real_decreasing_on(⟬c − d, c + d⟭, f) ∧ real_derivative_at(f, c, l) ⇒ l ≤ &0` |
| `IncreasingIffDerivativeNonneg` | `(∀x. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x))) ⇒ (real_increasing_on(⟬a, b⟭, f) ⇔ (∀x. a < x ∧ x < b ⇒ &0 ≤ f'(x)))` |
| `DecreasingIffDerivativeNonpos` | `(∀x. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x))) ⇒ (real_decreasing_on(⟬a, b⟭, f) ⇔ (∀x. a < x ∧ x < b ⇒ f'(x) ≤ &0))` |

A row opening
with `…` shares the hypotheses of the row above it but for the sign of
`f'`. Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
