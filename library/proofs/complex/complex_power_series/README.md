# complex_power_series — power series of a complex variable: absolute convergence inside the radius, the derivative term by term, the exponential as its own derivative and the cosine and the sine as each other's up to sign

A power series `Σ a(n)·zⁿ` that converges at every point of the disc
`|z| < R` converges absolutely there, and so does its derived series
`Σ (n + 1)·a(n + 1)·zⁿ`; its sum is holomorphic on the disc, with the
derived series' sum as its derivative. The same holds about any centre
c, and there the sum determines the coefficients. The chapter is the complex
twin of `real_power_series`, stated over `complex_sums` with the
modulus where the line has the absolute value. The exponential, the
cosine and the sine are power series converging everywhere, so each has
a derivative at every point: exp is its own derivative, the sine's is
the cosine and the cosine's is minus the sine; and exp turns sums into
products.

## Convergence inside the radius (series.go)

If the terms a(n)·rⁿ stay bounded by B, then at |z| < |r| each
|a(n)·zⁿ| is at most B·qⁿ with q = |z|/|r| < 1, so the series converges
absolutely by comparison with the geometric series. A series converging
at r has bounded terms: its real and imaginary parts are convergent real
series, and a number is at most the sum of its parts' sizes. So a series
converging on the disc |z| < R converges absolutely there, by Abel's
lemma at the real point $\frac{\lvert z \rvert + R}{2}$. Between |z| and R lies a radius ρ
at which the series without its first term converges absolutely; on
⟦0, ∞⟭ the power tⁿ⁺¹ lies above its tangent line, which gives
(n + 1)·|z|ⁿ·(ρ − |z|) ≤ ρⁿ⁺¹, so each term of the derived series is at
most $\frac{\lvert a(n+1) \cdot \rho^{n+1} \rvert}{\rho - \lvert z \rvert}$ and the derived series converges
absolutely by comparison.

| member | statement |
|---|---|
| `PowerSeriesAbelBounded` | `(∀n. \|a(n) · rⁿ\| ≤ B) ∧ \|z\| < \|r\| ⇒ ∃s. real_sums(λn. \|a(n) · zⁿ\|, s)` |
| `PowerSeriesAbel` | `(∃s. complex_sums(λn. a(n) · rⁿ, s)) ∧ \|z\| < \|r\| ⇒ ∃s. real_sums(λn. \|a(n) · zⁿ\|, s)` |
| `PowerSeriesAbsoluteInside` | `(∀w. \|w\| < R ⇒ ∃s. complex_sums(λn. a(n) · wⁿ, s)) ∧ \|z\| < R ⇒ ∃s. real_sums(λn. \|a(n) · zⁿ\|, s)` |
| `PowerSeriesAbsoluteBeyond` | the same hypotheses `⇒ ∃ρ t. \|z\| < ρ ∧ ρ < R ∧ real_sums(λn. \|a(n + 1) · &ρⁿ⁺¹\|, t)` |
| `PowerSeriesDerivedConverges` | the same hypotheses `⇒ ∃s. real_sums(λn. \|complex_of_real(&(n + 1)) · a(n + 1) · zⁿ\|, s)` |

## Term-by-term differentiation (derivative.go)

The remainder Gₙ = (c + h)ⁿ⁺¹ − cⁿ⁺¹ − (n + 1)cⁿh obeys
Gₙ₊₁ = (c + h)Gₙ + (n + 1)cⁿh². The real remainder of (|c| + δ)ⁿ⁺¹ at
|c| obeys the same recurrence with |c| + δ and δ, so since
|c + h| ≤ |c| + δ, induction gives δ²|Gₙ| ≤ |h|²(|c| + δ)ⁿ⁺¹. Inside the
disc, f(c + h) − f(c) − h·d is the sum of the series a(n + 1)·Gₙ, which
is dominated by (|h|/δ)² times the series of sizes at the ρ of
`PowerSeriesAbsoluteBeyond`, with δ = ρ − |c|. So the increment is d·h to
within a constant times |h|², and that makes d the derivative
(`complex_derivative.DerivativeFromQuadraticRemainder`).

| member | statement |
|---|---|
| `PowRemainderBound` | `\|h\| ≤ δ ⇒ δ² · \|(c + h)ⁿ⁺¹ − cⁿ⁺¹ − complex_of_real(&(n + 1)) · cⁿ · h\| ≤ \|h\|² · (\|c\| + δ)ⁿ⁺¹` |
| `PowerSeriesDerivative` | `(∀z. \|z\| < R ⇒ complex_sums(λn. a(n) · zⁿ, f(z))) ∧ \|c\| < R ⇒ ∃d. complex_sums(λn. complex_of_real(&(n + 1)) · a(n + 1) · cⁿ, d) ∧ complex_derivative_at(f, c, d)` |
| `PowerSeriesHolomorphic` | `(∀z. \|z\| < R ⇒ complex_sums(λn. a(n) · zⁿ, f(z))) ⇒ holomorphic_on({z \| \|z\| < R}, f)` |

## A power series about a centre (centred.go)

A power series a about c that converges on the disc of radius R has, at
each point w of the disc, the sum of the derived series as its
derivative: moved to 0 it is a series in u = z − c, differentiated term
by term at w − c, and the chain rule through z ↦ z − c, of derivative 1,
brings the derivative back. So its sum is holomorphic on the disc. At c
every term after the first carries the factor c − c = 0, so the series
sums to its constant coefficient. Suppose the sum is 0 throughout a
punctured disc about c: then the function equal to a(0) at c and to 0
elsewhere is the sum on the whole disc, so continuous at c, yet 0 at
points as near c as we like, so a(0) = 0. Dropping that term and dividing
by z − c gives a series of the same kind, so induction makes every
coefficient 0. Two series with one sum near c differ by such a series, so
they have the same coefficients. A series whose first m coefficients
vanish keeps its sum when they are dropped; the series of the rest
converges on the same disc, and (z − c)ᵐ times its sum is the first
series' sum.

| member | statement |
|---|---|
| `PowerSeriesDerivativeDisc` | `(∀z. \|z − c\| < R ⇒ complex_sums(λn. a(n) * (z − c) ^ n, f(z))) ∧ \|w − c\| < R ⇒ ∃d. complex_sums(λn. &(n + 1) * a(n + 1) * (w − c) ^ n, d) ∧ complex_derivative_at(f, w, d)` |
| `PowerSeriesHolomorphicDisc` | `(∀z. \|z − c\| < R ⇒ complex_sums(λn. a(n) * (z − c) ^ n, f(z))) ⇒ holomorphic_on({z \| \|z − c\| < R}, f)` |
| `PowerSeriesAtCentre` | `complex_sums(λn. a(n) * (c − c) ^ n, a(0))` |
| `CoefficientsVanish` | `&0 < ρ ∧ (∀z. &0 < \|z − c\| ∧ \|z − c\| < ρ ⇒ complex_sums(λk. a(k) * (z − c) ^ k, &0)) ⇒ a(n) = &0` |
| `CoefficientsUnique` | `&0 < ρ ∧ (∀z. \|z − c\| < ρ ⇒ complex_sums(λn. a(n) * (z − c) ^ n, g(z))) ∧` the same for b `⇒ a = b` |
| `PowerSeriesFactor` | `(∀z. \|z − c\| < R ⇒ complex_sums(λn. a(n) * (z − c) ^ n, f(z))) ∧ (∀k. k < m ⇒ a(k) = &0) ⇒ ∃h. (∀z. \|z − c\| < R ⇒ complex_sums(λn. a(n + m) * (z − c) ^ n, h(z))) ∧ (∀z. \|z − c\| < R ⇒ f(z) = (z − c) ^ m * h(z))` |

## The exponential, the cosine and the sine (exp.go)

The exponential is a power series converging everywhere, with
coefficients 1/n!. Term-by-term differentiation gives it a derivative at
z, the sum of the derived series, whose coefficients $\frac{n+1}{(n+1)!}$ are
again $\frac{1}{n!}$, so that sum is exp(z). The chain rule turns this into the derivative exp(g(s))·d of z ↦ exp(g(z)) where g has derivative d at s, k·exp(k·c) for w ↦ exp(k·w). The sine and the cosine are
$\frac{\exp(i \cdot w) - \exp(-i \cdot w)}{2i}$ and $\frac{\exp(i \cdot w) + \exp(-i \cdot w)}{2}$, so their
derivatives are the cosine and minus the sine, since 1/i = −i. exp turns sums into products: with
z + w fixed, h(v) = exp(v)·exp(z + w − v) has derivative 0 everywhere, by
the product rule and the chain rule through v ↦ z + w − v, so h is constant on the plane, which is convex, and exp(z)·exp(w) = h(z) = h(0) = exp(z + w); then
exp(z)·exp(−z) = exp(0) = 1, so exp never vanishes. The modulus of exp(z)
is the real exponential of re z: exp(z) = exp(re z)·exp(i·im z), and the
second factor has modulus 1. On a right half-plane a holomorphic f with
f′ = f·g′ is a constant multiple of exp(g): f/exp(g) has derivative 0 there, and the half-plane is convex, re being affine along a segment, so f/exp(g) is constant.

| member | statement |
|---|---|
| `ExpDerivative` | `complex_derivative_at(exp, z, exp(z))` |
| `ExpChainDerivative` | `complex_derivative_at(g, s, d) ⇒ complex_derivative_at(λz. exp(g(z)), s, exp(g(s)) * d)` |
| `ExpScaledDerivative` | `complex_derivative_at(λw. exp(k * w), c, k * exp(k * c))` |
| `SinDerivative` | `complex_derivative_at(sin, z, cos(z))` |
| `CosDerivative` | `complex_derivative_at(cos, z, −sin(z))` |
| `ExpAdd` | `exp(z + w) = exp(z) * exp(w)` |
| `ExpNonzero` | `exp(z) ≠ &0` |
| `AbsExp` | `\|exp(z)\| = exp(re(z))` |
| `ExponentialOfPrimitive` | `∀f g f' g':(complex → complex). ∀c:real. (∀s:complex. c < re(s) ⇒ complex_derivative_at(f, s, f'(s))) ∧ (∀s:complex. c < re(s) ⇒ complex_derivative_at(g, s, g'(s))) ∧ (∀s:complex. c < re(s) ⇒ f'(s) = f(s) * g'(s)) ⇒ ∃C:complex. ∀s:complex. c < re(s) ⇒ f(s) = C * exp(g(s))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
