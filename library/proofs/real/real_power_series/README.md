# real_power_series — power series on the real line

A power series converges absolutely inside a radius and diverges outside it. Inside the radius it converges uniformly on every smaller closed interval, so its sum is continuous there and can be differentiated and integrated term by term. The Lambert series of a bounded sequence sums to the power series of its divisor sums.

## The movements

**Abel's lemma and the radius (radius.go).** If the terms a(n)·rⁿ stay
bounded by B, then at |x| < |r| each |a(n)·xⁿ| is at most B·qⁿ with
q = |x|/|r| < 1, so the series converges absolutely by comparison with
the geometric series. A series that converges at r has bounded terms
(`real_series.SumsTermsBounded`), so the same holds; read on an interval, a series
converging on ⟬−R, R⟭ converges absolutely there, and between |x| and R
lies a ρ at which the series without its first term converges
absolutely (`PowerSeriesAbsoluteBeyond`). The radii r at which
the terms stay bounded form a set S holding 0. If S is unbounded the
series converges absolutely everywhere. Otherwise R = sup S: below R
lies a point of S, where Abel's lemma applies, and wherever the series
converges its terms are bounded, so |x| ∈ S and |x| ≤ R.

**The derived and integrated series (derived.go).** On ⟦0, ∞⟭ the power
tⁿ⁺¹ lies above its tangent line (`real_pow.PowAboveTangentLine`). Read
at the ρ of `PowerSeriesAbsoluteBeyond` it gives
(n + 1)·|x|ⁿ·(ρ − |x|) ≤ ρⁿ⁺¹, so each term of the derived series is at
most $\frac{\lvert a(n+1) \cdot \rho^{n+1} \rvert}{\rho - \lvert x \rvert}$, the series of sizes at ρ with its first
term dropped. Each term of the integrated series is at most
|x|·|a(n)·xⁿ|.

**Term-by-term differentiation (derivative.go).** The remainder
Gₙ = (c + h)ⁿ⁺¹ − cⁿ⁺¹ − (n + 1)cⁿh obeys Gₙ₊₁ = (c + h)Gₙ + (n + 1)cⁿh²,
and the same remainder of (|c| + δ)ⁿ⁺¹ at |c| obeys the same recurrence
with |c| + δ and δ; since |c + h| ≤ |c| + δ, induction gives
δ²|Gₙ| ≤ h²(|c| + δ)ⁿ⁺¹. Inside the radius, f(c + h) − f(c) − h·d is the
sum of the series a(n + 1)·Gₙ, dominated by (h/δ)² times the series of
sizes at the ρ of `PowerSeriesAbsoluteBeyond`, δ = ρ − |c|. So the increment is d·h up to a constant times h²,
and `real_derivative.DerivativeFromQuadraticRemainder` makes d the
derivative.

**Uniform convergence and continuity (uniform.go).** For 0 ≤ r < R the
series converges absolutely at r. On ⟦−r, r⟧ each |a(n)·xⁿ| is at most
|a(n)·rⁿ|, so the Weierstrass M-test gives a uniform limit of the
partial sums there, and that limit is the sum f, a series having only
one sum (`real_uniform_convergence.UniformLimitCongruence`). The partial sums are polynomials, hence continuous, so f is
continuous on ⟦−r, r⟧. For |c| < R, take r halfway between |c| and R:
⟦−r, r⟧ holds the ball of radius r − |c| about c, and a function
continuous on a set holding a ball about c is continuous at c
(`real_continuous.ContinuousAtInterior`).

**Term-by-term integration (integral.go).** The sum F of the integrated
series $\sum a(n) \cdot \frac{x^{n+1}}{n+1}$ is itself a power series, with coefficients
b(0) = 0 and $b(n+1) = \frac{a(n)}{n+1}$; its derived series is the original
series, so term-by-term differentiation makes F an antiderivative of
the sum f inside the radius (`PowerSeriesAntiderivative`). Both f and F
are continuous there, so on every ⟦u, v⟧ inside ⟬−R, R⟭ the
Newton–Leibniz theorem (`real_integral.NewtonLeibnizContinuous`) makes F(v) − F(u) the integral of f. Every term
vanishes at 0, so F(0) = 0; for x ≥ 0 the integral from 0 to x is F(x),
and for x < 0 the oriented integral is minus the integral over ⟦x, 0⟧,
which is F(x) again.

**The Lambert series (lambert.go).** For a sequence a bounded by 1 in
size and 0 ≤ t < 1, the Lambert series $\sum_{n \ge 1} a(n) \cdot \frac{t^n}{1-t^n}$ converges, and its
sum is that of the power series whose n-th coefficient is the divisor
sum $\sum_{d \mid n} a(d)$.

## Members

| entry | statement |
|---|---|
| `PowerSeriesAbelBounded` | `(∀n. real_abs(a(n) · rⁿ) ≤ B) ∧ real_abs(x) < real_abs(r) ⇒ ∃s. real_sums(λn. real_abs(a(n) · xⁿ), s)` |
| `PowerSeriesAbel` | `(∃s. real_sums(λn. a(n) · rⁿ, s)) ∧ real_abs(x) < real_abs(r) ⇒ ∃s. real_sums(λn. real_abs(a(n) · xⁿ), s)` |
| `PowerSeriesAbsoluteInside` | `(∀y. real_abs(y) < R ⇒ ∃s. real_sums(λn. a(n) · yⁿ, s)) ∧ real_abs(x) < R ⇒ ∃s. real_sums(λn. real_abs(a(n) · xⁿ), s)` |
| `PowerSeriesAbsoluteBeyond` | `(∀y. real_abs(y) < R ⇒ ∃s. real_sums(λn. a(n) · yⁿ, s)) ∧ real_abs(x) < R ⇒ ∃ρ t. real_abs(x) < ρ ∧ ρ < R ∧ real_sums(λn. real_abs(a(n + 1) · ρⁿ⁺¹), t)` |
| `RadiusOfConvergence` | `(∀x. ∃s. real_sums(λn. real_abs(a(n) · xⁿ), s)) ∨ ∃R. &0 ≤ R ∧ (∀x. real_abs(x) < R ⇒ ∃s. real_sums(λn. real_abs(a(n) · xⁿ), s)) ∧ (∀x. R < real_abs(x) ⇒ ¬∃s. real_sums(λn. a(n) · xⁿ, s))` |
| `PowerSeriesDerivedConverges` | `(∀y. real_abs(y) < R ⇒ ∃s. real_sums(λn. a(n) · yⁿ, s)) ∧ real_abs(x) < R ⇒ ∃s. real_sums(λn. real_abs(&(n + 1) · a(n + 1) · xⁿ), s)` |
| `PowerSeriesIntegratedConverges` | `(∀y. real_abs(y) < R ⇒ ∃s. real_sums(λn. a(n) · yⁿ, s)) ∧ real_abs(x) < R ⇒ ∃s. real_sums(λn. a(n) · xⁿ⁺¹ / &(n + 1), s)` |
| `PowRemainderBound` | `real_abs(h) ≤ δ ⇒ δ² · real_abs((c + h)ⁿ⁺¹ − cⁿ⁺¹ − &(n + 1) · cⁿ · h) ≤ h² · (real_abs(c) + δ)ⁿ⁺¹` |
| `PowerSeriesDerivative` | `(∀x. real_abs(x) < R ⇒ real_sums(λn. a(n) · xⁿ, f(x))) ∧ real_abs(c) < R ⇒ ∃d. real_sums(λn. &(n + 1) · a(n + 1) · cⁿ, d) ∧ real_derivative_at(f, c, d)` |
| `PowerSeriesUniform` | `(∀x. real_abs(x) < R ⇒ real_sums(λn. a(n) · xⁿ, f(x))) ∧ &0 ≤ r ∧ r < R ⇒ real_converges_uniformly_on({x \| real_abs(x) ≤ r}, λn x. Σ_{k∈0 .. n} a(k) · xᵏ, f)` |
| `PowerSeriesContinuous` | `(∀x. real_abs(x) < R ⇒ real_sums(λn. a(n) · xⁿ, f(x))) ∧ real_abs(c) < R ⇒ real_continuous_at(f, c)` |
| `PowerSeriesAntiderivative` | `(∀x. real_abs(x) < R ⇒ real_sums(λn. a(n) · xⁿ, f(x))) ∧ (∀x. real_abs(x) < R ⇒ real_sums(λn. a(n) · xⁿ⁺¹ / &(n + 1), F(x))) ∧ real_abs(c) < R ⇒ real_derivative_at(F, c, f(c))` |
| `PowerSeriesIntegral` | `(∀y. real_abs(y) < R ⇒ real_sums(λn. a(n) · yⁿ, f(y))) ∧ real_abs(x) < R ⇒ real_sums(λn. a(n) · xⁿ⁺¹ / &(n + 1), real_integral(f, &0, x))` |
| `LambertExpansion` | `(∀n. real_abs(a(n)) ≤ &1) ∧ &0 ≤ t ∧ t < &1 ⇒ ∃S. real_sums(λn. a(n + 1) · tⁿ⁺¹ / (&1 − tⁿ⁺¹), S) ∧ real_sums(λn. (Σ_{d∈{d \| d ∣ n + 1}} a(d)) · tⁿ⁺¹, S)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
