# integral_convergence — almost everywhere convergence and integral limits

Fatou's lemma follows from measure_integral's monotone convergence theorem through the tail infima, measurable by ExtendedMeasurableInf, and dominated convergence from Fatou's lemma at h ± f(n). Almost everywhere convergence is handled by a single measurable zero exceptional set. Convergence in measure is defined beside it: the set where the n-th function lies farther than ε from the limit has measure eventually below any positive bound. The nonnegative integral is a lower integral, so monotone convergence and Fatou ask no measurability of the limit; dominated convergence asks it, because its conclusion contains the limit's integrability and the measure space may be incomplete. The integral limits include convergence in the integral of the absolute difference, and an integrable function is the L¹ limit of its truncations at ±n, bounded functions with integrable squares, and the nonnegative integral against a discrete measure is the weighted discrete mass, so on a finite carrier with nonnegative real weights every real function is integrable to its weighted sum.

## Members

| Entry | Statement |
| --- | --- |
| `ConvergesInMeasureDef` | `converges_in_measure(Ω, μ, Y, Z)`: for `&0 < ε` and `&0 < δ`, eventually `μ({x \| x ∈ Ω ∧ ε < \|Y(n, x) - Z(x)\|}) ≤ extended_of_real(δ)` |
| `ConvergesInMeasureDeviationMass` | `converges_in_measure(Ω, μ, V, Z) ∧ &0 < δ ∧ &0 < ρ ⇒` eventually `extended_to_real(μ({x \| x ∈ Ω ∧ δ < \|V(n, x) - Z(x)\|})) ≤ ρ` |
| `MonotoneConvergenceAE` | nonneg_integral(Ω, S, μ, g) = extended_sup(image(λn:num. nonneg_integral(Ω, S, μ, f(n)), 𝕌)) |
| `DominatedConvergenceAE` | real_integrable(Ω, S, μ, g) ∧ (∀n:num. real_integrable(Ω, S, μ, f(n))) ∧ real_converges_to(λn:num. measure_integral(Ω, S, μ, f(n)), measure_integral(Ω, S, μ, g)) ∧ real_converges_to(λn:num. measure_integral(Ω, S, μ, λx:A. \|f(n, x) - g(x)\|), &0) |
| `IntegralL1Limit` | real_converges_to(λn:num. measure_integral(Ω, S, μ, f(n)), measure_integral(Ω, S, μ, g)) |
| `FatouAE` | nonneg_integral(Ω, S, μ, g) ≤ extended_liminf(λn:num. nonneg_integral(Ω, S, μ, f(n))) |
| `DiscreteNonnegIntegral` | nonneg_integral(J, {E:set(I) \| E ⊆ J}, discrete_measure(J, w), f) = discrete_measure(J, λi:I. w(i) * f(i), J) |
| `FiniteDiscreteIntegral` | on a finite J with nonnegative real weights w, every real f is integrable for the discrete measure and `measure_integral = Σ_{i∈J} w(i) * f(i)` — card |
| `Fatou` | nonneg_integral(Ω, S, μ, λx:A. extended_liminf(λn:num. f(n, x))) ≤ extended_liminf(λn:num. nonneg_integral(Ω, S, μ, f(n))) |
| `DominatedLimitIntegrable` | measurable f(n) converging on Ω to g with `\|f(n)\| ≤ h` on Ω, h integrable ⇒ `\|g\| ≤ h` on Ω and g integrable, under `sigma_algebra_on(Ω, S)` |
| `DominatedLowerLimit` | the same hypotheses and `&0 < ε` ⇒ eventually `measure_integral(Ω, S, μ, g) − ε < measure_integral(Ω, S, μ, f(n))` under `measure_on(Ω, S, μ)` |
| `DominatedConvergence` | the same hypotheses ⇒ g and every f(n) integrable and `measure_integral(Ω, S, μ, f(n)) ⟶ measure_integral(Ω, S, μ, g)` under `measure_on(Ω, S, μ)` |
| `DominatedConvergenceL1` | the same hypotheses ⇒ `measure_integral(Ω, S, μ, λx. \|f(n, x) − g(x)\|) ⟶ &0` under `measure_on(Ω, S, μ)` |
| `BoundedTruncationL1` | the truncations Tₙ(x) = max(−n, min(n, X(x))) of an integrable X have integrable squares Tₙ·Tₙ and `measure_integral(Ω, S, μ, λx. \|Tₙ(x) − X(x)\|) ⟶ &0`, under `measure_on(Ω, S, μ)` |
