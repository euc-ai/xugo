# measure_integral — the integral of a real function on a measure space

A real function is integrable when it is measurable and the integral of the embedding of |f| in [0, ∞] is finite. The integral subtracts the real values of the nonnegative integrals of the embeddings of f and of −f; for integrable functions both values are finite. The total-function convention maps each infinite component to zero through `extended_to_real`; integral laws therefore carry their integrability hypotheses. A measurable function dominated by an integrable one is integrable, and integrable functions are closed under absolute values, sums, multiples and differences, because the nonnegative integral is additive. The integral is linear and monotone, is bounded by the integral of the absolute value, adds over finite sums, integrates indicators, and sees a function up to null sets; two measures that agree on the measurable sets integrate alike, and so do a σ-algebra and a sub-σ-algebra the function is measurable for.

## Members

| Entry | Statement |
| --- | --- |
| `RealIntegrableDef` | real_integrable |
| `RealIntegralDef` | measure_integral |
| `IntegrableAE` | (real_integrable(Ω, S, μ, f) ⇔ real_integrable(Ω, S, μ, g)) ∧ measure_integral(Ω, S, μ, f) = measure_integral(Ω, S, μ, g) |
| `BoundedMeasurableProduct` | real_integrable(Ω, S, μ, λx:A. h(x) * f(x)) ∧ measure_integral(Ω, S, μ, λx:A. \|h(x) * f(x)\|) ≤ C * measure_integral(Ω, S, μ, λx:A. \|f(x)\|) |
| `SubSigmaRealIntegral` | (real_integrable(Ω, G, μ, f) ⇔ real_integrable(Ω, S, μ, f)) ∧ measure_integral(Ω, G, μ, f) = measure_integral(Ω, S, μ, f) |
| `RealIntegrableEqOn` | `real_integrable(Ω, S, μ, f) ∧ (∀x. x ∈ Ω ⇒ f(x) = g(x)) ⇒ real_integrable(Ω, S, μ, g)`, no structure hypothesis |
| `IntegrableDominated` | `real_measurable(Ω, S, f) ∧ (∀x. x ∈ Ω ⇒ \|f(x)\| ≤ h(x)) ∧ real_integrable(Ω, S, μ, h) ⇒ real_integrable(Ω, S, μ, f)`, no structure hypothesis |
| `IntegrablePartsFinite` | `real_integrable(Ω, S, μ, f) ⇒` both `nonneg_integral(Ω, S, μ, λx. extended_of_real(f(x)))` and `nonneg_integral(Ω, S, μ, λx. extended_of_real(−f(x)))` are finite, no structure hypothesis |
| `IntegrableAbs` | `real_integrable(Ω, S, μ, f) ⇒ real_integrable(Ω, S, μ, λx. \|f(x)\|)` under `sigma_algebra_on(Ω, S)` |
| `IntegrableAdd` | `real_integrable(Ω, S, μ, f) ∧ real_integrable(Ω, S, μ, g) ⇒ real_integrable(Ω, S, μ, λx. f(x) + g(x))` under `measure_on(Ω, S, μ)` |
| `IntegrableScale` | `real_integrable(Ω, S, μ, f) ⇒ real_integrable(Ω, S, μ, λx. c * f(x))` under `measure_on(Ω, S, μ)` |
| `IntegrableSub` | `real_integrable(Ω, S, μ, f) ∧ real_integrable(Ω, S, μ, g) ⇒ real_integrable(Ω, S, μ, λx. f(x) − g(x))` under `measure_on(Ω, S, μ)` |
| `IntegralOfNonneg` | f ≥ 0 on Ω ⇒ `measure_integral(Ω, S, μ, f) = extended_to_real(nonneg_integral(Ω, S, μ, λx. extended_of_real(f(x))))`, no integrability and no structure hypothesis |
| `IntegralNonnegEmbedding` | integrable f ≥ 0 on Ω ⇒ its integral, embedded in [0, ∞], is its nonnegative integral, no structure hypothesis |
| `IntegralNonneg` | f ≥ 0 on Ω ⇒ `&0 ≤ measure_integral(Ω, S, μ, f)`, no integrability and no structure hypothesis |
| `IntegralZero` | `measure_integral(Ω, S, μ, λx. &0) = &0`, no hypothesis |
| `IntegralNeg` | `measure_integral(Ω, S, μ, λx. −f(x)) = −measure_integral(Ω, S, μ, f)`, no hypothesis |
| `IntegralScale` | `measure_integral(Ω, S, μ, λx. c * f(x)) = c * measure_integral(Ω, S, μ, f)` under `measure_on(Ω, S, μ)`, no integrability |
| `IntegralMono` | integrable f ≤ g on Ω ⇒ `measure_integral(Ω, S, μ, f) ≤ measure_integral(Ω, S, μ, g)`, no structure hypothesis |
| `IntegralAbsLe` | integrable f ⇒ `\|measure_integral(Ω, S, μ, f)\| ≤ extended_to_real(nonneg_integral(Ω, S, μ, λx. extended_of_real(\|f(x)\|)))`, no structure hypothesis |
| `IntegralAbsSubLe` | `(∀x. x ∈ Ω ⇒ \|f(x) - g(x)\| ≤ h(x)) ⇒ \|measure_integral(Ω, S, μ, f) - measure_integral(Ω, S, μ, g)\| ≤ measure_integral(Ω, S, μ, h)` for integrable f, g, h, under `measure_on(Ω, S, μ)` |
| `IntegralNonnegDifference` | f = u − v on Ω, u, v ≥ 0 measurable with finite integrals ⇒ the integral of f is the difference of theirs under `measure_on(Ω, S, μ)` |
| `IntegralAdd` | integrable f, g ⇒ `measure_integral(Ω, S, μ, λx. f(x) + g(x)) = measure_integral(Ω, S, μ, f) + measure_integral(Ω, S, μ, g)` under `measure_on(Ω, S, μ)` |
| `IntegralSub` | integrable f, g ⇒ `measure_integral(Ω, S, μ, λx. f(x) − g(x)) = measure_integral(Ω, S, μ, f) − measure_integral(Ω, S, μ, g)` under `measure_on(Ω, S, μ)` |
| `IntegralFiniteSum` | `(∀i. i < n ⇒ real_integrable(Ω, S, μ, z(i))) ⇒ real_integrable(Ω, S, μ, λx. Σ_{i<n} z(i, x)) ∧ measure_integral(Ω, S, μ, λx. Σ_{i<n} z(i, x)) = Σ_{i<n} measure_integral(Ω, S, μ, z(i))` under `measure_on(Ω, S, μ)` |
| `SquareIntegrableSum` | `(∀i. i < n ⇒ real_measurable(Ω, S, z(i)) ∧ real_integrable(Ω, S, μ, λx. z(i, x) * z(i, x))) ⇒ real_measurable(Ω, S, λx. Σ_{i<n} z(i, x)) ∧ real_integrable(Ω, S, μ, λx. (Σ_{i<n} z(i, x)) * Σ_{i<n} z(i, x))` under `measure_on(Ω, S, μ)` |
| `IntegralIndicator` | `E ∈ S ⇒ measure_integral(Ω, S, μ, λx. COND(x ∈ E, c, &0)) = c * extended_to_real(μ(E))` under `measure_on(Ω, S, μ)`, μ(E) possibly infinite, both sides then 0 |
| `IntegrableIndicator` | `E ∈ S ∧ μ(E) ≠ extended_infinity ⇒ real_integrable(Ω, S, μ, λx. COND(x ∈ E, c, &0))` under `measure_on(Ω, S, μ)` |
| `IntegralEqualMeasures` | `(∀E. E ∈ S ⇒ μ(E) = ν(E)) ⇒ (real_integrable(Ω, S, μ, f) ⇔ real_integrable(Ω, S, ν, f)) ∧ measure_integral(Ω, S, μ, f) = measure_integral(Ω, S, ν, f)` under `sigma_algebra_on(Ω, S)` |
| `IntegralAE` | `measure_ae_eq(Ω, S, μ, f, g) ⇒ measure_integral(Ω, S, μ, f) = measure_integral(Ω, S, μ, g)` under `measure_on(Ω, S, μ)`, no measurability |
| `AEBoundedIntegral` | `real_measurable(Ω, S, f) ∧ real_integrable(Ω, S, μ, g) ∧ measure_ae(Ω, S, μ, λx. \|f(x)\| ≤ g(x)) ⇒ real_integrable(Ω, S, μ, f) ∧ \|measure_integral(Ω, S, μ, f)\| ≤ measure_integral(Ω, S, μ, g)` under `measure_on(Ω, S, μ)` |
