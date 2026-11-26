# measure_simple — nonnegative simple functions, their integral, and the approximation of a measurable function by them

A nonnegative simple function is a measurable real function that is nonnegative on Ω and takes finitely many values there; its integral against a measure is the sum, over those values, of each value times the measure of its level set. The measure is additive on finitely many disjoint measurable sets, so the simple integral can be computed on any finite measurable partition of Ω on whose pieces the function is constant. That makes it monotone, additive and homogeneous under a nonnegative factor, gives an indicator's integral, and computes it on an event. Simple functions are closed under sums and nonnegative multiples. Every measurable [0, ∞]-valued function is the increasing supremum of simple functions (SimpleApproximation, in the supremum form, so an infinite value is reached): the approximation at level n rounds min(f, n) down to the grid of step 2⁻ⁿ.

## Members

| Entry | Statement |
| --- | --- |
| `NonnegSimpleDef` | measure_simple |
| `SimpleIntegralDef` | measure_simple_integral |
| `SimpleLevelSets` | `measure_simple(Ω, S, s) ⇒ {x \| x ∈ Ω ∧ s(x) = y} ∈ S` under `sigma_algebra_on(Ω, S)` |
| `SimpleScale` | `measure_simple(Ω, S, s) ∧ &0 ≤ c ⇒ measure_simple(Ω, S, λx. c * s(x))` under `sigma_algebra_on(Ω, S)` |
| `SimpleAdd` | `measure_simple(Ω, S, s) ∧ measure_simple(Ω, S, t) ⇒ measure_simple(Ω, S, λx. s(x) + t(x))` under `sigma_algebra_on(Ω, S)` |
| `SimplePairsFinite` | `measure_simple(Ω, S, s) ∧ measure_simple(Ω, S, t) ⇒ finite(image(λx. (s(x), t(x)), Ω))` |
| `SimpleIntegralPartition` | a finite measurable partition of Ω on whose pieces s is constant gives `measure_simple_integral(Ω, μ, s)` as the sum over the pieces under `measure_on(Ω, S, μ)` |
| `SimpleIntegralIndicator` | `E ∈ S ∧ &0 ≤ c ⇒` the indicator is simple with simple integral `extended_of_real(c) * μ(E)` under `measure_on(Ω, S, μ)` |
| `SimpleIntegralScale` | `measure_simple_integral(Ω, μ, λx. c * s(x)) = extended_of_real(c) * measure_simple_integral(Ω, μ, s)` for simple s, `&0 ≤ c`, under `measure_on(Ω, S, μ)` |
| `SimpleIntegralRefine` | the simple integral of `h(s, t)` as a sum over the pairs of values of s and t under `measure_on(Ω, S, μ)` |
| `SimpleIntegralMono` | `s ≤ t` on Ω ⇒ `measure_simple_integral(Ω, μ, s) ≤ measure_simple_integral(Ω, μ, t)` for simple s, t, under `measure_on(Ω, S, μ)` |
| `SimpleIntegralAdd` | `measure_simple_integral(Ω, μ, λx. s(x) + t(x)) = measure_simple_integral(Ω, μ, s) + measure_simple_integral(Ω, μ, t)` for simple s, t, under `measure_on(Ω, S, μ)` |
| `SimpleIntegralRestrict` | `measure_simple(Ω, S, s) ∧ E ∈ S ⇒` the restriction of s to E is simple, with simple integral `Σ_{y∈image(s, Ω)} extended_of_real(y) * μ({x \| x ∈ Ω ∧ s(x) = y} ∩ E)` under `measure_on(Ω, S, μ)` |
| `IntegerPartSimple` | h measurable and bounded by `&M` on Ω, `k` its integer part there, `&0 < c` ⇒ `measure_simple(Ω, S, λx. &k(x) / c)` under `sigma_algebra_on(Ω, S)` |
| `SimpleApproximation` | `extended_measurable(Ω, S, f) ⇒` simple s(n), increasing on Ω, below f, with `f(x) = extended_sup(image(λn. extended_of_real(s(n, x)), 𝕌))` on Ω, under `sigma_algebra_on(Ω, S)` |
