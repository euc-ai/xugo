# nonneg_integral — the integral of a [0, ∞]-valued function on a measure space

The nonnegative integral accepts extended nonnegative functions and is the supremum of the simple integrals of the simple functions lying below the function on Ω. It is monotone, sees a function on Ω only, vanishes on the zero function, is a simple function's own simple integral, and takes a nonnegative factor out. The monotone convergence theorem is proved here, pointwise on an arbitrary measure space, because the integral's own algebra rests on it: the nonnegative integral is additive (NonnegIntegralAdd), integrates an indicator to its value times the measure of its event, and is carried along a measurable map to the measure the map pushes forward (NonnegIntegralPushforward). It sees a function up to null sets (NonnegIntegralAE), vanishes exactly on the functions that vanish almost everywhere, has a finite value only at a function finite almost everywhere, bounds the measure of an upper level set (Markov, Chebyshev), and is the same for a sub-σ-algebra the function is measurable for.

## Members

| Entry | Statement |
| --- | --- |
| `NonnegIntegralDef` | nonneg_integral |
| `NonnegIntegralAE` | nonneg_integral(Ω, S, μ, f) = nonneg_integral(Ω, S, μ, g) |
| `Markov` | extended_of_real(t) * μ({x:A \| x ∈ Ω ∧ extended_of_real(t) ≤ f(x)}) ≤ nonneg_integral(Ω, S, μ, f) |
| `IntegralZeroIffAE` | nonneg_integral(Ω, S, μ, f) = &0 ⇔ measure_ae(Ω, S, μ, λx:A. f(x) = &0) |
| `FiniteIntegralAEFinite` | measure_ae(Ω, S, μ, λx:A. f(x) ≠ extended_infinity) |
| `SubSigmaIntegral` | nonneg_integral(Ω, G, μ, f) = nonneg_integral(Ω, S, μ, f) |
| `Chebyshev` | extended_of_real(t * t) * μ({x:A \| x ∈ Ω ∧ t ≤ \|f(x)\|}) ≤ nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x) * f(x))) |
| `NonnegIntegralMono` | `(∀x. x ∈ Ω ⇒ f(x) ≤ g(x)) ⇒ nonneg_integral(Ω, S, μ, f) ≤ nonneg_integral(Ω, S, μ, g)`, no structure hypothesis |
| `NonnegIntegralZero` | `nonneg_integral(Ω, S, μ, λx. &0) = &0`, no structure hypothesis |
| `NonnegIntegralSimple` | `measure_simple(Ω, S, s) ⇒ nonneg_integral(Ω, S, μ, λx. extended_of_real(s(x))) = measure_simple_integral(Ω, μ, s)` under `measure_on(Ω, S, μ)` |
| `NonnegIntegralScale` | `&0 ≤ c ⇒ nonneg_integral(Ω, S, μ, λx. extended_of_real(c) * f(x)) = extended_of_real(c) * nonneg_integral(Ω, S, μ, f)` under `measure_on(Ω, S, μ)` |
| `NonnegIntegralIndicator` | `E ∈ S ⇒ nonneg_integral(Ω, S, μ, λx. COND(x ∈ E, z, &0)) = z * μ(E)` for every z in ⟦0, ∞⟧, under `measure_on(Ω, S, μ)` |
| `MonotoneConvergence` | nonneg_integral(Ω, S, μ, λx:A. extended_sup(image(λn:num. f(n, x), 𝕌))) = extended_sup(image(λn:num. nonneg_integral(Ω, S, μ, f(n)), 𝕌)) |
| `MonotoneConvergenceSimple` | nonneg_integral(Ω, S, μ, g) = extended_sup(image(λn:num. measure_simple_integral(Ω, μ, s(n)), 𝕌)) |
| `NonnegIntegralAdd` | nonneg_integral(Ω, S, μ, λx:A. f(x) + g(x)) = nonneg_integral(Ω, S, μ, f) + nonneg_integral(Ω, S, μ, g) |
| `NonnegIntegralPushforward` | `measurable_map(Ω, S, V, T, F) ∧ (∀E. E ∈ T ⇒ ν(E) = μ(preimage_on(Ω, F, E))) ∧ extended_measurable(V, T, k) ⇒ nonneg_integral(V, T, ν, k) = nonneg_integral(Ω, S, μ, λx. k(F(x)))` under `measure_on(Ω, S, μ)` and `measure_on(V, T, ν)` |
| `NonnegIntegralEqOn` | functions equal on Ω have equal nonnegative integrals, no structure hypothesis |
