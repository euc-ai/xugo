# measure_space — measures and almost everywhere statements

Measures assign extended nonnegative mass to measurable subsets of an explicit carrier. Null sets are subsets of measurable zero sets, so almost everywhere statements make sense without completing the sigma algebra. Finite additivity follows from countable additivity by padding a disjoint pair with empty sets. Two measures that agree on a generating π-system agree on every measurable set, given equal finite total mass or an increasing exhaustion of the carrier by sets of the π-system of finite mass.

## Members

| Entry | Statement |
| --- | --- |
| `MeasureOn` | measure_on |
| `FiniteMeasureDef` | finite_measure_on |
| `NullSetDef` | measure_null |
| `AlmostEverywhereDef` | measure_ae |
| `AEEqualDef` | measure_ae_eq |
| `RestrictMeasureDef` | restricted_measure |
| `PushforwardMeasureDef` | pushforward_measure |
| `DiscreteMeasureDef` | discrete_measure |
| `SigmaFiniteDef` | `sigma_finite_on(Ω, S, μ)`: a measure with Ω a countable union of measurable sets of finite measure |
| `DiracMeasureDef` | `dirac_measure(a, E) = COND(a ∈ E, &1, &0)` |
| `RestrictMeasure` | measure_on(E, image(λU:set(A). U ∩ E, S), restricted_measure(μ, E)) |
| `RestrictMeasureOnCarrier` | `measure_on(Ω, S, μ) ∧ E ∈ S ⇒ measure_on(Ω, S, restricted_measure(μ, E))` |
| `SubSigmaMeasure` | measure_on(Ω, G, μ) |
| `NullCountableUnion` | measure_null(Ω, S, μ, ⋃image(E, 𝕌)) |
| `AECountable` | measure_ae(Ω, S, μ, λx:A. ∀n:num. P(n, x)) |
| `AEConjunction` | `measure_ae(Ω, S, μ, P) ∧ measure_ae(Ω, S, μ, Q) ⇒ measure_ae(Ω, S, μ, λx. P(x) ∧ Q(x))` under `measure_on(Ω, S, μ)` |
| `AEOfEverywhere` | `(∀x. x ∈ Ω ⇒ P(x)) ⇒ measure_ae(Ω, S, μ, P)` under `measure_on(Ω, S, μ)` |
| `AEMono` | `measure_ae(Ω, S, μ, P) ∧ (∀x. x ∈ Ω ∧ P(x) ⇒ Q(x)) ⇒ measure_ae(Ω, S, μ, Q)`, no structure hypothesis |
| `AEOffNullSet` | `N ∈ S ∧ μ(N) = &0 ⇒ measure_ae(Ω, S, μ, λx. x ∉ N)`, no structure hypothesis |
| `AEEqualEquivalence` | (∀f:(A → B). measure_ae_eq(Ω, S, μ, f, f)) ∧ (∀f g:(A → B). measure_ae_eq(Ω, S, μ, f, g) ⇒ measure_ae_eq(Ω, S, μ, g, f)) ∧ (∀f g h:(A → B). measure_ae_eq(Ω, S, μ, f, g) ∧ measure_ae_eq(Ω, S, μ, g, h) ⇒ measure_ae_eq(Ω, S, μ, f, h)) |
| `AEOperation` | measure_ae_eq(Ω, S, μ, λx:A. op(f(x), h(x)), λx:A. op(g(x), k(x))) |
| `PushforwardMeasure` | measure_on(V, T, pushforward_measure(Ω, μ, f)) |
| `DiscreteMeasure` | measure_on(Ω, {E:set(A) \| E ⊆ Ω}, discrete_measure(Ω, w)) |
| `DiracMeasure` | for a ∈ Ω, `dirac_measure(a)` is a measure on any σ-algebra on Ω, of total mass one — card |
| `FiniteMeasureSigmaFinite` | `finite_measure_on(Ω, S, μ) ⇒ sigma_finite_on(Ω, S, μ)` |
| `SigmaFiniteIncreasingCover` | `sigma_finite_on(Ω, S, μ) ⇒ ∃a. (∀n. a(n) ∈ S ∧ μ(a(n)) ≠ extended_infinity) ∧ (∀n. a(n) ⊆ a(n + 1)) ∧ ⋃image(a, 𝕌) = Ω` |
| `MeasureAdditive` | `E ∈ S ∧ D ∈ S ∧ E ∩ D = ∅ ⇒ μ(E ∪ D) = μ(E) + μ(D)` under `measure_on(Ω, S, μ)` |
| `MeasureAddDiff` | `s ∈ S ∧ t ∈ S ∧ s ⊆ t ⇒ μ(t) = μ(s) + μ(t ∖ s)` under `measure_on(Ω, S, μ)` |
| `MeasureMono` | `s ∈ S ∧ t ∈ S ∧ s ⊆ t ⇒ μ(s) ≤ μ(t)` under `measure_on(Ω, S, μ)` |
| `MeasureContinuousIncreasing` | `(∀n. a(n) ∈ S) ∧ (∀n. a(n) ⊆ a(n + 1)) ⇒ μ(⋃image(a, 𝕌)) = extended_sup(image(λn. μ(a(n)), 𝕌))` under `measure_on(Ω, S, μ)` |
| `MeasureFromContinuousIncreasing` | `sigma_algebra_on(Ω, S) ∧ μ(∅) = &0 ∧ (∀E F. E ∈ S ∧ F ∈ S ∧ E ∩ F = ∅ ⇒ μ(E ∪ F) = μ(E) + μ(F)) ∧ (∀a. (∀n. a(n) ∈ S) ∧ (∀n. a(n) ⊆ a(n + 1)) ⇒ μ(⋃image(a, 𝕌)) = extended_sup(image(λn. μ(a(n)), 𝕌))) ⇒ measure_on(Ω, S, μ)` |
| `MeasureContinuousDecreasing` | `(∀n. b(n) ∈ S) ∧ (∀n. b(n + 1) ⊆ b(n)) ∧ μ(b(0)) ≠ extended_infinity ⇒ μ(⋂image(b, 𝕌)) = extended_inf(image(λn. μ(b(n)), 𝕌))` under `measure_on(Ω, S, μ)` |
| `MeasureCountableSubadditive` | `(∀n. a(n) ∈ S) ⇒ μ(⋃image(a, 𝕌)) ≤ extended_series(λn. μ(a(n)))` under `measure_on(Ω, S, μ)` |
| `MeasureFiniteAdditive` | `finite(k) ∧ (∀i. i ∈ k ⇒ E(i) ∈ S) ∧ (pairwise disjoint on k) ⇒ μ(⋃image(E, k)) = Σ_{i∈k} μ(E(i))` under `measure_on(Ω, S, μ)` |
| `MeasureDeterminedByPi` | `measure_on(Ω, S, μ) ∧ measure_on(Ω, S, ν) ∧ μ(Ω) = ν(Ω) ∧ μ(Ω) ≠ extended_infinity ∧ pi_system_on(Ω, C) ∧ S = generated_sigma(Ω, C) ∧ (∀R. R ∈ C ⇒ μ(R) = ν(R)) ∧ E ∈ S ⇒ μ(E) = ν(E)`; equal total mass is asked because C need not hold Ω |
| `MeasureDeterminedByPiExhaustion` | `measure_on(Ω, S, μ) ∧ measure_on(Ω, S, ν) ∧ pi_system_on(Ω, C) ∧ S = generated_sigma(Ω, C) ∧ (∀R. R ∈ C ⇒ μ(R) = ν(R)) ∧ (∀n. K(n) ∈ C ∧ μ(K(n)) ≠ extended_infinity) ∧ (∀n. K(n) ⊆ K(n + 1)) ∧ ⋃image(K, 𝕌) = Ω ∧ E ∈ S ⇒ μ(E) = ν(E)` |
