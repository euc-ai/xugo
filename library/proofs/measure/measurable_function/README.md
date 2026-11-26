# measurable_function — measurable functions into the real line and into [0, ∞]

Real measurability is measurability into the Borel real line; [0, ∞]-valued measurability is measurability for `extended_borel`, the σ-algebra the rays above real levels generate. Strict upper-ray preimages characterize each: complements and countable unions give interval preimages, then every open and Borel preimage. Through the rays, measurable real functions are closed under sums, real multiples and products, maximum and minimum, absolute value, finite sums, pointwise suprema and infima, limits, integer parts and restriction to a measurable event. The embedding of a measurable real function in [0, ∞] is measurable, and so are the real values `extended_to_real` reads off a measurable [0, ∞]-valued function, the pointwise supremum and infimum of a measurable sequence, and the set where a measurable function is infinite.

## Members

| Entry | Statement |
| --- | --- |
| `RealMeasurableDef` | real_measurable |
| `RealMeasurableSourceMono` | `S ⊆ T ∧ real_measurable(Ω, S, f) ⇒ real_measurable(Ω, T, f)` |
| `ExtendedBorelDef` | extended_borel |
| `ExtendedMeasurableDef` | extended_measurable |
| `RealMeasurableIffRay` | Under `sigma_algebra_on(Ω, S)`, `real_measurable(Ω, S, f) ⇔ ∀c:real. {x:A \| x ∈ Ω ∧ c < f(x)} ∈ S` |
| `RealMeasurableIffNonnegRay` | f ≥ 0 on Ω ⇒ (`real_measurable(Ω, S, f) ⇔ ∀c:real. &0 ≤ c ⇒ {x:A \| x ∈ Ω ∧ c < f(x)} ∈ S`) under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableConst` | `real_measurable(Ω, S, λx. k)` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableAtMost` | `real_measurable(Ω, S, f) ⇒ {x \| x ∈ Ω ∧ f(x) ≤ c} ∈ S` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableBelow` | `real_measurable(Ω, S, f) ⇒ {x \| x ∈ Ω ∧ f(x) < c} ∈ S` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableAtLeast` | `real_measurable(Ω, S, f) ⇒ {x \| x ∈ Ω ∧ c ≤ f(x)} ∈ S` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableNeg` | `real_measurable(Ω, S, f) ⇒ real_measurable(Ω, S, λx. −f(x))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableScale` | `real_measurable(Ω, S, f) ⇒ real_measurable(Ω, S, λx. k * f(x))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableAdd` | `f, g measurable ⇒ real_measurable(Ω, S, λx. f(x) + g(x))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableSum` | `(∀j. j < n ⇒ real_measurable(Ω, S, f(j))) ⇒ real_measurable(Ω, S, λx. Σ_{j<n} f(j, x))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableMax` | `f, g measurable ⇒ real_measurable(Ω, S, λx. max(f(x), g(x)))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableMin` | `f, g measurable ⇒ real_measurable(Ω, S, λx. min(f(x), g(x)))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableAbs` | `real_measurable(Ω, S, f) ⇒ real_measurable(Ω, S, λx. \|f(x)\|)` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableSquare` | `real_measurable(Ω, S, f) ⇒ real_measurable(Ω, S, λx. f(x) * f(x))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableMul` | `f, g measurable ⇒ real_measurable(Ω, S, λx. f(x) * g(x))` under `sigma_algebra_on(Ω, S)`, by polarization |
| `RealMeasurableParts` | `real_measurable(Ω, S, f) ⇒` both `λx. max(f(x), &0)` and `λx. max(−f(x), &0)` measurable under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableSup` | a pointwise least upper bound on Ω of measurable f(n) is measurable under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableInf` | a pointwise greatest lower bound on Ω of measurable f(n) is measurable under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableLimit` | `(∀n. real_measurable(Ω, S, f(n))) ∧ (∀x. x ∈ Ω ⇒ f(n, x) ⟶ g(x)) ⇒ real_measurable(Ω, S, g)` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableIntegerPart` | `h` measurable and `&k(x) ≤ h(x) < &k(x) + &1` on Ω ⇒ `real_measurable(Ω, S, λx. &k(x))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableIndicator` | `E ∈ S ⇒ real_measurable(Ω, S, λx. COND(x ∈ E, c, &0))` under `sigma_algebra_on(Ω, S)` |
| `ExtendedMeasurableIffRay` | `extended_measurable(Ω, S, f) ⇔ ∀r:real. {x \| x ∈ Ω ∧ extended_of_real(r) < f(x)} ∈ S` under `sigma_algebra_on(Ω, S)` |
| `ExtendedMeasurableOfReal` | `real_measurable(Ω, S, f) ⇒ extended_measurable(Ω, S, λx. extended_of_real(f(x)))` under `sigma_algebra_on(Ω, S)` |
| `ExtendedMeasurableSup` | `(∀n. extended_measurable(Ω, S, f(n))) ⇒ extended_measurable(Ω, S, λx. extended_sup(image(λn. f(n, x), 𝕌)))` under `sigma_algebra_on(Ω, S)` |
| `ExtendedMeasurableAtLeast` | `extended_measurable(Ω, S, f) ⇒ {x \| x ∈ Ω ∧ extended_of_real(r) ≤ f(x)} ∈ S` under `sigma_algebra_on(Ω, S)` |
| `ExtendedMeasurableInf` | `(∀n. extended_measurable(Ω, S, f(n))) ⇒ extended_measurable(Ω, S, λx. extended_inf(image(λn. f(n, x), 𝕌)))` under `sigma_algebra_on(Ω, S)` |
| `ExtendedMeasurableOnEvent` | `E ∈ S ∧ extended_measurable(Ω, S, f) ⇒ extended_measurable(Ω, S, λx. COND(x ∈ E, f(x), &0))` under `sigma_algebra_on(Ω, S)` |
| `ExtendedMeasurableInfinitySet` | `extended_measurable(Ω, S, g) ⇒ {x \| x ∈ Ω ∧ g(x) = extended_infinity} ∈ S` under `sigma_algebra_on(Ω, S)` |
| `ExtendedMeasurableToReal` | `extended_measurable(Ω, S, g) ⇒ real_measurable(Ω, S, λx. extended_to_real(g(x)))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableOnEvent` | `E ∈ S ∧ real_measurable(Ω, S, f) ⇒ real_measurable(Ω, S, λx. COND(x ∈ E, f(x), &0))` under `sigma_algebra_on(Ω, S)` |
| `RealMeasurableCut` | `N ∈ S ∧ real_measurable(Ω, S, f) ⇒ real_measurable(Ω, S, λx. COND(x ∉ N, f(x), &0))` under `sigma_algebra_on(Ω, S)` |
