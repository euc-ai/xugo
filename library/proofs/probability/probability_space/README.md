# probability_space — probability measures and expectation

A probability space is a measure space of total mass one. Expectation is its real integral and variance the expectation of the squared distance from the expectation; no countability condition is imposed on the sample space. Nonnegative weights of total one on a finite carrier give the first model: the discrete measure, under which expectation is the weighted sum. With equal weights it is the uniform law (`uniform_measure`), where the mass of a set is its share of the points.

## Members

| Entry | Statement |
| --- | --- |
| `ProbabilityOnDef` | probability_on |
| `ExpectationDef` | expectation |
| `ProbabilityBounds` | `probability_on(Ω, S, μ) ∧ E ∈ S ⇒ μ(E) ≤ &1 ∧ μ(Ω ∖ E) + μ(E) = &1` |
| `ProbabilityEventFinite` | `probability_on(Ω, S, μ) ∧ E ∈ S ⇒ μ(E) ≠ extended_infinity ∧ μ(E) = extended_of_real(extended_to_real(μ(E)))` |
| `ProbabilitySigmaFinite` | `probability_on(Ω, S, μ) ⇒ sigma_finite_on(Ω, S, μ)` |
| `ExpectationConstant` | `probability_on(Ω, S, μ) ⇒ real_integrable(Ω, S, μ, λx. c) ∧ expectation(Ω, S, μ, λx. c) = c` |
| `SquareIntegrableIntegrable` | `probability_on(Ω, S, μ) ∧ real_measurable(Ω, S, Y) ∧ real_integrable(Ω, S, μ, λx. Y(x) * Y(x)) ⇒ real_integrable(Ω, S, μ, Y)` |
| `BoundedIntegrable` | `probability_on(Ω, S, μ) ∧ real_measurable(Ω, S, f) ∧ (∀x. x ∈ Ω ⇒ \|f(x)\| ≤ B) ⇒ real_integrable(Ω, S, μ, f)` |
| `ExpectationIndicator` | `probability_on(Ω, S, μ) ∧ E ∈ S ⇒ real_integrable(Ω, S, μ, λx. COND(x ∈ E, c, &0)) ∧ expectation(Ω, S, μ, λx. COND(x ∈ E, c, &0)) = c * extended_to_real(μ(E))` |
| `ProbabilityIntegralSqrtUpperBound` | `probability_on(Ω, S, μ) ∧ real_integrable(Ω, S, μ, q) ∧ real_measurable(Ω, S, λx. real_sqrt(q(x))) ∧ measure_ae(Ω, S, μ, λx. &0 ≤ q(x)) ⇒ real_integrable(Ω, S, μ, λx. real_sqrt(q(x))) ∧ (measure_integral(Ω, S, μ, λx. real_sqrt(q(x))) ^ 2 ≤ measure_integral(Ω, S, μ, q) ∧ &0 ≤ measure_integral(Ω, S, μ, λx. real_sqrt(q(x))))` |
| `ExpectationDifferenceOnEvent` | `probability_on(Ω, S, μ) ∧ E ∈ S ∧ real_integrable(Ω, S, μ, f) ∧ real_integrable(Ω, S, μ, g) ∧ &0 ≤ C ∧ (∀x. x ∈ Ω ⇒ \|f(x) - g(x)\| ≤ B) ∧ (∀x. x ∈ Ω ∧ x ∉ E ⇒ \|f(x) - g(x)\| ≤ C) ⇒ \|expectation(Ω, S, μ, f) - expectation(Ω, S, μ, g)\| ≤ C + B * extended_to_real(μ(E))` |
| `FiniteWeightedProbability` | nonnegative weights of total one on a finite Ω make the discrete measure a probability, under which every X is integrable with `expectation = Σ_{x∈Ω} w(x) * X(x)` — card |
| `VarianceDef` | `variance(Ω, S, μ, X)`: the expectation of `(X(x) - expectation(Ω, S, μ, X)) * (X(x) - expectation(Ω, S, μ, X))` |
| `VarianceAffine` | `real_integrable(Ω, S, μ, λx. (a * Y(x) + b) * (a * Y(x) + b)) ∧ variance(Ω, S, μ, λx. a * Y(x) + b) = a * a * variance(Ω, S, μ, Y)` for a square-integrable Y on a probability space |
| `UniformMeasureDef` | `uniform_measure(Ω)`: the discrete measure on Ω of constant weight 1/card(Ω) |
| `UniformProbability` | on a finite nonempty Ω, `uniform_measure(Ω)` is a probability on all subsets, the mass of E being card(E)/card(Ω) — card |
| `CondProbDef` | `cond_prob(μ, E, D) = extended_to_real(μ(E ∩ D)) / extended_to_real(μ(D))`, 0 at a null D |
