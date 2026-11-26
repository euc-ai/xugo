# random_variable — distributions as pushforward probability measures

A random variable is a measurable map. Its distribution is the pushforward of the probability measure, and integration against that distribution is integration after composition. Two real variables on one space are identically distributed when their distributions agree on the Borel sets. A Borel probability on the line is determined by its distribution function, which is continuous from the right everywhere and from the left at every point of no mass.

## Members

| Entry | Statement |
| --- | --- |
| `IdenticallyDistributedDef` | identically_distributed: `pushforward_measure(Ω, μ, X, E) = pushforward_measure(Ω, μ, Y, E)` for every Borel E |
| `DistributionProbability` | probability_on(V, T, pushforward_measure(Ω, μ, X)) |
| `ExpectationPushforward` | (real_integrable(V, T, pushforward_measure(Ω, μ, X), h) ⇔ real_integrable(Ω, S, μ, h ∘ X)) ∧ expectation(V, T, pushforward_measure(Ω, μ, X), h) = expectation(Ω, S, μ, h ∘ X) |
| `IdenticallyDistributedExpectation` | identically distributed random variables give every Borel function of them the same integrability and the same expectation |
| `ProbabilityDeterminedByLowerRays` | `probability_on(𝕌, borel_sets(real_topology), μ) ∧ probability_on(𝕌, borel_sets(real_topology), ν) ∧ (∀b. μ({x \| x ≤ b}) = ν({x \| x ≤ b})) ∧ E ∈ borel_sets(real_topology) ⇒ μ(E) = ν(E)` |
| `DistributionFunctionRightContinuous` | the distribution function is continuous from the right (some b > t within e, so every point of (t, b], F being increasing): `probability_on(𝕌, borel_sets(real_topology), μ) ∧ &0 < e ⇒ ∃b. t < b ∧ extended_to_real(μ({y \| y ≤ b})) < extended_to_real(μ({y \| y ≤ t})) + e` |
| `DistributionFunctionLeftContinuousAtNull` | and from the left at a point of no mass (some a < t within e): `probability_on(𝕌, borel_sets(real_topology), μ) ∧ μ({t}) = extended_of_real(&0) ∧ &0 < e ⇒ ∃a. a < t ∧ extended_to_real(μ({y \| y ≤ t})) < extended_to_real(μ({y \| y ≤ a})) + e` |
