# borel_function — Borel sets and Borel functions of the real line

The Borel sets of the real line form a σ-algebra on it and hold its rays and its closed intervals, and its Borel functions hold the identity and every function continuous on the line. A Borel function composed after a measurable real function is measurable, with no structure asked of the source; a real function generates the least σ-algebra it is measurable for, and a Borel function of it generates one inside it. These are facts of the line's topology, continuity among them, which the measurable functions of an arbitrary space in `measurable_function` do not read; the simple functions and the integrals stand on that chapter without them.

## Members

| Entry | Statement |
| --- | --- |
| `LineBorelSigmaAlgebra` | `sigma_algebra_on(𝕌, borel_sets(real_topology))` |
| `RaysBorel` | `{x \| x ≤ b} ∈ borel_sets(real_topology) ∧ {x \| b < x} ∈ borel_sets(real_topology)` |
| `ClosedIntervalBorel` | `⟦a, b⟧ ∈ borel_sets(real_topology)` |
| `ContinuousBorelMeasurable` | `real_continuous_on(𝕌, f) ⇒ real_measurable(𝕌, borel_sets(real_topology), f)` |
| `RealMeasurableCompose` | `real_measurable(Ω, S, u) ∧ real_measurable(𝕌, borel_sets(real_topology), f) ⇒ real_measurable(Ω, S, λx. f(u(x)))`, no structure hypothesis |
| `RealPullbackSigma` | X generates a σ-algebra on Ω, is measurable for it, and it lies in every family X is measurable for: `sigma_algebra_on(Ω, pullback_sigma(Ω, X, borel_sets(real_topology)))` and its leastness |
| `RealPullbackCompose` | `real_measurable(𝕌, borel_sets(real_topology), h) ⇒ pullback_sigma(Ω, λx. h(X(x)), borel_sets(real_topology)) ⊆ pullback_sigma(Ω, X, borel_sets(real_topology))` |
| `RealMeasurableIdentity` | `real_measurable(𝕌, borel_sets(real_topology), λx. x)` |
