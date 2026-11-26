# weak_convergence — weak convergence of probability measures on the Borel sets of a topology: a test for it on the line, and the convergence of distribution functions it gives

`weakly_converges(T, ν, ρ)` says that the ν(n) and ρ are probability measures on the Borel sets of T and that the expectation of every bounded continuous real function under ν(n) tends to its expectation under ρ. Convergence in distribution of random variables is this relation between their distributions, the pushforwards of random_variable. On the line a test connects it to what a limit theorem proves, and a consequence to what it is used for. It is enough to test functions that are three times differentiable and bounded with their three derivatives: the constant among them makes the limit a probability, which lets no mass escape; a bounded continuous test clipped to a window is, read through the clamp, uniformly continuous, hence uniformly within ε of a function with three bounded derivatives (real_integral.UniformSmoothApproximation); and a tent cutoff holds the outside of the window. And weak convergence gives convergence of the distribution functions at every point the limit gives no mass: a ramp falling from the indicator of one half-line to that of a slightly longer one is a bounded continuous test squeezed between them, and the limit's distribution function is continuous at a point of no mass (random_variable's DistributionFunctionRightContinuous and DistributionFunctionLeftContinuousAtNull).

## Members

| Entry | Statement |
| --- | --- |
| `WeaklyConvergesDef` | `weakly_converges(T, ν, ρ)`: the ν(n) and ρ are probabilities on `borel_sets(T)`, and `measure_integral(⋃T, borel_sets(T), ν(n), f) ⟶ measure_integral(⋃T, borel_sets(T), ρ, f)` for every bounded f with `continuous_map(T, real_topology, f)` |
| `WeakConvergenceSmoothTests` | probabilities ν(n) and a measure ρ on the Borel sets of the line whose expectations converge at every D(0), D a tower of three derivatives bounded together, satisfy `weakly_converges(real_topology, ν, ρ)` |
| `WeakConvergenceDistributionFunction` | `weakly_converges(real_topology, ν, ρ)` and `ρ({t}) = &0` `⇒` the masses `ν(n, {y \| y ≤ t})` tend to `ρ({y \| y ≤ t})` |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
