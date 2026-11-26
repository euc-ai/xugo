# conditional_expectation — conditional expectation as an event-integral relation

Conditional expectation is a relation between integrable real functions: the output is measurable for the smaller sigma algebra and has the same integral on every event in it. Uniqueness and its algebraic laws use only integration, so they apply before any existence construction. A known factor is pulled out in three steps: a dominated almost-everywhere limit of related pairs is related (CondExpDominatedLimit), a G-measurable factor with finitely many values is a finite sum of event cuts (CondExpFiniteRangeFactor), and an almost-everywhere bounded G-measurable factor is a dominated limit of simple ones (CondExpKnownFactor). A known factor times a conditionally centred variable integrates to zero: a bounded factor against any residual X − Y (CondExpBoundedProductResidual), and an unbounded one, by truncation and dominated convergence, wherever the product is integrable (CondExpZeroPredictableProduct).

## Members

| Entry | Statement |
| --- | --- |
| `IsCondExpDef` | is_cond_exp |
| `CondExpIdentity` | is_cond_exp(Ω, S, μ, G, X, X) |
| `CondExpLinear` | is_cond_exp(Ω, S, μ, G, λx:A. a * X(x) + b * U(x), λx:A. a * Y(x) + b * V(x)) |
| `CondExpMono` | conditional expectation preserves almost-everywhere order |
| `CondExpUnique` | measure_ae_eq(Ω, S, μ, Y, Z): monotonicity read both ways |
| `CondExpContraction` | measure_integral(Ω, S, μ, λx:A. \|Y(x)\|) ≤ measure_integral(Ω, S, μ, λx:A. \|X(x)\|) — card |
| `CondExpTower` | is_cond_exp(Ω, S, μ, H, X, Z) — card |
| `CondExpKnownFactor` | is_cond_exp(Ω, S, μ, G, λx:A. h(x) * X(x), λx:A. h(x) * Y(x)); any a.e. absolute bound C |
| `CondExpAE` | is_cond_exp(Ω, S, μ, G, U, V) — card |
| `CondExpIntegral` | measure_integral(Ω, S, μ, X) = measure_integral(Ω, S, μ, Y) |
| `CondExpDominatedLimit` | `is_cond_exp(Ω, S, μ, G, U, V)` when related sequences converge almost everywhere to measurable U, V and each has an integrable dominating function |
| `CondExpFiniteRangeFactor` | `is_cond_exp(Ω, S, μ, G, hX, hY)` when `is_cond_exp(Ω, S, μ, G, X, Y)` and h is G-measurable with finite image on Ω; signed factors are allowed |
| `CondExpBoundedProductResidual` | `is_cond_exp(Ω, S, μ, G, X, Y) ∧ real_measurable(Ω, G, B) ∧ measure_ae(Ω, S, μ, λx. \|B(x)\| ≤ C) ⇒ real_integrable(Ω, S, μ, λx. B(x) * (X(x) - Y(x))) ∧ measure_integral(Ω, S, μ, λx. B(x) * (X(x) - Y(x))) = &0` |
| `CondExpZeroPredictableProduct` | `is_cond_exp(Ω, S, μ, G, X, λx. &0) ∧ real_measurable(Ω, G, h) ∧ real_integrable(Ω, S, μ, λx. h(x) * X(x)) ⇒ measure_integral(Ω, S, μ, λx. h(x) * X(x)) = &0`, h not asked to be bounded |
