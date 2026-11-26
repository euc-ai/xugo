# martingale — real martingales and stopped processes

A martingale is an adapted integrable process satisfying the conditional-expectation relation at consecutive times. Supermartingales are stated by an event-integral inequality. Bounded predictable transforms and stopping use these relations alone. A martingale difference row is a finite row of increments, each centred given the past, with their conditional variances; stopped predictably where its running conditional variance passes a level, it stays one.

## Members

| Entry | Statement |
| --- | --- |
| `MartingaleDef` | martingale_on |
| `SupermartingaleDef` | supermartingale_on |
| `MartingaleTransformDef` | martingale_transform |
| `MartingaleDifferenceRowDef` | `martingale_difference_row(Ω, S, μ, F, n, ξ, v)`: F is a filtration and, for k < n, ξ(k) is F(k + 1)-measurable with `is_cond_exp(Ω, S, μ, F(k), ξ(k), λx. &0)` and `is_cond_exp(Ω, S, μ, F(k), λx. ξ(k, x) * ξ(k, x), v(k))` |
| `MartingaleConditional` | is_cond_exp(Ω, S, μ, F(m), M(n), M(m)) — card |
| `MartingaleAdaptedIntegrable` | measure_on(Ω, S, μ) ∧ filtration_on(Ω, S, F) ∧ adapted_process(Ω, F, M) ∧ (∀n:num. real_integrable(Ω, S, μ, M(n))) |
| `MartingaleTransform` | martingale_on(Ω, S, μ, F, martingale_transform(M, H)) |
| `StoppedMartingale` | martingale_on(Ω, S, μ, F, stopped_process(M, T)) — card |
| `StoppedSupermartingale` | supermartingale_on(Ω, S, μ, F, stopped_process(M, T)) — card |
| `StoppedMartingaleDifferences` | `martingale_difference_row(Ω, S, μ, F, n, ξ, v) ⇒` the row with ξ(k) and v(k) cut to 0 where v(0) + … + v(k) exceeds c is a martingale difference row for F |
