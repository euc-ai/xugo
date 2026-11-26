# lindeberg_bound — Lindeberg's bound for one row of martingale differences: a smooth test at the row's sum against its standard normal integral, through the row's Lindeberg sum

The chapter's subject is one finite row. A row of martingale differences ξ(k), k < n, for a filtration F has ξ(k) measurable for F(k + 1), with conditional mean 0 and conditional variance v(k) given F(k). Its sum is compared with a normal variable through a test function with bounded second and third derivatives. Lindeberg's replacement, one step of the row at a time, with Taylor's formula and the two conditional moments, bounds the distance between the expectation of the test function at the row's sum and its integral against `normal_distribution(0, 1)` by `lindeberg_sum(Ω, S, μ, n, ξ, ε)`, the part of the row's second moments carried by values beyond ε. The bound is stated twice: with a clock c that the conditional variances may fall short of, what is left being spent on a normal variable (`MartingaleLindebergSmoothing`), and for conditional variances summing to exactly 1 (`MartingaleLindebergBound`). Independence is not read.

## Members

| Entry | Statement |
| --- | --- |
| `LindebergSumDef` | `lindeberg_sum(Ω, S, μ, n, ξ, ε)`: the sum over k < n of `event_integral(Ω, S, μ, {x \| ε < \|ξ(k, x)\|}, λx. ξ(k, x) * ξ(k, x))` |
| `LindebergSumNonnegative` | `&0 ≤ lindeberg_sum(Ω, S, μ, n, ξ, ε)` |
| `MartingaleLindebergSmoothing` | a row of martingale differences with conditional variances summing to at most c: the expectation of D(0) at the row's sum, smoothed by a normal variable of the variance left of c, is within `M₃ * ε / &6 * c + M₂ * L + M₃ / &3 * c * real_sqrt(ε ^ 2 + L)` of the integral of `λy. D(0)(real_sqrt(c) * y)` against `normal_distribution(&0, &1)`, L the Lindeberg sum at ε |
| `MartingaleLindebergBound` | conditional variances summing to 1: D(0) at the row's sum is integrable and its expectation is within `M₃ * ε / &6 + M₂ * L + M₃ / &3 * real_sqrt(ε ^ 2 + L)` of the integral of D(0) against `normal_distribution(&0, &1)` |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
