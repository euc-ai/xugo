# variance_stopping — Lindeberg's bound for a row of martingale differences whose conditional variances sum only to about 1, by stopping the row where they pass 1 + δ

The bound of `lindeberg_bound` asks the conditional variances of a row to sum to at most a clock. A row of an array whose conditional variances sum to 1 only in the limit, in measure, meets that clock only off an event of small probability. The chapter stops the row where its conditional variances first pass 1 + δ: the stopped terms are again martingale differences, their conditional variances sum to at most 1 + δ almost everywhere, and one event of the mass of {|Σv − 1| > δ} carries every failure — off it the stopped and the original sums agree and the variance the stopped row leaves of the clock is at most 2δ. The stopped row, smoothed by a normal variable of that remaining variance, is within the Lindeberg bound at the clock 1 + δ of the normal integral at scale √(1 + δ). Removing the smoothing variable and rescaling √(1 + δ) to 1 cost multiples of the first absolute moment of the standard normal, and the exceptional event costs four times the test's bound times its probability. `MartingaleLindebergApproximateBound` adds the four errors; the central limit theorem for martingale arrays reads it row by row.

## Members

| Entry | Statement |
| --- | --- |
| `MartingaleLindebergApproximateBound` | a row of martingale differences and a test D(0) whose derivatives up to the third are bounded by B: for δ, ε > 0 the expectation of D(0) at the row's sum is within `B * (real_sqrt(&2 * δ) + δ) * m + &4 * B * extended_to_real(μ(E))` plus the Lindeberg bound at the clock 1 + δ of the integral of D(0) against `normal_distribution(&0, &1)`, m the first absolute moment of `normal_distribution(&0, &1)` and E the event `{x \| x ∈ Ω ∧ δ < \|Σ_{k<n} v(k, x) - &1\|}` |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
