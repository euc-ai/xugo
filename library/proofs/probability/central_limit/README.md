# central_limit — the central limit theorem for independent identically distributed variables and for arrays of martingale differences, from a Lindeberg bound

The chapter's limit theorems rest on Lindeberg's bound for one finite row of martingale differences, which `lindeberg_bound` proves through the row's Lindeberg sum `lindeberg_sum(Ω, S, μ, n, ξ, ε)`, and on its form for a row whose conditional variances sum only to about 1, which `variance_stopping` obtains by stopping the row where they pass 1 + δ. Independence is not read there. For independent centred variables, with the σ-algebras of the earlier ones as filtration, the conditional variances are the variances, by `IndependentFamilyCondExp` of independence.

The limit theorems all conclude weak convergence of the row sums' distributions to the standard normal distribution. `MartingaleCentralLimit` is the Brown–Billingsley form: rows of martingale differences, each with its own filtration, whose conditional variances sum to 1 in the limit, in measure, and whose Lindeberg sums tend to 0. `MartingaleCentralLimitConditional` asks the Lindeberg condition only conditionally and in measure, the Hall–Heyde and McLeish form. For rows of independent centred variables the natural filtrations make the conditional variances the variances, and `LindebergFeller` follows; `Lyapunov` replaces the Lindeberg condition by moments of order 2 + δ, and `CentralLimit`, for independent identically distributed variables of mean m and standard deviation σ > 0 normalized by σ·√n, is `LindebergFeller` at the rows (X(k) − m)/(σ·√n). Their distribution functions then converge at every point, the standard normal distribution having no atom (`CentralLimitDistributionFunction`).

## Members

| Entry | Statement |
| --- | --- |
| `CentralLimit` | independent identically distributed X(n), square-integrable with mean m and standard deviation σ > 0: the distributions of the normalized sums satisfy `weakly_converges(real_topology, …, normal_distribution(&0, &1))` |
| `CentralLimitDistributionFunction` | under the same hypotheses the probability that the normalized sum is at most t tends to `normal_distribution(&0, &1, {y \| y ≤ t})` |
| `MartingaleCentralLimit` | an array of martingale difference rows whose conditional variances sum to 1 in measure and whose Lindeberg sums tend to 0: the distributions of the row sums satisfy `weakly_converges(real_topology, …, normal_distribution(&0, &1))` |
| `MartingaleCentralLimitConditional` | `MartingaleCentralLimit` with the conditional Lindeberg terms w(ε, n, k), the conditional expectations of ξ(n, k)² cut to ε < \|ξ(n, k)\|, whose row sums tend to 0 in measure for every ε > 0, in place of the Lindeberg condition: the same conclusion — card |
| `LindebergFeller` | rows of independent centred square-integrable variables whose variances sum to 1 in the limit and whose Lindeberg sums tend to 0: the distributions of the row sums satisfy `weakly_converges(real_topology, …, normal_distribution(&0, &1))` |
| `Lyapunov` | the rows of `LindebergFeller`, with the row sums of `E[real_rpow(\|ξ(n, k)\|, &2 + δ)]` tending to 0 for some δ > 0 in place of the Lindeberg condition: the same conclusion |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
