# normal_moments — the moments of the normal distribution: its mean and variance, the absolute moments of the standard normal, and tests of quadratic growth

Under `normal_distribution(m, v)` of probability/normal_distribution, for 0 < v, the identity variable has mean m and variance v, its square integrable. The standard normal's moments are computed on the windows ⟦−n, n⟧ of its density φ: −φ is a primitive of y·φ(y), so the first moment's windows vanish, and integration by parts makes the second moment's windows those of φ less 2n·φ(n), which tends to 0; the affine image of probability/normal_distribution carries them to mean m and variance v. The same primitive gives the absolute first moment of the standard normal, √(2/π), and (y² + 2)·φ(y), whose derivative is −y³·φ(y), its absolute third moment, 2√(2/π), at most 2 since π ≥ 2. A Borel test bounded in absolute value by a multiple of 1 + y² is integrable under every normal distribution of positive variance, by the finite second moment.

## Members

| Entry | Statement |
| --- | --- |
| `NormalDistributionMoments` | for `&0 < v`, under `normal_distribution(m, v)` the square of the identity is integrable, its expectation is m and its variance v |
| `StandardNormalAbsoluteMoment` | under `normal_distribution(&0, &1)` the absolute value of the identity is integrable and its expectation is `real_sqrt(&2 / π)` |
| `StandardNormalThirdAbsoluteMomentValue` | under `normal_distribution(&0, &1)` the cube of the absolute value is integrable and its expectation is `&2 * real_sqrt(&2 / π)` |
| `StandardNormalThirdAbsoluteMoment` | under `normal_distribution(&0, &1)` the cube of the absolute value is integrable and its expectation is at most `&2` |
| `NormalQuadraticGrowthIntegrable` | for `&0 < v` and a Borel h bounded in absolute value by `K * (&1 + y * y)`: h is integrable against `normal_distribution(m, v)` |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
