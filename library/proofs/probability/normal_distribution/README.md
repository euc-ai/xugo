# normal_distribution — the normal density and the distribution it gives the line: total mass, affine images and the standard distribution function

`normal_density(m, v, x)` is $e^{-(x-m)^2/(2v)}/\sqrt{2\pi v}$, the density of mean m and variance v, and `normal_distribution(m, v)` is the measure it gives the line against the Lebesgue measure, a density measure of measure/density_measure. The second parameter is the variance, not the standard deviation. For 0 < v the distribution is a probability on the Borel sets, by the Gaussian integral of real/lebesgue_riemann, and it is the image of the standard distribution `normal_distribution(0, 1)` under y ↦ m + √v·y, stated as a change of variable in the expectation. The standard distribution gives no point mass, so measures converging weakly to it have distribution functions converging to its own at every point. For v ≤ 0 the formula gives the zero measure, not a point mass, and every member asks 0 < v. The moments of the distribution are probability/normal_moments, and the sums of independent normal variables probability/normal_convolution.

## Members

| Entry | Statement |
| --- | --- |
| `NormalDensityDef` | `normal_density(m, v, x) = exp(-((x - m) ^ 2 / (&2 * v))) / real_sqrt(&2 * π * v)` |
| `NormalDistributionDef` | `normal_distribution(m, v, E)`: the density measure of `normal_density(m, v)` against the Lebesgue measure, at E |
| `NormalDistributionProbability` | `&0 < v ⇒ probability_on(𝕌, borel_sets(real_topology), normal_distribution(m, v))` |
| `NormalDistributionAffine` | for `&0 < v` and a Borel h: h is integrable against `normal_distribution(m, v)` exactly when `λy. h(m + real_sqrt(v) * y)` is against `normal_distribution(&0, &1)`, and the two expectations agree |
| `StandardNormalDistributionFunctionLimit` | measures ν(n) converging weakly to `normal_distribution(&0, &1)`: their masses of `{y \| y ≤ t}` tend to its mass of that set, at every t |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
