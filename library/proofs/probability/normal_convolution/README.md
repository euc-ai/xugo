# normal_convolution — sums of independent normal variables: the convolution of two normal distributions and the smoothing it gives a test

The sum of two independent normal variables is normal, the means and the variances adding. It is stated on the product of the two distributions of probability/normal_distribution, as the mass of the pairs whose sum lies in a Borel set, and proved by the density: the product of the two normal densities factors into the density at the sum and a normal density in the first coordinate, by completing the square, and after Tonelli exchanges the integrals that second density has mass one. Read against a test, the convolution says that the expectation of h under `normal_distribution(a + b, s + t)` is the iterated expectation of h at the sum under `normal_distribution(a, s)` and `normal_distribution(b, t)`. Through the affine image of probability/normal_distribution this becomes the semigroup of the smoothings by the standard normal: averaging h first at scale √u and then at scale √v is averaging it once at scale √(u + v), a zero variance included.

## Members

| Entry | Statement |
| --- | --- |
| `NormalDensityConvolutionProduct` | for `&0 < s` and `&0 < t`: `normal_density(a, s, x) * normal_density(b + x, t, z)` is `normal_density(a + b, s + t, z)` times the normal density of mean `a + s / (s + t) * (z - a - b)` and variance `s * t / (s + t)` at x |
| `NormalDistributionConvolution` | for `&0 < s`, `&0 < t` and a Borel E: `product_measure(𝕌, borel_sets(real_topology), normal_distribution(a, s), normal_distribution(b, t), {p \| fst(p) + snd(p) ∈ E}) = normal_distribution(a + b, s + t, E)` |
| `NormalDistributionConvolutionExpectation` | for `&0 < s`, `&0 < t` and a Borel h integrable against `normal_distribution(a + b, s + t)`: its expectation there is the expectation under `normal_distribution(a, s)` of `λx. expectation(…, normal_distribution(b, t), λy. h(x + y))` |
| `StandardNormalSmoothingSemigroup` | for `&0 ≤ u`, `&0 ≤ v` and a Borel h, integrable where both variances are positive: the iterated expectation of `h(a + real_sqrt(u) * x + real_sqrt(v) * y)` under `normal_distribution(&0, &1)` twice is the expectation of `h(a + real_sqrt(u + v) * y)` under it |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
