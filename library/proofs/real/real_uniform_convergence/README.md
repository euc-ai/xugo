# real_uniform_convergence — uniform convergence of sequences and series of real functions

A sequence of functions converges uniformly on a set when one index serves every point of the set. Uniform limits keep continuity, commute with the integral, and commute with the derivative when the derivatives converge uniformly. The Weierstrass M-test is the usual source of uniformly convergent series.

## The movements

**Uniform Cauchy.** The Cauchy criterion names its limit: at each point
the values f(n)(x) form a Cauchy sequence, and their upper limit is the
uniform limit. The Weierstrass M-test (`WeierstrassMajorant`, the majorant test) is that
criterion read at partial sums: two partial sums differ by a tail, and
at every point a tail of u is at most the same tail of M.

**Continuity.** A uniform limit of continuous functions is continuous,
by the ε/3 argument: one f(n) uniformly close to g, then that f(n)'s
radius at c.

**Derivatives.** The mean value inequality
(`real_derivative.MeanValueInequality`) applied to f(m) − f(n) bounds
their increments uniformly by the distance between the derivatives,
an estimate `UniformLimitDerivative` proves as its first section. Read
against the point c it makes the f(n) uniformly
Cauchy; read near x it carries the increment estimate over to the
limit g, and the derivative read as an increment bound
(`real_derivative.DerivativeIncrement`) gives g′(x) = h(x).

**Integrals.** Two functions within η of each other on ⟦a, b⟧ have
Riemann sums within η·(b − a) of each other (`real_integral.RiemannSumsClose`): every
tag lies in ⟦a, b⟧, and the lengths of the pieces telescope to b − a.
Under uniform convergence the integrals I(n) form a Cauchy sequence,
the difference f(m) − f(n) being uniformly small and its integral being
I(m) − I(n); their limit J is the integral of g by the ε/3 argument run
on Riemann sums. Term-by-term integration (`UniformSumsIntegral`) is
this read at partial sums, whose integrals add term by term
(`real_integral.HasIntegralSum`).

`⟬a, b⟭` and `⟦a, b⟧` are the open and the closed interval of
`real_topology`, `real_open_interval(a, b)` and
`real_closed_interval(a, b)`.

## Members

| entry | statement |
|---|---|
| `RealConvergesUniformlyOnDef` | `real_converges_uniformly_on(s, f, g) ⇔ ∀ε. &0 < ε ⇒ ∃N. ∀n x. N ≤ n ∧ x ∈ s ⇒ real_abs(f(n)(x) − g(x)) < ε` |
| `UniformImpPointwise` | `real_converges_uniformly_on(s, f, g) ∧ x ∈ s ⇒ (λn. f(n)(x)) ⟶ g(x)` |
| `UniformCauchy` | `(∃g. real_converges_uniformly_on(s, f, g)) ⇔ ∀ε. &0 < ε ⇒ ∃N. ∀m n x. N ≤ m ∧ N ≤ n ∧ x ∈ s ⇒ real_abs(f(m)(x) − f(n)(x)) < ε` |
| `WeierstrassMajorant` | `(∀n x. x ∈ s ⇒ real_abs(u(n)(x)) ≤ M(n)) ∧ real_sums(M, t) ⇒ ∃g. (∀x. x ∈ s ⇒ real_sums(λn. u(n)(x), g(x))) ∧ real_converges_uniformly_on(s, λn x. Σ_{k∈0 .. n} u(k)(x), g)` |
| `UniformLimitCongruence` | `real_converges_uniformly_on(s, f, g) ∧ (∀x. x ∈ s ⇒ g(x) = h(x)) ⇒ real_converges_uniformly_on(s, f, h)` |
| `UniformLimitContinuous` | `(∀n. real_continuous_on(s, f(n))) ∧ real_converges_uniformly_on(s, f, g) ⇒ real_continuous_on(s, g)` |
| `UniformLimitDerivative` | `(∀n x. a < x ∧ x < b ⇒ real_derivative_at(f(n), x, f'(n)(x))) ∧ real_converges_uniformly_on(⟬a, b⟭, f', h) ∧ a < c ∧ c < b ∧ (λn. f(n)(c)) ⟶ l ⇒ ∃g. real_converges_uniformly_on(⟬a, b⟭, f, g) ∧ g(c) = l ∧ ∀x. a < x ∧ x < b ⇒ real_derivative_at(g, x, h(x))` |
| `UniformLimitIntegral` | `(∀n. real_has_integral(f(n), a, b, I(n))) ∧ real_converges_uniformly_on(⟦a, b⟧, f, g) ⇒ ∃J. real_has_integral(g, a, b, J) ∧ I ⟶ J` |
| `UniformSumsIntegral` | `(∀k. real_has_integral(u(k), a, b, c(k))) ∧ real_converges_uniformly_on(⟦a, b⟧, λn x. Σ_{k∈0 .. n} u(k)(x), g) ⇒ ∃J. real_has_integral(g, a, b, J) ∧ real_sums(c, J)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
