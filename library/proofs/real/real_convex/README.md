# real_convex — convex real functions and the classical inequalities

A function is convex on a set when its graph lies below every chord. The chapter gives the chord-slope characterization and the derivative test, and proves Jensen's inequality for finite convex combinations. The classical inequalities follow from it: arithmetic–geometric means, Young, Hölder and Minkowski.

## The movements

**Chords.** Convexity is read through chords: on any set, f is convex
exactly when, for x < y < z with x and z in the set, the slope of the
left chord is at most the slope of the right one
(`ConvexIffChordSlopes`); the three-chord lemma places the long chord's
slope between them.

**Derivatives.** On an interval, the mean value theorem turns an
increasing derivative, or a nonnegative second derivative, into
convexity. The exponential and −log are the examples.

**Jensen.** Jensen's inequality is an induction on the finite index
set, adjoining one point at a time and renormalizing the remaining
weights by 1 − w(j) (`ConvexCombinationInsert`: a combination over j
adjoined to u is the value at j beside the renormalized combination over
u); an interval holds every convex combination of its points by
the same induction (`ConvexCombinationIn`).

**Means.** The arithmetic–geometric mean inequality in power form is
Jensen for −log at the weights 1/n, a zero term making the product 0;
weighted AM–GM is Jensen for −log at arbitrary weights, the logarithm
turning the product of powers $x(i)^{w(i)}$ into $\sum w(i) \cdot \log x(i)$.

**Young, Hölder, Minkowski.** Young's inequality is the convexity of
exp at the conjugate weights 1/p and 1/q, between p·log a and q·log b.
Hölder's inequality applies Young term by term at |a(i)|/μ and
|b(i)|/ν, μ and ν being the p- and q-norms, and the terms sum to
1/p + 1/q = 1; a vanishing norm forces its sequence to vanish
(`PowerSumZero`). Minkowski's inequality writes $\lvert a+b \rvert^p$ as
$\lvert a+b \rvert \cdot \lvert a+b \rvert^{p-1}$ and applies Hölder at $q = \frac{p}{p-1}$ to each half.

## Members

| entry | statement |
|---|---|
| `RealConvexOnDef` | `real_convex_on(s, f) ⇔ ∀x y t. x ∈ s ∧ y ∈ s ∧ &0 ≤ t ∧ t ≤ &1 ⇒ f(t · x + (&1 − t) · y) ≤ t · f(x) + (&1 − t) · f(y)` |
| `ConvexChordSlopes` | `real_convex_on(s, f) ∧ x ∈ s ∧ z ∈ s ∧ x < y ∧ y < z ⇒ (f(y) − f(x)) / (y − x) ≤ (f(z) − f(x)) / (z − x) ∧ (f(z) − f(x)) / (z − x) ≤ (f(z) − f(y)) / (z − y)` |
| `ConvexIffChordSlopes` | `real_convex_on(s, f) ⇔ ∀x y z. x ∈ s ∧ z ∈ s ∧ x < y ∧ y < z ⇒ (f(y) − f(x)) / (y − x) ≤ (f(z) − f(y)) / (z − y)` |
| `DerivativeIncreasingConvex` | `real_interval(s) ∧ (∀x. x ∈ s ⇒ real_derivative_at(f, x, f'(x))) ∧ real_increasing_on(s, f') ⇒ real_convex_on(s, f)` |
| `SecondDerivativeNonnegConvex` | `real_interval(s) ∧ (∀x. x ∈ s ⇒ real_derivative_at(f, x, f'(x)) ∧ real_derivative_at(f', x, f''(x)) ∧ &0 ≤ f''(x)) ⇒ real_convex_on(s, f)` |
| `ExpConvex` | `real_convex_on(𝕌, real_exp)` |
| `NegLogConvex` | `real_convex_on({x \| &0 < x}, λx. −real_log(x))` |
| `ConvexCombinationInsert` | `finite(u) ∧ j ∉ u ∧ (∀i. i ∈ u ⇒ &0 ≤ w(i)) ∧ Σ_{i∈insert(j, u)} w(i) = &1 ⇒ Σ_{i∈u} w(i) = &1 − w(j) ∧ Σ_{i∈insert(j, u)} w(i) · y(i) = w(j) · y(j) + (&1 − w(j)) · Σ_{i∈u} real_inv(&1 − w(j)) · w(i) · y(i)` |
| `ConvexCombinationIn` | `real_interval(s) ∧ finite(k) ∧ (∀i. i ∈ k ⇒ &0 ≤ w(i) ∧ x(i) ∈ s) ∧ Σ_{i∈k} w(i) = &1 ⇒ Σ_{i∈k} w(i) · x(i) ∈ s` |
| `Jensen` | `real_convex_on(s, f) ∧ real_interval(s) ∧ finite(k) ∧ (∀i. i ∈ k ⇒ &0 ≤ w(i) ∧ x(i) ∈ s) ∧ Σ_{i∈k} w(i) = &1 ⇒ f(Σ_{i∈k} w(i) · x(i)) ≤ Σ_{i∈k} w(i) · f(x(i))` |
| `AmGm` | `(∀i. i ∈ 1 .. n ⇒ &0 ≤ x(i)) ⇒ Π_{i∈1 .. n} x(i) ≤ real_pow((Σ_{i∈1 .. n} x(i)) / &n, n)` |
| `WeightedAmGm` | `finite(k) ∧ (∀i. i ∈ k ⇒ &0 ≤ w(i) ∧ &0 < x(i)) ∧ Σ_{i∈k} w(i) = &1 ⇒ Π_{i∈k} real_rpow(x(i), w(i)) ≤ Σ_{i∈k} w(i) · x(i)` |
| `Young` | `&0 ≤ a ∧ &0 ≤ b ∧ &1 < p ∧ &1 < q ∧ real_inv(p) + real_inv(q) = &1 ⇒ a · b ≤ real_rpow(a, p) / p + real_rpow(b, q) / q` |
| `PowerSumZero` | `finite(k) ∧ Σ_{i∈k} real_rpow(real_abs(a(i)), p) = &0 ∧ j ∈ k ⇒ a(j) = &0` |
| `Holder` | `finite(k) ∧ &1 < p ∧ &1 < q ∧ real_inv(p) + real_inv(q) = &1 ⇒ Σ_{i∈k} real_abs(a(i) · b(i)) ≤ real_rpow(Σ_{i∈k} real_rpow(real_abs(a(i)), p), real_inv(p)) · real_rpow(Σ_{i∈k} real_rpow(real_abs(b(i)), q), real_inv(q))` |
| `Minkowski` | `finite(k) ∧ &1 ≤ p ⇒ real_rpow(Σ_{i∈k} real_rpow(real_abs(a(i) + b(i)), p), real_inv(p)) ≤ real_rpow(Σ_{i∈k} real_rpow(real_abs(a(i)), p), real_inv(p)) + real_rpow(Σ_{i∈k} real_rpow(real_abs(b(i)), p), real_inv(p))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
