# dirichlet_series — Dirichlet series: convergence on half-planes, holomorphy and the derivative, the product as a convolution, and the exponential form for a completely multiplicative coefficient

A Dirichlet series is $\sum_{n \ge 1} a(n) \cdot n^{-s}$, with $n^{-s}$ the complex
power `complex_cpow(&n, −s)`. `dirichlet_sums(a, s, v)` says that it
sums to v and `dirichlet_series(a, s)` is the sum, as `complex_sums` and
a chosen value are for any series. The series is indexed from 1: its
term of index n is $a(n+1) \cdot (n+1)^{-s}$, and the value a(0) is never
read. `dirichlet_convolution(a, b)` is the sequence
$n \mapsto \sum_{d \mid n} a(d) \cdot b(n/d)$, whose series is the product of the two series.

The chapter takes the half-plane of convergence as a hypothesis — a
real σ at which the moduli are summable, a bound on the coefficients, a
bound on their partial sums — and names no abscissa.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `dirichlet_sums(a, s, v)` | `complex_sums(λn. a(n + 1) * complex_cpow(&(n + 1), −s), v)` |
| `dirichlet_series(a, s)` | the v with `dirichlet_sums(a, s, v)` |
| `dirichlet_convolution(a, b, n)` | `Σ_{d∈{d \| d ∣ n}} a(d) * b(div(n, d))` |

## Convergence (convergence.go)

`dirichlet_sums` is linear in the coefficients: it adds, scales, holds
the zero sequence at 0, and passes to a finite sum of sequences. A
series with real coefficients at a real σ is the embedding of the real
series. The modulus of $n^{-s}$ is $n^{-\operatorname{Re} s}$, so absolute convergence at a real σ
gives the closed half-plane to its right, and bounded coefficients give
Re s > 1 with the sum within $\frac{B}{\operatorname{Re} s - 1}$ of the first coefficient;
coefficients that are bounded, or at most log n, give absolute
convergence at every real σ > 1. Two series with real coefficients at
a real σ > 1, the first at most log n, differ by at most the sum of any
summable majorant of their weighted differences
(`DirichletSeriesDifferenceBound`).
Partial summation writes a partial sum through the partial sums A(n) of
the coefficients; when those are bounded the series converges on
Re s > 0, conditionally, with a remainder controlled by
$\lvert n^{-s} - (n+1)^{-s} \rvert \le \lvert s \rvert \cdot n^{-\operatorname{Re} s - 1}$.

| member | statement |
|---|---|
| `DirichletSeriesValue` | `∀a:(num → complex). ∀s v:complex. dirichlet_sums(a, s, v) ⇒ dirichlet_series(a, s) = v` |
| `DirichletSumsAdd` | `∀a b:(num → complex). ∀s v w:complex. dirichlet_sums(a, s, v) ∧ dirichlet_sums(b, s, w) ⇒ dirichlet_sums(λn:num. a(n) + b(n), s, v + w)` |
| `DirichletSumsScale` | `∀a:(num → complex). ∀s v c:complex. dirichlet_sums(a, s, v) ⇒ dirichlet_sums(λn:num. c * a(n), s, c * v)` |
| `DirichletSumsZero` | `∀s:complex. dirichlet_sums(λn:num. &0, s, &0)` |
| `DirichletSumsFiniteSum` | `∀F:(A → num → complex). ∀V:(A → complex). ∀s:complex. ∀S:set(A). finite(S) ∧ (∀x:A. x ∈ S ⇒ dirichlet_sums(F(x), s, V(x))) ⇒ dirichlet_sums(λn:num. Σ_{x∈S} F(x, n), s, Σ_{x∈S} V(x))` |
| `DirichletSeriesOfReal` | `∀f:(num → real). ∀σ v:real. real_sums(λn:num. f(n + 1) * real_rpow(&(n + 1), -σ), v) ⇒ dirichlet_series(λn:num. &f(n), &σ) = &v` |
| `AbsolutelySummableRight` | `∀a:(num → complex). ∀σ t:real. ∀s:complex. real_sums(λn:num. \|a(n + 1)\| * real_rpow(&(n + 1), -σ), t) ∧ σ ≤ re(s) ⇒ ∃u:real. real_sums(λn:num. \|a(n + 1) * complex_cpow(&(n + 1), -s)\|, u) ∧ u ≤ t` |
| `AbsolutelyConvergentRight` | `∀a:(num → complex). ∀σ t:real. ∀s:complex. real_sums(λn:num. \|a(n + 1)\| * real_rpow(&(n + 1), -σ), t) ∧ σ ≤ re(s) ⇒ ∃v:complex. dirichlet_sums(a, s, v) ∧ \|v\| ≤ t` |
| `BoundedCoefficientsConverge` | `∀a:(num → complex). ∀B:real. ∀s:complex. (∀n:num. \|a(n)\| ≤ B) ∧ &1 < re(s) ⇒ ∃v:complex. dirichlet_sums(a, s, v) ∧ \|v - a(1)\| ≤ B / (re(s) - &1)` |
| `BoundedAbsolutelySummable` | `∀a:(num → complex). ∀B σ:real. (∀n:num. \|a(n)\| ≤ B) ∧ &1 < σ ⇒ ∃t:real. real_sums(λn:num. \|a(n + 1)\| * real_rpow(&(n + 1), -σ), t)` |
| `LogBoundedAbsolutelySummable` | `∀a:(num → complex). ∀σ:real. (∀n:num. \|a(n + 1)\| ≤ log(&(n + 1))) ∧ &1 < σ ⇒ ∃t:real. real_sums(λn:num. \|a(n + 1)\| * real_rpow(&(n + 1), -σ), t)` |
| `LogBoundedCoefficientsConverge` | `∀f:(num → complex). ∀s:complex. (∀n:num. \|f(n + 1)\| ≤ log(&(n + 1))) ∧ &1 < re(s) ⇒ dirichlet_sums(f, s, dirichlet_series(f, s))` |
| `DirichletSeriesDifferenceBound` | `∀F G U:(num → real). ∀σ t:real. &1 < σ ∧ (∀n:num. \|F(n + 1)\| ≤ log(&(n + 1))) ∧ (∀n:num. \|F(n + 1) - G(n + 1)\| * real_rpow(&(n + 1), -σ) ≤ U(n)) ∧ real_sums(U, t) ⇒ \|dirichlet_series(λn:num. &F(n), &σ) - dirichlet_series(λn:num. &G(n), &σ)\| ≤ t` |
| `DirichletPartialSummation` | `∀a:(num → complex). ∀s:complex. ∀N:num. Σ_{n∈1 .. N} a(n) * complex_cpow(&n, -s) = (Σ_{k∈1 .. N} a(k)) * complex_cpow(&(N + 1), -s) + Σ_{n∈1 .. N} (Σ_{k∈1 .. n} a(k)) * (complex_cpow(&n, -s) - complex_cpow(&(n + 1), -s))` |
| `BoundedSumsConverge` | `∀a:(num → complex). ∀B:real. ∀s:complex. ∀N:num. (∀M:num. \|Σ_{k∈1 .. M} a(k)\| ≤ B) ∧ &0 < re(s) ∧ 0 < N ⇒ ∃v:complex. dirichlet_sums(a, s, v) ∧ \|v - Σ_{n∈1 .. N} a(n) * complex_cpow(&n, -s)\| ≤ &2 * B * \|s\| / (re(s) * real_rpow(&N, re(s)))` |
| `DirichletSeriesAtInfinity` | `∀a:(num → complex). ∀B ε:real. (∀n:num. \|a(n)\| ≤ B) ∧ &0 < ε ⇒ ∃c:real. ∀σ:real. c ≤ σ ⇒ \|dirichlet_series(a, &σ) - a(1)\| < ε` |

## Holomorphy (holomorphy.go)

The terms are entire functions of s, and so is each partial sum. On an
open half-plane of absolute convergence the sum has at every point the
derivative minus the series of log n · a(n), the series of the terms'
derivatives (`cauchy_integral.SeriesDerivative`), and is holomorphic.
The sum is holomorphic on Re s > 0 for bounded partial sums too
(`BoundedSumsHolomorphic`): a series of functions holomorphic on
Re s > 0, whose n-th term is at most
$C \cdot (\lvert s \rvert + 1)^2 \cdot (n+1)^{-\operatorname{Re} s - 1}$,
has a holomorphic sum there (`DominatedSeriesHolomorphic`).

| member | statement |
|---|---|
| `DirichletSeriesLocalMajorant` | `∀a:(num → complex). ∀c:real. ∀u:complex. (∀σ:real. c < σ ⇒ ∃t:real. real_sums(λn:num. \|a(n + 1)\| * real_rpow(&(n + 1), -σ), t)) ∧ c < re(u) ⇒ ∃r:real. ∃M:(num → real). ∃t:real. &0 < r ∧ real_sums(M, t) ∧ (∀n:num. ∀z:complex. \|z - u\| < r ⇒ z ∈ {w:complex \| c < re(w)} ∧ \|a(n + 1) * complex_cpow(&(n + 1), -z)\| ≤ M(n))` |
| `DirichletTermDerivative` | `∀a:(num → complex). ∀n:num. ∀z:complex. complex_derivative_at(λw:complex. a(n + 1) * complex_cpow(&(n + 1), -w), z, -&(log(&(n + 1))) * a(n + 1) * complex_cpow(&(n + 1), -z))` |
| `PartialSumHolomorphic` | `∀a:(num → complex). ∀N:num. holomorphic_on(𝕌, λz:complex. Σ_{n∈1 .. N} a(n) * complex_cpow(&n, -z))` |
| `DirichletSeriesHolomorphic` | `∀a:(num → complex). ∀c:real. (∀σ:real. c < σ ⇒ ∃t:real. real_sums(λn:num. \|a(n + 1)\| * real_rpow(&(n + 1), -σ), t)) ⇒ holomorphic_on({s:complex \| c < re(s)}, λs:complex. dirichlet_series(a, s))` |
| `DirichletSeriesDerivative` | `∀a:(num → complex). ∀c:real. ∀s:complex. (∀σ:real. c < σ ⇒ ∃t:real. real_sums(λn:num. \|a(n + 1)\| * real_rpow(&(n + 1), -σ), t)) ∧ c < re(s) ⇒ complex_derivative_at(λz:complex. dirichlet_series(a, z), s, -dirichlet_series(λn:num. &log(&n) * a(n), s))` |
| `DominatedSeriesHolomorphic` | `∀g:(num → complex → complex). ∀C:real. (∀n:num. holomorphic_on({s:complex \| &0 < re(s)}, g(n))) ∧ (∀n:num. ∀s:complex. &0 < re(s) ⇒ \|g(n, s)\| ≤ C * (\|s\| + &1) * (\|s\| + &1) * real_rpow(&(n + 1), -re(s) - &1)) ⇒ ∃F:(complex → complex). (∀s:complex. &0 < re(s) ⇒ complex_sums(λn:num. g(n, s), F(s))) ∧ holomorphic_on({s:complex \| &0 < re(s)}, F)` |
| `BoundedSumsHolomorphic` | `∀a:(num → complex). ∀B:real. (∀M:num. \|Σ_{k∈1 .. M} a(k)\| ≤ B) ⇒ holomorphic_on({s:complex \| &0 < re(s)}, λs:complex. dirichlet_series(a, s))` |

## Products, and a completely multiplicative coefficient (product.go)

The product of two absolutely convergent Dirichlet series is the series
of the convolution: the double series of the products of terms is
regrouped along the fibres of (m, n) ↦ m·n
(`complex_series.DoubleSeriesRegroup`), which are the divisor pairs.
For a completely multiplicative f the identity $\sum_{d \mid n} \Lambda(d) = \log n$
twists to (Λ·f) ∗ f = log·f, so the series of log n · f(n) is the series
of f times the series of Λ(n)·f(n): with the derivative above,
D(f)′ = −D(f)·D(Λ·f) (`LogarithmicDerivative`). That is a differential equation F′ = F·G′ with G
the series of $\frac{\Lambda(n)}{\log n} \cdot f(n)$, and on a half-plane its solutions are
the multiples of exp(G); the multiple is f(1). So for f(1) = 1 and
|f| ≤ 1 the series of f is an exponential on Re s > 1
(`LogarithmicSeries`) and never vanishes (`DirichletSeriesNonzero`). No product over the primes is formed.

| member | statement |
|---|---|
| `DirichletProduct` | `∀a b:(num → complex). ∀σ t u:real. ∀s:complex. real_sums(λn:num. \|a(n + 1)\| * real_rpow(&(n + 1), -σ), t) ∧ real_sums(λn:num. \|b(n + 1)\| * real_rpow(&(n + 1), -σ), u) ∧ σ ≤ re(s) ⇒ dirichlet_sums(dirichlet_convolution(a, b), s, dirichlet_series(a, s) * dirichlet_series(b, s))` |
| `ConvolutionTwist` | `∀f a b:(num → complex). ∀n:num. (∀m k:num. 0 < m ∧ 0 < k ⇒ f(m * k) = f(m) * f(k)) ∧ 0 < n ⇒ dirichlet_convolution(λm:num. f(m) * a(m), λm:num. f(m) * b(m), n) = f(n) * dirichlet_convolution(a, b, n)` |
| `LogSeriesProduct` | `∀f:(num → complex). ∀s:complex. (∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)) ∧ (∀n:num. \|f(n)\| ≤ &1) ∧ &1 < re(s) ⇒ dirichlet_series(λn:num. &log(&n) * f(n), s) = dirichlet_series(f, s) * dirichlet_series(λn:num. &von_mangoldt(n) * f(n), s)` |
| `LogarithmicDerivative` | `∀f:(num → complex). ∀s:complex. (∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)) ∧ (∀n:num. \|f(n)\| ≤ &1) ∧ &1 < re(s) ⇒ complex_derivative_at(λz:complex. dirichlet_series(f, z), s, -(dirichlet_series(f, s) * dirichlet_series(λn:num. &von_mangoldt(n) * f(n), s)))` |
| `LogarithmicSeries` | `∀f:(num → complex). ∀s:complex. (∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)) ∧ f(1) = &1 ∧ (∀n:num. \|f(n)\| ≤ &1) ∧ &1 < re(s) ⇒ dirichlet_series(f, s) = exp(dirichlet_series(λn:num. &(von_mangoldt(n) / log(&n)) * f(n), s))` |
| `DirichletSeriesNonzero` | `∀f:(num → complex). ∀s:complex. (∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)) ∧ f(1) = &1 ∧ (∀n:num. \|f(n)\| ≤ &1) ∧ &1 < re(s) ⇒ dirichlet_series(f, s) ≠ &0` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
