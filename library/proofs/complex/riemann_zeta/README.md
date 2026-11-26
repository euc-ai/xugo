# riemann_zeta — the Riemann zeta function on Re s > 0: its pole at 1, its logarithmic derivative, and no zero on Re s ≥ 1

`riemann_zeta(s)` is ζ on the half-plane Re s > 0, defined there at once:
$\zeta(s) = \frac{\xi(s)}{s-1}$, where

$$
\xi(s) = 1 + \sum_{n \ge 1} \Bigl[(s-1) \cdot n^{-s} - \bigl(n^{1-s} - (n+1)^{1-s}\bigr)\Bigr]
$$

is a series that converges for Re s > 0, each of its terms being at most
$\lvert s-1 \rvert \cdot \lvert s \rvert \cdot n^{-\operatorname{Re} s - 1}$
(`complex_cpow.CpowTangentRemainderBound`). The chapter's table calls it
`«xi»`, and its bracketed term, read at index n + 1, `«xiTerm»(s, n)`. For
Re s > 1 the differences telescope to 1 and $\xi(s) = (s-1) \cdot \sum n^{-s}$, so
ζ is the sum of $n^{-s}$ there (`ZetaSums`); at s = 1 every term vanishes
and ξ(1) = 1, so ζ has a simple pole at 1 with residue 1 and
$\zeta(s) - \frac{1}{s-1}$ continues holomorphically to Re s > 0
(`ZetaContinuation`). `«xi»` is the series itself and not the product
(s − 1)·ζ(s): the two agree off 1, and at 1 the product is 0 while
«xi» is 1.

At s = 1 the constant is a quotient by zero, which in ℂ is 0:
`riemann_zeta(&1) = &0`, a convention at the pole and not a value of ζ,
so a statement that ζ has no zero excludes s = 1. For Re s ≤ 0 the
constant is not ζ — at s = 0 every term of the series vanishes and it is
−1, where ζ(0) = −1/2, and elsewhere there the series has no sum. This
chapter is not ζ on the whole plane, and the functional equation is not
here.

## The definition (definitions.go)

| constant | reading |
|---|---|
| `riemann_zeta(s)` | `«xi»(s) / (s − 1)`, with `«xi»(s)` the regularized series $1 + \sum \bigl[(s-1) \cdot n^{-s} - \bigl(n^{1-s} - (n+1)^{1-s}\bigr)\bigr]$ |

## The continuation (continuation.go)

| member | statement |
|---|---|
| `XiSums` | `∀s:complex. &0 < re(s) ⇒ complex_sums(«xiTerm»(s), «xi»(s) - &1)` |
| `XiHolomorphic` | `holomorphic_on({s:complex \| &0 < re(s)}, «xi»)` |
| `XiAtOne` | `«xi»(complex_of_real(&1)) = &1` |
| `ZetaSums` | `∀s:complex. &1 < re(s) ⇒ dirichlet_sums(λn:num. &1, s, riemann_zeta(s))` |
| `ZetaHolomorphic` | `holomorphic_on({s:complex \| &0 < re(s) ∧ s ≠ &1}, riemann_zeta)` |
| `ZetaContinuation` | `∃k:(complex → complex). holomorphic_on({s:complex \| &0 < re(s)}, k) ∧ (∀s:complex. &0 < re(s) ∧ s ≠ &1 ⇒ riemann_zeta(s) = complex_inv(s - &1) + k(s))` |
| `ZetaPole` | `(λs:complex. (s - &1) * riemann_zeta(s)) ⟶ complex_of_real(&1) (at complex_of_real(&1))` — card |

## On the closed half-plane Re s ≥ 1 (line.go)

For Re s > 1, ζ is the Dirichlet series of the constant 1, and the
chapter on Dirichlet series gives its derivative, −ζ times the series
of Λ (`ZetaMangoldt`), and ζ as the exponential of the series of
Λ(n)/log n (`ZetaExponential`) — the Euler product in logarithmic form,
from which ζ ≠ 0 there.

One inequality carries the line Re s = 1. For a completely
multiplicative f with f(1) = 1 and |f| ≤ 1 and a real σ > 1,

$$
\zeta(\sigma)^3 \cdot \lvert D(f, \sigma) \rvert^4 \cdot \lvert D(f^2, \sigma) \rvert \ge 1
$$

(`MertensInequality`): the three factors are exponentials, and the
exponent's real part is a series of nonnegative terms because
3 + 4·Re u + Re(u²) = 2(1 + Re u)² + 1 − |u|² ≥ 0 for |u| ≤ 1. At
$f(n) = n^{-it}$ the factors are ζ(σ), ζ(σ + it) and ζ(σ + 2it)
(`ZetaMertens`), the series of $n^{-v}$ at s being ζ(s + v) for
Re(s + v) > 1 (`ZetaShift`). A function differentiable at 1 that meets
the bound against one continuous at 1 does not vanish at 1, the fourth
power of a zero beating the cube of the pole (`MertensNonvanishing`). So ζ has no zero
on the line (`ZetaNonzeroOnLine`) and ξ none on the closed half-plane
(`XiNonzero`). The series of Λ, less $\frac{1}{s-1}$, continues
holomorphically to the open set `«regularDomain»` of Re s > 0 where ξ
does not vanish, and that set holds 1, where ξ is 1
(`MangoldtSeriesContinuationOffZeros`); so it continues to an open set
containing Re s ≥ 1 (`MangoldtSeriesContinuation`): the input of the
prime number theorem. Near 1, (σ − 1) times the series of Λ at a real
σ > 1 tends to 1 (`MangoldtSeriesPole`). The same inequality at a
Dirichlet character is read by `dirichlet_l_function`.

| member | statement |
|---|---|
| `ZetaDerivativeSeries` | `∀s:complex. &1 < re(s) ⇒ complex_derivative_at(riemann_zeta, s, -dirichlet_series(λn:num. &log(&n), s))` |
| `ZetaMangoldt` | `∀s:complex. &1 < re(s) ⇒ complex_derivative_at(riemann_zeta, s, -(riemann_zeta(s) * dirichlet_series(λn:num. &von_mangoldt(n), s)))` |
| `ZetaExponential` | `∀s:complex. &1 < re(s) ⇒ riemann_zeta(s) = exp(dirichlet_series(λn:num. &(von_mangoldt(n) / log(&n)), s))` |
| `ZetaShift` | `∀g:(num → complex). ∀v s:complex. (∀n:num. 0 < n ⇒ g(n) = complex_cpow(&n, -v)) ∧ &1 < re(s + v) ⇒ dirichlet_series(g, s) = riemann_zeta(s + v)` |
| `ZetaNonzeroRight` | `∀s:complex. &1 < re(s) ⇒ riemann_zeta(s) ≠ &0` |
| `MertensInequality` | `∀f:(num → complex). ∀σ:real. (∀m n:num. 0 < m ∧ 0 < n ⇒ f(m * n) = f(m) * f(n)) ∧ f(1) = &1 ∧ (∀n:num. \|f(n)\| ≤ &1) ∧ &1 < σ ⇒ &1 ≤ \|riemann_zeta(&σ)\| ^ 3 * \|dirichlet_series(f, &σ)\| ^ 4 * \|dirichlet_series(λn:num. f(n) * f(n), &σ)\|` |
| `ZetaMertens` | `∀v:complex. ∀σ:real. re(v) = &0 ∧ &1 < σ ⇒ &1 ≤ \|riemann_zeta(&σ)\| ^ 3 * \|riemann_zeta(&σ + v)\| ^ 4 * \|riemann_zeta(&σ + &2 * v)\|` |
| `ZetaRealBounds` | `∀σ:real. &1 < σ ⇒ riemann_zeta(&σ) = &\|riemann_zeta(&σ)\| ∧ &1 ≤ \|riemann_zeta(&σ)\| ∧ \|riemann_zeta(&σ)\| ≤ &1 + &1 / (σ - &1)` |
| `MertensNonvanishing` | `∀F G:(complex → complex). ∀l:complex. (∀σ:real. &1 < σ ⇒ &1 ≤ \|riemann_zeta(&σ)\| ^ 3 * \|F(&σ)\| ^ 4 * \|G(&σ)\|) ∧ complex_derivative_at(F, &1, l) ∧ complex_continuous_at(G, &1) ⇒ F(&1) ≠ &0` |
| `ZetaNonzeroOnLine` | `∀s:complex. re(s) = &1 ∧ s ≠ &1 ⇒ riemann_zeta(s) ≠ &0` |
| `XiNonzero` | `∀s:complex. &1 ≤ re(s) ⇒ «xi»(s) ≠ &0` |
| `MangoldtSeriesContinuationOffZeros` | `∃g:(complex → complex). «regularDomain» ∈ complex_topology ∧ complex_of_real(&1) ∈ «regularDomain» ∧ holomorphic_on(«regularDomain», g) ∧ (∀s:complex. &1 < re(s) ⇒ dirichlet_series(λn:num. &von_mangoldt(n), s) = complex_inv(s - &1) + g(s))` |
| `MangoldtSeriesContinuation` | `∃U:set(complex). ∃g:(complex → complex). U ∈ complex_topology ∧ (∀s:complex. &1 ≤ re(s) ⇒ s ∈ U) ∧ holomorphic_on(U, g) ∧ ∀s:complex. &1 < re(s) ⇒ dirichlet_series(λn:num. &(von_mangoldt(n)), s) = complex_inv(s - &1) + g(s)` |
| `MangoldtSeriesPole` | `∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ (∀σ:real. &1 < σ ∧ σ < &1 + δ ⇒ \|&(σ - &1) * dirichlet_series(λn:num. &von_mangoldt(n), &σ) - &1\| < ε)` |
| `EulerProduct` | `∀s:complex. &1 < re(s) ⇒ (λN:num. Π_{p∈{p:num \| nat_prime(p) ∧ p ≤ N}} complex_inv(&1 - complex_cpow(&p, -s))) ⟶ riemann_zeta(s)` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
