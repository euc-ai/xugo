# dirichlet_l_function — the L-series of a Dirichlet character: holomorphic on Re s > 0 for a non-principal character, and not zero at 1

The L-series of a Dirichlet character χ is its Dirichlet series,
`dirichlet_series(χ, s)`; it has no constant of its own. For a
non-principal χ the partial sums of χ are bounded, so the series
converges and is holomorphic on the whole half-plane Re s > 0. Its
derivative is minus itself times the series of Λ·χ, and for Re s > 1 it
is an exponential and has no zero — both read from `dirichlet_series`
at the completely multiplicative χ.

The chapter's theorem is that the L-series of a non-principal character
does not vanish at 1 (`LSeriesNonzeroAtOne`), the fact Dirichlet's
theorem turns on. For a character that is not real-valued it is
`riemann_zeta.MertensInequality` at f = χ: ζ(σ)³·|L(σ, χ)|⁴·|L(σ, χ²)| ≥ 1,
where χ² is again non-principal, so L(·, χ) is differentiable at 1 and
L(·, χ²) continuous there, and a function differentiable at 1 that meets
that bound against one continuous at 1 does not vanish at 1
(`riemann_zeta.MertensNonvanishing`). For a real character χ² is
principal and that count fails; the argument is Monsky's. The divisor
sums $c(n) = \sum_{d \mid n} \chi(d)$, the table's `«divisorSum»`, are nonnegative and at
least 1 at the squares, so the power series Σ c(n)·tⁿ is unbounded as
t → 1⁻ (`real_series.SquarePowersUnbounded`). It is also the Lambert
series $\sum \chi(n) \cdot \frac{t^n}{1-t^n}$ (`real_power_series.LambertExpansion`, read at the
real part of χ), and if the L-series vanished at 1 that would be minus
Σ χ(n)·b(n, t) with the weights $b(n, t) = \frac{1}{n(1-t)} - \frac{t^n}{1-t^n}$, the table's `«weight»`,
decreasing from 1 to 0 — bounded by φ(q), by Abel's inequality
(`real_sum.AbelInequality`).

For a non-principal χ the series of Λ·χ, which is −L′/L on Re s > 1,
extends to a function continuous at 1 (`NonprincipalMangoldtContinuous`).

## The L-series (l_series.go)

| member | statement |
|---|---|
| `LSeriesConverges` | `∀q:num. ∀χ:(num → complex). ∀s:complex. dirichlet_character(q, χ) ∧ 0 < q ∧ (∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1) ∧ &0 < re(s) ⇒ ∃v:complex. dirichlet_sums(χ, s, v)` |
| `LSeriesHolomorphic` | `∀q:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1) ⇒ holomorphic_on({s:complex \| &0 < re(s)}, λs:complex. dirichlet_series(χ, s))` |
| `LSeriesMangoldt` | `∀q:num. ∀χ:(num → complex). ∀s:complex. dirichlet_character(q, χ) ∧ 0 < q ∧ &1 < re(s) ⇒ complex_derivative_at(λz:complex. dirichlet_series(χ, z), s, -(dirichlet_series(χ, s) * dirichlet_series(λn:num. &von_mangoldt(n) * χ(n), s)))` |
| `LSeriesNonzeroRight` | `∀q:num. ∀χ:(num → complex). ∀s:complex. dirichlet_character(q, χ) ∧ 0 < q ∧ &1 < re(s) ⇒ dirichlet_series(χ, s) ≠ &0` |
| `LSeriesNonzeroAtOneComplex` | `∀q:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∃n:num. im(χ(n)) ≠ &0) ⇒ dirichlet_series(χ, &1) ≠ &0` |
| `LSeriesNonzeroAtOne` | `∀q:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1) ⇒ dirichlet_series(χ, &1) ≠ &0` |
| `NonprincipalMangoldtContinuous` | `∀q:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1) ⇒ ∃Q:(complex → complex). complex_continuous_at(Q, &1) ∧ (∀s:complex. &1 < re(s) ⇒ Q(s) = dirichlet_series(λn:num. &von_mangoldt(n) * χ(n), s))` |

## A real character (real_character.go)

| member | statement |
|---|---|
| `CharacterDivisorSumPrimePowerNonneg` | `∀q p k:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∀n:num. im(χ(n)) = &0) ∧ nat_prime(p) ⇒ &0 ≤ «divisorSum»(χ, p ^ k)` |
| `CharacterDivisorSumEvenPrimePowerAtLeastOne` | `∀q p k:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∀n:num. im(χ(n)) = &0) ∧ nat_prime(p) ⇒ &1 ≤ «divisorSum»(χ, p ^ (2 * k))` |
| `CharacterDivisorSumNonneg` | `∀q n:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∀k:num. im(χ(k)) = &0) ∧ 0 < n ⇒ &0 ≤ «divisorSum»(χ, n)` |
| `CharacterDivisorSumSquareAtLeastOne` | `∀q m:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∀k:num. im(χ(k)) = &0) ∧ 0 < m ⇒ &1 ≤ «divisorSum»(χ, m * m)` |
| `MonskyWeights` | `∀t:real. ∀n:num. &0 ≤ t ∧ t < &1 ∧ 0 < n ⇒ «weight»(1, t) = &1 ∧ &0 ≤ «weight»(n + 1, t) ∧ «weight»(n + 1, t) ≤ «weight»(n, t)` |
| `MonskyBound` | `∀q:num. ∀χ:(num → complex). ∀t S:real. dirichlet_character(q, χ) ∧ 0 < q ∧ (∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1) ∧ dirichlet_series(χ, &1) = &0 ∧ &0 ≤ t ∧ t < &1 ∧ real_sums(λn:num. «divisorSum»(χ, n + 1) * t ^ (n + 1), S) ⇒ \|S\| ≤ &totient(q)` |
| `LSeriesNonzeroAtOneReal` | `∀q:num. ∀χ:(num → complex). dirichlet_character(q, χ) ∧ 0 < q ∧ (∀n:num. im(χ(n)) = &0) ∧ (∃n:num. nat_coprime(n, q) ∧ χ(n) ≠ &1) ⇒ dirichlet_series(χ, &1) ≠ &0` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
