# primes_in_progressions — Dirichlet's theorem: the primes of an arithmetic progression, their density as s → 1⁺ and their infinitude

For q > 0 and a coprime to q there are infinitely many primes
p ≡ a mod q (`PrimesInProgression`). The proof weighs the progression
by a Dirichlet series and lets the real argument σ decrease to 1.

The orthogonality of the characters mod q writes the series of Λ over
the progression as the average, over the characters, of conj(χ(a))
times the series of Λ·χ. The series of Λ·χ is minus the logarithmic
derivative of the L-series of χ. For the principal character it is the
series of Λ up to a bounded term, with the pole of ζ's logarithmic
derivative: (σ − 1) times it tends to 1. For every other character it
extends continuously to 1, because the L-series does not vanish there
(`dirichlet_l_function.NonprincipalMangoldtContinuous`). So (σ − 1)
times the series over the progression tends to 1/φ(q): each class
coprime to q carries the same share of the pole. Over the prime powers
pᵏ with k ≥ 2 the series of Λ converges at σ = 1
(`prime_distribution.MangoldtPrimePowersConverge`), so they contribute a
bounded amount, and the same holds for the primes alone,
weighted by log p (`ProgressionPrimeDensity`), and finitely many primes
could not carry a pole.

No logarithm of an L-series is taken and the principal L-series is
never continued; the density is stated in this weighted form.

## The Mangoldt series of a progression near 1 (mangoldt_density.go)

| member | statement |
|---|---|
| `ProgressionMangoldtSeries` | `∀q a:num. ∀s:complex. 0 < q ∧ nat_coprime(a, q) ∧ &1 < re(s) ⇒ Σ_{χ∈{χ:num → complex \| dirichlet_character(q, χ)}} conj(χ(a)) * dirichlet_series(λn:num. complex_of_real(von_mangoldt(n)) * χ(n), s) = &totient(q) * dirichlet_series(λn:num. COND(n ≡ a (mod q), complex_of_real(von_mangoldt(n)), &0), s)` |
| `PrincipalMangoldtPole` | `∀q:num. ∀ε:real. 0 < q ∧ &0 < ε ⇒ ∃δ:real. &0 < δ ∧ (∀σ:real. &1 < σ ∧ σ < &1 + δ ⇒ \|&(σ - &1) * dirichlet_series(λn:num. COND(nat_coprime(n, q), complex_of_real(von_mangoldt(n)), &0), &σ) - &1\| < ε)` |
| `ProgressionMangoldtDensity` | `∀q a:num. ∀ε:real. 0 < q ∧ nat_coprime(a, q) ∧ &0 < ε ⇒ ∃δ:real. &0 < δ ∧ (∀σ:real. &1 < σ ∧ σ < &1 + δ ⇒ \|&(σ - &1) * dirichlet_series(λn:num. COND(n ≡ a (mod q), complex_of_real(von_mangoldt(n)), &0), &σ) - &(&1 / &totient(q))\| < ε)` |

## From Λ to the primes (primes.go)

| member | statement |
|---|---|
| `ProgressionPrimeDensity` | `∀q a:num. ∀ε:real. 0 < q ∧ nat_coprime(a, q) ∧ &0 < ε ⇒ ∃δ:real. &0 < δ ∧ (∀σ:real. &1 < σ ∧ σ < &1 + δ ⇒ \|&(σ - &1) * dirichlet_series(λn:num. COND(nat_prime(n) ∧ n ≡ a (mod q), complex_of_real(log(&n)), &0), &σ) - &(&1 / &totient(q))\| < ε)` |
| `PrimesInProgression` | `∀q a:num. 0 < q ∧ nat_coprime(a, q) ⇒ infinite({p:num \| nat_prime(p) ∧ p ≡ a (mod q)})` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
