# prime_distribution — how the primes are spread: Chebyshev's bounds and Bertrand's postulate

π(n) counts the primes up to n and the primorial multiplies them. The
central binomial coefficient C(2m, m) carries both bounds. Every prime in
⟬m + 1, 2m + 1⟧ divides C(2m + 1, m) (`nat_prime.PrimesBetweenDivideBinomial`),
which is at most 4 ^ m (`binomial.MiddleBinomialOddBound`), and that bounds
the primorial by 4 ^ n. Every prime power dividing C(2n, n) is at most 2n
while the coefficient is at least $\frac{4^n}{2n+1}$
(`binomial.CentralBinomialLowerBound`), which bounds π from below. Erdős's
argument for Bertrand's postulate plays the two against each other: with no
prime in ⟬n, 2n⟧, every prime factor of C(2n, n) is at most 2n/3, and the
product of their powers is then too small for n large; the small n are
settled by a chain of primes each less than twice the one before.

## Members

| Member | Statement |
|---|---|
| `PrimeCountingDef` | `prime_counting`: num → num |
| `PrimorialDef` | `primorial`: num → num |
| `VonMangoldtDef` | `von_mangoldt`: num → real |
| `ChebyshevPsiDef` | `chebyshev_psi`: num → real |

## π and the primorial

`primorial.go`. Only finitely many primes are at most n, and for m ≤ n they
split into those up to m and those in ⟬m, n⟧; π and the primorial read that
split as a sum and a product. π(n) ≤ n, π is monotone, and at most m + 1
primes are at most 2m, since besides 2 each is an odd number 2t − 1 with t
in 1 .. m. The primorial only grows at primes and is at least 1. Split at
m + 1, the primes in ⟬m + 1, 2m + 1⟧ all divide C(2m + 1, m), which is at
most 4 ^ m (both facts from the lower chapters named above), so by
induction the primorial of n is at most 4 ^ n.

| Member | Statement |
|---|---|
| `PrimesFinite` | Only finitely many primes are at most n |
| `PrimesSplit` | For m ≤ n, the primes up to n are those up to m together with those in ⟬m, n⟧, the two parts disjoint and finite |
| `PrimeCountingLessEqSelf` | At most n primes are at most n |
| `PrimeCountingMonotone` | π grows with its argument |
| `PrimeCountingSplit` | For m ≤ n, π(n) is π(m) plus the number of primes in ⟬m, n⟧ |
| `PrimeCountingDoubleBound` | At most m + 1 primes are at most 2m |
| `PrimorialClauses` | primorial(0) = 1, and primorial(n + 1) is (n + 1) · primorial(n) when n + 1 is prime, else primorial(n) |
| `PrimorialSplit` | For m ≤ n, primorial(n) is primorial(m) times the product of the primes in ⟬m, n⟧ |
| `PrimorialPositive` | The primorial is at least 1 |
| `PrimorialBound` | The product of the primes up to n is at most 4 ^ n |

## The prime powers in C(2n, n)

`central_binomial.go`. Legendre's formula counts the multiplicity of a
prime p in $C(2n, n) = \frac{(2n)!}{(n!)^2}$ as the sum over 1 .. 2n of the carries
div(2n, p ^ i) − 2 · div(n, p ^ i), the carries of n + n in base p. Each
carry is 0 or 1, and 0 once p ^ i exceeds 2n, so every prime power dividing
C(2n, n) is at most 2n, and a prime whose square exceeds 2n divides it at
most once. A prime p in ⟬2n/3, n⟧ does not divide it at all, its first
carry being 2 − 2 · 1 = 0 and every later one 0 since p² > 2n.

| Member | Statement |
|---|---|
| `CentralBinomialMultiplicity` | The multiplicity of a prime p in C(2n, n) is the sum over 1 .. 2n of the carries div(2n, p ^ i) − 2 · div(n, p ^ i) |
| `CentralBinomialPrimePower` | For n ≥ 1, every prime power dividing C(2n, n) is at most 2n |
| `CentralBinomialFactorization` | C(2n, n) is the product of its prime powers over the primes up to 2n |
| `LargePrimeMultiplicityAtMostOne` | A prime p with 2n < p² divides C(2n, n) at most once |
| `MiddlePrimesDoNotDivide` | For n ≥ 3, a prime p with p ≤ n < 3p/2 does not divide C(2n, n) |

## Erdős's bound and Bertrand's postulate

`bertrand.go`. With no prime in ⟬n, 2n⟧, a prime factor of C(2n, n) either
has its square at most 2n, and then contributes a power at most 2n, or is
at most 2n/3 and divides it at most once. Writing C(2n, n) as the product
of its prime powers bounds it by (2n) to the number of primes up to √(2n),
times the primorial of 2n/3. $C(2n, n)$ is at least $\frac{4^n}{2n+1}$
(`binomial.CentralBinomialLowerBound`); against Erdős's upper bound, and
with at most 2 ^ i + 1 primes p having p² ≤ 2n when $2n < 4^{i+1}$
(π(2m) ≤ m + 1), this forces a prime in ⟬n, 2n⟧ once n ≥ 613. Below that,
a chain of primes each less than twice the one before covers every n.

| Member | Statement |
|---|---|
| `NoPrimeBinomialBound` | For n ≥ 3 with no prime in ⟬n, 2n⟧, C(2n, n) ≤ (2n) ^ #{p prime : p² ≤ 2n} · primorial(⌊2n/3⌋) |
| `BertrandLarge` | For n ≥ 613 some prime lies in ⟬n, 2n⟧ |
| `BertrandChainPrimes` | 3, 5, 7, 13, 23, 43, 83, 163, 317 and 631 are prime |
| `BertrandSmall` | For 1 ≤ n < 613 some prime lies in ⟬n, 2n⟧ |
| `Bertrand` | Bertrand's postulate: for n ≥ 1 some prime p has n < p ≤ 2n |

## Chebyshev's bounds

`chebyshev.go`. C(2m, m) is the product of its prime powers, each at most
2m, so $4^m \le (2m+1) \cdot (2m)^{\pi(2m)}$, which gives $2^n \le n^{2\pi(n)}$.
Above, take m with m² ≤ n < (m + 1)². The primes up to m contribute at most
n ^ m ≤ 4 ^ n. Each prime in ⟬m, n⟧ has its square above n, so n raised to
their number is at most the square of their product, which divides the
primorial and is at most 4 ^ n; so $n^{\pi(n)} \le 64^n$. Taking logarithms,
with log 2 < 5/6, gives $\frac{\log 2}{2} \cdot n \le \pi(n) \cdot \log n \le 5n$, the upper bound for
every n ≥ 1.

| Member | Statement |
|---|---|
| `CentralBinomialUpperBound` | For m ≥ 1, $C(2m, m) \le (2m)^{\pi(2m)}$ |
| `ChebyshevLowerPower` | For n ≥ 2, $2^n \le n^{2\pi(n)}$ |
| `ChebyshevUpperPower` | $n^{\pi(n)} \le 64^n$ |
| `ChebyshevUpperBound` | For n ≥ 1, $\pi(n) \cdot \log n \le 5n$ |
| `ChebyshevBounds` | Chebyshev's bounds: for n ≥ 2, $\frac{\log 2}{2} \cdot n \le \pi(n) \cdot \log n \le 5n$ |

## Λ and ψ (mangoldt.go)

The von Mangoldt function Λ(n), `von_mangoldt`, is log p at a power pᵏ
of a prime with k > 0 and 0 elsewhere, p being the prime the table's
`«primeBase»` picks from pᵏ, and Chebyshev's ψ(n), `chebyshev_psi`, is the
sum of Λ over 1 .. n. Over a set of integers from 1 to n, Λ adds up to
the sum, over the primes p ≤ n, of the number of positive powers of p
in the set times log p; over the divisors of n the values of Λ add up to log n, the
logarithm of n's factorization. Over the prime powers pᵏ with k ≥ 2 the
series of Λ(n)/n converges. ψ is nonnegative and monotone,
ψ(n) ≤ π(n)·log n ≤ 5n by Chebyshev's bound, so ψ(n)/n lies between 0
and 5, and the primes in ⟬m, n⟧ weighted by log m are counted by ψ(n).

| member | statement |
|---|---|
| `PrimePowerChosenBase` | `∀p k:num. nat_prime(p) ∧ 0 < k ⇒ «primeBase»(p ^ k) = p` |
| `MangoldtPrimePower` | `∀p k:num. nat_prime(p) ∧ 0 < k ⇒ von_mangoldt(p ^ k) = log(&p)` |
| `MangoldtNonneg` | `∀n:num. &0 ≤ von_mangoldt(n)` |
| `MangoldtLessEqLog` | `∀n:num. 0 < n ⇒ von_mangoldt(n) ≤ log(&n)` |
| `MangoldtPrimePowersConverge` | `∃M:real. real_sums(λn:num. COND(nat_prime(n + 1), &0, von_mangoldt(n + 1) * real_rpow(&(n + 1), -&1)), M)` |
| `LogPrimeFactorization` | `∀n:num. 0 < n ⇒ Σ_{p∈«primes»(n)} «multiplicityWeight»(n, p) = log(&n)` |
| `MangoldtSumByPrimes` | `∀n:num. ∀s:set(num). s ⊆ 1 .. n ⇒ Σ_{d∈s} von_mangoldt(d) = Σ_{p∈«primes»(n)} &card(«powersIn»(s, p)) * log(&p)` |
| `MangoldtDivisorSum` | `∀n:num. 0 < n ⇒ Σ_{d∈{d:num \| d ∣ n}} von_mangoldt(d) = log(&n)` |
| `PsiMonotone` | `∀m n:num. m ≤ n ⇒ chebyshev_psi(m) ≤ chebyshev_psi(n)` |
| `PsiNonneg` | `∀n:num. &0 ≤ chebyshev_psi(n)` |
| `PrimePowerCountLogBound` | `∀p n:num. ∀s:set(num). 2 ≤ p ∧ p ≤ n ∧ (∀d:num. d ∈ s ⇒ (∃k:num. 0 < k ∧ d = p ^ k) ∧ d ≤ n) ⇒ &card(s) * log(&p) ≤ log(&n)` |
| `PsiLessEqPiLog` | `∀n:num. chebyshev_psi(n) ≤ &prime_counting(n) * log(&n)` |
| `PsiLinearBound` | `∀n:num. chebyshev_psi(n) ≤ &5 * &n` |
| `PsiRatioBound` | `∀n:num. &0 ≤ chebyshev_psi(n) / &n ∧ chebyshev_psi(n) / &n ≤ &5` |
| `PrimeCountingThroughPsi` | `∀m n:num. 0 < m ∧ m ≤ n ⇒ (&prime_counting(n) - &prime_counting(m)) * log(&m) ≤ chebyshev_psi(n)` |
