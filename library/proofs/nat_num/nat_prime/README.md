# nat_prime — primality, defined in ℕ

    nat_prime = λp. p ≠ 1 ∧ ∀x. x ∣ p ⇒ x = 1 ∨ x = p

— divisibility being `nat_num/nat_divides`'s relation, so the definition
stands on ℕ's own construction and nothing above it.

The definition ℕ's primality arrived with does not: it is the same
sentence, word for word, over a divisibility that is introduced through
the ℤ embedding — which puts ℤ underneath every ℕ statement about
primes. So unlike the three chapters before it, this one is not a
re-derivation: it is a re-spelling, the same sentence over ℕ's own
divisibility.

The constant is defined here (`definitions.go`), through the define
door: the equation is read in the chapter's vocabulary, the kernel
mints the constant, and the definition entry is what a proof cites to
unfold it — in this package or any other, the same constant with the
same defining theorem behind it.

## Where ℤ appears, and why it does not

Nowhere. None of the four native chapters leaves ℕ; this one never did.

That is not free. The classical proof that a prime dividing `a·b` and
missing `b` must divide `a` cancels the coprimality with Bézout —
`1 = p·y + b·z`, multiplied through by `a` — and Bézout needs
coefficients ℕ does not have, which is why that proof descends to ℤ
and stays down for a long ring normalization. Here the
cancellation is `nat_gcd.CoprimeCancel`, which needs no combination,
only the gcd's universal property; it lives with the gcd for that
reason, and its README tells the argument. Euclid's lemma is that
cancellation read at a prime that misses `b`.

## The infinitude of the primes

The chapter's second subject, in `infinitude.go`, is Euclid's theorem:
past any number there is a prime. The argument is the one Euclid gave,
and the file states it with the bound it delivers — `EuclidBound` says
that for every n some prime lies strictly past n and at or below
n! + 1 — because a bound that is stated can be cited, where "there
exists a larger prime" would have to be re-derived by anyone who needed
the size.

Two facts carry it, each a member in its own right. `PrimeFactor` says
every number past 1 has a prime divisor: a descent, run as a
course-of-values induction, from a composite to a proper divisor and
from there to the prime below. `PrimeDividesFactorial` says a prime
divides n! exactly when it is at most n — and it is here that Euclid's
lemma does its work, sending a prime that divides (n+1)·n! into one of
the two factors. The theorem then reads off both: the prime that
`PrimeFactor` finds in n! + 1 cannot be at most n, since it would then
divide n!, hence 1 (`nat_divides.DividesAddCancel` cancels the n!), and
`PrimeAtLeastTwo` says no prime does.

"Infinitely many" is a statement about a set, so the part closes with
`PrimesInfinite`, the chapter's one member said in the vocabulary of
sets: `infinite({p | nat_prime(p)})`. The only chapter member it cites
is `EuclidBound`: a finite set of numbers is bounded
(`num_segment.FiniteIffBounded`), and Euclid's prime past the bound lies
in the set.

## A square is a prime times a square only at zero

`SquareEqPrimeTimesSquare` is Euclid's lemma spent once more, as a
descent: if a² = p·b² with p prime, then p divides a·a and so divides a;
writing a = p·c and cancelling one p leaves b² = p·c², the same equation
at a smaller pair unless b is already 0. So the only solution is
a = b = 0. It is the ℕ half of the irrationality of √p, which
`real/rational` states; the chapter proves it by strong induction on a,
and reduces no fraction to lowest terms.

## The divisors of a prime power

`PrimePowerDivisor`: a divisor of pⁿ is p^k for some k ≤ n. Induction on
n, the divisor kept general: a divisor of pⁿ⁺¹ other than 1 has a prime
factor, which divides pⁿ⁺¹ and so is p, and once p cancels the cofactor
divides pⁿ.

`PrimePowerSquareRoot` is `PrimePowerDivisor` at a root: a number divides
its own square, so a square root of pᵉ divides pᵉ and is a power of p.

## Factorization into primes

The chapter's third subject, in `factorization.go`, is the fundamental
theorem of arithmetic: every nonzero number is a product of primes, and
the primes are determined by the number up to their order. A
factorization is a list — `list_product(l) = n`, every member of `l`
prime — and "up to order" is `list_permutation`, both from `datatypes/list`.
A list is what "a product of primes" writes down, and a permutation is
exactly the freedom commutativity gives a product. The same theorem
can be stated with an exponent function of finite support instead,
which the list form does not need.

Existence, `FactorizationExists`, is a descent of the same shape as
`PrimeFactor`'s, citing `PrimeFactor` for the prime at each step: a
number past 1 is a prime times a smaller cofactor, and the prime goes
in front of the cofactor's list.

Uniqueness rests on Euclid's lemma extended to a list,
`PrimeDividesListProduct`. `ListProductCancelPrime` spends it on the
one step the proof repeats: a prime that multiplies some k to the
product of a list of primes is a member of that list, and cancels from
it, leaving a list of primes with product k. `FactorizationUnique` is
then one induction on the first list, for every second list at once.

## Fermat's little theorem

The chapter's fourth subject, in `fermat.go`: for a prime p, aᵖ is
congruent to a modulo p. The proof is the binomial one. A prime divides
every coefficient strictly inside its row of Pascal's triangle
(`PrimeDividesBinomial`): p divides p!, which the factorial formula
splits as k!·(p − k)!·binomial(p, k), and by Euclid's lemma p divides
one of the three factors — never a factorial of a number below it. So
the binomial theorem writes (a + b)ᵖ as aᵖ + bᵖ plus terms p divides
one by one, and so all together (`nat_sum.DividesSum`): raising to the
p-th power is additive modulo p (`PowPrimeAdditive`). `FermatLittle` is
then an induction on a — (a + 1)ᵖ is aᵖ + 1 modulo p, which the
hypothesis makes a + 1. And for a not a multiple of p, aᵖ⁻¹ ≡ 1
(`FermatLittleCoprime`): aᵖ is a·aᵖ⁻¹ and a is a·1, and a, coprime to
the prime, cancels (`nat_congruence.MulCancel`).

## Squares modulo a prime

A residue 0 < a < p squares to 1 mod p exactly when p divides
(a − 1)(a + 1), so by Euclid's lemma exactly when a is 1 or p − 1
(`SelfInverse`); Wilson's theorem pairs every other unit with its
inverse. Below p/2 distinct numbers have distinct squares mod p
(`SquaresDistinctModPrime`): x² ≡ y² makes p divide (x − y)(x + y), and
both factors are below p.

## Members

| member | statement |
|---|---|
| `OneOrPrime` | `∀p:num. p = 1 ∨ nat_prime(p) ⇔ ∀d:num. d ∣ p ⇒ d = 1 ∨ d = p` |
| `PrimeAtLeastTwo` | `∀p:num. nat_prime(p) ⇒ 2 ≤ p` |
| `PrimeDividesOrCoprime` | `∀p:num. p = 1 ∨ nat_prime(p) ⇔ ∀n:num. p ∣ n ∨ nat_coprime(p, n)` |
| `PrimeCoprimeIffNotDivides` | `∀p:num. nat_prime(p) ⇔ ∀n:num. nat_coprime(p, n) ⇔ ¬(p ∣ n)` |
| `PrimeTwo` | `nat_prime(2)` |
| `PrimeDividesPrime` | `∀p q:num. nat_prime(p) ∧ nat_prime(q) ⇒ (p ∣ q ⇔ p = q)` |
| `PrimeOddUnlessTwo` | `∀p:num. nat_prime(p) ∧ p ≠ 2 ⇒ nat_odd(p)` |
| `OddPrimeHalf` | `∀p:num. nat_prime(p) ∧ p ≠ 2 ⇒ p = 2 * div(p - 1, 2) + 1` |
| `OddPrimeSplit` | `∀n:num. nat_odd(n) ∧ n ≠ 1 ⇒ ∃p m:num. nat_prime(p) ∧ p ≠ 2 ∧ nat_odd(p) ∧ nat_odd(m) ∧ n = p * m ∧ m < n` |
| `EuclidLemma` | `∀p a b:num. p = 0 ∨ p = 1 ∨ nat_prime(p) ⇒ (p ∣ a * b ⇔ p ∣ a ∨ p ∣ b)` |
| `PrimeDividesPower` | `∀p m e:num. nat_prime(p) ∧ p ∣ m ^ e ⇒ p ∣ m` |
| `FactorOfPrimeSquare` | `∀p d e:num. nat_prime(p) ∧ d * e = p * p ⇒ d = 1 ∨ d = p ∨ d = p * p` |
| `ZeroOneOrPrime` | `∀p:num. p = 0 ∨ p = 1 ∨ nat_prime(p) ⇔ ∀a b:num. p ∣ a * b ⇒ p ∣ a ∨ p ∣ b` |
| `SquareEqPrimeTimesSquare` | `∀p a b:num. nat_prime(p) ∧ a * a = p * (b * b) ⇒ a = 0 ∧ b = 0` |
| `PrimePowerSquareRoot` | `∀p e s:num. nat_prime(p) ∧ s * s = p ^ e ⇒ ∃n:num. s = p ^ n` |
| `CoprimePrimePowerIff` | `∀p k a:num. nat_prime(p) ∧ 0 < k ⇒ (nat_coprime(a, p ^ k) ⇔ ¬(p ∣ a))` |
| `PrimePowerDivisor` | `∀p n d:num. nat_prime(p) ∧ d ∣ p ^ n ⇒ ∃k:num. k ≤ n ∧ d = p ^ k` |
| `PrimeDividesFactorial` | `∀p n:num. nat_prime(p) ⇒ (p ∣ factorial(n) ⇔ p ≤ n)` |
| `PrimeFactor` | `∀n:num. 1 < n ⇒ ∃p:num. nat_prime(p) ∧ p ∣ n` |
| `PrimeDivisorsFinite` | `∀n:num. n ≠ 0 ⇒ finite({p:num \| nat_prime(p) ∧ p ∣ n})` |
| `EuclidBound` | `∀n:num. ∃p:num. nat_prime(p) ∧ n < p ∧ p ≤ factorial(n) + 1` |
| `PrimesInfinite` | `infinite({p:num \| nat_prime(p)})` |
| `PrimeDividesListProduct` | `∀p:num. ∀l:list(num). nat_prime(p) ⇒ (p ∣ list_product(l) ⇔ ∃q:num. list_member(q, l) ∧ p ∣ q)` |
| `FactorizationExists` | `∀n:num. n ≠ 0 ⇒ ∃l:list(num). (∀q:num. list_member(q, l) ⇒ nat_prime(q)) ∧ list_product(l) = n` |
| `ListProductCancelPrime` | `∀p k:num. ∀m:list(num). nat_prime(p) ∧ (∀q:num. list_member(q, m) ⇒ nat_prime(q)) ∧ p * k = list_product(m) ⇒ ∃r:list(num). list_permutation(m, cons(p, r)) ∧ (∀q:num. list_member(q, r) ⇒ nat_prime(q)) ∧ list_product(r) = k` |
| `FactorizationUnique` | `∀l m:list(num). (∀q:num. list_member(q, l) ⇒ nat_prime(q)) ∧ (∀q:num. list_member(q, m) ⇒ nat_prime(q)) ∧ list_product(l) = list_product(m) ⇒ list_permutation(l, m)` |
| `PrimeDividesBinomial` | `∀p k:num. nat_prime(p) ∧ 0 < k ∧ k < p ⇒ p ∣ binomial(p, k)` |
| `PrimesBetweenDivideBinomial` | `∀m p:num. nat_prime(p) ∧ m + 1 < p ∧ p ≤ 2 * m + 1 ⇒ p ∣ binomial(2 * m + 1, m)` |
| `PowPrimeAdditive` | `∀p a b:num. nat_prime(p) ⇒ nat_pow(a + b, p) ≡ nat_pow(a, p) + nat_pow(b, p) (mod p)` |
| `FermatLittle` | `∀p a:num. nat_prime(p) ⇒ nat_pow(a, p) ≡ a (mod p)` |
| `FermatLittleCoprime` | `∀p a:num. nat_prime(p) ∧ ¬(p ∣ a) ⇒ nat_pow(a, p - 1) ≡ 1 (mod p)` |
| `SelfInverse` | `∀p a:num. nat_prime(p) ∧ 0 < a ∧ a < p ⇒ (a * a ≡ 1 (mod p) ⇔ a = 1 ∨ a = p − 1)` — the square roots of 1 modulo a prime |
| `SquaresDistinctModPrime` | `∀p x y:num. nat_prime(p) ∧ 2 * x < p ∧ 2 * y < p ∧ x * x ≡ y * y (mod p) ⇒ x = y` — below p/2, distinct numbers have distinct squares mod p |
| `PrimeByTrialDivision` | `∀n:num. 2 ≤ n ∧ (∀d:num. nat_prime(d) ∧ d * d ≤ n ⇒ ¬(d ∣ n)) ⇒ nat_prime(n)` — trial division (`trial_division.go`) |
| `CoprimeToFactorialPrime` | `∀p m x y:num. 2 ≤ p ∧ p < (m + 1) * (m + 1) ∧ p * x = factorial(m) * y + 1 ⇒ nat_prime(p)` — a Bezout relation with m! certifies primality (`trial_division.go`) |

The members are the chapter's public API.

## Reading the proofs

Corpus-wide conventions — ground-cite witnesses, the `↦` marker, comment
policy, statement style — are in [proofs/README.md](../../README.md) and
are not restated here.

`∣` is `nat_num/nat_divides`'s relation, so the statements above read
as they would on paper.
