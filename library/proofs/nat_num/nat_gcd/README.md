# nat_gcd — the greatest common divisor, defined in ℕ

    nat_gcd     = λa b. εd. (d ∣ a ∧ d ∣ b) ∧ ∀e. (e ∣ a ∧ e ∣ b) ⇒ e ∣ d
    nat_coprime = λa b. nat_gcd(a, b) = 1

— `∣` being `nat_num/nat_divides`'s relation, so both definitions stand
on ℕ's own construction and nothing above it.

The definition ℕ's gcd arrived with does not: `num_gcd(a, b)` is
`num_of_int(int_gcd(&a, &b))` and `num_coprime` is `int_coprime` of the
embeddings, which puts ℤ underneath every ℕ statement about common
divisors. This chapter puts the definitions back in ℕ.

Three things about the specification above are choices.

**Maximality is stated by DIVISIBILITY, not by ≤.** It is the stronger
property, it is the one the theorems actually use, and — unlike the
≤ version — it is total: at (0, 0) every natural is a common divisor, so
there is no ≤-greatest one and the ε would be choosing from an empty
set, while the ∣-greatest one is 0.

**The arguments are curried.** A gcd that takes a pair puts `fst` and
`snd` into everything that unfolds it. Nothing here takes a pair, so
nothing here meets a projection.

**Coprimality is `gcd = 1`,** not the Bézout condition. The
specification's `Coprime` is where that reading is shown to
be equivalent to the one a reader expects — 1 is the only common
divisor — in ℕ's own terms.

The two constants are defined here (`definitions.go`), through the
define door: each equation is read in the chapter's vocabulary, the
kernel mints the constant, and the definition entry is what a proof
cites to unfold it — in this package or any other, the same constant
with the same defining theorem behind it.

## Where ℤ appears, and why it does not

Nowhere. Like `nat_divides` before it, the chapter never
leaves ℕ.

A Hilbert choice is well formed whatever is true; what has to be earned
is that it is choosing from something. Here that is: some natural is a
common divisor of a and b that every common divisor divides. The first
proof of it descended — read maximality as Bézout's identity, whose
combination `a·x + b·y` needs coefficients ℕ does not have — and for a
while this chapter was the one place in the native development where a
proof genuinely left ℕ.

It never needed to. Maximality here is stated by DIVISIBILITY, and the
∣-greatest common divisor is what Euclid's algorithm computes — no
coefficients involved. The existence proof runs the algorithm as a
course-of-values induction on the first argument. The step passes from
(a, b) to the SWAPPED pair (nat_mod(b, a), a) — the swap is what puts the
remainder, the one thing that shrank, into the induction's slot — and
the move keeps the pair's common divisors (`dividesResidue`, which the
residue tier already needed); at a = 0 the gcd is b outright. The
Bézout reading is a strictly stronger statement about the same number,
and nothing in the chapter ever used the coefficients it provides.

The induction is `nat_order.StrongInduction`, cited at the predicate
"a has a gcd with every b".

## Members

| member | statement |
|---|---|
| `gcdExists` | `∀a b:num. ∃d:num. (d ∣ a ∧ d ∣ b) ∧ ∀e. e ∣ a ∧ e ∣ b ⇒ e ∣ d` — Euclid's algorithm as an induction |
| `Gcd` | the specification, at `nat_gcd(a, b)` itself — gcd's universal property |
| `Coprime` | `∀a b:num. nat_coprime(a, b) ⇔ ∀d:num. d ∣ a ∧ d ∣ b ⇒ d = 1` |
| `CoprimeSym` | `∀a b:num. nat_coprime(a, b) ⇔ nat_coprime(b, a)` |
| `OneCoprime` | `∀n:num. nat_coprime(1, n)` |
| `dividesResidue` | `∀d n a:num. d ∣ n ⇒ (d ∣ nat_mod(a, n) ⇔ d ∣ a)` |
| `CoprimeLMod` | `∀a n:num. nat_coprime(nat_mod(a, n), n) ⇔ nat_coprime(a, n)` |
| `CoprimeRMod` | `∀a n:num. nat_coprime(n, nat_mod(a, n)) ⇔ nat_coprime(n, a)` |
| `CoprimeCancel` | `∀p a b:num. nat_coprime(p, b) ∧ p ∣ a * b ⇒ p ∣ a` — a coprime factor cancels from a divisibility |
| `DivisorProductFactors` | `d ∣ m * n ⇒ ∃a b. d = a * b ∧ a ∣ m ∧ b ∣ n` — a divisor of a product splits between its factors |
| `CoprimeProductDivides` | `∀a b n:num. nat_coprime(a, b) ∧ a ∣ n ∧ b ∣ n ⇒ a * b ∣ n` — two coprime divisors divide together |
| `CoprimeMul` | `∀a b n:num. nat_coprime(a * b, n) ⇔ nat_coprime(a, n) ∧ nat_coprime(b, n)` |
| `CoprimePowRight` | `∀a b k:num. nat_coprime(a, b) ⇒ nat_coprime(a, b ^ k)` |
| `GcdFromCommonMultiples` | If d ∣ r·e and r·e divides every positive common multiple of d and r, then e·gcd(d, r) = d |
| `GcdMulLeft` | `∀c a b:num. nat_gcd(c * a, c * b) = c * nat_gcd(a, b)` — a common factor comes out of a gcd |

`gcdExists` and `dividesResidue` are chapter machinery, unexported.
The exported members are the chapter's public API.

## Cancelling a coprime factor

`CoprimeCancel` says that a divisor p coprime to b divides a whenever
it divides a·b. The common factor law `GcdMulLeft` gives
`nat_gcd(a·p, a·b) = a·nat_gcd(p, b) = a`. Since p divides both
arguments, the gcd's universal property puts p under a. This also
covers a = 0.

`CoprimeProductDivides` is its first consequence: two coprime divisors
of n divide it together. n is a taken some number of times, e; b divides
a·e and shares nothing with a, so it divides e, and n is a·b taken the
rest.

Coprimality to n passes to and from the factors of a product
(`CoprimeMul`), and coprimality to b passes to every power of b
(`CoprimePowRight`), by induction using the product law at each successor.

## What the native definitions made unnecessary

The two residue members are where the native definitions pay. Over
the ℤ-routed definitions the left one descends to ℤ, unfolds
coprimality into a Bézout combination and a congruence into a multiple
of the modulus, and regroups the combination by ring normalization; the
right one then transposes a Bézout combination to get the slots swapped.

Read through `Coprime`, neither has any content to transplant.
Coprimality is a statement about a pair's common divisors; the pairs
`(nat_mod(a, n), n)` and `(a, n)` have the same ones, because a divisor of
n counts the whole copies of n inside a and so cannot tell a from its
remainder (`dividesResidue`). Both members are one sentence, over the
same three facts. The slot symmetry is
free for the same reason — a common divisor of a pair does not know
which slot it came from — so `CoprimeRMod` is not derived from
`CoprimeLMod` at all.

## Reading the proofs

Corpus-wide conventions — ground-cite witnesses, the `↦` marker, comment
policy, statement style — are in [proofs/README.md](../../README.md)
and are not restated here.

Two chapter-specific things. `dividesResidue` is cited WHOLE rather
than at an instance: it is used for its quantifier over divisors, which
is the part of the statement the argument runs against, so there is no
instance to name. And that proof's induction is shaped `Normalized`:
`ByInduction` installs the principle as its file states it, so the
assembly is one ⇒-elimination, but the principle grounded at a
predicate of this depth keeps λ-redexes the proved step must meet, and
the shaping reduces them (the engine manual's §`ByInduction` records
the wall).
