# real_cardinality — how many numbers there are

The comparisons of `sets/cardinal`, read at the number sets inside ℝ.
The integers and the rationals are countable, the rationals exactly as
many as the naturals; the reals are not countable, and are exactly as
many as the sets of naturals — Cantor's theorem, a ternary expansion
and Dedekind's cuts, joined by Schröder–Bernstein.

## The countable number sets

The integers are countable (`CountableInteger`): every integer is &n or
−&n for a natural n, so they lie inside the union of two images of ℕ,
and each image, their union and every subset of it are countable.

The rationals are countable (`CountableRational`): a rational is m / n
with m and n integers, the value of the quotient map at the pair (m, n),
so the rationals lie inside the quotient map's image of ℤ × ℤ, which is
countable because ℤ is. And there are exactly as many rationals as
naturals (`RationalCardEqNum`): no more, being countable, and no fewer,
since n ↦ &n sends the naturals among the rationals without identifying
two of them — Schröder–Bernstein joins the two comparisons.

## The ternary expansion

A set of naturals s is read as a real by its ternary expansion with
digits 0 and 1: the series `ternary_digits(s)`, whose n-th term is 3⁻ⁿ
when n ∈ s and 0 otherwise (`ternaryDigitsDef`), and so lies between 0
and 3⁻ⁿ (`TernaryDigitBounds`). That series has a sum
(`TernaryConverges`), by comparison with the geometric series Σ 3⁻ⁿ,
which sums because |3⁻¹| < 1.

Where two such expansions first differ — at a place n in s but not in
t — the one with the 1 is larger (`TernaryFirstDifference`). Up to n the
partial sums differ by exactly 3⁻ⁿ: for n > 0 the digit at n is peeled
off both sums and the rest agree term by term; for n = 0 each sum is its
one term. Past n the s-series only adds nonnegative terms, so its sum
x is at least its partial sum. The t-series past n sums to y less its
partial sum (`real_series.SumsOffset`), and it is termwise at most the
geometric series from 3^-(n+1), which sums to 3^-(n+1)·(1 − 3⁻¹)⁻¹ =
3⁻ⁿ/2. So y exceeds its partial sum by at most 3⁻ⁿ/2, and
x − y ≥ 3⁻ⁿ − 3⁻ⁿ/2 > 0.

So the expansion is injective (`TernaryInjective`): two different sets
differ at a least place n, and whichever of them holds n has the
strictly larger sum, so they cannot both sum to x.

So the sets of naturals inject into ℝ (`PowersetNumLeReal`): each set
goes to the value ε chooses among the sums of its expansion — a sum,
because the series converges — and two sets sent to one value have
expansions with a common sum, so they are equal.

## The reals are not countable

There are strictly more reals than naturals (`NumLessReal`): by Cantor's
theorem the sets of naturals outnumber the naturals
(`cardinal.CantorUniv`), and they inject into ℝ, so ℕ < P(ℕ) ≤ ℝ. Read
through the definition of the strict order, that is the statement that
ℝ is no larger than ℕ is false: ℝ is not countable (`RealUncountable`).
Nor are the irrationals (`IrrationalUncountable`): every real is
rational or not, so were the irrationals countable, ℝ would be the union
of two countable sets.

## The continuum

There are exactly as many reals as sets of naturals. One half is the
ternary expansion. The other is Dedekind's idea that a real is
determined by the rationals below it (`RealLePowersetNum`): the
rationals being countable, a map q tags them by naturals, no two alike,
and a real x goes to its cut — the set of tags of the rationals below
x. Of two different reals one lies below the other, say x < y, and a
rational p lies strictly between them (`rational.RationalBetween`); p's
tag is in y's cut but not in x's, since a rational below x with p's tag
would be p itself, which lies above x. So different reals have
different cuts, and every cut is a set of naturals. Each set injecting
into the other, Schröder–Bernstein makes them the same size
(`RealCardEqPowersetNum`).

## Members

The definition (definitions.go):

| entry | statement |
|---|---|
| `ternaryDigitsDef` | `ternary_digits(s, n) = COND(n ∈ s, real_pow(real_inv(&3), n), &0)` |

The countable number sets (countable.go):

| entry | statement |
|---|---|
| `CountableInteger` | `countable({x:real \| integer(x)})` |
| `CountableRational` | `countable({x:real \| rational(x)})` |
| `RationalCardEqNum` | `card_eq({x:real \| rational(x)}, 𝕌⟨num⟩)` |

The ternary expansion (ternary.go):

| entry | statement |
|---|---|
| `TernaryDigitBounds` | `&0 ≤ ternary_digits(s, n) ∧ ternary_digits(s, n) ≤ real_pow(real_inv(&3), n)` |
| `TernaryConverges` | `∃x. real_sums(ternary_digits(s), x)` |
| `TernaryFirstDifference` | `(∀k. k < n ⇒ (k ∈ s ⇔ k ∈ t)) ∧ n ∈ s ∧ n ∉ t ∧ real_sums(ternary_digits(s), x) ∧ real_sums(ternary_digits(t), y) ⇒ y < x` |
| `TernaryInjective` | `real_sums(ternary_digits(s), x) ∧ real_sums(ternary_digits(t), x) ⇒ s = t` |
| `PowersetNumLeReal` | `card_le(𝕌⟨set(num)⟩, 𝕌⟨real⟩)` |

The reals are not countable, and the continuum (continuum.go):

| entry | statement |
|---|---|
| `NumLessReal` | `card_lt(𝕌⟨num⟩, 𝕌⟨real⟩)` |
| `RealUncountable` | `¬countable(𝕌⟨real⟩)` |
| `IrrationalUncountable` | `¬countable({x:real \| ¬rational(x)})` |
| `RealLePowersetNum` | `card_le(𝕌⟨real⟩, 𝕌⟨set(num)⟩)` |
| `RealCardEqPowersetNum` | `card_eq(𝕌⟨real⟩, 𝕌⟨set(num)⟩)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
