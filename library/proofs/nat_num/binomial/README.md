# binomial — the binomial coefficients

    binomial(0, k)      = COND(k = 0, 1, 0)
    binomial(suc(n), k) = COND(k = 0, 1, binomial(n, k - 1) + binomial(n, k))

`binomial(n, k)` is the entry of Pascal's triangle in row n and column
k, and the definition is the triangle's own rule, read as a recursion on
the row. Column 0 holds 1 in every row; every other entry is the sum of
the two entries above it; row 0 holds nothing past column 0. The column
rides along as a parameter the recursive call is free to move, which is
how one recursion on n fills a table of two dimensions.

The chapter's first theorem, `Clauses`, states the triangle the way it
is drawn — `binomial(n, 0) = 1`, `binomial(0, suc(k)) = 0`, and Pascal's
rule `binomial(suc(n), suc(k)) = binomial(n, k) + binomial(n, suc(k))` —
and most later members argue from those three clauses; the binomial
theorem's step reads the COND itself, where it splits a term.

## The shape of the triangle

Two facts fix where the triangle lives. `EqZero` says an entry is zero
exactly when its column lies past its row; `Diagonal` says the right
edge is 1 all the way down. Both are inductions on the row. The entry
just past the diagonal, zero by `EqZero`, is where a row's sum stops.

`FactorialFormula` is the product formula
`k!·(n - k)!·binomial(n, k) = n!` for k ≤ n, stated without a division
because ℕ has none. It is proved in a working form without subtraction,
over the row written as m + k, by a double induction: Pascal's rule
splits the entry, and each of the two entries above it is priced by one
induction hypothesis, carrying an extra factor `suc(k)` or `suc(m)` —
and `suc(k) + suc(m)` is the new factor of the factorial.

`Symmetry` applies the factorial formula at the complementary columns
k and n − k, then cancels their common nonzero factorial factors.

## The binomial theorem

`Expansion` is

$$
(x + y)^n = \sum_{k \in 0 .. n} \operatorname{binomial}(n, k) \cdot x^k \cdot y^{n-k}
$$

over ℕ, by induction on n. For the step, Pascal's rule splits each term
of row n + 1 into a share from the entry above it and, past column 0, a
share from the entry above-left. The shares from above add up to y times
row n's expansion — the last of them is `binomial(n, n + 1) = 0`, which
is `EqZero` — and the shares from above-left, read one column along, to
x times it. The sums are `iterate/nat/nat_sum`'s, over the interval `0 .. n`.

The same theorem over ℝ, with each coefficient carried in by `&`, is
`real/real_pow`'s `BinomialExpansion`: the proof is this one read in ℝ.

## What the coefficients count

`SubsetCount` says a set of n elements has `binomial(n, k)` subsets of k
elements, and is the reason the numbers are called what they are. By
induction on n: a set of n + 1 elements is a point x added to a set t of
n, and a subset of size k + 1 either misses x — a subset of t of size
k + 1 — or is x added to a subset of t of size k. The two kinds do not
meet, adding x tells the second kind apart, and Pascal's rule adds the
two counts.

## The central coefficients

The middle entry C(2n, n) of an even row and its neighbour C(2m + 1, m)
in an odd one. One step from C(2n, n) to C(2n + 2, n + 1) multiplies by
$\frac{2(2n+1)}{n+1}$ (`CentralBinomialRecurrence`), which keeps $C(2n, n)$ at
least $\frac{4^n}{2n+1}$ (`CentralBinomialLowerBound`); and C(2m + 1, m), one of
two equal terms of a row summing to 2 · 4ᵐ, is at most 4ᵐ
(`MiddleBinomialOddBound`). These are the estimates Chebyshev's bounds
and Bertrand's postulate run on, in `nat_num/prime_distribution`.

## Members

| member | statement |
|---|---|
| `BinomialDef` | the definition above |
| `Clauses` | `(∀n. binomial(n, 0) = 1) ∧ (∀k. binomial(0, suc(k)) = 0) ∧ (∀n k. binomial(suc(n), suc(k)) = binomial(n, k) + binomial(n, suc(k)))` |
| `EqZero` | `∀n k:num. binomial(n, k) = 0 ⇔ n < k` |
| `Diagonal` | `∀n:num. binomial(n, n) = 1` |
| `ColumnOne` | `∀n:num. binomial(n, 1) = n` |
| `ColumnTwo` | `∀n:num. 2 * binomial(n, 2) + n = n * n` — twice binomial(n, 2) is n(n − 1) |
| `FactorialFormula` | `∀n k:num. k ≤ n ⇒ factorial(k) * factorial(n - k) * binomial(n, k) = factorial(n)` |
| `Symmetry` | `∀n k:num. k ≤ n ⇒ binomial(n, k) = binomial(n, n - k)` |
| `Expansion` | `∀n:num. ∀x y:num. nat_pow(x + y, n) = sum(0 .. n, λk:num. binomial(n, k) * nat_pow(x, k) * nat_pow(y, n - k))` |
| `PowSecondOrder` | `∀a n:num. ∃r:num. (1 + a) ^ n = 1 + n * a + binomial(n, 2) * a ^ 2 + a ^ 3 * r` — the binomial theorem to second order |
| `SubsetCount` | `∀n k:num. ∀s:set(A). has_size(s, n) ⇒ has_size({t:set(A) \| t ⊆ s ∧ has_size(t, k)}, binomial(n, k))` |
| `CentralBinomialRecurrence` | `∀n:num. (n + 1) * binomial(2 * n + 2, n + 1) = 2 * (2 * n + 1) * binomial(2 * n, n)` — one step along the central coefficients |
| `CentralBinomialLowerBound` | `∀n:num. 4 ^ n ≤ (2 * n + 1) * binomial(2 * n, n)` |
| `MiddleBinomialOddBound` | `∀m:num. binomial(2 * m + 1, m) ≤ 4 ^ m` |

## Reading the proofs

Corpus-wide conventions are in [proofs/README.md](../../README.md) and
are not restated here. One chapter-specific spelling: `∅⟨A:τ⟩` is the
empty set of elements of type τ — `∅⟨A:A⟩` the empty subset, `∅⟨A:set(A)⟩`
the empty family of subsets — written where nothing else in the text
fixes which one is meant.
