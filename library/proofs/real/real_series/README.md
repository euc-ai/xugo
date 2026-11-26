# real_series — infinite series of reals

A series is its sequence of terms `a : ℕ → ℝ`, and it sums to `s` when
its partial sums do: `real_sums(a, s) ⇔ (λn. Σ_{k∈0 .. n} a(k)) ⟶ s`.
Everything the chapter says about a series is therefore a statement
about the sequence of its partial sums, and the sequences chapter's
limits, order and completeness are its tools — read through the
interval calculus of `iterate/real/real_sum`, which is how a partial sum is
taken apart.

As the sequences chapter mints no `lim`, this chapter mints no value
for the sum of a series: the relation is the object. A theorem that a
series converges without naming its sum states `∃s. real_sums(a, s)`.

**The algebra and order of sums (sums.go).** A series has at most one
sum, two limits of one sequence of partial sums being equal. Sums add,
subtract and scale termwise, because a partial sum of a termwise sum,
difference or multiple is the sum, difference or multiple of the partial
sums, and limits do the same; the series of zeros sums to 0.
A series nowhere above another sums to no more: its partial sums are
nowhere above the other's, and limits keep order. A partial sum of a
nonnegative series is at most its sum: past index `n` the partial sums
only take in more nonnegative terms, so none falls below the one up to
`n`, and the limit keeps that bound. And dropping a series' first term
drops it from the sum, the partial sums of the shifted series being
those of the series one index on, less `a(0)`. Dropping the first `m + 1`
terms drops them from the sum, by induction on `m`: each step shifts
once more, since the tail past `m + 1` is the tail past `m` without its
first term `a(m + 1)`, and the partial sum to `m + 1` is the one to `m`
plus that same term. Summing a series two
terms at a time keeps its sum: the paired series' partial sum to `n`
takes the terms `a(2k)` and `a(2k + 1)` for `k ≤ n`, which together are
its terms up to `2n + 1`, so the paired partial sums are the
series' partial sums at the strictly rising indices `2n + 1` — a
subsequence, which keeps the limit. An alternating series whose terms
are nonnegative and do not increase has its sum between 0 and its first
term: taken two terms at a time it adds up the differences
`a(2n) − a(2n + 1)`, each nonnegative, so its sum is at least the first
of them; and dropping the first term and changing sign leaves another
such series, the alternating series of the tail `a(n + 1)`, which sums
to `a(0) − s`.

**Completeness (cauchy.go).** The Cauchy criterion is the sequences
chapter's, read at the partial sums: a tail `Σ_{k∈p + 1 .. q} a(k)` is
the difference of the partial sums to `q` and to `p`, so a series whose
tails become uniformly small has Cauchy partial sums, and conversely.
The sum the criterion finds is named in the proof — the upper limit of
the partial sums — and the statement keeps only its existence. Read at
a one-term tail, `Σ_{k∈n .. n} a(k) = a(n)`, the criterion says the
terms of a convergent series tend to 0.

**The geometric series (geometric.go).** Multiplying `Σ_{k∈0 .. n} xᵏ`
by `1 − x` turns every term into a difference of consecutive powers,
and the sum telescopes to `1 − xⁿ⁺¹`; stated multiplied out, the
formula needs no side condition. Below 1 in size, `x` leaves `1 − x`
positive, so the formula solves for the partial sums as
`(1 − x)⁻¹·(1 − xⁿ⁺¹)`; the powers tend to 0, so the series sums to
`(1 − x)⁻¹`. Every bound B is reached by a partial sum of
$\sum_{m \ge 1} t^{m^2}$ at some t with 0 ≤ t < 1.

**Comparison (comparison.go).** A series whose terms are, from some
index on, no larger in size than those of a convergent series
converges: past that index a tail of the smaller series is at most the
same tail of the larger, so the Cauchy criterion, read forward for the
larger series and backward for the smaller, gives the sum. A series
dominated termwise in size sums to no more in size: each term `a(n)`
lies between `−b(n)` and `b(n)`, `−b` sums to `−t`, and the order of sums
read against `b` and against `−b` puts `s` between `−t` and `t`. And the
ratio test is a comparison with the geometric series: raising the
ratio to `r = max(c, 1/2)` puts it strictly between 0 and 1, the terms
past `N` then decay at least geometrically, `|a(N + k)| ≤ |a(N)|·rᵏ` by
induction on `k`, and so past `N` they are dominated by `|a(N)|/rᴺ` times
the geometric series of `r`, which has a sum.

**The Cauchy product (product.go).** The Cauchy product of `a` and `b`
is the series `λn. Σ_{k∈0 .. n} a(k)·b(n − k)`. Write `A(N)` and `B(N)`
for the partial sums of `a` and `b` up to `N`. The product's partial sum
up to `N` adds up `a(i)·b(j)` over the triangle `i + j ≤ N`, and summed
by rows (`iterate/real/real_sum`'s `Antidiagonal`) it is
`Σ_{i∈0 .. N} a(i)·B(N − i)`; the square `i, j ≤ N` sums to `A(N)·B(N)`.
For nonnegative terms the triangle lies inside the square `i, j ≤ N`
and, once `M + M ≤ N`, contains the square `i, j ≤ M`; the square sums
tend to `s·t`, so the triangle's sums do too. For two absolutely
convergent series, the gap between the square and the triangle, summed
by rows, is `Σ_{i∈0 .. N} a(i)·(B(N) − B(N − i))`; each stretch
`B(N) − B(N − i)` of `b` is at most, in size, the same stretch of the
partial sums of `|b|`, so the gap is at most, in size, the gap for `|a|`
and `|b|` — which the nonnegative case sends to 0. The triangle's sums
lie within a vanishing distance of the square sums, which tend to
`s·t`, so they tend to `s·t` as well.

## Members

| entry | statement |
|---|---|
| `RealSumsDef` | `real_sums(a, s) ⇔ (λn. Σ_{k∈0 .. n} a(k)) ⟶ s` |
| `SumsUnique` | `real_sums(a, s) ∧ real_sums(a, t) ⇒ s = t` |
| `SumsAdd` | `real_sums(a, s) ∧ real_sums(b, t) ⇒ real_sums(λn. a(n) + b(n), s + t)` |
| `SumsScale` | `real_sums(a, s) ⇒ real_sums(λn. c · a(n), c · s)` |
| `SumsSub` | `real_sums(a, s) ∧ real_sums(b, t) ⇒ real_sums(λn. a(n) − b(n), s − t)` |
| `SumsZero` | `real_sums(λn. &0, &0)` |
| `SumsLessEq` | `(∀n. a(n) ≤ b(n)) ∧ real_sums(a, s) ∧ real_sums(b, t) ⇒ s ≤ t` |
| `SumsPartialLessEq` | `(∀n. &0 ≤ a(n)) ∧ real_sums(a, s) ⇒ ∀n. Σ_{k∈0 .. n} a(k) ≤ s` |
| `SumsShift` | `real_sums(a, s) ⇔ real_sums(λn. a(n + 1), s − a(0))` |
| `SumsOffset` | `real_sums(a, s) ⇔ real_sums(λn. a(n + m + 1), s − Σ_{k∈0 .. m} a(k))` |
| `SumsPair` | `real_sums(a, s) ⇒ real_sums(λn. a(2·n) + a(2·n + 1), s)` |
| `AlternatingBound` | `(∀n. &0 ≤ a(n) ∧ a(n + 1) ≤ a(n)) ∧ real_sums(λn. real_pow(−&1, n) · a(n), s) ⇒ &0 ≤ s ∧ s ≤ a(0)` |
| `SumsCauchy` | `(∃s. real_sums(a, s)) ⇔ ∀ε. &0 < ε ⇒ ∃N. ∀m n. N ≤ m ⇒ real_abs(Σ_{k∈m .. n} a(k)) < ε` |
| `SumsTermsTendToZero` | `real_sums(a, s) ⇒ a ⟶ &0` |
| `SumsTermsBounded` | `(∃s. real_sums(a, s)) ⇒ ∃B. ∀n. real_abs(a(n)) ≤ B` |
| `GeometricPartialSum` | `(&1 − x) · Σ_{k∈0 .. n} xᵏ = &1 − xⁿ⁺¹` |
| `Geometric` | `real_abs(x) < &1 ⇒ real_sums(λn. xⁿ, real_inv(&1 − x))` |
| `SquarePowersUnbounded` | `∃t M. &0 ≤ t ∧ t < &1 ∧ B ≤ Σ_{m∈1 .. M} real_pow(t, m · m)` |
| `Comparison` | `(∀n. N ≤ n ⇒ real_abs(a(n)) ≤ b(n)) ∧ real_sums(b, t) ⇒ ∃s. real_sums(a, s)` |
| `ComparisonBound` | `(∀n. real_abs(a(n)) ≤ b(n)) ∧ real_sums(a, s) ∧ real_sums(b, t) ⇒ real_abs(s) ≤ t` |
| `Ratio` | `c < &1 ∧ (∀n. N ≤ n ⇒ real_abs(a(n + 1)) ≤ c · real_abs(a(n))) ⇒ ∃s. real_sums(a, s)` |
| `CauchyProductNonneg` | `(∀n. &0 ≤ a(n) ∧ &0 ≤ b(n)) ∧ real_sums(a, s) ∧ real_sums(b, t) ⇒ real_sums(λn. Σ_{k∈0 .. n} a(k) · b(n − k), s · t)` |
| `CauchyProduct` | `real_sums(a, s) ∧ real_sums(b, t) ∧ real_sums(λn. real_abs(a(n)), u) ∧ real_sums(λn. real_abs(b(n)), v) ⇒ real_sums(λn. Σ_{k∈0 .. n} a(k) · b(n − k), s · t)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
