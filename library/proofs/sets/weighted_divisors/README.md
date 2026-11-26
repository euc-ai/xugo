# weighted_divisors — counting effective divisors by degree

A weight w assigns a natural number to each point of a set S. An effective divisor is a finitely supported function D : A → num that vanishes off S and at the points of weight 0; its degree is Σ w(x)·D(x). When only finitely many points of S weigh at most n, the effective divisors of degree n are finitely many, their number is the n-th coefficient of the Euler product of the geometric series $\sum_k z^{k \cdot w(x)}$ over those points, and it satisfies the logarithmic recurrence $n \cdot c(n) = \sum_{0<m \le n} a(m) \cdot c(n-m)$, where a(m) sums the weights dividing m. No positivity of w is asked: a point of weight 0 carries no divisor and its geometric series is 1.

The chapter's abbreviations (family.go) name the convolution of sequences of naturals «conv», the step «step» that multiplies by a point's geometric series and the series «unit» = 1, the level «lowWeight» of the weight at n, the divisors «divisors» of degree n, and the degrees «oneToN» from 1 to n.

## Definitions

| Member | Statement |
|---|---|
| `WeightedEffectiveDef` | `weighted_effective(S, w, D)`: D has finite support, and is nonzero only at points of S of positive weight |
| `WeightedDegreeDef` | `weighted_degree(w, D)` = Σ w(x)·D(x) over the support of D |
| `WeightedCountDef` | `weighted_count(S, w, n)` = the number of effective divisors of degree n |
| `WeightedMultiplesDef` | `weighted_multiples(S, w, m)` = Σ w(x) over the points of S whose weight divides m, and 0 at m = 0 |

## Support and degree

A nonzero value of an effective divisor sits at a point of S whose weight is at most the degree, and is itself at most the degree; so the divisors of degree n are maps from the level at n into {0, …, n}, finitely many. The degree splits off one point's contribution, may be summed over any set holding the support, and grows by k·w(x) when k is added at x.

| Member | Statement |
|---|---|
| `WeightedSupportBound` | a point where an effective divisor does not vanish is a point of S of positive weight, and both its weight and the value there are at most the degree |
| `WeightedDivisorsFinite` | when only finitely many points of S weigh at most n, only finitely many effective divisors have degree n |
| `WeightedCountZero` | the zero divisor is the one effective divisor of degree 0 |
| `WeightedDegreeSplit` | the degree of a finitely supported D is w(x)·D(x) plus the degree of D cleared at x |
| `WeightedDegreeOver` | the degree of D may be summed over any set holding its support |
| `WeightedRaise` | adding k at a point x of S of positive weight keeps a divisor effective and raises its degree by k·w(x) |

## The Euler product

Over a finite set T the counting sequence is a fold: adjoining a fresh point x multiplies it by the geometric series of w(x), because the divisors over T ∪ {x} of degree m that spend i = w(x)·D(x) at x are the divisors over T of degree m − i. Only the points of weight at most n can occur in degree n, so the count over S is the fold over that level. A fold over a set asks its steps to commute, and two points' steps do because «conv» is left-commutative, which the polynomial chapter proves in ℕ's finite sums, both sides summing one triangle of products in its two orders (`polynomial.NatPolynomialMulLeftComm`).

| Member | Statement |
|---|---|
| `WeightedCountFibre` | the effective divisors over T ∪ {x} of degree m spending i at x number weighted_count(T, w, m − i), when w(x) divides i |
| `WeightedCountInsert` | adjoining a fresh point multiplies the counting sequence by that point's geometric series |
| `WeightedCountFold` | over a finite set the counting sequence is the folded product of the points' geometric series |
| `WeightedCountProduct` | the count in degree n is the n-th coefficient of the Euler product over the points of weight at most n |

## The logarithmic recurrence

A divisor D holds k copies of x when k ≤ D(x); k copies weigh k·w(x), the amount D spends at x when k = D(x). Count a divisor of degree n together with a marked copy of one of its points, weighted by that point's weight: by divisor the total is n·c(n); by the point x and the number k of the marked copy it is Σ w(x)·c(n − k·w(x)), since the divisors with at least k copies of x are those of degree n − k·w(x) with k copies added; grouping by m = k·w(x) gives $\sum_{0<m \le n} a(m) \cdot c(n-m)$.

| Member | Statement |
|---|---|
| `WeightedCountAtLeast` | the effective divisors of degree n with at least k copies of x number weighted_count(S, w, n − k·w(x)) |
| `WeightedMultiplicitySum` | Σ D(x) over the effective divisors of degree n is Σ c(n − m) over the multiples 0 < m ≤ n of w(x) |
| `WeightedCountRecurrence` | n·c(n) = Σ_{0<m≤n} weighted_multiples(S, w, m)·c(n − m) |

## The theorem

| Member | Statement |
|---|---|
| `WeightedEulerProduct` | when only finitely many points of S weigh at most n: the effective divisors of degree n are finitely many, counted by the Euler product, and bound by the logarithmic recurrence |
