# real_sum — Σ

The ℝ-valued fold: `real_sum s f` adds up a real-valued function over an
index set of any type. It is total — a sum is defined whatever the set
and whatever the summand — and where the summand is nonzero at
infinitely many points the answer is zero by convention. That
convention is not a corner case to be stepped around; several of the
chapter's laws hold *because* of it, and one of them says so directly.

This chapter is what real addition contributes to the fold mechanism of
`iterate/monoidal`. The two facts it rests on — real addition
folds, and its neutral element is `&0` — are the ring chapter's
(`real_ring.MonoidalAdd`, `real_ring.NeutralAdd`). The chapter keeps the
real-valued interfaces its consumers use: recursion at `∅` and `insert`,
splitting over unions, deleting a point, gathering fibres, totalled over
the image or over any set covering it (`Fibres`, `Regroup`), reindexing
by a map one to one on the index set (`Image`), and exchanging two
indices. Other fold laws are read directly from `monoidal` at real
addition.

What is proper to Σ is the interplay with the rest of ℝ's algebra.
Linearity: sums of sums, scalars moving through from either side, and
two finite sums multiplied out into one sum over the pairs of their
indices (`ProductOfSums`).
Vanishing: a summand that is zero everywhere sums to zero, a sum hears
only the points where its summand is not zero (restricting the index
set to them changes nothing), and a sum heard at infinitely many
points is zero as well. Subtraction and
negation flowing through the summand. And the constant sum, which
counts the index set — $\sum_{x \in s} c = \lvert s \rvert \cdot c$, whose one-value case reads
the cardinality itself as a sum; over the n numbers below n it is n·c (`ConstBelow`). The constant law transports
`nat_sum.SumOfOnes` through `RealOfNatSum` and scales the resulting
sum of ones. Summed over a finite set, the indicator of a predicate
counts the points where it holds (`IndicatorSum`).

The interval calculus is the fourth movement: sums over the segment
`m .. n`, the form indexed series are actually written in. Here every
law the chapter proves acquires a second, interval reading — the
recursion peels a term at either end, the index shifts, the segment
splits at a midpoint or by the parity of its index — and the
finiteness hypotheses discharge once and for all, because a segment is
finite. The order laws read there too: a
summand nowhere above another sums to no more over a segment, a sum
whose summand is dominated in size by another is at most that other's
sum in size, and a segment extended past its upper bound by nonnegative
terms sums to no less. This is the vocabulary the polynomial chapter
(`real/real_polynomial`) consumes wholesale: a polynomial IS
$\sum_{i \in 0..m} c_i \cdot x^i$.

The fifth movement is order and estimates: a summand nowhere above
another sums to no more, positivity, pricing a sum by a per-term
bound and reading the price back — a bound on a sum of nonnegative
terms bounds each term, so a vanishing one vanishes termwise —
comparing sums over comparable index sets, and the triangle
inequality — the sum's size within the sum of sizes. Nonnegativity
is `monoidal.Closed` read at the property `0 ≤ x`: zero has the
property, and addition preserves it.

Two closing movements complete the chapter. The series tools: an indexed
series is as often cancelled as summed, and when the summand is the
difference of consecutive values of one function only the two ends
survive — the telescope, taken as the primitive and proved by induction
on the upper bound; the downward telescope is its negation, and
summation by parts is the telescope of f·g read through the discrete
Leibniz rule and Σ's linearity. Abel's inequality bounds
$\sum_{k \in 1..N} a(k) \cdot b(k)$, for b nonincreasing on 1 .. N + 1 with
b(N + 1) ≥ 0, by B·b(1) when every partial sum of a up to N is at most B
in size
(`AbelInequality`). And regrouping: a sum over the triangle
i + j ≤ N taken along its antidiagonals is the same sum taken along its
rows — the regrouping a Cauchy product rests on, by one more induction
on the upper bound; a double sum restricted by a relation, exchanged; and a relation between two finite sets counted from both
sides — the double counting that says a k-regular relation into t has
k·|t| pairs.

## Sums over the subsets of a set

The subsets of a set are an index set of their own: the points of a cube, a subset
being the coordinates that are set. A function that changes sign when a point is toggled sums
to zero over them, a sum over the subsets of a disjoint union is a double sum over the subsets
of its parts, and a sum over sets of pairs with one second coordinate is a sum over subsets.

| Member | Statement |
|---|---|
| `SubsetsSumToggleOdd` | a function on the subsets of S that changes sign when a point of S is toggled sums to 0 — card |
| `SubsetsSumDisjointUnion` | the sum over the subsets of a disjoint union J ∪ K is the double sum over the subsets Y of J and Z of K, read at Y ∪ Z — card |
| `SubsetsSumCrossSingleton` | a sum over the sets of pairs of J × {b} is the sum over the subsets of J, each set read through its slice at b |

## A bound on naturals

`NatSumBound` bounds a finite sum of naturals, each at most c, by card(s) · c
in ℝ. `RealOfNatSum` carries the natural sum into ℝ, where `Bound`
applies. Counting a set by its fibres over a finite set is `nat_sum`'s
(`nat_sum.CardFibresBound`).

## The files

`fold.go` is the fold read at ℝ — the bridge, the module
chapter's sum at real addition among it (`RealModuleSum`), the
mechanism's laws instantiated at real addition, and the laws about
changing the index set, the regrouping laws among them. `linearity.go`
is ℝ's own algebra meeting the sum: linearity, vanishing, and the
constant sum. `interval.go` is the interval calculus and, under a
second banner, the series tools. `order.go` is order and estimates.
`nat_bound.go` holds the bound on naturals. `subsets.go` holds the
sums over the subsets of a set.
