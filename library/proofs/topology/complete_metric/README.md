# complete_metric — sequences, completeness and compactness in a metric space

A sequence of points of M converges to a point l of M when every
positive distance about l holds all its terms past some index:
`metric_converges_to(M, d, x, l)`. It is Cauchy when its terms past
some index lie within any positive distance of each other:
`metric_cauchy(M, d, x)`. The space is complete when every Cauchy
sequence converges, `metric_complete(M, d)`, and a subset is totally
bounded when, for every positive distance, finitely many of its points
come within it of all its points, `totally_bounded(M, d, s)`. These are
real_sequences' ε-N sentences with d(x, y) for |x − y|, and the
chapter's first theorems are that chapter's, read at a general
distance.

Convergence, Cauchy-ness and total boundedness leave M and d implicit
under a law over `metric_space(M, d)`, as `ball` does. Completeness
spells both, since it is asked of subsets with the same distance:
`metric_complete(s, d)` is the completeness of s as a space.

## The definitions

| member | statement |
|---|---|
| `MetricConvergesToDef` | `metric_converges_to(M, d, x, l) ⇔ l ∈ M ∧ (∀n. x(n) ∈ M) ∧ ∀ε. &0 < ε ⇒ ∃N. ∀n. N ≤ n ⇒ d(x(n), l) < ε` |
| `MetricCauchyDef` | `metric_cauchy(M, d, x) ⇔ (∀n. x(n) ∈ M) ∧ ∀ε. &0 < ε ⇒ ∃N. ∀m n. N ≤ m ∧ N ≤ n ⇒ d(x(m), x(n)) < ε` |
| `MetricCompleteDef` | `metric_complete(M, d) ⇔ ∀x. metric_cauchy(M, d, x) ⇒ ∃l. metric_converges_to(M, d, x, l)` |
| `TotallyBoundedDef` | `totally_bounded(M, d, s) ⇔ s ⊆ M ∧ ∀ε. &0 < ε ⇒ ∃k. finite(k) ∧ k ⊆ s ∧ ∀y. y ∈ s ⇒ ∃x. x ∈ k ∧ d(x, y) < ε` |

## Sequences (sequences.go)

A limit is unique, a convergent sequence is Cauchy, a subsequence
converges where the sequence does, and a Cauchy sequence converges
where one of its subsequences does. A point of M every ball about
which meets a set is the limit of a sequence of points of the set — one
chosen in each ball of radius $\frac{1}{n+1}$ — which is how a closed set is
shown to be one that keeps its limits: the closed sets of the metric
topology are the sets that keep the limits of their convergent
sequences; through that, a closed subset of a complete space is
complete, and a complete subset of any metric space is closed in it.

| member | statement |
|---|---|
| `LimitUnique` | `metric_space(M, d) ∧ metric_converges_to(M, d, x, l) ∧ metric_converges_to(M, d, x, m) ⇒ l = m` |
| `ConvergentImpCauchy` | `metric_space(M, d) ∧ metric_converges_to(M, d, x, l) ⇒ metric_cauchy(M, d, x)` |
| `LimitSubsequence` | `(∀j. σ(j) < σ(j + 1)) ∧ metric_converges_to(M, d, x, l) ⇒ metric_converges_to(M, d, x ∘ σ, l)` |
| `CauchySubsequenceConverges` | `metric_space(M, d) ∧ metric_cauchy(M, d, x) ∧ (∀j. σ(j) < σ(j + 1)) ∧ metric_converges_to(M, d, x ∘ σ, l) ⇒ metric_converges_to(M, d, x, l)` |
| `ApproachingSequence` | `metric_space(M, d) ∧ l ∈ M ∧ (∀r. &0 < r ⇒ ball(l, r) ∩ s ≠ ∅) ⇒ ∃x. (∀n. x(n) ∈ s) ∧ metric_converges_to(x, l)` |
| `ClosedIffSequential` | `metric_space(M, d) ⇒ (closed_in(metric_topology(M, d), c) ⇔ c ⊆ M ∧ ∀x l. (∀n. x(n) ∈ c) ∧ metric_converges_to(M, d, x, l) ⇒ l ∈ c)` |
| `ClosedComplete` | `metric_space(M, d) ∧ metric_complete(M, d) ∧ closed_in(metric_topology(M, d), s) ⇒ metric_complete(s, d)` |
| `CompleteClosed` | `metric_space(M, d) ∧ s ⊆ M ∧ metric_complete(s, d) ⇒ closed_in(metric_topology(M, d), s)` |

## What completeness gives (complete.go)

Nested non-empty closed sets whose diameters shrink to nothing have a
common point: a point of each forms a Cauchy sequence, and its limit
lies in every one of them. Read on balls: closed balls about points of
M, each inside the one before and with radii tending to zero, have a
common point. Baire's theorem follows: countably many
dense open sets meet in a dense set: a non-empty open set and a dense
open set meet in a set holding a closed ball of any small radius, so
inside any open set a shrinking chain of closed balls can be threaded
through them one at a time, the next ball chosen once inside each and
the choices iterated by recursion. Banach's fixed point theorem is the
third: the iterates of a contraction from any point form a Cauchy
sequence, by the geometric sum of their steps — a sequence whose
successive distances are at most c·qⁿ with 0 ≤ q < 1 is Cauchy — and
its limit is the one fixed point.

| member | statement |
|---|---|
| `CantorIntersection` | `metric_space(M, d) ∧ metric_complete(M, d) ∧ (∀n. c(n) closed, non-empty, c(n + 1) ⊆ c(n)) ∧ diameters → 0 ⇒ ∃l. ∀n. l ∈ c(n)` |
| `NestedClosedBallsMeet` | `metric_space(M, d) ∧ metric_complete(M, d) ∧ (∀n. x(n) ∈ M ∧ &0 ≤ r(n)) ∧ (∀n. closed_ball(x(n + 1), r(n + 1)) ⊆ closed_ball(x(n), r(n))) ∧ (∀ε. &0 < ε ⇒ ∃n. r(n) < ε) ⇒ ∃l. ∀n. l ∈ closed_ball(x(n), r(n))` |
| `ClosedBallInDenseMeet` | `metric_space(M, d) ∧ u ∈ metric_topology ∧ u ≠ ∅ ∧ v ∈ metric_topology ∧ closure(metric_topology, v) = M ∧ &0 < ε ⇒ ∃c r. c ∈ M ∧ &0 < r ∧ r < ε ∧ closed_ball(c, r) ⊆ u ∩ v` |
| `BaireCategory` | `metric_space(M, d) ∧ metric_complete(M, d) ∧ (∀n. g(n) open and dense) ⇒ closure(metric_topology(M, d), ⋂image(g, 𝕌)) = M` |
| `GeometricStepsCauchy` | `(∀n. x(n) ∈ M) ∧ &0 ≤ q ∧ q < &1 ∧ (∀n. d(x(n + 1), x(n)) ≤ c * q ^ n) ⇒ metric_cauchy(x)` |
| `BanachFixedPoint` | `metric_space(M, d) ∧ metric_complete(M, d) ∧ M ≠ ∅ ∧ f maps M into M ∧ k < &1 ∧ d(f(x), f(y)) ≤ k * d(x, y) on M ⇒ f has exactly one fixed point in M` |

## Compact metric spaces (compact.go)

In a metric space compactness is sequential compactness: every
sequence of points of a compact set has a subsequence converging to
one of them, and conversely. Total boundedness is the existence of
Cauchy subsequences, so a set is compact exactly when it is complete
and totally bounded. A compact set's sequences have cluster points in
it, and a cluster point is the limit of a subsequence; a set whose
sequences have subsequences converging in it is totally bounded and its
open covers have Lebesgue numbers, so it is compact. Total boundedness
gives Cauchy subsequences by refining the indices level by level —
finitely many balls of radius $\frac{1}{n+1}$ cover the set, one holds
infinitely many of the remaining terms — and a strictly increasing
selection threads the levels; conversely a set with no finite ε-net
holds a sequence of points ε apart. An open cover of a compact space has
a Lebesgue number — a positive radius every ball of which lies in one
member — and a continuous map out of a compact space is therefore
uniformly continuous.

| member | statement |
|---|---|
| `IncreasingSelection` | `(∀j. infinite(J(j))) ⇒ ∃σ. (∀j. σ(j) < σ(j + 1)) ∧ (∀j. σ(j) ∈ J(j))` |
| `ClusterPointSubsequence` | `metric_space(M, d) ∧ (∀n. x(n) ∈ M) ∧ l ∈ M ∧ (∀r. &0 < r ⇒ ∀N. ∃n. N ≤ n ∧ d(x(n), l) < r) ⇒ ∃σ. (∀j. σ(j) < σ(j + 1)) ∧ metric_converges_to(M, d, x ∘ σ, l)` |
| `TotallyBoundedRefine` | `totally_bounded(M, d, s) ∧ (∀n. x(n) ∈ s) ∧ infinite(I) ∧ &0 < r ⇒ ∃J. J ⊆ I ∧ infinite(J) ∧ (∃c. c ∈ s ∧ ∀n. n ∈ J ⇒ d(c, x(n)) < r)` |
| `SeparatedSequence` | `¬(∃k. finite(k) ∧ k ⊆ s ∧ ∀y. y ∈ s ⇒ ∃x. x ∈ k ∧ d(x, y) < ε) ⇒ ∃x. (∀n. x(n) ∈ s) ∧ (∀m n. m < n ⇒ ε ≤ d(x(m), x(n)))` |
| `CompactImpSequential` | `metric_space(M, d) ∧ compact_in(metric_topology(M, d), k) ⇒ k ⊆ M ∧ every sequence of k has a subsequence converging in k` |
| `SequentialLebesgue` | `metric_space(M, d) ∧ k ⊆ M ∧ every sequence of k has a subsequence converging in k ∧ c ⊆ metric_topology(M, d) ∧ k ⊆ ⋃c ⇒ ∃δ. &0 < δ ∧ ∀x. x ∈ k ⇒ ∃u. u ∈ c ∧ ball(M, d, x, δ) ⊆ u` |
| `SequentialTotallyBounded` | `metric_space(M, d) ∧ k ⊆ M ∧ every sequence of k has a subsequence converging in k ⇒ totally_bounded(M, d, k)` |
| `SequentialImpCompact` | `metric_space(M, d) ∧ k ⊆ M ∧ every sequence of k has a subsequence converging in k ⇒ compact_in(metric_topology(M, d), k)` |
| `CompactSequential` | `metric_space(M, d) ⇒ (compact_in(metric_topology(M, d), k) ⇔ k ⊆ M ∧ every sequence of k has a subsequence converging in k)` |
| `TotallyBoundedSequential` | `metric_space(M, d) ⇒ (totally_bounded(M, d, s) ⇔ s ⊆ M ∧ every sequence of s has a Cauchy subsequence)` |
| `CompactCompleteTotallyBounded` | `metric_space(M, d) ⇒ (compact_in(metric_topology(M, d), k) ⇔ metric_complete(k, d) ∧ totally_bounded(M, d, k))` |
| `LebesgueNumber` | `metric_space(M, d) ∧ compact_in(metric_topology(M, d), M) ∧ c an open cover of M ⇒ ∃δ. &0 < δ ∧ ∀x. x ∈ M ⇒ ∃u. u ∈ c ∧ ball(M, d, x, δ) ⊆ u` |
| `HeineCantor` | `metric_space(M, d) ∧ metric_space(N, e) ∧ compact_in(metric_topology(M, d), M) ∧ continuous_map(metric_topology(M, d), metric_topology(N, e), f) ⇒ uniformly_continuous_map(M, d, N, e, f)` |

## Closure, continuity and boundedness by sequences (sequences.go, compact.go, complete.go)

The closure of a set is the set of limits of its sequences, and a map
between metric spaces is continuous exactly when it carries convergent
sequences to convergent sequences. The terms of a Cauchy sequence form
a bounded set, their distances from the first term forming a Cauchy
sequence of reals, and a totally bounded set is bounded. The product
of two complete metric spaces is complete, a sequence of pairs being
Cauchy or convergent as its two projections are; so is a countable
product of complete spaces under metric_space's countable product
distance `countable_product_metric(J, d, h)`, the distance controlling
each coordinate uniformly and finitely many coordinates controlling it.

| member | statement |
|---|---|
| `ClosureIffSequential` | `s ⊆ M ⇒ ∀l. l ∈ closure(metric_topology, s) ⇔ ∃x. (∀n. x(n) ∈ s) ∧ metric_converges_to(x, l)` |
| `ContinuousIffSequential` | `metric_space(M, d) ∧ metric_space(N, e) ⇒ (continuous_map(metric_topology, metric_topology(N, e), f) ⇔ (∀x. x ∈ M ⇒ f(x) ∈ N) ∧ (∀x. ∀l. metric_converges_to(x, l) ⇒ metric_converges_to(N, e, f ∘ x, f(l))))` |
| `CauchyBounded` | `metric_cauchy(x) ⇒ metric_bounded(image(x, 𝕌))` |
| `TotallyBoundedImpBounded` | `totally_bounded(s) ⇒ metric_bounded(s)` |
| `ProductComplete` | `metric_complete(M, d) ∧ metric_complete(N, e) ⇒ metric_complete(set_cross(M, N), product_metric(d, e))` |
| `CountableProductComplete` | `J ⊆ image(h, 𝕌) ∧ (∀i. i ∈ J ⇒ metric_complete(X(i), d(i))) ⇒ metric_complete(indexed_functions(J, z, X), countable_product_metric(J, d, h))` |

## Uniform continuity (uniform.go)

A map between metric spaces is uniformly continuous when one δ serves
every point for each ε, `uniformly_continuous_map(M, d, N, e, f)`, and
Lipschitz when it stretches no distance by more than a fixed factor,
`lipschitz_map(M, d, N, e, f)`. Both are structures over their five
components, and a member assuming one is its law, the components bound
once; their axioms are the two clauses of each definition. A Lipschitz
map is uniformly continuous and a uniformly continuous map continuous.
Uniformly continuous maps compose and carry Cauchy sequences to Cauchy
sequences — which is what lets one defined on a dense subset extend to
the whole space when the target is complete: two sequences of the subset
converging to one point have images converging to one limit, the
extension's value there. A continuous map out of a compact metric space
is uniformly continuous (`HeineCantor`, above).

| member | statement |
|---|---|
| `UniformlyContinuousMap` | `uniformly_continuous_map(M, d, N, e, f) ⇔ (∀x. x ∈ M ⇒ f(x) ∈ N) ∧ (∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ (∀x y. x ∈ M ∧ y ∈ M ∧ d(x, y) < δ ⇒ e(f(x), f(y)) < ε))` |
| `LipschitzMap` | `lipschitz_map(M, d, N, e, f) ⇔ (∀x. x ∈ M ⇒ f(x) ∈ N) ∧ (∃k. ∀x y. x ∈ M ∧ y ∈ M ⇒ e(f(x), f(y)) ≤ k * d(x, y))` |
| `UniformlyContinuousMapsInto` | `uniformly_continuous_map(M, d, N, e, f) ⇒ ∀x. x ∈ M ⇒ f(x) ∈ N` |
| `UniformlyContinuousDelta` | `uniformly_continuous_map(M, d, N, e, f) ⇒ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x y. x ∈ M ∧ y ∈ M ∧ d(x, y) < δ ⇒ e(f(x), f(y)) < ε` |
| `LipschitzMapsInto` | `lipschitz_map(M, d, N, e, f) ⇒ ∀x. x ∈ M ⇒ f(x) ∈ N` |
| `LipschitzBound` | `lipschitz_map(M, d, N, e, f) ⇒ ∃k. ∀x y. x ∈ M ∧ y ∈ M ⇒ e(f(x), f(y)) ≤ k * d(x, y)` |
| `LipschitzImpUniformlyContinuous` | `metric_space(M, d) ∧ lipschitz_map(M, d, N, e, f) ⇒ uniformly_continuous_map(M, d, N, e, f)` |
| `UniformlyContinuousImpContinuous` | `metric_space(N, e) ∧ uniformly_continuous_map(M, d, N, e, f) ⇒ continuous_map(metric_topology(M, d), metric_topology(N, e), f)` |
| `UniformlyContinuousCompose` | `uniformly_continuous_map(M, d, N, e, f) ∧ uniformly_continuous_map(N, e, L, h, g) ⇒ uniformly_continuous_map(M, d, L, h, g ∘ f)` |
| `UniformlyContinuousCauchy` | `uniformly_continuous_map(M, d, N, e, f) ∧ metric_cauchy(M, d, x) ⇒ metric_cauchy(N, e, f ∘ x)` |
| `UniformlyContinuousSameLimit` | `uniformly_continuous_map(s, d, N, e, f) ∧ (∀n. x(n) ∈ s ∧ y(n) ∈ s) ∧ metric_converges_to(M, d, x, p) ∧ metric_converges_to(M, d, y, p) ∧ metric_converges_to(N, e, f ∘ x, l) ∧ metric_converges_to(N, e, f ∘ y, m) ⇒ l = m` |
| `UniformContinuousExtension` | `metric_space(M, d) ∧ metric_space(N, e) ∧ metric_complete(N, e) ∧ s ⊆ M ∧ closure(metric_topology, s) = M ∧ uniformly_continuous_map(s, d, N, e, f) ⇒ ∃g. uniformly_continuous_map(M, d, N, e, g) ∧ (∀x. x ∈ s ⇒ g(x) = f(x))` |

## Instances

The line with |x − y| is complete (`real_topology.RealComplete`), the
instance theorem of its own chapter.

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
