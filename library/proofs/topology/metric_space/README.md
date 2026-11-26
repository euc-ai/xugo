# metric_space — a distance, and the topology it determines

A metric space is a set M of points with a distance d between any two
of them: `metric_space(M, d)`. The distance vanishes exactly between a
point and itself, reads the same both ways, and is never longer than a
detour through a third point. Those are the three axioms; that a
distance is never negative follows from them.

The carrier is a component of the structure, beside the distance. A
topology's points are the union of its open sets, so the topology
chapters mint no carrier; a distance determines no such set, and the
chapter that needs this most is ℝⁿ, whose n-vectors are a subset of all
sequences and whose distance, read on every sequence, cannot tell apart
two sequences that agree below n.

The distance determines a family of open sets: a subset of M is open
when each of its points has a ball about it inside the set,
`metric_topology(M, d)`. The notions stated over one space — the balls
and the open sets — read M and d as their first two arguments and leave
them implicit under a law, `ball(x, r)` for `ball(M, d, x, r)`. A member
that uses no axiom is a plain theorem and spells them. The topology the
chapter reads the family through is `topology/topological_space`'s
(`is_topology`, `closed_in`, `hausdorff`, `subtopology`), and continuity is
`topology/continuous`'s `continuous_map`.

## The structure and its axioms

| member | statement |
|---|---|
| `MetricSpace` | `metric_space(M, d) ⇔ (∀x y. x ∈ M ∧ y ∈ M ⇒ (d(x, y) = &0 ⇔ x = y)) ∧ (∀x y. x ∈ M ∧ y ∈ M ⇒ d(x, y) = d(y, x)) ∧ (∀x y z. x ∈ M ∧ y ∈ M ∧ z ∈ M ⇒ d(x, z) ≤ d(x, y) + d(y, z))` |
| `DistZeroIff` | `x ∈ M ∧ y ∈ M ⇒ (d(x, y) = &0 ⇔ x = y)` |
| `DistSym` | `x ∈ M ∧ y ∈ M ⇒ d(x, y) = d(y, x)` |
| `DistTriangle` | `x ∈ M ∧ y ∈ M ∧ z ∈ M ⇒ d(x, z) ≤ d(x, y) + d(y, z)` |

## Balls and open sets (definitions.go)

| constant | reading |
|---|---|
| `ball(M, d, x, r)` | `{y \| y ∈ M ∧ d(x, y) < r}` |
| `closed_ball(M, d, x, r)` | `{y \| y ∈ M ∧ d(x, y) ≤ r}` |
| `metric_topology(M, d)` | `{u \| u ⊆ M ∧ ∀x. x ∈ u ⇒ ∃r. &0 < r ∧ ball(M, d, x, r) ⊆ u}` |

## The distance and the balls

A distance is never negative: the way out and back is a detour from a
point to itself, so twice the distance is at least the distance of a
point from itself, which is zero. A point of M lies in every ball about
it of positive radius, and in every closed ball about it of radius at
least zero. The balls about one point are nested by their radii, a ball
lies in the closed ball of the same radius, and a closed ball lies in
the ball of any larger radius; these three facts ask nothing of the
distance.

| member | statement |
|---|---|
| `DistSelf` | `x ∈ M ⇒ d(x, x) = &0` |
| `DistNonneg` | `x ∈ M ∧ y ∈ M ⇒ &0 ≤ d(x, y)` |
| `CentreInBall` | `x ∈ M ∧ &0 < r ⇒ x ∈ ball(x, r)` |
| `BallConcentric` | `r ≤ s ⇒ ball(M, d, x, r) ⊆ ball(M, d, x, s)` |
| `CentreInClosedBall` | `x ∈ M ∧ &0 ≤ r ⇒ x ∈ closed_ball(x, r)` |
| `BallSubsetClosedBall` | `ball(M, d, x, r) ⊆ closed_ball(M, d, x, r)` |
| `ClosedBallSubsetBall` | `r < s ⇒ closed_ball(M, d, x, r) ⊆ ball(M, d, x, s)` |

## The topology (topology.go)

Most of what makes the open sets a topology asks nothing of the
distance. Two open sets meet in an open set because the ball of the
smaller of two radii lies in both balls; a union of open sets is open
because a point of the union keeps the ball its own member gives it;
the space of the topology is M because M itself is open, a ball being
drawn from the points of M. Closedness is openness of the complement in
M, and a ball lies in that complement exactly when it misses the set.
The triangle inequality enters with the balls: a point y of the ball of
radius r about x keeps the ball of radius r − d(x, y) about itself
inside it, and a point y of M outside the closed ball of radius r keeps
the ball of radius d(x, y) − r about itself clear of it. The same
inequality separates points: two distinct points are a positive distance
apart, and the balls of half that distance about each share no point,
since the detour from one centre to the other through such a point would
be shorter than the distance itself.

| member | statement |
|---|---|
| `OpenIff` | `u ∈ metric_topology(M, d) ⇔ u ⊆ M ∧ ∀x. x ∈ u ⇒ ∃r. &0 < r ∧ ball(M, d, x, r) ⊆ u` |
| `MetricTopology` | `is_topology(metric_topology(M, d))` |
| `MetricTopologySpace` | `⋃metric_topology(M, d) = M` |
| `ClosedIff` | `closed_in(metric_topology(M, d), c) ⇔ c ⊆ M ∧ ∀x. x ∈ M ∧ x ∉ c ⇒ ∃r. &0 < r ∧ ball(M, d, x, r) ∩ c = ∅` |
| `BallOpen` | `x ∈ M ⇒ ball(x, r) ∈ metric_topology` |
| `ClosedBallClosed` | `x ∈ M ⇒ closed_in(metric_topology, closed_ball(x, r))` |
| `MetricHausdorff` | `hausdorff(metric_topology)` |

## The subspace (subspace.go)

A subset s of M with the same distance is a metric space, and its open
sets are exactly the traces on s of the open sets of M. Everything rests
on one identity: a ball of s is the ball of M about the same point, cut
to s.

| member | statement |
|---|---|
| `SubMetricSpace` | `s ⊆ M ⇒ metric_space(s, d)` |
| `MetricTopologySubspace` | `s ⊆ M ⇒ metric_topology(s, d) = subtopology(metric_topology, s)` |

## Continuity (continuous.go)

Continuity between the metric topologies of two distances is continuity
in the ε-δ sense. Of the two distances only the target's is asked
anything — that its balls are open and hold their centres — so the one
hypothesis is `metric_space(N, e)`, and both spaces are spelled.

| member | statement |
|---|---|
| `ContinuousMapIff` | `metric_space(N, e) ⇒ (continuous_map(metric_topology(M, d), metric_topology(N, e), f) ⇔ (∀x. x ∈ M ⇒ f(x) ∈ N) ∧ (∀x ε. x ∈ M ∧ &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀y. y ∈ M ∧ d(x, y) < δ ⇒ e(f(x), f(y)) < ε))` |

## Bounded sets (bounded.go)

A subset of M is bounded when the distances between its points are
bounded: `metric_bounded(M, d, s)`. No centre is named, so the empty set
is bounded in the empty space too; a non-empty set is bounded exactly
when it lies in a closed ball. A subset of a bounded set, a union of
two and so of finitely many, and a ball are bounded, and a compact set
is bounded: the balls of radius 1 about its points cover it, finitely
many of them already do, and each is bounded.

| member | statement |
|---|---|
| `MetricBoundedDef` | `metric_bounded(M, d, s) ⇔ s ⊆ M ∧ (∃b. ∀x y. x ∈ s ∧ y ∈ s ⇒ d(x, y) ≤ b)` |
| `BoundedIffInBall` | `metric_bounded(s) ⇔ s ⊆ M ∧ (s = ∅ ∨ ∃c. ∃r. c ∈ M ∧ s ⊆ closed_ball(c, r))` |
| `BoundedSubset` | `metric_bounded(M, d, t) ∧ s ⊆ t ⇒ metric_bounded(M, d, s)` |
| `BoundedUnion` | `metric_bounded(s) ∧ metric_bounded(t) ⇒ metric_bounded(s ∪ t)` |
| `BoundedUnions` | `finite(f) ∧ (∀u. u ∈ f ⇒ metric_bounded(u)) ⇒ metric_bounded(⋃f)` |
| `BallBounded` | `x ∈ M ⇒ metric_bounded(ball(x, r))` |
| `CompactBounded` | `compact_in(metric_topology, k) ⇒ metric_bounded(k)` |

## Countability (countability.go)

The balls are a base of the metric topology, and so are the balls of
radius 1/n about the points of a dense set; the balls of radius 1/n
about a point are a countable base at it: the topology of a distance is
first countable. For it a countable base, a countable dense set, and a
countable subcover of every open cover are one property — balls of
radius 1/n about a countable dense set, or about the centres of
countable covers by balls of each radius 1/n, make the base: a Lindelöf
metric space is separable.

| member | statement |
|---|---|
| `BallsBase` | `topology_base(metric_topology, {ball(x, r) \| x, r \| x ∈ M ∧ &0 < r})` |
| `MetricFirstCountable` | `first_countable_space(metric_topology)` |
| `DenseBallsBase` | `D ⊆ M ∧ closure(metric_topology, D) = M ⇒ topology_base(metric_topology, {ball(c, real_inv(&n)) \| c, n \| c ∈ D})` |
| `MetricSeparableIffSecondCountable` | `separable_space(metric_topology) ⇔ second_countable_space(metric_topology)` |
| `LindelofSeparable` | `lindelof_space(metric_topology) ⇒ separable_space(metric_topology)` |
| `MetricLindelofIffSecondCountable` | `lindelof_space(metric_topology) ⇔ second_countable_space(metric_topology)` |

## The product (product.go)

The product of two metric spaces carries the distance that is the
larger of the two component distances, `product_metric(d, e)`. The
Euclidean combination is the other choice; the two
distances have the same open sets, and under the larger one a ball of
the product is exactly the rectangle of the two balls, and a closed
ball the rectangle of the two closed balls. So the product
is a metric space, and its topology is the product of the two metric
topologies.

| member | statement |
|---|---|
| `ProductMetricDef` | `product_metric(d, e, p, q) = real_max(d(fst(p), fst(q)), e(snd(p), snd(q)))` |
| `ProductMetric` | `metric_space(M, d) ∧ metric_space(N, e) ⇒ metric_space(set_cross(M, N), product_metric(d, e))` |
| `ProductBall` | `ball(set_cross(M, N), product_metric(d, e), p, r) = set_cross(ball(M, d, fst(p), r), ball(N, e, snd(p), r))` |
| `ProductClosedBall` | `closed_ball(set_cross(M, N), product_metric(d, e), p, r) = set_cross(closed_ball(M, d, fst(p), r), closed_ball(N, e, snd(p), r))` |
| `ProductMetricTopology` | `metric_space(M, d) ∧ metric_space(N, e) ⇒ metric_topology(set_cross(M, N), product_metric(d, e)) = product_topology(metric_topology, metric_topology(N, e))` |

On a countable product of functions the distance is a supremum,
`countable_product_metric(J, d, h)`. A sequence h runs through the
active indices J — it may repeat an index and take inactive ones — and
the coordinate it takes at the place n contributes its factor distance
clipped at one and weighted by $\frac{1}{n+1}$ when h(n) lies in J, and zero
when it does not; the distance is the supremum over n. Three laws are
how it is used, and the members after them cite the laws, not the
definition: it dominates the clipped weighted distance at every place
whose index lies in J, with no axiom of the factors; it lies below every
nonnegative bound of those; and it is not negative when the coordinate
distances at those places are not. On `indexed_functions(J, z, X)` it is
a metric when the active factors are; it controls uniformly each active
coordinate that h takes; finitely many coordinates control it, for any
two functions and with no axiom of the factors; and its topology is the
product of the factor metric topologies.

| member | statement |
|---|---|
| `CountableProductMetricDef` | `countable_product_metric(J, d, h, f, g) = sup(image(λn. COND(h(n) ∈ J, min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1), &0), 𝕌))` |
| `CountableProductCoordinateBelow` | `h(n) ∈ J ⇒ min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1) ≤ countable_product_metric(J, d, h, f, g)` |
| `CountableProductLeastBound` | `&0 ≤ b ∧ (∀n. h(n) ∈ J ⇒ min(d(h(n), f(h(n)), g(h(n))), &1) * real_inv(&n + &1) ≤ b) ⇒ countable_product_metric(J, d, h, f, g) ≤ b` |
| `CountableProductNonneg` | `(∀n. h(n) ∈ J ⇒ &0 ≤ d(h(n), f(h(n)), g(h(n)))) ⇒ &0 ≤ countable_product_metric(J, d, h, f, g)` |
| `CountableProductMetric` | `J ⊆ image(h, 𝕌) ∧ (∀i. i ∈ J ⇒ metric_space(X(i), d(i))) ⇒ metric_space(indexed_functions(J, z, X), countable_product_metric(J, d, h))` |
| `CountableProductProjectionUniform` | `i ∈ image(h, 𝕌) ∧ i ∈ J ∧ &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀f g. countable_product_metric(J, d, h, f, g) < δ ⇒ d(i, f(i), g(i)) < ε` |
| `CountableProductHeadBound` | `&0 < ε ⇒ ∃N. ∀f g. (∀n. n ≤ N ∧ h(n) ∈ J ⇒ d(h(n), f(h(n)), g(h(n))) < ε) ⇒ countable_product_metric(J, d, h, f, g) ≤ ε` |
| `CountableProductMetricTopology` | `J ⊆ image(h, 𝕌) ∧ (∀i. i ∈ J ⇒ metric_space(X(i), d(i))) ⇒ metric_topology(indexed_functions(J, z, X), countable_product_metric(J, d, h)) = indexed_product_topology(J, z, λi. metric_topology(X(i), d(i)))` |

## Metrizable spaces (metrizable.go)

A topology is metrizable when it is the topology of some distance on
some set: `metrizable_space(T)`. A subspace of a metrizable space is
one, the product of two is one, and a discrete space is one, under the
distance that is 1 between distinct points.

| member | statement |
|---|---|
| `MetrizableSpaceDef` | `metrizable_space(T) ⇔ ∃M. ∃d. metric_space(M, d) ∧ T = metric_topology` |
| `MetrizableSubtopology` | `metrizable_space(T) ⇒ metrizable_space(subtopology(T, s))` |
| `MetrizableProduct` | `metrizable_space(T) ∧ metrizable_space(S) ⇒ metrizable_space(product_topology(T, S))` |
| `DiscreteMetrizable` | `metrizable_space({t \| t ⊆ X})` |
## Instances

The line with |x − y| is a metric space whose open sets are the line's
own (`real_topology.RealMetric`, `real_topology.RealTopologyMetric`); the
n-vectors with their distance are one (`euclidean.EuclideanMetric`), and
their open sets are ℝⁿ's (`vector/euclidean_topology`). Each instance is
a theorem of a chapter of its carrier.

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
