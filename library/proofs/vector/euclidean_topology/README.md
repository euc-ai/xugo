# euclidean_topology — the topology of ℝⁿ: its open sets, convergence by coordinates, compactness of closed bounded sets, and Brouwer's fixed point theorem on the cube

The n-vectors with the distance form a metric space
(`euclidean.EuclideanMetric`), and the open sets of ℝⁿ are that metric
space's open sets: `euclidean_topology(n)` is the metric topology of the
carrier `{u | vec⟨n⟩(u)}` under `vec_dist⟨n⟩`. "u is open" is membership,
`u ∈ euclidean_topology(n)`, as on the line; no openness predicate is
minted. The other constants are coordinatewise open boxes, the unit
cube, the unit sphere, the unit sphere as a space and the closed unit ball.

The space's own theorems are the metric chapter's, read at the n-vectors
and written in their vocabulary — a ball about c is the set of n-vectors
within r of c, not `ball({u | vec⟨n⟩(u)}, vec_dist⟨n⟩, c, r)`. That the
open sets form a topology and that its points are the n-vectors ask
nothing of the distance; that the balls are open and that two distinct
n-vectors lie in disjoint open sets read the distance's axioms, through
the instance. What ℝⁿ adds to a metric space is its coordinates: a map
into ℝⁿ is continuous as its coordinates are, a sequence converges as
its coordinates do, a box is compact, being a product of intervals, so
the cube is sequentially compact, and Brouwer's theorem on the
cube is Kuhn's combinatorial lemma brought to the limit.

The chapter binds the real ring once, as `euclidean` does
(`WithInstance(comm_ring.CommRing, real_ring.CommRing)`), so its statements
spell `vec⟨n⟩(u)` and `dist⟨n⟩(u, v)`; and an unanchored numeral `&k` is
a real one (`WithCoerceDomain(RealDomain)`).

## The definitions (definitions.go and open_boxes.go)

| constant | reading |
|---|---|
| `euclidean_topology(n)` | `metric_topology({u \| vec⟨n⟩(u)}, vec_dist⟨n⟩)` |
| `euclidean_open_box⟨n⟩(a, b)` | `{u \| vec⟨n⟩(u) ∧ ∀i < n. a(i) < u(i) ∧ u(i) < b(i)}` |
| `unit_cube(n)` | `{u \| vec⟨n⟩(u) ∧ ∀i. i < n ⇒ &0 ≤ u(i) ∧ u(i) ≤ &1}` |
| `euclidean_sphere(n)` | `{u \| vec⟨n + 1⟩(u) ∧ ‖u‖_(n + 1) = &1}` — the unit sphere Sⁿ in ℝⁿ⁺¹ |
| `euclidean_sphere_topology(n)` | `subtopology(euclidean_topology(n + 1), euclidean_sphere(n))` — Sⁿ as a space |
| `euclidean_ball(n)` | `{u \| vec⟨n⟩(u) ∧ ‖u‖_n ≤ &1}` — the closed unit ball Dⁿ; $D^{n+1}$ is bounded by euclidean_sphere(n) |

## The space (euclidean_topology.go)

| member | statement |
|---|---|
| `EuclideanTopology` | `is_topology(euclidean_topology(n))` |
| `EuclideanSpace` | `⋃euclidean_topology(n) = {u \| vec⟨n⟩(u)}` — the points of ℝⁿ are the n-vectors |
| `EuclideanSecondCountable` | `second_countable_space(euclidean_topology(n))`, including n = 0 — card |
| `OpenIff` | `u ∈ euclidean_topology(n) ⇔ (∀x. x ∈ u ⇒ vec⟨n⟩(x)) ∧ (∀x. x ∈ u ⇒ ∃r. &0 < r ∧ ∀y. vec⟨n⟩(y) ∧ dist⟨n⟩(x, y) < r ⇒ y ∈ u)` |
| `BallOpen` | `vec⟨n⟩(c) ⇒ {y \| vec⟨n⟩(y) ∧ dist⟨n⟩(c, y) < r} ∈ euclidean_topology(n)` |
| `EuclideanHausdorff` | `hausdorff(euclidean_topology(n))` — two distinct n-vectors lie in disjoint open sets |

The countable compact-box cover makes ℝⁿ Lindelöf, and the metric
space theorem turns that into a countable base. Its open subspaces
therefore admit countable subcovers, as used in local analytic
arguments.

## Coordinates (coordinates.go)

A coordinate of a difference is at most its norm, so each coordinate
is a continuous real function on ℝⁿ. Conversely a map from any space
into ℝⁿ is continuous as soon as it takes its values in ℝⁿ and its n
coordinates are continuous: about a point of the preimage of an open
set, which holds a ball of some radius r about the image, the points
whose n coordinates lie within $\frac{r}{n+1}$ of the image's are the space
met with n preimages of open intervals, an open set, and their images
lie within $\frac{n \cdot r}{n+1}$ of it (`euclidean.CoordinateNormBound`). The
chapter's table names «append»(a, t), the tuple a with its coordinate n
set to t, which appends t to an n-vector a; appending is continuous from
ℝⁿ × ℝ to ℝⁿ⁺¹, its coordinates being the second projection and the
coordinates of the first. The unit cube is ℝⁿ met with the n slabs
0 ≤ x(i) ≤ 1, each the preimage of ⟦0, 1⟧ under a continuous coordinate,
so it is closed; it holds the zero vector, so it is not empty.

| member | statement |
|---|---|
| `CoordinateContinuous` | `i < n ⇒ continuous_map(euclidean_topology(n), real_topology, λx. x(i))` |
| `ContinuousIffCoordinates` | `is_topology(T) ⇒ (continuous_map(T, euclidean_topology(n), f) ⇔ (∀x. x ∈ ⋃T ⇒ vec⟨n⟩(f(x))) ∧ (∀i. i < n ⇒ continuous_map(T, real_topology, λx. f(x)(i))))` |
| `AppendCoordinateVec` | `vec⟨n⟩(a) ⇒ vec⟨n + 1⟩(«append»(a, t))` |
| `AppendCoordinateContinuous` | `continuous_map(product_topology(euclidean_topology(n), real_topology), euclidean_topology(n + 1), λp. «append»(fst(p), snd(p)))` |
| `CubeClosed` | `closed_in(euclidean_topology(n), unit_cube(n))` |
| `CubeNonempty` | `unit_cube(n) ≠ ∅` — the zero vector lies in the cube |

## Open boxes (open_boxes.go)

An open box uses independent strict lower and upper bounds in each
active coordinate. The bound functions may have arbitrary tails;
the points in the box are zero-padded n-vectors. At n = 0 there are
no active coordinates and every box is the singleton zero vector.

Boxes are open, and their pairwise intersections are boxes
with maximum lower and minimum upper bounds, including empty intersections.
A sufficiently small box around any point of an open set stays inside it.
Thus a compact K inside an open U has a finite box cover whose union
lies in U; empty K permits the empty cover. This surrounds compact
images in Euclidean space without asserting anything about contractibility
of the intersections with those images.

| Member | Statement |
|---|---|
| `OpenBoxOpen` | Every coordinatewise open box is Euclidean open — card |
| `OpenBoxIntersection` | Intersections take maximum lower and minimum upper bounds — card |
| `OpenBoxBasis` | Every point of an open set lies in a box contained in that set |
| `CompactOpenBoxCover` | A compact set inside an open set has a finite subordinate box cover — card |

## Sequences (sequences.go)

A sequence of n-vectors converges exactly when each of its n coordinates
does: one way by the bound of a coordinate by the norm, the other
because a difference whose n coordinates are at most b in size has norm
at most n·b. A Cauchy sequence of n-vectors has Cauchy coordinates; each
converges on the line, and the sequence converges to its n limits
extended by 0, so ℝⁿ is complete. A closed ball of ℝⁿ is closed in it,
hence complete.

| member | statement |
|---|---|
| `ConvergesIffCoordinates` | `(∀k. vec⟨n⟩(x(k))) ∧ vec⟨n⟩(l) ⇒ (metric_converges_to({u \| vec⟨n⟩(u)}, vec_dist⟨n⟩, x, l) ⇔ ∀i. i < n ⇒ (λk. x(k)(i)) ⟶ l(i))` |
| `EuclideanComplete` | `metric_complete({u \| vec⟨n⟩(u)}, vec_dist⟨n⟩)` |
| `ClosedBallComplete` | `vec⟨n⟩(c) ⇒ metric_complete({u \| vec⟨n⟩(u) ∧ ‖u − c‖_n ≤ r}, vec_dist⟨n⟩)` |

## Brouwer's fixed point theorem (fixed_point.go)

A map of the cube into itself labels each point and coordinate by the
direction it moves that coordinate: ⊥ where it does not move it down, ⊤
where it does not move it up, ⊥ on the lower faces and ⊤ on the upper
ones. Kuhn's lemma (`kuhn_labelling.KuhnLemma`) on the grid of width 1/p then
finds a cell in which every coordinate is moved up at one point and
down at another; the grid is carried into the cube by dividing each
coordinate by p, and the cube's labelling read through that scaling is ⊥
and ⊤ on the grid's faces, as Kuhn's lemma asks. No continuity has
entered yet. As p grows the cells have a convergent subsequence, and
the two points of each coordinate converge with them. A continuous map
of the cube carries convergent sequences of the cube to convergent
sequences: a sequence kept in the shrinking cells is squeezed onto
their limit coordinate by coordinate, its image onto the image of the
limit, and the limit is moved in no coordinate.

| member | statement |
|---|---|
| `KuhnLabelling` | `(∀x. x ∈ unit_cube(n) ⇒ f(x) ∈ unit_cube(n)) ⇒ ∃l.` l(x, i) ⊥ where x(i) = &0, ⊤ where x(i) = &1, `x(i) ≤ f(x)(i)` where ⊥ and `f(x)(i) ≤ x(i)` where ⊤ |
| `AlmostFixedCell` | `0 < p ∧ (∀x. x ∈ unit_cube(n) ⇒ f(x) ∈ unit_cube(n)) ⇒` some point q of the cube has, for each i < n, two points r, s of the cube within &1 / &p of it above in every coordinate with `r(i) ≤ f(r)(i)` and `f(s)(i) ≤ s(i)` |
| `BrouwerCube` | `(∀x. x ∈ unit_cube(n) ⇒ f(x) ∈ unit_cube(n)) ∧ continuous_map(subtopology(euclidean_topology(n), unit_cube(n)), euclidean_topology(n), f) ⇒ ∃x. x ∈ unit_cube(n) ∧ f(x) = x` |

## Compact sets of ℝⁿ (compactness.go)

A box ⟦a, b⟧ⁿ is compact, by induction on n and without sequences: in ℝ⁰
every point is the zero vector, so the box is finite; the box of ℝⁿ⁺¹ is
the box of ℝⁿ times ⟦a, b⟧ with the second factor appended as the
coordinate n, and the product of two compact sets is compact and
appending is continuous, so the image is compact. The unit cube is the
box ⟦0, 1⟧ⁿ, so it is compact, and in a metric space a compact set is
sequentially compact (`complete_metric.CompactImpSequential`): a
sequence of the cube has a subsequence converging in the cube.
Heine–Borel follows:
a closed set whose points have norm at most B lies in the box ⟦−B, B⟧ⁿ,
and a closed set inside a compact set
is compact. The norm is continuous, two norms differing by at most the
distance between the vectors. Conversely a compact set is closed, ℝⁿ
being Hausdorff, and bounded, its norms being a compact set of reals:
the compact sets of ℝⁿ are exactly its closed bounded sets. So the
closed unit ball Dⁿ, the points
whose norm lies in ⟦0, 1⟧, is closed and compact, and the unit sphere Sⁿ,
the points of ℝⁿ⁺¹ of norm exactly 1, is closed inside $D^{n+1}$ and
compact too. What $D^{n+1}$ holds besides Sⁿ is the open unit ball.

| member | statement |
|---|---|
| `BoxAppendCoordinate` | `{u \| vec⟨n + 1⟩(u) ∧ ∀i. i < n + 1 ⇒ a ≤ u(i) ∧ u(i) ≤ b} = image(λp. «append»(fst(p), snd(p)), set_cross({u \| vec⟨n⟩(u) ∧ ∀i. i < n ⇒ a ≤ u(i) ∧ u(i) ≤ b}, ⟦a, b⟧))` |
| `BoxCompact` | `compact_in(euclidean_topology(n), {u \| vec⟨n⟩(u) ∧ ∀i. i < n ⇒ a ≤ u(i) ∧ u(i) ≤ b})` |
| `CubeSubsequence` | `(∀k. x(k) ∈ unit_cube(n)) ⇒ ∃σ l. (∀j. σ(j) < σ(j + 1)) ∧ l ∈ unit_cube(n) ∧ metric_converges_to({u \| vec⟨n⟩(u)}, vec_dist⟨n⟩, x ∘ σ, l)` |
| `HeineBorel` | `closed_in(euclidean_topology(n), k) ∧ (∀x. x ∈ k ⇒ ‖x‖_n ≤ B) ⇒ compact_in(euclidean_topology(n), k)` |
| `CompactIffClosedBounded` | `compact_in(euclidean_topology(n), k) ⇔ closed_in(euclidean_topology(n), k) ∧ ∃B. ∀x. x ∈ k ⇒ ‖x‖_n ≤ B` |
| `NormContinuous` | `continuous_map(euclidean_topology(n), real_topology, λx. ‖x‖_n)` |
| `BallCompact` | `compact_in(euclidean_topology(n), euclidean_ball(n))` |
| `SphereSubsetBall` | `euclidean_sphere(n) ⊆ euclidean_ball(n + 1)` |
| `BallMinusSphere` | `euclidean_ball(n + 1) ∖ euclidean_sphere(n) = {u \| vec⟨n + 1⟩(u) ∧ ‖u‖_(n + 1) < &1}` |
| `SphereCompact` | `compact_in(euclidean_topology(n + 1), euclidean_sphere(n))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
