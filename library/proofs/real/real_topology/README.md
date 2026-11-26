# real_topology — the real line as a topological space

A set u of reals is open when each of its points has a radius around
it inside u: for every `x ∈ u` some `δ > 0` has every `y` with
`|y − x| < δ` in u. The family of those sets is `real_topology`, and it
is a topology in the sense of `topology/topological_space` — the
chapter proves that instance first, once the definition is read as
membership. "u is open" is `u ∈
real_topology`, membership, exactly as it is in the abstract chapter,
so nothing beside the family is minted to say it; an interval is a set
holding every real between two of its points, `real_interval(s)`. The
four bounded intervals are constants of the chapter, written `⟦a, b⟧`,
`⟬a, b⟭`, `⟦a, b⟭` and `⟬a, b⟧` (the tortoise shell brackets keep
`(a, b)` the pair); the rays are written as the sets they are.

This is where the abstract topology meets the reals the extrema and
limit chapters built. The laws of `topological_space` are cited here at
the instance, and its notions are spelled with the family written out,
`compact_in(real_topology, k)`. Completeness enters four times, each
time in a form another chapter prepared: as the supremum of a set of
reals (`real_sup_inf`) in the two least-upper-bound arguments that make
an interval connected and a closed interval compact; as the supremum a
closed bounded set holds; as Bolzano–Weierstrass (`real_sequences`) in
the sequential reading of compactness; and as Cauchy's criterion
(`real_sequences`) in the completeness of the line as a metric space
(`RealComplete`). The functions on this space —
continuity, the intermediate and extreme value theorems — are
`real/real_continuous`'s.

## The chapter has eight movements

**1. The open sets.** `OpenIff` reads the definition as membership in
the family, and it is the form every later member reads openness in.
Everything else the line's open sets have in common with any metric
space is read off `topology/metric_space` through the sixth movement
below: the open sets form a topology (`RealTopology`), the space is the
whole line (`RealSpace`), a set is closed exactly when each real outside
it has a radius missing it (`ClosedIff`, the form the chapter reads
closedness in), a ball is open (`BallOpen`), and two distinct reals lie
in disjoint open sets (`RealHausdorff`).

**2. Rays and intervals.** The rays above and below a point are open, a
point x above a keeping the radius x − a; an open interval is the meet
of two rays, and the complement of a closed interval in the line is the
union of two, so a closed interval is closed. The four intervals between
a and b are constants of the chapter: `real_closed_interval(a, b)`,
written `⟦a, b⟧`, `real_open_interval(a, b)`, written `⟬a, b⟭`, and the
half-open `real_closed_open_interval(a, b)` and
`real_open_closed_interval(a, b)`, written `⟦a, b⟭` and `⟬a, b⟧`. Each
definition declares that the closers read membership in it as its two
bounds, `x ∈ ⟦a, b⟧` as `a ≤ x ∧ x ≤ b`, so a proof cites nothing to
read it; the four membership laws (`ClosedIntervalMembership` and its
siblings) state that reading for a rewrite or an instance.

**3. The connected sets are the intervals.** An interval holds every
point t·x + (1 − t)·y between two of its points (`IntervalSegment`). An interval cannot be
split by two open sets. The heart is a closed interval ⟦p, q⟧ with p in
an open u, q in an open v, and every point in one of them: the points
of ⟦p, q⟧ in u have a supremum m. If m lies in v, a point of u
approaches it from below inside v's radius about m, and that point lies
in both. If it does not, m lies in u, below q, and a point a little
above m would still lie in u — above the supremum. Conversely a set that
skips a point y between two of its points is split by the open rays
below and above y. So the connected sets of the line are exactly its
intervals.

**4. Compact sets.** A closed bounded interval is compact — Heine–Borel
on the line, by the same least-upper-bound device: the points up to
which finitely many members of an open cover already cover ⟦a, x⟧ have
a supremum, and the member holding that supremum carries the finite
cover past b. A compact set is bounded, the balls about 0 covering it
and finitely many of them, being nested, lying in the largest. A
non-empty closed set bounded above holds its supremum: were the
supremum outside, the open complement would keep a whole radius about
it clear of the set, yet the supremum is approached from inside. A
compact set is closed — the abstract chapter's `CompactClosed` read at
the line, which is Hausdorff — so a non-empty compact set holds its
supremum and its infimum — its greatest and least
elements, which the extreme value theorem reads off.

**5. Sequences.** A set of reals is closed exactly when it keeps the
limits of its convergent sequences; the converse is built from one
point of the set in each ball of radius $\frac{1}{n+1}$, the sequence
`real_sequences` shows tends to the centre. A sequence in a compact set
has a subsequence converging in the set: the set is bounded, so
Bolzano–Weierstrass gives the subsequence, and closed, so it keeps the
limit.

**6. The line as a metric space.** The distance `dist(x, y) = |x − y|`
makes the whole line a metric space — each axiom a fact of the order
and |·| — and the line's open sets are exactly the open sets of that
distance (`topology/metric_space`): a ball of the distance about c is
the set of reals within its radius of c, since |c − y| = |y − c|
(`RealBall`), so the two tests of openness are one test. That is the
bridge through which every theorem about metric spaces reads on the
line — the first movement's facts today, continuity as ε-δ and the
subspace of a subset when they are wanted.

**7. The line among the spaces.** The open intervals with rational ends
are a countable base of the line; every real has a compact
neighbourhood, a closed interval about it, and a base of connected
ones, the open intervals; and the line itself is not compact, a compact
set of reals being bounded. Under the distance of the sixth movement the
line is complete — Cauchy's criterion, read as a property of the metric
space.

**8. Open sets from intervals (intervals.go).** An open set of reals
is a union of countably many open intervals. Each of its points lies in
an interval with rational ends inside it (`RationalIntervalInside`).
The pairs of rationals are countable, so a sequence runs through them;
keep each interval it bounds that lies inside the set, put the empty
interval ⟬0, 0⟭ in place of the rest, and these intervals together make
up the whole set (`OpenCountableIntervalUnion`).

## Members

| entry | statement |
|---|---|
| `RealTopologyDef` | `real_topology = {u \| ∀x. x ∈ u ⇒ ∃δ. &0 < δ ∧ ∀y. real_abs(y − x) < δ ⇒ y ∈ u}` |
| `RealIntervalDef` | `real_interval(s) ⇔ ∀x y z. x ∈ s ∧ z ∈ s ∧ x ≤ y ∧ y ≤ z ⇒ y ∈ s` |
| `RealClosedIntervalDef` | `⟦a, b⟧ = {x \| a ≤ x ∧ x ≤ b}` (`real_closed_interval(a, b)`) |
| `RealOpenIntervalDef` | `⟬a, b⟭ = {x \| a < x ∧ x < b}` (`real_open_interval(a, b)`) |
| `RealClosedOpenIntervalDef` | `⟦a, b⟭ = {x \| a ≤ x ∧ x < b}` (`real_closed_open_interval(a, b)`) |
| `RealOpenClosedIntervalDef` | `⟬a, b⟧ = {x \| a < x ∧ x ≤ b}` (`real_open_closed_interval(a, b)`) |
| `OpenIff` | `u ∈ real_topology ⇔ ∀x. x ∈ u ⇒ ∃δ. &0 < δ ∧ ∀y. real_abs(y − x) < δ ⇒ y ∈ u` |
| `RealTopology` | `is_topology(real_topology)` |
| `RealSpace` | `⋃real_topology = 𝕌` |
| `ClosedIff` | `closed_in(real_topology, s) ⇔ ∀x. x ∉ s ⇒ ∃δ. &0 < δ ∧ ∀y. real_abs(y − x) < δ ⇒ y ∉ s` |
| `BallOpen` | `{y \| real_abs(y − c) < r} ∈ real_topology` |
| `RayAboveOpen` | `{x \| a < x} ∈ real_topology` |
| `RayBelowOpen` | `{x \| x < b} ∈ real_topology` |
| `ClosedIntervalMembership` | `x ∈ ⟦a, b⟧ ⇔ a ≤ x ∧ x ≤ b` |
| `OpenIntervalMembership` | `x ∈ ⟬a, b⟭ ⇔ a < x ∧ x < b` |
| `ClosedOpenIntervalMembership` | `x ∈ ⟦a, b⟭ ⇔ a ≤ x ∧ x < b` |
| `OpenClosedIntervalMembership` | `x ∈ ⟬a, b⟧ ⇔ a < x ∧ x ≤ b` |
| `OpenIntervalOpen` | `⟬a, b⟭ ∈ real_topology` |
| `ClosedIntervalClosed` | `closed_in(real_topology, ⟦a, b⟧)` |
| `RealHausdorff` | `hausdorff(real_topology)` |
| `IntervalSegment` | `real_interval(s) ∧ x ∈ s ∧ y ∈ s ∧ &0 ≤ t ∧ t ≤ &1 ⇒ t · x + (&1 − t) · y ∈ s` |
| `IntervalConnected` | `real_interval(s) ⇒ connected_in(real_topology, s)` |
| `ConnectedImpInterval` | `connected_in(real_topology, s) ⇒ real_interval(s)` |
| `ConnectedIffInterval` | `connected_in(real_topology, s) ⇔ real_interval(s)` |
| `ClosedIntervalCompact` | `compact_in(real_topology, ⟦a, b⟧)` |
| `CompactBounded` | `compact_in(real_topology, k) ⇒ ∃B. ∀x. x ∈ k ⇒ real_abs(x) ≤ B` |
| `SupClosedAttained` | `closed_in(real_topology, s) ∧ s ≠ ∅ ∧ (∃b. ∀x. x ∈ s ⇒ x ≤ b) ⇒ sup(s) ∈ s` |
| `InfClosedAttained` | `closed_in(real_topology, s) ∧ s ≠ ∅ ∧ (∃b. ∀x. x ∈ s ⇒ b ≤ x) ⇒ inf(s) ∈ s` |
| `SupCompactAttained` | `compact_in(real_topology, k) ∧ k ≠ ∅ ⇒ sup(k) ∈ k ∧ (∀x. x ∈ k ⇒ x ≤ sup(k))` |
| `InfCompactAttained` | `compact_in(real_topology, k) ∧ k ≠ ∅ ⇒ inf(k) ∈ k ∧ (∀x. x ∈ k ⇒ inf(k) ≤ x)` |
| `ClosedIffSequential` | `closed_in(real_topology, s) ⇔ ∀a l. (∀n. a(n) ∈ s) ∧ a ⟶ l ⇒ l ∈ s` |
| `CompactSubsequence` | `compact_in(real_topology, k) ∧ (∀n. a(n) ∈ k) ⇒ ∃σ l. (∀j. σ(j) < σ(j + 1)) ∧ a ∘ σ ⟶ l ∧ l ∈ k` |
| `RealMetric` | `metric_space(𝕌, real_dist)` |
| `RealBall` | `y ∈ ball(𝕌, real_dist, c, r) ⇔ real_abs(y - c) < r` |
| `RealTopologyMetric` | `real_topology = metric_topology(𝕌, real_dist)` |
| `RealComplete` | `metric_complete(𝕌, real_dist)` — the line is complete, its Cauchy sequences being real_sequences' |
| `RealSecondCountable` | `second_countable_space(real_topology)` |
| `RealLocallyCompact` | `locally_compact_space(real_topology)` |
| `RealLocallyConnected` | `locally_connected_space(real_topology)` |
| `RealNotCompact` | `¬compact_in(real_topology, 𝕌)` |
| `RationalIntervalInside` | `u ∈ real_topology ∧ x ∈ u ⇒ ∃p q. rational(p) ∧ rational(q) ∧ p < x ∧ x < q ∧ ⟬p, q⟭ ⊆ u` |
| `OpenCountableIntervalUnion` | `u ∈ real_topology ⇒ ∃a b. ∀x. x ∈ u ⇔ ∃n. a(n) < x ∧ x < b(n)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
