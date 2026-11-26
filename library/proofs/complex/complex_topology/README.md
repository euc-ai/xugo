# complex_topology — the plane ℂ as a metric space: its open sets, limits of sequences and functions, continuity, and compact sets

The distance of two complex numbers is the modulus of their difference,
`dist(z, w) = |z − w|` (`complex_dist`), and the open sets of ℂ are the
metric topology of the whole plane under it, `complex_topology`; "u is
open" is membership, as on the line. A sequence tends to `l`,
`a ⟶ l`, when its terms are eventually within every ε of `l`; a
function tends to `l` at `c`, `f ⟶ l (at c)`, on punctured discs about
`c`; and continuity at a point and on a set (relative to the set) are
read the same way. The arrow is the line's arrow, chosen by the types
it joins. Series are `complex/complex_series`'s: a series sums to s
exactly when its partial sums tend to s (`complex_series.SumsIffPartialSums`).

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `complex_dist(z, w)`, written `dist(z, w)` | `\|z − w\|` |
| `complex_topology` | `metric_topology(𝕌, complex_dist)` |
| `complex_converges_to(a, l)`, written `a ⟶ l` | `∀ε > 0 ∃N ∀n ≥ N. \|a(n) − l\| < ε` |
| `complex_limit_at(f, c, l)`, written `f ⟶ l (at c)` | `∀ε > 0 ∃δ > 0 ∀z. 0 < \|z − c\| < δ ⇒ \|f(z) − l\| < ε` |
| `complex_continuous_at(f, c)` | `∀ε > 0 ∃δ > 0 ∀z. \|z − c\| < δ ⇒ \|f(z) − f(c)\| < ε` |
| `complex_continuous_on(s, f)` | the same at each `c ∈ s`, for `z ∈ s` |
| `complex_coordinate_topology(r)` | the product topology on `num → complex` over the coordinates below r, the others held at 0: ℂ^r |

## The space (metric.go)

The plane's topological facts are the metric chapter's, read at the
instance `ComplexMetric`. A ball of the distance is the disc of complex
numbers within its radius of its centre (`ComplexBall`), and through it
openness and the open discs are said in the plane's own terms, and a set
under the same distance carries the subspace topology
(`ComplexTopologySubspace`); the plane is complete, Cauchy's criterion
read through the distance. The half-plane right of a vertical line is
open. A punctured disc is open: a point at distance
d from the centre keeps the disc of radius min(d, r − d) about it inside,
by the triangle inequality on either side. The points of a finite set
keep a positive distance from any other point: by induction, each new
point x other than p lowers the distance to min(δ, |x − p|). The plane is
Hausdorff, so its finite sets are closed (`separation.T1FiniteClosed`),
and an open set less finitely many points is open.

| member | statement |
|---|---|
| `ComplexMetric` | `metric_space(𝕌, complex_dist)` |
| `ComplexBall` | `w ∈ ball(𝕌, complex_dist, c, r) ⇔ \|w − c\| < r` |
| `ComplexTopology` | `is_topology(complex_topology)` |
| `ComplexTopologySpace` | `⋃complex_topology = 𝕌` |
| `ComplexOpenIff` | `u ∈ complex_topology ⇔ ∀z. z ∈ u ⇒ ∃r. &0 < r ∧ ∀w. \|w − z\| < r ⇒ w ∈ u` |
| `DiscOpen` | `{w \| \|w − c\| < r} ∈ complex_topology` |
| `PuncturedDiscOpen` | `{z \| &0 < \|z − c\| ∧ \|z − c\| < r} ∈ complex_topology` |
| `RightHalfPlaneOpen` | `{z \| c < re(z)} ∈ complex_topology` |
| `FinitePointsIsolated` | `finite(P) ⇒ ∃δ. &0 < δ ∧ ∀q. q ∈ P ∧ \|q − p\| < δ ⇒ q = p` |
| `ComplexHausdorff` | `hausdorff(complex_topology)` |
| `OpenDiffFinite` | `S ∈ complex_topology ∧ finite(P) ⇒ S ∖ P ∈ complex_topology` |
| `ComplexTopologySubspace` | `metric_topology(s, complex_dist) = subtopology(complex_topology, s)` |
| `ConvergesIffMetric` | `a ⟶ l ⇔ metric_converges_to(𝕌, complex_dist, a, l)` |
| `ComplexComplete` | `metric_complete(𝕌, complex_dist)` |

## Sequences (sequences.go)

Everything runs through the parts. A part of a difference is the
difference of the parts (`complex_field.PartsSub`) and at most its modulus, and the modulus is at most the sum of the parts' sizes,
since z = re(z) + i·im(z) and |i| = 1 (`complex_abs.AbsLeParts`). So a sequence
converges exactly when its two parts do (`ConvergesIffParts`), and the
limit laws for constants, negatives, sums, products and conjugates are
the line's laws on the two parts; a product's parts are re·re − im·im
and re·im + im·re. A sequence whose moduli are at most those of a real
sequence tending to 0 tends to 0. Uniqueness is the metric chapter's, read at the
plane through `ConvergesIffMetric`. The modulus and the inverse are direct
ε–N arguments: two moduli differ by at most the modulus of the
difference, and a number more than |l|/2 in modulus and within
ε·|l|²/2 of l has its inverse within ε of 1/l, since
|1/u − 1/l| = |u − l| / (|u|·|l|) (`InvEstimate`). Bolzano–Weierstrass takes
the line's theorem part by part, the real parts thinned first and the
imaginary parts along that subsequence; Cauchy's criterion does so from
Cauchy to convergent, and the converse is the metric chapter's (a
convergent sequence is Cauchy, read at the plane's metric).

| member | statement |
|---|---|
| `ConvergesIffParts` | `a ⟶ l ⇔ (λn. re(a(n))) ⟶ re(l) ∧ (λn. im(a(n))) ⟶ im(l)` |
| `LimitConst` | `(λn. c) ⟶ c` |
| `LimitNeg` | `a ⟶ l ⇒ (λn. −a(n)) ⟶ −l` |
| `LimitAdd` | `a ⟶ l ∧ b ⟶ m ⇒ (λn. a(n) + b(n)) ⟶ l + m` |
| `LimitSub` | `a ⟶ l ∧ b ⟶ m ⇒ (λn. a(n) − b(n)) ⟶ l − m` |
| `LimitMul` | `a ⟶ l ∧ b ⟶ m ⇒ (λn. a(n) * b(n)) ⟶ l * m` |
| `LimitConj` | `a ⟶ l ⇒ (λn. conj(a(n))) ⟶ conj(l)` |
| `LimitUnique` | `a ⟶ l ∧ a ⟶ m ⇒ l = m` |
| `LimitOfReal` | `(λn. &(x(n))) ⟶ &l ⇔ x ⟶ l` |
| `LimitAbs` | `a ⟶ l ⇒ (λn. \|a(n)\|) ⟶ \|l\|` |
| `LimitSqueezeZero` | `(∀n. \|a(n)\| ≤ b(n)) ∧ b ⟶ &0 ⇒ a ⟶ complex_of_real(&0)` |
| `InvEstimate` | `&0 < ε ∧ l ≠ &0 ∧ \|l\| / &2 < \|u\| ∧ \|u − l\| < ε * \|l\| * \|l\| / &2 ⇒ \|complex_inv(u) − complex_inv(l)\| < ε` |
| `LimitInv` | `a ⟶ l ∧ l ≠ &0 ⇒ (λn. complex_inv(a(n))) ⟶ complex_inv(l)` |
| `CauchyIffConvergent` | `(∀ε > 0 ∃N ∀m n ≥ N. \|a(m) − a(n)\| < ε) ⇔ ∃l. a ⟶ l` |
| `BolzanoWeierstrass` | `(∀n. \|a(n)\| ≤ B) ⇒ ∃σ l. (∀j. σ(j) < σ(j + 1)) ∧ a ∘ σ ⟶ l` |

## Limits at a point (limits.go)

The line's arguments (`real_function_limits`) carried to ℂ, with the
modulus in place of the absolute value. Two limits at one point share,
for every ε, the punctured disc of the smaller of their two radii, and a
point of a punctured disc of radius d is c + d/2, a real half-radius out.
The sum gives each summand ε/2; the product splits its deviation into
three terms, f·g − l·m = (f − l)(g − m) + l(g − m) + m(f − l); the inverse
of a function with a nonzero limit keeps f above |l|/2 in modulus on one
disc and within ε·|l|²/2 of l on another, where the estimate on the
inverse (`InvEstimate`) applies. Two limits l ≠ m, taken at half
their distance, meet at a point of the shared disc, which the triangle
inequality forbids. Two functions that agree on a punctured disc about c
have one limit there (`LimitAtLocal`), an equation of limits as on the
line. A function continuous at the limit carries the limit
along. A limit at c is read along sequences: f ⟶ l (at c) exactly
when f carries every sequence tending to c without touching it to a
sequence tending to l; the converse goes by contradiction, the points
where f stays ε away from l accumulating at c
(`complete_metric.ApproachingSequence`).

| member | statement |
|---|---|
| `PuncturedDiscPoint` | `&0 < d ⇒ &0 < \|c + &(d / &2) − c\| ∧ \|c + &(d / &2) − c\| < d` |
| `LimitAtCommonRadius` | `f ⟶ l (at c) ∧ g ⟶ m (at c) ∧ &0 < ε ⇒ ∃δ. &0 < δ ∧ (∀z. &0 < \|z − c\| ∧ \|z − c\| < δ ⇒ \|f(z) − l\| < ε ∧ \|g(z) − m\| < ε)` |
| `LimitAtConst` | `(λz. k) ⟶ k (at c)` |
| `LimitAtId` | `(λz. z) ⟶ c (at c)` |
| `LimitAtNeg` | `f ⟶ l (at c) ⇒ (λz. −f(z)) ⟶ −l (at c)` |
| `LimitAtAdd` | `f ⟶ l (at c) ∧ g ⟶ m (at c) ⇒ (λz. f(z) + g(z)) ⟶ l + m (at c)` |
| `LimitAtSub` | `f ⟶ l (at c) ∧ g ⟶ m (at c) ⇒ (λz. f(z) − g(z)) ⟶ l − m (at c)` |
| `LimitAtMul` | `f ⟶ l (at c) ∧ g ⟶ m (at c) ⇒ (λz. f(z) * g(z)) ⟶ l * m (at c)` |
| `LimitAtInv` | `f ⟶ l (at c) ∧ l ≠ &0 ⇒ (λz. complex_inv(f(z))) ⟶ complex_inv(l) (at c)` |
| `LimitAtUnique` | `f ⟶ l (at c) ∧ f ⟶ m (at c) ⇒ l = m` |
| `LimitAtLocal` | `&0 < d ∧ (∀z. &0 < \|z − c\| ∧ \|z − c\| < d ⇒ f(z) = g(z)) ⇒ complex_limit_at(f, c) = complex_limit_at(g, c)` |
| `LimitAtCompose` | `f ⟶ l (at c) ∧ complex_continuous_at(g, l) ⇒ (g ∘ f) ⟶ g(l) (at c)` |
| `LimitAtSequential` | `f ⟶ l (at c) ⇔ ∀a. (∀n. a(n) ≠ c) ∧ a ⟶ c ⇒ (λn. f(a(n))) ⟶ l` |

## Continuity (continuous.go)

Continuity at c is tending to f(c) at c — the punctured disc lies inside
the disc, and at c itself the value is f(c) — so each continuity law at
a point is its limit law read at the values. A function that moves no
point further from its value at c than the point lies from c is
continuous at c, with ε itself as the radius; conjugation, the real and
imaginary parts and the modulus, each read as a complex number, are such
maps. Continuity on a set is relative to the set: continuity at every
point of s gives it, it passes to subsets, and on an open set it is the
same as continuity at every point, a disc about c lying inside s.
Continuity on a set is continuity of a map from the subspace to the
plane, the metric chapter's ε–δ sentence read with the distance |w − z|;
the modulus is a continuous map to the line, being the distance from 0;
so are the real and imaginary parts, with δ = ε, since neither part
moves a point further than the point moves
(`complex_abs.PartsNonexpanding`); a map from any space into the plane
is continuous exactly when its two parts are;
and a function continuous at c carries every sequence tending to c to a
sequence tending to its value. An open rectangle, «rectangle» in
`RectangleOpenConvex`, the z with x₁ < re(z) < x₂ and y₁ < im(z) < y₂,
is open and convex.

| member | statement |
|---|---|
| `ContinuousAtIffLimit` | `complex_continuous_at(f, c) ⇔ f ⟶ f(c) (at c)` |
| `ContinuousAtLocal` | `&0 < d ∧ (∀z. \|z − c\| < d ⇒ f(z) = g(z)) ∧ complex_continuous_at(g, c) ⇒ complex_continuous_at(f, c)` |
| `ContinuousAtCompose` | `complex_continuous_at(g, c) ∧ complex_continuous_at(f, g(c)) ⇒ complex_continuous_at(f ∘ g, c)` |
| `ContinuousAtRealCompose` | `complex_continuous_at(λw. &g(w), c) ∧ real_continuous_at(f, g(c)) ⇒ complex_continuous_at(λw. &f(g(w)), c)` |
| `ContinuousAtConst` | `complex_continuous_at(λz. k, c)` |
| `ContinuousAtId` | `complex_continuous_at(λz. z, c)` |
| `ContinuousAtNeg` | `complex_continuous_at(f, c) ⇒ complex_continuous_at(λz. −f(z), c)` |
| `ContinuousAtAdd` | `complex_continuous_at(f, c) ∧ complex_continuous_at(g, c) ⇒ complex_continuous_at(λz. f(z) + g(z), c)` |
| `ContinuousAtSub` | `complex_continuous_at(f, c) ∧ complex_continuous_at(g, c) ⇒ complex_continuous_at(λz. f(z) − g(z), c)` |
| `ContinuousAtMul` | `complex_continuous_at(f, c) ∧ complex_continuous_at(g, c) ⇒ complex_continuous_at(λz. f(z) * g(z), c)` |
| `ContinuousAtInv` | `complex_continuous_at(f, c) ∧ f(c) ≠ &0 ⇒ complex_continuous_at(λz. complex_inv(f(z)), c)` |
| `ContinuousAtNonexpanding` | `(∀z. \|f(z) − f(c)\| ≤ \|z − c\|) ⇒ complex_continuous_at(f, c)` |
| `ContinuousAtConj` | `complex_continuous_at(λz. conj(z), c)` |
| `ContinuousAtParts` | `complex_continuous_at(λz. &(re(z)), c) ∧ complex_continuous_at(λz. &(im(z)), c) ∧ complex_continuous_at(λz. &(\|z\|), c)` |
| `ContinuousAtOn` | `(∀z. z ∈ s ⇒ complex_continuous_at(f, z)) ⇒ complex_continuous_on(s, f)` |
| `ContinuousOnSubset` | `complex_continuous_on(s, f) ∧ t ⊆ s ⇒ complex_continuous_on(t, f)` |
| `ContinuousOnOpenIff` | `s ∈ complex_topology ⇒ (complex_continuous_on(s, f) ⇔ ∀z. z ∈ s ⇒ complex_continuous_at(f, z))` |
| `ContinuousOnIffMap` | `complex_continuous_on(s, f) ⇔ continuous_map(subtopology(complex_topology, s), complex_topology, f)` |
| `ModulusContinuous` | `continuous_map(complex_topology, real_topology, λz. \|z\|)` |
| `PartsContinuous` | `continuous_map(complex_topology, real_topology, λz. re(z)) ∧ continuous_map(complex_topology, real_topology, λz. im(z))` |
| `ContinuousIffParts` | `is_topology(R) ⇒ (continuous_map(R, complex_topology, h) ⇔ continuous_map(R, real_topology, λx. re(h(x))) ∧ continuous_map(R, real_topology, λx. im(h(x))))` |
| `RectangleOpenConvex` | `«rectangle» ∈ complex_topology ∧ (∀u v. ∀t. u ∈ «rectangle» ∧ v ∈ «rectangle» ∧ &0 ≤ t ∧ t ≤ &1 ⇒ u + &t * (v − u) ∈ «rectangle»)` |
| `ContinuousAtSequential` | `complex_continuous_at(f, c) ∧ a ⟶ c ⇒ (λn. f(a(n))) ⟶ f(c)` |

## Compact sets (compact.go)

A set of complex numbers is compact exactly when it is closed and
bounded in modulus (Heine–Borel). A compact set is closed in the
Hausdorff plane, and its moduli are a compact, so bounded, set of reals.
Conversely, a closed set bounded in modulus is sequentially compact —
Bolzano–Weierstrass gives each of its sequences a subsequence
converging in the distance, whose limit the closed set keeps — and in
a metric space that is compactness. So closed discs are compact, and so
are circles, a closed disc meeting the closed complement of an open
disc. A function continuous on a set is a continuous map from the
subspace, and the topology chapters' theorems on compact sets read
through it: on a compact set its values are bounded, its modulus
attains a largest value, and it is uniformly
continuous, by Heine–Cantor in the compact metric space the set is
under the same distance. An open set containing the closed half-plane
Re s ≥ 1 contains, for every R, the points with 1 − δ < Re s and
|Im s| ≤ R, for some δ > 0.

| member | statement |
|---|---|
| `ClosedBoundedSequentiallyCompact` | `closed_in(complex_topology, k) ∧ (∀z. z ∈ k ⇒ \|z\| ≤ B) ∧ (∀n. x(n) ∈ k) ⇒ ∃σ l. (∀j. σ(j) < σ(j + 1)) ∧ l ∈ k ∧ metric_converges_to(𝕌, complex_dist, x ∘ σ, l)` |
| `ComplexCompactIff` | `compact_in(complex_topology, k) ⇔ closed_in(complex_topology, k) ∧ ∃B. ∀z. z ∈ k ⇒ \|z\| ≤ B` |
| `ClosedDiscCompact` | `compact_in(complex_topology, {z \| \|z − c\| ≤ r})` |
| `CircleCompact` | `compact_in(complex_topology, {z \| \|z − c\| = r})` |
| `ModulusAttainsMax` | `compact_in(complex_topology, k) ∧ k ≠ ∅ ∧ complex_continuous_on(k, f) ⇒ ∃z. z ∈ k ∧ ∀w. w ∈ k ⇒ \|f(w)\| ≤ \|f(z)\|` |
| `ContinuousOnCompactBounded` | `compact_in(complex_topology, k) ∧ complex_continuous_on(k, f) ⇒ ∃B. ∀w. w ∈ k ⇒ \|f(w)\| ≤ B` |
| `ContinuousOnCompactUniform` | `compact_in(complex_topology, k) ∧ complex_continuous_on(k, f) ∧ &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀z w. z ∈ k ∧ w ∈ k ∧ \|z − w\| < δ ⇒ \|f(z) − f(w)\| < ε` |
| `StripInsideOpen` | `U ∈ complex_topology ∧ (∀s. &1 ≤ re(s) ⇒ s ∈ U) ⇒ ∃δ. &0 < δ ∧ (∀s. &1 − δ < re(s) ∧ \|im(s)\| ≤ R ⇒ s ∈ U)` |

## Right of a point (right_limits.go)

Complex functions of a real variable σ, read on the intervals
a < σ < a + d to the right of a point a. If (σ − a)·f(σ) tends to l as
σ decreases to a, so does (σ − a)·g(σ) for any g within a bound of f on
such an interval (`ScaledLimitBoundedDifference`). A finite sum of
functions, each bounded on some such interval, is bounded on one
(`FiniteSumBoundedNear`).

| member | statement |
|---|---|
| `ScaledLimitBoundedDifference` | `(∀η. &0 < η ⇒ ∃d. &0 < d ∧ (∀σ. a < σ ∧ σ < a + d ⇒ \|&(σ − a) * f(σ) − l\| < η)) ∧ &0 < e ∧ (∀σ. a < σ ∧ σ < a + e ⇒ \|f(σ) − g(σ)\| ≤ M) ∧ &0 < ε ⇒ ∃δ. &0 < δ ∧ (∀σ. a < σ ∧ σ < a + δ ⇒ \|&(σ − a) * g(σ) − l\| < ε)` |
| `FiniteSumBoundedNear` | `finite(S) ∧ (∀x. x ∈ S ⇒ ∃d M. &0 < d ∧ (∀σ. a < σ ∧ σ < a + d ⇒ \|F(x, σ)\| ≤ M)) ⇒ ∃d M. &0 < d ∧ (∀σ. a < σ ∧ σ < a + d ⇒ \|Σ_{x∈S} F(x, σ)\| ≤ M)` |

## Continuous complex functions on a space (cards.go)

What `real_valued` states for real functions on a space, stated here for
complex ones: sums and products of continuous complex functions are
continuous, so is the reciprocal of one that vanishes nowhere, and so are
finite sums and finite products, the forms a
matrix product and a determinant of continuous entries are read in. The
coordinate space ℂ^r is locally compact and Hausdorff. Read through its
real and imaginary parts it is real 2r-space.

| member | statement |
|---|---|
| `ContinuousComplexAdd` | `is_topology(T) ∧ continuous_map(T, complex_topology, f) ∧ continuous_map(T, complex_topology, g) ⇒ continuous_map(T, complex_topology, λx. f(x) + g(x))` — card |
| `ContinuousComplexMul` | the same for `λx. f(x) * g(x)` — card |
| `ContinuousComplexInv` | `is_topology(T) ∧ continuous_map(T, complex_topology, f) ∧ (∀x. x ∈ ⋃T ⇒ f(x) ≠ &0) ⇒ continuous_map(T, complex_topology, λx. complex_inv(f(x)))` — card |
| `ContinuousComplexSum` | `is_topology(T) ∧ finite(s) ∧ (∀k. k ∈ s ⇒ continuous_map(T, complex_topology, f(k))) ⇒ continuous_map(T, complex_topology, λx. module_sum(complex_add, &0, s, λk. f(k, x)))` — card |
| `ContinuousComplexProduct` | the same for `module_sum(complex_mul, &1, s, λk. f(k, x))` — card |
| `CoordinateLocallyCompact` | `locally_compact_space(complex_coordinate_topology(r)) ∧ hausdorff(complex_coordinate_topology(r))` — card |
| `CoordinateRealHomeomorphism` | `homeomorphic_map(euclidean_topology(2N), complex_coordinate_topology(N), λw i. COND(i < N, &w(i) + i·&w(N + i), 0))` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
