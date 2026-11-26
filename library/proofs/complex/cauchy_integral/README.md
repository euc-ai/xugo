# cauchy_integral — Cauchy's theorem on a convex set, the Cauchy integral formula on a disc, and what follows from it

A function holomorphic at every point of a closed triangle has integral
zero round its boundary (Goursat): cut the triangle
into four by its midpoints, keep a quarter whose boundary integral is at
least a quarter of the whole, and the nested quarters shrink to a point
where the function is its tangent line to within any ε, whose boundary
integral is zero. The same holds with one exceptional point where the
function is only continuous. On a convex open set the integral from a
fixed point along segments is then a primitive, so the integral round
every closed path in the set is zero. Round a circle, $\frac{1}{z-w}$ has
integral 2πi for every w inside: the geometric series in $\frac{w-c}{z-c}$,
cut after N terms, leaves a remainder whose integral is bounded by a
multiple of qᴺ with q < 1, while the terms integrate to 2πi and zeros.
The integral formula follows by Cauchy's theorem for
$\frac{f(w)-f(z)}{w-z}$, and the same cut series expands a holomorphic
function as a power series on every disc inside its domain. Its
coefficients are bounded by the function's size on a circle (Cauchy's
estimates), which makes a bounded entire function constant (Liouville);
the zeros of a function not identically zero near a point are isolated;
a function on a disc whose zeros accumulate at a point of the disc
vanishes on the whole disc (the identity theorem), so a function not
identically zero there has finitely many zeros in each smaller closed
disc; a function whose modulus on a disc is greatest at its centre is
constant on the disc; a function bounded near an isolated point
extends holomorphically across it; and the sum of a series of
holomorphic functions with a summable local majorant is holomorphic and
is differentiated term by term (Weierstrass).

The chapter reads path_integral's table — `«segInt»(f, z, w)`, the
integral along the segment from z to w, `«circleInt»(f, c, r)`, the
integral once round the circle about c of radius r, and
`«closedPathIn»(X, γ, γ', a, b)`, a closed piecewise smooth path on
⟦a, b⟧ lying in X — and its own names
`«triangle»(a, b, c)`, the closed triangle; `«boundaryInt»(f, a, b, c)`,
the integral round its boundary; `«perimeter»(a, b, c)`, its perimeter
|b − a| + |c − b| + |a − c|; `«convex»(K)`, a convex set of the plane,
holding `segment_path(x, y, θ)` for any two of its points and θ in
⟦0, 1⟧; `«disc»(c, r)`, the open disc about c of radius r; and
`«coef»(f, c, r, k)`, the k-th coefficient of f about c read off the
circle of radius r, «circleInt»(λu. f(u)/(u − c)ᵏ⁺¹, c, r)/(2πi).

## Triangles (triangle.go)

A function with a primitive integrates along a segment to the
primitive's change between the segment's ends: the segment from z to w
is a piecewise smooth path that reaches z at time 0 and w at time 1, so
the fundamental theorem along a path applies. A linear function α + βz
has the primitive αz + βz²/2 in the whole plane; round the boundary of a
triangle the three changes of the primitive cancel, so the integral is
zero. Along a segment the ML estimate reads: the segment's speed is the
constant |w − z|, so an integrand bounded by M gives at most M·|w − z|.
The closed triangle holds its vertices, at coordinates (0, 0), (1, 0)
and (0, 1) along the sides from a, and it is convex: the point at time u
of the segment between two of its points has coordinates that are one
convex combination of theirs, so again nonnegative with sum at most 1.
A function continuous at every point of a convex set is continuous along
every segment of the set, which lies in it.
It holds every triangle whose vertices it holds: the point at
coordinates (σ, τ) along the sides from p combines the coordinates of p,
q and r with weights 1 − σ − τ, σ and τ. Two of its points are at most
its perimeter apart, since p − q is (s₁ − s₂)(b − a) + (t₂ − t₁)(a − c)
with both coefficients at most 1 in size. It is closed: a convergent
sequence of its points has coordinates bounded in the plane, a
subsequence of which converges with its limit in the simplex, and the
continuous map from coordinates to points carries that limit to the
sequence's.
So each side lies in the triangle, and a function continuous on the
triangle and bounded there by M has integral round the boundary at most
M times the perimeter. The midpoints of the sides cut a triangle into
four, the corner triangles at a, b and c and the middle one, and the
boundary integral of the whole is the sum of the four, each run with the
same orientation: each side splits at its midpoint into two sides of
corner triangles (run backwards, the segment from c to a at time s is
the segment from a to c at time 1 − s, so its midpoint is the same
point), and each side of the middle triangle is also a side of a corner
triangle, run the other way, so its two integrals cancel.

| member | statement |
|---|---|
| `SegmentIntegralPrimitive` | `(∀t. 0 ≤ t ≤ 1 ⇒ complex_derivative_at(F, segment_path(z, w, t), f(segment_path(z, w, t)))) ∧ (∀t. 0 ≤ t ≤ 1 ⇒ complex_continuous_at(f, segment_path(z, w, t))) ⇒ «segInt»(f, z, w) = F(w) − F(z)` |
| `TriangleBoundaryLinear` | `«boundaryInt»(λz. α + β * z, a, b, c) = &0` |
| `SegmentIntegralBound` | `(∀t. 0 ≤ t ≤ 1 ⇒ complex_continuous_at(f, segment_path(z, w, t)) ∧ \|f(segment_path(z, w, t))\| ≤ M) ⇒ \|«segInt»(f, z, w)\| ≤ M * \|w − z\|` |
| `TriangleVertices` | `a ∈ «triangle»(a, b, c) ∧ b ∈ «triangle»(a, b, c) ∧ c ∈ «triangle»(a, b, c)` |
| `TriangleConvex` | `«convex»(«triangle»(a, b, c))` |
| `ContinuousAlongSegment` | `«convex»(K) ∧ (∀z. z ∈ K ⇒ complex_continuous_at(f, z)) ∧ p ∈ K ∧ q ∈ K ∧ &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(p, q, t))` |
| `TriangleSubset` | `p ∈ «triangle»(a, b, c) ∧ q ∈ «triangle»(a, b, c) ∧ r ∈ «triangle»(a, b, c) ⇒ «triangle»(p, q, r) ⊆ «triangle»(a, b, c)` |
| `TriangleDiameter` | `p ∈ «triangle»(a, b, c) ∧ q ∈ «triangle»(a, b, c) ⇒ \|p − q\| ≤ «perimeter»(a, b, c)` |
| `TriangleClosed` | `closed_in(complex_topology, «triangle»(a, b, c))` |
| `TriangleBoundaryBound` | `(∀z. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z) ∧ \|f(z)\| ≤ M) ⇒ \|«boundaryInt»(f, a, b, c)\| ≤ M * «perimeter»(a, b, c)` |
| `TriangleQuadrisection` | `(∀z. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)) ⇒ «boundaryInt»(f, a, b, c) = «boundaryInt»(f, a, m_ab, m_ca) + «boundaryInt»(f, m_ab, b, m_bc) + «boundaryInt»(f, m_ca, m_bc, c) + «boundaryInt»(f, m_bc, m_ca, m_ab)`, the midpoints m_ab, m_bc, m_ca being segment_path(·, ·, 1/2) |

## Goursat (goursat.go)

The integral round a triangle is linear in the function: along each side
the integral of f − g is the difference of the integrals, every side
lying in the triangle. The midpoints cut a triangle into four quarters
whose boundary integrals sum to the whole, so by the triangle inequality
one of them keeps at least a quarter of it; its vertices are vertices or
midpoints, all in the triangle, and each of its sides is half a side of
the triangle, so it has half the perimeter. Choosing such a quarter for
every triangle inside the triangle and iterating the choice by recursion
gives nested triangles T(n), each inside the one before, keeping 4⁻ⁿ of
the boundary integral and 2⁻ⁿ of the perimeter P. They are closed,
nonempty and shrinking, so Cantor's intersection theorem
(`complete_metric.CantorIntersection`) gives a common point z₀ of the
triangle. There f has a derivative l, and given ε, f is within
ε·|z − z₀| of its tangent line f(z₀) + l(z − z₀) on a disc about z₀ that
holds T(N) once N is large. The tangent line is linear, so its integral
round T(N) is zero, and the boundary integral of f round T(N) is at most
ε times the square of T(N)'s perimeter; scaled back by 4ᴺ, the
triangle's is at most P²·ε. As ε is arbitrary, its size is at most 0
(`real_order_field.NonposOfSmallMultiples`), so it is zero.

| member | statement |
|---|---|
| `SegmentIntegralSub` | `(∀t. 0 ≤ t ≤ 1 ⇒ complex_continuous_at(f, segment_path(z, w, t))) ∧` the same for g `⇒ «segInt»(λu. f(u) − g(u), z, w) = «segInt»(f, z, w) − «segInt»(g, z, w)` |
| `BoundaryIntegralSub` | `(∀z. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)) ∧` the same for g `⇒ «boundaryInt»(λu. f(u) − g(u), a, b, c) = «boundaryInt»(f, a, b, c) − «boundaryInt»(g, a, b, c)` |
| `TriangleQuarter` | `(∀z. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)) ⇒ ∃p q r.` p, q, r ∈ «triangle»(a, b, c) `∧ \|«boundaryInt»(f, a, b, c)\| ≤ &4 * \|«boundaryInt»(f, p, q, r)\| ∧ «perimeter»(p, q, r) = «perimeter»(a, b, c) / &2` |
| `TriangleNest` | `(∀z. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)) ⇒ ∃p q r : num → complex.` each T(n) = «triangle»(p(n), q(n), r(n)) lies in «triangle»(a, b, c) and T(n + 1) in T(n), `\|«boundaryInt»(f, a, b, c)\| · (1/2)ⁿ · (1/2)ⁿ ≤ \|«boundaryInt»(f, p(n), q(n), r(n))\|`, and T(n)'s perimeter «perimeter»(p(n), q(n), r(n)) is «perimeter»(a, b, c) · (1/2)ⁿ |
| `Goursat` | `holomorphic_on(«triangle»(a, b, c), f) ⇒ «boundaryInt»(f, a, b, c) = &0` |

## One exceptional point (exceptional.go)

Two numbers u and v with im(conj(u)·v) = 0 are parallel: when u ≠ 0, the
parts of N·v and d·u agree, for N = re(u)² + im(u)² and
d = re(u)·re(v) + im(u)·im(v), so v = (d/N)·u. When im(conj(u)·v) ≠ 0
they are independent over ℝ: from x·u + y·v = 0, taking parts and
combining, x and y times re(u)·im(v) − im(u)·re(v) vanish. A flat
triangle has boundary integral 0, because one vertex lies on the side
joining the other two, and that side splits there into the other two
sides run backwards. A triangle splits at any of its points p into three
triangles with p as a vertex; the three edges from p are each run once
each way. Cut off the corner at p of a triangle that is not flat along
the points b_τ and c_τ at time τ of its sides from p: the two pieces
left, b_τ b c and b_τ c c_τ, miss p, since a point of either is p plus
a real combination of b − p and c − p whose coefficients have a
positive sum. For f holomorphic except at p they have boundary integral
0 by Goursat, so the boundary integral is that of the corner triangle.
Near p, f is within 1 of f(p), so round a corner triangle with
$0 < \tau \le \min\left(1, \frac{\delta}{P+1}\right)$ the integral is at most (|f(p)| + 1)·P·τ; a
size at most a fixed multiple of every small enough τ > 0 is at most 0
(`real_order_field.NonposOfSmallMultiples`). Hence a function continuous on a triangle and holomorphic there
except at one point has integral 0 round its boundary.

| member | statement |
|---|---|
| `ParallelRealMultiple` | `u ≠ &0 ∧ im(conj(u) * v) = &0 ⇒ ∃k:real. v = &k * u` |
| `SkewIndependent` | `im(conj(u) * v) ≠ &0 ∧ &x * u + &y * v = &0 ⇒ x = &0 ∧ y = &0` |
| `TriangleSplitAt` | `(∀z. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)) ∧ p ∈ «triangle»(a, b, c) ⇒ «boundaryInt»(f, a, b, c) = «boundaryInt»(f, a, b, p) + «boundaryInt»(f, b, c, p) + «boundaryInt»(f, c, a, p)` |
| `TriangleFlat` | `(∀z. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)) ∧ im(conj(b − a) * (c − a)) = &0 ⇒ «boundaryInt»(f, a, b, c) = &0` |
| `TriangleCutCorner` | `(∀z. z ∈ «triangle»(p, b, c) ⇒ complex_continuous_at(f, z)) ∧ &0 ≤ τ ∧ τ ≤ &1 ⇒ «boundaryInt»(f, p, b, c) = «boundaryInt»(f, p, b_τ, c_τ) + «boundaryInt»(f, b_τ, b, c) + «boundaryInt»(f, b_τ, c, c_τ)`, with b_τ = segment_path(p, b, τ), c_τ = segment_path(p, c, τ) |
| `TriangleCornerApart` | `im(conj(b − p) * (c − p)) ≠ &0 ∧ &0 < τ ∧ τ ≤ &1 ⇒ p ∉ «triangle»(b_τ, b, c) ∧ p ∉ «triangle»(b_τ, c, c_τ)` |
| `TriangleShrinkToCorner` | `(∀z. z ∈ «triangle»(p, b, c) ⇒ complex_continuous_at(f, z)) ∧ holomorphic_on(«triangle»(p, b, c) ∖ {p}, f) ∧ im(conj(b − p) * (c − p)) ≠ &0 ∧ &0 < τ ∧ τ ≤ &1 ⇒ «boundaryInt»(f, p, b, c) = «boundaryInt»(f, p, b_τ, c_τ)` |
| `GoursatAtVertex` | `(∀z. z ∈ «triangle»(p, b, c) ⇒ complex_continuous_at(f, z)) ∧ holomorphic_on(«triangle»(p, b, c) ∖ {p}, f) ⇒ «boundaryInt»(f, p, b, c) = &0` |
| `GoursatExceptPoint` | `(∀z. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)) ∧ holomorphic_on(«triangle»(a, b, c) ∖ {p}, f) ⇒ «boundaryInt»(f, a, b, c) = &0` |

## Cauchy on a convex set (convex.go)

A convex set holds every triangle whose vertices it holds: a point of
the triangle at coordinates (σ, τ) along the sides from a is either a
itself, or the point at time σ + τ of the segment from a to the point at
time $\frac{\tau}{\sigma+\tau}$ of the side from b to c. A disc is convex: the point at
time t of the segment from z to w is c plus (1 − t)·(z − c) + t·(w − c),
so its distance from c is at most the larger of |z − c| and |w − c|.
So a disc is connected: a set open in the plane that holds each point of
the disc it comes arbitrarily near, and holds one point q of the disc,
holds them all. Along the segment from q to another point w, the times
whose point lies in the set are open, and so are the times near which
no point does; each time in ⟦0, 1⟧ is of one kind or the other and none
of both, and ⟦0, 1⟧ is connected (`real_topology.IntervalConnected`).
Along a segment from z to w on
which f is continuous and within M of f(z), the integral of f is within
M·|w − z| of f(z)·(w − z): the constant f(z) integrates to f(z)·(w − z)
through its primitive f(z)·u, and the estimate along a segment bounds
the integral of f − f(z). Now let f be continuous on a convex open set s
and holomorphic there except at one point. Fix a in s and let F(z) be
the integral of f along the segment from a to z. For w near z the
triangle a z w lies in s, so by Goursat with an exceptional point its
boundary integral is 0; hence F(w) − F(z) is the integral along the
segment from z to w, which is within ε·|w − z| of f(z)·(w − z): F is a
primitive of f. For f holomorphic on s, the integral round a closed
piecewise smooth path in s is the change of F between the path's ends,
which is 0.

| member | statement |
|---|---|
| `TriangleInConvex` | `«convex»(K) ∧ a ∈ K ∧ b ∈ K ∧ c ∈ K ⇒ «triangle»(a, b, c) ⊆ K` |
| `DiscConvex` | `«convex»(«disc»(c, R))` |
| `DiscConnected` | `(∀z. z ∈ A ⇒ ∃ρ. &0 < ρ ∧ ∀x. \|x − z\| < ρ ⇒ x ∈ A) ∧ (∀z. \|z − c\| < R ∧ (∀δ. &0 < δ ⇒ ∃x. x ∈ A ∧ \|x − z\| < δ) ⇒ z ∈ A) ∧ \|q − c\| < R ∧ q ∈ A ∧ \|w − c\| < R ⇒ w ∈ A` |
| `SegmentIntegralDeviation` | `(∀t. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t)) ∧ \|f(segment_path(z, w, t)) − f(z)\| ≤ M) ⇒ \|«segInt»(f, z, w) − f(z) * (w − z)\| ≤ M * \|w − z\|` |
| `ConvexPrimitive` | `s ∈ complex_topology ∧ «convex»(s) ∧ complex_continuous_on(s, f) ∧ holomorphic_on(s ∖ {p}, f) ⇒ ∃F. ∀z. z ∈ s ⇒ complex_derivative_at(F, z, f(z))` |
| `CauchyConvex` | `s ∈ complex_topology ∧ «convex»(s) ∧ holomorphic_on(s, f) ∧ «closedPathIn»(s, γ, γ', a, b) ⇒ path_integral(f, γ, γ', a, b) = &0` |

## The circle (circle.go)

Round a circle about c of radius r, $\frac{1}{z-w}$ integrates to 2πi for every
w with |w − c| < r. Write $q(z) = \frac{w-c}{z-c}$: the point inside over
the circle's point, both measured from c. Off c and w, the field
identity $\frac{1}{z-w} = \frac{1}{z-c} + \frac{q(z)}{z-w}$, multiplied by qᵏ, cuts
the geometric series in q one term further:
$\frac{q^k}{z-w} = \frac{q^k}{z-c} + \frac{q^{k+1}}{z-w}$. The circle passes through
neither point: c is r > 0 away, and w is not on it, lying nearer c.
Every $\frac{q^N}{z-v}$ is holomorphic, so continuous, off c and v. Round the
circle, then, the remainder after k terms is the (k + 1)-th term plus
the remainder after k + 1, since the integral round a circle sees a
function only there and is additive in functions continuous there
(`path_integral.CircleIntegralCongruence`, `CircleIntegralAdd`). The
first term, $\frac{1}{z-c}$, integrates to 2πi. Each later term $\frac{q^{n+1}}{z-c}$
is the derivative of $-\frac{q^{n+1}}{n+1}$ off c, so it integrates to 0 round the
closed circle (`CircleIntegralPrimitive`). The remainder after N terms is
Taylor's weighted remainder (expansion.go) for the constant weight 1, so
its integral is at most $2\pi r \cdot \frac{(\lvert w-c \rvert / r)^N}{r - \lvert w-c \rvert}$. These bounds
tend to 0; the distance of the integral from 2πi is fixed and below every
one of them, so it is 0. The members write «q»(z) for $\frac{w-c}{z-c}$.

| member | statement |
|---|---|
| `CutSeriesContinuous` | `z ≠ c ∧ z ≠ v ⇒ complex_continuous_at(λu. «q»(u) ^ N / (u − v), z)` |
| `CircleHigherTermVanishes` | `&0 < r ⇒ «circleInt»(λz. «q»(z) ^ (n + 1) / (z − c), c, r) = &0` |
| `CircleRemainder` | `\|w − c\| < r ⇒ «circleInt»(λz. complex_inv(z − w), c, r) = &(&2 * pi) * complex_i + «circleInt»(λz. «q»(z) ^ (N + 1) / (z − w), c, r)` |
| `CircleRemainderBound` | `\|w − c\| < r ⇒ \|«circleInt»(λz. «q»(z) ^ N / (z − w), c, r)\| ≤ &2 * pi * r * real_pow(\|w − c\| / r, N) / (r − \|w − c\|)` |
| `CircleWindingInside` | `\|w − c\| < r ⇒ «circleInt»(λz. complex_inv(z − w), c, r) = &(&2 * pi) * complex_i` |

## The integral formula (formula.go)

For f holomorphic on a set s holding w,
Carathéodory's form of the derivative at w gives φ with
f(z) − f(w) = φ(z)·(z − w) for every z, continuous at w; near any other
point of s, φ is the difference quotient $\frac{f(u)-f(w)}{u-w}$, which
has a derivative by the quotient rule. So φ is continuous on s and
holomorphic there off w. Take a circle of radius r about c inside a disc of radius R where f is
holomorphic, with w inside the circle. φ has a primitive on the convex
open disc, which holds the circle, so φ integrates to 0 round it
(`path_integral.CircleIntegralPrimitive`). The circle misses w, so on it
$\frac{f(z)}{z-w}$ is $\varphi(z) + f(w) \cdot (z-w)^{-1}$. The integral round the circle
sees only those values, and is linear in functions continuous there;
(z − w)⁻¹ integrates to 2πi. Hence the integral of $\frac{f(z)}{z-w}$ round
the circle is 2πi·f(w).

| member | statement |
|---|---|
| `DifferenceQuotientHolomorphic` | `holomorphic_on(s, f) ∧ w ∈ s ⇒ ∃φ. (∀z. f(z) − f(w) = φ(z) * (z − w)) ∧ complex_continuous_on(s, φ) ∧ holomorphic_on(s ∖ {w}, φ)` |
| `CauchyIntegralFormula` | `holomorphic_on(«disc»(c, R), f) ∧ r < R ∧ \|w − c\| < r ⇒ «circleInt»(λz. f(z) / (z − w), c, r) = &(&2 * pi) * complex_i * f(w)` |

## Power series (expansion.go)

Write $q(u) = \frac{z-c}{u-c}$, the point inside over the circle's point as
in the circle section, now with z inside and u on the circle. Weighted by
f(u), the cut series splits each remainder $f(u) \cdot \frac{q^k}{u-z}$ into the term
$(z-c)^k \cdot \frac{f(u)}{(u-c)^{k+1}}$ and the next remainder $f(u) \cdot \frac{q^{k+1}}{u-z}$. Off c,
$\frac{f(u)}{(u-c)^n}$ is continuous wherever f is: (u − c)ⁿ is holomorphic, and
it is not 0, u − c not being 0 (`field.PowEqZero`). So every piece is
continuous on the circle, and round it the remainder after k terms
integrates to (z − c)ᵏ times the k-th coefficient integral plus the
integral of the remainder after k + 1. The remainder after no terms
integrates to 2πi·f(z) by the integral formula, so by induction f(z) is
the partial sum up to N of its power series plus the integral of the
remainder after N + 1 terms over 2πi: Taylor's formula with Cauchy's
remainder. On the circle |q| = |z − c|/r and the distance to z is at
least r − |z − c|; with f continuous and at most M there, the ML estimate
on the circle (`path_integral.CircleIntegralBound`) bounds the
remainder's integral by $2\pi r M \cdot \frac{(\lvert z-c \rvert / r)^N}{r - \lvert z-c \rvert}$. f, holomorphic
and so continuous on the compact circle, has such an M; the bounds tend
to 0, so the partial sums tend to f(z). The members write «q»(u) for
$\frac{z-c}{u-c}$; the k-th coefficient integral is the chapter's
«coef»(f, c, r, k).

The coefficients «coef»(f, c, r, ·) read off a circle do not depend on
its radius r: the series of two circles both sum to f inside the smaller
one, so they agree (`complex_power_series.CoefficientsUnique`). So the
coefficients of the circle of radius R/2 expand f on the
whole disc: a point z of the disc lies inside the circle of radius
$\frac{\lvert z-c \rvert + R}{2}$, halfway between |z − c| and R, which lies in the disc.

| member | statement |
|---|---|
| `CoefficientIntegrandContinuous` | `complex_continuous_at(f, p) ∧ p ≠ c ⇒ complex_continuous_at(λu. f(u) / (u − c) ^ n, p)` |
| `TaylorRemainderBound` | `(∀u. \|u − c\| = r ⇒ complex_continuous_at(f, u) ∧ \|f(u)\| ≤ M) ∧ \|z − c\| < r ⇒ \|«circleInt»(λu. f(u) * («q»(u) ^ N / (u − z)), c, r)\| ≤ &2 * pi * r * M * real_pow(\|z − c\| / r, N) / (r − \|z − c\|)` |
| `TaylorRemainder` | `holomorphic_on(«disc»(c, R), f) ∧ r < R ∧ \|z − c\| < r ⇒ f(z) = Σ_{k∈0 .. N} «coef»(f, c, r, k) * (z − c) ^ k + «circleInt»(λu. f(u) * («q»(u) ^ (N + 1) / (u − z)), c, r) / (&(&2 * pi) * complex_i)` |
| `PowerSeriesExpansionCircle` | `holomorphic_on(«disc»(c, R), f) ∧ r < R ∧ \|z − c\| < r ⇒ complex_sums(λn. «coef»(f, c, r, n) * (z − c) ^ n, f(z))` |
| `PowerSeriesExpansion` | `holomorphic_on(«disc»(c, R), f) ⇒ ∃a. ∀z. \|z − c\| < R ⇒ complex_sums(λn. a(n) * (z − c) ^ n, f(z))` |

## Consequences of the expansion (consequences.go)

Cauchy's estimate holds for any power series a about c that sums to f on
the disc of radius R: f is then holomorphic there, so by
`complex_power_series.CoefficientsUnique` a is the series of coefficients
«coef»(f, c, r, ·) read off any circle of radius 0 < r < R, and 2πi·a(n)
is the integral of
$\frac{f(u)}{(u-c)^{n+1}}$ round it. With |f| ≤ M on the circle that integrand is at
most $\frac{M}{r^{n+1}}$ in modulus, and the ML estimate gives
$2\pi \lvert a(n) \rvert \le 2\pi r \cdot \frac{M}{r^{n+1}}$: |a(n)|·rⁿ ≤ M. On the open disc of radius r itself, with |f| ≤ M there, the estimate holds at r as well: the circles of radius r(1 − 1/(k + 2)) lie inside the disc, and the bound passes to the limit of their radii (`CauchyEstimateDisc`). Expand a bounded entire function
about w; the estimate holds on circles of every radius, and a coefficient
a(m + 1) ≠ 0 would fail it at the radius $\frac{M+1}{\lvert a(m+1) \rvert} + 1$, chosen so
that |a(m + 1)| times it exceeds M. So every coefficient after the first
is 0, and the function is its constant coefficient everywhere
(Liouville).

The derivative of a function holomorphic on an open set s is holomorphic
there: choose a derivative g(z) at each point; about each z in s a disc
lies in s, f is the sum of its power series on it, and at each point of
the disc the derived series sums to a derivative of f
(`complex_power_series.PowerSeriesDerivativeDisc`), which is g there
since a derivative is unique; so g is the sum of a power series on the
disc, hence holomorphic. So is the logarithmic derivative g/f on
«nonvanishing», the part of s where f does not vanish, and that part is
open (`LogDerivativeHolomorphic`). A function holomorphic on a disc and
not identically 0 there has some coefficient that is not 0; with
m the least such index, the series of the remaining coefficients sums to
an h with f = (z − c)ᵐ·h (`complex_power_series.PowerSeriesFactor`), h
holomorphic and
h(c) = a(m) ≠ 0, and since h is continuous at c, f has no zero at
positive distance below some δ from c.

Read backwards, zeros accumulating at a point p of the disc make f vanish
on each disc about p inside the disc, else they would be isolated at p;
and where f vanishes on a disc about p, its zeros accumulate at each
point w of that disc, so f vanishes on each disc about w inside the disc.
With ρ = R − |q − c| for a point q at which the zeros accumulate, the
times s in ⟦0, 1⟧ whose point c + s·(q − c) on the segment from c to q
has f vanishing within ρ of it form a set S holding 1, and an earlier
time whose point lies less than ρ from that of a time of S lies in S,
every disc of radius ρ about a point of the segment lying inside the
disc. A time of S within $k = \frac{\rho}{2R}$ above the infimum of S is at most
k, else a step of k back from it would lie in S below the infimum; so
0 lies in S, f vanishes near c, and so on the whole disc (the identity
theorem). A closed disc of radius r < R is compact, so infinitely many
zeros in it would have a limit point there
(`topology/compact.CompactLimitPoint`) at which they accumulate: a
function not identically 0 on the disc has finitely many zeros in each
such closed disc.

For f holomorphic on a disc less its centre and bounded there by M,
(z − c)²·f(z) is holomorphic off c, and at c its increment is at most
M·|h|², so its derivative there is 0: it is holomorphic on the whole
disc, its expansion's first two coefficients vanish, and it is (z − c)²
times the sum g of a power series, which agrees with f off c (Riemann's
theorem).

| member | statement |
|---|---|
| `CauchyEstimate` | `(∀z. \|z − c\| < R ⇒ complex_sums(λk. a(k) * (z − c) ^ k, f(z))) ∧ &0 < r ∧ r < R ∧ (∀z. \|z − c\| = r ⇒ \|f(z)\| ≤ M) ⇒ \|a(n)\| * real_pow(r, n) ≤ M` |
| `CauchyEstimateDisc` | `(∀z. \|z − c\| < r ⇒ complex_sums(λk. a(k) * (z − c) ^ k, f(z))) ∧ &0 < r ∧ (∀z. \|z − c\| < r ⇒ \|f(z)\| ≤ M) ⇒ \|a(n)\| * real_pow(r, n) ≤ M` |
| `Liouville` | `holomorphic_on(𝕌, f) ∧ (∀u. \|f(u)\| ≤ M) ⇒ f(z) = f(w)` |
| `HolomorphicDerivative` | `s ∈ complex_topology ∧ holomorphic_on(s, f) ⇒ ∃g. (∀z. z ∈ s ⇒ complex_derivative_at(f, z, g(z))) ∧ holomorphic_on(s, g)` |
| `LogDerivativeHolomorphic` | `s ∈ complex_topology ∧ holomorphic_on(s, f) ⇒ ∃g. (∀z. z ∈ s ⇒ complex_derivative_at(f, z, g(z))) ∧ «nonvanishing» ∈ complex_topology ∧ holomorphic_on(«nonvanishing», λz. g(z) / f(z))` |
| `ZeroFactor` | `holomorphic_on(«disc»(c, R), f) ∧ ¬(∀z. \|z − c\| < R ⇒ f(z) = &0) ⇒ ∃m h. holomorphic_on(«disc»(c, R), h) ∧ h(c) ≠ &0 ∧ (∀z. \|z − c\| < R ⇒ f(z) = (z − c) ^ m * h(z))` |
| `IsolatedZeros` | `holomorphic_on(«disc»(c, R), f) ∧ ¬(∀z. \|z − c\| < R ⇒ f(z) = &0) ⇒ ∃δ. &0 < δ ∧ (∀z. &0 < \|z − c\| ∧ \|z − c\| < δ ⇒ f(z) ≠ &0)` |
| `IdentityTheorem` | `holomorphic_on(«disc»(c, R), f) ∧ \|q − c\| < R ∧ (∀δ. &0 < δ ⇒ ∃w. &0 < \|w − q\| ∧ \|w − q\| < δ ∧ f(w) = &0) ∧ \|z − c\| < R ⇒ f(z) = &0` |
| `ZerosFiniteInClosedDisc` | `holomorphic_on(«disc»(c, R), f) ∧ r < R ∧ ¬(∀z. \|z − c\| < R ⇒ f(z) = &0) ⇒ finite({z \| \|z − c\| ≤ r ∧ f(z) = &0})` |
| `RemovableSingularity` | `holomorphic_on(«disc»(c, R) ∖ {c}, f) ∧ (∀z. &0 < \|z − c\| ∧ \|z − c\| < R ⇒ \|f(z)\| ≤ M) ⇒ ∃g. holomorphic_on(«disc»(c, R), g) ∧ (∀z. &0 < \|z − c\| ∧ \|z − c\| < R ⇒ g(z) = f(z))` |

## Maximum modulus (maximum.go)

A function holomorphic on a disc has a derivative, so is continuous, at
every point of the disc; so f is continuous along every circle of radius
r < R about the centre, and
the parts of f along the circle are continuous functions of the time on
⟦0, 2π⟧. The mean value property is the integral formula at the centre:
there $z - c = r \cdot e^{it}$, so the integrand $\frac{f(z)}{z-c} \cdot i \cdot r \cdot e^{it}$ is
i·f(z), and i times the integral of f along the circle is 2πi·f(c).
Every point z lies on the circle about c of radius |z − c|, reached at a
time in ⟦0, 2π⟧ (`path_integral.CirclePathReaches`). If the real part of a holomorphic g is at most re(g(c))
at every time of ⟦0, 2π⟧ along such a circle, the gap re(g(c)) − re(g) is a continuous
nonnegative function of the time whose integral is 0 by the mean value
property, so it vanishes (`real_integral.NonnegIntegralZeroVanishes`).
For the maximum modulus principle, turn f by conj(f(c)): the real part
of conj(f(c))·f is the component of f along f(c), at most
|f(c)|·|f| ≤ |f(c)|² on the disc and equal to |f(c)|² at c. So it is
|f(c)|² all along the circle through any z, at z too; with
|f(z)| ≤ |f(c)|, the parts of f(z) − f(c) have squares adding up to
|f(z)|² − 2·|f(c)|² + |f(c)|² ≤ 0, so f(z) = f(c).

| member | statement |
|---|---|
| `ContinuousAlongCircle` | `holomorphic_on(«disc»(c, R), f) ∧ &0 < r ∧ r < R ⇒ real_continuous_on(⟦&0, &2 * pi⟧, λt. re(f(circle_path(c, r, t)))) ∧ real_continuous_on(⟦&0, &2 * pi⟧, λt. im(f(circle_path(c, r, t))))` |
| `MeanValueCircle` | `holomorphic_on(«disc»(c, R), f) ∧ &0 < r ∧ r < R ⇒ complex_integral(λt. f(circle_path(c, r, t)), &0, &2 * pi) = &(&2 * pi) * f(c)` |
| `RealPartConstantOnCircle` | `holomorphic_on(«disc»(c, R), g) ∧ &0 < r ∧ r < R ∧ (∀s. &0 ≤ s ∧ s ≤ &2 * pi ⇒ re(g(circle_path(c, r, s))) ≤ re(g(c))) ∧ &0 ≤ t ∧ t ≤ &2 * pi ⇒ re(g(circle_path(c, r, t))) = re(g(c))` |
| `MaximumModulus` | `holomorphic_on(«disc»(c, R), f) ∧ (∀w. \|w − c\| < R ⇒ \|f(w)\| ≤ \|f(c)\|) ∧ \|z − c\| < R ⇒ f(z) = f(c)` |

## Series of holomorphic functions (weierstrass.go)

A series of functions holomorphic on a set, dominated on a disc about
each point of the set by a convergent series of numbers, has a
holomorphic sum, and the sum's derivative is the sum of the
derivatives. This is Weierstrass's theorem in the form his M-test gives
it. The hypothesis is local — one disc inside the set and one summable
majorant for each point, which makes the set open without its being
assumed — and no notion of uniform convergence is named.

The proof does not pass through an integral of the sum. A function
holomorphic on a disc and bounded by M there differs from its tangent
line at the centre by at most 2M|h|²/r² (`TangentRemainderBound`, from
the power series expansion and Cauchy's estimate at the radius of the
disc itself, `CauchyEstimateDisc`). That bound uses nothing of the
function but its size, so it can be summed over the series: the sum
differs from a line by a constant times |h|², which makes the line's
slope its derivative
(`complex_derivative.DerivativeFromQuadraticRemainder`).

| member | statement |
|---|---|
| `TangentRemainderBound` | `&0 < r ∧ holomorphic_on({z \| \|z − c\| < r}, g) ∧ (∀z. \|z − c\| < r ⇒ \|g(z)\| ≤ M) ∧ complex_derivative_at(g, c, d) ∧ \|h\| ≤ r / &2 ⇒ \|g(c + h) − g(c) − d * h\| ≤ &2 * M * (\|h\| * \|h\|) / (r * r)` |
| `SeriesHolomorphic` | `(∀n. holomorphic_on(S, g(n))) ∧ (∀c. c ∈ S ⇒ ∃r M t. &0 < r ∧ real_sums(M, t) ∧ (∀n z. \|z − c\| < r ⇒ z ∈ S ∧ \|g(n, z)\| ≤ M(n))) ⇒ ∃f. (∀z. z ∈ S ⇒ complex_sums(λn. g(n, z), f(z))) ∧ holomorphic_on(S, f)` |
| `SeriesDerivative` | `(∀n w. w ∈ S ⇒ complex_derivative_at(g(n), w, g'(n, w))) ∧ (∀c. c ∈ S ⇒ ∃r M t. &0 < r ∧ real_sums(M, t) ∧ (∀n w. \|w − c\| < r ⇒ w ∈ S ∧ \|g(n, w)\| ≤ M(n))) ∧ (∀w. w ∈ S ⇒ complex_sums(λn. g(n, w), f(w))) ∧ z ∈ S ⇒ ∃d. complex_sums(λn. g'(n, z), d) ∧ complex_derivative_at(f, z, d)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
