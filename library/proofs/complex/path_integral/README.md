# path_integral — the integral of a complex function of a real variable, and the integral along a piecewise smooth path

A complex function `g` of a real variable is integrated part by part:
`complex_has_integral(g, a, b, I)` holds when the real and imaginary
parts of `g` have the parts of `I` as their Riemann integrals on
`⟦a, b⟧`, and `complex_integral(g, a, b)` is the oriented value, as
`real_integral` is on the line. A path `γ : ℝ → ℂ` has velocity `d` at
`t`, `path_derivative_at(γ, t, d)` (complex_derivative's constant), when
its parts have the parts of `d`
as derivatives. A piecewise smooth path on `⟦a, b⟧` is continuous there
and has a bounded velocity `γ'`, continuous and the derivative of `γ`
off finitely many points; the velocity is an argument of its own, as a
derivative is on the line. The integral of `f` along `γ` is
`path_integral(f, γ, γ', a, b)` $= \int_a^b f(\gamma(t)) \cdot \gamma'(t) dt$, over any
parameter interval `⟦a, b⟧`. Two paths are named: the segment
`segment_path(z, w)`, run on `⟦0, 1⟧`, and the circle
`circle_path(c, r)`, run on `⟦0, 2π⟧`. The chapter's table names
`«segInt»(f, z, w)`, the integral along the segment from z to w,
`«circleInt»(f, c, r)`, the integral once round the circle about c of
radius r, and `«closedPathIn»(X, γ, γ', a, b)`: γ is a piecewise smooth
path on `⟦a, b⟧` with velocity γ', closed, γ(b) = γ(a), and it stays in
the set X. cauchy_integral reads the table, and residue through it.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `complex_has_integral(g, a, b, I)` | the parts of g have the parts of I as integrals on ⟦a, b⟧ |
| `complex_integral(g, a, b)` | `complex(real_integral(re ∘ g, a, b), real_integral(im ∘ g, a, b))` |
| `piecewise_smooth_path(γ, γ', a, b)` | a ≤ b; γ continuous on ⟦a, b⟧; γ' bounded on ⟦a, b⟧; off a finite k, γ' the velocity strictly inside and continuous |
| `path_integral(f, γ, γ', a, b)` | `complex_integral(λt. f(γ(t)) * γ'(t), a, b)` |
| `segment_path(z, w)` | `λt. z + t·(w − z)` |
| `circle_path(c, r)` | `λt. c + r·exp(i·t)` |

## The integral part by part (integral.go)

Each law of the real integral holds part by part, reassembled by
`ComplexEq` or the definition. A complex multiple mixes the parts:
re(c·g) = re c·re g − im c·im g and im(c·g) = re c·im g + im c·re g,
each a combination of the two real integrals. Where the parts are
continuous on an interval, the oriented integral adds over adjacent
stretches of it in any order, and an affine change of the variable is
the real one part by part. The Newton–Leibniz theorem allows finitely
many points where G has no velocity, each part being the real theorem
off the same finite set; with no point set aside it is the theorem as
usually stated. The estimate of the modulus
turns g so that its integral points along the positive axis: the
component of g(t) along I, the real part of conj(I)·g(t), has integral
|I|² and is at most |I|·|g(t)| ≤ |I|·h(t) where h dominates |g|, so
|I|² ≤ |I|·J for J the integral of h, and a positive |I| cancels
(`ComplexHasIntegralDominated`). Its two cases are h = |g|, the integral
of the modulus, and h = M, a constant bound with integral M·(b − a),
which asks nothing of |g| beyond the bound.

| member | statement |
|---|---|
| `ComplexHasIntegralUnique` | `complex_has_integral(g, a, b, I) ∧ complex_has_integral(g, a, b, J) ⇒ I = J` |
| `ComplexHasIntegralValue` | `complex_has_integral(g, a, b, I) ⇒ complex_integral(g, a, b) = I` |
| `ComplexIntegralConst` | `a ≤ b ⇒ complex_integral(λt. k, a, b) = k * &(b − a)` |
| `ComplexHasIntegralAdd` | `complex_has_integral(g, a, b, I) ∧ complex_has_integral(h, a, b, J) ⇒ complex_has_integral(λt. g(t) + h(t), a, b, I + J)` |
| `ComplexHasIntegralNeg` | `complex_has_integral(g, a, b, I) ⇒ complex_has_integral(λt. −g(t), a, b, −I)` |
| `ComplexHasIntegralSub` | `complex_has_integral(g, a, b, I) ∧ complex_has_integral(h, a, b, J) ⇒ complex_has_integral(λt. g(t) − h(t), a, b, I − J)` |
| `ComplexHasIntegralScale` | `complex_has_integral(g, a, b, I) ⇒ complex_has_integral(λt. c * g(t), a, b, c * I)` |
| `ComplexHasIntegralSplit` | `a ≤ c ∧ c ≤ b ∧ complex_has_integral(g, a, c, I) ∧ complex_has_integral(g, c, b, J) ⇒ complex_has_integral(g, a, b, I + J)` |
| `ComplexIntegrableSubinterval` | `complex_has_integral(g, a, b, I) ∧ a ≤ c ∧ c ≤ d ∧ d ≤ b ⇒ ∃J. complex_has_integral(g, c, d, J)` |
| `ComplexContinuousIntegrable` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, λt. re(g(t))) ∧ real_continuous_on(⟦a, b⟧, λt. im(g(t))) ⇒ ∃I. complex_has_integral(g, a, b, I)` |
| `ComplexIntegralAdditive` | g's parts continuous on ⟦l, r⟧ ∧ a, b, c ∈ ⟦l, r⟧ ⇒ `complex_integral(g, a, b) + complex_integral(g, b, c) = complex_integral(g, a, c)` |
| `ComplexIntegralAffine` | g's parts continuous on ⟦l, r⟧ ∧ β, β + α ∈ ⟦l, r⟧ ⇒ `complex_integral(λt. g(β + α * t) * &α, &0, &1) = complex_integral(g, β, β + α)` |
| `ComplexHasIntegralDominated` | `complex_has_integral(g, a, b, I) ∧ real_has_integral(h, a, b, J) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ \|g(t)\| ≤ h(t)) ⇒ \|I\| ≤ J` |
| `ComplexHasIntegralAbsBound` | `complex_has_integral(g, a, b, I) ∧ real_has_integral(λt. \|g(t)\|, a, b, J) ⇒ \|I\| ≤ J` |
| `ComplexHasIntegralBound` | `(∀t. a ≤ t ∧ t ≤ b ⇒ \|g(t)\| ≤ M) ∧ complex_has_integral(g, a, b, I) ⇒ \|I\| ≤ M * (b − a)` |
| `ComplexNewtonLeibnizOffFinite` | `finite(k) ∧ real_continuous_on(⟦a, b⟧, λt. re(G(t))) ∧ real_continuous_on(⟦a, b⟧, λt. im(G(t))) ∧ (∀t. a < t ∧ t < b ∧ t ∉ k ⇒ path_derivative_at(G, t, g(t))) ∧ complex_has_integral(g, a, b, I) ⇒ I = G(b) − G(a)` |
| `ComplexNewtonLeibniz` | `real_continuous_on(⟦a, b⟧, λt. re(G(t))) ∧ real_continuous_on(⟦a, b⟧, λt. im(G(t))) ∧ (∀t. a < t ∧ t < b ⇒ path_derivative_at(G, t, g(t))) ∧ complex_has_integral(g, a, b, I) ⇒ I = G(b) − G(a)` |

## Paths (paths.go)

A path's velocity is read part by part, so a path with a velocity at
every point of a set has continuous parts there. A function continuous
at a point is continuous there part by part: once both parts of z are
near those of w, both parts of f(z) are near those of f(w), a complex
number being no longer than the sum of its parts. So a function
continuous at the points of a path whose parts are continuous, at a
point or on a set, is continuous along it, part by part. The chain rule
along a path follows from Carathéodory's form on both sides. A function
continuous along a piecewise smooth path has an integral along it: its
integrand is bounded and continuous off the path's exceptional set.
With the chain rule comes the fundamental theorem: the integral of f
along γ is the change of a primitive between the path's ends, the
Newton–Leibniz theorem allowing the path's finitely many exceptional
points. With a length, the ML estimate bounds an integral along a path
by M times the integral of the speed. Integrals along a path are linear
in the function (a finite sum of functions continuous along a path
integrates term by term, by induction on the index set), and see the
function only on the path: two functions that agree at γ(t) for every t
between a and b have the same integral, each part of the integrand
having the same oriented integral (`real_integral.IntegralCongruence`).
The segment is
rewritten into its parts before the definitions are opened; it is
piecewise smooth with no exceptional point, its velocity being the
constant w − z. Along a segment an affine change of the time variable
reverses the integral when the segment is run backwards, and splits it
at any point into the integrals along the two pieces.

| member | statement |
|---|---|
| `PathDerivativeContinuousOn` | `(∀t. t ∈ s ⇒ path_derivative_at(γ, t, γ'(t))) ⇒ real_continuous_on(s, λt. re(γ(t))) ∧ real_continuous_on(s, λt. im(γ(t)))` |
| `ContinuousAtPartwise` | `complex_continuous_at(f, w) ∧ &0 < ε ⇒ ∃η. &0 < η ∧ ∀z. \|re(z) − re(w)\| < η ∧ \|im(z) − im(w)\| < η ⇒ \|re(f(z)) − re(f(w))\| < ε ∧ \|im(f(z)) − im(f(w))\| < ε` |
| `ContinuousAlongPath` | `real_continuous_on(s, λt. re(γ(t))) ∧ real_continuous_on(s, λt. im(γ(t))) ∧ (∀t. t ∈ s ⇒ complex_continuous_at(f, γ(t))) ⇒ real_continuous_on(s, λt. re(f(γ(t)))) ∧ real_continuous_on(s, λt. im(f(γ(t))))` |
| `ContinuousAtAlongPath` | `real_continuous_at(λt. re(γ(t)), c) ∧ real_continuous_at(λt. im(γ(t)), c) ∧ complex_continuous_at(f, γ(c)) ⇒ real_continuous_at(λt. re(f(γ(t))), c) ∧ real_continuous_at(λt. im(f(γ(t))), c)` |
| `PathDerivativeCompose` | `complex_derivative_at(F, γ(t), l) ∧ path_derivative_at(γ, t, d) ⇒ path_derivative_at(λs. F(γ(s)), t, l * d)` |
| `PathIntegrable` | `piecewise_smooth_path(γ, γ', a, b) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t))) ⇒ ∃I. complex_has_integral(λt. f(γ(t)) * γ'(t), a, b, I)` |
| `PathIntegralPrimitive` | `piecewise_smooth_path(γ, γ', a, b) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ complex_derivative_at(F, γ(t), f(γ(t)))) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t))) ⇒ path_integral(f, γ, γ', a, b) = F(γ(b)) − F(γ(a))` |
| `PathSpeedIntegrable` | `piecewise_smooth_path(γ, γ', a, b) ⇒ ∃L. real_has_integral(λt. \|γ'(t)\|, a, b, L)` |
| `PathIntegralBound` | `piecewise_smooth_path(γ, γ', a, b) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(f, γ(t)) ∧ \|f(γ(t))\| ≤ M) ⇒ \|path_integral(f, γ, γ', a, b)\| ≤ M * real_integral(λt. \|γ'(t)\|, a, b)` |
| `PathIntegralAdd` | `piecewise_smooth_path(γ, γ', a, b) ∧` f, g continuous at γ(t) on ⟦a, b⟧ `⇒ path_integral(λz. f(z) + g(z), γ, γ', a, b) = path_integral(f, γ, γ', a, b) + path_integral(g, γ, γ', a, b)` |
| `PathIntegralSub` | `piecewise_smooth_path(γ, γ', a, b) ∧` f, g continuous at γ(t) on ⟦a, b⟧ `⇒ path_integral(λz. f(z) − g(z), γ, γ', a, b) = path_integral(f, γ, γ', a, b) − path_integral(g, γ, γ', a, b)` |
| `PathIntegralScale` | `piecewise_smooth_path(γ, γ', a, b) ∧` f continuous at γ(t) on ⟦a, b⟧ `⇒ path_integral(λz. k * f(z), γ, γ', a, b) = k * path_integral(f, γ, γ', a, b)` |
| `PathIntegralSum` | `finite(I) ∧ piecewise_smooth_path(γ, γ', a, b) ∧ (∀i t. i ∈ I ∧ a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(F(i), γ(t))) ⇒ path_integral(λz. Σ_{i∈I} F(i, z), γ, γ', a, b) = Σ_{i∈I} path_integral(F(i), γ, γ', a, b)` |
| `PathIntegralCongruence` | `(∀t. min(a, b) ≤ t ∧ t ≤ max(a, b) ⇒ f(γ(t)) = g(γ(t))) ⇒ path_integral(f, γ, γ', a, b) = path_integral(g, γ, γ', a, b)` |
| `SegmentPathDerivative` | `path_derivative_at(segment_path(z, w), t, w − z)` |
| `SegmentPiecewiseSmooth` | `piecewise_smooth_path(segment_path(z, w), λt. w − z, &0, &1)` |
| `SegmentIntegrandContinuous` | `(∀t. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))) ⇒` the parts of `λu. f(segment_path(z, w, u)) * (w − z)` are continuous on ⟦0, 1⟧ |
| `SegmentReverse` | f continuous along ⟦z, w⟧ `⇒ «segInt»(f, w, z) = −«segInt»(f, z, w)` |
| `SegmentSplit` | `&0 ≤ s ∧ s ≤ &1 ∧` f continuous along ⟦z, w⟧ `⇒ «segInt»(f, z, w) = «segInt»(f, z, segment_path(z, w, s)) + «segInt»(f, segment_path(z, w, s), w)` |

## The circle (circle.go)

The circle is rewritten into its parts before the definitions are
opened: by Euler's formula the circle about c is the point with parts
re(c) + r·cos s and im(c) + r·sin s, whose derivatives r·(−sin t) and
r·cos t are the parts of i·r·exp(it). Run on ⟦0, 2π⟧ it is piecewise
smooth with no exceptional point, its velocity having continuous parts
and modulus |i·r|, and it is so on any parameter interval. The circle
is closed: by Euler's formula exp(2πi) and exp(0) have the cosine and
sine of 2π and of 0 as their parts, which agree by periodicity. Its
points lie at distance |r| from the centre, and its speed is the
constant |r|, so its length is 2π·|r|. Every point z lies on the
circle about c of radius |z − c| at a time in ⟦0, 2π⟧: its polar angle in
⟬−π, π⟧, moved on by a full turn when negative. Once around a circle the
integrand of $\frac{1}{z-c}$ is the constant i, so the integral is 2π·i, which
is not 0: its modulus is 2π, and π is positive. A character e^{imt}, m
an integer, integrates over one period to 2π at m = 0, where it is the
constant one, and to 0 otherwise: e^{imt}/(im), the character scaled by
1/(im), is a primitive and takes one value at both ends, the cosine and
the sine having period 2π. With
r > 0 the integral round the circle about c of radius r is one over the
circle's points |u − c| = r. It sees a function only on the circle, and
is additive and homogeneous in functions continuous there; it is 0 for a
function with a primitive on the circle, the circle being closed; and
for a function continuous and at most B in modulus there, it is at most
B times the length 2πr. On the circle about 0 of radius R > 0 every
point has modulus R, its right half runs from −iR to iR, and over an
arc from α to β the integral of a function continuous and at most M in
modulus along it is at most M times the arc's length R·(β − α).

| member | statement |
|---|---|
| `CirclePathDerivative` | `path_derivative_at(circle_path(c, r), t, complex_i * &r * exp(complex_i * &t))` |
| `CirclePiecewiseSmooth` | `piecewise_smooth_path(circle_path(c, r), λt. complex_i * &r * exp(complex_i * &t), &0, &2 * π)` |
| `CircleArcPiecewiseSmooth` | `∀c:complex. ∀r a b:real. a ≤ b ⇒ piecewise_smooth_path(circle_path(c, r), λt:real. complex_i * &r * exp(complex_i * &t), a, b)` |
| `RightArcPath` | `piecewise_smooth_path(circle_path(&0, R), λt. complex_i * &R * exp(complex_i * &t), −(π / &2), π / &2) ∧ circle_path(&0, R, −(π / &2)) = −(complex_i * &R) ∧ circle_path(&0, R, π / &2) = complex_i * &R` |
| `CirclePathClosed` | `circle_path(c, r, &2 * π) = circle_path(c, r, &0)` |
| `CirclePathRadius` | `\|circle_path(c, r, t) − c\| = \|r\|` |
| `CirclePathModulus` | `&0 < R ⇒ \|circle_path(&0, R, t)\| = R` |
| `CirclePathReaches` | `∃t. &0 ≤ t ∧ t ≤ &2 * π ∧ circle_path(c, \|z − c\|, t) = z` |
| `CircleLength` | `real_integral(λt. \|complex_i * &r * exp(complex_i * &t)\|, &0, &2 * π) = &2 * π * \|r\|` |
| `CircleIntegralInverse` | `&0 < r ⇒ «circleInt»(λz. complex_inv(z − c), c, r) = &(&2 * π) * complex_i` |
| `CircleCharacterIntegral` | `complex_integral(λt. exp(complex_i * &(real_of_int(m) * t)), &0, &2 * π) = COND(m = &0, &(&2 * π), &0)` |
| `TwoPiINonzero` | `&(&2 * π) * complex_i ≠ &0` |
| `CircleIntegralCongruence` | `&0 < r ∧ (∀u. \|u − c\| = r ⇒ f(u) = g(u)) ⇒ «circleInt»(f, c, r) = «circleInt»(g, c, r)` |
| `CircleIntegralAdd` | `&0 < r ∧` f, g continuous at every u with \|u − c\| = r `⇒ «circleInt»(λz. f(z) + g(z), c, r) = «circleInt»(f, c, r) + «circleInt»(g, c, r)` |
| `CircleIntegralScale` | `&0 < r ∧` f continuous at every u with \|u − c\| = r `⇒ «circleInt»(λz. k * f(z), c, r) = k * «circleInt»(f, c, r)` |
| `CircleIntegralPrimitive` | `&0 < r ∧ (∀u. \|u − c\| = r ⇒ complex_derivative_at(F, u, f(u)) ∧ complex_continuous_at(f, u)) ⇒ «circleInt»(f, c, r) = &0` |
| `CircleIntegralBound` | `&0 < r ∧ (∀u. \|u − c\| = r ⇒ complex_continuous_at(f, u) ∧ \|f(u)\| ≤ B) ⇒ \|«circleInt»(f, c, r)\| ≤ &2 * π * r * B` |
| `ArcIntegralBound` | `&0 < R ∧ α ≤ β ∧ (∀t. α ≤ t ∧ t ≤ β ⇒ complex_continuous_at(f, circle_path(&0, R, t)) ∧ \|f(circle_path(&0, R, t))\| ≤ M) ⇒ \|path_integral(f, circle_path(&0, R), λt. complex_i * &R * exp(complex_i * &t), α, β)\| ≤ M * (R * (β − α))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
