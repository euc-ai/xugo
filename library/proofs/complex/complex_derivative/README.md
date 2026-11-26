# complex_derivative — the complex derivative and the holomorphic functions

A function `f : ℂ → ℂ` has derivative `l` at `c` when its difference
quotient `(f(z) − f(c)) / (z − c)` tends to `l` at `c`:

`complex_derivative_at(f, c, l) ⇔ (λz. (f(z) − f(c)) / (z − c)) ⟶ l (at c)`.

The relation is the object, as on the line (`real_derivative`): a
statement names the derivative it is about. What the line has no word
for is the property itself: `holomorphic_on(s, f)` says that `f` has a
complex derivative at every point of `s`, which is what Cauchy's theory
reads — it asks of a function that it be holomorphic, and seldom what
its derivative is. On an open set this is holomorphy; on a set that is
not open it asks a derivative in the whole plane at each of its points,
which is pointwise complex differentiability, so the statements that
mean holomorphy in the usual sense take `s` open. The velocity of a path
γ : ℝ → ℂ, `path_derivative_at`, is defined here: it is what a complex
derivative becomes read along a real line.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `complex_derivative_at(f, c, l)` | `(λz. (f(z) − f(c)) / (z − c)) ⟶ l (at c)` |
| `holomorphic_on(s, f)` | `∀z. z ∈ s ⇒ ∃l. complex_derivative_at(f, z, l)` |
| `path_derivative_at(γ, t, d)` | the parts of γ have the parts of d as derivatives at t: the path γ has velocity d at t |

## The derivative (derivative.go)

A function has at most one derivative at a point: two limits of one
quotient are one number. Off the centre, the quotient's distance from l,
times |z − c|, is the increment's distance from l·(z − c), so the
derivative is the linear approximation whose error is below ε·|z − c|
on a punctured disc about c (`DerivativeIncrement`). Carathéodory's form reads the
derivative as a slope continuous at c, the quotient patched at c with l;
from it f is continuous where it has a derivative, and the chain rule
composes the two slopes, φ(g(z))·ψ(z), with no division by g(z) − g(c).
Sums, negatives, differences and multiples rearrange the quotient into
the same operation on quotients; the product rule splits the quotient of
f·g as f(z)·(g's quotient) + g(c)·(f's quotient); the reciprocal rule
works on a disc where g stays away from 0. The power rule: z⁰ is the
constant 1, with derivative $0 = 0 \cdot c^{0-1}$, and at a successor
exponent an induction through the product rule gives (m + 1)·cᵐ, its
coefficient the real number m + 1 read in ℂ. A derivative sees f only on a disc about c
(`DerivativeLocal`).

| member | statement |
|---|---|
| `DerivativeUnique` | `complex_derivative_at(f, c, l) ∧ complex_derivative_at(f, c, m) ⇒ l = m` |
| `DerivativeIncrement` | `complex_derivative_at(f, c, l) ⇔ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀z. &0 < \|z − c\| ∧ \|z − c\| < δ ⇒ \|f(z) − f(c) − l * (z − c)\| < ε * \|z − c\|` |
| `DerivativeCaratheodory` | `complex_derivative_at(f, c, l) ⇔ ∃φ. (∀z. f(z) − f(c) = φ(z) * (z − c)) ∧ complex_continuous_at(φ, c) ∧ φ(c) = l` |
| `DerivativeContinuous` | `complex_derivative_at(f, c, l) ⇒ complex_continuous_at(f, c)` |
| `DerivativeLocal` | `&0 < d ∧ (∀z. \|z − c\| < d ⇒ f(z) = g(z)) ∧ complex_derivative_at(g, c, l) ⇒ complex_derivative_at(f, c, l)` |
| `DerivativeConst` | `complex_derivative_at(λz. k, c, &0)` |
| `DerivativeId` | `complex_derivative_at(λz. z, c, &1)` |
| `DerivativeAdd` | `complex_derivative_at(f, c, l) ∧ complex_derivative_at(g, c, m) ⇒ complex_derivative_at(λz. f(z) + g(z), c, l + m)` |
| `DerivativeNeg` | `complex_derivative_at(f, c, l) ⇒ complex_derivative_at(λz. −f(z), c, −l)` |
| `DerivativeSub` | `complex_derivative_at(f, c, l) ∧ complex_derivative_at(g, c, m) ⇒ complex_derivative_at(λz. f(z) − g(z), c, l − m)` |
| `DerivativeScale` | `complex_derivative_at(f, c, l) ⇒ complex_derivative_at(λz. k * f(z), c, k * l)` |
| `DerivativeMul` | `complex_derivative_at(f, c, l) ∧ complex_derivative_at(g, c, m) ⇒ complex_derivative_at(λz. f(z) * g(z), c, l * g(c) + f(c) * m)` |
| `DerivativeInv` | `complex_derivative_at(g, c, m) ∧ g(c) ≠ &0 ⇒ complex_derivative_at(λz. complex_inv(g(z)), c, −(m / g(c) ^ 2))` |
| `DerivativeDiv` | `complex_derivative_at(f, c, l) ∧ complex_derivative_at(g, c, m) ∧ g(c) ≠ &0 ⇒ complex_derivative_at(λz. f(z) / g(z), c, (l * g(c) − f(c) * m) / g(c) ^ 2)` |
| `DerivativeChain` | `complex_derivative_at(g, c, m) ∧ complex_derivative_at(f, g(c), l) ⇒ complex_derivative_at(f ∘ g, c, l * m)` |
| `DerivativeInverse` | `complex_continuous_at(g, c) ∧ &0 < d ∧ (∀z. \|z − c\| < d ⇒ f(g(z)) = z) ∧ complex_derivative_at(f, g(c), l) ∧ l ≠ &0 ⇒ complex_derivative_at(g, c, complex_inv(l))` |
| `DerivativePow` | `complex_derivative_at(λz. z ^ n, c, &(&n) * c ^ (n − 1))` |
| `DerivativeFromQuadraticRemainder` | `&0 < d ∧ (∀h. \|h\| < d ⇒ \|f(c + h) − f(c) − L * h\| ≤ K * \|h\|²) ⇒ complex_derivative_at(f, c, L)` |

## Holomorphic functions (holomorphic.go)

Each closure law is the rule for derivatives read at every point of the
set: a holomorphic function is continuous at each point of its set and
on it, holomorphy passes
to subsets, and it is kept by constants, the identity, sums, differences, negatives, products,
powers, inverses away from zero, quotients and composition into a set
where the outer function is holomorphic. Since a derivative sees only a
disc about its point, on an open set a function equal to a holomorphic
one is holomorphic; finite sums keep holomorphy, by induction on the
index set.

| member | statement |
|---|---|
| `HolomorphicOnContinuous` | `holomorphic_on(s, f) ⇒ complex_continuous_on(s, f)` |
| `HolomorphicOnContinuousAt` | `holomorphic_on(s, f) ∧ z ∈ s ⇒ complex_continuous_at(f, z)` |
| `HolomorphicOnSubset` | `holomorphic_on(s, f) ∧ t ⊆ s ⇒ holomorphic_on(t, f)` |
| `HolomorphicOnAgree` | `s ∈ complex_topology ∧ holomorphic_on(s, h) ∧ (∀z. z ∈ s ⇒ f(z) = h(z)) ⇒ holomorphic_on(s, f)` |
| `HolomorphicOnConst` | `holomorphic_on(s, λz. k)` |
| `HolomorphicOnId` | `holomorphic_on(s, λz. z)` |
| `HolomorphicOnAdd` | `holomorphic_on(s, f) ∧ holomorphic_on(s, g) ⇒ holomorphic_on(s, λz. f(z) + g(z))` |
| `HolomorphicOnSub` | `holomorphic_on(s, f) ∧ holomorphic_on(s, g) ⇒ holomorphic_on(s, λz. f(z) − g(z))` |
| `HolomorphicOnNeg` | `holomorphic_on(s, f) ⇒ holomorphic_on(s, λz. −f(z))` |
| `HolomorphicOnSum` | `finite(I) ∧ (∀i. i ∈ I ⇒ holomorphic_on(s, F(i))) ⇒ holomorphic_on(s, λz. Σ_{i∈I} F(i, z))` |
| `HolomorphicOnMul` | `holomorphic_on(s, f) ∧ holomorphic_on(s, g) ⇒ holomorphic_on(s, λz. f(z) * g(z))` |
| `HolomorphicOnPow` | `holomorphic_on(s, f) ⇒ holomorphic_on(s, λz. f(z) ^ n)` |
| `HolomorphicOnInv` | `holomorphic_on(s, f) ∧ (∀z. z ∈ s ⇒ f(z) ≠ &0) ⇒ holomorphic_on(s, λz. complex_inv(f(z)))` |
| `HolomorphicOnDiv` | `holomorphic_on(s, f) ∧ holomorphic_on(s, g) ∧ (∀z. z ∈ s ⇒ g(z) ≠ &0) ⇒ holomorphic_on(s, λz. f(z) / g(z))` |
| `HolomorphicOnCompose` | `holomorphic_on(s, g) ∧ holomorphic_on(t, f) ∧ (∀z. z ∈ s ⇒ g(z) ∈ t) ⇒ holomorphic_on(s, f ∘ g)` |

## Along a real line (lines.go)

A line of ℂ is t ↦ z + t·w with t real. A function continuous at a point
of a line is continuous along it, part by part: the reals keep their own
distance in ℂ and a part of a difference is at most its modulus, so one
radius serves both parts. A function with complex derivative l at
z + t₀·w has, along the line, velocity l·w at t₀ — real and imaginary
parts with real derivatives re(l·w) and im(l·w): Carathéodory's slope φ, read
along the line, factors the increment as φ(ζ(t))·w·(t − t₀), and since
t − t₀ is real each part of it is that part of φ(ζ(t))·w times t − t₀.
At w = 1 and w = i through c this gives the Cauchy–Riemann equations in
complex form: f has velocity l along the horizontal line and i·l along
the vertical one, ∂f/∂y = i·∂f/∂x; with u = re f and v = im f,
∂u/∂x = re l = ∂v/∂y and ∂v/∂x = im l = −∂u/∂y, since i·l has parts
−im l and re l. On a convex set where f has derivative 0, the segment between two of its points stays in it, both parts of f have derivative 0 along it, and so f takes one value there. A disc is convex — the point at t of a segment is at most (1 − t)·|u − c| + t·|v − c| from the centre — so f is constant on a disc where its derivative is 0. Conversely, partial derivatives on a disc about c that are
continuous at c and satisfy the Cauchy–Riemann equations there give the
complex derivative ux(c) + i·vx(c): walking from c to z along the
horizontal line and then the vertical one, each part moves on each step
by its partial at c times the step, to within η times the step, by the
mean value inequality, and with the equations at c the error
f(z) − f(c) − l·(z − c) is at most 4η|z − c|.

| member | statement |
|---|---|
| `ContinuousAlongLine` | `complex_continuous_at(g, z + &t₀ * w) ⇒ real_continuous_at(λt. re(g(z + &t * w)), t₀) ∧ real_continuous_at(λt. im(g(z + &t * w)), t₀)` |
| `DerivativeAlongLine` | `complex_derivative_at(f, z + &t₀ * w, l) ⇒ path_derivative_at(λt. f(z + &t * w), t₀, l * w)` |
| `CauchyRiemann` | `complex_derivative_at(f, c, l) ⇒ path_derivative_at(λt. f(c + &t), &0, l) ∧ path_derivative_at(λt. f(c + complex_i * &t), &0, complex_i * l)` |
| `DerivativeZeroConstantOnConvex` | `(∀u v t. u ∈ U ∧ v ∈ U ∧ &0 ≤ t ∧ t ≤ &1 ⇒ u + &t * (v − u) ∈ U) ∧ (∀u. u ∈ U ⇒ complex_derivative_at(f, u, &0)) ∧ z ∈ U ∧ w ∈ U ⇒ f(z) = f(w)` |
| `DerivativeZeroConstant` | `(∀w. \|w − c\| < r ⇒ complex_derivative_at(f, w, &0)) ∧ \|z − c\| < r ⇒ f(z) = f(c)` |
| `CauchyRiemannConverse` | `&0 < r ∧ (∀z. \|z − c\| < r ⇒ real_derivative_at(λt. re(f(z + &t)), &0, ux(z))) ∧ …` (uy, vx, vy alike) `∧ complex_continuous_at(λz. &(ux(z)), c) ∧ …` (uy, vx, vy) `∧ ux(c) = vy(c) ∧ uy(c) = −vx(c) ⇒ complex_derivative_at(f, c, &(ux(c)) + complex_i * &(vx(c)))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
