# inverse_function — the implicit function theorem in block form, the inverse function theorem as its corollary, and Lagrange multipliers

An equation F(x, y) = 0 between x in ℝⁿ and y in ℝᵐ, with F(a, b) = 0,
defines y as a function of x near a when F's derivative in y at (a, b)
is invertible. The variables stay in their two blocks. In y, F has near
(a, b) the derivative `Dy(x, y)` of y ↦ F(x, y), a map of ℝᵐ into itself
continuous at (a, b) in the operator norm,
`vec_op_norm⟨m, m⟩(λv. Dy(x, y, v) − Dy(a, b, v)) ≤ ε` near (a, b); the inverse of
`Dy(a, b)` is a linear map K with `vec_inverse_on⟨m⟩(Dy(a, b), K)`. In x
only the slice x ↦ F(x, b) is asked for a derivative, `Lx` from ℝⁿ to
ℝᵐ, and only at a. The solution g is the fixed point of
T(y) = y − K(F(x, y)), a contraction for x near a by the mean value
inequality, and its derivative at a is −K∘Lx. The inverse function
theorem is the case F(x, y) = f(y) − x.

## The contraction (contraction.go)

T fixes every zero of F(x, ·), K being linear. Near (a, b) it is
κ-Lipschitz for every κ > 0: along a segment in the ball (an open ball is convex,
`euclidean.SegmentInBall`) its
derivative u ↦ K(Dy(a, b)(u) − Dy(x, v)(u)) is stretched by at most
‖K‖ times the operator norm of Dy(x, v) − Dy(a, b), which the continuity
of Dy makes small, so its operator norm is at most κ
(`euclidean.OpNormLessEqIff`); the mean value inequality does the rest.

| member | statement |
|---|---|
| `ZeroIsFixedPoint` | `vec_linear(K) ∧ F(x, y) = vec_zero ⇒ y − K(F(x, y)) = y` |
| `ImplicitLipschitz` | `vec⟨n⟩(a) ∧ vec⟨m⟩(b) ∧ &0 < r ∧` F carries ℝⁿ × ℝᵐ into ℝᵐ `∧` Dy, its derivative in y near (a, b), continuous at (a, b) `∧ vec_inverse_on⟨m⟩(Dy(a, b), K) ∧ &0 < κ ⇒ ∃δ. &0 < δ ∧ ∀x y z.` (n- and m-vectors within δ of a, b) `‖y − K(F(x, y)) − (z − K(F(x, z)))‖_m ≤ κ * ‖y − z‖_m` |

## The solution (solution.go)

For x near a, T halves distances within δ of b (`ImplicitLipschitz` at
κ = 1/2); σ = δ/2 puts the closed σ-ball M about b inside that open
δ-ball. T moves b by K(F(x, b)), less than σ/2, so it maps M, complete
as a closed ball of ℝᵐ (`euclidean_topology.ClosedBallComplete`), into
itself; Banach's theorem gives its one fixed point g(x), a zero of
F(x, ·) because K is one-to-one on ℝᵐ (`vec_derivative.InverseInjective`),
and the triangle inequality through T(b) gives ‖g(x) − b‖ ≤ 2‖K(F(x, b))‖.
A zero of F(x, ·) within σ of b is a fixed point of T in M
(`ZeroIsFixedPoint`), so it is g(x).

| member | statement |
|---|---|
| `ImplicitSolution` | ImplicitLipschitz's hypotheses but `&0 < κ`, `∧ F(a, b) = vec_zero ∧` ‖F(x, b)‖_m below every ε > 0 for x near a `⇒ ∃ρ σ g. &0 < ρ ∧ &0 < σ ∧ g(a) = b ∧` for x within ρ of a, g(x) is an m-vector within σ of b with `F(x, g(x)) = vec_zero` and `‖g(x) − b‖_m ≤ &2 * ‖K(F(x, b))‖_m`, `∧` every zero of F(x, ·) within σ of b is g(x) |

## The theorem (theorem.go)

g(x) − b differs from K(F(a, b)) − K(F(x, b)) by T(g(x)) − T(b), at most
κ times the linearly growing ‖g(x) − b‖, for every κ. So g has the
derivative of x ↦ −K(F(x, b)), which is −K ∘ Lx: a map whose increments
agree with another's to first order has its derivative
(`vec_derivative.VecDerivativeTangent`). The inverse
function theorem is the case F(x, y) = f(y) − x at (f(a), a): y ↦ f(y) − x
has f's derivative and x ↦ f(a) − x the derivative −id, so the inverse
has the derivative −K ∘ (−id) = K.

| member | statement |
|---|---|
| `ImplicitFunction` | `vec⟨n⟩(a) ∧ vec⟨m⟩(b) ∧ &0 < r ∧ F(a, b) = vec_zero ∧` F carries ℝⁿ × ℝᵐ into ℝᵐ `∧` Dy, its derivative in y near (a, b), continuous at (a, b) `∧ vec_derivative_at⟨n, m⟩(λu. F(u, b), a, Lx) ∧ vec_inverse_on⟨m⟩(Dy(a, b), K) ⇒ ∃ρ σ g. &0 < ρ ∧ &0 < σ ∧ g(a) = b ∧` g(x) the zero of F(x, ·) within σ of b for x within ρ of a, the only one there, `∧ vec_derivative_at⟨n, m⟩(g, a, λu. −K(Lx(u)))` |
| `InverseFunction` | `vec⟨n⟩(a) ∧ &0 < r ∧` f carries ℝⁿ into ℝⁿ `∧` D(y), f's derivative near a, continuous at a `∧ vec_inverse_on⟨n⟩(D(a), K) ⇒ ∃ρ σ g. &0 < ρ ∧ &0 < σ ∧ g(f(a)) = a ∧` for x within ρ of f(a), g(x) is an n-vector within σ of a with f(g(x)) = x, the only solution of f(y) = x there, `∧ vec_derivative_at⟨n, n⟩(g, f(a), K)` |

## Lagrange multipliers (lagrange.go)

At a minimum (a, b) of f on the zeros of G, where G's derivative Dy(a, b)
in y is invertible with inverse K, the gradients p and q of f are one
multiplier μ ∈ ℝᵐ read through G's derivatives Lx and Dy(a, b). μ is the
adjoint of K at q (dot's `adjoint`), so ⟪q, K(w)⟫ = ⟪μ, w⟫ on ℝᵐ, and the
y-equation is that identity at w = Dy(a, b)(v), K undoing Dy(a, b). For
the x-equation, `ImplicitFunction` gives the solution g of G(x, y) = 0
near a, with the derivative −K ∘ Lx. Along each line through a (`euclidean.LineThroughPoint`),
t ↦ f(a + t•u, g(a + t•u)) has the derivative ⟪p, u⟫ − ⟪μ, Lx(u)⟫ at 0,
by the chain rule on the graph of g (`GraphDerivativeAlongLine`: the
joint first-order estimate of f at (x, g(x)), g's estimate, and its
linear growth add up to ε‖x − a‖ at the tolerance $\frac{\varepsilon}{2 + \lVert L \rVert + \lVert q \rVert}$, ‖L‖ the operator norm).
Since g is continuous at a, f is least there at t = 0, so that
derivative vanishes (`real_derivative.LocalMinDerivativeZero`).

| member | statement |
|---|---|
| `GraphDerivativeAlongLine` | f has the gradients p, q at (a, b) `∧ vec_derivative_at⟨n, m⟩(g, a, L) ∧ g(a) = b ∧ &0 < ρ ∧` g carries the n-vectors within ρ of a to m-vectors `∧ vec⟨n⟩(u) ⇒ real_derivative_at(λt. f(a + t • u, g(a + t • u)), &0, ⟪p, u⟫_n + ⟪q, L(u)⟫_m)` |
| `LagrangeMultiplier` | ImplicitFunction's hypotheses at F = G `∧` f has the gradients p, q at (a, b) `∧` (a, b) is a local minimum of f on G = 0 `⇒ ∃μ. vec⟨m⟩(μ) ∧ (∀u. vec⟨n⟩(u) ⇒ ⟪p, u⟫_n = ⟪μ, Lx(u)⟫_m) ∧ (∀v. vec⟨m⟩(v) ⇒ ⟪q, v⟫_m = ⟪μ, Dy(a, b, v)⟫_m)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
