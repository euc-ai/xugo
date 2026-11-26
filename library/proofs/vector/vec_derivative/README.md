# vec_derivative — the derivative of a map from ℝⁿ to ℝᵐ, partial derivatives, and the symmetry of mixed partials

A map `f` from ℝⁿ to ℝᵐ has the linear map `L` as its derivative at a
point `c` of ℝⁿ — the Fréchet derivative — when its increment is `L`
applied to the step, up to an error small against the step:

`vec_derivative_at⟨n, m⟩(f, c, L) ⇔ vec⟨n⟩(c) ∧ vec_linear(L) ∧ L carries ℝⁿ into ℝᵐ ∧ ∀ε > 0 ∃δ > 0. ‖x − c‖_n < δ ⇒ ‖f(x) − f(c) − L(x − c)‖_m ≤ ε·‖x − c‖_n`.

As on the line (`real_derivative`), the relation is the object: every
statement names the derivative it is about, and a map with a derivative
at every point of a set names it as a function `D` of the point.
The derivative is a linear map, not a matrix; `L` is read only on ℝⁿ.

A real function on ℝⁿ has a partial derivative `d` at `c` along the
coordinate `j` when `t ↦ f(c + t·e_j)` has derivative `d` at 0:
`partial_derivative_at(f, j, c, d)`. A map into ℝᵐ is read through its
coordinates `λx. f(x)(i)`.

`vec_continuous_at⟨n, m⟩(f, c)` is continuity at a point of ℝⁿ, which a
derivative implies. `vec_inverse_on⟨n⟩(L, K)` says that the linear map K
inverts L on ℝⁿ. The size of a linear map is euclidean's operator norm
`vec_op_norm⟨n, m⟩(L)`, which bounds its stretch (`euclidean.OpNormBound`)
and is at most the total size of its images of the basis
(`euclidean.LinearBasisBound`); continuity of a derivative D at c reads
`vec_op_norm⟨n, m⟩(λv. D(x, v) − D(c, v)) ≤ ε` near c. The facts about linear maps the
rules read — a difference, the zero map, a sum, a multiple and a
composite — are vec_space's, read at ℝ.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `vec_derivative_at⟨n, m⟩(f, c, L)` | f has derivative L at the point c of ℝⁿ |
| `vec_continuous_at⟨n, m⟩(f, c)` | `vec⟨n⟩(c) ∧ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x. vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ ‖f(x) - f(c)‖_m < ε` |
| `partial_derivative_at(f, j, c, d)` | `real_derivative_at(λt. f(c + t • basis_vector(j)), &0, d)` |
| `vec_inverse_on⟨n⟩(L, K)` | `vec_linear(K) ∧ ∀h. vec⟨n⟩(h) ⇒ vec⟨n⟩(K(h)) ∧ K(L(h)) = h ∧ L(K(h)) = h` |

## The derivative and its rules (derivative.go)

Each rule is an ε–δ argument on the definition: the error of the new map
is assembled from the errors of the old ones, the radius is the smallest
of the radii those serve, and the triangle inequality prices the sum. A
linear map that matches a map's increment exactly is its derivative, the
error being zero (`VecDerivativeExactIncrement`); the constant and the
linear rules are that. Near a point where it has a derivative L a
map grows at most at the rate ‖L‖ + 1, ‖L‖ the operator norm
(`VecDerivativeIncrementBound`); continuity and the chain rule read that
bound. The chain rule needs f to carry the n-vectors
near c to m-vectors: g's estimate at f(c) holds only at m-vectors, and
f's derivative constrains only its first m coordinates. The derivative
is unique on ℝⁿ: each coordinate of L(u) is a derivative along a line
(`DirectionalDerivative`), and a real function has one derivative. A map
that inverts another on ℝⁿ is one-to-one there; and a map whose
increments agree with g's to first order at c has g's derivative there,
the triangle inequality adding the two errors.

| member | statement |
|---|---|
| `InverseInjective` | `vec_inverse_on⟨n⟩(L, K) ∧ vec⟨n⟩(u) ∧ vec⟨n⟩(v) ∧ K(u) = K(v) ⇒ u = v` |
| `VecDerivativeUnique` | `vec_derivative_at⟨n, m⟩(f, c, L) ∧ vec_derivative_at⟨n, m⟩(f, c, K) ∧ vec⟨n⟩(u) ⇒ L(u) = K(u)` |
| `VecDerivativeIncrementBound` | `vec_derivative_at⟨n, m⟩(f, c, L) ⇒ ∃δ. &0 < δ ∧ ∀x. vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ ‖f(x) - f(c)‖_m ≤ (vec_op_norm⟨n, m⟩(L) + &1) * ‖x - c‖_n` |
| `VecDerivativeContinuous` | `vec_derivative_at⟨n, m⟩(f, c, L) ⇒ vec_continuous_at⟨n, m⟩(f, c)` |
| `VecDerivativeExactIncrement` | `vec⟨n⟩(c) ∧ vec_linear(L) ∧ (∀u. vec⟨n⟩(u) ⇒ vec⟨m⟩(L(u))) ∧ (∀x. f(x) - f(c) = L(x - c)) ⇒ vec_derivative_at⟨n, m⟩(f, c, L)` |
| `VecDerivativeConst` | `vec⟨n⟩(c) ⇒ vec_derivative_at⟨n, m⟩(λx. k, c, λu. vec_zero)` |
| `VecDerivativeLinear` | `vec⟨n⟩(c) ∧ vec_linear(L) ∧ (∀u. vec⟨n⟩(u) ⇒ vec⟨m⟩(L(u))) ⇒ vec_derivative_at⟨n, m⟩(L, c, L)` |
| `VecDerivativeIdentity` | `vec⟨n⟩(c) ⇒ vec_derivative_at⟨n, n⟩(λu. u, c, λu. u)` — the identity is linear and keeps ℝⁿ (`VecDerivativeLinear`) |
| `VecDerivativeAdd` | `vec_derivative_at⟨n, m⟩(f, c, L) ∧ vec_derivative_at⟨n, m⟩(g, c, K) ⇒ vec_derivative_at⟨n, m⟩(λx. f(x) + g(x), c, λu. L(u) + K(u))` |
| `VecDerivativeScale` | `vec_derivative_at⟨n, m⟩(f, c, L) ⇒ vec_derivative_at⟨n, m⟩(λx. a • f(x), c, λu. a • L(u))` |
| `VecDerivativeNeg` | `vec_derivative_at⟨n, m⟩(f, c, L) ⇒ vec_derivative_at⟨n, m⟩(λx. -f(x), c, λu. -L(u))` |
| `VecDerivativeSub` | `vec_derivative_at⟨n, m⟩(f, c, L) ∧ vec_derivative_at⟨n, m⟩(g, c, K) ⇒ vec_derivative_at⟨n, m⟩(λx. f(x) - g(x), c, λu. L(u) - K(u))` |
| `VecDerivativeLocal` | `&0 < r ∧ (∀x. vec⟨n⟩(x) ∧ ‖x - c‖_n < r ⇒ f(x) = g(x)) ∧ vec_derivative_at⟨n, m⟩(g, c, L) ⇒ vec_derivative_at⟨n, m⟩(f, c, L)` |
| `VecDerivativeTangent` | `vec_derivative_at⟨n, m⟩(g, c, L) ∧ (∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x. vec⟨n⟩(x) ∧ ‖x − c‖_n < δ ⇒ ‖f(x) − f(c) − (g(x) − g(c))‖_m ≤ ε * ‖x − c‖_n) ⇒ vec_derivative_at⟨n, m⟩(f, c, L)` |
| `VecDerivativeChain` | `vec_derivative_at⟨n, m⟩(f, c, L) ∧ vec_derivative_at⟨m, k⟩(g, f(c), K) ∧ &0 < r ∧ (∀x. vec⟨n⟩(x) ∧ ‖x − c‖_n < r ⇒ vec⟨m⟩(f(x))) ⇒ vec_derivative_at⟨n, k⟩(g ∘ f, c, K ∘ L)` |

## Along a line (derivative.go)

Read along any line, the derivative is a one-variable derivative
coordinate by coordinate; uniqueness and the partial derivatives both
come from there. Read against a fixed vector u, the form ⟪u, f⟫ along a line has
derivative ⟪u, L(w)⟫, summand by summand (`DotDerivativeAlongLine`).
Against u = f(y) − f(x) on the segment from x to y, the mean value
theorem and Cauchy–Schwarz give ‖f(y) − f(x)‖ ≤ B·‖y − x‖ wherever the
derivative's operator norm is at most B (`MeanValueInequality`).

| member | statement |
|---|---|
| `DerivativeAlongLine` | `vec_derivative_at⟨n, m⟩(f, x + t₀ • w, L) ∧ vec⟨n⟩(x) ∧ vec⟨n⟩(w) ∧ i < m ⇒ real_derivative_at(λt. f(x + t • w)(i), t₀, L(w)(i))` |
| `DirectionalDerivative` | `vec_derivative_at⟨n, m⟩(f, c, L) ∧ vec⟨n⟩(w) ∧ i < m ⇒ real_derivative_at(λt. f(c + t • w)(i), &0, L(w)(i))` |
| `DotDerivativeAlongLine` | `vec_derivative_at⟨n, m⟩(f, x + t₀ • w, L) ∧ vec⟨n⟩(x) ∧ vec⟨n⟩(w) ⇒ real_derivative_at(λt. ⟪u, f(x + t • w)⟫_m, t₀, ⟪u, L(w)⟫_m)` |
| `MeanValueInequality` | `vec⟨n⟩(x) ∧ vec⟨n⟩(y) ∧ (∀t. &0 ≤ t ∧ t ≤ &1 ⇒ ∃L. vec_derivative_at⟨n, m⟩(f, x + t • (y − x), L) ∧ vec_op_norm⟨n, m⟩(L) ≤ B) ⇒ ‖f(y) − f(x)‖_m ≤ B * ‖y − x‖_n` |

## Partial derivatives (partials.go)

The derivative determines the partial derivatives: each is a coordinate
of L(e_j), the derivative along the line in the direction e_j
(`PartialFromDerivative`). A partial derivative at a point of a
coordinate line is the derivative along that line, read at any parameter
(`PartialAlongLine`). With all partials existing near c and continuous at
c, the increment of a real function on ℝⁿ is ⟪D(c), x − c⟫ to within
ε‖x − c‖: the proof walks from c to x one coordinate at a time and bounds
each step by the mean value inequality against the slope D(c)(k)
(`real_derivative.MeanValueNearSlope`), finitely many radii met in one common radius
(`real_order_ring.CommonRadius`). Applied to each coordinate of a map
into ℝᵐ, this gives the derivative $u \mapsto (⟪D(c)(i), u⟫)_{i<m}$. Mixed
partials agree at c (Schwarz) when they exist on a small square about c
in the plane of e_i and e_j and are continuous at c along that plane:
the second difference
over a small square is h²·Dij(c) to within εh² read along e_i first,
and h²·Dji(c) to within εh² read along e_j first.

| member | statement |
|---|---|
| `PartialAlongLine` | `partial_derivative_at(f, j, x + s • basis_vector(j), d) ⇔ real_derivative_at(λt. f(x + t • basis_vector(j)), s, d)` |
| `PartialFromDerivative` | `vec_derivative_at⟨n, m⟩(f, c, L) ∧ j < n ∧ i < m ⇒ partial_derivative_at(λx. f(x)(i), j, c, L(basis_vector(j))(i))` |
| `ContinuousPartialsIncrement` | `vec⟨n⟩(c) ∧ &0 < r ∧` the partials D(x)(j) of f near c, each continuous at c, `∧ &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x. vec⟨n⟩(x) ∧ ‖x − c‖_n < δ ⇒ \|f(x) − f(c) − ⟪D(c), x − c⟫_n\| ≤ ε * ‖x − c‖_n` |
| `ContinuousPartialsDerivative` | `vec⟨n⟩(c) ∧ &0 < r ∧` the partials D(x)(i)(j) of the coordinates f(·)(i) near c, each continuous at c, `⇒ vec_derivative_at⟨n, m⟩(f, c, λu. λi. COND(i < m, ⟪D(c)(i), u⟫_n, &0))` |
| `MixedPartialsCommute` | `&0 < r ∧` the four partials Di, Dj, Dij, Dji on the square \|s\|, \|t\| < r about c, at «p»(s, t) = c + s·e_i + t·e_j, `∧` Dij, Dji continuous at c `⇒ Dij(c) = Dji(c)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
