# vec_smooth — smooth functions on open sets of ℝⁿ: the partial derivative as a function, the classes Cᵏ, smooth maps, the Jacobian, diffeomorphisms and the inverse function theorem, bump functions and partitions of unity

vec_derivative states derivatives as relations: `partial_derivative_at(f, j, c, d)`
says the number d is f's partial derivative at c along coordinate j. To
speak of a function all of whose derivatives exist, the derivative has to
be a function again, so this chapter names it: `partial_derivative(f, j)`
is ∂ⱼf, the d of the relation at each point where there is one
(PartialDerivativeDef), and where there is none an unspecified real.

A real function g on ℝⁿ is of class Cᵏ on a set U,
`vec_continuously_differentiable_on⟨n⟩(U, k, g)`, by recursion on k: class 0
is continuity at the points of U; class k + 1 asks continuity, every
partial derivative at every point of U, and each ∂ⱼg of class k. It is
smooth on U, `vec_smooth_on⟨n⟩(U, g)`, when it is of every class. A map
f of ℝⁿ into ℝᵐ is smooth on U, `vec_smooth_map_on⟨n, m⟩(U, f)`, when it
carries U into ℝᵐ and its coordinates are smooth; a diffeomorphism of U
onto V, `vec_diffeomorphic_map⟨n⟩(U, V, f)`, is a smooth bijection with a
smooth inverse. The Jacobian matrix `vec_jacobian_matrix⟨n, m⟩(f, x)` holds
the partial derivatives ∂ⱼfᵢ(x), and `vec_jacobian_determinant⟨n⟩(f, x)` is
its determinant at `real_ring`. A function has compact support in U,
`vec_compactly_supported_in⟨n⟩(U, g)`, when it vanishes at every n-vector
off a compact subset of U.

Every closure property is an induction on the class for all functions at
once: the partial derivatives of a sum, a product or a composite are built
by the sum, product and chain rules from those of the parts, one class
lower. A smooth function is smooth after composing with a function of one
variable that has derivatives of every order, stated as the corpus states
higher derivatives, a sequence D(0), D(1), … each the derivative of the one
before; reciprocals and square roots are instances. The inverse function
theorem comes from vector/inverse_function's, the inverse's Jacobian being
the inverse of the map's and so as smooth as the map. The bump functions
are built from one function of one variable, 0 up to 0 and $e^{-1/t}$ after;
the partitions of unity on a compact set from finitely many bumps, by the
product trick that needs no division.

## The partial derivative as a function (partials.go)

| member | statement |
|---|---|
| `PartialDerivativeValue` | `partial_derivative_at(f, j, c, d) ⇒ partial_derivative(f, j, c) = d` |
| `PartialDerivativeLocal` | f = g at the n-vectors within r of c `⇒` the same partial derivatives at c along j < n |
| `PartialDerivativeAdd` | `partial_derivative_at(f, j, c, a) ∧ partial_derivative_at(g, j, c, b) ⇒ partial_derivative_at(λx. f(x) + g(x), j, c, a + b)` — card |
| `PartialDerivativeMul` | the same `⇒ partial_derivative_at(λx. f(x) * g(x), j, c, a * g(c) + f(c) * b)` — card |
| `PartialDerivativeChain` | for f's coordinates of class C¹ on U open, carrying U into V open, and g of class C¹ on V: `partial_derivative_at(λy. g(f(y)), j, x, Σ_{i<m} partial_derivative(g, i, f(x)) * partial_derivative(λy. f(y)(i), j, x))` — card |
| `PartialDerivativeSymmetric` | g of class C² on U open: `partial_derivative(partial_derivative(g, i), j, x) = partial_derivative(partial_derivative(g, j), i, x)` — card |

## The classes Cᵏ (classes.go)

| member | statement |
|---|---|
| `ContinuouslyDifferentiableMono` | `j ≤ k ∧ vec_continuously_differentiable_on⟨n⟩(U, k, g) ⇒ vec_continuously_differentiable_on⟨n⟩(U, j, g)` — card |
| `ContinuouslyDifferentiableSubset` | `V ⊆ U` and class k on U `⇒` class k on V — card |
| `ContinuouslyDifferentiableCongruence` | on U open, g = h on U and g of class k `⇒` h of class k |
| `ContinuouslyDifferentiableAdd` | on U open, g and h of class k `⇒` g + h of class k — card |
| `ContinuouslyDifferentiableSum` | on U open, each h(i), i < N, of class k `⇒` `λx. Σ_{i<N} h(i)(x)` of class k — card |
| `ContinuouslyDifferentiableMul` | on U open, g and h of class k `⇒` g·h of class k — card |
| `ContinuouslyDifferentiableCompose` | f's coordinates of class k on U open, carrying U into V open, g of class k on V `⇒` g ∘ f of class k on U — card |
| `ContinuouslyDifferentiableLocallyLipschitz` | an ℝᵐ-valued map with C¹ coordinates on open U ⊆ ℝⁿ is locally Lipschitz on U — card |

A C¹ map with values in ℝᵐ is Lipschitz on a sufficiently small
open neighbourhood of each point of its open domain. This is the
bridge from the smooth classes to local Lipschitz image theorems.

## Smooth functions (smooth.go)

| member | statement |
|---|---|
| `SmoothConst` | `U ⊆ {u \| vec⟨n⟩(u)} ⇒ vec_smooth_on⟨n⟩(U, λx. a)` — card |
| `SmoothCoordinate` | `U ⊆ {u \| vec⟨n⟩(u)} ⇒ vec_smooth_on⟨n⟩(U, λx. x(i))` — card |
| `SmoothAdd`, `SmoothSub`, `SmoothMul` | on U open, g and h smooth `⇒` g + h, g − h, g·h smooth — cards |
| `SmoothSum` | on U open, each h(i), i < N, smooth `⇒` their sum smooth — card |
| `SmoothCompose` | `vec_smooth_map_on⟨n, m⟩(U, f)` carrying U into V, g smooth on V, U and V open `⇒ vec_smooth_on⟨n⟩(U, λx. g(f(x)))` — card |
| `SmoothMapCompose` | the same for maps: `vec_smooth_map_on⟨n, k⟩(U, h ∘ f)` — card |
| `SmoothComposeReal` | D(k + 1) the derivative of D(k) on an open set s of ℝ holding g(U), g smooth on U open `⇒ vec_smooth_on⟨n⟩(U, λx. D(0)(g(x)))` — card |
| `SmoothReciprocal` | g smooth without zeros on U open `⇒ vec_smooth_on⟨n⟩(U, λx. &1 / g(x))` — card |
| `SmoothSqrt` | g smooth and positive on U open `⇒ vec_smooth_on⟨n⟩(U, λx. real_sqrt(g(x)))` — card |
| `SmoothSubset` | `V ⊆ U ∧ vec_smooth_on⟨n⟩(U, g) ⇒ vec_smooth_on⟨n⟩(V, g)` — card |
| `SmoothLocal` | U open, each point of U in an open V ⊆ U with g smooth on V `⇒ vec_smooth_on⟨n⟩(U, g)` — card |
| `SmoothPartial` | `vec_smooth_on⟨n⟩(U, g) ∧ j < n ⇒ vec_smooth_on⟨n⟩(U, partial_derivative(g, j))`, and it is the partial derivative at every point of U — card |
| `LinearSmoothMap` | L linear, carrying ℝⁿ into ℝᵐ, `U ⊆ {u \| vec⟨n⟩(u)} ⇒ vec_smooth_map_on⟨n, m⟩(U, L)` with `vec_jacobian_matrix⟨n, m⟩(L, x) = matrix_of(n, L)` on U — card |

## The Jacobian and diffeomorphisms (jacobian.go)

| member | statement |
|---|---|
| `JacobianDerivative` | f's coordinates of class C¹ on U open, `x ∈ U ⇒ vec_derivative_at⟨n, m⟩(f, x, matrix_act⟨n⟩(vec_jacobian_matrix⟨n, m⟩(f, x)))` — card |
| `JacobianChain` | for smooth maps f on U into V and h on V: `vec_jacobian_matrix⟨n, k⟩(h ∘ f, x) = matrix_mul(m, vec_jacobian_matrix⟨m, k⟩(h, f(x)), vec_jacobian_matrix⟨n, m⟩(f, x))` — card |
| `JacobianDeterminantChain` | the same at n = m = k: `vec_jacobian_determinant⟨n⟩(h ∘ f, x) = vec_jacobian_determinant⟨n⟩(h, f(x)) * vec_jacobian_determinant⟨n⟩(f, x)` — card |
| `DiffeomorphismJacobianNonzero` | `vec_diffeomorphic_map⟨n⟩(U, V, f)`, U and V open, `x ∈ U ⇒ vec_jacobian_determinant⟨n⟩(f, x) ≠ &0` — card |
| `DiffeomorphismInverse` | `vec_diffeomorphic_map⟨n⟩(U, V, f) ⇒ ∃g. vec_diffeomorphic_map⟨n⟩(V, U, g)` inverse to f — card |
| `SmoothInverseFunction` | `vec_smooth_map_on⟨n, n⟩(U, f)`, U open, `a ∈ U`, `vec_jacobian_determinant⟨n⟩(f, a) ≠ &0 ⇒ ∃V W.` open, `a ∈ V ⊆ U ∧ vec_diffeomorphic_map⟨n⟩(V, W, f)` — card |

## Bump functions and partitions of unity (bump.go)

| member | statement |
|---|---|
| `FlatFunctionSmooth` | t ↦ 0 for t ≤ 0, exp(−1/t) for t > 0, has a derivative D(k + 1) of each D(k) at every real — card |
| `BumpFunction` | `vec⟨n⟩(c) ∧ &0 < r ∧ r < R ⇒ ∃φ.` smooth on ℝⁿ, between 0 and 1, 1 within r of c and 0 from R — card |
| `SmoothPartitionOfUnity` | K compact, covered by open sets c `⇒ ∃N ψ.` each ψ(i) smooth, nonnegative, with compact support in a member of c, `Σ_{i<N} ψ(i)(x) ≤ &1` on ℝⁿ and `= &1` on K — card |
| `SmoothPartitionOfUnityOpen` | two open sets covering U admit a nonnegative smooth partition whose relative supports lie in the respective sets — card |

For two open sets V and W, the partition on U = V ∪ W is smooth on
all of U and sums to one there. Its two supports are closed relative
to U and contained in V and W respectively; they need not be compact
or closed in all of ℝⁿ. This is the support condition used to extend
forms by zero across an open-cover overlap.

## Integrals in a parameter and Hadamard's lemma (parameter_integral.go)

| member | statement |
|---|---|
| `PartialDerivativeUnderIntegral` | H of class C¹ on W open in ℝⁿ⁺¹ holding every `«append»(y, t)` with y ∈ U open, t ∈ ⟦0, 1⟧, `j < n`, `x ∈ U ⇒` the integral over ⟦0, 1⟧ has the integral of ∂ⱼH for its partial derivative at x — card |
| `SmoothParameterIntegral` | the same with H smooth `⇒ vec_smooth_on⟨n⟩(U, λy. real_integral(λt. H(«append»(y, t)), &0, &1))` — card |
| `Hadamard` | U open and convex, `a ∈ U`, g smooth on U `⇒ ∃h.` each h(j) smooth with `h(j)(a) = partial_derivative(g, j, a)` and `g(x) = g(a) + Σ_{j<n} (x(j) - a(j)) * h(j)(x)` on U — card |

## Matrix families (matrix.go)

The determinant and adjugate entries are polynomials in the active matrix
entries. A nowhere-zero determinant makes the cofactor inverse smooth by
`SmoothReciprocal`. The size is fixed and entries outside the active block
are not read; inactive entries of the adjugate and inverse are constant zero.

| Member | Statement |
|---|---|
| `SmoothDeterminant` | A matrix family with smooth active entries has smooth determinant — card |
| `SmoothAdjugate` | Every entry of its adjugate is smooth — card |
| `SmoothMatrixInverse` | Every entry of the cofactor inverse is smooth where the determinant is nowhere zero — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
