# vec_integral — the integral over ℝⁿ of continuous functions of rapid decay: Fubini, the changes of variables, the integral of a partial derivative and of a product, and radial integrals with the Gaussian

The integral over ℝⁿ is the iterated integral, one coordinate at a time:
`vec_integral⟨n⟩(g)` is the value at the zero vector for n = 0, and for
n + 1 the Lebesgue integral over t of the integral over ℝⁿ of the slice
x ↦ g(«append»(x, t)), t put at coordinate n. The definition is a number
for every g; the functions it is meant for are the continuous ones of
rapid decay, every power of 1 + ⟪x, x⟫ times |g| bounded, written
`«rapid»(n, g)` (the family's table). For those every slice integral is
again continuous and of rapid decay in the last coordinate, and Lebesgue
integrable, so the iterated integral is linear and monotone. The continuous
functions with compact support, written `«Cc»(n, g)`, are among them
(CcRapid), and for those each one-variable integral is a Riemann integral
over an interval holding the support, by `LebesgueIntegralInterval` of
real/lebesgue_riemann. No measure on ℝⁿ is built. Two
laws ask nothing of the integrand, the Lebesgue integral of a multiple
being the multiple of the integral at every function: the integral of a
multiple (IntegralScale) and the integral of a product of functions of
separate coordinates, the product of their integrals (IntegralProduct).

The order of integration is the definition's, the last coordinates
outermost; IntegralSplit groups it into blocks with no hypothesis at all,
and Fubini, the other order, is where continuity and decay are spent: the
compactly supported case by double Riemann sums, a function of rapid decay
as the limit of its cutoffs. Permuting
coordinates, translating and scaling one coordinate are then
one-variable substitutions inside an iterated integral, and Gaussian
elimination makes every invertible linear change of variables a product
of them, the integral multiplied by the absolute value of the
determinant. A diffeomorphism near a point is a linear map followed by
two maps that each change one coordinate, which the induction on the
dimension handles slice by slice; a partition of unity puts the pieces
together, for functions with compact support in the image. The integral
of a partial derivative of a function of class C¹ is 0 when the function
and that derivative decrease rapidly, the fundamental theorem of calculus
in the innermost integral: integration by parts with no boundary term.
Polar coordinates in the plane, and an induction that splits off one plane
at a time, give the integral of a function of the squared norm over
ℝ²ⁿ⁺², a one-variable integral against sⁿ with the constant πⁿ⁺¹/n!. The
Gaussian integral over ℝⁿ is the n-th power of the line's, which is √π
(real/lebesgue_riemann).

## The integral (integral.go)

| member | statement |
|---|---|
| `IntegralCongruence` | `(∀x. vec⟨n⟩(x) ⇒ g(x) = h(x)) ⇒ vec_integral⟨n⟩(g) = vec_integral⟨n⟩(h)` — card |
| `IntegralSliceContinuous` | `«Cc»(n + 1, g) ⇒` every slice is `«Cc»(n, …)`, and the slice integral is continuous in t and 0 for \|t\| large — card |
| `InnerIntegralContinuous` | `«Cc»(n + m, g) ⇒ «Cc»(m, λy. vec_integral⟨n⟩(λx. g(«join»(x, y))))` — card |
| `IntegralBound` | `&0 ≤ R`, \|g\| ≤ B on ℝⁿ, g zero off ⟦−R, R⟧ⁿ `⇒ \|vec_integral⟨n⟩(g)\| ≤ B * (&2 * R) ^ n` — card |
| `IntegralAdd` | `«rapid»(n, g) ∧ «rapid»(n, h) ⇒ vec_integral⟨n⟩(λx. g(x) + h(x)) = vec_integral⟨n⟩(g) + vec_integral⟨n⟩(h)` — card |
| `IntegralScale` | `vec_integral⟨n⟩(λx. a * g(x)) = a * vec_integral⟨n⟩(g)`, for every g — card |
| `IntegralSum` | each h(i), i < N, `«rapid»` `⇒ vec_integral⟨n⟩(λx. Σ_{i<N} h(i)(x)) = Σ_{i<N} vec_integral⟨n⟩(h(i))` — card |
| `IntegralMono` | `«rapid»(n, g) ∧ «rapid»(n, h)`, g ≤ h on ℝⁿ `⇒ vec_integral⟨n⟩(g) ≤ vec_integral⟨n⟩(h)` — card |
| `CcRapid` | `«Cc»(n, g) ⇒ «rapid»(n, g)` |
| `RapidSliceIntegral` | `«rapid»(n + 1, g) ⇒` every slice is `«rapid»(n, …)`, and the slice integral is continuous, of rapid decay and Lebesgue integrable in t — card |
| `RapidInnerIntegral` | `«rapid»(n + m, g) ⇒ «rapid»(m, λy. vec_integral⟨n⟩(λx. g(«join»(x, y))))` — card |
| `IntegralProduct` | `vec_integral⟨n⟩(λx. Π_{i<n} φ(i, x(i))) = Π_{i<n} lebesgue_integral(φ(i))`, for every φ — card |

## Fubini and the linear changes of variables (fubini.go)

| member | statement |
|---|---|
| `IntegralSplit` | `vec_integral⟨n + m⟩(g) = vec_integral⟨m⟩(λy. vec_integral⟨n⟩(λx. g(«join»(x, y))))` — card |
| `Fubini` | `«rapid»(n + m, g) ⇒ vec_integral⟨n + m⟩(g) = vec_integral⟨n⟩(λx. vec_integral⟨m⟩(λy. g(«join»(x, y))))` — card |
| `IntegralPermuteCoordinates` | `«rapid»(n, g) ∧ p ∈ symmetric_group({i \| i < n}) ⇒ vec_integral⟨n⟩(λx. g(λi. x(permutation_map(p, i)))) = vec_integral⟨n⟩(g)` — card |
| `IntegralTranslate` | `«rapid»(n, g) ∧ vec⟨n⟩(a) ⇒ vec_integral⟨n⟩(λx. g(x + a)) = vec_integral⟨n⟩(g)` — card |
| `IntegralLinearChange` | `«rapid»(n, g)`, L linear on ℝⁿ with `determinant(real_ring, n, matrix_of(n, L)) ≠ &0`: `vec_integral⟨n⟩(λx. g(L(x)) * \|determinant(real_ring, n, matrix_of(n, L))\|) = vec_integral⟨n⟩(g)` — card |

## The change of variables (change_of_variables.go)

| member | statement |
|---|---|
| `ChangeOfVariablesLocal` | for a diffeomorphism φ of U onto V, open, each `a ∈ U` has an open W ⊆ U about it where the change of variables holds for every continuous g with compact support in `image(φ, W)` — card |
| `ChangeOfVariables` | φ a diffeomorphism of U onto V, open, g continuous with `vec_compactly_supported_in⟨n⟩(V, g)` `⇒ vec_integral⟨n⟩(λx. COND(x ∈ U, g(φ(x)) * \|vec_jacobian_determinant⟨n⟩(φ, x)\|, &0)) = vec_integral⟨n⟩(g)` — card |
| `IntegralPartialZero` | g of class C¹ on ℝⁿ, `«rapid»(n, g) ∧ «rapid»(n, partial_derivative(g, j)) ∧ j < n ⇒ vec_integral⟨n⟩(partial_derivative(g, j)) = &0` — card |

## Radial integrals and the Gaussian (radial.go)

| member | statement |
|---|---|
| `PolarCoordinates` | g continuous on the plane, zero from radius R: `vec_integral⟨2⟩(g) = real_integral(λr. r * real_integral(λθ. g(«polar»(r, θ)), -π, π), &0, R)` — card |
| `EvenRadialIntegral` | ψ continuous on the nonnegative reals, zero from R: `vec_integral⟨2 * n + 2⟩(λy. ψ(⟪y, y⟫_(2 * n + 2))) = π ^ (n + 1) / &factorial(n) * real_integral(λs. ψ(s) * s ^ n, &0, R)` — card |
| `GaussianIntegral` | `vec_integral⟨n⟩(λx. exp(−Σ_{i<n} x(i)²)) = √π ^ n` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
