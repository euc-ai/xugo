# tauberian — Newman's Tauberian theorem: a Dirichlet series with bounded coefficients converges on the line Re s = 1 where its sum continues holomorphically

If the coefficients a(n) are bounded and the sum F of $\sum a(n) \cdot n^{-s}$ on
Re s > 1 continues holomorphically to an open set containing the closed
half-plane Re s ≥ 1, then the series converges at every point of that
half-plane, to F (`NewmanTauberian`). Nothing is asked of the open set's
shape.

The proof compares F(w) with the partial sum S_N(w) through one contour
integral. For H holomorphic near the contour, the integral of
H(z)·N^z·(1/z + z/R²) round it is 2πi·H(0); the factor
«kernel»(R, z) = 1/z + z/R² has modulus 2|Re z|/R² on the circle
|z| = R, which is what tames the two series bounds. The contour is the
right half of that circle, from −iR to iR, closed on the left by three
sides of the rectangle ⟦−δ, 0⟧ × ⟦−R, R⟧, thin enough for F(· + w) to be
holomorphic on it. The four pieces are integrated one by one and never
joined into a path: a function holomorphic on a convex open set has a
primitive there (`cauchy_integral`), so its integrals over the pieces
telescope, and the integral of 1/z over them is 2πi by two primitives,
log z on the half-circle and log(−z) on the sides. On the right arc
the tail of the series is at most $\frac{B \cdot N^{-x}}{x}$ and the integrand at most
2B/R²; the partial sum is entire, so its left side is the left
half-circle, where the pointwise bound is $2B/R^2 + 2B/(NR)$. On the
rectangle sides N^z is small. Hence, for B > 0, |F(w) − S_N(w)| is
eventually at most 3B/R, for every R > 0 (`NewmanApproximation`).

Besides «kernel», the chapter's table names the pieces the rows read:
«partial»(a, N, s), the N-th partial sum of the Dirichlet series of a
at s; «arcInt»(G, R, a, b), the integral of G along the circle of radius
R about 0 over the parameter interval from a to b; «sides»(R, δ), the
three sides iR → −δ + iR → −δ − iR → −iR, «sidesInt»(G, R, δ), the
integral of G along them, and «box»(R, δ), the closed box
−δ ≤ Re z ≤ R, |Im z| ≤ R that holds the contour; «numerator»(G, R, N)
and «weightedKernel»(G, R, N), G(z)·N^z times 1 + z²/R² and times
«kernel»(R, z). «convex» and «disc», the open disc, are
`cauchy_integral`'s.

## The estimates (estimates.go)

On an arc of the circle |z| = R, a bound
$\lvert G(z) \rvert \le K \cdot N^{-\operatorname{Re} z} / \lvert \operatorname{Re} z \rvert$
off the imaginary axis bounds the integral of «weightedKernel»(G, R, N) by
2K/R times the arc's parameter length (`WeightedKernelArcBound`).

| member | statement |
|---|---|
| `KernelOnCircle` | `∀R:real. ∀z:complex. &0 < R ∧ \|z\| = R ⇒ \|«kernel»(R, z)\| = &2 * \|re(z)\| / (R * R)` |
| `KernelContinuousAt` | `∀R:real. ∀z:complex. z ≠ &0 ⇒ complex_continuous_at(λu:complex. «kernel»(R, u), z)` |
| `ShiftedTermBound` | `∀a:(num → complex). ∀B:real. ∀z w:complex. ∀n:num. \|a(n)\| ≤ B ∧ &1 ≤ re(w) ∧ 0 < n ⇒ \|a(n) * complex_cpow(&n, -(z + w))\| ≤ B * real_rpow(&n, -re(z) - &1)` |
| `TailBoundRight` | `∀a:(num → complex). ∀B:real. ∀z w v:complex. ∀N:num. (∀n:num. \|a(n)\| ≤ B) ∧ &1 ≤ re(w) ∧ &0 < re(z) ∧ 0 < N ∧ dirichlet_sums(a, z + w, v) ⇒ \|v - «partial»(a, N, z + w)\| ≤ B * real_rpow(&N, -re(z)) / re(z)` |
| `HeadBoundLeft` | `∀a:(num → complex). ∀B:real. ∀z w:complex. ∀N:num. (∀n:num. \|a(n)\| ≤ B) ∧ &1 ≤ re(w) ∧ re(z) < &0 ∧ 0 < N ⇒ \|«partial»(a, N, z + w)\| ≤ B * real_rpow(&N, -re(z)) * (&1 / &N + &1 / -re(z))` |
| `WeightedKernelArcBound` | `∀G:(complex → complex). ∀R K α β:real. ∀N:num. &0 < R ∧ &0 ≤ K ∧ 0 < N ∧ α ≤ β ∧ (∀t:real. α ≤ t ∧ t ≤ β ⇒ complex_continuous_at(G, circle_path(&0, R, t)) ∧ (re(circle_path(&0, R, t)) ≠ &0 ⇒ \|G(circle_path(&0, R, t))\| ≤ K * real_rpow(&N, -re(circle_path(&0, R, t))) / \|re(circle_path(&0, R, t))\|)) ⇒ \|«arcInt»(«weightedKernel»(G, R, N), R, α, β)\| ≤ &2 * K * (β - α) / R` |
| `RightArcInBox` | `∀R t:real. &0 < R ∧ -(π / &2) ≤ t ∧ t ≤ π / &2 ⇒ &0 ≤ re(circle_path(&0, R, t)) ∧ re(circle_path(&0, R, t)) ≤ R ∧ \|im(circle_path(&0, R, t))\| ≤ R ∧ circle_path(&0, R, t) ≠ &0` |
| `RightArcBound` | `∀a:(num → complex). ∀B R:real. ∀F:(complex → complex). ∀w:complex. ∀N:num. (∀n:num. \|a(n)\| ≤ B) ∧ &1 ≤ re(w) ∧ &0 < R ∧ 0 < N ∧ (∀z:complex. \|z\| = R ∧ &0 < re(z) ⇒ dirichlet_sums(a, z + w, F(z + w))) ∧ (∀z:complex. \|z\| = R ∧ &0 ≤ re(z) ⇒ complex_continuous_at(F, z + w)) ⇒ \|«arcInt»(«weightedKernel»(λz:complex. F(z + w) - «partial»(a, N, z + w), R, N), R, -(π / &2), π / &2)\| ≤ &2 * π * B / R` |
| `LeftArcBound` | `∀a:(num → complex). ∀B R:real. ∀w:complex. ∀N:num. (∀n:num. \|a(n)\| ≤ B) ∧ &1 ≤ re(w) ∧ &0 < R ∧ 0 < N ⇒ \|«arcInt»(«weightedKernel»(λz:complex. «partial»(a, N, z + w), R, N), R, π / &2, &3 * π / &2)\| ≤ &2 * π * B * (&1 / &N + &1 / R)` |
| `LeftSidesBound` | `∀G:(complex → complex). ∀M R δ:real. ∀N:num. &0 < R ∧ &0 < δ ∧ 2 ≤ N ∧ (∀z:complex. z ∈ «sides»(R, δ) ⇒ complex_continuous_at(G, z) ∧ \|G(z)\| ≤ M) ⇒ \|«sidesInt»(λz:complex. G(z) * complex_cpow(&N, z), R, δ)\| ≤ M * (&2 / log(&N) + &2 * R * real_rpow(&N, -δ))` |

## The contour (contour.go)

In `LeftSidesInBox`, «leftBox»(z) says −δ ≤ Re z ≤ 0, |Im z| ≤ R and
z ≠ 0: every point of the three sides lies there.

| member | statement |
|---|---|
| `LeftSidesInBox` | `∀R δ t:real. &0 < R ∧ &0 < δ ∧ &0 ≤ t ∧ t ≤ &1 ⇒ «leftBox»(segment_path(complex_i * &R, -&δ + complex_i * &R, t)) ∧ «leftBox»(segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R, t)) ∧ «leftBox»(segment_path(-&δ - complex_i * &R, -(complex_i * &R), t))` |
| `ContourInverseIntegral` | `∀R δ:real. &0 < R ∧ &0 < δ ⇒ «arcInt»(λz:complex. complex_inv(z), R, -(π / &2), π / &2) + «sidesInt»(λz:complex. complex_inv(z), R, δ) = &(&2 * π) * complex_i` |
| `ContourFormula` | `∀H:(complex → complex). ∀V:set(complex). ∀R δ:real. &0 < R ∧ &0 < δ ∧ V ∈ complex_topology ∧ «convex»(V) ∧ holomorphic_on(V, H) ∧ (∀z:complex. z ∈ «box»(R, δ) ⇒ z ∈ V) ⇒ «arcInt»(λz:complex. H(z) / z, R, -(π / &2), π / &2) + «sidesInt»(λz:complex. H(z) / z, R, δ) = &(&2 * π) * complex_i * H(&0)` |
| `CircleFormula` | `∀H:(complex → complex). ∀R ρ:real. &0 < R ∧ R < ρ ∧ holomorphic_on(«disc»(complex_of_real(&0), ρ), H) ⇒ «arcInt»(λz:complex. H(z) / z, R, -(π / &2), π / &2) + «arcInt»(λz:complex. H(z) / z, R, π / &2, &3 * π / &2) = &(&2 * π) * complex_i * H(&0)` |

## The theorem (theorem.go)

| member | statement |
|---|---|
| `NewmanSidesBounded` | `∀G:(complex → complex). ∀R δ:real. &0 < R ∧ &0 < δ ∧ (∀z:complex. z ∈ «sides»(R, δ) ⇒ complex_continuous_at(G, z)) ⇒ ∃M:real. ∀z:complex. z ∈ «sides»(R, δ) ⇒ \|G(z)\| ≤ M` |
| `NewmanEventualError` | `∀B M R δ:real. &0 < B ∧ &0 < R ∧ &0 < δ ⇒ ∃K:num. ∀N:num. K ≤ N ⇒ 2 ≤ N ∧ B * (&1 / &N) + M / π * (&1 / log(&N)) + M * R / π * real_rpow(&N, -δ) ≤ B / R` |
| `NewmanWeightedNumerator` | `∀G:(complex → complex). ∀V:set(complex). ∀R:real. ∀N:num. holomorphic_on(V, G) ∧ 0 < N ⇒ holomorphic_on(V, «numerator»(G, R, N)) ∧ «numerator»(G, R, N, complex_of_real(&0)) = G(&0)` |
| `NewmanPathWeight` | `∀G:(complex → complex). ∀R:real. ∀N:num. ∀γ v:(real → complex). ∀l u:real. l ≤ u ∧ (∀t:real. l ≤ t ∧ t ≤ u ⇒ γ(t) ≠ &0) ⇒ path_integral(λz:complex. «numerator»(G, R, N, z) / z, γ, v, l, u) = path_integral(«weightedKernel»(G, R, N), γ, v, l, u)` |
| `NewmanApproximation` | `∀a:(num → complex). ∀B R:real. ∀U:set(complex). ∀F:(complex → complex). ∀w:complex. (∀n:num. \|a(n)\| ≤ B) ∧ &0 < B ∧ U ∈ complex_topology ∧ (∀s:complex. &1 ≤ re(s) ⇒ s ∈ U) ∧ holomorphic_on(U, F) ∧ (∀s:complex. &1 < re(s) ⇒ dirichlet_sums(a, s, F(s))) ∧ &1 ≤ re(w) ∧ &0 < R ⇒ ∃K:num. ∀N:num. K ≤ N ⇒ \|F(w) - «partial»(a, N, w)\| ≤ &3 * B / R` |
| `NewmanTauberian` | `∀a:(num → complex). ∀B:real. ∀U:set(complex). ∀F:(complex → complex). ∀w:complex. (∀n:num. \|a(n)\| ≤ B) ∧ U ∈ complex_topology ∧ (∀s:complex. &1 ≤ re(s) ⇒ s ∈ U) ∧ holomorphic_on(U, F) ∧ (∀s:complex. &1 < re(s) ⇒ dirichlet_sums(a, s, F(s))) ∧ &1 ≤ re(w) ⇒ dirichlet_sums(a, w, F(w))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
