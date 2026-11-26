# closed_point — closed points of a Weierstrass curve

A closed point is an affine maximal ideal together with its ideal on chart
one, or the origin. The residue field may be larger than k. Its degree is
its k-dimension. Invertibility here is not elliptic_curve's
`biaffine_regular_point`, which includes rationality. Frobenius counts are
weighted sums over points whose positive degree divides m, for m≥1.

Each chart is a quadratic ring k[t] + k[t]·w with w² in k[t]: chart zero
at t = x, w = y, chart one at t = 1/x, w = y/x². Its maximal ideals are
read once, for such a ring: one meets k[t] in the ideal of p(t), p monic
irreducible over k, the norm of a nonzero member giving a nonzero member of
k[t] (`QuadraticChartContractsToPrime`); above p it is (p(t), w − r(t)) for a
square root r of w² modulo p, or the inert p(t)-multiples
(`QuadraticMaximalIdealClassification`); and (p(t), w − r(t)) is invertible
when 2w and F′(t) span the ring, w² = F(t) (`QuadraticFibreIdealInvertible`,
the Jacobian criterion for a quadratic fibre), so every maximal ideal of
such a ring is invertible, the inert ones being principal
(`QuadraticChartMaximalInvertible`). The two charts are instances.
The Jacobian pair on each chart is
elliptic_curve.WeierstrassChartPartialsUnit, which asks a smooth datum,
`smooth_weierstrass` (2 ≠ 0 and 4a³ + 27b² ≠ 0). With every maximal ideal
invertible and every nonzero ideal of finite colength
(algebraic_curve.NonzeroIdealFiniteColength), every nonzero ideal of either
chart is invertible; each chart is then integrally closed in L
(ideal_factorization.InvertibleIdealsIntegrallyClosed), and over a finite k
— where finite(k) first enters — the datum is a smooth finite curve over k.
Its closed points, degrees and Frobenius counts are then those of
scheme/smooth_curve at the Weierstrass charts, through the general chapter's
gluing theorems, which is the form in which scheme/elliptic_hasse_weil reads
them. At m = 1 the count is the number of rational ideal pairs, N₁ = N
(`FrobeniusCountOne`): a degree dividing one is one, and the closed points of
degree one are the rational pairs.

The contraction, the classification and the origin member hold for every
Weierstrass datum; regularity asks a smooth datum, `smooth_weierstrass`,
not a finite k. The point-degree and finiteness statements assume a smooth
datum over a finite base field. PointCountAffine holds
for every finite-base Weierstrass model. The ideal-conjugation criterion
is restricted to first-kind ideals; inert ideals are conjugation-fixed too.

## Definitions

| Member | Meaning |
|---|---|
| `ClosedPointDef` | `elliptic_closed_point` |
| `PointDegreeDef` | `elliptic_point_degree` |
| `ResidueFieldDef` | `elliptic_residue_field` |
| `FrobeniusCountDef` | `elliptic_frobenius_count` |
| `PointCountDef` | `elliptic_point_count` |
| `AffineSolutionCountDef` | `affine_solution_count` |

## Counting

| Member | Statement |
|---|---|
| `ResidueFieldSize` | The residue field at P has q^deg(P) elements. — card |
| `PointCountAffine` | Every finite-base model has N=1+affine_solution_count(restrict_ring(field_ring(L), k),a,b). — card |

## The quadratic chart

The ring k[t] + k[t]·w inside L, t transcendental over k and w² in k[t],
read once for both charts.

| Member | Statement |
|---|---|
| `QuadraticChartContractsToPrime` | A maximal ideal of k[t] + k[t]·w, with t transcendental, w² in k[t] and 1/t outside the ring, meets k[t] in the ideal of p(t), p monic irreducible over k. |
| `QuadraticMaximalIdealClassification` | A maximal ideal of k[t] + k[t]·w (w² ∈ k[t]) over p(t)·k[t], p irreducible over k, is (p(t), w − r(t)) for a square root r of w² mod p of degree below p's, or the inert p(t)·S. |
| `QuadraticFibreIdealInvertible` | Over S ⊇ k[t] with t transcendental, w² = F(t) and (2w, F′(t)) = S, an ideal (p(t), w−r(t)) with w² ≡ r(t)² mod p(t) is invertible: the Jacobian criterion for a quadratic fibre. |
| `QuadraticChartMaximalInvertible` | Every maximal ideal of k[t] + k[t]·w is invertible when t is transcendental over k, w² = F(t) for F over k, and 2w and F′(t) span the ring. |
| `PrincipalIdealInvertible` | A nonzero member of a subring S of L spans an invertible ideal of S. |

## Points

Each chart-zero member sits beside its chart-one twin.

| Member | Statement |
|---|---|
| `MaximalContractsToPrime` | An affine maximal ideal contracts to a monic irreducible polynomial ideal. |
| `ChartOneContractsToPrime` | A chart-one maximal ideal meets k[1/x] in the ideal of p(1/x), p monic irreducible over k. |
| `MaximalIdealClassification` | An affine maximal ideal is of the first kind, (p, y−r) with r² ≡ y² mod p — ramified when r = 0, split otherwise — or inert, (p) with y² no square mod p. |
| `ChartOneMaximalIdealClassification` | Chart-one maximal ideals over k[s], s = 1/x, are first-kind (p(s), u−r(s)) or inert (p(s)). |
| `WeierstrassCubicPolynomial` | The cubic X³ + aX + b is a polynomial over k with value y² at x and derivative value 3x² + a there. |
| `ChartOneQuartic` | The chart-one quartic X + aX³ + bX⁴ is a polynomial over k; at s it and its derivative take s(1 + as² + bs³) and 1 + 3as² + 4bs³. |
| `ChartZeroMaximalInvertible` | Every chart-zero maximal ideal is an invertible fractional ideal. |
| `ChartOneMaximalInvertible` | Every chart-one maximal ideal is invertible. |
| `ClosedPointsOffOrigin` | The only chart-one maximal ideal containing s=1/x is the origin ideal. |
| `PointDegreeFirstKind` | The residue degree of (p,y−r) is deg p. — card |
| `PointDegreeSecondKind` | The residue degree of an inert (p) is 2 deg p. — card |
| `RamifiedIffConjugateEqual` | A first-kind ideal equals its conjugate exactly when it contains y. — card |
| `ClosedPointIdealLattice` | Every closed-point ideal pair is a compatible lattice pair. — card |
| `ClosedPointIdealInvertible` | Every closed-point ideal pair is invertible. — card |
| `ClosedPointDegreePositive` | Closed points have positive degree and affine residue fields are finite-dimensional. — card |
| `MaximalPowerColength` | dim_k(A₀/m_P^t)=t deg P, including t=0. — card |

## The datum as a smooth finite curve

| Member | Statement |
|---|---|
| `ChartIdealsInvertible` | Every nonzero ideal of either chart of a smooth datum is invertible. |
| `WeierstrassChartsNormal` | Both charts of a smooth datum are integrally closed in L. |
| `WeierstrassSmoothFiniteCurve` | A smooth datum over a finite field is a smooth finite curve over k with coordinate x, on its two charts and their overlap. |

## The closed points of the curve

| Member | Statement |
|---|---|
| `ClosedPointsAreCurveClosedPoints` | The closed points here are smooth_curve's closed points at the Weierstrass charts, with the same degrees. |
| `FrobeniusCountIsWeightedMultiples` | N_m is the weighted-multiples count at the closed points weighted by degree. |
| `FrobeniusCountOne` | N₁=N: the Frobenius count at m = 1 is the number of rational ideal pairs. |
