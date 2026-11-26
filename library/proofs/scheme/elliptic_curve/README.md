# elliptic_curve — the curve y² = x³ + ax + b over a field, its two affine charts as quotients of free algebras and inside its function field, their smoothness, its rational points, genus one, the lines through its points, its trivial canonical pair and its points as a group through Pic⁰

The curve y² = x³ + ax + b over a field k is covered by two affine
charts. Away from its point at infinity it is the ring
k[x, y]/(y² − x³ − ax − b); around the point at infinity, in the
coordinates s = 1/x and u = y/x², the relation divided by x⁴ reads
u² = s + as³ + bs⁴, and the chart is k[s, u]/(u² − s − as³ − bs⁴). Each
ring is a quotient of the free algebra on two names by one relation:
`weierstrass_ring` and `weierstrass_chart_one_ring` are `koszul_quotient`
of the free algebra over k at `weierstrass_relation` and
`weierstrass_chart_one_relation`. A quotient of a free algebra is what
the partial derivatives, the Kähler differentials and the cotangent
complex of a plane curve are computed on (algebra/ring/partial_derivative,
algebra/ring/kaehler, algebra/cotangent/cotangent_examples), so the two
rings arrive with their differentials and their deformation theory.

Each relation is monic of degree two in one variable, and its constant
term in that variable is no square: x³ + ax + b has odd degree, and
s + as³ + bs⁴ has order one at s = 0. So each ring is an integral domain
over any domain k, whatever a and b are — the cusp y² = x³ included.
Smoothness is what reads the coefficients. When 2 ≠ 0 and
4a³ + 27b² ≠ 0, the resultant of the cubic and its derivative, the two
partial derivatives of each relation generate the unit ideal of its
ring: (2y, 3x² + a) = (1) and (2u, 1 + 3as² + 4bs³) = (1). Then the
module of Kähler differentials of each chart is free of rank one on the
invariant differential $\omega = \frac{dx}{2y} = \frac{dy}{3x^2 + a}$, and the cotangent
complex of each chart, [A → A²] with 1 ↦ (F_x, F_y), has a unimodular
row: every André–Quillen cohomology Dⁿ(A/k, N) with n ≥ 1 vanishes, for
every coefficient module N. Characteristic 3 needs no exclusion here:
there 4a³ + 27b² is a³ and 3x² + a is the unit a.

The statements that compute a cotangent complex fix its host to the
subsets of prod(num, D), where the free algebras and their quotients
have room whenever k does.

The same curve is read inside a field. A Weierstrass datum
`weierstrass(L, k, x, y, a, b)` is a subfield k of a field L holding a
and b, and members x and y of L with y² = x³ + ax + b, x transcendental
over k and L the field of fractions of chart 0. Chart 0 is
k[x] + k[x]·y and chart 1 is k[s] + k[s]·u with s = 1/x and u = y/x²,
both subsets of L (`weierstrass_chart_zero`, `weierstrass_chart_one`),
glued along A₀[1/x] = A₁[x]. The field of fractions of the Weierstrass
ring holds such a datum, and in every such field each quotient of a free
algebra above is isomorphic to its chart, so what is proved of the two
rings — their differentials, their cotangent complexes — holds of the
charts. Since y lies outside k(x), each chart is free of rank two over
its polynomial ring, on 1, y and on 1, u; the functions regular on both
charts are the constants; and the datum is a curve over the projective
line in the sense of `scheme/algebraic_curve`, with x the coordinate of
the line. Along the basis 1, y the structure pair is O(0) ⊕ O(−2) on the
line, so H⁰ is k and H¹ is one-dimensional: the genus is one and
χ(O) = 0. None of this asks 2 ≠ 0 or 4a³ + 27b² ≠ 0: a nodal or cuspidal
cubic is such a datum too, of arithmetic genus one. A datum that does ask
them is a smooth datum, `smooth_weierstrass(L, k, x, y, a, b)`: a
Weierstrass datum with 2 ≠ 0 and 4a³ + 27b² ≠ 0 in L.

The rational points are held as `scheme/biaffine_rational_point` holds them, by an
ideal in each chart. A solution (x₀, y₀) in k of the affine equation
gives the ideal of x − x₀ and y − y₀ in chart 0, the kernel of the
evaluation at the point, and in chart 1 the trace of the ideal it
generates in the overlap; the point lies on chart 1 exactly when x₀ ≠ 0.
The origin lies off chart 0 and has the ideal of s and u in chart 1.
These are all the rational points, each solution giving its own, and
the conjugation y ↦ −y sends (x₀, y₀) to (x₀, −y₀) and fixes the origin.
A point is regular when its ideal is invertible on each chart, which a
relation v·g = u·h between two generators decides
(`algebra/ring/fractional_ideal`): the equation factored at the point,
(y − y₀)(y + y₀) = (x − x₀)(x² + xx₀ + x₀² + a), makes it regular where
2y₀ ≠ 0, and, with the roles of the two factors swapped, where y₀ = 0
and 4a³ + 27b² ≠ 0. At the origin the chart-one equation
u² = s(1 + as² + bs³) makes it regular for every a and b. So when 2 ≠ 0
and 4a³ + 27b² ≠ 0 every rational point is regular.

## The two rings

| member | statement |
|---|---|
| `weierstrassRelationDef` | `weierstrass_relation(k, x, y, a, b)` = y² − x³ − ax − b in the free algebra over k on x and y |
| `WeierstrassRingDef` | `weierstrass_ring(k, x, y, a, b)` = `koszul_quotient` of that free algebra at the relation, k[x, y]/(y² − x³ − ax − b) |
| `weierstrassChartOneRelationDef` | `weierstrass_chart_one_relation(k, s, u, a, b)` = u² − s − as³ − bs⁴ in the free algebra over k on s and u |
| `weierstrassChartOneRingDef` | `weierstrass_chart_one_ring(k, s, u, a, b)` = k[s, u]/(u² − s − as³ − bs⁴), the chart at the point at infinity |
| `WeierstrassRingDomain` | k a domain, a and b in k, x ≠ y and s ≠ u ⇒ both rings are integral domains — card |
| `WeierstrassRingInUniverse` | in the host of the subsets of prod(num, D) both rings have room for their cotangent complexes — card |

## Smoothness

| member | statement |
|---|---|
| `WeierstrassPartialsUnit` | over a field with 2 ≠ 0 and 4a³ + 27b² ≠ 0 the partial derivatives of each relation generate the unit ideal: (2y, 3x² + a) = (1) and (2u, 1 + 3as² + 4bs³) = (1) — card |
| `WeierstrassChartPartialsUnit` | inside L: (2y, 3x² + a) spans chart 0 and (2u, 1 + 3as² + 4bs³) spans chart 1, when 2 ≠ 0 and 4a³ + 27b² ≠ 0 |
| `WeierstrassKaehlerAffine` | there each module of Kähler differentials over k is free on one ω, r ↦ r•ω, with dx = 2y·ω and dy = (3x² + a)·ω, and ds = 2u·ω and du = (1 + 3as² + 4bs³)·ω — card |
| `WeierstrassChartsSmooth` | there `Dⁿ(A/k, N) = 0` for every n ≥ 1 and every module N over either ring — card |

## The curve inside its function field

| member | statement |
|---|---|
| `WeierstrassChartZeroDef` | `weierstrass_chart_zero(R, k, x, y)` = k[x] + k[x]·y inside the ring `R` |
| `WeierstrassChartOneDef` | `weierstrass_chart_one(F, k, x, y)` = k[s] + k[s]·u inside the field `F`, s = 1/x and u = y/x² |
| `WeierstrassDef` | `weierstrass(L, k, x, y, a, b)`: k a subfield holding a and b, y² = x³ + ax + b in L, x transcendental over k, L the field of fractions of chart 0 |
| `SmoothWeierstrassDef` | `smooth_weierstrass(L, k, x, y, a, b)`: a Weierstrass datum with 2 ≠ 0 and 4a³ + 27b² ≠ 0 in L, the smooth datum; finite(k) is no part of it |
| `SmoothWeierstrassDatum` | a smooth datum is a Weierstrass datum |
| `WeierstrassSubfield` | a datum's k is a subfield of L |
| `WeierstrassCoefficientA` | a datum's coefficient a lies in k |
| `WeierstrassCoefficientB` | a datum's coefficient b lies in k |
| `WeierstrassXInField` | a datum's x lies in L |
| `WeierstrassYInField` | a datum's y lies in L |
| `WeierstrassEquation` | a datum's x and y satisfy y² = x³ + ax + b |
| `WeierstrassTranscendental` | a datum's x is transcendental over k |
| `WeierstrassFractionField` | L is the field of fractions of a datum's chart 0 |
| `WeierstrassXInvertible` | a datum's x is a unit of L: x ≠ zero, and inv(x) lies in L and inverts x on either side |
| `WeierstrassChartZeroMembers` | z lies in chart 0 exactly when z = p + q·y with p and q in k[x] |
| `WeierstrassChartOneMembers` | z lies in chart 1 exactly when z = p + q·u with p and q in k[s], s = 1/x and u = y/x² |
| `WeierstrassModelExists` | the field of fractions of the Weierstrass ring over a field holds a Weierstrass datum, the images of k, x, y, a and b — card |
| `WeierstrassImageIsomorphism` | in a field holding a datum, evaluation at x and y is an isomorphism from the Weierstrass ring over k onto chart 0, fixing k — card |
| `WeierstrassChartOneEmbeds` | there the chart-one ring maps by s ↦ 1/x and u ↦ y/x² isomorphically onto chart 1, fixing k — card |
| `WeierstrassBasisZero` | chart 0 is a subring containing k[x], free over k[x] on 1 and y, and 1 ≠ y |
| `WeierstrassChartOneEquation` | u² = s(1 + as² + bs³) in the field |
| `WeierstrassBasisOne` | chart 1 is a subring containing k[s], free over k[s] on 1 and u, and 1 ≠ u |
| `ChartZeroAwayInChartOne` | for x a nonzero member of L and any y, A₀[1/x] ⊆ A₁[x]: a power of 1/x carries chart 0 with x inverted into chart 1; read at (1/x, y/x²) it is the other inclusion |
| `WeierstrassOverlap` | A₀[1/x] = A₁[x] |
| `WeierstrassGlobalSections` | A₀ ∩ A₁ = k |
| `WeierstrassBiaffine` | glued along A₀[1/x] the two charts are a biaffine datum with x and 1/x |
| `WeierstrassIsCurve` | the datum is a curve over the projective line, x its coordinate |

## One and y are independent

| member | statement |
|---|---|
| `ChartZeroCoefficientsVanish` | 1 and y are independent over k[x]: p + q·y = zero with p and q in k[x] forces p = q = zero |
| `WeierstrassLaurentCoefficients` | 1 and y are independent over k[x, 1/x]: c + d·y = zero with c and d in k[x, 1/x] forces c = d = zero |
| `WeierstrassOverlapCoordinates` | the overlap A₀[1/x] is k[x, 1/x] · 1 ⊕ k[x, 1/x] · y: its members are the p + q·y with p, q in k[x, 1/x], each in one way |

## Genus one

| member | statement |
|---|---|
| `StructurePairFree` | along 1, y the structure pair is the free pair O(0) · 1 ⊕ O(−2) · y on the line |
| `GenusOne` | the genus is one |
| `EulerStructureZero` | the structure pair has finite-dimensional cohomology and χ(O) = 0 — card |

## Rational points and regularity

| member | statement |
|---|---|
| `weierstrassPointDef` | `weierstrass_point(L, k, x, y, x₀, y₀)`: the ideal of x − x₀ and y − y₀ in chart 0, and in chart 1 the trace of the ideal it generates in the overlap |
| `WeierstrassOriginDef` | `weierstrass_origin(F, k, x, y)`: chart 0 itself, and the ideal of s and u in chart 1 |
| `WeierstrassNegPointDef` | `weierstrass_neg_point(F, k, x, y, P)`: the conjugation y ↦ −y, u ↦ −u applied to each chart's ideal |
| `AffinePointMaximal` | a solution in k of the affine equation gives a rational point, its chart-0 ideal the kernel of the evaluation at it, maximal — card |
| `AffinePointCharts` | the point of (x₀, y₀) lies on chart 1 exactly when x₀ ≠ 0, its ideal there that of s − 1/x₀ and u − y₀/x₀² — card |
| `OriginMaximal` | the origin is a rational point, its chart-1 ideal the P(s) + Q(s)·u with P(0) = 0, maximal |
| `RationalPointsOfWeierstrass` | the rational points are the origin and the points of the solutions, distinct solutions giving distinct points — card |
| `NegPointValues` | the conjugation sends the point of (x₀, y₀) to that of (x₀, −y₀) and fixes the origin — card |
| `FactoredRelation` | (y − y₀)(y + y₀) = (x − x₀)(x² + xx₀ + x₀² + a), and for x₀ ≠ 0 the same relation in s and u on chart 1 — card |
| `AffinePointRegularOrdinary` | where 2 ≠ 0 and y₀ ≠ 0 the point of (x₀, y₀) is regular — card |
| `AffinePointRegularTwoTorsion` | where y₀ = 0 and 4a³ + 27b² ≠ 0 the point of (x₀, y₀) is regular — card |
| `OriginRegular` | the origin is regular, for every a and b — card |
| `AllRationalPointsRegular` | when 2 ≠ 0 and 4a³ + 27b² ≠ 0 every rational point is regular — card |

## Lines and the ideals they cut

A line y = μx + ν over k whose cubic splits over k cuts the curve in
three rational points counted with multiplicity: y − (μx + ν) generates
their product on chart 0 and has a pole of order three at the origin,
so its divisor is P₁ + P₂ + P₃ − 3O; a vertical line x − x₀ has divisor
P + (−P) − 2O.

| member | statement |
|---|---|
| `weierstrassLineDef` | `weierstrass_line(x, y, μ, ν)` = y − (μx + ν), the line function |
| `weierstrassChartOneLineDef` | `weierstrass_chart_one_line(x, y, μ, ν)` = u − (μs + νs²), the line function times s² |
| `LineCubicFactors` | two roots x₁, x₂ in k of x³ + ax + b − (μx + ν)², a double one where the line is tangent, split it as (x − x₁)(x − x₂)(x − x₃) with x₃ = μ² − x₁ − x₂ — card |
| `PointIdealOnLine` | where that cubic splits over k, each root t gives a point (t, μt + ν) of the curve, its chart-0 ideal holding the line function and its chart-1 ideal the chart-one form — card |
| `LineIdealChartZero` | when 2 ≠ 0 and 4a³ + 27b² ≠ 0, $\ell \cdot A_0 = m_{P_1} \cdot m_{P_2} \cdot m_{P_3}$, a repeated root a repeated factor — card |
| `LineIdealChartOne` | there (u − μs − νs²)·A₁ is the origin's ideal times the chart-1 ideals of P₁, P₂, P₃ — card |
| `UniformizerAtOrigin` | s·A₁ is the square of the origin's ideal, for every a and b — card |
| `VerticalIdealChartZero` | when 2 ≠ 0 and 4a³ + 27b² ≠ 0, $(x - x_0) \cdot A_0 = m_P \cdot m_{-P}$ for P = (x₀, y₀), −P = (x₀, −y₀) — card |
| `VerticalIdealChartOne` | there (s − x₀s²)·A₁ is the origin's ideal squared times the chart-1 ideals of P and −P — card |
| `LineLatticeIdentity` | there ℓ times the structure pair is P₁ · P₂ · P₃ · O⁻³, O the origin: the divisor of ℓ is P₁ + P₂ + P₃ − 3O — card |
| `VerticalLatticeIdentity` | there (x − x₀) times the structure pair is P · (−P) · O⁻²: the divisor of x − x₀ is P + (−P) − 2O — card |

## The dualizing pair

The dualizing pair ω of the curve over the line is generated on both
charts by one element y*, the coordinate functional of y in the basis
1, y of the overlap over k[x, 1/x]: ω = O · y*, so the canonical pair is
trivial.

| member | statement |
|---|---|
| `weierstrassDualGeneratorDef` | `weierstrass_dual_generator(R, k, x, y)` = y*, the coordinate functional of y in the basis 1, y of the overlap over k[x, 1/x], zero off the overlap |
| `DualGeneratorReads` | y* lies in the dualizing container and reads the coefficient of y at p + q·y, and that of one at y · (p + q·y) |
| `DualGeneratorZero` | chart 0 of ω is A₀ • y* |
| `DualBasisZero` | y* lies in the dualizing container; y* and y • y* read the coefficients of y and of one; {y • y*, y*} is a basis of chart 0 of ω over k[x] |
| `DualGeneratorsAgree` | on chart 1, y* is s² times the coefficient of u and u • y* is s² times that of one: chart 1's generator s²·u* is y* itself |
| `DualGeneratorOne` | chart 1 of ω is A₁ • y* |
| `DualBasisOne` | {u • y*, y*} is a basis of chart 1 of ω over k[s] |
| `CanonicalTrivial` | multiplication by y* is an isomorphism of lattice pairs from (A₀, A₁) onto ω, for every Weierstrass cubic |

## Riemann–Roch on the curve

With K = 0 and g = 1, Riemann–Roch on the curve reads
ℓ(M) − ℓ(M⁻¹) = deg M.

| member | statement |
|---|---|
| `WeierstrassRiemannRoch` | for an invertible pair M, M and M⁻¹ have finite-dimensional cohomology and ℓ(M) − ℓ(M⁻¹) = deg M |

## The dualizing pair and the Kähler differentials

Where the curve is smooth, each chart of ω should be the chart's module
of Kähler differentials, y* corresponding to the invariant differential
$\frac{dx}{2y}$.

| member | statement |
|---|---|
| `WeierstrassKaehlerCharts` | where 2 ≠ 0 and 4a³ + 27b² ≠ 0, each chart's Kähler module over k is free on one ω, with dx = 2y·ω, dy = (3x² + a)·ω, and ds = 2u·ω, du = (1 + 3as² + 4bs³)·ω — card |
| `KaehlerCanonical` | there each chart of ω is isomorphic over its chart to that chart's Kähler module, $\frac{dx}{2y}$ going to y* on both charts — card |

## Abel–Jacobi and the group of rational points

Based at the origin, P ↦ the class of O(P − O) sends the regular points
into Pic⁰ (curve_degree); Riemann–Roch with K = 0 and g = 1 makes it
one-to-one and onto, so the rational points of a smooth curve carry the
group of Pic⁰.

| member | statement |
|---|---|
| `AbelJacobiInjective` | distinct regular points have distinct classes O(P − O) — card |
| `AbelJacobiSurjective` | every class of Pic⁰ is the class O(P − O) of a regular point — card |
| `AbelJacobiBijection` | where 2 ≠ 0 and 4a³ + 27b² ≠ 0, P ↦ class of O(P − O) is a bijection from the rational points onto Pic⁰ — card |
| `WeierstrassPointSumDef` | `weierstrass_point_sum(L, k, x, y, P, Q)`: the rational point whose class is the product of the classes of P and Q |
| `NegPointClass` | the conjugation keeps the regular points and sends the class of O(P − O) to its inverse — card |
| `PointGroupTransported` | where 2 ≠ 0 and 4a³ + 27b² ≠ 0, the rational points form an abelian group under the transported sum, with the origin as unit and the conjugation as inverse — card |

## The chord-and-tangent law

The group carried over from Pic⁰ is the classical one: the three points
where a line meets the curve sum to the origin, which gives the chord and
tangent formulas for the sum in coordinates.

| member | statement |
|---|---|
| `ChordTangentSum` | where 2 ≠ 0 and 4a³ + 27b² ≠ 0, the three points where a line y = μx + ν meets the curve, counted with multiplicity, sum to the origin: P₁ ⊕ P₂ = −P₃ — card |
| `GroupLawFormulas` | there, in coordinates: the origin is the unit, (x₁, y₁) ⊕ (x₁, −y₁) = O, and otherwise (x₁, y₁) ⊕ (x₂, y₂) = (x₃, −(μ(x₃ − x₁) + y₁)) with x₃ = μ² − x₁ − x₂, μ the chord's slope $\frac{y_2 - y_1}{x_2 - x_1}$ or the tangent's $\frac{3x_1^2 + a}{2y_1}$ — card |

## The projective model

The same cubic, homogenized, is the plane curve Y²Z = X³ + aXZ² + bZ³
over k, read as a projective equation in the sense of
`scheme/projective_curve` inside any field M holding k. Its one point on
Z = 0 is (0 : 1 : 0); elsewhere it is the affine curve, so its ideal is
prime over M because the Weierstrass ring is a domain, and its gradient
vanishes nowhere because the partials of the affine relation generate
the unit ideal. Its Hilbert function is 3d, so its genus is one.

| member | statement |
|---|---|
| `WeierstrassSmoothProjectiveCurve` | over a finite subfield k of a field M, with 2 ≠ 0 and 4a³ + 27b² ≠ 0, the cubic Y²Z − X³ − aXZ² − bZ³ is a smooth projective equation curve of genus one — card |
