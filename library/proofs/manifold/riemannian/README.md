# riemannian — Riemannian metrics, positive frames and their connection matrices

A Riemannian metric is a compatible family of smooth positive definite
coordinate matrices. It gives a positive symmetric pairing on tangent
fibers. Positive orthonormal frames and their dual coframes express
the Levi-Civita connection directly through the first structure equation.
The chapter constructs that connection explicitly, proves its uniqueness,
and compares connections and curvature under frame and coordinate changes.
Normalized curvature Pfaffians on positive charts determine the closed
global Euler form, independently of every local frame choice.

## Metrics and tangent pairings

For the chart type `C = prod(set(A), A → num → real)`, a metric has host type
`C → (num → real) → num → num → real`. The predicate
`riemannian_metric⟨n⟩(T, 𝒜, g)` includes the smooth manifold condition.
Each compatible chart c carries a symmetric positive definite n by n
matrix g(c,y), with smooth entries on its coordinate image. Matrices
are padded by zero; incompatible charts and points outside the image
carry the zero matrix. Smoothness is local on the image, and imposes
no smooth extension across its boundary.

For the transition from c to d, with coordinate function τ and Jacobian J,
the compatibility law is

$$
G_c(y)=J(y)^{\mathrm{T}}G_d(\tau(y))J(y).
$$

`riemannian_pairing⟨n⟩(T, 𝒜, g, x, v, w)` contracts the two tangent
components against the metric in a chosen active chart. `PairingChart`
makes the value independent of that choice. The function is zero on
invalid inputs, while bilinearity, symmetry and positive definiteness
are asserted on actual tangent fibers. At dimension zero the only
tangent vector is zero; an empty manifold has the zero metric family.

A Euclidean immersion supplies a metric by taking the Gram matrix of
its differential. Compact manifolds therefore admit metrics by the
existing Euclidean embedding theorem. The general metric definition,
and all frame and connection laws, apply to arbitrary Riemannian
metrics. Constant convex combinations of two metrics remain metrics,
including both endpoint parameters.

| Member | Statement |
|---|---|
| `MetricDef` | `riemannian_metric⟨n⟩(T, 𝒜, g)`: normalized smooth positive definite matrices with Jacobian compatibility |
| `PairingDef` | `riemannian_pairing⟨n⟩(T, 𝒜, g, x, v, w)`: metric contraction in an active chart, zero on invalid inputs |
| `InducedMetricDef` | `riemannian_induced_metric⟨n, N⟩(T, 𝒜, f)`: the normalized Gram matrices of coordinate differentials |
| `PairingChart` | Any active chart computes the tangent pairing — card |
| `PairingBilinearSymmetric` | The pairing is bilinear and symmetric on each tangent fiber — card |
| `PairingPositive` | The quadratic value is nonnegative and vanishes exactly on the zero tangent vector — card |
| `MetricConvexCombination` | A constant convex combination of two Riemannian metrics is a metric — card |
| `ImmersionMetric` | A smooth Euclidean immersion induces a Riemannian metric — card |
| `CompactMetricExists` | Every compact smooth manifold admits a Riemannian metric — card |

## Positive orthonormal frames and coframes

`riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)` describes a smooth
matrix field on the coordinate image, zero outside it. Its columns
are orthonormal for g, and its determinant is positive relative to the
ordered coordinates of c. This agrees with a supplied manifold
orientation when c is a positive chart. The predicate itself imposes
no global orientability assumption.

Gram-Schmidt applied to the coordinate basis gives such a frame on
the whole image. Positive residual lengths make every square root
and reciprocal smooth. The resulting triangular frame has positive
diagonal, so its determinant has the required sign. No connectedness
or contractibility assumption on the coordinate image is needed.
The empty frame at dimension zero has determinant one.

The coefficient matrix of the dual coframe is

$$
C=E^{\mathrm{T}}G,\qquad CE=EC=I.
$$

`riemannian_coframe⟨n⟩(g, c, E)` packages these one-forms as an n by 1
matrix. It reads only the first vector column of a form argument.
Evaluation on the frame gives the Kronecker delta and recovers every
padded tangent coordinate vector. A two-form expands in these coframes
with one half of the sum over all ordered pairs; this factor agrees
with the existing signed-shuffle convention for wedge.

| Member | Statement |
|---|---|
| `PositiveFrameDef` | `riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)`: a normalized positive orthonormal frame in chart c |
| `coframeDef` | `riemannian_coframe⟨n⟩(g, c, E)`: the column of one-forms with coefficient matrix $E^{\mathrm{T}}G$ |
| `PositiveFrameExists` | A metric admits a positive orthonormal frame on every compatible chart image — card |
| `PositiveFrameInverse` | The metric dual coefficient matrix is the two-sided inverse of the frame — card |
| `CoframeForm` | The coframe is an n by 1 matrix of normalized smooth one-forms — card |
| `CoframeDual` | Evaluating the coframe on its frame gives the Kronecker delta — card |
| `CoframeExpansion` | Frame vectors reconstruct every padded coordinate vector from its coframe coefficients — card |
| `CoframeTwoFormExpansion` | A two-form is one half of its ordered frame-component wedge expansion — card |

## The connection from the structure equation

The structure coefficients are the values of the exterior derivatives
of the coframe on pairs of frame vectors. They are smooth and
antisymmetric in their last two indices. The normalization fixes

$$
d\theta^a=\frac{1}{2}\sum_{b,c}c^a_{bc}\theta^b\wedge\theta^c.
$$

The explicit connection is

$$
A_{ab}=\frac{1}{2}\sum_c(c^a_{bc}+c^b_{ca}-c^c_{ab})\theta^c.
$$

`riemannian_connection⟨n⟩(g, c, E)` is a square matrix of smooth
one-forms. It is skew and satisfies the torsion equation

$$
d\theta+A\wedge\theta=0.
$$

These two conditions determine it uniquely. The difference of two
solutions has frame coefficients antisymmetric in the first two
indices and symmetric in the last two; cycling the symmetries makes
each coefficient its own negative, hence zero. The normalization and
matrix padding turn this pointwise uniqueness into literal equality
of the total matrix-valued forms. This is the Levi-Civita connection
in an orthonormal frame; the construction uses the structure equation.

| Member | Statement |
|---|---|
| `structureCoefficientsDef` | `riemannian_structure_coefficients⟨n⟩(g, c, E)`: the ordered frame evaluations of the coframe derivatives |
| `ConnectionDef` | `riemannian_connection⟨n⟩(g, c, E)`: the explicit cyclic structure-coefficient formula |
| `StructureCoefficientsSmooth` | The coefficients are smooth and antisymmetric in their last two indices — card |
| `CoframeStructureEquation` | The coframe derivative has its structure-coefficient wedge expansion — card |
| `ConnectionSkew` | The connection is a skew matrix of smooth one-forms — card |
| `ConnectionTorsionFree` | The connection satisfies the first structure equation — card |
| `ConnectionUnique` | A skew connection satisfying that equation equals the explicit connection — card |

## Changing the positive frame within a chart

For two positive orthonormal frames E and F in the same chart, define

$$
H=E^{\mathrm{T}}GF,\qquad F=EH,\qquad\theta_F=H^{\mathrm{T}}\theta_E.
$$

`riemannian_frame_change⟨n⟩(g, c, E, F)` is H viewed as a normalized
matrix of zero-forms. It is orthogonal and has determinant one on the
coordinate image. Positivity of both frames is measured against the
same chart, so no global orientation hypothesis is needed here.
The coframe relation and connection uniqueness give

$$
A_F=H^{\mathrm{T}}A_EH+H^{\mathrm{T}}dH.
$$

The Euclidean gauge calculus then gives the congruence of curvatures
and equality of their Pfaffians. These statements include zero rank;
in odd rank the Pfaffians both vanish. Their scope is a change of
frame within one fixed coordinate chart.

| Member | Statement |
|---|---|
| `frameChangeDef` | `riemannian_frame_change⟨n⟩(g, c, E, F)`: the normalized zero-form transition matrix |
| `FrameChangeSpecialOrthogonal` | Two positive frames have an orthogonal transition of determinant one — card |
| `CoframeFrameChange` | The new coframe is the transpose transition times the old coframe — card |
| `ConnectionFrameChange` | The new connection obeys the orthogonal gauge formula — card |
| `CurvatureFrameChange` | Curvature changes by congruence — card |
| `CurvaturePfaffianFrameChange` | The curvature Pfaffian is independent of the positive frame in a fixed chart — card |

## Restrictions and coordinate changes

Restricting a compatible chart to an open subset restricts its metric
coefficients by normalized zero extension. A positive frame restricts
in the same way. The coframe and connection then equal identity
pullback of the original expressions to the smaller image. These are
equalities of normalized total functions; values on the rest of the
original chart image are discarded.

For charts c and d, let τ carry c-coordinates to d-coordinates and
let J be its Jacobian. For positive coordinate frames E in c and F
in d, the overlap transition is

$$
H=(JE)^{\mathrm{T}}G_dF,\qquad F=JEH.
$$

The target fields in this formula are evaluated at τ(y), and H is
normalized on the source overlap image. It is orthogonal. Its
pointwise determinant is the sign of the coordinate Jacobian; a
disconnected overlap need not have a single sign. The pulled-back
coframe and connection satisfy

$$
\tau^\ast\theta_d=H^{\mathrm{T}}\theta_c,
\qquad
\tau^\ast A_d=H^{\mathrm{T}}A_cH+H^{\mathrm{T}}dH.
$$

Here the source expressions are restricted to the overlap. The
connection proof gauges the target connection back to the positive
source coframe and uses uniqueness there. It therefore also applies
to orientation-reversing coordinate transitions. Curvature transforms
by the corresponding congruence.

| Member | Statement |
|---|---|
| `chartFrameChangeDef` | `riemannian_chart_frame_change⟨n⟩(g, c, d, E, F)`: the normalized overlap zero-form matrix |
| `MetricAtlasInvariant` | Two smooth atlases with the same compatible charts define the same metric predicate — card |
| `MetricChartRestrict` | Metric coefficients in a restricted chart are the normalized restriction of the original coefficients — card |
| `PositiveFrameRestrict` | Normalized restriction gives a positive frame in the restricted chart — card |
| `CoframeRestrict` | Restricting the chart and frame restricts the coframe by identity pullback — card |
| `ConnectionRestrict` | The corresponding connection restricts by identity pullback — card |
| `ChartFrameChangeOrthogonal` | The cross-coordinate overlap matrix is orthogonal — card |
| `ChartFrameChangeDeterminant` | Its determinant is the pointwise sign of the coordinate Jacobian — card |
| `CoframeChartChange` | Coordinate pullback of the target coframe is the transpose overlap matrix times the restricted source coframe — card |
| `ConnectionChartChange` | Coordinate pullback of the target connection obeys the orthogonal gauge formula — card |
| `CurvatureChartChange` | Coordinate pullback of curvature obeys the corresponding congruence formula — card |

## The global Euler form

`riemannian_local_euler_form⟨n⟩(g, c, E)` is the Pfaffian of the
connection curvature after multiplying each matrix entry by
$1/(2\pi)$. In order 2m this is $(2\pi)^{-m}$ times the unscaled
Pfaffian. Odd orders give zero; order zero gives the normalized unit.
The local form is independent of the positive frame.
Scaling the curvature matrix is distinct from taking the curvature
of a scaled connection, whose linear and quadratic terms scale
differently.

Between positive charts the coordinate Jacobian is positive, so the
overlap gauge has determinant one. Its Pfaffian is invariant, giving
exactly the pullback compatibility needed to glue the local Euler
forms on an oriented atlas. The underlying metric is arbitrary, and
compactness is unnecessary.

`riemannian_euler_representative⟨n⟩(T, 𝒜, g, ω)` asks for a normalized
manifold n-form on all compatible charts, with its component on every
positive chart equal to the local Euler form for every positive frame.
It includes the orientation and metric conditions. An oriented atlas
covers the manifold, so extension from its original charts exists
and is unique. The same local formula then holds on every positive
compatible chart.

The global `riemannian_euler_form⟨n⟩(T, 𝒜, g)` selects this unique
representative. It is zero when the orientation or metric input is
invalid. For valid input, incompatible charts have zero components,
while negative or mixed-orientation compatible charts receive the
components determined by overlap pullback. Assigning zero to all
nonpositive charts would fail to define a manifold form.

The Euler form is closed by a dimension count: it has top degree, so
its exterior derivative is a form of degree above the dimension, and
the curvature Pfaffian identity is not read; that identity serves a
Pfaffian on a base of dimension above the matrix order. The Euler form
vanishes in odd dimension and equals the canonical normalized
zero-form unit in dimension zero. Replacing the oriented atlas by another
covering atlas of positive charts leaves the metric predicate and
the entire Euler form unchanged.

| Member | Statement |
|---|---|
| `localEulerDef` | `riemannian_local_euler_form⟨n⟩(g, c, E)`: the Pfaffian of curvature divided entrywise by $2\pi$ |
| `eulerRepresentativeDef` | `riemannian_euler_representative⟨n⟩(T, 𝒜, g, ω)`: a normalized manifold form with the positive-chart Euler expressions |
| `EulerFormDef` | `riemannian_euler_form⟨n⟩(T, 𝒜, g)`: the unique representative on valid input, zero otherwise |
| `LocalEulerForm` | The local Euler expression is a normalized smooth n-form — card |
| `LocalEulerScale` | In order 2m the normalization factor is $(2\pi)^{-m}$ — card |
| `LocalEulerFrameIndependent` | The local Euler form is independent of its positive frame — card |
| `LocalEulerOverlap` | Local Euler forms agree by pullback on positive-chart overlaps — card |
| `EulerRepresentativeExistsUnique` | An oriented Riemannian manifold has exactly one Euler representative — card |
| `EulerForm` | The chosen Euler form is a normalized manifold n-form — card |
| `EulerPositiveChart` | Every positive chart and positive frame compute its component — card |
| `EulerClosed` | The global Euler form is closed — card |
| `EulerOdd` | The Euler form vanishes in odd dimension — card |
| `EulerZeroDimension` | The zero-dimensional Euler form is the canonical normalized unit — card |
| `EulerAtlasInvariant` | Replacing the atlas by an oriented atlas of positive charts preserves the whole Euler form — card |
