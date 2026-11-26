# form_integral — orientation, compact form integrals and Stokes

An oriented manifold is a smooth manifold whose original chart
transitions have positive Jacobian determinant on every overlap.
`positive_manifold_chart⟨n⟩(T, 𝒜, c)` selects smoothly compatible charts
with positive transitions to the original atlas. Positive charts cover
the manifold and have positive transitions to one another. Completing
an atlas by its positive charts keeps both its smooth structure and its
orientation. Replacing it by another positive covering atlas does the
same.

Forms continue to be indexed by all smoothly compatible charts, as in
[differential_form](../differential_form/README.md). Positivity selects
the charts used for integration. On an open subset U,
`oriented_open_atlas⟨n⟩(T, 𝒜, U)` keeps positive charts with domains in U.
Its smooth completion is exactly the usual open-submanifold smooth
structure. The atlas of all compatible charts generally contains both
orientations and is not itself the oriented atlas for integration.

`manifold_chart_integral⟨n⟩(c, ω)` integrates the identity-frame
coefficient of ω(c) over Euclidean n-space. For a top form with compact
base support contained in c's domain, that coefficient is globally
smooth and has compact support inside the coordinate image. On an
intersection of two positive charts, the top-degree transformation law
uses the signed determinant, while Euclidean change of variables uses
its absolute value. Positivity makes them agree. The support must lie
inside the intersection for that chart-comparison formula.

A `manifold_integral_partition⟨n⟩(T, 𝒜, K, N, c, ψ)` is a finite
partition equal to one near compact K, with each weight compactly
supported inside its assigned positive chart c(i). Only i < N matters.
An empty K admits N = 0. Partitions use the compact cutoff construction
in [smooth_manifold](../smooth_manifold/README.md).

`has_manifold_form_integral⟨n⟩(T, 𝒜, ω, I)` requires orientation, a
top-degree form and compact support, together with one such partition
of the support whose weighted coordinate integral sum is I.
`manifold_form_integral⟨n⟩(T, 𝒜, ω)` selects I by epsilon. Existence
comes from the compact partition theorem; uniqueness compares two
partitions through their finite product refinement. Each doubly
weighted term has compact support in the two assigned chart domains,
so chart comparison applies. No arbitrary original term is assumed
to fit every chart of the other partition.

The operator is characterized on compactly supported top forms. It is
linear, equals a single chart integral when the support lies there,
and respects a change of positive covering atlas. Restriction to an
open subset containing the support and extension by zero from compact
submanifold support preserve the integral. The positive open atlas and
the usual smooth open atlas have the same compatible charts, so the
existing normalized form restriction and extension operations apply.
No convergence statement is attached to the epsilon value on other
inputs.

An `oriented_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)` is a homeomorphism with
smooth forward map and smooth carrier inverse, and positive coordinate
Jacobians on open chart-preimage domains. A whole source chart need
not fit in one target chart. Inversion preserves this predicate.
Pullback transports form support by carrier-relative preimage; the
inverse homeomorphism therefore preserves compactness of support.
Positive coordinate change of variables gives invariance of the
top-form integral. This compactness conclusion is not asserted for
pullback by an arbitrary smooth map.

`reflected_manifold_atlas(𝒜)` reverses the first coordinate in each
original chart. It has the same smooth compatible charts. In positive
dimension its integral is the negative of the original integral. In
dimension zero the empty determinant is one: every compatible chart is
positive and reflection fixes the Euclidean carrier. The atlas
convention gives every point the canonical positive sign, and compact
zero-form integration is the finite sum of scalar values on support.
The sign-reversal law explicitly requires n > 0.

`ManifoldStokes` is stated in dimension n+1 for a compactly supported
n-form η, with integral of dη equal to zero. All charts are open
Euclidean charts, so these manifolds have no boundary. Localize η by a
finite positive-chart partition and differentiate the whole finite
identity. Each resulting exact summand stays in its chart; its top
coefficient is a finite alternating sum of coordinate partials of
globally smooth compact coefficients. `IntegralPartialZero` makes
those integrals vanish. Terms from derivatives of the partition stay
inside d(ψ_i η); they are not discarded individually. On a compact
manifold, closed form support is automatically compact.

## Definitions

| Member | Constant |
|---|---|
| `OrientedManifoldDef` | `oriented_manifold⟨n⟩(T, 𝒜)` |
| `PositiveChartDef` | `positive_manifold_chart⟨n⟩(T, 𝒜, c)` |
| `OrientedOpenAtlasDef` | `oriented_open_atlas⟨n⟩(T, 𝒜, U)` |
| `reflectedAtlasDef` | `reflected_manifold_atlas(𝒜)` |
| `chartIntegralDef` | `manifold_chart_integral⟨n⟩(c, ω)` |
| `integralPartitionDef` | `manifold_integral_partition⟨n⟩(T, 𝒜, K, N, c, ψ)` |
| `HasIntegralDef` | `has_manifold_form_integral⟨n⟩(T, 𝒜, ω, I)` |
| `IntegralDef` | `manifold_form_integral⟨n⟩(T, 𝒜, ω)` |
| `OrientedDiffeomorphismDef` | `oriented_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)` |
| `fiberSliceDef` | `manifold_fiber_slice⟨n, m⟩(T, 𝒜, S, ℬ, k, ω, c, y, P)` |
| `FiberIntegralDef` | `manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω)` |

## Orientation cards

| Member | Statement |
|---|---|
| `AtlasMemberPositive` | Every original chart is positive — card |
| `PositiveTransition` | Positive charts have positive overlap diffeomorphisms — card |
| `PositiveChartRestrict` | Open restriction preserves a positive chart — card |
| `PositiveAtlas` | Positive completion preserves smooth compatibility and orientation — card |
| `OrientedAtlasChange` | A positive covering atlas determines the same orientation — card |
| `OrientedOpenSubmanifold` | Positive charts in an open subset orient its usual smooth structure — card |
| `OrientedEuclidean` | An identity-chart Euclidean open set is oriented — card |
| `OrientedZeroDimension` | Zero-dimensional smooth manifolds and compatible charts are canonically positive — card |
| `ReflectedAtlas` | Reflecting charts preserves the smooth structure and gives an oriented atlas — card |

## Integral construction and laws

| Member | Statement |
|---|---|
| `ChartIntegralChange` | Two positive charts give the same integral for support inside their overlap — card |
| `IntegralPartitionExists` | Compact sets admit finite partitions assigned to positive charts — card |
| `IntegralPartitionIndependent` | Two such partitions of a form support give equal sums — card |
| `HasIntegralExists` | Compact top forms have an integral value — card |
| `HasIntegralUnique` | The witnessed value is unique — card |
| `IntegralSpec` | The selected operator value satisfies the integral relation — card |
| `IntegralValue` | Any witnessed value equals the operator — card |
| `IntegralByPartition` | Any partition near a compact set containing support computes the operator — card |
| `IntegralSingleChart` | Support in one positive chart gives its Euclidean integral — card |
| `IntegralZero` | The zero form has integral zero — card |
| `IntegralAdd` | Integration is additive — card |
| `IntegralScale` | Integration commutes with real scaling — card |
| `IntegralFiniteSum` | Integration commutes with finite sums, including the empty sum — card |
| `IntegralAtlasInvariant` | Changing the positive covering atlas preserves the integral — card |
| `IntegralRestriction` | Open restriction containing the support preserves the integral — card |
| `IntegralExtension` | Compactly supported extension by zero preserves the integral — card |
| `IntegralReverseOrientation` | Reflecting orientation negates the integral when n > 0 — card |
| `IntegralZeroDimension` | Compact zero-dimensional integration is a finite point sum — card |

## Diffeomorphisms and Stokes

| Member | Statement |
|---|---|
| `OrientedDiffeomorphismInverse` | The inverse of a positive diffeomorphism is positive — card |
| `DiffeomorphismPullbackSupport` | Pullback support is the preimage of target support — card |
| `IntegralDiffeomorphism` | Positive diffeomorphisms preserve top-form integrals — card |
| `ManifoldStokes` | Compactly supported exact top forms integrate to zero without boundary — card |
| `CompactManifoldStokes` | On a compact manifold the compact-support hypothesis is automatic — card |

## Integration over the second factor

Let `(T, 𝒜)` be an n-dimensional smooth manifold and `(S, ℬ)` a compact
oriented m-dimensional manifold. Integration over the second factor
sends a degree k+m form on their product to a degree k form on the
base. The base need not be compact or oriented, and the product form
need not have compact support. No orientation of the product is used.

`manifold_fiber_slice` fixes a base chart c, a coordinate point y and
k horizontal vectors P. In every compatible fiber chart d it reads
the product form on the paired chart `(c,d)`, at the concatenated
point `(y,z)`, with the horizontal columns followed by m vertical
columns. The matrix has zero cross blocks and zero tails. This gives
a normalized top form on the fiber; incompatible charts and exterior
coordinate values give zero. Invalid base data give the whole zero
fiber form. Compatible factor charts give compatible product charts
by `smooth_manifold.ProductCompatibleChart`.

`manifold_fiber_integral` integrates that top fiber form at each base
chart, point and horizontal frame. The operator is zero outside valid
base chart data. Every slice has compact support because the fiber
carrier is compact. A finite positive-chart partition of that entire
carrier computes all slices at once, independently of the base point
and frame. Its fiber coordinate supports are fixed compact sets inside
the assigned charts. Localized coefficients are therefore smooth in
the base parameters after integration, by iterated parameter integration
over bounded boxes. Merely knowing that each individual slice has
compact support would not justify this argument.

The slot convention is **horizontal before vertical**. Writing I for
fiber integration and π₁*, π₂* for pullback, it gives

$$
d I(\omega) = I(d\omega)
$$

$$
I(\pi_1^{\ast} \alpha \wedge \omega) = \alpha \wedge I(\omega)
$$

$$
I(\omega \wedge \pi_1^{\ast} \alpha) = (-1)^{m \deg \alpha} \bigl(I(\omega) \wedge \alpha\bigr)
$$

$$
I(\pi_1^{\ast} \alpha \wedge \pi_2^{\ast} \beta) = \left(\int \beta\right) \alpha \qquad (\deg \beta = m)
$$

In the derivative formula, horizontal differentiation passes through
the fixed-partition integral.
The other terms are fiber exterior derivatives and integrate to zero
by boundaryless Stokes. Derivatives of partition weights are retained
inside the whole exact fiber forms. In dimension zero there are no
vertical derivative terms.

Base pullback commutes with integration even for a nonproper base map
and unequal base dimensions. Replacing the fiber atlas by a positive
covering atlas preserves integration; reflecting the fiber orientation
negates it when m > 0. These statements use whole normalized form
families, so their equalities include all exterior and incompatible
components.

The output support lies inside the projection of the product support.
That projection is closed because the fiber is compact; compact product
support gives compact output support. Equality of supports is not
claimed, since fiber contributions may cancel. A compact zero-dimensional fiber is a finite positive set of
points, and integration is the sum of pullbacks along its point sections.

| Member | Statement |
|---|---|
| `FiberSliceForm` | Horizontal insertion produces a normalized top fiber form — card |
| `FiberSliceBaseChange` | Base chart changes push the horizontal frame through the Jacobian — card |
| `FiberIntegralCoordinate` | One fixed fiber partition computes every coordinate integral — card |
| `FiberIntegralForm` | Fiber integration produces a smooth base form of degree k — card |
| `FiberIntegralAdd` | Fiber integration is additive — card |
| `FiberIntegralScale` | Fiber integration commutes with real scaling — card |
| `FiberIntegralFiniteSum` | Fiber integration commutes with finite sums, including the empty sum — card |
| `FiberIntegralExteriorDerivative` | Exterior differentiation commutes with fiber integration — card |
| `FiberIntegralProjectionFormula` | A base form wedged on the left passes outside the integral — card |
| `FiberIntegralRightProjection` | A base p-form on the right contributes the sign $(-1)^{mp}$ — card |
| `FiberIntegralProduct` | A product form integrates to its base factor times the fiber integral — card |
| `FiberIntegralNaturality` | Pullback along a base map commutes with fiber integration — card |
| `FiberIntegralAtlasInvariant` | Positive fiber-atlas changes preserve the integral — card |
| `FiberIntegralReverseOrientation` | Reflecting positive-dimensional fiber orientation negates the integral — card |
| `FiberIntegralSupport` | Output support is contained in the projection of input support — card |
| `FiberIntegralCompactSupport` | Compact product support gives compact output support — card |
| `FiberIntegralZeroDimension` | Integration over a compact zero-dimensional fiber sums section pullbacks — card |

## Orientation of a diffeomorphism from one point

On a connected oriented source, a smooth diffeomorphism preserves
orientation if its Jacobian has positive determinant at one point in
positive source and target charts. Local determinants are continuous
and nonzero, and their signs agree under positive chart changes. The
positive-sign locus is therefore open and closed. Invertibility and
connectedness are both needed to propagate the initial sign.
An oriented diffeomorphism also restricts to any open and its actual
image, using the positive open atlases.

[manifold_diagonal](../manifold_diagonal/README.md) applies
this to the coordinate fiber maps of a diagonal neighbourhood.

| Member | Statement |
|---|---|
| `DiffeomorphismOrientationAtPoint` | positivity at one point propagates along a diffeomorphism from a connected oriented source — card |
| `OrientedDiffeomorphismOpenRestrict` | positive diffeomorphisms restrict to opens and their images with positive open atlases — card |
