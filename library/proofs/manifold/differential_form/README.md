# differential_form — compatible chart families of smooth forms

For a manifold with point type A, a differential form is a function

    ω : prod(set(A), A → num → real)
          → (num → real) → (num → num → real) → real.

Each compatible chart c receives a Euclidean form on its coordinate
image. On an overlap, the c component is the pullback of the d component
along the transition from c coordinates to d coordinates. Components
vanish on incompatible charts and outside each coordinate image. This
normalization makes equality literal equality of the entire families,
including their values at inactive indices and coordinate points.

`manifold_form_on⟨n⟩(T, 𝒜, k, ω)` includes the manifold condition.
The original atlas covers the manifold, so its components determine the
whole normalized family. Compatible Euclidean forms on those original
charts extend uniquely to such a family; their values at other indices
are not prescribed. Existence uses the local criterion in
[vec_form](../../vector/vec_form/README.md), after the transition laws
make the local extensions agree. No quotient of chart representatives
or chosen maximal atlas is required.

The degree carrier is a restriction of three nested real function
modules. Wedge and exterior derivative act in every compatible chart,
and Euclidean pullback naturality preserves the transition equations.
The exterior derivative takes input degree k and produces degree k+1.
The unit has value one in each compatible coordinate image and zero
elsewhere. On an empty manifold it is the zero family; every degree
carrier then contains only that family. Degrees above n are zero on
every manifold. Dimension and degree zero are included throughout.

For a smooth map f, `manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω)`
selects a target chart containing the image of each source coordinate
point, then evaluates the Euclidean Jacobian pullback. The target chart
is held fixed inside that Jacobian. A whole source chart need not map
into one target chart, and the pointwise selection is not claimed to
vary continuously.

`PullbackCoordinate` replaces this choice by any fixed target chart on
an open coordinate region mapping into its domain. At each point the
chosen and fixed target charts overlap; continuity supplies an open
source neighbourhood mapping into that intersection. Transition
compatibility and the chain rule identify their pullback values there.
The resulting local formula proves smoothness and is used before any
differentiation. Pullback is linear and contravariant, and commutes
with wedge and exterior derivative.

Restriction to an open subset U retains every compatible chart whose
domain lies in U and sets every other whole component to zero.
`OpenCompatibleChart` identifies precisely these indices with the
compatible charts of the open submanifold. Restriction is pullback by
the open inclusion, composes on nested open subsets, commutes with
wedge and exterior derivative, and takes a pullback to the pullback
from the open subset. Coordinate functions and chosen inverses
outside their domains remain unconstrained; the open-domain guards and
normalization keep those values out of all asserted form laws.

## Definitions

| Member | Constant |
|---|---|
| `FormOnDef` | `manifold_form_on⟨n⟩(T, 𝒜, k, ω)` |
| `FormModuleDef` | `manifold_form_module⟨n⟩(T, 𝒜, k)` |
| `WedgeDef` | `manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β)` |
| `ExteriorDerivativeDef` | `manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω)` |
| `UnitDef` | `manifold_form_unit⟨n⟩(T, 𝒜)` |
| `RestrictDef` | `manifold_form_restrict⟨n⟩(T, 𝒜, U, ω)` |
| `PullbackDef` | `manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω)` |

## Carriers, extension and restriction

| Member | Statement |
|---|---|
| `FormModule` | Forms of each degree form a real module — card |
| `FormModulePointwise` | The degree module's operations are pointwise and its carrier is the k-forms |
| `FormAdd` | The sum of two k-forms is a k-form |
| `FormAboveDimension` | A form of degree greater than n is the zero family — card |
| `FormExt` | Agreement on the original atlas determines the entire family — card |
| `FormAtlasExtension` | Compatible original-atlas components extend uniquely — card |
| `FormRestrict` | Restriction gives a form on the open submanifold — card |
| `RestrictionCompose` | Restrictions compose on nested open subsets — card |

## Wedge and exterior derivative

| Member | Statement |
|---|---|
| `WedgeForm` | Wedge adds form degrees — card |
| `WedgeBilinear` | Wedge is bilinear on the degree modules — card |
| `WedgeAddLeft` | Wedge is additive in its first factor |
| `WedgeZeroRight` | A form wedged with the zero family is the zero family |
| `WedgeAssociative` | Wedge is associative — card |
| `WedgeGradedCommutative` | Exchanging degrees p and q contributes $(-1)^{pq}$ — card |
| `WedgeUnit` | The normalized constant one is a zero-form and a two-sided unit — card |
| `ExteriorDerivativeForm` | Exterior derivative raises the degree by one — card |
| `ExteriorDerivativeLinear` | Exterior derivative is a homomorphism of degree modules — card |
| `ExteriorDerivativeAdd` | The exterior derivative of a sum of two k-forms is the sum of their derivatives |
| `ExteriorDerivativeSquareZero` | d² is the zero family — card |
| `ExteriorDerivativeLeibniz` | d(α∧β) = dα∧β + (-1)^p α∧dβ — card |
| `ExteriorDerivativeWedgeClosed` | For a closed ω, d(β∧ω) = dβ∧ω |

## Pullback and naturality

| Member | Statement |
|---|---|
| `PullbackCoordinate` | Any fixed target chart gives the pullback on its open source preimage — card |
| `PullbackForm` | Smooth pullback preserves form degree — card |
| `PullbackLinear` | Pullback is a homomorphism of degree modules — card |
| `PullbackIdentity` | Identity pullback fixes every form — card |
| `PullbackCompose` | f* g* = (g ∘ f)* — card |
| `PullbackWedge` | Pullback preserves wedge — card |
| `PullbackExteriorDerivative` | Pullback commutes with exterior derivative — card |
| `PullbackOpenInclusion` | Open inclusion pullback equals restriction — card |
| `RestrictionWedge` | Restriction preserves wedge — card |
| `RestrictionExteriorDerivative` | Restriction commutes with exterior derivative — card |
| `RestrictionZero` | Restriction of the zero family is the zero family |
| `RestrictionPullback` | Restricting a pullback to an open subset is the pullback from that subset |

## Support, weights and extension by zero

`manifold_function_form⟨n⟩(T, 𝒜, f)` writes a normalized smooth scalar
function as a zero-form, with no dependence on the matrix argument.
Every zero-form comes from a unique such function. The scalar's zero
normalization outside the base carrier is needed for uniqueness there.
`manifold_form_weight⟨n⟩(T, 𝒜, f, ω)` multiplies each active coordinate
value by f at the corresponding base point. It is the wedge of the
associated zero-form with ω and preserves ω's degree.

`manifold_form_support⟨n⟩(T, 𝒜, ω)` is a closed subset of the base
manifold. It closes the locus where some active chart and matrix give
a nonzero value. For a form, transition pullbacks are invertible, so
vanishing is independent of the active chart. In a compatible chart,
the support of the component relative to its open coordinate image is
the coordinate image of the base support intersected with the chart
domain. No ambient Euclidean boundary support is included in that
coordinate statement.

Weighting has support in the intersection of scalar and form supports,
and exterior differentiation cannot enlarge support. Open restriction
intersects support with the open subset. These facts use the open
complement of a closed support, where all coefficients vanish locally.
A wedge of any two families has support in the intersection of its
factors' supports: its nonzero locus lies in both of theirs, and closure
is monotone.

`manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω)` reads the component at the
restriction of each ambient chart to U and puts zero outside its image.
It is a total family for every input, and restriction recovers any form
on the open submanifold; conversely a form whose support lies in U is
the extension of its restriction to U. Smoothness requires its submanifold support
to be closed in the ambient manifold. Under that condition extension
preserves support and commutes with exterior differentiation. Being
closed only in U is insufficient at the extension boundary.

A finite partition near a compact set containing the form's support
writes it as a literal sum of weighted forms. Each summand has compact
support inside one covering open set. Taking the cover to be chart
domains gives compact chart-supported summands. If the compact set is
empty, the form is zero and an empty sum gives the same family.

| Member | Statement |
|---|---|
| `SupportDef` | `manifold_form_support⟨n⟩(T, 𝒜, ω)` |
| `FunctionFormDef` | `manifold_function_form⟨n⟩(T, 𝒜, f)` |
| `WeightDef` | `manifold_form_weight⟨n⟩(T, 𝒜, f, ω)` |
| `ExtendZeroDef` | `manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω)` |
| `FunctionForm` | A smooth scalar function gives a zero-form — card |
| `FormZeroDegree` | Every zero-form comes from a unique normalized smooth scalar function — card |
| `WeightAsWedge` | Weighting is wedge multiplication by the corresponding zero-form — card |
| `WeightForm` | Smooth weighting preserves form degree — card |
| `SupportClosed` | Base support is closed for every component family on a topology — card |
| `SupportEmpty` | A form has empty support exactly when it is the zero family — card |
| `SupportCoordinate` | Relative coordinate support is the chart image of restricted base support — card |
| `WeightSupport` | Weighting has support in the intersection of the two supports — card |
| `WedgeSupport` | A wedge of any two families has support in the intersection of their supports — card |
| `ExteriorDerivativeSupport` | Exterior derivative does not enlarge support — card |
| `SupportRestrict` | Open restriction intersects base support with the open subset — card |
| `ExtendZeroForm` | Ambient closed support makes extension by zero a form — card |
| `ExtendZeroRestrict` | Restricting the extended family recovers the source form — card |
| `RestrictExtendZero` | A form supported in an open subset is the extension by zero of its restriction — card |
| `WedgeRestrictExtendZero` | A wedge whose second factor is supported in an open subset is the extension by zero of the wedge of the restrictions |
| `ExtendZeroSupport` | Extension preserves support when it is ambient closed — card |
| `ExtendZeroExteriorDerivative` | Extension by zero commutes with exterior derivative under that support condition — card |
| `ExtendZeroWedgeClosed` | For a closed ω supported in U, extending β∧ω from U by zero gives a form whose derivative extends dβ∧ω |
| `ExtendZeroAdd` | Extension by zero takes sums to sums |
| `FormPartitionDecomposition` | A finite partition gives compactly supported subordinate form summands — card |

## Compact coordinate coefficients

For a form with compact base support contained in one compatible chart,
evaluation on any fixed matrix is a smooth scalar function on the whole
Euclidean space, with compact support inside the coordinate image.
The finite minor expansion gives smoothness on the image; the compact
support stays away from its boundary, so the existing zero normalization
is smooth there as well. This applies in every form degree and supplies
both top coefficients for integration and lower-degree coefficients for
Stokes in [form_integral](../form_integral/README.md).

| Member | Statement |
|---|---|
| `ChartCoefficientCompact` | Compact support inside a chart gives globally smooth compact coordinate coefficients — card |
