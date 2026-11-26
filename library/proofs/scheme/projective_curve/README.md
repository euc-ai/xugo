# projective_curve — homogeneous projective equation curves: their definitions, the space of forms and the Hilbert function

A finite homogeneous equation set defines a projective equation curve: a geometrically prime ideal, a linear Hilbert polynomial, and the Jacobian rank of a smooth curve. Its Hilbert function defines the genus independently of any presentation. This chapter holds the definitions, with the parts of a point and of a curve that proofs read stated as laws; the dimension of the forms of one degree; bounds on the Hilbert function; the values of forms at a point; and the chart of a form, the open set where it does not vanish. The line X₂ = 0 of the projective plane, over a finite subfield k of any field M, is a smooth projective equation curve of genus zero: the definition has an instance, every conjunct exercised. The forms themselves, the homogeneous polynomials over a ring, are the chapter homogeneous_polynomial. The chapters projective_generic_point, projective_form_pair, projective_sections, projective_affine_piece, projective_form_chart and projective_presentation build on it, in that order.

## Members

| Member | Statement |
|---|---|
| `ProjectiveEquationPointsDef` | `projective_equation_points`: ring_ops(A) → set(A) → set(A) → num → set(((num → num) → A)) → set(num → A) |
| `PointCoordinatesIn` | the coordinates up to n of a point of the curve over l lie in l |
| `PointZeroPastN` | the coordinates past n of a point of the curve are zero |
| `PointLeadingOne` | the first nonzero coordinate of a point of the curve is one, at an index up to n |
| `PointEquationsVanish` | every equation in E vanishes at a point of the curve |
| `PointsAsNormalizedZeros` | the points over F of the curve cut out by a listed family P(0), …, P(r − 1) are the normalized (n + 1)-tuples of F at which every P(j) vanishes |
| `ProjectiveHilbertFunctionDef` | `projective_hilbert_function`: ring_ops(A) → set(A) → num → set(((num → num) → A)) → num → num |
| `ProjectiveGenusDef` | `projective_equation_genus`: ring_ops(A) → set(A) → num → set(((num → num) → A)) → num |
| `GenusAlongMultiples` | when the Hilbert function is eventually linear and h(r·j) + g = c·j + 1 from some j on, the genus is g |
| `SmoothProjectiveEquationCurveDef` | The input is a finite homogeneous closed embedding with geometrically prime ideal, linear Hilbert polynomial, and the Jacobian rank of a smooth projective curve |
| `CurveConstantsSubfield` | the constants k of a smooth projective equation curve are a subfield of the field |
| `CurveConstantsFinite` | the constants k of a smooth projective equation curve are finitely many |
| `CurveEquationsForms` | each equation of a smooth projective equation curve is a form over its constants |
| `CurveIdealGeometricallyPrime` | the equations of a smooth projective equation curve span a prime ideal of the polynomials over the whole field |
| `CurveHasPoint` | a smooth projective equation curve has a point with coordinates in the field |
| `CurveHilbertEventuallyLinear` | the Hilbert function of a smooth projective equation curve is eventually e·d + 1 − g, with e positive |
| `CurveJacobianRank` | at every point of a smooth projective equation curve, the gradients of its equations span a space of dimension n − 1 |
| `ProjectiveGenericFieldDef` | `projective_generic_field`: field_ops(A) → set(A) → num → set((num → num) → A) → set(A) → bool |

## The space of forms and bounds on the Hilbert function

| Member | Statement |
|---|---|
| `FormsFreeModule` | over a ring R, the forms of degree d in the variables 0, …, n are the free R-module on the monomials of degree d |
| `FormsDimension` | The forms of degree d in the variables 0, …, n over a subfield k form a space of dimension binomial(d + n, n) |
| `PrincipalFormsShift` | For a nonzero form F of degree e ≤ d, the forms of degree d in the ideal of F are F times the forms of degree d − e, multiplication by F injective |
| `FormMultiplicationLinear` | Multiplying by a form F of degree e is a k-linear map from the forms of degree s to those of degree s + e |
| `PlaneCurveHilbertFunction` | A plane curve of degree e > 0 has 2·h(d) + (e − 1)(e − 2) = 2(e·d + 1) at every d ≥ e |
| `FormsSubspace` | the forms of degree d over a subfield k are a vector space over k, meeting every ideal of the polynomials over k in a subspace |
| `HilbertFunctionCodimension` | the forms of degree d in the ideal of E are finite-dimensional, and their dimension and h(d) add to binomial(d + n, n) |
| `HilbertFunctionBelowCodimension` | a subspace of the forms of degree d inside the ideal bounds the Hilbert function at d by its codimension |
| `CurveIdealPrime` | the ideal over k of a smooth projective equation curve is prime |
| `HyperplaneSectionBound` | for a polynomial F outside a prime ideal, a subspace of the forms of degree d holding the ideal's forms of degree d and F times every form of degree e has codimension at most h(d) − h(e) |

## The generic point

| Member | Statement |
|---|---|
| `EvaluationLinear` | evaluating the forms of degree d along σ at y is linear over k acting on L through σ |
| `FormValuesDimension` | when a form of degree d vanishes at y exactly on the ideal, the values of the forms of degree d are a subspace of L, over k through σ, of dimension h(d) |
| `AlgebraicCoordinatesBound` | coordinates all algebraic over σ(k) bound h(d) by [σ(k)(y) : σ(k)] |
| `TranscendentalPairBound` | a coordinate transcendental over σ(k) and another transcendental over σ(k)(first) give (p + 1)(q + 1) ≤ h(d) for p + q ≤ d, when y(j) = one |
| `CoordinatePowerValue` | at a point y with y(j) = one, each power y(i)ᵗ with t ≤ d is the value along σ of a form of degree d |
| `TranscendentalCoordinateBound` | a coordinate transcendental over σ(k) gives p + 1 ≤ h(d) for p ≤ d, when y(j) = one |

## The charts

| Member | Statement |
|---|---|
| `ChartSubring` | the chart of a form over k is a subring of M holding k |
| `PointEvaluation` | evaluation at a point with coordinates in a subfield K ⊇ k is a ring map from the polynomials over k with values in K |
| `ChartQuotient` | the value of a form of degree r·b over F(x)^b lies in the chart of F |

## Points

| Member | Statement |
|---|---|
| `PointNormalization` | a zero of E with coordinates in l, zero past n and not zero, scaled by the inverse of its first nonzero coordinate, is a point of the curve over l |
| `ProjectiveEquationPointsMono` | for K ⊆ L, the points of the curve over K are points over L |

## Evaluation at a point

| Member | Statement |
|---|---|
| `EvaluationNatural` | a ring map from a subring S of M into M fixing k commutes with evaluating the polynomials over k at points of S |
| `FormValuesSubspace` | at the generic point x the values of the forms of degree e are a k-subspace of K of dimension h(e) |

## An instance

| Member | Statement |
|---|---|
| `PlaneLineCurve` | the line X₂ = 0 in the projective plane, over a finite subfield k of any field M, is a smooth projective equation curve of genus zero |
