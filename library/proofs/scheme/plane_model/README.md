# plane_model — integral plane equations and fixed good opens

A monic absolutely irreducible equation has a generic regular function-field model. Weighting its generator builds two explicit finite free charts, which may be singular: the scaled equation is the minimal polynomial of the weighted generator, so both charts are free of rank deg F over the line, glued along k[t][z] with t inverted, and they meet only in the constants. The structure pair of the model is the free line pair along the powers of z, zⁱ twisted by −bi, so its arithmetic genus is the sum of bi − 1 over 0 < i < deg F. Bezout certificates isolate regular fibres and bound the removed points uniformly across finite constant extensions; comparison with any other model of the function field (smooth_curve's birational charts) keeps that error fixed. A solution of the equation is a point of the chart: the inclusion of k lifts to k[t] because t is transcendental, and to k[t][z] because the minimal polynomial is monic over k[t] (`algebraic_element.TranscendentalLift`, `algebraic_element.HomomorphismExtendsAtRoot`).

The chapter's statements share one abbreviation table (family.go), written over the binders M, K, k, t, z, F, b, l and a: «pmRing» for K read in M as a ring (the field itself is written `restrict_field(M, K)`); «pmRational», «pmPolynomials», «pmInversePolynomials» for k(t), k[t], k[1/t] (with «pmRationalInK», «pmPolynomialsInK» for k(t), k[t] read in K); «pmGenerator» and «pmScaled» for $w = t^{-b} \cdot z$ and its scaled equation; «pmChart0», «pmChart1», «pmOverlap» for the plane charts, with «pmImage0», «pmImage1» for the charts spelled with M's operations and «pmPowersZ», «pmPowersW» for their power bases; «pmPoints» and «pmCount» for the l-points and the rational point count; and «pmExtendedField», «pmExtendedChart0», «pmExtendedChart1», «pmExtendedOverlap» for the field and the charts spanned over a constant field l (its composite with K is written `constant_composite(M, K, l)`). The polynomial a of a good certificate is valued at t, written `polynomial_eval(a, t)`.

## Definitions

| Member | Statement |
|---|---|
| `IntegralPlaneModelDef` | The equation is represented at a generic root in its regular function field |
| `PlaneChartZeroDef` | `plane_chart_zero`: ring_ops(A) → set(A) → A → A → set(A) |
| `PlaneChartOneDef` | `plane_chart_one`: field_ops(A) → set(A) → A → A → num → set(A) |
| `AbsolutePlaneEquationDef` | `absolute_plane_equation`: field_ops(A) → set(A) → (num → num → A) → bool |
| `PlaneEquationCountDef` | `plane_equation_count`: ring_ops(A) → set(A) → (num → num → A) → num |
| `PlaneGoodCertificateDef` | `plane_good_certificate`: ring_ops(A) → set(A) → A → (num → A) → (num → A) → (num → A) → (num → A) → bool |

## The model and its charts

| Member | Statement |
|---|---|
| `IntegralPlaneModelExists` | A regular function field separable over k(t) has an integral plane model at t |
| `AbsoluteEquationGenericModel` | Over a perfect k in an algebraically closed M, an absolutely irreducible plane equation read at a transcendental t is an integral plane model of k(t)(z) at a root z, of its degree in Z |
| `PlaneModelInAmbient` | An integral plane model read in the ambient field: the constants, the transcendental parameter, F as the minimal polynomial of z over k(t), and the second chart's data — t ≠ 0, $w = t^{-b} z$ in M, k[1/t] a subring inside k(t), z = t^b w |
| `PlaneChartsInAmbient` | The charts of a plane model are read off the operations of the ambient field |
| `PlaneModelOverPolynomials` | The polynomial of an integral plane model lies over k[t] |
| `PlaneModelRelation` | The equation of a plane model is a monic polynomial over k[t] vanishing at z |
| `PlaneChartsBiaffine` | The two charts of a plane model, k[t][z] and $k[1/t][t^{-b} z]$, are biaffine, glued along k[t][z] with t inverted |
| `ScaledMonicEquation` | With u = t⁻¹ and w = u^b z, the polynomial with coefficients $u^{b(d-i)} \cdot F(i)$ up to d = deg F is monic of degree d over k[u] and vanishes at w |
| `PlaneScaledMinimalPolynomial` | The scaled equation is the minimal polynomial of $w = t^{-b} z$ over k(t), of degree deg F |
| `PlaneChartOneBasis` | The second chart is free over k[1/t] on the powers of w below deg F |
| `PlaneChartsMeet` | The functions regular on both charts are the constants |
| `PlaneEquationBiaffineCurve` | An integral plane model is a curve over the projective line, its first chart free over k[t] on the powers of z below deg F |
| `PlaneStructurePairFree` | The structure pair of a plane model is the free line pair along the powers of z below deg F, the power zⁱ twisted by −bi |
| `PlaneModelArithmeticGenus` | The arithmetic genus of an integral plane model of weight b is the sum of bi − 1 over the exponents 0 < i < deg F |
| `PlaneSolutionPoint` | A solution of the plane equation in l is a point of the chart k[t][z], sending t and z to its coordinates |

## Constant extension and regular points

| Member | Statement |
|---|---|
| `PlaneModelBaseChange` | Extending the constants to a finite extension l, the model's charts spanned over l are a curve over the line of the same genus, and the powers of z below deg F stay a basis of the extended first chart over l[t] |
| `SecondChartRegular` | A point of the first chart carrying a Jacobian relation that also lies on the second chart $k[1/t][t^{-b} z]$, hence off t = 0, is regular there |
| `PlaneRegularPointsFromBezout` | An l-point of the extended first chart at which a(t) survives is a regular point of the extended plane model, and t − φ(t) has order one there |

## Counting

| Member | Statement |
|---|---|
| `PlaneChartFibreBound` | The first chart has at most deg F points in a subfield over each value of t |
| `PlaneCountNearChart` | The rational count of a plane model is the points of its first chart, up to deg F |
| `PlaneGoodOpenUniformBadPointBound` | Over a finite constant field l, the points of the extended first chart where a(t) survives are at most the rational point count, and fall short of it by at most d(deg a + 1) |
| `FunctionFieldModelsAgreeOffFiniteSet` | A curve over the line and the charts of a plane model at the same t agree once one nonzero polynomial over k is inverted at t, and their rational counts lie within a fixed bound over every finite subfield |
