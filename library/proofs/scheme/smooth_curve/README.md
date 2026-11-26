# smooth_curve — smooth finite-field curves: their charts, closed points, and the finitely many of bounded degree

Normal charts over a finite field, which is perfect, specify the smooth geometrically integral input: the normal charts make the constants exact (`NormalChartsRegular`). Closed points have residue-degree weights, and finitely many have bounded degree. Every statement binds the curve over its own function field L. The divisors of closed points are in the chapters after this one: their arithmetic and the factorization of an invertible pair inside the charts are scheme/closed_divisor, their correspondence with the invertible lattice pairs is scheme/divisor_lattice_correspondence, and Pic⁰, the canonical divisor and Riemann–Roch are scheme/smooth_curve_riemann_roch. What asks for a larger field is elsewhere: the points of the curve over the finite subfields of a closed field, its birational comparison and its constant extension are scheme/curve_point_count, and the constant extension of the function field itself is algebra/field/constant_composite, its charts algebra/field/constant_field_extension.

## Definitions

| Member | Statement |
|---|---|
| `SmoothFiniteFieldCurveDef` | Over a perfect finite field, a normal integral curve is smooth |
| `CurveClosedPointDef` | `curve_closed_point`: ring_ops(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → bool |
| `ClosedPointDegreeDef` | `curve_closed_degree`: ring_ops(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → num |

## Charts

Every chart, ideal and pair is a subset of the function field L. A chart of a smooth curve is a Dedekind domain: its nonzero ideals have finite colength over the constants and are invertible. A fact is proved at A₀ and read at A₁ through `SmoothCurveSwap`.

| Member | Statement |
|---|---|
| `SmoothCurveSwap` | A smooth curve with its coordinate inverted and its charts exchanged is a smooth curve |
| `SmoothCurveOverLine` | The function field of a smooth curve is a field, and its charts make a curve over the line |
| `SmoothCurveFiniteConstants` | The constants of a smooth curve are finite |
| `SmoothCurveChartZeroNormal` | The chart A₀ of a smooth curve is integrally closed in its function field |
| `SmoothCurveChartOneNormal` | The chart A₁ of a smooth curve is integrally closed in its function field |
| `ChartCommRing` | A chart of a smooth curve is a ring under the function field's operations |
| `OverlapCommRing` | The overlap of a smooth curve is a ring under the function field's operations |
| `ChartSubring` | The constants are a subfield of L lying in the chart, and the chart is a subring of L |
| `NormalChartsRegular` | A curve over the line over a finite field whose two charts are integrally closed in L has a function field regular over k: its constants are exact |
| `ColengthCosetCount` | An ideal of colength d over a finite field of q elements has q^d cosets |
| `ChartIdealFiniteQuotient` | A nonzero ideal of a chart has finite colength over the constants and finitely many cosets |
| `ChartMaximalNonzero` | The zero ideal is not maximal in a chart |
| `ChartIdealInvertible` | Every nonzero ideal of a chart is invertible |

## Closed points

A closed point is the pair of its ideals in the two charts, the whole chart where it does not lie. Each maximal ideal of a chart belongs to exactly one closed point.

| Member | Statement |
|---|---|
| `ClosedPointSwap` | A closed point read from the other chart: exchanging the charts and the components is the same point |
| `ClosedPointMaximal` | A closed point is a maximal ideal of a chart: the first component unless it is all of A₀ |
| `ChartOverlap` | The overlap is a subring of L, the chart with t inverted inside itself and inside L, and the powers of t and t⁻¹ invert each other |
| `OverlapPowerUnit` | A power of the coordinate is a unit of the overlap, undone by the same power of its inverse |
| `ChartMaximalLocalizes` | A maximal ideal of a chart avoiding t extends to a prime of the overlap which contracts back to it |
| `ClosedPointChart` | A point proper in A₀ holds t exactly when its other component is whole, and otherwise contracts from the span of that component |
| `ClosedPointContraction` | A point in both charts avoids the coordinate on either side and its components contract from each other's span; a point in one chart holds that chart's coordinate |
| `ClosedPointSecondComponent` | A closed point proper in chart 0 has for its second component the meet of A₁ with the span of its first |
| `OverlapPrimeMaximal` | A nonzero prime of the overlap contracts to a maximal ideal of a chart |
| `ChartMaximalClosedPoint` | Every maximal ideal of a chart is the first component of exactly one closed point |
| `DegreeOneClosedPointsRational` | A pair of chart ideals is a closed point of degree one exactly when it is a rational point of the biaffine datum on the overlap ring |

## Bounded degree

Two distinct powers of t agree modulo a maximal ideal of colength at most n, so all such ideals hold one of finitely many nonzero differences, and a nonzero element lies in finitely many ideals.

| Member | Statement |
|---|---|
| `ChartIdealsAboveElement` | A nonzero element of a chart lies in finitely many of its ideals |
| `ChartMaximalColength` | A maximal ideal of a chart has finite positive colength over the constants |
| `ChartMaximalPowerRepeat` | Two distinct powers of t up to q^n agree modulo a maximal ideal of colength at most n |
| `ChartMaximalBoundedColength` | A chart has finitely many maximal ideals of bounded colength |
| `ChartPointsBoundedColength` | Finitely many closed points are proper in a chart with bounded colength there |
| `ClosedPointDegreeInField` | The degree of a closed point is the dimension of a quotient of M's own chart module |
| `ClosedPointResidue` | A closed point has finite positive degree |
| `ClosedPointsBoundedDegree` | Finitely many closed points have bounded degree |
| `ClosedPointsFiniteByDegree` | A closed point exists, each has finite positive degree, and finitely many closed points and effective divisors have a given bound or degree |
