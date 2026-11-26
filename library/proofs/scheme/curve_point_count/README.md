# curve_point_count — points of a smooth curve over the finite subfields of a closed field

A smooth curve (scheme/smooth_curve) is stated over its own function field L. Counting its points over finite fields, comparing it with a birational model and extending its constants all read the curve inside a larger field M, algebraically closed where the counts are taken, with the function field a subfield K of M; `InAmbient` is that reading as one rule set. The rational point count over a finite subfield l is the number of evaluation points, read on the two charts with the overlap counted once, and over the subfield with q^m elements it is the sum of the degrees of the closed points whose degree divides m. Two curves over the line with one function field count alike up to a fixed bound. Extending the constants to the field with q^r elements gives a smooth curve of the same genus and the same cohomology dimensions, splits a closed point of degree d into gcd(d, r) points of degree d / gcd(d, r), and counts at degree m what the curve counts at degree r·m; the linear algebra, the normality and the splitting of maximal ideals under the extension are algebra/field/constant_field_extension, read here at the charts of the curve.

## Definitions

| Member | Statement |
|---|---|
| `CurveRationalPointCountDef` | This counts actual normalized evaluation maps on the two charts, with overlap counted once |
| `CurveExtensionCountDef` | R.carrier is the algebraically closed extension host in point-count theorems, not the function field of the curve |
| `CurveEvaluationPointsDef` | `curve_evaluation_points`: field_ops(A) → set(A) → set(A) → A → set(A) → set(A) → set(prod(bool, A → A)) |

## A curve inside a larger field

The chapter reads a curve over a subfield K of M at restrict_field(M, K), whose operations are M's and whose ring is M's ring restricted to K. `InAmbient` is that reading as one rule set; `CurveChartsInField` holds what is not an equality of terms for a smooth curve, and `CurveOverLineChartsInField` and `CurveOverLineFirstChart` hold it for any curve over the line.

| Member | Statement |
|---|---|
| `CurveChartsInField` | The charts, overlap and swap of a smooth curve over a subfield K, read in M |
| `CurveOverLineChartsInField` | The charts and overlap of a curve over the line in a subfield K, read in M, are subrings of M between k and K |
| `CurveOverLineFirstChart` | The first chart of a curve over the line, read in M: it and the overlap are subrings lying in K, it holds k and t, a power of t carries the overlap into it, k[t] is a subring of M lying in it, it is free of finite rank over k[t], and K is its field of fractions |

## Evaluation points

The points of the curve in a finite field: the first chart sees every point where t is finite, and the second adds those where t⁻¹ vanishes.

| Member | Statement |
|---|---|
| `ChartPointsFinite` | A chart of a curve has finitely many points in any finite ring |
| `OverlapPointsAway` | The overlap is the second chart with t⁻¹ inverted, so restriction takes its points one to one onto the chart's points making t⁻¹ a unit |
| `CurvePointSetsFinite` | The charts and the overlap of a curve have finitely many points in a finite set |
| `EvaluationPointsCount` | The evaluation points are finite and counted by the two charts less their overlap |
| `CurveCountAtInfinity` | The rational count is the points of the first chart and those of the second chart killing t⁻¹ |

## Point counts over k

The evaluation points fibre over the closed points of degree dividing m, with fibres the size of the degree: a point of a chart in the subfield with q^m elements has a maximal kernel, the kernel of exactly d points when the closed point under it has degree d (`residue_points.ResiduePoints`), and a maximal ideal of A₁ holding t⁻¹ is the point at infinity.

| Member | Statement |
|---|---|
| `ClosedPointAtInfinity` | A maximal ideal of A₁ holding the inverse of t is the second component of the closed point with first component A₀ |
| `EvaluationFibreSize` | Over a closed point of degree dividing m lie as many evaluation points as its degree |
| `EvaluationPointLiesOver` | Every evaluation point lies over exactly one closed point of degree dividing m |
| `ExtensionCountClosedPoints` | The point count over the field with q^m elements is the sum of the degrees of the closed points whose degree divides m |

## The extended curve

The charts of a constant extension, spanned over the field l of q^r constants, form a curve over the line. The extended chart holds k[t] and l and is finite over k[t], so an element integral over the extended chart has integral coordinates, by the trace argument of algebra/field/constant_galois, and lies in it: the extended charts are integrally closed in the composite, and the datum is a smooth curve over l. The points of the extended charts are those of the charts, so the extended curve counts at degree m what the curve counts at degree r·m.

| Member | Statement |
|---|---|
| `SmoothCurveRegular` | The function field of a smooth curve is regular over its constants read in any field holding it |
| `ConstantChartLine` | A chart of a curve over the line, its function field regular over k, after a constant extension of finite degree |
| `ConstantChartCurve` | The charts of a constant extension form a curve over the line |
| `ConstantChartOverLine` | the chart of A₀ holds k[t] and l and is finite over k[t] |
| `ConstantChartIntegrallyClosed` | The chart of A₀ is integrally closed in the composite K(l) |
| `SmoothCurveConstantExtension` | Extending the constants to the field with q^r elements gives a smooth curve over it, with the charts spanned over l |
| `ExtensionCountBaseChange` | The count of a curve over the field with q^r elements at degree m is its count over k at degree r·m |

## Cohomology

H⁰ and H¹ of an extended pair are the charts of H⁰ and H¹, so their dimensions do not change.

| Member | Statement |
|---|---|
| `ConstantChartLatticeDimensions` | An invertible pair keeps the dimensions of H⁰ and H¹ over a constant extension |
| `ConstantChartGenus` | A constant extension keeps the genus |

## Splitting

A closed point of degree d has gcd(d, r) closed points above it on the extended curve, each of degree d / gcd(d, r): the maximal ideals of the extended chart over a maximal ideal of the chart are counted in algebra/field/constant_splitting, an ideal of the overlap is generated by its part in the chart, and a closed point above P is read from its first component.

| Member | Statement |
|---|---|
| `OverlapIdealGenerated` | An ideal of the overlap is generated by its part in the chart |
| `ClosedPointLiesOver` | With charts A ⊆ B and one t, a closed point whose first component lies over fst(P) has its second over snd(P) |
| `ClosedPointSplittingAtChart` | The splitting for a point proper in A₀: first components biject the points above onto the maximal ideals over fst(P) |
| `ClosedPointSplitting` | A closed point of degree d has gcd(d, r) closed points above it on the extended curve, each of degree d / gcd(d, r) |

## Base change

The statement of base change: its clauses are the members above.

| Member | Statement |
|---|---|
| `SmoothCurveConstantBaseChange` | Extending the constants to the field with q^r elements gives a smooth curve of the same genus, splits closed points, shifts the point count, and keeps the cohomology dimensions of invertible pairs |

## Birational charts

Two curves over the line in one function field are compared chart by chart. A chart has boundedly many points over each value of t, one bound for every field of values. A nonzero element of a chart divides the value at t of a nonzero polynomial, so a chart's count is that of the chart with the element inverted, up to a fixed bound. Each first chart lies in the other with one element inverted, so the two curves count alike up to a fixed bound, over every finite field and at every extension degree.

| Member | Statement |
|---|---|
| `ChartFibreBound` | The first chart of a curve has boundedly many points over each value of t, one bound for every subfield of values |
| `ChartDividesLinePolynomial` | A nonzero element of the first chart divides there the value at t of a nonzero polynomial over k |
| `ChartInsideAway` | Of two curves with one function field and one field of constants, the first chart of one lies in the first chart of the other with one nonzero element inverted |
| `CurveCountNearAway` | For a nonzero h in the first chart, the rational point count is the number of points of the chart with h inverted, up to a bound fixed for every finite field |
| `BirationalBiaffinePointCountBound` | Two curves over the line with one function field and one field of constants have rational point counts within a fixed bound of each other over every finite subfield |
| `ExtensionCountComparison` | Two such curves, regular over a finite k inside an algebraically closed M, have extension counts within a fixed bound of each other at every positive degree |

