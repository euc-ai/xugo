# constant_splitting — the points of a chart and the splitting of maximal ideals in a constant extension

Let K be regular over a finite field k of q elements inside an algebraically
closed M, l the subfield of q^r elements and S a ring between k and K, with
chart S' over l (constant_field_extension). The points of S' in a field holding
l are the points of S, and over a maximal ideal of S of residue degree d lie
gcd(d, r) maximal ideals of S', each of degree d / gcd(d, r).

## Points of a chart

A point of S with values in a field holding l extends along a k-basis of l to a
point of S', and restriction to S undoes the extension: S' has the points of S,
as many of them. A subring of S' holding l and S is S', so two maps from S'
agreeing on l and on S agree.

| Member | Statement |
|---|---|
| `ConstantPointExtension` | A point of a ring between k and K extends along a k-basis of l to a point of its chart over l, equal to the point on the ring |
| `ConstantChartPoints` | Restriction is a bijection from the points of the chart of S over l onto the points of S over k |
| `ConstantChartPointCount` | The chart of S over l has finitely many points over l, as many as S has over k |
| `ConstantChartGenerated` | A subring of the chart of S over l holding l and S is the chart |
| `ConstantChartMapsAgree` | Two ring maps from the chart of S over l agreeing on l and on S agree on the chart |

## Splitting of maximal ideals

The l-points of S' in M restrict bijectively to the k-points of S, and a point
of S' taking S into a subfield holding l takes S' into it; so the k-points of S
with kernel m are the l-points of S' lying over m (residue_points), each
maximal ideal over m takes the same share of them, and the degrees of the
maximal ideals over m sum to d. Each is d / gcd(d, r), read off the sizes of
the subfields involved (`finite_field.FiniteConstantsTower`,
`nat_gcd.GcdFromCommonMultiples`).

| Member | Statement |
|---|---|
| `ConstantPointsInField` | Restriction is a bijection from the l-points of the extended chart in M to the k-points of S |
| `ConstantPointValues` | A point of the extended chart taking S into a subfield holding l takes the whole chart into it |
| `ConstantPointDegree` | The kernel of a point of the extended chart over m is maximal, of degree e with e·gcd(d, r) = d |
| `ConstantResidueFinite` | An ideal of the extended chart over an ideal of finite colength has finite colength over l |
| `MaximalIdealSplitting` | The maximal ideals of the extended chart over m number gcd(d, r), each of degree d / gcd(d, r) |
