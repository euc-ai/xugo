# projective_presentation — the points and genus of the two-chart curve, and the finite presentation of a smooth projective equation curve

Points over each finite field evaluate the charts, F's where F does not vanish and G's where it does. The genus is read along the multiples of r: from some j on, the sections of the pair (A₀, tʲ·A₁) over the two charts are the forms of degree r·j over F(x)ʲ, so h(r·j) + g = c·j + 1, with g the Čech genus and c the degree of the zeros of t, and the Hilbert genus is g.

## Points

| Member | Statement |
|---|---|
| `ChartEvaluation` | a point over l where H does not vanish, at which every form vanishing at x vanishes, evaluates the chart of H: $\frac{P(x)}{H(x)^a} \mapsto \frac{P(z)}{H(z)^a}$ |
| `ChartPointFromMap` | every point of the chart of H with values in l is the evaluation at a point of the curve over l at which H does not vanish |
| `ChartPointsDetermined` | two points of the chart of H that agree on the quotients $\frac{P(x)}{H(x)^a}$ are equal |
| `FormRatiosDetermine` | two points of the curve over M at which every form of degree r·a has one ratio to H^a are equal |
| `PointsMatchCharts` | the points over the field of qᵐ elements are the evaluation points of the two form charts, F's where F does not vanish and G's where it does |

## The genus

| Member | Statement |
|---|---|
| `ProjectiveGenusIsCurveGenus` | the Hilbert-polynomial genus is the Čech genus of the curve over the line the two form charts make |

## The presentation

A smooth projective equation curve over a finite field is presented by the charts of two forms, a power of a coordinate and a form without rational zeros: at a generic point x with x(j) = one, the zeros of Xⱼ on the curve are rational over one finite field, where an anisotropic form H of degree r has no zero but the origin, so F = Xⱼ^r and G = H, or H + F where H vanishes at x, have no common zero on the curve and their charts present it.

| Member | Statement |
|---|---|
| `SmoothProjectiveBiaffinePresentation` | a smooth projective equation curve over a finite field has a smooth finite two-chart presentation inside M with its Hilbert genus and its points over every finite extension |
