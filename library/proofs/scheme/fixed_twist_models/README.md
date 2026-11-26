# fixed_twist_models — common models of the fixed twists and the upper bound

Every twist field of a good open (scheme/constant_twist, scheme/galois_good_open) has a plane model, and one refinement of the good open, by inverting one polynomial c(t), carries a model of every twist at once, each twisted count changing by at most card(G) · deg(c) (`TwistModelsRefineGoodOpen`). On such a common good open the points of a model's affine chart in the field of Q elements are as many as the evaluations of C twisted at Q (`FixedTwistPointCorrespondence`), so the square-field bound for a plane model bounds each twisted count by |k|^m + B √|k|^m, with B and the threshold independent of s and m (`FixedTwistedUpperBound`).

## Definitions

| Member | Statement |
|---|---|
| `FixedTwistModelsDef` | `fixed_twist_models`: field_ops(A) → set(A) → set(A) → A → set(A) → (num → A) → (permutation(A) → A) → (permutation(A) → num → A) → (permutation(A) → num) → bool |

## Common models

| Member | Statement |
|---|---|
| `ChartModelFacts` | The chart of a finite ring with fraction field K is a finite ring with fraction field the composite |
| `CompositeSeparable` | Each member of the composite of L with the constants is separable over k(t) |
| `TwistModelAgrees` | The twisted field has a plane model whose extended chart agrees with that of a good open at every nonzero multiple of one p(t) |
| `TwistModelsOnRefinement` | A good open refines, by inverting one c(t), to a good open carrying a model of every fixed twist |
| `FixedTwistModelsOnCommonGoodOpen` | Every fixed twist has a model over one common good open |
| `TwistModelsRefineGoodOpen` | Refine the given good open by inverting one polynomial c(t): the refinement carries a model of every fixed twist field, and each twisted count changes by at most card(G) · deg(c) |

## The point correspondence

| Member | Statement |
|---|---|
| `FixedTwistChartData` | Where the rings of one twist of fixed models sit: regular fields, the constants l, C and D (the model's affine chart with a(t) inverted) as subrings holding k, and one chart over l |
| `FixedTwistActsOnChart` | The twist is a ring endomorphism of the common chart: the q-th power on l, s on C, the identity on D |
| `TwistEquationSpreads` | For a point of the common chart, ψ(y)^Q = ψ(φ y) spreads from a generating ring to the chart |
| `FixedTwistPointsOfAway` | Restriction to D is a bijection of W onto the points of D in F_Q |
| `FixedTwistPointsOfGoodOpen` | Restriction to C is a bijection of W onto the twisted evaluations of C |
| `FixedTwistPointCorrespondence` | The points of D in F_Q are as many as the twisted evaluations of C at Q: both are in bijection with W |

## The upper bound

| Member | Statement |
|---|---|
| `FixedTwistModelUpperBound` | One twist of fixed models obeys the square-field bound: constants B and Q₀ with the twisted count at most \|k\|^m + B·r when e(s) divides m - 1, \|k\|^m = r² and Q₀ ≤ \|k\|^m |
| `FixedTwistedUpperBound` | Over a square field and for 2\|G\| dividing m - 1, the twisted count at \|k\|^m is at most \|k\|^m + B √\|k\|^m, with B and the threshold independent of s and m |
