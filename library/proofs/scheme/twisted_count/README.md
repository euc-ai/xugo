# twisted_count — twisted evaluations counted over a good open

Over a good open C of L (scheme/galois_good_open), the evaluations twisted by s at Q = |k|^m are the geometric points ev of C with ev(f)^Q = ev(s f): the rational points that the power map moves as the inverse of s. Summed over the automorphism group they count the good base points the power fixes, and summed over a subgroup H the points of its invariant chart with values in the field of Q elements (`GoodFibreTwistCounting`). Inverting one more polynomial c(t) changes each twisted count by at most card(G) · deg(c) (`TwistedCountOffRefinement`).

## Definitions

| Member | Statement |
|---|---|
| `TwistedEvaluationsDef` | `twisted_evaluations`: field_ops(A) → set(A) → set(A) → num → permutation(A) → set(A → A) |
| `TwistedEvaluationCountDef` | `twisted_evaluation_count`: field_ops(A) → set(A) → set(A) → num → permutation(A) → num |
| `GoodBaseCountDef` | `good_base_count`: ring_ops(A) → set(A) → (num → A) → num → num |

## Counting over a good open

| Member | Statement |
|---|---|
| `GoodPointKeepsDenominator` | A point of a ring holding k, t and the inverse of a(t) does not kill a(t) |
| `PointFrobenius` | Raising values to the power card(k)^m keeps a point |
| `GoodPointBase` | A geometric point sends t to a good base point |
| `RationalPointOverGoodBase` | A rational point of the chart lies on the fibre over its value at t, a rational base point that is good |
| `RationalPointsFreeAction` | The group acts freely on the geometric points whose value at t the power fixes |
| `GoodGroupFixesChartData` | The group fixes the constants, t and the inverse of a(t) |
| `TwistedEvaluationsAreMoved` | The evaluations twisted by s are the rational points the power map moves as the inverse of s |
| `TwistedEvaluationsFinite` | The evaluations twisted by an element of the group are finitely many |
| `TwistedEvaluationCountByInvariant` | Where r tells the H-orbits of the rational points apart, the sum over H is card(H) for each value of r the power map leaves unchanged |
| `GoodActionKeepsT` | The action of the group does not change the value at t |
| `GoodFibreTwistCountOverBase` | The twisted evaluations summed over the whole group number its size for each good base point fixed by the power |
| `GoodFibreTwistCountOverChart` | The twisted evaluations summed over H number card(H) for each point of the invariant chart with values in the field of the power |
| `GoodFibreTwistCounting` | Summed over the automorphism group, the twisted evaluations count the good base points the power fixes; summed over a subgroup H, the points of the invariant chart with values in the field of the power |

## The count under refinement

| Member | Statement |
|---|---|
| `TwistEquationAway` | The twist equation of a point of C[1/c(t)] spreads from C: both sides are points of the localization, and restriction to C is injective |
| `TwistedPointsAway` | Restriction is a bijection from the twisted points of C[1/c(t)] onto the twisted points of C not killed by c at t |
| `PointsOverRootsBound` | The points of a good chart killing c at t number at most card(G) · deg(c) |
| `TwistedCountOffRefinement` | Inverting c(t) changes the count of points twisted by s by at most card(G) · deg(c) |
