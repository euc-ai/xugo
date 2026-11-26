# constant_field_extension — the chart of a subspace of a function field over a finite extension of its constants

Let K be a regular function field over k inside M, l a finite extension of k
inside M, and E a k-basis of l, a K-basis of the composite K' = K(l)
(constant_composite). A k-subspace S of K has the chart
S' = `constant_chart(M, l, S)` = ⊕ S·e, its span over l: an element of K' lies
in S' exactly when its E-coordinates lie in S. Everything about charts reads
off those coordinates. The chart of a ring is a ring holding l; charts commute
with intersections, sums, spans, quotients, adjoining an element and inverting
one, and keep dimensions and bases. The chapters constant_galois and
constant_splitting, and scheme/curve_point_count, read the charts of a smooth
curve's rings.

## Definitions

| Member | Statement |
|---|---|
| `ConstantChartDef` | `constant_chart`: ring_ops(A) → set(A) → set(A) → set(A) |

## Charts

| Member | Statement |
|---|---|
| `ConstantChartSubmodule` | The chart of a subset is a submodule over l holding it |
| `ConstantChartLeast` | The chart of T lies in every submodule over l holding T |
| `ConstantChartCombination` | A combination of elements of l with coefficients in S lies in the chart of S |
| `ConstantChartCoordinates` | An element of the composite lies in the chart of S exactly when its E-coordinates lie in S |
| `ConstantChartMembers` | The chart of S is the direct sum of the lines S·e |
| `ConstantChartMeet` | Charts commute with intersections |
| `ConstantChartContract` | The chart of S lies in the composite and meets K in S |
| `ConstantSubspaceSubmodule` | A k-subspace of K is a k-submodule of the field |
| `ConstantRingSubspace` | A ring between k and K is a k-subspace of K |
| `ConstantChartIndependent` | A subset of K independent over a ring S stays independent over the chart of S |
| `ConstantIndependentLifts` | A subset of K independent over k stays independent over l |
| `ConstantChartQuotient` | Charts keep the dimension of a quotient |
| `ConstantChartDimension` | The chart of a finite-dimensional k-subspace has the same dimension over l |
| `ConstantChartMultiplier` | A multiplier taking X into a submodule over l takes the chart of X there |
| `ConstantChartProduct` | When X·Y lies in a submodule Z over l, so do the products of their charts |
| `ConstantChartOverChart` | When S multiplies X into itself, the chart of X is a submodule over the chart of S |
| `ConstantIdealSubspace` | An ideal of a ring between k and K is a k-subspace of K |
| `ConstantChartRing` | The chart of a ring S between k and K is a subring holding l and S, and charts of ideals are ideals contracting back |
| `ConstantChartSubring` | The chart over l of a subring is a subring holding l and the subring |
| `ConstantChartPolynomialImage` | Spanning over l commutes with adjoining an element: the chart of S[w] is the chart of S with w adjoined |
| `ConstantChartSpan` | The span over the chart of S is the chart of the span over S |
| `ConstantChartBasis` | A basis of a module over S stays a basis of its chart over the chart of S |
| `ConstantChartSum` | The chart of a sum of two k-subspaces is the sum of their charts |
| `ConstantChartOfSpan` | The chart of a span over a ring between k and K is the span of the chart over the chart of the ring |
| `ConstantChartFinite` | The chart of a ring S between k and K is generated over S by a k-basis of l |

## Charts of rings

The charts of the rings a function field is built from: the chart of the
constants is l, the chart of k[t] is l[t], charting commutes with inverting an
element, and when K is the fraction field of S the composite is the fraction
field of the chart of S. That an element transcendental over k stays
transcendental over l is algebraic_element's (`algebraic_element.ConstantTranscendental`).

| Member | Statement |
|---|---|
| `ConstantChartOfConstants` | The chart of the constants is l |
| `ConstantPolynomialChart` | The polynomials in t over l are the chart of the polynomials in t over k |
| `ConstantChartAway` | The chart of a ring that is S with t inverted is the chart of S with t inverted |
| `ConstantChartOfAway` | For a nonzero f ∈ S, the chart over l of S with f inverted is the chart of S with f inverted |
| `ConstantChartFractions` | When K is the fraction field of S, the composite is the fraction field of the chart of S |
