# regular_point — local orders and pole filtrations at regular rational points

The local ring and powers of its maximal ideal define the integer order of a nonzero function. Rational points have residue field k, and the pole filtration at a regular rational point grows by at most one dimension a step. Relative pole-space criteria retain membership in a known global pole space, since orders at regular points alone do not detect singular-point regularity.

## Members

| Member | Statement |
|---|---|
| `PointLocalRingDef` | `point_local_ring`: ring_ops(A) → set(A) → set(A) → prod(set(A), set(A)) → set(A) |
| `RegularPointOrderDef` | `regular_point_order`: ring_ops(A) → set(A) → set(A) → prod(set(A), set(A)) → A → int |
| `RegularPointEvaluationDef` | `regular_point_evaluation`: ring_ops(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → A → A |
| `SinglePointPoleSpaceDef` | `single_point_pole_space`: ring_ops(A) → set(A) → set(A) → prod(set(A), set(A)) → num → module_ops(A, A) |
| `RegularPointOrderAndFiltration` | At a regular rational point the order is a valuation, evaluation is a ring map onto k with kernel the maximal ideal, and the pole spaces L(nP) grow by at most one dimension a step, cut out by the order |

## The residue field

Every function regular at a rational point differs from exactly one constant by a member of the maximal ideal; taking that constant is a ring map onto k.

| Member | Statement |
|---|---|
| `EvaluationAtRationalPoint` | The local ring at a rational point has residue field k: evaluation is a ring map onto k, fixing k, with kernel the maximal ideal |

## The order

At a regular rational point the local ring is the localization of the point's chart at an ideal that is rational and invertible there, so its maximal ideal is invertible, every nonzero function generates exactly one of its integer powers, and the exponent is a valuation (`subring_localization.OrderAtChartPoint`).

| Member | Statement |
|---|---|
| `OrderAtRegularPoint` | Every nonzero function generates exactly one integer power of the maximal ideal, the powers decrease strictly, and the exponent is a valuation |
| `RegularPointChart` | A regular rational point lies in a chart that is a subring holding k with fraction field L and finite principal colengths, where its ideal is rational and invertible |

## The pole filtration

L(nP) is the meet of the charts' (−n)-th powers of P's ideals; it grows by at most one dimension a step, the order at P cuts it out of L(mP), and its functions are regular at every other regular point.

| Member | Statement |
|---|---|
| `PoleSpaceCharts` | L(nP) is the meet of the two charts' (−n)-th signed powers of P's ideals |
| `RegularPointLocalRing` | At a regular point P's ideal is maximal and invertible in its chart, the local ring's maximal ideal is invertible, and P's signed powers lie in the same powers of that maximal ideal, which are fractional ideals there |
| `OrderReadsPowers` | A nonzero function lies in the j-th power of the maximal ideal exactly when j is at most its order |
| `PoleFiltrationAtRegularPoint` | L(nP) grows by at most one dimension per step, is cut out by the order at P, and is regular at every other regular point |
| `PoleSpaceRegularElsewhere` | A function with poles only at P is regular at every other regular point |
| `PoleSpaceCutByLocalPower` | Within L(mP), a function lying in the (−n)-th power of the maximal ideal of the local ring at P whenever it is nonzero lies in L(nP) |
| `PoleSpaceCutByOrder` | Within L(mP), the functions that are zero or of order at least −n are L(nP) |

## Pole spaces at a regular point

The powers of the inverse of P as lattice pairs, the nested k-subspaces L(n) their sections form, their dimensions between n + 1 − g and n + 1, and the orders at P of what lies in them.

| Member | Statement |
|---|---|
| `PolePairDegree` | The n-th power of the inverse of a regular point is invertible of degree n |
| `PoleSpaceSubmodule` | Each pole space is a k-submodule of the function field |
| `PoleSpaceModule` | A pole space is a module over the constants |
| `PoleSpacesNested` | The pole spaces increase with the order of the pole |
| `SinglePointPoleFiltration` | The spaces of functions with poles of order at most n at a regular point start at the constants, add budgets under products, and grow by at most one dimension, the n-th having dimension between n + 1 - g and n + 1 |
| `PoleOrderBounds` | A nonzero function with poles of order at most n at P has order between -n and 0 there |
| `PoleOrderAdaptedBasis` | The pole space of order a has a finite k-basis of distinct orders between -a and 0 |
| `PoleProductBudget` | Poles of order at most m times poles of order at most l are poles of order at most m + l |
| `PolePowerBudget` | The n-th power of a function with poles of order at most b has poles of order at most n * b |
| `PoleBasisInField` | A basis of a pole space lies in the function field, misses zero, and is independent over k |
| `PolesHoldOne` | One lies in every pole space at a regular point |

## Zeros of a section

Multiplication by a nonzero f with poles of order at most n at P maps N⁻¹ into the structure pair, and f · N⁻¹ stands in for the zero divisor of f, which f need not have on a model singular elsewhere: invertible of degree −n and inside the ideal of each zero of f off P, so f has at most n regular zeros off P.

| Member | Statement |
|---|---|
| `EvaluationZeroInIdeal` | At a regular point a member of the point's chart killed by evaluation lies in the point's ideal |
| `SectionZerosInside` | For a nonzero section f with poles at P, the pair f · N⁻¹ lies in the structure pair and in the ideal of every zero of f off P |
| `NonzeroSectionZeroCount` | A nonzero section with poles of order at most n at P has at most n regular zeros off P |

