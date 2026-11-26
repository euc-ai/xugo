# galois_good_open — good opens of a Galois cover of the line

Let L be a regular function field over a finite field k, Galois over k(t) for a transcendental t in L. A good open of L is a chart: a ring C between k[t] with one nonzero a(t) inverted and L, with fraction field L, finite over that ring and kept by every automorphism of L over k(t), such that over each good base point, an algebraic x with a(x) ≠ 0, the geometric points of C form a torsor of the Galois group of L over k(t) and each subgroup's invariant chart reads its quotient off the same points. `galois_good_open(M, k, L, t, C, a)` is that list of clauses. This chapter reads a good open one clause and one derived fact per member, the geometric points of a chart and the action of automorphisms on them, and refines a good open by inverting one more polynomial c(t), which leaves a good open with denominator a·c. That L has a good open is scheme/galois_good_fibres.

## Definitions

| Member | Statement |
|---|---|
| `GeometricEvaluationPointsDef` | `geometric_evaluation_points`: field_ops(A) → set(A) → set(A) → set(A → A) |
| `GeometricFibreDef` | `geometric_fibre`: field_ops(A) → set(A) → set(A) → A → A → set(A → A) |
| `EvaluationActionDef` | `evaluation_action`: ring_ops(A) → set(A) → permutation(A) → (A → A) → A → A |
| `InvariantChartDef` | `invariant_chart`: set(A) → set(permutation(A)) → set(A) |
| `GaloisGoodOpenDef` | `galois_good_open`: field_ops(A) → set(A) → set(A) → A → set(A) → (num → A) → bool |

## A good open, clause by clause

`galois_good_open(M, k, L, t, C, a)` is read one clause at a time, each clause a member of
its own, and the facts that follow from a good open are members too. Every proof that
reads a good open reads it through them by name.

| Member | Statement |
|---|---|
| `GoodOpenRegular` | L is a regular function field over k |
| `GoodOpenConstantsFinite` | k is finite |
| `GoodOpenParameterIn` | t lies in L |
| `GoodOpenParameterTranscendental` | t is transcendental over k |
| `GoodOpenGalois` | L is Galois over k(t) |
| `GoodOpenChartInField` | C lies in L |
| `GoodOpenChartRing` | C is a ring under the operations of M |
| `GoodOpenDenominatorOver` | a is a polynomial over k |
| `GoodOpenDenominatorNonzero` | a is not the zero polynomial |
| `GoodOpenChartHoldsBase` | C holds k[t] with a(t) inverted |
| `GoodOpenChartInverts` | C inverts a(t) |
| `GoodOpenFractionField` | L is the fraction field of C |
| `GoodOpenChartFinite` | C is a finite module over k[t] with a(t) inverted |
| `GoodOpenAutomorphismsKeepChart` | every automorphism of L over k(t) maps C onto itself |
| `GoodOpenFibresTorsors` | over each algebraic x with a(x) ≠ 0 the geometric fibre of C is a torsor of the Galois group of L over k(t), and each subgroup's invariant chart reads its quotient off it |

What follows from a good open, one fact per member:

| Member | Statement |
|---|---|
| `GoodOpenConstantsSubfield` | k is a subfield |
| `GoodOpenFieldSubfield` | L is a subfield |
| `GoodOpenConstantsInField` | k lies in L |
| `GoodOpenRationalSubfield` | k(t) is a subfield |
| `GoodOpenConstantsInRational` | k(t) holds k |
| `GoodOpenParameterInRational` | k(t) holds t |
| `GoodOpenRationalInField` | k(t) lies in L |
| `GoodOpenFiniteExtension` | L is a finite extension of k(t) |
| `GoodOpenGroupFinite` | the group of L over k(t) is finite |
| `GoodOpenPolynomialsSubring` | k[t] is a subring |
| `GoodOpenConstantsInPolynomials` | k[t] holds k |
| `GoodOpenParameterInPolynomials` | k[t] holds t |
| `GoodOpenChartSubring` | C is a subring |
| `GoodOpenPolynomialsInChart` | C holds k[t] |
| `GoodOpenConstantsInChart` | C holds k |
| `GoodOpenParameterInChart` | C holds t |
| `GoodOpenDenominatorInPolynomials` | a(t) lies in k[t] |
| `GoodOpenDenominatorValueNonzero` | a(t) is not zero |
| `GoodOpenDenominatorInChart` | C holds a(t) |
| `GoodOpenDenominatorInverseInChart` | C holds the inverse of a(t) |
| `GoodOpenDenominatorInRational` | a(t) lies in k(t) |
| `GoodOpenDenominatorInverseInRational` | k(t) holds the inverse of a(t) |

## Points and the evaluation action

A geometric point of a ring D over k is a ring map from D to the algebraic elements over k, the identity on k and zero off D; an automorphism acts on the points by precomposition with its inverse.

| Member | Statement |
|---|---|
| `PointAtPolynomialValue` | A point of a ring over k carries the value of a polynomial over k at t to its value at the image of t |
| `GeometricPointMember` | A geometric point of C is a ring map to the algebraic elements, fixing k and zero off C |
| `EvaluationActionIdentity` | The identity fixes a map vanishing off D |
| `EvaluationActionCompose` | The action is multiplicative at g when the inverse of g keeps D |
| `FibreAway` | Restriction is a bijection of the fibre of D[1/c(t)] onto the fibre of D over a point with c(x) ≠ 0 |
| `EvaluationActionPoint` | An automorphism whose inverse keeps D moves points of D to points of D |
| `EvaluationActionKeepsFibre` | An automorphism whose inverse keeps C keeps the points of C and their value at t |
| `InvariantChartFacts` | The invariants of a subring are a subring holding what lies in the fixed base |
| `AutomorphismOnStableRing` | An automorphism keeping a subring is a ring map of it |
| `PointRestricts` | A point of a ring restricts to a point of a subring holding the prescribed set |

## Refining a good open

| Member | Statement |
|---|---|
| `GroupKeepsChart` | The Galois group of a good open holds inverses, and each member and its inverse keep the chart |
| `AwayPowerFacts` | Powers of a nonzero member of K on an extension: nonzero, clearing nothing out of L, moved by automorphisms alone |
| `InvariantChartAway` | Inverting a fixed element commutes with taking invariants |
| `AutomorphismKeepsAway` | C[1/g] lies in L, and an automorphism keeping C keeps it |
| `GoodFibreAway` | The torsor clauses of a good fibre pass to C with c(t) inverted |
| `GaloisGoodOpenLocalize` | Inverting c(t) in a good open leaves a good open with denominator a·c |
| `ChartAwayFacts` | Inverting c(t) in a good open gives a good open between C and L, with c(t) a nonzero member of C |
