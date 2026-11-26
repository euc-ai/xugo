# curve_degree — the degree of an invertible pair on a curve finite over the projective line, divisors of points, and Pic⁰

On a curve finite over the projective line (scheme/algebraic_curve), the
degree of an invertible pair is deg M = χ(M) − χ(O). It is unchanged
by scaling and isomorphism, and twisting at a regular point raises it by
one, each chart and the overlap gaining the point's colength. A nonzero
section a puts a · O inside M, and the three chart quotients of M by it
force deg M ≥ 0, with M = a · O at degree zero and M = a · O(P) for a
regular point P at degree one. Additivity over products compares M and
O with their common subpair K = M ∩ O, then multiplies both inclusions
by N, which keeps the chart and overlap quotient dimensions. A divisor
is an integer multiplicity at finitely many regular points — a point is
its ideal pair, so a divisor is a function on pairs of subsets of L —
and its pair O(D) is the product of the powers $P^{-D(P)}$, a fold over
the support that does not depend on an order because the invertible
pairs commute. Rational points that are not regular, such as a cusp,
carry no multiplicity: their ideals are not invertible, so a twist
there leaves the invertible pairs and P · P⁻¹ is not O.

## Members

### The degree

| Member | Statement |
|---|---|
| `CurveDegreeDef` | `curve_degree(field_ring(L), k, A₀, A₁, A₀₁, M)`: deg M = χ(M) − χ(O) |
| `DegreeStructure` | deg O = 0 |
| `DegreeScale` | a nonzero multiple of an invertible pair has its degree |
| `DegreeIso` | a pair isomorphic to an invertible pair has its degree |
| `DegreeTwist` | twisting an invertible pair at a regular point raises its degree by one |
| `SectionDegreeNonneg` | an invertible pair with a nonzero section has degree at least zero |
| `DegreeZeroSectionTrivial` | an invertible pair of degree zero with a nonzero section a is a · O — card |
| `LargeDegreeHasSection` | an invertible pair of degree at least g has a nonzero section |
| `ProductQuotientDimensions` | for invertible pairs M and N and a lattice subpair K of M with finite chart quotients, multiplying by N keeps the chart and overlap quotients finite and their dimensions |
| `DegreeAdditive` | deg(M · N) = deg M + deg N for invertible pairs |
| `DegreeInverse` | deg M⁻¹ = −deg M |
| `InvertibleInsidePointsDegree` | an invertible pair inside the structure pair and inside a finite set S of regular points has degree at most −card(S) |
| `DegreeOneSectionIsPoint` | an invertible pair of degree one with a nonzero section a is a · O(P) for a regular point P — card |
| `RiemannRochEuler` | χ(M) = deg M + 1 − g |
| `NegativeDegreeNoSections` | an invertible pair of negative degree has no sections: ℓ(X) = 0 |

### Divisors

| Member | Statement |
|---|---|
| `CurveDivisorDef` | `curve_divisor(field_ring(L), k, A₀, A₁, A₀₁, D)`: integer multiplicities, nonzero at finitely many pairs and only at regular points |
| `CurveDivisorDegreeDef` | `curve_divisor_degree(D)`: deg D, the sum of the multiplicities over the support |
| `CurveDivisorPairDef` | `curve_divisor_pair(field_ring(L), A₀, A₁, A₀₁, D)`: O(D), the product of the powers $P^{-D(P)}$ over the support |
| `DivisorFoldRecursion` | the fold of D's steps over a finite set of pairs starts at O, a new pair applies its step, and every such fold is invertible |
| `DivisorLatticeInvertible` | O(D) is an invertible pair |
| `DivisorLatticeDegree` | deg O(D) = deg D |
| `DivisorLatticeAdd` | D + E is a divisor and O(D + E) = O(D) · O(E) — card |
| `DivisorLatticePoint` | the divisor n · P has degree n, and O(P) is the twist of O at P, O(−P) = P — card |
| `PrincipalDivisorDegree` | a divisor whose pair is a nonzero multiple of O has degree zero |

### Pic⁰

Being a nonzero multiple is an equivalence on the invertible pairs, and
its classes are the pairs up to isomorphism. Pic⁰ is the quotient of
the invertible pairs of degree zero by it — relations/equivalence's
`quotient_on` — and an abelian group under the product of classes; a
regular base point E sends a regular point P to the class of O(P − E).

| Member | Statement |
|---|---|
| `curvePairMultipleDef` | `curve_pair_multiple(L, M, N)` ⇔ N = a · M for a nonzero a of the field |
| `CurvePairClassDef` | `curve_pair_class(L, M)`: the class of M under curve_pair_multiple, its nonzero multiples |
| `CurveClassMulDef` | `curve_class_mul(L, A₀, A₁, X, Y)`: the products of members of two classes |
| `CurveClassInverseDef` | `curve_class_inverse(L, A₀, A₁, X)`: the inverses of the members of a class |
| `CurvePicZeroDef` | `curve_pic_zero(L, k, A₀, A₁, A₀₁)`: the quotient of the invertible pairs of degree zero by curve_pair_multiple |
| `CurvePointClassDef` | `curve_point_class(L, A₀, A₁, E, P)`: the class of E(P) = O(P − E) |
| `PairMultipleEquivalenceOn` | being a nonzero multiple is an equivalence on the invertible pairs |
| `PairMultipleInvertible` | a nonzero multiple of an invertible pair is invertible |
| `InPicZero` | the members of Pic⁰ are exactly the classes of the invertible pairs of degree zero |
| `PairClassEqIff` | two invertible pairs have one class iff one is a nonzero multiple of the other |
| `PairClassMul` | class(M) · class(N) = class(M · N) |
| `PairClassInverse` | class(M)⁻¹ = class(M⁻¹) |
| `PicZeroGroupOn` | Pic⁰ is a group under the product of classes, unit the class of (A₀, A₁) — card |
| `PicZeroAbelian` | Pic⁰ is an abelian group — card |
| `PointClassDegreeZero` | for regular E and P, O(P − E) is invertible of degree zero and its class lies in Pic⁰ — card |
