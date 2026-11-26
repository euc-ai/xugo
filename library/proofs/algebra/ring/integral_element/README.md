# integral_element — monic relations, common denominators and fraction fields over subrings

Integral elements are roots of positive-degree monic polynomials over a subring. Short powers generate their algebras; a fraction-field representation clears finitely many denominators without imposing a principal ideal domain hypothesis. Inside a field, the field a subring S generates is the fraction field of S (`SubringFractionField`), and k(t) is the instance at the values k[t] (`RationalFunctionsFractionField`). A subring with fraction field L that finitely many of its members span over a subfield K makes them span L over K (`FiniteSubringSpansField`), and a set independent over a subring stays independent over its fraction field (`IndependentOverFractionField`). The fraction fields here are subfields of L, read by `fraction_field_carrier`; `ring_localization` builds the fractions of a domain as classes of pairs. Two homomorphisms out of S agreeing on S and at z agree on S[z] (`PolynomialImageAgreement`); the extensions of a homomorphism of S to S[z] are `algebraic_element`'s lifts.

The elements integral over any subring S form a subring holding S (`IntegralElementsSubring`), by the determinant trick. An element z with z·e = P·e for a matrix P over S and a nonzero vector e in the field makes det(z·I − P) vanish (`vector/determinant`'s `DeterminantDependentColumns`), and that determinant is the value at z of a monic polynomial over S (`CharacteristicPolynomial`), so z is integral over S (`EigenvalueIntegral`). So an element z of the field that multiplies into itself a nonzero S-module spanned by finitely many members of the field is integral over S (`FinitelySpannedIntegral`), and S[x][y] is such a module for x + y, −x and x·y when x and y are integral (`IntegralAddNegMul`), so a finite sum of integral elements is integral (`IntegralModuleSum`). `principal_ideal_domain.StableModuleIntegral` reads the criterion for a finitely generated submodule holding one: its generators span it in the field, and one is its nonzero member. A root of a monic polynomial over the field, scaled by a member of S that brings every coefficient into S, is integral over S (`ScaledRootIntegral`). An element algebraic over a subfield k is integral over k, its minimal polynomial being monic over k (`AlgebraicIntegral`).

## Members

| Member | Statement |
|---|---|
| `IntegralOverDef` | `integral_over`: ring_ops(A) → A → bool |
| `IntegrallyClosedDef` | `integrally_closed_in`: ring_ops(A) → set(A) → bool |
| `IntegralClosureDef` | `integral_closure`: ring_ops(A) → set(A) → set(A) — the members of K integral over R |
| `BoundedFractionalDef` | `bounded_fractional`: ring_ops(A) → set(A) → set(A) → bool |
| `FiniteCommonDenominator` | finitely many members of L have a common nonzero denominator in S, when L is the fraction field of S |
| `FiniteSpanCommonDenominator` | the S-span of finitely many members of L has a common nonzero denominator in B, when L is the fraction field of the subring B and B is an S-submodule |
| `PolynomialImageSubmodule` | Polynomial values over a subring form a submodule of the ambient field. |
| `IntegralPowerSpan` | Short powers below the degree of a monic relation span the polynomial values. |
| `SubringFractionField` | the field a subring S of a field generates is a subfield containing S, and it is the fraction field of S |
| `MonicSubringPowerBasis` | A minimal polynomial over a subring gives the short power basis of its polynomial image. |
| `RationalFunctionsFractionField` | inside a field L, the field k(t) that a subfield k and an element t generate is the fraction field of the polynomial values k[t] |
| `FiniteSubringSpansField` | finitely many members of a subring of L with fraction field L, spanning it over a subfield K, span L over K |
| `IndependentOverFractionField` | a set independent over a subring S of a field stays independent over the fraction field K of S |
| `PolynomialImageAgreement` | Two homomorphisms agreeing on S and at z agree on S[z] |
| `HomomorphismSeparatesSimpleRoots` | A homomorphism to a nonzero ring keeps apart two roots at which the derivative is a unit |
| `AdjoinCommonDenominator` | A member of K(z) is cleared into B[z] by a denominator from B, for K the fraction field of B and z algebraic |
| `FiniteAdjoinDenominator` | Finitely many members of K(z) share one such denominator |
| `RootsOfImagePolynomial` | Each root of the image of a monic p vanishing on a finite Y of its degree is the image of a point of Y |
| `IntegralShortRepresentative` | A member of S[x], x a root of a monic p over S, is the value at x of a polynomial over S of degree below deg p |
| `AlgebraicOverFractionSubring` | An element algebraic over the fraction field of a subring S is algebraic over S |
| `PolynomialCommonDenominator` | A polynomial over a subfield B of L, B the fraction field of the subring S, has a common nonzero denominator d ∈ S: every d · p(i) lies in S |
| `CharacteristicPolynomial` | for a square matrix P over a subring S and z in the field, det(z·I − P) is the value at z of a monic polynomial over S of degree n |
| `EigenvalueIntegral` | an eigenvalue of a square matrix over S with an eigenvector in the field that is not zero is integral over S |
| `FinitelySpannedIntegral` | an element z of a field is integral over a subring S when multiplication by z keeps a nonzero S-module spanned by a finite subset of the field |
| `IntegralAddNegMul` | the sum, negative and product of two elements integral over S are integral over S |
| `IntegralModuleSum` | a finite sum of elements of a field integral over a subring S is integral over S |
| `IntegralElementsSubring` | the elements of a field integral over a subring form a subring holding it |
| `ScaledRootIntegral` | a root x of a monic polynomial over L, scaled by a d ∈ S that brings every coefficient into S, gives d·x integral over S |
| `AlgebraicIntegral` | an element of L algebraic over a subfield k is integral over k |
| `IntegralOverMono` | integrality over a subset of a ring passes to any larger subset, by the same monic relation |
