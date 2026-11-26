# invertible_fractional_ideal — an invertible fractional ideal as a partition of unity, its generators and denominators, and the invertible ideal of a point

An invertible fractional ideal M of a subring S of a field L writes one
as a finite sum one = Σ x(i) * y(i) with x(i) ∈ M and y(i) ∈ (S : M).
That makes M finitely generated and makes dividing by it taking the
colon, Y · (S : M) = (Y : M) for every fractional ideal Y, so that
(M : M) = S. When L is the field of fractions of S, M has a common
denominator in S and holds a nonzero principal ideal c · S.

Two criteria make the ideal of a point invertible. The ideal (u, v) of S
is invertible as soon as u ≠ zero, u and v satisfy a relation
v * g = u * h, and u, v, g and h span S: the ratio g/u lies in
(S : (u, v)). At the ideal of a k-rational point this is the curve's
Jacobian criterion, the ideal invertible where one of the relation's
coefficients does not vanish at the point. And a maximal ideal is
invertible when one of its nonzero members generates it away from the
ideal.

Every statement is read under the bundle `∀L:field_on(A)`, with S a
subring of L, `subring(field_ring(L), S)`.

## Members

### Generators and denominators

| Member | Statement |
|---|---|
| `InvertiblePartitionOfUnity` | an invertible M writes one as a finite sum Σ x(i) * y(i) with x(i) ∈ M and y(i) ∈ (S : M) |
| `PartitionOfUnityExpansion` | for one = Σ x(i) * y(i) with x(i), y(i) in L, every c ∈ L is Σ (c * x(i)) * y(i) |
| `InvertibleGenerated` | an invertible M is the span of a finite subset |
| `MulInverseIsColon` | for an invertible X and a fractional ideal Y, Y · (S : X) is the colon (Y : X), the members a of L with a · X ⊆ Y |
| `InvertibleSelfColon` | for an invertible X the colon (X : X), the members z of L with z · X ⊆ X, is the ring S |
| `InverseMulInside` | For Y inside an invertible fractional ideal X ⊆ S, the product X⁻¹Y lies in S, and in each prime of S holding Y but not X |
| `InvertibleCommonDenominator` | when L is the field of fractions of S, an invertible M has d · M ⊆ S for some nonzero d ∈ S |
| `InvertibleContainsPrincipal` | when L is the field of fractions of S, an invertible J holds c · S for some nonzero c ∈ S |

### A criterion at a point

| Member | Statement |
|---|---|
| `RelationIdealInvertible` | m = (u, v) is invertible when u ≠ zero, v * g = u * h with g, h in S, and u, v, g and h span S: g/u lies in (S : m) |
| `LocallyPrincipalMaximalInvertible` | a maximal ideal m of S holding a nonzero u that some s outside m carries into u·S, s·m ⊆ u·S, is invertible |
| `JacobianRelationInvertible` | m = (u, v) with S = k + m and v * g = u * h is invertible when g ∉ m and u ≠ zero, or h ∉ m and v ≠ zero |
