# fractional_ideal — the submodules of a field over a subring, their products and inverses, and the invertible ones

A fractional ideal of a subring S of a field L is an S-submodule of L.
Two of them multiply: M · N is the S-submodule spanned by the products
m · n. Each has an inverse (S : M), the members of L whose product with
every member of M lies in S, and M is invertible when M · (S : M) = S;
more generally a fractional ideal P and a subset N of L have a colon
(P : N), the members y of L with y * n ∈ P for every n ∈ N.

The product is associative and commutative with S as its unit, and it
sees its factors only through their spans. A fractional ideal N with
M · N = S is (S : M), so the invertible fractional ideals form a group
under the product, the nonzero multiples a · S among them, and the
principal ones multiply as their generators do. For a member e of L
with e² in S, S + S · e is a subring of L, free over S on one and e when
only c = d = zero gives c + d · e = zero.

Four chapters build on this one. invertible_fractional_ideal writes an
invertible fractional ideal as a partition of unity and reads off its
generators, its denominators and when the ideal of a point is
invertible; signed_ideal_power gives it integer powers; ideal_colength
compares the quotients of ideals before and after multiplying by it;
and subring_localization extends fractional ideals along subrings and to
the localization at a prime, where the order at a rational point is
read.

Every statement is read under the bundle `∀L:field_on(A)`, with S a
subring of L, `subring(field_ring(L), S)`.

## Members

### The definitions

| Member | Statement |
|---|---|
| `FractionalMulDef` | `fractional_mul(L, S, M, N)`: the S-submodule of L spanned by the products of M and N |
| `FractionalInverseDef` | `fractional_inverse(L, S, M)`: the members of L whose product with M lies in S |
| `InvertibleFractionalDef` | `invertible_fractional(L, S, M)`: an S-submodule whose product with its inverse is S |

### The field as a module over a subring

| Member | Statement |
|---|---|
| `FieldModuleOn` | L is a module over each subring S, S acting by the field's product |
| `SubringSubmodule` | a subring `S` is a fractional ideal of itself: `S` is an `S`-submodule of `L` |
| `IntegralIdealFractional` | the ideals of `S` are exactly the fractional ideals contained in `S`: `ring_ideal(S, I) ⇔ I` is an `S`-submodule of `L` and `I ⊆ S` |
| `FractionalSumIn` | a finite sum of members of a fractional ideal lies in it |
| `SpanHoldingOne` | a subset `X` of `S` holding `one` spans `S`: `span_S(X) = S` |
| `SpanHoldingUnit` | a subset of S holding a unit of S spans S |
| `SpanInSubringIsIdealSpan` | a subset X of S spans, inside L, the ideal of S it generates: span_S(X) = ideal_span(S, X) |
| `SubringTowerSpan` | spanning sets multiply over a tower R ⊆ S of subrings: B spanning S over R and C spanning I over S inside L, the products b · c span I over R — the subring form of `field_extension.TowerSpan` |
| `FractionalMulSubmodule` | the product of two subsets of L is a fractional ideal |
| `ColonSubmodule` | the colon (P : N), the members y of L with y * n ∈ P for every n ∈ N, is a fractional ideal for a fractional ideal P and N ⊆ L |
| `FractionalInverseSubset` | (S : M) ⊆ L |
| `FractionalInverseSubmodule` | (S : M) is a fractional ideal for every subset M of L |

### One and an element

| Member | Statement |
|---|---|
| `SpanOneAndElement` | for a member e of L, one and e span S + S · e, the p + q · e with p and q in S |
| `RingOneAndElement` | when e² lies in S, S + S · e is a ring under the field's operations, inside L, holding S and e |
| `BasisOneAndElement` | when c + d · e = zero with c and d in S forces c = d = zero, S + S · e is free over S on one and e, and one ≠ e |

### The laws of the product

| Member | Statement |
|---|---|
| `FractionalMulHolds` | m * n ∈ M · N for m ∈ M and n ∈ N |
| `FractionalMulLeast` | M · N lies in every fractional ideal holding the products m * n |
| `FractionalMulMono` | M ⊆ M' and N ⊆ N' give M · N ⊆ M' · N' |
| `FractionalMulSpan` | span(M) · N = M · N |
| `FractionalMulSpanRight` | M · span(N) = M · N |
| `FractionalMulAssoc` | (M · N) · P = M · (N · P) |
| `FractionalMulComm` | M · N = N · M |
| `FractionalMulOne` | S · M = M for a fractional ideal M |
| `FractionalIdealsCommMonoid` | the S-submodules of L form a commutative monoid under multiplication, with identity S |

### The inverse

| Member | Statement |
|---|---|
| `FractionalInverseUnique` | a fractional ideal N with M · N = S is (S : M), and M is invertible |
| `FractionalInverseOfUnit` | The fractional inverse into S of a set holding 1 lies in S |
| `FractionalInverseHoldsOne` | one lies in the fractional inverse into a subring S of any set inside S |

### Products and inverses of invertible fractional ideals

| Member | Statement |
|---|---|
| `SubringInvertible` | S is invertible and its own inverse |
| `InvertibleProduct` | M · N is invertible, with inverse (S : M) · (S : N) |
| `InvertibleInverse` | (S : M) is invertible, its inverse M |
| `InvertibleIdealPowers` | the natural powers Nⁿ of an invertible ideal N inside S are invertible and lie inside S |

### Multiples

| Member | Statement |
|---|---|
| `FractionalInverseScale` | for a ≠ zero in L and X ⊆ L, (S : a · X) = inv(a) · (S : X) |
| `ScaleSubmodule` | a · M is a fractional ideal for a fractional ideal M and a ∈ L |
| `ScaleOne` | one · M = M for M ⊆ L |
| `ScaleScale` | b · (a · M) = (b · a) · M for a and b in L and M ⊆ L |
| `FractionalMulScale` | (a · M) · N = a · (M · N) for a ∈ L and M, N ⊆ L |
| `PrincipalProduct` | (x · S) · (y · S) = (x * y) · S for x and y in L |
| `ScaleCancel` | for a ≠ zero in L and M ⊆ L, inv(a) · (a · M) = M |
| `InvertibleScale` | for a ≠ zero and M ⊆ L, a · M is invertible exactly when M is, and the nonzero multiples a · S are invertible |
