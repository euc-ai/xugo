# roots_of_unity — the multiplicative group of a field, its finite subgroups, which are cyclic, and roots of unity

The nonzero elements of a field form an abelian group under its product,
with the operations `field_units(F)`. Its finite subgroups are cyclic:
in a field the equation x ^ d = 1 has at most d solutions for each
d > 0, the hypothesis of the counting criterion of
algebra/group/cyclic_group, and so the multiplicative group of a finite
field is cyclic.

For a p-th root of unity ζ ≠ 1, p prime, the sum of $\zeta^{a \cdot k}$ over a below
p is p when p divides k and 0 otherwise. An algebraically closed field
of characteristic q holds such a ζ for every prime p ≠ q, and there is
an algebraically closed field of every prime characteristic; the
quadratic Gauss sum (algebra/field/gauss_sum) and quadratic reciprocity
(int_num/quadratic_reciprocity) are argued in such a field.

## Members

| Member | Statement |
|---|---|
| `FieldUnitsDef` | `field_units`: field_ops(A) → group_ops(A) |

## The multiplicative group of a field

The nonzero elements of a field form an abelian group under its product: a
product of nonzero elements is nonzero, as is the inverse of a nonzero
element, and the other axioms are the field's own. A finite subgroup H of
that group is cyclic by the counting criterion, since for d > 0 the
solutions of x ^ d = 1 in H are among the field's, which number at most d.
The multiplicative group of a finite field is the case where H is all the
nonzero elements.

| Member | Statement |
|---|---|
| `FieldUnitsAbelianGroupOn` | The nonzero elements of a field form an abelian group under its product |
| `RestrictFieldUnits` | Restricting the multiplicative group of a field to a set keeps the field's operations |
| `FiniteSubgroupCyclic` | Every finite subgroup of the multiplicative group of a field is cyclic |
| `FiniteFieldUnitsCyclic` | The multiplicative group of a finite field is cyclic |

## Roots of unity of prime order

`prime_order.go`. An element x ≠ e of a commutative monoid with xᵖ = e, p
prime, has xᵏ = e exactly when p divides k. So for a p-th root of unity
ζ ≠ 1 in a field and k not a multiple of p, ζᵏ ≠ 1 while
$(\zeta^k - 1) \cdot \sum_{a<p} \zeta^{a \cdot k} = (\zeta^p)^k - 1 = 0$ by `module.GeometricSum`, and
the sum is 0; when p divides k every term is 1 and the sum is p. In an
algebraically closed field of characteristic q ≠ p, a root of
$1 + X + \dots + X^{p-1}$ is a p-th root of unity, and it is not one because
that polynomial takes the value p · 1 ≠ 0 at one.

| Member | Statement |
|---|---|
| `PowIdentityIffPrimeDivides` | In a commutative monoid, an element x ≠ e with xᵖ = e for a prime p has xᵏ = e exactly when p divides k |
| `RootOfUnityPowerSum` | For a p-th root of unity ζ ≠ 1 in a field, p prime, the sum of $\zeta^{a \cdot k}$ over a below p is p when p divides k and 0 otherwise |
| `RootOfUnityInClosedField` | An algebraically closed field of prime characteristic q holds, for every prime p ≠ q, a p-th root of unity other than one |
| `ClosedFieldOfCharacteristic` | For every prime q there is an algebraically closed field of characteristic q, stated both as the field's characteristic and as its ring's prime characteristic |
