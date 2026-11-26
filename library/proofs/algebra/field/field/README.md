# field — a commutative ring whose one is not zero, with inverses

A field is a record `F:field_ops(A)` holding `add`, `zero`, `neg`,
`mul`, `one`, `sub`, `inv`, `div` and `carrier`. The predicate
`field_on(F)` says its ring projection `field_ring(F)` is a commutative
ring, its carrier is closed under inverse, zero and one are distinct,
each nonzero member has a left inverse, inverse zero is zero, and
division of members is multiplication by inverse.

The predicate `field(F)` states the original field axioms on every
element of A, using F's operations; its meaning does not depend on
`F.carrier`. The bridge `FieldOnUniverse` identifies it with
`field_on(restrict_field(F, 𝕌))`. Each carrier law keeps its guarded
`On` interface, while its bare whole-type view reads through
`FieldAtUniverse`. The ring projections are `Ring`, concluding
`comm_ring(field_ring(F))`, and `RingOn`, concluding
`comm_ring_on(field_ring(F))`. Subfields, fraction fields and residue
fields use carrier records and the same carrier laws.

Inverse is total and fixes zero. This makes division by zero zero and
lets involution, multiplicativity and the zero test hold on every
carrier member. A cancellation law still asks for a nonzero divisor.

The record fields carry the arithmetic notation: `x + y`, `x - y`,
`x * y`, `-x` and `x / y`; inverse is `F.inv(x)`. A law written through
`FieldOn.Law` binds the record as `F`, and a law over an arbitrary field
may open with `∀F:field_on(A).`.

## Records

| Member | Statement |
|---|---|
| `FieldOpsData` | `mk_field` packs the operations and carrier |
| `FieldRingDef` | `field_ring(F)` keeps the ring operations and carrier |
| `RestrictFieldDef` | `restrict_field(F, K)` keeps the operations and replaces the carrier by `K` |
| `RestrictFieldRing` | `restrict_ring(field_ring(F), S) = field_ring(restrict_field(F, S))`: restriction commutes with taking the ring |
| `FieldOnRing` | `field_on(F) ⇒ field_on(mk_field(field_ring(F).add, …, F.inv, F.div, field_ring(F).carrier))`: a field is the field its ring's operations make with its inverse and division |
| `RestrictFieldRecords` | Restricting the ring or the regular module of the restricted field K to a set gives the restriction of M's |

## The structures and their axioms

The field on a set adds one closure axiom, which has no whole-type
form: on `𝕌` it says nothing. The other closures a proof needs are the
ring's (`comm_ring.ZeroIn`, `OneIn`, `AddIn`, `NegIn`, `MulIn`, `SubIn`),
read at `RingOn`, and closure under division is a law. Each other axiom below has two
members, the axiom of the field on the set and its view on the whole
type. The table spells the whole-type statement; the set's member guards
each variable of it by membership in `F.carrier`, ahead of the law's own
hypothesis (`x ∈ F.carrier ⇒ x ≠ F.zero ⇒ F.inv(x) * x = F.one`).

| member | statement |
|---|---|
| `Field` | `field(F)` ⇔ the commutative ring, `F.one ≠ F.zero`, `x ≠ F.zero ⇒ F.mul(F.inv(x), x) = F.one`, `F.inv(F.zero) = F.zero` and `F.div(x, y) = F.mul(x, F.inv(y))` |
| `FieldOn` | `field_on(F)` ⇔ the commutative ring on `F.carrier`, `F.carrier` closed under `F.inv`, `F.one ≠ F.zero`, `F.inv(F.zero) = F.zero`, and the left inverse and the quotient for members of `F.carrier` |
| `FieldOnUniverse` | `field(F) ⇔ field_on(restrict_field(F, 𝕌))` |
| `Ring` | `comm_ring(field_ring(F))` |
| `RingOn` | `comm_ring_on(field_ring(F))` |
| `InvIn` | `x ∈ F.carrier ⇒ F.inv(x) ∈ F.carrier` |
| `DivIn` | `x ∈ F.carrier ∧ y ∈ F.carrier ⇒ x / y ∈ F.carrier` |

| whole type | on a set | statement |
|---|---|---|
| `OneNotZero` | `OneNotZeroOn` | `F.one ≠ F.zero` |
| `MulLeftInverse` | `MulLeftInverseOn` | `x ≠ F.zero ⇒ F.inv(x) * x = F.one` |
| `InvZero` | `InvZeroOn` | `F.inv(F.zero) = F.zero` |
| `DivMulInv` | `DivMulInvOn` | `x / y = x * F.inv(y)` |

## The inverse

The inverse's arithmetic comes from one law: a factor that multiplies y
to one is inv(y) (`InvLeftUnique`). `InvRightUnique`, `InvInv`,
`InvOne`, `InvMul` and `InvNeg` each exhibit a product equal to one and
let uniqueness name a factor; `InvInv`, `InvMul` and `InvNeg` hold at
zero as well, because the inverse of zero is zero, so none of the three
carries a nonzero hypothesis. `MulRightInverse` is the axiom read from
the other side, and `InvEqZero` holds because a nonzero x with
`F.inv(x) = F.zero` would make one zero. On the set, a term a law forms — `F.inv(x)`, a
product, a negation — lies in `F.carrier` by the closure law named beside it,
`InvIn` for the inverse and the ring's for the rest.

| whole type | on a set | statement |
|---|---|---|
| `MulRightInverse` | `MulRightInverseOn` | `x ≠ F.zero ⇒ x * F.inv(x) = F.one` |
| `InvLeftUnique` | `InvLeftUniqueOn` | `x * y = F.one ⇒ F.inv(y) = x` |
| `InvRightUnique` | `InvRightUniqueOn` | `x * y = F.one ⇒ F.inv(x) = y` |
| `InvInv` | `InvInvOn` | `F.inv(F.inv(x)) = x` |
| `InvOne` | `InvOneOn` | `F.inv(F.one) = F.one` |
| `InvMul` | `InvMulOn` | `F.inv(x * y) = F.inv(x) * F.inv(y)` |
| `InvNeg` | `InvNegOn` | `F.inv(-x) = -F.inv(x)` |
| `InvEqZero` | `InvEqZeroOn` | `F.inv(x) = F.zero ⇔ x = F.zero` |
| `MulEqZero` | `MulEqZeroOn` | `x * y = F.zero ⇔ x = F.zero ∨ y = F.zero` |
| — | `SquareRootsOfSquare` | `z, w ∈ F.carrier ⇒ (w * w = z * z ⇔ w = z ∨ w = -z)`: the square roots of z·z are z and −z |
| — | `FieldSquareRoots` | `F.one + F.one ≠ F.zero ⇒ (d = F.zero ⇒ has_size(roots, 1)) ∧ (d ≠ F.zero ⇒ has_size(roots, 0) ∨ has_size(roots, 2))`, roots = {z ∈ F.carrier \| z·z = d}: when 2 ≠ 0, zero has one square root and every other element none or two |
| `PowEqZero` | `PowEqZeroOn` | `x ∈ F.carrier ∧ xⁿ = F.zero ⇒ x = F.zero`: only zero has a power equal to zero (the whole-type law without the membership) |

`MulEqZero` is why a field is an integral domain
(`integral_domain.FieldIntegralDomain`): a zero factor absorbs the
product, and a nonzero factor's inverse strips that factor off a
vanishing product, leaving the other factor zero.

`MulBijective`, on the carrier alone: multiplying by a nonzero member c is a bijection of `F.carrier`, multiplying by `F.inv(c)` its inverse there — `c ∈ F.carrier ∧ c ≠ F.zero ⇒ injective_on(F.carrier, F.mul(c)) ∧ image(F.mul(c), F.carrier) = F.carrier`.

## Division

A quotient is a product with an inverse (`DivMulInv`), so each law here
opens the quotient and reasons about the inverse.

| whole type | on a set | statement |
|---|---|---|
| `DivRightMul` | `DivRightMulOn` | `y ≠ F.zero ⇒ x / y * y = x` |
| `DivLeftMul` | `DivLeftMulOn` | `y ≠ F.zero ⇒ y * (x / y) = x` |
| `DivOne` | `DivOneOn` | `x / F.one = x` |
| `DivRefl` | `DivReflOn` | `x ≠ F.zero ⇒ x / x = F.one` |
| `InvDiv` | `InvDivOn` | `F.inv(x / y) = y / x` |

`DivRefl` keeps its hypothesis because the inverse is total: at zero,
`x / x` is `F.zero * F.inv(F.zero)`, which is zero, not one.

## Subfields

`subfield(F, K)` says `K ⊆ F.carrier`, that `K` holds zero and one,
and that addition, negation, multiplication and inverse preserve it.
It is exactly a subset whose restricted record is a field
(`SubfieldFieldOn`). The definition's conditions are available as
`SubfieldSubset`, `SubfieldZero`, `SubfieldOne`, `SubfieldAdd`,
`SubfieldNeg`, `SubfieldMul` and `SubfieldInv`.

`ring_subfield(R, inv, k)` says `k` is a field under `R`'s own operations, with inverse
`inv` and division `x * inv(y)` (`RingSubfieldDef`); it asks neither `k ⊆ R.carrier`
nor a ring on `R.carrier`.

| Member | Statement |
|---|---|
| `CarrierSubfield` | the field's carrier is its own subfield |
| `FieldRingSubfield` | a field is a field under its own ring's operations: `ring_subfield(field_ring(F), F.inv, field_ring(F).carrier)` |
| `SubfieldSubring` | `subfield(F, k) ⇒ subring(field_ring(F), k)` |
| `SubfieldCommRing` | `subfield(F, k) ⇒ comm_ring_on(restrict_ring(field_ring(F), k))`: a subfield is a commutative ring under the field's operations |
| `SubfieldRingSubfield` | `subfield(F, k) ⇒ ring_subfield(restrict_ring(field_ring(F), S), F.inv, k)`: a subfield is a field under the operations of F's ring, restricted to any set |
| `SubfieldSub` | a subfield holds differences |
| `SubfieldDiv` | a subfield holds quotients |
| `SubfieldPowerIn` | a subfield holds the powers of its members |
| `SquareClosedDef` | `square_closed(F, k)`: every member of `k` is the square of a member of `k` |
| `QuadraticFormula` | two being nonzero, a root in `F` of `a + b·x + x·x` with `a`, `b` in a subfield `k` lies in `k` when `b·b − 4a` has a square root in `k` |
| `SubfieldInter` | two subfields meet in a subfield |
| `SubfieldInters` | a nonempty family of subfields meets in a subfield |
| `FieldOnRingSubfield` | `field_on(mk_field(R.add, …, R.sub, inv, div, k)) ⇒ ring_subfield(R, inv, k)`: a field under R's operations, whatever its division |
| `RingSubfieldSubring` | `k ⊆ R.carrier ∧ ring_subfield(R, inv, k) ⇒ subring(R, k)` |
| `RingSubfieldRestrict` | `ring_subfield(restrict_ring(R, S), inv, k) ⇔ ring_subfield(R, inv, k)`: restricting R's carrier keeps its operations |
| `SubfieldTrans` | a subfield of a restricted subfield is a subfield |
| `SubfieldRestrict` | a subfield inside k is a subfield of the restriction to k |

The nonempty hypothesis in `SubfieldInters` is necessary: the empty
meet is `𝕌`, which need not lie in the field's carrier.

## Fraction fields

Inside a field supplied beforehand, a subset S presents the carrier as its fraction field when each member times some nonzero member of S lies in S.

| Member | Statement |
|---|---|
| `FractionFieldCarrierDef` | `fraction_field_carrier(R, S)`: S lies in R's carrier, and each member of the carrier times some nonzero member of S lies in S |
| `FractionFieldCarrierMono` | a carrier made of the fractions of `X` is made of the fractions of every `Y` with `X ⊆ Y ⊆` the carrier |

## Maps

`MapInv` says a map between two field carriers preserving zero, one and
products preserves inverse. The map carries the source carrier into
the target carrier. For a nonzero source member its image and the image
of its inverse multiply to one, so inverse uniqueness applies in the
target; at zero both sides are zero. This applies to multiplicative
maps such as the complex modulus as well as field homomorphisms.
