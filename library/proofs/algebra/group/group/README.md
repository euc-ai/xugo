# group — groups, subgroups, normal subgroups and cosets

A group is described by a value `G:group_ops(A)`, which holds its product
`G.mul`, identity `G.one`, inverse `G.inv` and carrier `G.carrier`.
`group_on(G)` requires the carrier to contain the identity, be closed
under the product and inverse, and satisfy associativity, left identity
and left inverse. The right laws follow from these one-sided axioms.
Under this structure `x * y` is `G.mul(x, y)`.

Every carrier law has membership guards for the points it uses.
`group(G)` states the original three group axioms on all of `A`,
independently of `G.carrier`. `GroupOnUniverse` proves
`group(G) ⇔ group_on(restrict_group(G, 𝕌))`. Each whole-type law is
the view of its carrier law through `GroupAtUniverse`.
A subgroup uses `restrict_group(G, h)`, which keeps the operations and
replaces the carrier by `h`. Quotients use a carrier of cosets, a subset
of `set(A)`, and read the same laws at their group record.

## The structure and its axioms

| member | statement under `group_on(G)` |
|---|---|
| `GroupOpsData` | `mk_group` packs product, identity, inverse and carrier; its fields project them |
| `RestrictGroupDef` | `restrict_group(G, h) = mk_group(G.mul, G.one, G.inv, h)` |
| `GroupOn` | carrier closure and the three one-sided group axioms |
| `OneIn` | `G.one ∈ G.carrier` |
| `MulIn` | `x ∈ G.carrier ∧ y ∈ G.carrier ⇒ x * y ∈ G.carrier` |
| `InvIn` | `x ∈ G.carrier ⇒ G.inv(x) ∈ G.carrier` |
| `AssocOn` | `x * (y * z) = (x * y) * z` for carrier points |
| `LeftIdentityOn` | `G.one * x = x` for a carrier point |
| `LeftInverseOn` | `G.inv(x) * x = G.one` for a carrier point |

## The other sides

The inverse of `x` undoes `x` from the left, whatever follows it. The
identity is the only carrier element equal to its own square, and
`x * G.inv(x)` has that property. This proves the right inverse and then
the right identity. These undoing laws keep later proofs from repeatedly
regrouping the same products.

| member | statement for carrier points |
|---|---|
| `InvMulCancelLeftOn` | `G.inv(x) * (x * y) = y` |
| `IdempotentIsOneOn` | `e * e = e ⇒ e = G.one` |
| `RightInverseOn` | `x * G.inv(x) = G.one` |
| `MulInvCancelLeftOn` | `x * (G.inv(x) * y) = y` |
| `RightIdentityOn` | `x * G.one = x` |
| `MulInvCancelRightOn` | `(y * x) * G.inv(x) = y` |
| `InvMulCancelRightOn` | `y * G.inv(x) * x = y` |

## Cancellation and the inverse

Cancellation reads a factor back out by multiplying by an inverse.
A left inverse is unique in the carrier; the inverse of a product is
the product of the inverses in reverse order.

| member | statement for carrier points |
|---|---|
| `LeftCancelOn` | `x * y = x * z ⇔ y = z` |
| `RightCancelOn` | `y * x = z * x ⇔ y = z` |
| `InvUniqueOn` | `x * y = G.one ⇔ x = G.inv(y)` |
| `InvMulEqOneOn` | `G.inv(x) * y = G.one ⇔ x = y` |
| `InvInvOn` | `G.inv(G.inv(x)) = x` |
| `InvMulOn` | `G.inv(x * y) = G.inv(y) * G.inv(x)` |
| `InvOneOn` | `G.inv(G.one) = G.one` |

## Subgroups and normal subgroups

`subgroup(G, h)` says `h ⊆ G.carrier`, contains `G.one`, and is closed
under `G.mul` and `G.inv`. These closure conditions make sense for every
record; under `group_on(G)`, they are equivalent to `h` being a subset
whose restricted record is a group. Normality adds invariance under
conjugation by points of the ambient carrier.

| member | statement |
|---|---|
| `SubgroupDef` | `subgroup(G, h)` is inclusion and the three closure conditions |
| `SubgroupSubset`, `SubgroupOne`, `SubgroupMul`, `SubgroupInv` | the four conditions, read separately |
| `SubgroupMulInv` | a subgroup holds the product of one of its members with the inverse of another |
| `SubgroupInvIffOn` | a subgroup holds `G.inv(x)` exactly when it holds a carrier point `x` |
| `TrivialSubgroupOn` | `subgroup(G, {G.one})` |
| `CarrierSubgroupOn` | `subgroup(G, G.carrier)` |
| `SubgroupGroupOn` | `subgroup(G, h) ⇔ h ⊆ G.carrier ∧ group_on(restrict_group(G, h))` |
| `NormalSubgroupDef` | `normal_subgroup(G, h)` is subgroup closure and conjugation invariance |
| `NormalSubgroupSubgroup`, `NormalSubgroupConjugate` | its two conditions |
| `NormalSubgroupSwapOn` | a normal subgroup holds `x * y` exactly when it holds `y * x`, for carrier points |

## Powers of a member

`power.go`. A power of a member is `monoid_pow(G.mul, G.one, x, n)`,
spelled in full because the power's implicit arguments are a monoid's `op`
and `e`, which a group record does not name. The commutative monoid's laws
of exponents need commutativity only to multiply two different bases, so
for one base they hold in any group, proved here on the carrier.

| member | statement |
|---|---|
| `PowIn` | every power of a member lies in the carrier |
| `PowOne` | x ^ 1 = x for a member x |
| `PowAdd` | x ^ (m + n) = x ^ m * x ^ n for a member x — associativity alone, the product need not commute |
| `PowPow` | (x ^ m) ^ n = x ^ (m · n) for a member x |
| `OnePow` | every power of the identity is the identity |
| `PowInSubgroupIffDivides` | the exponents at which a member's powers lie in a subgroup are the multiples of one exponent d (0 when no positive power does) |

## Products of lists

`lists.go`. The product of a list of carrier points, `list_fold(G.mul, l, G.one)`.

| member | statement |
|---|---|
| `FoldIn` | the product of a list of carrier points lies in the carrier |
| `FoldShift` | `list_fold(G.mul, t, b) = list_fold(G.mul, t, G.one) * b` for carrier entries and a carrier point b |
| `RotateProductOne` | moving the head of a list of product G.one to its end keeps the product G.one |

## Cosets

The low-level operation `left_coset(mul, x, h)` moves `h` by multiplying
its members on the left by `x`. It needs only an operation. Under a group
record its operation is supplied explicitly as `G.mul`. For a subgroup,
cosets are the equivalence classes of the relation “lies in the coset
of”. Two cosets are equal exactly when the inverse difference of their
points belongs to the subgroup.

| member | statement |
|---|---|
| `LeftCosetDef` | `left_coset(mul, x, h) = image(λy. mul(x, y), h)` |
| `CosetMapDef` | `coset_map(mul, h) = λx. left_coset(mul, x, h)`, the coset map |
| `LeftCosetIn` | a carrier point's coset of a carrier subset stays in the carrier |
| `InLeftCosetOn` | `y ∈ left_coset(G.mul, x, h) ⇔ G.inv(x) * y ∈ h`, for carrier points and `h ⊆ G.carrier` |
| `LeftCosetOneOn` | `left_coset(G.mul, G.one, h) = h`, for a carrier subset |
| `TranslateCoset` | `left_coset(G.mul, g, left_coset(G.mul, x, h)) = left_coset(G.mul, g * x, h)`, for carrier points and a carrier subset |
| `InOwnLeftCosetOn` | a carrier point lies in its own coset of a subgroup |
| `LeftCosetClass` | a left coset is the corresponding unrestricted relation class |
| `LeftCosetClassOn` | it is also the class inside the carrier |
| `CosetClosedOn` | the carrier is closed under the coset relation of a carrier subset |
| `CosetEquivalenceOn` | the coset relation of a subgroup is an equivalence on the carrier |
| `LeftCosetEqOn` | two cosets of a subgroup are equal exactly when their points differ by a subgroup element |

The counting of a finite group by these classes, Lagrange's theorem,
is the `finite_group` chapter's.

## Whole-type views

The bare names below retain the unguarded whole-type interface. Their
`On` partners are proved on the carrier. In whole-type subgroup laws,
the ambient record is `restrict_group(G, 𝕌)`, so no assumption about
`G.carrier` is introduced.

| whole type | carrier law |
|---|---|
| `Assoc` | `AssocOn` |
| `LeftIdentity` | `LeftIdentityOn` |
| `LeftInverse` | `LeftInverseOn` |
| `InvMulCancelLeft` | `InvMulCancelLeftOn` |
| `IdempotentIsOne` | `IdempotentIsOneOn` |
| `RightInverse` | `RightInverseOn` |
| `MulInvCancelLeft` | `MulInvCancelLeftOn` |
| `RightIdentity` | `RightIdentityOn` |
| `MulInvCancelRight` | `MulInvCancelRightOn` |
| `InvMulCancelRight` | `InvMulCancelRightOn` |
| `LeftCancel` | `LeftCancelOn` |
| `RightCancel` | `RightCancelOn` |
| `InvUnique` | `InvUniqueOn` |
| `InvMulEqOne` | `InvMulEqOneOn` |
| `InvInv` | `InvInvOn` |
| `InvMul` | `InvMulOn` |
| `InvOne` | `InvOneOn` |
| `SubgroupInvIff` | `SubgroupInvIffOn` |
| `TrivialSubgroup` | `TrivialSubgroupOn` |
| `CarrierSubgroup` | `CarrierSubgroupOn` |
| `NormalSubgroupSwap` | `NormalSubgroupSwapOn` |
| `InLeftCoset` | `InLeftCosetOn` |
| `LeftCosetOne` | `LeftCosetOneOn` |
| `InOwnLeftCoset` | `InOwnLeftCosetOn` |
| `LeftCosetEq` | `LeftCosetEqOn` |

`CosetEquivalence` is a whole-type statement and retains its proof.
