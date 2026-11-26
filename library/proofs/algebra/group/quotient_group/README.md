# quotient_group — the group of cosets of a normal subgroup

For `G:group_ops(A)` satisfying `group_on(G)`, a normal subgroup `N`
cuts `G.carrier` into left cosets. These cosets form a group: their
product is the set of products of their members, their identity is `N`,
and their inverse takes the inverse of every member. The quotient's
record is `quotient_group(G, N)`, which `QuotientGroupDef` defines as
`mk_group(set_mul(G.mul), N, set_inv(G.inv), left_cosets(G.mul, G.carrier, N))`.
`QuotientGroupOn` states its group laws. The quotient of a subgroup `h` of
`G` is `quotient_group(restrict_group(G, h), N)`.

Its carrier is a subset of `set(A)`: the cosets of a variable subgroup
form a set. Keeping the carrier in the record lets this quotient and
its subgroups read the same group laws as the original group. Set
multiplication chooses no representatives. The theorem that a product
of cosets is the coset of the product supplies that representative
reading when a proof needs it.

## Operations on sets

The low-level operations take only the data they use. `set_mul` takes
a binary operation, `set_inv` an inverse map, and `left_cosets` an
operation and a carrier set. Under a group law they are supplied as
`set_mul(G.mul, s, t)`, `set_inv(G.inv, s)` and
`left_cosets(G.mul, G.carrier, N)`.

| member | statement |
|---|---|
| `SetMulDef` | `set_mul(mul, s, t) = {mul(x, y) \| x ∈ s ∧ y ∈ t}` |
| `SetMulMono` | the product grows with its right factor — card |
| `SetMulAssoc` | the product of carrier subsets associates — card |
| `InSetMul` | a product-set member is the product of a member of each factor |
| `SetInvDef` | `set_inv(inv, s) = image(inv, s)` |
| `SetMulIn`, `SetInvIn` | products and inverses of carrier subsets stay in the carrier |
| `InSetInvOn` | `z ∈ set_inv(G.inv, s) ⇔ G.inv(z) ∈ s`, for `s ⊆ G.carrier` and `z ∈ G.carrier` |
| `LeftCosetsDef` | `left_cosets(mul, c, N) = quotient_on(c, λx y. y ∈ left_coset(mul, x, N))` |
| `QuotientGroupDef` | `quotient_group(G, N) = mk_group(set_mul(G.mul), N, set_inv(G.inv), left_cosets(G.mul, G.carrier, N))` |
| `LeftCosetsImage` | for a carrier subset, its cosets are the image of the carrier under the coset map |
| `LeftCosetsFinite` | `finite(c) ⇒ finite(left_cosets(mul, c, h))`: a finite set has finitely many left cosets of any set, for any operation |
| `InLeftCosets` | a coset is the coset of some carrier point |
| `LeftCosetInLeftCosets` | a carrier point's coset of a carrier subset is a coset |
| `SubgroupInLeftCosets` | `subgroup(G, N) ⇒ N ∈ left_cosets(G.mul, G.carrier, N)` |
| `ForallInLeftCosets`, `ForallInLeftCosetsPair` | universal statements about cosets read at one or two representatives |

The carrier is closed under the coset relation of a carrier subset.
Its quotient is therefore the image under the class map, and the
classes are the cosets. These membership readings let proofs work with
representatives while the actual operations remain operations on sets.

## The quotient group

Normality permits a factor to pass a factor from the other coset as a
conjugate. It also permits a product in `N` to be reversed, which is
what the inverse calculation needs. With these two laws and
`group.LeftCosetOneOn`, the coset map `x ↦ x·N` carries the product,
the identity and the inverse of `G` to the set product, `N` and the set
inverse, and the cosets are the image of the carrier under it
(`LeftCosetsImage`). `QuotientGroupOn` is then
`group_homomorphism.ImageGroupOn`: the homomorphic image of a group is
a group.

| member | statement under `group_on(G)` |
|---|---|
| `LeftCosetMulOn` | for normal `N` and carrier points `x,y`, the product of their cosets is the coset of `x * y` |
| `LeftCosetInvOn` | the inverse of a carrier point's coset is the coset of its inverse |
| `QuotientGroupOn` | `normal_subgroup(G, N) ⇒ group_on(quotient_group(G, N))` |
| `ProjectionKernelOn` | `subgroup(G, N) ⇒ group_kernel(N, G.carrier, coset_map(G.mul, N)) = N` |
| `LeftCosetIsSubgroupIffIn` | `subgroup(G, h)` ⇒ `left_coset(G.mul, x, h) = h ⇔ x ∈ h` for `x` in `G.carrier` |
| `QuotientTrivialIff` | `subgroup(G, N) ⇒ (left_cosets(G.mul, G.carrier, N) = {N} ⇔ N = G.carrier)` |
| `LeftCosetSetMulAbsorb` | `subgroup(G, k) ∧ h ⊆ k ∧ G.one ∈ h` ⇒ `set_mul(G.mul, left_coset(G.mul, x, h), k) = left_coset(G.mul, x, k)` for `x` in `G.carrier` |

`LeftCosetIsSubgroupIffIn` needs subgroup closure alone: a carrier point's
coset equals `N` exactly when its inverse belongs to `N`, equivalently
when the point does.

## Counting cosets

A set meeting every left coset of a subgroup in exactly one point counts
the cosets. Lagrange's theorem counts a finite group as a subgroup's
order times its index, the number of its left cosets, and a group is
finite exactly when a subgroup and its set of cosets are: the cosets
cover the carrier and each has the subgroup's size. For a subgroup k of
any group, finite or not, and h ⊆ k holding the identity (a subgroup,
say), the index of h is finite exactly when the index of k and that of h
in k are, and it is then their product, [G : h] = [G : k] · [k : h]:
each coset of k splits into [k : h] cosets of h, the translates of the
cosets of h in k. A strictly larger subgroup has a strictly smaller
finite index.

| member | statement under `group_on(G)` |
|---|---|
| `LeftCosetsTransversalSize` | for a subgroup `h`, a set `T ⊆ G.carrier` of size `k` meeting every left coset in exactly one point gives `has_size(left_cosets(G.mul, G.carrier, h), k)` |
| `LagrangeIndex` | `finite(G.carrier) ∧ subgroup(G, h) ⇒ card(G.carrier) = card(h) * card(left_cosets(G.mul, G.carrier, h))`: the order of a finite group is a subgroup's order times its index |
| `FiniteIffSubgroupAndCosets` | `subgroup(G, h) ⇒ (finite(G.carrier) ⇔ finite(h) ∧ finite(left_cosets(G.mul, G.carrier, h)))`: a group is finite exactly when a subgroup and its set of cosets are |
| `IndexMultiplicative` | `subgroup(G, k) ∧ h ⊆ k ∧ G.one ∈ h ⇒ (finite(left_cosets(G.mul, G.carrier, h)) ⇔ finite(left_cosets(G.mul, G.carrier, k)) ∧ finite(left_cosets(G.mul, k, h))) ∧ (finite(left_cosets(G.mul, G.carrier, h)) ⇒ card(left_cosets(G.mul, G.carrier, h)) = card(left_cosets(G.mul, G.carrier, k)) * card(left_cosets(G.mul, k, h)))`: the index is multiplicative along a tower, finite or not; `h` need only lie in `k` and hold the identity |
| `StrictInclusionLowersIndex` | `subgroup(G, h) ∧ subgroup(G, k) ∧ h ⊆ k ∧ h ≠ k ∧ finite(left_cosets(G.mul, G.carrier, h)) ⇒ card(left_cosets(G.mul, G.carrier, k)) < card(left_cosets(G.mul, G.carrier, h))`: a strictly larger subgroup has a strictly smaller finite index |

## The correspondence

One direction of the correspondence theorem, with the count. For a
normal subgroup N, the coset map carries G's operations to the
quotient's, so the preimage of a subgroup S of G/N is a subgroup of G; it
holds N, whose points have the quotient's identity N as their coset. The
coset map carries the preimage onto S, so Lagrange's theorem at N inside
it counts card(N) * card(S) points.

| member | statement under `group_on(G)` |
|---|---|
| `PreimageSubgroup` | for normal `N` and a subgroup `S` of `quotient_group(G, N)`, `preimage_on(G.carrier, coset_map(G.mul, N), S)` is a subgroup of G holding N |
| `PreimageCard` | for a finite group, that preimage has `card(N) * card(S)` points |

## The first isomorphism theorem

A homomorphism `group_homomorphism(G, H, f)` is constant on cosets of its
kernel `K = group_kernel(H.one, G.carrier, f)`. Thus the value of `f` at
a chosen member of a coset is well defined. The resulting map,
`induced_map(f)`, is an isomorphism from the quotient record by `K` to
`restrict_group(H, image(f, G.carrier))`.

Its multiplicativity is the product law for cosets and the product law
for `f`. Equal induced values imply equal images under `f`, hence an
inverse difference in the kernel, hence equal cosets. Every image
point is reached by the coset of its preimage.

| member | statement |
|---|---|
| `InducedMapCosetWithin` | for a subgroup inside the kernel, the induced value of a carrier point's coset is its image under `f` |
| `InducedMapCoset` | this reading at the kernel itself |
| `ImageLeftCosetMul` | if `f` carries a subgroup `N` into a subgroup `K`, then `image(f, uN) K = f(u) K` for source carrier points |
| `FirstIsomorphism` | the induced map is a group isomorphism from the quotient by the kernel onto the image |

## Whole-type views

`group.GroupAtUniverse` supplies the whole-type statements under
`group(G)`. Normality and subgroup assumptions use
`restrict_group(G, 𝕌)`, retaining the whole-type ambient group even
when `G.carrier` is another set.

| whole type | carrier law |
|---|---|
| `InSetInv` | `InSetInvOn` |
| `LeftCosetMul` | `LeftCosetMulOn` |
| `LeftCosetInv` | `LeftCosetInvOn` |
| `QuotientGroup` | `QuotientGroupOn` |
| `ProjectionKernel` | `ProjectionKernelOn` |

The whole-type quotient still has a carrier of cosets:
`quotient_group(restrict_group(G, 𝕌), N)`, whose carrier is
`left_cosets(G.mul, 𝕌, N)`.
