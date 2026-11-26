# finite_group — the order of a finite group, Lagrange's theorem, and p-groups

A finite group is a group record `G` with `group_on(G)` and
`finite(G.carrier)`; its order is `card(G.carrier)`. The structure, its
subgroups and its cosets are the `group` chapter's. This chapter counts
them: the order is positive, a subgroup of a finite group is finite, and
a finite subgroup is as large as a subgroup inside it times the number of
that subgroup's cosets in it. The Sylow theorems are the chapter `sylow`
beside it.

## The order of a finite group

| member | statement |
|---|---|
| `CarrierCardPositive` | `finite(G.carrier) ⇒ 0 < card(G.carrier)`: a finite group has positive order |
| `SubgroupFinite` | `finite(G.carrier) ∧ subgroup(G, h) ⇒ finite(h)`, for any record |

## Lagrange's theorem

A left coset `left_coset(G.mul, x, h)` is the image of `h` under
multiplication by `x`, which cancels, so it is as large as `h`. Lagrange
counts the finite subgroup `k` by its classes under the coset relation of
`h`. Each class is a coset of `h`, each coset has `card(h)` elements, and
their quotient is the image of the coset map. The partition and counting
arguments belong to the equivalence and finite-set chapters.

| member | statement |
|---|---|
| `LeftCosetSizeOn` | `has_size(h, n) ⇒ has_size(left_coset(G.mul, x, h), n)`, for a carrier point and a carrier subset |
| `LagrangeOn` | `subgroup(G, h) ∧ subgroup(G, k) ∧ h ⊆ k ∧ finite(k) ⇒ card(k) = card(h) * card(image(coset_map(G.mul, h), k))` |
| `LagrangeDivides` | under `group(G)`, with the hypotheses of `Lagrange`, `card(h) ∣ card(k)` |
| `LagrangeDividesOn` | `subgroup(G, h) ∧ finite(G.carrier) ⇒ card(h) ∣ card(G.carrier)` — a subgroup's size divides the size of a finite group on a set |

## p-groups

A p-group is a finite group whose order is a power of p, and a
p-subgroup a subgroup that is one: a property of a subgroup is the
group property of its restricted record. Neither definition asks p to be
prime.

| member | statement |
|---|---|
| `PGroupDef` | `p_group(G, p) ⇔ group_on(G) ∧ finite(G.carrier) ∧ ∃n. card(G.carrier) = p ^ n` |
| `PGroupFinite` | `p_group(G, p) ⇒ finite(G.carrier)`: a p-group is finite |
| `PGroupPowerOrder` | `p_group(G, p) ⇒ ∃n. card(G.carrier) = p ^ n`: the order of a p-group is a power of p |
| `PSubgroupDef` | `p_subgroup(G, p, h) ⇔ subgroup(G, h) ∧ p_group(restrict_group(G, h), p)` |
| `PSubgroupSubgroup`, `PSubgroupPGroup` | its two conditions |
| `PSubgroupIff` | `p_subgroup(G, p, h) ⇔ subgroup(G, h) ∧ finite(h) ∧ ∃n. card(h) = p ^ n`, for a group G: a p-subgroup is a finite subgroup whose order is a power of p |

## Whole-type views

As in `group`, a bare name is the whole-type view of its `On` partner,
read at `restrict_group(G, 𝕌)`.

| whole type | carrier law |
|---|---|
| `LeftCosetSize` | `LeftCosetSizeOn` |
| `Lagrange` | `LagrangeOn` |

`LagrangeDivides` is a whole-type statement and retains its proof.
