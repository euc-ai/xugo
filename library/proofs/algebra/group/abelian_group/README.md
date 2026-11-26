# abelian_group — the group whose operation commutes

`abelian_group_on(G)` says that `G:group_ops(A)` is a group and its
product commutes on `G.carrier`. Its operations and carrier are those of
the same record used by `group_on(G)`. Under a law, `x * y` means
`G.mul(x, y)`.

Every group law reads through `GroupOn`. For example,
`group.InvInvOn.Read(GroupOn.Read(abelian))` is the involution of the
inverse on carrier points. Commutativity adds a commutative monoid on
the carrier and lets inversion preserve the order of a product.

| member | statement under `abelian_group_on(G)` |
|---|---|
| `AbelianGroupOn` | `group_on(G)` and commutativity on the carrier |
| `GroupOn` | `group_on(G)` |
| `CommOn` | `x ∈ G.carrier ∧ y ∈ G.carrier ⇒ x * y = y * x` |
| `MonoidOn` | `comm_monoid_on(G.carrier, G.mul, G.one)` |
| `NegAddOn` | `x ∈ G.carrier ∧ y ∈ G.carrier ⇒ G.inv(x * y) = G.inv(x) * G.inv(y)` |

An additive group uses a record whose product, identity and inverse are
its addition, zero and negation. Its subgroups are `subgroup(G, h)`, and
its restricted group is `restrict_group(G, h)`.

## Whole-type views

`AbelianGroup` states `abelian_group(G)`: `group(G)` together with
commutativity on all of `A`, independently of `G.carrier`.
`AbelianGroupOnUniverse` proves
`abelian_group(G) ⇔ abelian_group_on(restrict_group(G, 𝕌))`.
`AbelianGroupAtUniverse` transports each carrier law to this interface.

| whole type | carrier law | statement |
|---|---|---|
| `Group` | `GroupOn` | the corresponding group predicate |
| `Comm` | `CommOn` | `x * y = y * x` |
| `Monoid` | `MonoidOn` | `comm_monoid(G.mul, G.one)` on the whole type |
| `NegAdd` | `NegAddOn` | `G.inv(x * y) = G.inv(x) * G.inv(y)` |
