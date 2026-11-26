# set_product — the product of two sets, and the diagonal of one

The product of a set s of A's and a set t of B's is the set of pairs
with first component in s and second in t: `set_cross(s, t)`, a set of
`prod(A, B)`. The pair type, the pairing `(x, y)` and the projections
`fst` and `snd` are `cartesian/pairs`'; this chapter is what the set
operations say about the product. The diagonal of s is the set of pairs
(x, x) with x in s: `set_diagonal(s)`, a set of `prod(A, A)`.

## The definitions

| member | statement |
|---|---|
| `SetCrossDef` | `set_cross(s, t) = {(x, y) \| x:A, y:B \| x ∈ s ∧ y ∈ t}` |
| `SetDiagonalDef` | `set_diagonal(s) = {(x, x) \| x:A \| x ∈ s}` |

## Membership

A pair lies in the product exactly when each component lies in its
factor, and a point of the pair type exactly when its projections do —
the same fact read at a pair and at a point, every point being the pair
of its projections. The diagonal is read the same two ways: a pair lies
on it exactly when its first component lies in s and its second is the
first. So the diagonal lies in the square (`DiagonalSubsetCross`).

| member | statement |
|---|---|
| `InCross` | `(x, y) ∈ set_cross(s, t) ⇔ x ∈ s ∧ y ∈ t` |
| `InCrossProjections` | `p ∈ set_cross(s, t) ⇔ fst(p) ∈ s ∧ snd(p) ∈ t` |
| `InDiagonal` | `(x, y) ∈ set_diagonal(s) ⇔ x ∈ s ∧ y = x` |
| `InDiagonalProjections` | `p ∈ set_diagonal(s) ⇔ fst(p) ∈ s ∧ snd(p) = fst(p)` |
| `DiagonalSubsetCross` | `set_diagonal(s) ⊆ set_cross(s, s)` |

## The product and the set operations

A product is empty exactly when a factor is, and lies in another
exactly when it is empty or each factor lies in the other's. Products
meet factor by factor and distribute over a union in either factor; a
product less a product is two products, the identity through which the
complement of a rectangle is read.

| member | statement |
|---|---|
| `CrossEmptyIff` | `set_cross(s, t) = ∅ ⇔ s = ∅ ∨ t = ∅` |
| `CrossSubsetIff` | `set_cross(s, t) ⊆ set_cross(u, v) ⇔ s = ∅ ∨ t = ∅ ∨ (s ⊆ u ∧ t ⊆ v)` |
| `CrossInter` | `set_cross(s ∩ u, t ∩ v) = set_cross(s, t) ∩ set_cross(u, v)` |
| `CrossUnionLeft` | `set_cross(s ∪ u, t) = set_cross(s, t) ∪ set_cross(u, t)` |
| `CrossUnionRight` | `set_cross(s, t ∪ v) = set_cross(s, t) ∪ set_cross(s, v)` |
| `CrossDifference` | `set_cross(s, t) ∖ set_cross(u, v) = set_cross(s ∖ u, t) ∪ set_cross(s, t ∖ v)` |

## Projections

Each projection of a product is its factor when the other factor is
non-empty: a point of the other factor pairs every point of this one
into the product.

| member | statement |
|---|---|
| `ImageFstCross` | `¬(t = ∅) ⇒ image(fst, set_cross(s, t)) = s` |
| `ImageSndCross` | `¬(s = ∅) ⇒ image(snd, set_cross(s, t)) = t` |
| `CrossSwap` | `set_cross(s, t)` is the image of `set_cross(t, s)` under the swap of coordinates |

The size of a product is the size chapters' to state, each at
`set_cross`: a product of finite sets is finite
(`finite_set.FiniteProduct`), of countable sets countable
(`cardinal.CountableProduct`), and of sets of m and n points a set of
m · n points (`cardinality.HasSizeProduct`, `cardinality.CardProduct`).

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
