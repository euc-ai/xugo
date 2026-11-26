# product_topology — the topology on the product of two spaces and of an indexed family

The product of two spaces has the pairs of their points for points, and
a set of pairs is open when each of its points lies in a rectangle of
two open sets inside it: `product_topology(T, S)`. The definition is
read point by point, as the topology of a distance is read through
balls, so most of what follows asks nothing of the two topologies:
unions of open sets, open rectangles, the points of the product, the
continuity of the projections. The axioms enter where two rectangles
about one point have to be met, where a factor is read pointwise, and
where a whole space is taken as an open set. The product of two sets is
`sets/set_product`'s `set_cross`, and both topologies are spelled in
every statement.

The product of an indexed family is the second half (indexed.go). Its
factors live in one type: T(i) is a topology for each index i of J, and
the points of the product are the functions picking a point of the i-th
space at each i ∈ J and a prescribed value z(i) off it
(`sets/indexed_functions`); the topology is generated on that carrier by
the coordinate cylinders. The points of the product are the indexed
functions, a cylinder over an open set of its factor is open, and each
coordinate is continuous; a map into the product is continuous exactly
when its values are indexed functions and its coordinates are
continuous. None of this asks the factors to be topologies, generation
on a carrier giving a topology whatever generates it. A product of
Hausdorff spaces is Hausdorff. Tychonoff's theorem — a product of
compact spaces is compact — goes through the Alexander subbase lemma
(`compact`'s, whose proof reads the maximal principle of
`relations/order`): a cover by cylinders with no finite subcover leaves,
at each index, a point of the factor outside the sides the cover uses
there, and one choice of such points gives a point of the product the
cover misses.

## The definition

| member | statement |
|---|---|
| `ProductTopologyDef` | `product_topology(T, S) = {w:set(prod(A, B)) \| ∀p. p ∈ w ⇒ ∃u. ∃v. u ∈ T ∧ v ∈ S ∧ p ∈ set_cross(u, v) ∧ set_cross(u, v) ⊆ w}` |

## The open sets (product_topology.go)

A rectangle of two open sets is open, and the points of the product are
the pairs of points. The product of two topologies is a topology — its
one use of an axiom is where the rectangles about a point common to two
open sets meet in the rectangle of the two meets.

There is also a construction from maps: on `X = set_cross(⋃T, ⋃S)`,
take the union of `induced_topology(X, T, fst)` and
`induced_topology(X, S, snd)` and generate a topology on `X`.
`ProductInducedGenerated` identifies it with the rectangle definition.
The two families are the open cylinders; two cylinders meet in a
rectangle, and every rectangle supplies the pointwise open-set test.

| member | statement |
|---|---|
| `ProductOpenIff` | `w ∈ product_topology(T, S) ⇔ ∀p. p ∈ w ⇒ ∃u. ∃v. u ∈ T ∧ v ∈ S ∧ p ∈ set_cross(u, v) ∧ set_cross(u, v) ⊆ w` |
| `RectangleOpen` | `u ∈ T ∧ v ∈ S ⇒ set_cross(u, v) ∈ product_topology(T, S)` |
| `ProductSpace` | `⋃product_topology(T, S) = set_cross(⋃T, ⋃S)` |
| `ProductTopology` | `is_topology(T) ∧ is_topology(S) ⇒ is_topology(product_topology(T, S))` |
| `ProductInducedGenerated` | if `T` and `S` are topologies, their product is `topology_generated_on(X, induced_topology(X, T, fst) ∪ induced_topology(X, S, snd))`, where `X = set_cross(⋃T, ⋃S)` |

## Closed sets

A rectangle of two closed sets is closed: its complement is two
rectangles, each open point by point.

| member | statement |
|---|---|
| `ClosedRectangle` | `closed_in(T, c) ∧ closed_in(S, d) ⇒ closed_in(product_topology(T, S), set_cross(c, d))` — card |

## Maps (maps.go)

The projections are continuous. A map into a product is continuous
exactly when its two components are; two continuous maps make a
continuous map of the products; and pairing with a fixed first
coordinate is continuous.

| member | statement |
|---|---|
| `FstContinuous` | `continuous_map(product_topology(T, S), T, fst)` |
| `SndContinuous` | `continuous_map(product_topology(T, S), S, snd)` |
| `PairedContinuousIff` | `is_topology(R) ⇒ (continuous_map(R, product_topology(T, S), h) ⇔ continuous_map(R, T, λz. fst(h(z))) ∧ continuous_map(R, S, λz. snd(h(z))))` |
| `ProductMapContinuous` | `continuous_map(T, U, f) ∧ continuous_map(S, V, g) ⇒ continuous_map(product_topology(T, S), product_topology(U, V), λp. (f(fst(p)), g(snd(p))))` |
| `SliceRightContinuous` | `is_topology(S) ∧ x ∈ ⋃T ⇒ continuous_map(S, product_topology(T, S), λy. (x, y))` |

## What a product inherits (properties.go)

Two Hausdorff spaces have a Hausdorff product; a space is Hausdorff
exactly when its diagonal is closed in its square; and the graph of a
continuous map f into a Hausdorff space is closed, being the preimage of
that diagonal under (x, y) ↦ (f(x), y). The tube lemma — an
open set around a slice {x} × k with k compact holds a whole tube u × k
— is what compactness passes through: the product of two compact sets
is compact, a rectangle of compact neighbourhoods makes the product of
two locally compact spaces locally compact, and the projection along a
compact factor is a closed map. Two countable bases make a countable base of rectangles.

| member | statement |
|---|---|
| `HausdorffProduct` | `hausdorff(T) ∧ hausdorff(S) ⇒ hausdorff(product_topology(T, S))` |
| `HausdorffIffDiagonalClosed` | `hausdorff(T) ⇔ closed_in(product_topology(T, T), set_diagonal(⋃T))` |
| `ClosedGraph` | `continuous_map(T, S, f) ∧ hausdorff(S) ⇒ closed_in(product_topology(T, S), {(x, f(x)) \| x \| x ∈ ⋃T})` |
| `TubeLemma` | `is_topology(T) ∧ compact_in(S, k) ∧ w ∈ product_topology(T, S) ∧ x ∈ ⋃T ∧ set_cross({x}, k) ⊆ w ⇒ ∃u. u ∈ T ∧ x ∈ u ∧ set_cross(u, k) ⊆ w` |
| `CompactProduct` | `is_topology(T) ∧ is_topology(S) ∧ compact_in(T, k) ∧ compact_in(S, l) ⇒ compact_in(product_topology(T, S), set_cross(k, l))` |
| `LocallyCompactProduct` | `is_topology(T) ∧ is_topology(S) ∧ locally_compact_space(T) ∧ locally_compact_space(S) ⇒ locally_compact_space(product_topology(T, S))` |
| `ProjectionClosedMap` | `is_topology(T) ∧ compact_in(S, ⋃S) ⇒ closed_map(product_topology(T, S), T, fst)` |
| `SecondCountableProduct` | `second_countable_space(T) ∧ second_countable_space(S) ⇒ second_countable_space(product_topology(T, S))` — card |

That the product of two path-connected sets is path-connected is
`path_connected`'s, and that the topology of the product distance is
the product of the two metric topologies is `metric_space`'s.

## The product of an indexed family

| member | statement |
|---|---|
| `IndexedProductTopologyDef` | `indexed_product_topology(J, z, T) = topology_generated_on(indexed_functions(J, z, λi. ⋃T(i)), {u \| ∃i v. i ∈ J ∧ v ∈ T(i) ∧ u = {f \| f ∈ indexed_functions(J, z, λj. ⋃T(j)) ∧ f(i) ∈ v}})` |
| `IndexedProductCarrier` | `⋃indexed_product_topology(J, z, T) = indexed_functions(J, z, λi. ⋃T(i))` |
| `IndexedProductTopology` | `is_topology(indexed_product_topology(J, z, T))` |
| `IndexedProductTopologyCongruence` | Equal factor topologies at every active index give the same normalized product topology. |
| `IndexedCylinderOpen` | `i ∈ J ∧ v ∈ T(i) ⇒ {f \| f ∈ indexed_functions(J, z, λj. ⋃T(j)) ∧ f(i) ∈ v} ∈ indexed_product_topology(J, z, T)` |
| `IndexedProjectionContinuous` | `i ∈ J ⇒ continuous_map(indexed_product_topology(J, z, T), T(i), λf. f(i))` |
| `IndexedContinuousIff` | `is_topology(R) ⇒ (continuous_map(R, indexed_product_topology(J, z, T), h) ⇔ (∀x. x ∈ ⋃R ⇒ h(x) ∈ indexed_functions(J, z, λi. ⋃T(i))) ∧ (∀i. i ∈ J ⇒ continuous_map(R, T(i), λx. h(x, i))))` |
| `IndexedHausdorff` | `(∀i. i ∈ J ⇒ hausdorff(T(i))) ⇒ hausdorff(indexed_product_topology(J, z, T))` |
| `IndexedFiniteModificationsDense` | The points that differ from a product point `a` at finitely many active coordinates, each changed value taken from a dense subset `C(i)` of its factor, are dense in the indexed product. |
| `ProductFiniteSupportDense` | When the prescribed values lie in the active factors, the points of the product that differ from the prescribed point at finitely many coordinates are dense. |
| `IndexedProductSeparable` | A countable indexed product of separable topologies is separable. |
| `Tychonoff` | `(∀i. i ∈ J ⇒ compact_in(T(i), ⋃T(i))) ⇒ compact_in(indexed_product_topology(J, z, T), indexed_functions(J, z, λi. ⋃T(i)))` |

The product of an indexed family is always a topology, generated on
the indexed functions. Its finite modifications of one point by values
from dense subsets of the factors are dense, since every finite
intersection of cylinders constrains finitely many coordinates, and the
cylinders at one coordinate meet in an open set of its factor. Taken at
the prescribed point with the whole factors for the dense sets, this is
the density of the finitely supported points of a product whose
prescribed values lie in the active factors. Over a countable index
set, with countable dense factor sets, there are countably many such
modifications ([`cardinal`](../../sets/cardinal/README.md)'s
`CountableFiniteModifications`). That is the countable dense set of a
countable product of separable spaces. The density and separability
theorems have their own reading unit, `indexed_density.go`, apart from
the product topology's elementary laws in `indexed.go`.

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
