# compactification — the one-point compactification of a space

A space is made compact by adding one point, at infinity, whose
neighbourhoods are the complements of the closed compact sets. The space
is carried on the optional values of its own type: `none` is the new
point and `some` carries each point of the space in, so the new point is
never one of the space's points whatever its carrier — the line's
carrier is all of ℝ, and a point chosen outside it would not exist. The
open sets of `one_point_compactification(T)` are the images under `some`
of the open sets of T, and the sets `insert(none, image(some, ⋃T ∖ k))`
for k closed and compact in T. Closedness is asked of k because a compact
set of a space that is not Hausdorff need not be closed.

## The definition (definitions.go)

| member | statement |
|---|---|
| `OnePointCompactificationDef` | `one_point_compactification(T) = {v \| (∃u. u ∈ T ∧ v = image(some, u)) ∨ (∃k. closed_in(T, k) ∧ compact_in(T, k) ∧ v = insert(none, image(some, ⋃T ∖ k)))}` |

## The one-point compactification (one_point.go)

The open sets come in the two kinds the definition names: images of open
sets (`OnePointImageOpen`), and the new point with the image of the
space less a closed compact set (`OnePointComplementOpen`); together they
cover the space with the new point added, which is open as the
complement of the closed compact empty set (`OnePointSpace`). Everything
else is read through the trace of a set v of optional values on the
space, `{x | some(x) ∈ v}`, the points the space carries into v. The
trace of an open set is open, with no axiom of the topology read
(`OnePointPreimageOpen`), and a set is open exactly when its trace is
open and, if it holds the new point, the complement of its trace is
compact (`OnePointOpenIff`): every optional value is none or some value,
so a set is the image of its trace, or the new point with that image.
Read through traces, the topology axioms become statements about the
space (`OnePointTopology`): the trace of a meet is the meet of the
traces, its complement the union of two compact complements; the trace
of a union is open pointwise, and when the union holds the new point the
complement of its trace is a closed part of one member's compact
complement. `some` is continuous, the preimage of an open set cut to the
space being its trace (`OnePointSomeContinuous`); so in an open cover a
member holding the new point has a compact complement k, whose image
finitely many members cover, and with it they cover everything
(`OnePointCompact`). The space sits inside as an open subspace, `some`
being a continuous open injection onto the open image of the space
(`OnePointOpenEmbedding`). The compactification is Hausdorff exactly when
the space is Hausdorff and locally compact (`OnePointHausdorffIff`): open
sets separating some(x) from the new point give x a neighbourhood inside
a compact set, and conversely a compact neighbourhood of x, closed in the
Hausdorff space, separates some(x) from the new point. The space is
dense exactly when it is not compact (`OnePointDenseIff`): if it is
compact, the new point alone is open.

| member | statement |
|---|---|
| `OnePointImageOpen` | `u ∈ T ⇒ image(some, u) ∈ one_point_compactification(T)` |
| `OnePointComplementOpen` | `closed_in(T, k) ∧ compact_in(T, k) ⇒ insert(none, image(some, ⋃T ∖ k)) ∈ one_point_compactification(T)` |
| `OnePointSpace` | `is_topology(T) ⇒ ⋃one_point_compactification(T) = insert(none, image(some, ⋃T))` |
| `OnePointPreimageOpen` | `v ∈ one_point_compactification(T) ⇒ {x \| some(x) ∈ v} ∈ T` |
| `OnePointOpenIff` | `v ∈ one_point_compactification(T) ⇔ {x \| some(x) ∈ v} ∈ T ∧ (none ∈ v ⇒ compact_in(T, ⋃T ∖ {x \| some(x) ∈ v}))` |
| `OnePointTopology` | `is_topology(T) ⇒ is_topology(one_point_compactification(T))` |
| `OnePointSomeContinuous` | `continuous_map(T, one_point_compactification(T), some)` |
| `OnePointCompact` | `is_topology(T) ⇒ compact_in(one_point_compactification(T), ⋃one_point_compactification(T))` |
| `OnePointOpenEmbedding` | `is_topology(T) ⇒ image(some, ⋃T) ∈ one_point_compactification(T) ∧ embedding_map(T, one_point_compactification(T), some)` |
| `OnePointHausdorffIff` | `is_topology(T) ⇒ (hausdorff(one_point_compactification(T)) ⇔ hausdorff(T) ∧ locally_compact_space(T))` |
| `OnePointDenseIff` | `is_topology(T) ⇒ (closure(one_point_compactification(T), image(some, ⋃T)) = ⋃one_point_compactification(T) ⇔ ¬compact_in(T, ⋃T))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
