# path_connected — paths, and sets any two points of which a path joins

A path in a space is a continuous map from the unit interval ⟦0, 1⟧,
read with the line's topology cut down to it, into the space:
`path_in(T, g)`. A set is path-connected when it lies in the space and
any two of its points are the two ends of a path whose values on
⟦0, 1⟧ stay in the set: `path_connected_in(T, s)`. The interval is a
subspace of the line, so the chapter reads ℝ's topology and sits above
it, as `metric_space` does; the topology it reads the space through is
`topological_space`'s, and continuity is `continuous`'s.

Both notions leave the topology implicit under a law, as the one-space
notions of `topological_space` do.

## The definitions

| member | statement |
|---|---|
| `PathInDef` | `path_in(T, g) ⇔ continuous_map(subtopology(real_topology, ⟦&0, &1⟧), T, g)` |
| `PathConnectedInDef` | `path_connected_in(T, s) ⇔ s ⊆ ⋃T ∧ ∀x y. x ∈ s ∧ y ∈ s ⇒ ∃g. path_in(T, g) ∧ image(g, ⟦0, 1⟧) ⊆ s ∧ g(&0) = x ∧ g(&1) = y` |
| `PathJoinDef` | `path_join(g, h) = λt. COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1))` — g at double speed, then h |
| `PathReverseDef` | `path_reverse(g) = λt. g(&1 - t)` — g run backwards |

## The unit interval

| member | statement |
|---|---|
| `UnitIntervalPoints` | `x ∈ ⋃subtopology(real_topology, ⟦0, 1⟧) ⇔ &0 ≤ x ∧ x ≤ &1` — the points of the unit interval, read as a subspace of the line |

## Path-connected sets are connected

The values of a path form a connected set: ⟦0, 1⟧ is an interval of
the line, so connected, and a continuous map carries a connected set to
a connected set. A path-connected set is then the union of the value
sets of the paths from one of its points, connected sets sharing that
point.

| member | statement |
|---|---|
| `PathImageConnected` | `path_in(T, g) ⇒ connected_in(T, image(g, ⟦0, 1⟧))` |
| `PathConnectedConnected` | `path_connected_in(T, s) ⇒ connected_in(T, s)` |

## Joining paths

A path ending where a second begins joins it into one: the first run at
double speed on ⟦0, 1/2⟧, the second on ⟦1/2, 1⟧. The two halves are
closed in ⟦0, 1⟧ and the joined map is continuous on each, so it is
continuous by the pasting lemma. Two path-connected sets sharing a
point then unite to a path-connected set. The join and the reverse are
named, `path_join(g, h)` and `path_reverse(g)`, for the chapters that
compute with paths up to homotopy (topology/homotopy,
topology/fundamental_group); the members here spell them out.

| member | statement |
|---|---|
| `PathJoin` | `path_in(T, g) ∧ path_in(T, h) ∧ g(&1) = h(&0) ⇒ path_in(T, λt. COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1)))` |
| `PathReparametrise` | `path_in(T, g) ∧ continuous_map(real_topology, real_topology, p) ∧ (∀t. t ∈ s ⇒ &0 ≤ p(t) ∧ p(t) ≤ &1) ⇒ continuous_map(subtopology(real_topology, s), T, λt. g(p(t)))` |
| `PathJoinEnds` | `(∀t. j(t) = COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1))) ⇒ j(&0) = g(&0) ∧ j(&1) = h(&1)` |
| `PathJoinImage` | `image(λt. COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1)), ⟦0, 1⟧) ⊆ image(g, ⟦0, 1⟧) ∪ image(h, ⟦0, 1⟧)` |
| `PathConnectedUnion` | `path_connected_in(T, s) ∧ path_connected_in(T, t) ∧ s ∩ t ≠ ∅ ⇒ path_connected_in(T, s ∪ t)` |

## Images and the line

A continuous map carries a path to a path, so a path-connected set to a
path-connected set. Every interval of the line is path-connected, by
the straight path from one point to the other — an instance theorem of
the line, stated here because the line's own chapter sits below the
notion.

| member | statement |
|---|---|
| `ImagePathConnected` | `continuous_map(T, S, f) ∧ path_connected_in(T, s) ⇒ path_connected_in(S, image(f, s))` |
| `IntervalPathConnected` | `real_interval(s) ⇒ path_connected_in(real_topology, s)` |

## Path components (path_component.go)

The path component of a point is the set of points a path joins to it:
`path_component(T, x)`, empty when the point is not one of the space.
A constant map is a path and a path run backwards is one, so with the
joining of paths the relation is an equivalence and the path components
partition the space. Each is path-connected — the largest path-connected
set about its point — and lies in the point's connected component. A
space is path-connected exactly when it is the path component of each of
its points.

`PathComponentEquivalence` places the path relation on the set `⋃T`.
Its classes and quotient are identified by `PathComponentClass` and
`PathComponentsQuotient`; coverage reads the general
`relations/equivalence.QuotientOnCovers` law at that equivalence.

| member | statement |
|---|---|
| `PathComponentDef` | `path_component(T, x) = {y \| ∃g. path_in(T, g) ∧ g(&0) = x ∧ g(&1) = y}` |
| `PathConstant` | `x ∈ ⋃T ⇒ path_in(T, λt. x)` |
| `PathReverse` | `path_in(T, g) ⇒ path_in(T, λt. g(&1 - t))` |
| `PathComponentSubsetSpace` | `path_component(T, x) ⊆ ⋃T` |
| `PathComponentSelfIff` | `x ∈ path_component(T, x) ⇔ x ∈ ⋃T` |
| `PathComponentSym` | `y ∈ path_component(T, x) ⇒ x ∈ path_component(T, y)` |
| `PathComponentTrans` | `y ∈ path_component(T, x) ∧ z ∈ path_component(T, y) ⇒ z ∈ path_component(T, x)` |
| `PathComponentEq` | `y ∈ path_component(T, x) ⇒ path_component(T, y) = path_component(T, x)` |
| `PathComponentEquivalence` | path-component membership is an equivalence on `⋃T` |
| `PathComponentClass` | for a point of `⋃T`, its path component is its carrier equivalence class |
| `PathComponentsQuotient` | the image of the path-component map on `⋃T` is its `quotient_on` |
| `PathComponentsCover` | `⋃image(λx. path_component(T, x), ⋃T) = ⋃T` |
| `PathImageSubsetComponent` | `path_in(T, g) ⇒ image(g, ⟦0, 1⟧) ⊆ path_component(T, g(&0))` — the values of a path lie in the path component of its start, each reached by the path run up to its time |
| `PathComponentPathConnected` | `path_connected_in(T, path_component(T, x))` |
| `PathComponentMaximal` | `path_connected_in(T, s) ∧ x ∈ s ⇒ s ⊆ path_component(T, x)` |
| `PathComponentSubsetComponent` | `path_component(T, x) ⊆ connected_component(T, x)` |
| `PathConnectedIffOneComponent` | `path_connected_in(T, ⋃T) ⇔ ∀x. x ∈ ⋃T ⇒ path_component(T, x) = ⋃T` |

## Locally path-connected spaces

A space is locally path-connected when every open neighbourhood of a
point holds a path-connected open neighbourhood of it:
`locally_path_connected_space(T)`. Such a space is locally connected.
Its path components are open, so each is closed too, its complement
being a union of the others; a connected component, meeting one, lies
in it. So the path components are the connected components, and a
connected locally path-connected space is path-connected.

| member | statement |
|---|---|
| `LocallyPathConnectedSpaceDef` | `locally_path_connected_space(T) ⇔ ∀u. ∀x. u ∈ T ∧ x ∈ u ⇒ ∃v. v ∈ T ∧ path_connected_in(T, v) ∧ x ∈ v ∧ v ⊆ u` |
| `LocallyPathConnectedImpLocallyConnected` | `locally_path_connected_space(T) ⇒ locally_connected_space(T)` |
| `LocallyPathConnectedComponentOpen` | `locally_path_connected_space(T) ⇒ ∀x. path_component(x) ∈ T` |
| `LocallyPathConnectedComponentsAgree` | `locally_path_connected_space(T) ⇒ ∀x. path_component(x) = connected_component(x)` |
| `ConnectedLocallyPathConnected` | `locally_path_connected_space(T) ∧ connected_in(⋃T) ⇒ path_connected_in(⋃T)` |

## Products

The product of two path-connected sets is path-connected: the pair of a
path in each is a path in the product, a map into a product being
continuous when its components are.

| member | statement |
|---|---|
| `PathConnectedProduct` | `path_connected_in(T, k) ∧ path_connected_in(S, l) ⇒ path_connected_in(product_topology(T, S), set_cross(k, l))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
