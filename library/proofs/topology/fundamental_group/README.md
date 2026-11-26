# fundamental_group — the classes of paths under homotopy, the fundamental group of a space at a point, the homomorphisms continuous maps induce, simply connected spaces and the Seifert–van Kampen theorem

The class of a path is the set of paths homotopic to it with the ends
held, `path_class(T, g)`. Joining and reversing pass to classes, and the
two operations are defined on any sets of paths without a base point and
without choosing a representative: `path_class_join(T, C, D)` is every
path homotopic to the join of a member of C with a member of D, and
`path_class_reverse(T, C)` every path homotopic to the reverse of a
member of C. On classes of paths that meet end to start these are the
class of the join and the class of the reverse, so one pair of
operations serves the groupoid of all paths and the group of loops at a
point alike; on classes that do not meet, the join reads joins that are
not paths, and nothing here is stated there.

The fundamental group at x, `fundamental_group(T, x)`, is a group record:
its carrier the classes of the loops at x, `loops_at(T, x)`, the quotient
of the loops by path homotopy; its product the join, its unit the class
of the constant loop and its inverse the reverse. At a point of the space
it is a group, the axioms being the groupoid laws of topology/homotopy
read through classes; at a point outside it has no loops and an empty
carrier. A path from x to y conjugates the group at x onto the group at y.
The class of a loop in the record is the class of a loop, which is how a
statement about the group is read: `FundamentalGroupMember`.

A continuous map carries the class of a path to the class of its image,
`fundamental_map(S, f, C)`, a homomorphism of fundamental groups,
functorial. Two maps homotopic with the base point held induce one
homomorphism; under a free homotopy the two homomorphisms differ by the
change of base point along the track of the base point, so a homotopy
equivalence induces isomorphisms and a contractible space is simply
connected: path-connected, with every loop homotopic to the constant
loop (`simply_connected_space(T)`; the empty space is one).

The Seifert–van Kampen theorem is stated as a universal property. For a
space covered by two open sets u and v whose intersection is
path-connected and holds the base point, the classes of the loops inside
u or inside v generate the fundamental group of the union: two
homomorphisms out of it agreeing on them agree. When u and v are
path-connected too, homomorphisms out of the groups of u and of v that
agree on the group of the intersection extend to one out of the group of
the union. Together the two make the group of the union the pushout of
the two groups over that of the intersection, which no free product needs
to be built to say. A union of two simply connected open sets with a
nonempty path-connected intersection is simply connected.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `loops_at(T, x)` | `{g \| path_in(T, g) ∧ g(&0) = x ∧ g(&1) = x}` |
| `path_class(T, g)` | `{k \| path_homotopic(T, g, k)}` |
| `path_class_join(T, C, D)` | `{k \| ∃g h. g ∈ C ∧ h ∈ D ∧ path_homotopic(T, k, path_join(g, h))}` |
| `path_class_reverse(T, C)` | `{k \| ∃g. g ∈ C ∧ path_homotopic(T, k, path_reverse(g))}` |
| `fundamental_group(T, x)` | `mk_group(path_class_join(T), path_class(T, λt. x), path_class_reverse(T), quotient_on(loops_at(T, x), path_homotopic(T)))` |
| `fundamental_map(S, f, C)` | `{k \| ∃g. g ∈ C ∧ path_homotopic(S, k, f ∘ g)}` |
| `simply_connected_space(T)` | `path_connected_in(T, ⋃T) ∧ ∀x g. g ∈ loops_at(T, x) ⇒ path_homotopic(T, g, λt. x)` |

## The classes and the group (classes.go)

| member | statement |
|---|---|
| `PathClassEq` | `path_in(T, g) ∧ path_in(T, h) ⇒ (path_class(T, g) = path_class(T, h) ⇔ path_homotopic(T, g, h))` — card |
| `PathClassJoinClass` | `path_in(T, g) ∧ path_in(T, h) ∧ g(&1) = h(&0) ⇒ path_class_join(T, path_class(T, g), path_class(T, h)) = path_class(T, path_join(g, h))` — card |
| `PathClassReverseClass` | `path_in(T, g) ⇒ path_class_reverse(T, path_class(T, g)) = path_class(T, path_reverse(g))` — card |
| `FundamentalGroupMember` | `C ∈ fundamental_group(T, x).carrier ⇔ ∃g. g ∈ loops_at(T, x) ∧ C = path_class(T, g)` — card |
| `FundamentalGroupOn` | `x ∈ ⋃T ⇒ group_on(fundamental_group(T, x))` — card |
| `BasepointChange` | `path_in(T, g) ⇒ group_isomorphism(fundamental_group(T, g(&0)), fundamental_group(T, g(&1)), λC. path_class_join(T, path_class_join(T, path_class(T, path_reverse(g)), C), path_class(T, g)))` — card |

## Induced maps (maps.go)

| member | statement |
|---|---|
| `FundamentalMapClass` | `continuous_map(T, S, f) ∧ path_in(T, g) ⇒ fundamental_map(S, f, path_class(T, g)) = path_class(S, f ∘ g)` — card |
| `FundamentalMapHom` | `continuous_map(T, S, f) ∧ x ∈ ⋃T ⇒ group_homomorphism(fundamental_group(T, x), fundamental_group(S, f(x)), fundamental_map(S, f))` — card |
| `FundamentalMapIdentity` | `C ∈ fundamental_group(T, x).carrier ⇒ fundamental_map(T, λy. y, C) = C` — card |
| `FundamentalMapCompose` | `continuous_map(T, S, f) ∧ continuous_map(S, U, h) ∧ D ∈ fundamental_group(T, x).carrier ⇒ fundamental_map(U, h ∘ f, D) = fundamental_map(U, h, fundamental_map(S, f, D))` — card |
| `FundamentalMapHomotopic` | `homotopic_rel(T, S, {x}, f, h) ∧ D ∈ fundamental_group(T, x).carrier ⇒ fundamental_map(S, f, D) = fundamental_map(S, h, D)` — card |
| `FundamentalMapFreeHomotopy` | for H a homotopy from f to h on T × «I» and D in the group at x: `fundamental_map(S, h, D)` is `fundamental_map(S, f, D)` conjugated by the class of the track `λs. H((x, s))` — card |
| `HomotopyEquivalenceFundamentalGroup` | `homotopy_equivalence(T, S, f, g) ∧ x ∈ ⋃T ⇒ group_isomorphism(fundamental_group(T, x), fundamental_group(S, f(x)), fundamental_map(S, f))` — card |
| `ContractibleSimplyConnected` | `contractible_space(T) ⇒ simply_connected_space(T)` — card |
| `SimplyConnectedPathsHomotopic` | `simply_connected_space(T)` and two paths with the same ends ⇒ `path_homotopic(T, g, h)` — card |

## Seifert–van Kampen (van_kampen.go)

| member | statement |
|---|---|
| `VanKampenGenerated` | for `is_topology(T)`, u and v open with `⋃T ⊆ u ∪ v`, `u ∩ v` path-connected and x in it: two homomorphisms out of `fundamental_group(T, x)` agreeing on the images of the groups of u and of v agree — card |
| `VanKampenExtension` | for u, v and `u ∩ v` path-connected besides: homomorphisms φ, ψ out of the groups of u and of v agreeing on the group of `u ∩ v` extend to one χ out of `fundamental_group(T, x)` — card |
| `SimplyConnectedUnion` | `is_topology(T)`, u and v open covering it, each simply connected, `u ∩ v` path-connected and nonempty ⇒ `simply_connected_space(T)` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
