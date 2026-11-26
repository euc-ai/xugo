# topological_space — a topology as a family of sets

A topology on a type A is a family T of subsets of A closed under two
operations: the intersection of two members, and the union of any
subfamily. That is the whole definition, `is_topology(T)`, and it has
one component, the family. Its carrier is `⋃T`, the union of the
family, so it is determined by the open sets. "u is open" is `u ∈ T`,
membership, so nothing is minted to say so. The whole space and the
empty set are open by the union axiom, at the subfamily T and at the
empty subfamily, so neither is an axiom.

The structure is a predicate on the family, not a type or a
typeclass: it is stated once and carried as the hypothesis of every
law (constitution §Structures), so that a proof about open sets is a
proof about membership in T, which the set-theoretic closer reads
directly. The notions stated over one space — closed sets, interior
and closure, the limit points and the frontier of a set, a base, the
subspace topology — read the topology as their first
argument and leave it implicit under a law, `closed_in(c)` for
`closed_in(T, c)`. A member that uses no axiom is a plain theorem and
spells the family, `closed_in(T, c)`: that spelling is how a reader
sees at a glance that it needs no structure. It is a convention of the
chapter; the parser would complete the short form under any binder
named `T`.

## The structure and its axioms

| member | statement |
|---|---|
| `IsTopology` | `is_topology(T) ⇔ (∀u v. u ∈ T ∧ v ∈ T ⇒ u ∩ v ∈ T) ∧ (∀s. s ⊆ T ⇒ ⋃s ∈ T)` |
| `InterOpen` | `u ∈ T ∧ v ∈ T ⇒ u ∩ v ∈ T` |
| `UnionsOpen` | `s ⊆ T ⇒ ⋃s ∈ T` |

## Instances

An instance is a theorem stating the predicate at a concrete family.
The subspace topology is one by the general induced-topology
construction below, under the hypothesis that T is a topology.

| member | statement |
|---|---|
| `Discrete` | `is_topology({t \| t ⊆ X})` — every subset of X is open |
| `IntersTopologies` | `(∀T. T ∈ F ⇒ is_topology(T)) ⇒ is_topology(⋂F)` — a family of topologies, empty or not, meets in a topology |

## What the axioms say about open sets

| member | statement |
|---|---|
| `SpaceOpen` | `⋃T ∈ T` — the space is open |
| `EmptyOpen` | `∅ ∈ T` — the empty set is open, as the union of the empty subfamily |
| `UnionOpen` | `u ∈ T ∧ v ∈ T ⇒ u ∪ v ∈ T` — two open sets unite to an open set, as the union of the two-member subfamily |
| `IntersOpen` | `finite(f) ∧ ¬(f = ∅) ∧ f ⊆ T ⇒ ⋂f ∈ T` — finitely many open sets meet in an open set, provided there is at least one; by induction on the family using the pairwise axiom |
| `OpenPointwise` | `u ∈ T ⇔ (∀x. x ∈ u ⇒ ∃v. v ∈ T ∧ v ⊆ u ∧ x ∈ v)` — a set is open iff each of its points lies in an open set inside it; backward, the set is its own interior |
| `SeparatedFromFiniteUnion` | `x ∈ ⋃T ∧ finite(d) ∧ (∀v. v ∈ d ⇒ ∃u. u ∈ T ∧ x ∈ u ∧ u ∩ v = ∅) ⇒ ∃u. u ∈ T ∧ x ∈ u ∧ u ∩ ⋃d = ∅` — a point with an open neighbourhood disjoint from each of finitely many sets has one disjoint from their union; by induction on the family, meeting the neighbourhoods |

## Closed sets

A set is closed when it lies in the space and its complement there is
open, and a set inside the space is open exactly when its complement
there is closed. The space and the empty set are closed, being each
other's complements; two closed sets unite and meet in closed sets,
and a non-empty family of closed sets meets in a closed set, all by de
Morgan in the space, the complement of a union being the intersection
of the complements and the complement of an intersection the union of
them, which the two axioms make open. The family must be non-empty,
since the intersection of no sets is the whole type, which need not
lie in the space. An open set with a closed set taken away is open,
being its meet with the closed set's open complement.

| member | statement |
|---|---|
| `ClosedInDef` | `closed_in(T, c) ⇔ c ⊆ ⋃T ∧ ⋃T ∖ c ∈ T` |
| `SpaceClosed` | `closed_in(⋃T)` |
| `EmptyClosed` | `closed_in(∅)` |
| `OpenClosedComplement` | `u ∈ T ⇔ u ⊆ ⋃T ∧ closed_in(T, ⋃T ∖ u)` — a set is open iff it lies in the space and its complement there is closed |
| `UnionClosed` | `closed_in(c) ∧ closed_in(d) ⇒ closed_in(c ∪ d)` — the complement of the union is the intersection of the two open complements |
| `InterClosed` | `closed_in(c) ∧ closed_in(d) ⇒ closed_in(c ∩ d)` — the complement of the meet is the union of the two open complements |
| `IntersClosed` | `¬(f = ∅) ∧ (∀c. c ∈ f ⇒ closed_in(c)) ⇒ closed_in(⋂f)` |
| `DiffOpen` | `u ∈ T ∧ closed_in(c) ⇒ u ∖ c ∈ T` — removing c is meeting its open complement |

## Interior and closure

The interior of s is the union of the open sets inside s, the
largest open set s contains; the closure of s is the intersection of
the closed sets around s, the smallest closed set containing s. For s
inside the space, the space is one of those closed sets; for s
outside it the family is empty and its intersection is everything,
which is why a law about the closure carries `s ⊆ ⋃T`. What each is
by its definition alone — the interior inside s and above every open
set inside s, the closure around s and below every closed set around
s, an open set its own interior and a closed set its own closure —
needs no axiom. That the interior is open and the closure closed takes
the axioms, and makes them the largest open set inside s and the
smallest closed set around it.

| member | statement |
|---|---|
| `InteriorDef` | `interior(T, s) = ⋃{u \| u ∈ T ∧ u ⊆ s}` |
| `ClosureDef` | `closure(T, s) = ⋂{c \| closed_in(T, c) ∧ s ⊆ c}` |
| `InteriorSubset` | `interior(T, s) ⊆ s` |
| `InteriorMaximal` | `u ∈ T ∧ u ⊆ s ⇒ u ⊆ interior(T, s)` |
| `InteriorOfOpen` | `u ∈ T ⇒ interior(T, u) = u` |
| `InteriorOpen` | `interior(s) ∈ T` — a union of open sets |
| `InteriorPointwise` | `∀x. x ∈ interior(T, s) ⇔ ∃u. u ∈ T ∧ u ⊆ s ∧ x ∈ u` |
| `SubsetClosure` | `s ⊆ closure(T, s)` |
| `ClosureMinimal` | `closed_in(T, c) ∧ s ⊆ c ⇒ closure(T, s) ⊆ c` |
| `ClosureOfClosed` | `closed_in(T, c) ⇒ closure(T, c) = c` |
| `ClosureClosed` | `s ⊆ ⋃T ⇒ closed_in(closure(s))` — a non-empty intersection of closed sets, the space being one of them |
| `ClosurePointwise` | `s ⊆ ⋃T ⇒ ∀x. x ∈ closure(s) ⇔ x ∈ ⋃T ∧ (∀u. u ∈ T ∧ x ∈ u ⇒ ¬(u ∩ s = ∅))` — every open set holding the point meets s |

## Interior and closure are dual

The closure of a set inside the space is the complement there of the
interior of its complement. Read at a point, the closure asks that
every open set holding the point meet s, the interior of the
complement that some open set holding it lie inside ⋃T ∖ s; an open
set lies in the space, so missing s and lying inside the complement of
s are one condition, and the two readings are each other's negation.

| member | statement |
|---|---|
| `InteriorClosureDual` | `s ⊆ ⋃T ⇒ closure(s) = ⋃T ∖ interior(⋃T ∖ s)` |

## Closure and interior as order-theoretic operations

The carrier of the closure operation is the set of subsets of the
space, `{s | s ⊆ ⋃T}`. Its closed points are the closed sets of `T`.
`ClosureClosed`, `SubsetClosure`, and `ClosureMinimal` identify the
least closed set above each carrier point; `relations/order.ClosureFromLeast`
then supplies the closure-operator laws. This is the same construction
used for the span of a subset of a module's carrier and for ideal
generation in a ring. Its fixed points form a complete lattice by
`ClosureFixedPointsCompleteLattice`: joins are closures of unions, and
meets are intersections relative to the space, including an empty meet.

Under reverse inclusion, interior is a closure operator on the same
powerset: it selects the largest open subset. The fixed-point theorem
and complete-lattice duality then give the open-set lattice. Its joins
are unions and its meets are `interior(⋃T ∩ ⋂F)`, so the empty meet
is the space itself.

| member | statement |
|---|---|
| `ClosureOperator` | `closure_operator_on({s \| s ⊆ ⋃T}, ⊆, closure)` |
| `ClosedSetsCompleteLattice` | the closed sets form a complete lattice, with supremum `closure(⋃F)` and infimum `⋃T ∩ ⋂F` |
| `InteriorOperator` | interior is a closure operator on `{s \| s ⊆ ⋃T}` under reverse inclusion |
| `OpenSetsCompleteLattice` | `T` is a complete lattice under inclusion, with supremum `⋃F` and infimum `interior(⋃T ∩ ⋂F)` |

## The algebra of interior and closure

Interior and closure are monotone, and each applied twice is itself;
an open set is the set that is its own interior, a closed set the
subset of the space that is its own closure. The closure of a union is
the union of the closures. An open set meets a closure inside the
closure of its meet with the set, and a subset of the space is dense —
its closure the whole space — exactly when it meets every non-empty
open set. Monotonicity asks nothing of the topology, not even that the
set lie in the space: where no closed set is around a set its closure
is everything.

| member | statement |
|---|---|
| `InteriorSubsetSpace` | `interior(T, s) ⊆ ⋃T` |
| `InteriorMono` | `s ⊆ t ⇒ interior(T, s) ⊆ interior(T, t)` |
| `OpenIffInterior` | `s ∈ T ⇔ interior(s) = s` |
| `ClosureMono` | `s ⊆ t ⇒ closure(T, s) ⊆ closure(T, t)` |
| `ClosureSubsetSpace` | `s ⊆ ⋃T ⇒ closure(s) ⊆ ⋃T` |
| `ClosureEmpty` | `closure(∅) = ∅` — card |
| `ClosureIdempotent` | `s ⊆ ⋃T ⇒ closure(closure(s)) = closure(s)` — generic closure-operator idempotence |
| `ClosedIffClosure` | `closed_in(s) ⇔ s ⊆ ⋃T ∧ closure(s) = s` |
| `ClosureUnion` | `s ⊆ ⋃T ∧ t ⊆ ⋃T ⇒ closure(s ∪ t) = closure(s) ∪ closure(t)` — card |
| `InteriorClosureComplement` | `s ⊆ ⋃T ⇒ interior(s) = ⋃T ∖ closure(⋃T ∖ s)` |
| `OpenInterClosure` | `u ∈ T ∧ s ⊆ ⋃T ⇒ u ∩ closure(s) ⊆ closure(u ∩ s)` — card |
| `DenseMeetsOpen` | `s ⊆ ⋃T ⇒ (closure(s) = ⋃T ⇔ ∀u. u ∈ T ∧ ¬(u = ∅) ⇒ ¬(u ∩ s = ∅))` |

## Limit points and the frontier (frontier.go)

A limit point of s is a point of the space every open neighbourhood of
which holds a point of s other than itself: `derived_set(T, s)`. The
closure of a subset of the space is the set with its limit points. The
frontier of s is its closure less its interior, `frontier(T, s)`. It
is closed.

| member | statement |
|---|---|
| `DerivedSetDef` | `derived_set(T, s) = {x \| x ∈ ⋃T ∧ (∀u. u ∈ T ∧ x ∈ u ⇒ ∃y. y ≠ x ∧ y ∈ s ∧ y ∈ u)}` |
| `FrontierDef` | `frontier(T, s) = closure(T, s) ∖ interior(T, s)` |
| `DerivedMono` | `s ⊆ t ⇒ derived_set(T, s) ⊆ derived_set(T, t)` |
| `ClosureDerived` | `s ⊆ ⋃T ⇒ closure(s) = s ∪ derived_set(s)` |
| `FrontierClosures` | `s ⊆ ⋃T ⇒ frontier(s) = closure(s) ∩ closure(⋃T ∖ s)` |
| `FrontierClosed` | `s ⊆ ⋃T ⇒ closed_in(frontier(s))` |

## Bases and generated topologies (base.go)

A base of a topology is a family of open sets among which every point
of an open set finds one inside that open set, `topology_base(T, b)`;
the open sets are then exactly the unions of members of the base, and
the traces of a base on a subset are a base of the subspace. Any
family of sets generates a topology, the smallest containing it:
`topology_generated(b)`, the intersection of the topologies containing
b — an intersection that is never empty, the family of all subsets of
⋃b being one of them. Its open sets are the unions of the finite
intersections of members of b, and its points are the points of b. A
family in which two members meeting at a point hold a third about the
point inside both defines a topology — the sets each of whose points
lies in a member inside them — so it is a base of the topology it
generates, and a topology is generated by any base of it.

| member | statement |
|---|---|
| `TopologyBaseDef` | `topology_base(T, b) ⇔ b ⊆ T ∧ (∀u. ∀x. u ∈ T ∧ x ∈ u ⇒ ∃v. v ∈ b ∧ x ∈ v ∧ v ⊆ u)` |
| `TopologyGeneratedDef` | `topology_generated(b) = ⋂{T \| is_topology(T) ∧ b ⊆ T}` |
| `BaseOpenIff` | `topology_base(b) ⇒ ∀u. u ∈ T ⇔ ∃c. c ⊆ b ∧ u = ⋃c` |
| `SubtopologyBase` | `topology_base(T, b) ⇒ topology_base(subtopology(T, s), image(λv. v ∩ s, b))` |
| `GeneratedTopology` | `is_topology(topology_generated(b))` |
| `GeneratedContains` | `b ⊆ topology_generated(b)` |
| `GeneratedMinimal` | `b ⊆ T ⇒ topology_generated(b) ⊆ T` |
| `GeneratedSpace` | `⋃topology_generated(b) = ⋃b` |
| `LocalMeetsTopology` | `(∀u v. ∀x. u ∈ b ∧ v ∈ b ∧ x ∈ u ∧ x ∈ v ⇒ ∃w. w ∈ b ∧ x ∈ w ∧ w ⊆ u ∩ v) ⇒ is_topology({u \| ∀x. x ∈ u ⇒ ∃w. w ∈ b ∧ x ∈ w ∧ w ⊆ u})` |
| `GeneratedOpenIff` | `u ∈ topology_generated(b) ⇔ ∃c. u = ⋃c ∧ ∀w. w ∈ c ⇒ ∃f. finite(f) ∧ ¬(f = ∅) ∧ f ⊆ b ∧ w = ⋂f` |
| `BaseOfGenerated` | `(∀u v. ∀x. u ∈ b ∧ v ∈ b ∧ x ∈ u ∧ x ∈ v ⇒ ∃w. w ∈ b ∧ x ∈ w ∧ w ⊆ u ∩ v) ⇒ topology_base(topology_generated(b), b)` |
| `BaseGenerates` | `topology_base(b) ⇒ topology_generated(b) = T` |

## Generation on a fixed carrier

`topology_generated_on(X, b)` is `topology_generated(b ∪ {X})`.
For a family of subsets of `X`, adjoining `X` makes the generated
space exactly `X`, including when the generating family is empty.
The least topology on `X` containing each family is a closure operator
on the powerset of the powerset of `X`, by `ClosureFromLeast`.

| member | statement |
|---|---|
| `TopologyGeneratedOnDef` | `topology_generated_on(X, b) = topology_generated(b ∪ {X})` |
| `GeneratedOnTopology` | `topology_generated_on(X, b)` is a topology |
| `GeneratedOnSpace` | `b ⊆ {s \| s ⊆ X} ⇒ ⋃topology_generated_on(X, b) = X` |
| `GeneratedOnContains` | `b ⊆ topology_generated_on(X, b)` |
| `GeneratedOnMinimal` | a topology on `X` containing `b` contains `topology_generated_on(X, b)` |
| `GeneratedOnClosureOperator` | generation on `X` is a closure operator on `{b \| b ⊆ {s \| s ⊆ X}}` |

## Induced and coinduced topologies

`induced_topology(X, S, f)` consists of the preimages of the members
of `S`, restricted to `X`. When `S` is a topology, these form a
topology. Their union is `preimage_on(X, f, ⋃S)`: it equals `X` when
`f` carries `X` into `⋃S`. The construction therefore keeps both the
specified domain carrier and the actual covered space visible.

`coinduced_topology(Y, T, f)` consists of the subsets of `Y` whose
restricted preimages are in `T`. It is a topology when `T` is one,
and its carrier is `Y` when `image(f, ⋃T) ⊆ Y`. The two constructions
satisfy `induced_topology(⋃T, S, f) ⊆ T` exactly when
`S ⊆ coinduced_topology(⋃S, T, f)`, without topology axioms.

| member | statement |
|---|---|
| `InducedTopologyDef` | `induced_topology(X, S, f) = image(λv. preimage_on(X, f, v), S)` |
| `InducedSpace` | `⋃induced_topology(X, S, f) = preimage_on(X, f, ⋃S)` |
| `InducedTopology` | `is_topology(S) ⇒ is_topology(induced_topology(X, S, f))` |
| `CoinducedTopologyDef` | `coinduced_topology(Y, T, f) = {v \| v ⊆ Y ∧ preimage_on(⋃T, f, v) ∈ T}` |
| `CoinducedTopology` | `is_topology(T) ⇒ is_topology(coinduced_topology(Y, T, f))` |
| `CoinducedSpace` | if `T` is a topology and `image(f, ⋃T) ⊆ Y`, the coinduced carrier is `Y` |
| `InducedCoinducedAdjunction` | `induced_topology(⋃T, S, f) ⊆ T ⇔ S ⊆ coinduced_topology(⋃S, T, f)` |

## The subspace topology

A subset s of the space carries the topology whose open sets are the
open sets of T cut down to s; its closed sets are the closed sets cut
down likewise, and the closure of a subset of s there is its closure
in the space cut to s. The subspace on the whole space is the space,
and a subspace of a subspace is the subspace on the meet. In an open
subspace the open sets are the open sets of T inside it, and in a
closed subspace the closed sets are the closed sets of T inside it.
What a subset of a subspace keeps of its compactness or connectedness
is the `compact` and `connected` chapters'.

| member | statement |
|---|---|
| `SubtopologyDef` | `subtopology(T, s) = image(λu. u ∩ s, T)` |
| `SubtopologyInduced` | `subtopology(T, s) = induced_topology(⋃T ∩ s, T, identity_map)` |
| `SubtopologySpace` | `⋃subtopology(T, s) = ⋃T ∩ s` — the subspace's points are the points of the space in s |
| `TraceOpen` | `u ∈ T ⇒ u ∩ s ∈ subtopology(T, s)` — the trace of an open set is open in the subspace |
| `OpenInSubtopology` | `t ∈ subtopology(T, s) ⇔ ∃u. t = u ∩ s ∧ u ∈ T` — and every open set of the subspace is such a trace |
| `SubtopologyTopology` | `is_topology(subtopology(s))` — induced along the identity on `⋃T ∩ s` |
| `ClosedInSubtopology` | `closed_in(subtopology(T, s), c) ⇔ ∃d. closed_in(T, d) ∧ c = d ∩ s` |
| `SubtopologySelf` | `subtopology(T, ⋃T) = T` |
| `SubtopologySubtopology` | `subtopology(subtopology(T, s), t) = subtopology(T, s ∩ t)` |
| `OpenInOpenSubtopology` | `s ∈ T ⇒ (t ∈ subtopology(s) ⇔ t ∈ T ∧ t ⊆ s)` |
| `ClosedInClosedSubtopology` | `closed_in(s) ⇒ (closed_in(subtopology(s), c) ⇔ closed_in(c) ∧ c ⊆ s)` |
| `ClosedInSubtopologyInsideClosed` | `closed_in(subtopology(s), c) ∧ closed_in(d) ∧ c ⊆ d ∧ d ⊆ s ⇒ closed_in(c)` |
| `ClosureSubtopology` | `s ⊆ ⋃T ∧ t ⊆ s ⇒ closure(subtopology(s), t) = closure(t) ∩ s` — card |

## Separation

A space is Hausdorff when two distinct points lie in disjoint open
sets. That is a property of the space, so the topology is its one
argument and is always spelled. A subspace of a Hausdorff space is
Hausdorff. The other separation properties and how they stand to this
one are the `separation` chapter's; the compact sets of a Hausdorff
space are `compact`'s.

| member | statement |
|---|---|
| `HausdorffDef` | `hausdorff(T) ⇔ ∀x y. x ∈ ⋃T ∧ y ∈ ⋃T ∧ x ≠ y ⇒ ∃u v. u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅` |
| `HausdorffSubtopology` | `hausdorff(T) ⇒ hausdorff(subtopology(T, s))` |

## The discrete topology, read

The subsets of a set X form a topology (`Discrete`, above): its points
are the points of X, and every subset of X is open in it.

| member | statement |
|---|---|
| `DiscreteSpace` | `⋃{t \| t ⊆ X} = X` |
