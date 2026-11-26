# connected — connected sets of a space and the components of its points

A subset k of a space is connected when two open sets that cover it and
each meet it share a point of it: `connected_in(T, k)` — Lean's
`IsPreconnected`. Its contrapositive is the textbook sentence, that k is
not split by two open sets each meeting it and disjoint ON k (two open
sets may overlap outside k and still split it); the positive form is a
Horn clause, which a proof applies at two open sets of its choosing. The
empty set is connected. The space itself is connected when
`connected_in(T, ⋃T)`. The topology is the first argument and is left
implicit under a law over `is_topology(T)`; most of what follows asks
nothing of the axioms and spells it. What continuous maps do to
connectedness is the `continuous` chapter's, and paths are
`path_connected`'s.

## The definitions

| member | statement |
|---|---|
| `ConnectedInDef` | `connected_in(T, k) ⇔ k ⊆ ⋃T ∧ (∀u v. u ∈ T ∧ v ∈ T ∧ k ⊆ u ∪ v ∧ k ∩ u ≠ ∅ ∧ k ∩ v ≠ ∅ ⇒ k ∩ u ∩ v ≠ ∅)` |
| `ConnectedComponentDef` | `connected_component(T, x) = ⋃{s:A → bool \| connected_in(T, s) ∧ x ∈ s}` |
| `LocallyConnectedSpaceDef` | `locally_connected_space(T) ⇔ ∀u. ∀x. u ∈ T ∧ x ∈ u ⇒ ∃v. v ∈ T ∧ connected_in(T, v) ∧ x ∈ v ∧ v ⊆ u` |

## Connected sets (connected.go)

The empty set and a single point of the space are connected. Connected
sets sharing a point unite to a connected set: two open sets covering
the union and each meeting it hold the common point on one side, and a
member meeting the other side is split by them. A set between a
connected set and its closure is connected, since an open set meeting
the closure meets the set; so the closure is. A connected set lies
inside or outside any set both open and closed, and a space is
connected exactly when its only such sets are the empty set and itself.

| member | statement |
|---|---|
| `EmptyConnected` | `connected_in(T, ∅)` |
| `SingletonConnected` | `x ∈ ⋃T ⇒ connected_in(T, {x})` |
| `ConnectedUnions` | `(∀s. s ∈ f ⇒ connected_in(T, s)) ∧ ¬(⋂f = ∅) ⇒ connected_in(T, ⋃f)` |
| `ConnectedUnion` | `connected_in(T, s) ∧ connected_in(T, t) ∧ ¬(s ∩ t = ∅) ⇒ connected_in(T, s ∪ t)` |
| `ConnectedIntermediateClosure` | `connected_in(s) ∧ s ⊆ t ∧ t ⊆ closure(s) ⇒ connected_in(t)` |
| `ConnectedClosure` | `connected_in(s) ⇒ connected_in(closure(s))` |
| `ConnectedClopen` | `connected_in(T, c) ∧ t ∈ T ∧ closed_in(T, t) ⇒ c ⊆ t ∨ c ∩ t = ∅` |
| `ConnectedIffNoClopen` | `connected_in(T, ⋃T) ⇔ ∀t. t ∈ T ∧ closed_in(T, t) ⇒ t = ∅ ∨ t = ⋃T` |

## Components

The component of a point is the union of the connected sets holding it,
`connected_component(T, x)` — the largest of them, empty when the point
is not one of the space. Components lie in the space and cover it; two
of them are equal or disjoint, so they partition it; each is connected,
and closed, since the closure of the component is a connected set
holding the point. A space is connected exactly when it is the
component of each of its points. Where there are only finitely many
components each is open as well.

The relation `R(x, y) ⇔ y ∈ connected_component(T, x)` is an
equivalence on the carrier `⋃T`. `ComponentClass` identifies its
classes there, and `ComponentsQuotient` identifies their family.
Coverage is the general `relations/equivalence.QuotientOnCovers`
law read at this equivalence.

| member | statement |
|---|---|
| `ComponentEquivalence` | `λx y. y ∈ connected_component(T, x)` is an equivalence on `⋃T` |
| `ComponentSubsetSpace` | `connected_component(T, x) ⊆ ⋃T` |
| `ComponentSelfIff` | `x ∈ connected_component(T, x) ⇔ x ∈ ⋃T` |
| `ComponentEmptyIff` | `connected_component(T, x) = ∅ ⇔ x ∉ ⋃T` |
| `ComponentConnected` | `connected_in(T, connected_component(T, x))` |
| `ComponentMaximal` | `connected_in(T, s) ∧ x ∈ s ⇒ s ⊆ connected_component(T, x)` |
| `ComponentEq` | `y ∈ connected_component(T, x) ⇒ connected_component(T, y) = connected_component(T, x)` |
| `ComponentClass` | for `x ∈ ⋃T`, the component is the class of `x` for the component relation restricted to `⋃T` |
| `ComponentsQuotient` | the image of the component map on `⋃T` is its `quotient_on` |
| `ComponentsDisjoint` | `connected_component(T, x) = connected_component(T, y) ∨ connected_component(T, x) ∩ connected_component(T, y) = ∅` |
| `ComponentsCover` | `⋃image(λx. connected_component(T, x), ⋃T) = ⋃T` |
| `ComponentClosed` | `closed_in(connected_component(x))` |
| `ConnectedIffOneComponent` | `connected_in(T, ⋃T) ⇔ ∀x. x ∈ ⋃T ⇒ connected_component(T, x) = ⋃T` |
| `FiniteComponentsOpen` | `finite(image(λy. connected_component(y), ⋃T)) ⇒ ∀x. connected_component(x) ∈ T` |

## Subspaces

Connectedness of a subset k of s does not depend on which of the two
spaces k is read in: a split of k by two open sets of one space is a
split by two of the other — their traces, or the open sets their two
parts are the traces of.

| member | statement |
|---|---|
| `ConnectedInSubtopology` | `k ⊆ s ⇒ (connected_in(subtopology(T, s), k) ⇔ connected_in(T, k))` |

## Locally connected spaces

A space is locally connected when every open neighbourhood of a point
holds a connected open neighbourhood of it: `locally_connected_space(T)`.
Its components are then open, an open subspace of it is locally
connected, and the property is exactly that the components of every
open subspace are open.

| member | statement |
|---|---|
| `LocallyConnectedComponentOpen` | `locally_connected_space(T) ⇒ ∀x. connected_component(x) ∈ T` |
| `LocallyConnectedOpenSubtopology` | `locally_connected_space(T) ∧ u ∈ T ⇒ locally_connected_space(subtopology(u))` |
| `LocallyConnectedIffComponentsOpen` | `locally_connected_space(T) ⇔ ∀u. ∀x. u ∈ T ⇒ connected_component(subtopology(u), x) ∈ T` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
