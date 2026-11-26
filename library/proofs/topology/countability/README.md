# countability — countable bases, dense countable sets and countable subcovers

Four ways a space can be small in the countable sense. Its topology has
a countable base (`second_countable_space`); each point has countably
many open sets among which every open neighbourhood of the point holds
one about the point (`first_countable_space`); a countable set of
points is dense (`separable_space`); every open cover of the space has
a countable subfamily covering it (`lindelof_space`, compactness of the
space with countable for finite). Each is a property of the space, so
the topology is its one argument and is spelled. Countability itself is
`sets/cardinal`'s.

## The definitions

| member | statement |
|---|---|
| `SecondCountableSpaceDef` | `second_countable_space(T) ⇔ ∃b. countable(b) ∧ topology_base(T, b)` |
| `FirstCountableSpaceDef` | `first_countable_space(T) ⇔ ∀x. x ∈ ⋃T ⇒ ∃b. countable(b) ∧ b ⊆ T ∧ (∀u. u ∈ T ∧ x ∈ u ⇒ ∃v. v ∈ b ∧ x ∈ v ∧ v ⊆ u)` |
| `SeparableSpaceDef` | `separable_space(T) ⇔ ∃c. countable(c) ∧ c ⊆ ⋃T ∧ closure(T, c) = ⋃T` |
| `LindelofSpaceDef` | `lindelof_space(T) ⇔ ∀c. c ⊆ T ∧ ⋃T ⊆ ⋃c ⇒ ∃d. d ⊆ c ∧ countable(d) ∧ ⋃T ⊆ ⋃d` |

## From a countable base (countability.go)

One point taken from each non-empty member of a countable base is a
countable dense set; and for an open cover, the base members that fit
inside some member of the cover are countably many and already cover
the space, so one member of the cover around each is a countable
subcover. A subspace of a space with a countable base has one, the
traces of the base.

| member | statement |
|---|---|
| `SecondCountableImpSeparable` | `is_topology(T) ∧ second_countable_space(T) ⇒ separable_space(T)` |
| `SecondCountableImpLindelof` | `second_countable_space(T) ⇒ lindelof_space(T)` |
| `SecondCountableSubtopology` | `second_countable_space(T) ⇒ second_countable_space(subtopology(T, s))` — card |
| `SecondCountableOpenCover` | a countable open cover by second countable subspaces makes the space second countable — card |

For a countable open cover, the countable bases of its subspaces
unite to a countable base of the whole space. Openness is essential
here: it makes every subspace base member open in the ambient space.

## Lindelöf spaces

A compact space is Lindelöf, a finite subcover being a countable one.
A regular Lindelöf space is normal: two disjoint closed sets are each
covered by countably many open sets whose closures miss the other, and
removing from the n-th set of each sequence the closures of the first n
of the other leaves disjoint open sets around the two.

| member | statement |
|---|---|
| `CompactImpLindelof` | `compact_in(T, ⋃T) ⇒ lindelof_space(T)` — card |
| `RegularLindelofNormal` | `is_topology(T) ∧ regular_space(T) ∧ lindelof_space(T) ⇒ normal_space(T)` — card |
| `LindelofCountableCover` | a countable cover by Lindelöf subspaces makes the space Lindelöf — card |

The Lindelöf conclusion needs no openness of the covering subspaces.
Trace an ambient open cover on each subspace and collect the chosen
countable subcovers. In particular, a countable union of compact
subspaces is Lindelöf.

That a continuous image of a Lindelöf space is Lindelöf is
`continuous.ImageLindelof`; that for the topology of a distance the
countable base, the countable dense set and the countable subcovers are
one property is `metric_space`'s.

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
