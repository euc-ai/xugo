# separation — the separation axioms: T0, T1, regular and normal spaces

How well the open sets of a space tell its points and its closed sets
apart. Of two distinct points some open set holds exactly one
(`t0_space`); each has an open neighbourhood missing the other
(`t1_space`); the two lie in disjoint open sets (`hausdorff`, defined
with the space in `topological_space`). A closed set and a point
outside it lie in disjoint open sets (`regular_space`); two disjoint
closed sets do (`normal_space`). Each is a property of the space, so
the topology is its one argument and is spelled. Regular and normal ask
nothing of points: neither implies Hausdorff unless points are closed,
and where both are wanted a statement asks for both.

The chapter reads only open and closed sets. The real-valued functions
normality produces — Urysohn's lemma, Tietze's extension — and complete
regularity, which is defined by such a function, are the `real_valued`
chapter's, above the real line.

## The definitions

| member | statement |
|---|---|
| `T0SpaceDef` | `t0_space(T) ⇔ ∀x y. x ∈ ⋃T ∧ y ∈ ⋃T ∧ x ≠ y ⇒ ∃u. u ∈ T ∧ ¬(x ∈ u ⇔ y ∈ u)` |
| `T1SpaceDef` | `t1_space(T) ⇔ ∀x y. x ∈ ⋃T ∧ y ∈ ⋃T ∧ x ≠ y ⇒ ∃u. u ∈ T ∧ x ∈ u ∧ y ∉ u` |
| `RegularSpaceDef` | `regular_space(T) ⇔ ∀c. ∀x. closed_in(T, c) ∧ x ∈ ⋃T ∧ x ∉ c ⇒ ∃u v. u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ c ⊆ v ∧ u ∩ v = ∅` |
| `NormalSpaceDef` | `normal_space(T) ⇔ ∀s t. closed_in(T, s) ∧ closed_in(T, t) ∧ s ∩ t = ∅ ⇒ ∃u v. u ∈ T ∧ v ∈ T ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅` |

## T0, T1 and Hausdorff (axioms.go)

Hausdorff implies T1 and T1 implies T0. A space is T1 exactly when its
points are closed sets, so in a T1 space every finite set of points is
closed. A subspace of a T1 space is T1.

| member | statement |
|---|---|
| `HausdorffImpT1` | `hausdorff(T) ⇒ t1_space(T)` |
| `T1ImpT0` | `t1_space(T) ⇒ t0_space(T)` |
| `T1IffSingletonsClosed` | `t1_space(T) ⇔ ∀x. x ∈ ⋃T ⇒ closed_in({x})` |
| `T1FiniteClosed` | `t1_space(T) ∧ finite(s) ∧ s ⊆ ⋃T ⇒ closed_in(s)` |
| `T1Subtopology` | `t1_space(T) ⇒ t1_space(subtopology(T, s))` |

## Regular spaces

A space is regular exactly when every open neighbourhood of a point
holds an open one whose closure is still inside it — the form in which
regularity is used. A subspace of a regular space is regular. A regular
T0 space is Hausdorff: the open set telling two points apart has a
closed complement holding one of them, which regularity separates from
the other. A compact Hausdorff space is regular, a point being separated
from a compact set.

| member | statement |
|---|---|
| `RegularIffClosedNeighbourhoods` | `regular_space(T) ⇔ ∀w. ∀x. w ∈ T ∧ x ∈ w ⇒ ∃u. u ∈ T ∧ x ∈ u ∧ closure(u) ⊆ w` |
| `RegularSubtopology` | `regular_space(T) ⇒ regular_space(subtopology(T, s))` |
| `RegularT0ImpHausdorff` | `regular_space(T) ∧ t0_space(T) ⇒ hausdorff(T)` |
| `CompactHausdorffRegular` | `hausdorff(T) ∧ compact_in(⋃T) ⇒ regular_space(T)` |

## Normal spaces (normal.go)

A compact Hausdorff space is normal: its closed sets are compact, and
two disjoint compact sets of a Hausdorff space lie in disjoint open
sets. A space is normal exactly when a closed set inside an open set u
has an open neighbourhood whose closure is still inside u — the step
Urysohn's construction repeats. A normal space whose points are closed
is regular and Hausdorff, and a closed subspace of a normal space is
normal. That the topology of a distance is normal is `real_valued`'s
`MetricNormal`, and that a regular space every open cover of which has
a countable subcover is normal is `countability`'s.

| member | statement |
|---|---|
| `CompactHausdorffNormal` | `is_topology(T) ∧ hausdorff(T) ∧ compact_in(⋃T) ⇒ normal_space(T)` |
| `NormalShrink` | `normal_space(T) ∧ closed_in(T, c) ∧ u ∈ T ∧ c ⊆ u ⇒ ∃v. v ∈ T ∧ c ⊆ v ∧ closure(T, v) ⊆ u` |
| `NormalIffShrink` | `normal_space(T) ⇔ ∀c u. closed_in(c) ∧ u ∈ T ∧ c ⊆ u ⇒ ∃v. v ∈ T ∧ c ⊆ v ∧ closure(v) ⊆ u` |
| `NormalT1ImpRegular` | `normal_space(T) ∧ t1_space(T) ⇒ regular_space(T)` |
| `NormalT1ImpHausdorff` | `normal_space(T) ∧ t1_space(T) ⇒ hausdorff(T)` |
| `NormalClosedSubtopology` | `normal_space(T) ∧ closed_in(c) ⇒ normal_space(subtopology(c))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
