# compact — compact sets of a space

A subset k of a space is compact when every family of open sets
covering it has a finite subfamily covering it: `compact_in(T, k)` —
the open-cover definition; Lean defines compactness by filters and
proves this form. The space itself is compact when `compact_in(T, ⋃T)`; no
second constant says so. The topology is the first argument and is
left implicit under a law over `is_topology(T)`, as it is for
`closed_in`; most of what follows asks nothing of the axioms and spells
it. What continuous maps do to compactness is the `continuous`
chapter's, and products are `product_topology`'s.

## The definitions

| member | statement |
|---|---|
| `CompactInDef` | `compact_in(T, k) ⇔ k ⊆ ⋃T ∧ (∀c. c ⊆ T ∧ k ⊆ ⋃c ⇒ ∃d. d ⊆ c ∧ finite(d) ∧ k ⊆ ⋃d)` |
| `LocallyCompactSpaceDef` | `locally_compact_space(T) ⇔ ∀x. x ∈ ⋃T ⇒ ∃u k. u ∈ T ∧ compact_in(T, k) ∧ x ∈ u ∧ u ⊆ k` |

## What compactness survives (compact.go)

The empty set and every finite set of points are compact. A compact set
meets a closed set in a compact set: an open cover of the meet, with the
closed set's complement added, covers the compact set, and the members of
a finite subcover taken from the cover still cover the meet. A closed set
inside a compact set is its own meet with it, and so is compact.
Finitely many compact sets unite to a compact set. The compact sets of a
discrete space are its finite subsets: the singletons of a compact set's
points are open and cover it, and finitely many singletons hold
finitely many points. Read through complements, compactness is the finite
intersection property: a family of closed sets each finitely many of
which meet k has a point of k in common — so in a compact space a
decreasing sequence of non-empty closed sets has a common point. An
infinite subset s of a compact set has a limit point in it: otherwise
the open sets meeting s in finitely many points would cover the compact
set, finitely many would, and s, the union of its finitely many finite
traces on them, would be finite. None of this asks anything of the
axioms.

| member | statement |
|---|---|
| `EmptyCompact` | `compact_in(T, ∅)` |
| `FiniteCompact` | `finite(k) ∧ k ⊆ ⋃T ⇒ compact_in(T, k)` |
| `ClosedSubsetCompact` | `compact_in(T, k) ∧ closed_in(T, c) ∧ c ⊆ k ⇒ compact_in(T, c)` |
| `CompactInterClosed` | `compact_in(T, k) ∧ closed_in(T, c) ⇒ compact_in(T, k ∩ c)` |
| `CompactUnion` | `compact_in(T, s) ∧ compact_in(T, t) ⇒ compact_in(T, s ∪ t)` |
| `CompactUnions` | `finite(f) ∧ (∀k. k ∈ f ⇒ compact_in(T, k)) ⇒ compact_in(T, ⋃f)` |
| `CompactFip` | `compact_in(T, k) ⇔ k ⊆ ⋃T ∧ ∀f. (∀c. c ∈ f ⇒ closed_in(T, c)) ∧ (∀g. finite(g) ∧ g ⊆ f ⇒ ¬(k ∩ ⋂g = ∅)) ⇒ ¬(k ∩ ⋂f = ∅)` |
| `CompactNest` | `compact_in(T, ⋃T) ∧ (∀n. closed_in(T, c(n)) ∧ ¬(c(n) = ∅) ∧ c(n + 1) ⊆ c(n)) ⇒ ¬(⋂image(c, 𝕌) = ∅)` |
| `CompactLimitPoint` | `compact_in(T, k) ∧ s ⊆ k ∧ infinite(s) ⇒ ∃x. x ∈ k ∧ x ∈ derived_set(T, s)` |
| `DiscreteCompactIffFinite` | `compact_in({t \| t ⊆ X}, k) ⇔ finite(k) ∧ k ⊆ X` |

## Compact sets in a Hausdorff space

A point outside a compact set k in a Hausdorff space and k lie in
disjoint open sets. No choice function enters: the open sets separated
from the point are named as a family, which covers k by the Hausdorff
property; compactness takes finitely many of them, their union is an
open set around k, and a point separated from each of finitely many
sets is separated from their union
(`topological_space.SeparatedFromFiniteUnion`). Forgetting the open set
around k leaves a neighbourhood of the point missing k, and so k is
closed. Run once more over the points of a second compact set, with a
set in place of the point (`SetSeparatedFromFiniteUnion`), the same
argument separates two disjoint compact sets. Two compact sets of a Hausdorff space meet in a
compact set, each being closed.

| member | statement |
|---|---|
| `SeparatedFromCompact` | `hausdorff(T) ∧ compact_in(k) ∧ x ∈ ⋃T ∧ x ∉ k ⇒ ∃u. u ∈ T ∧ x ∈ u ∧ u ∩ k = ∅` |
| `CompactClosed` | `hausdorff(T) ∧ compact_in(k) ⇒ closed_in(k)` — the complement of k in the space is open by the pointwise criterion |
| `PointCompactSeparation` | `hausdorff(T) ∧ compact_in(k) ∧ x ∈ ⋃T ∧ x ∉ k ⇒ ∃u v. u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ k ⊆ v ∧ u ∩ v = ∅` |
| `SetSeparatedFromFiniteUnion` | `s ⊆ ⋃T ∧ finite(d) ∧ (∀w. w ∈ d ⇒ ∃v. v ∈ T ∧ s ⊆ v ∧ v ∩ w = ∅) ⇒ ∃v. v ∈ T ∧ s ⊆ v ∧ v ∩ ⋃d = ∅` |
| `CompactSeparation` | `hausdorff(T) ∧ compact_in(s) ∧ compact_in(t) ∧ s ∩ t = ∅ ⇒ ∃u v. u ∈ T ∧ v ∈ T ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅` |
| `CompactInter` | `hausdorff(T) ∧ compact_in(s) ∧ compact_in(t) ⇒ compact_in(s ∩ t)` |

## Subspaces

Compactness of a subset k of s does not depend on which of the two
spaces k is read in: cutting the open sets down to s changes nothing k
can see, so an open cover in one space turns into one in the other —
by cutting each open set to s, or by collecting the open sets whose
trace is a member of the cover. That is what lets a theorem about a map
from a subspace, such as a function continuous on an interval, use the
subset's compactness in the whole space.

| member | statement |
|---|---|
| `CompactInSubtopology` | `k ⊆ s ⇒ (compact_in(subtopology(T, s), k) ⇔ compact_in(T, k))` |
| `CompactInOwnSubtopology` | `compact_in(T, k) ⇒ compact_in(subtopology(T, k), k)` |

## Locally compact spaces

A space is locally compact when every point has an open neighbourhood
inside a compact set: `locally_compact_space(T)`, a property of the
space, with the topology spelled. A compact space is locally compact,
and a closed subspace of a locally compact space is. In a Hausdorff
space the compact set can be taken inside any given neighbourhood: every
open neighbourhood of a point holds an open one whose closure is compact
and still inside — which makes an open subspace locally compact too.

| member | statement |
|---|---|
| `CompactImpLocallyCompact` | `compact_in(⋃T) ⇒ locally_compact_space(T)` |
| `LocallyCompactClosedSubtopology` | `locally_compact_space(T) ∧ closed_in(T, c) ⇒ locally_compact_space(subtopology(T, c))` |
| `LocallyCompactHausdorffNeighbourhood` | `hausdorff(T) ∧ locally_compact_space(T) ∧ w ∈ T ∧ x ∈ w ⇒ ∃v. v ∈ T ∧ x ∈ v ∧ compact_in(closure(v)) ∧ closure(v) ⊆ w` |
| `LocallyCompactOpenSubtopology` | `hausdorff(T) ∧ locally_compact_space(T) ∧ u ∈ T ⇒ locally_compact_space(subtopology(u))` |

## The Alexander subbase lemma (alexander.go)

A set X is compact in the topology a family b generates on it as soon as
every cover of X by members of b has a finite subcover; the members of b
need not lie in X, X being itself one of the generators. Suppose not. The
open covers of X with no finite subcover hold the union of each non-empty
chain of them — a finite subfamily of that union lies in one member of
the chain (`finite_set.FiniteSubsetUnionsChain`) — so by Zorn's lemma
(`order.ZornFamily`) one of them, m, is maximal. An open set outside m
covers X with finitely many members of m, adding it to m leaving the
family; and X itself is not a member of m. A point of X lies in a member
w of m, so in the meet of finitely many generators inside w
(`topological_space.GeneratedOpenIff`). Were none of them in m ∩ b, each
would cover X with finitely many members of m, and so would their meet
(`IntersCoverUpToFinite`, by induction on the finite family): w and those
members would be a finite subcover of m. So the members of m ∩ b cover
X, finitely many already do by the hypothesis, and m has a finite
subcover after all. This is the lemma Tychonoff's theorem stands on
(`product_topology.Tychonoff`).

| member | statement |
|---|---|
| `IntersCoverUpToFinite` | `finite(f) ∧ (∀s. s ∈ f ⇒ ∃d. d ⊆ c ∧ finite(d) ∧ k ⊆ s ∪ ⋃d) ⇒ ∃d. d ⊆ c ∧ finite(d) ∧ k ⊆ ⋂f ∪ ⋃d` |
| `AlexanderSubbase` | `(∀c. c ⊆ b ∧ X ⊆ ⋃c ⇒ ∃d. d ⊆ c ∧ finite(d) ∧ X ⊆ ⋃d) ⇒ compact_in(topology_generated_on(X, b), X)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
