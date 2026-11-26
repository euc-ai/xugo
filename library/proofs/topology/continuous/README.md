# continuous — maps between spaces: continuous, open, closed and quotient maps, homeomorphisms

A map f between two spaces is continuous when it carries the points
of the first into the second and the preimage of every open set is
open: `continuous_map(T, S, f)`. The preimage is cut to the space,
`preimage_on(⋃T, f, v)`, since the map's domain type may hold points
the space does not; Lean's `f ⁻¹' v` needs no cut, its space being a
type.

Continuity is the chapter's structure. `continuous_map(T, S, f)` is a
predicate over three explicit components (constitution §Structures),
and a member that assumes it is its law, `continuous_map(T, S, f) ⇒
body`, stated through `ContinuousMap.Law` with the components bound
once. Inside such a law the first space's one-space notions are
written short and the second's spelled — `compact_in(k) ⇒
compact_in(S, image(f, k))` — and that is how the two spaces are told
apart. A consumer holding a continuity fact reads a law at it and
names no space: `ImageCompact.Read(cont).At(k)`. The other properties
a map may have — open, closed and quotient maps, homeomorphisms,
embeddings — are structures over the same three components, their laws
stated the same way. A statement whose map runs between spaces built
from others (a subspace, a product, the line) spells its continuity in
full, as a law cannot bind a compound component. Most of what continuity
gives, it gives from the definition alone; a theorem that needs an
axiom of a space — a constant map or a pasting, of the domain; the
compact-to-Hausdorff theorems, of the target — carries that space's
`is_topology` in its body.

A map is only ever read at the points of its space: one that agrees
there with a continuous map is continuous (`Eq`), which is what lets a
statement ignore what a map does elsewhere.

## The structures and the definitions (definitions.go)

| member | statement |
|---|---|
| `ContinuousMap` | `continuous_map(T, S, f) ⇔ (∀x. x ∈ ⋃T ⇒ f(x) ∈ ⋃S) ∧ (∀v. v ∈ S ⇒ {x \| x ∈ ⋃T ∧ f(x) ∈ v} ∈ T)` |
| `ContinuousMapAtDef` | `continuous_map_at(T, S, f, x) ⇔ x ∈ ⋃T ∧ f(x) ∈ ⋃S ∧ (∀v. v ∈ S ∧ f(x) ∈ v ⇒ ∃u. u ∈ T ∧ x ∈ u ∧ (∀y. y ∈ u ⇒ f(y) ∈ v))` |
| `OpenMap` | `open_map(T, S, f) ⇔ ∀u. u ∈ T ⇒ image(f, u) ∈ S` |
| `ClosedMap` | `closed_map(T, S, f) ⇔ ∀c. closed_in⟨A:A⟩(T, c) ⇒ closed_in⟨A:B⟩(S, image(f, c))` |
| `QuotientMap` | `quotient_map(T, S, f) ⇔ image(f, ⋃T) = ⋃S ∧ (∀v. v ⊆ ⋃S ⇒ ({x \| x ∈ ⋃T ∧ f(x) ∈ v} ∈ T ⇔ v ∈ S))` |
| `QuotientTopologyDef` | `quotient_topology(T, f) = {v:B → bool \| v ⊆ image(f, ⋃T) ∧ {x \| x ∈ ⋃T ∧ f(x) ∈ v} ∈ T}` |
| `HomeomorphicMap` | `homeomorphic_map(T, S, f) ⇔ continuous_map⟨A:A, B:B⟩(T, S, f) ∧ (∃g. continuous_map⟨A:B, B:A⟩(S, T, g) ∧ (∀x. x ∈ ⋃T ⇒ g(f(x)) = x) ∧ (∀y. y ∈ ⋃S ⇒ f(g(y)) = y))` |
| `HomeomorphicDef` | `homeomorphic(T, S) ⇔ ∃f. homeomorphic_map(T, S, f)` |
| `EmbeddingMap` | `embedding_map(T, S, f) ⇔ homeomorphic_map(T, subtopology(S, image(f, ⋃T)), f)` |
| `RetractOfDef` | `retract_of(T, s) ⇔ s ⊆ ⋃T ∧ (∃r. continuous_map(T, subtopology(T, s), r) ∧ (∀x. x ∈ s ⇒ r(x) = x))` |
| `FixedPointPropertyDef` | `fixed_point_property(T) ⇔ ∀f. continuous_map(T, T, f) ⇒ ∃x. x ∈ ⋃T ∧ f(x) = x` |

## The axioms

A structure's axioms are the conjuncts of its definition, cited at a
hypothesis rather than unfolded: a continuous map carries the space
into the target and pulls open sets back to open sets; a homeomorphism
is continuous and has a continuous inverse; a quotient map is onto and
makes a subset of the target open exactly when its preimage is.

| member | statement |
|---|---|
| `MapsInto` | `continuous_map(T, S, f) ⇒ ∀x. x ∈ ⋃T ⇒ f(x) ∈ ⋃S` |
| `PreimageOpen` | `continuous_map(T, S, f) ⇒ ∀v. v ∈ S ⇒ {x \| x ∈ ⋃T ∧ f(x) ∈ v} ∈ T` |
| `HomeomorphismContinuous` | `homeomorphic_map(T, S, f) ⇒ continuous_map(T, S, f)` |
| `HomeomorphismInverseMaps` | `homeomorphic_map(T, S, f) ⇒ ∃g. continuous_map(S, T, g) ∧ (∀x. x ∈ ⋃T ⇒ g(f(x)) = x) ∧ (∀y. y ∈ ⋃S ⇒ f(g(y)) = y)` |
| `QuotientOnto` | `quotient_map(T, S, f) ⇒ image(f, ⋃T) = ⋃S` |
| `QuotientOpenIff` | `quotient_map(T, S, f) ⇒ ∀v. v ⊆ ⋃S ⇒ ({x \| x ∈ ⋃T ∧ f(x) ∈ v} ∈ T ⇔ v ∈ S)` |

## Composition, constants and subspaces (continuous.go)

Continuous maps compose and the identity is one; a constant map to a
point of the second space is one. A continuous map is continuous on
every subspace, and a map is continuous into a subspace exactly when it
is continuous into the space and takes its values in the subset.

| member | statement |
|---|---|
| `Compose` | `continuous_map(T, S, f) ∧ continuous_map(S, R, g) ⇒ continuous_map(T, R, g ∘ f)` |
| `Identity` | `continuous_map(T, T, identity_map)` — the preimage of an open set under the identity is the set itself, the cut to ⋃T losing nothing |
| `Constant` | `is_topology(T) ∧ c ∈ ⋃S ⇒ continuous_map(T, S, λx. c)` |
| `Eq` | `(∀x. x ∈ ⋃T ⇒ f(x) = g(x)) ∧ continuous_map(T, S, f) ⇒ continuous_map(T, S, g)` |
| `FromSubtopology` | `continuous_map(T, S, f) ⇒ continuous_map(subtopology(T, s), S, f)` |
| `IntoSubtopology` | `continuous_map(T, subtopology(S, t), f) ⇔ continuous_map(T, S, f) ∧ (∀x. x ∈ ⋃T ⇒ f(x) ∈ t)` |

## Normalized continuous maps (hom_sets.go)

`continuous_hom_set(T, S)` holds the continuous maps whose values off
`⋃T` are fixed to `junk`. The domain and codomain may have different
host types. Normalization preserves the values that continuity reads,
so every continuous map determines a representative in this hom set.
The codomain default need not belong to the target carrier, and the
empty source carrier needs no separate convention.

| Member | Statement |
| --- | --- |
| `ContinuousHomSetDef` | Continuous maps `T → S` fixed by normalization off `⋃T`. |
| `NormalizeHomSetIff` | `normalize_on(⋃T, junk, f)` belongs to the hom set exactly when `f` is continuous. |
| `HomSetExt` | Hom-set representatives are equal exactly when they agree on the source space. |
| `HomSetIdentity` | The normalized identity belongs to the hom set from `T` to itself. |
| `HomSetCompose` | Normalized composition closes the continuous hom sets. |

## Continuity read other ways

The induced-topology reading separates the two parts of continuity:
`image(f, ⋃T) ⊆ ⋃S` puts the map on the carriers, and
`induced_topology(⋃T, S, f) ⊆ T` says that every pulled-back open is
open. This equivalence uses no topology axiom.
By `topological_space.InducedCoinducedAdjunction`, the second part can
also be read as `S ⊆ coinduced_topology(⋃S, T, f)`.

The complement in ⋃T of a preimage is the preimage of the complement
in ⋃S, because f carries ⋃T into ⋃S; through that identity the
open-set reading of continuity and the closed-set reading are dual.
Continuity is checked on a base of the second space, or on any family
generating its topology; it is continuity at each point of the space;
and it carries the closure of a set into the closure of its image.

| member | statement |
|---|---|
| `ContinuousIffInduced` | `continuous_map(T, S, f) ⇔ image(f, ⋃T) ⊆ ⋃S ∧ induced_topology(⋃T, S, f) ⊆ T` |
| `ClosedPreimage` | `continuous_map(T, S, f) ⇔ (∀x. x ∈ ⋃T ⇒ f(x) ∈ ⋃S) ∧ (∀c. closed_in(S, c) ⇒ closed_in(T, {x \| x ∈ ⋃T ∧ f(x) ∈ c}))` |
| `ContinuousOnBase` | `is_topology(T) ∧ topology_base(S, b) ⇒ (continuous_map(T, S, f) ⇔ (∀x. x ∈ ⋃T ⇒ f(x) ∈ ⋃S) ∧ (∀v. v ∈ b ⇒ {x \| x ∈ ⋃T ∧ f(x) ∈ v} ∈ T))` |
| `ContinuousIntoGenerated` | `is_topology(T) ⇒ (continuous_map(T, topology_generated(b), f) ⇔ (∀x. x ∈ ⋃T ⇒ f(x) ∈ ⋃b) ∧ (∀v. v ∈ b ⇒ {x \| x ∈ ⋃T ∧ f(x) ∈ v} ∈ T))` |
| `ContinuousIffAt` | `continuous_map(T, S, f) ⇔ ∀x. x ∈ ⋃T ⇒ continuous_map_at(T, S, f, x)` |
| `ImageClosureSubset` | `is_topology(S) ∧ continuous_map(T, S, f) ∧ s ⊆ ⋃T ⇒ image(f, closure(T, s)) ⊆ closure(S, image(f, s))` |

## Pasting

A map continuous on each of two closed sets that cover the space is
continuous: the preimage of a closed set is its part in the one united
with its part in the other, each closed in its subspace and so in the
space, the subspace being closed, and the union of two closed sets is
closed. A map continuous on each member of an open cover is continuous,
the preimage of an open set being open, as each of its points lies in
its preimage in a member of the cover, open in an open subspace and so
open. Two closed pieces paste, so by induction finitely many do.

| member | statement |
|---|---|
| `ClosedPasting` | `is_topology(T) ∧ closed_in(c) ∧ closed_in(d) ∧ ⋃T ⊆ c ∪ d ∧ continuous_map(subtopology(c), S, f) ∧ continuous_map(subtopology(d), S, f) ⇒ continuous_map(T, S, f)` |
| `OpenPasting` | `is_topology(T) ∧ c ⊆ T ∧ ⋃T ⊆ ⋃c ∧ (∀u. u ∈ c ⇒ continuous_map(subtopology(u), S, f)) ⇒ continuous_map(T, S, f)` |
| `FiniteClosedPasting` | `is_topology(T) ∧ finite(k) ∧ (∀c. c ∈ k ⇒ closed_in(T, c)) ∧ ⋃T ⊆ ⋃k ∧ (∀c. c ∈ k ⇒ continuous_map(subtopology(T, c), S, f)) ⇒ continuous_map(T, S, f)` — card |

## What continuous maps preserve

The image of a compact set is compact, and the image of a connected
set is connected. Each is one application of the definition at sets
pulled back along the map. An open cover of the image pulls back to an
open cover of k, finitely many preimages cover k, and the finitely many
sets of the cover they came from cover the image — the one finiteness
fact spent being `finite_set.FiniteSubsetImage`. Two open sets that
would split the image pull back to two open sets that would split k.
With countable for finite the first argument carries a Lindelöf space
onto a Lindelöf space: one set of the cover is chosen for each of the
countably many preimages, and the chosen sets are countably many by
`cardinal.CountableImage`.

| member | statement |
|---|---|
| `ImageCompact` | `continuous_map(T, S, f) ∧ compact_in(T, k) ⇒ compact_in(S, image(f, k))` |
| `ImageConnected` | `continuous_map(T, S, f) ∧ connected_in(T, k) ⇒ connected_in(S, image(f, k))` |
| `ImageLindelof` | `continuous_map(T, S, f) ∧ lindelof_space(T) ∧ image(f, ⋃T) = ⋃S ⇒ lindelof_space(S)` |

## Open, closed and quotient maps (maps.go)

A map is open when it carries open sets to open sets and closed when it
carries closed sets to closed sets; neither is asked to be continuous.
A quotient map carries the first space onto the second so that a subset
of the second is open exactly when its preimage is. It is continuous; a
continuous map onto the second space that is open or closed is one;
quotient maps compose; and a map out of the second space is continuous
exactly when its composite with the quotient map is. The quotient
topology of a map, `quotient_topology(T, f)`, is the family of subsets
of the image whose preimage is open — a topology, onto which the map is
a quotient map, and the only one: a map is a quotient map exactly when
it is onto and the second topology is its quotient topology.
The quotient topology is `coinduced_topology(image(f, ⋃T), T, f)`:
the image supplies its target carrier, and `CoinducedTopology` supplies
the topology axioms.

| member | statement |
|---|---|
| `QuotientImpContinuous` | `quotient_map(T, S, f) ⇒ continuous_map(T, S, f)` |
| `OpenSurjectionQuotient` | `continuous_map(T, S, f) ∧ open_map(T, S, f) ∧ image(f, ⋃T) = ⋃S ⇒ quotient_map(T, S, f)` |
| `ClosedSurjectionQuotient` | `continuous_map(T, S, f) ∧ closed_map(T, S, f) ∧ image(f, ⋃T) = ⋃S ⇒ quotient_map(T, S, f)` |
| `QuotientUniversal` | `quotient_map(T, S, f) ⇒ (continuous_map(S, R, g) ⇔ continuous_map(T, R, g ∘ f))` |
| `QuotientCompose` | `quotient_map(T, S, f) ∧ quotient_map(S, R, g) ⇒ quotient_map(T, R, g ∘ f)` |
| `QuotientTopologyCoinduced` | `quotient_topology(T, f) = coinduced_topology(image(f, ⋃T), T, f)` |
| `QuotientTopologyTopology` | `is_topology(T) ⇒ is_topology(quotient_topology(T, f))` |
| `QuotientTopologyQuotientMap` | `is_topology(T) ⇒ quotient_map(T, quotient_topology(T, f), f)` |
| `QuotientMapIff` | `quotient_map(T, S, f) ⇔ image(f, ⋃T) = ⋃S ∧ S = quotient_topology(T, f)` |

## The quotient by the fibres (fibre_quotient.go)

A continuous map identifies two points of its space when it takes one
value at both: its classes are its fibres through the points of the
space, `«fibre»(x) = {y | y ∈ ⋃T ∧ f(y) = f(x)}`, and the class map is a
quotient map onto `quotient_topology(T, «fibre»)`. The map factors
through the class map: sending a class to f's value at a point chosen in
it gives a map h that is continuous on the quotient (its composite with
the class map agrees with f, so the universal property applies), one to
one on the classes (the fibre of f over h's value at a class is that
class), and has f's own image. When f is onto a Hausdorff space and
already onto it from a compact part k of its space, every class is the
class of a point of k, so the quotient is compact, the continuous image
of k; h is then a continuous bijection from a compact space onto a
Hausdorff one, a homeomorphism — the target is the quotient of the space
by the fibres. The circle as ℝ/ℤ, the spheres and the torus are its
instances (`vector/standard_quotient_spaces`), with k a closed interval,
a ball or a square.

| member | statement |
|---|---|
| `FibreQuotientFactor` | `is_topology(T) ∧ continuous_map(T, S, f) ⇒ ∃h. (∀x. x ∈ ⋃T ⇒ h(«fibre»(x)) = f(x)) ∧ continuous_map(quotient_topology(T, «fibre»), S, h) ∧ injective_on(⋃quotient_topology(T, «fibre»), h) ∧ image(h, ⋃quotient_topology(T, «fibre»)) = image(f, ⋃T)` |
| `FibreQuotientHomeomorphic` | `is_topology(T) ∧ is_topology(S) ∧ hausdorff(S) ∧ continuous_map(T, S, f) ∧ compact_in(T, k) ∧ image(f, k) = ⋃S ⇒ homeomorphic(quotient_topology(T, «fibre»), S)` |

## Homeomorphisms (homeomorphism.go)

A homeomorphism is a continuous map with a continuous inverse on the
two spaces, so a map agreeing with one on its space is one too. Its
inverse is one, the identity is one, they compose, and one restricts
to a homeomorphism of each subspace onto its image; so
being homeomorphic is reflexive, symmetric and transitive. A
homeomorphism is exactly a continuous open bijection of the spaces. A
continuous bijection is one as soon as it carries closed sets to closed
sets, since the preimage of a closed set under the inverse is its image
under the map. From a compact space to a Hausdorff space every
continuous map does: a closed set is compact, its image compact, and a
compact set of a Hausdorff space closed. So a continuous bijection from
a compact space onto a Hausdorff space is a homeomorphism.

| member | statement |
|---|---|
| `HomeomorphismEq` | `(∀x. x ∈ ⋃T ⇒ f(x) = g(x)) ∧ homeomorphic_map(T, S, f) ⇒ homeomorphic_map(T, S, g)` |
| `HomeomorphismInverse` | `homeomorphic_map(T, S, f) ⇒ homeomorphic_map(S, T, inverse_on(⋃T, f)) ∧ (∀x. x ∈ ⋃T ⇒ inverse_on(⋃T, f, f(x)) = x) ∧ (∀y. y ∈ ⋃S ⇒ f(inverse_on(⋃T, f, y)) = y)` |
| `HomeomorphismIdentity` | `homeomorphic_map(T, T, identity_map)` |
| `HomeomorphismCompose` | `homeomorphic_map(T, S, f) ∧ homeomorphic_map(S, R, g) ⇒ homeomorphic_map(T, R, g ∘ f)` |
| `HomeomorphismIffOpenBijection` | `homeomorphic_map(T, S, f) ⇔ continuous_map(T, S, f) ∧ open_map(T, S, f) ∧ image(f, ⋃T) = ⋃S ∧ injective_on(⋃T, f)` |
| `HomeomorphismSubtopologies` | `homeomorphic_map(T, S, f) ∧ s ⊆ ⋃T ⇒ homeomorphic_map(subtopology(T, s), subtopology(S, image(f, s)), f)` |
| `HomeomorphicRefl` | `homeomorphic(T, T)` |
| `HomeomorphicSym` | `homeomorphic(T, S) ⇒ homeomorphic(S, T)` |
| `HomeomorphicTrans` | `homeomorphic(T, S) ∧ homeomorphic(S, R) ⇒ homeomorphic(T, R)` |
| `ClosedBijectionHomeomorphism` | `continuous_map(T, S, f) ∧ (∀c. closed_in(T, c) ⇒ closed_in(S, image(f, c))) ∧ image(f, ⋃T) = ⋃S ∧ injective_on(⋃T, f) ⇒ homeomorphic_map(T, S, f)` |
| `CompactHausdorffClosedMap` | `is_topology(S) ∧ hausdorff(S) ∧ compact_in(T, ⋃T) ∧ continuous_map(T, S, f) ∧ closed_in(T, c) ⇒ closed_in(S, image(f, c))` |
| `CompactHausdorffHomeomorphism` | `is_topology(S) ∧ hausdorff(S) ∧ compact_in(T, ⋃T) ∧ continuous_map(T, S, f) ∧ image(f, ⋃T) = ⋃S ∧ injective_on(⋃T, f) ⇒ homeomorphic_map(T, S, f)` |

## What a homeomorphism preserves

A space with a continuous one-to-one map into a Hausdorff space is
Hausdorff, so of two homeomorphic spaces one is Hausdorff exactly when
the other is; the same holds of compactness and of connectedness, by
the image theorems along the map and its inverse.

| member | statement |
|---|---|
| `HausdorffInjectivePreimage` | `continuous_map(T, S, f) ∧ hausdorff(S) ∧ injective_on(⋃T, f) ⇒ hausdorff(T)` |
| `HomeomorphicHausdorff` | `homeomorphic(T, S) ⇒ (hausdorff(T) ⇔ hausdorff(S))` |
| `HomeomorphicCompact` | `homeomorphic(T, S) ⇒ (compact_in(T, ⋃T) ⇔ compact_in(S, ⋃S))` |
| `HomeomorphicConnected` | `homeomorphic(T, S) ⇒ (connected_in(T, ⋃T) ⇔ connected_in(S, ⋃S))` |

## Embeddings and retracts

An embedding is a homeomorphism onto its image, read as a subspace of
the second space. It is continuous, and a continuous one-to-one map of
a compact space into a Hausdorff space is one. A subset s is a retract
of the space when a continuous map of the space into the subspace s
fixes every point of s: `retract_of(T, s)`. A retract of a Hausdorff
space is closed.

| member | statement |
|---|---|
| `EmbeddingImpContinuous` | `embedding_map(T, S, f) ⇒ continuous_map(T, S, f)` |
| `CompactHausdorffEmbedding` | `is_topology(S) ∧ hausdorff(S) ∧ compact_in(T, ⋃T) ∧ continuous_map(T, S, f) ∧ injective_on(⋃T, f) ⇒ embedding_map(T, S, f)` |
| `RetractClosed` | `hausdorff(T) ∧ retract_of(s) ⇒ closed_in(s)` |

## The fixed point property (fixed_point.go)

A space has the fixed point property when every continuous map of it
into itself fixes one of its points: `fixed_point_property(T)`. The
property is topological, carried across a homeomorphism by conjugating
the map, and it passes to a retract, a self-map of the retract followed
after the retraction being a self-map of the space whose fixed point is
already in the retract. Brouwer's theorem is that compact convex sets of
ℝⁿ have it (vector/convex_topology).

| member | statement |
|---|---|
| `HomeomorphicFixedPoint` | `homeomorphic(T, S) ∧ fixed_point_property(T) ⇒ fixed_point_property(S)` — card |
| `RetractFixedPoint` | `retract_of(T, s) ∧ fixed_point_property(T) ⇒ fixed_point_property(subtopology(T, s))` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
