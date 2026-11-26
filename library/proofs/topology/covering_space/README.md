# covering_space — covering maps and the lifting of paths and of homotopies of paths through them

An open set u of the base S is evenly covered by p when the part of the
covering space T that p carries into u is a union of pairwise disjoint
open sets, the sheets, each carried homeomorphically onto u:
`evenly_covered(T, S, p, u)`. A covering map is continuous with every
point of the base in an evenly covered open set: `covering_map(T, S, p)`.
It is not asked to be onto; nothing below uses it, and when the base is
a topology the points it reaches form an open and closed set.

On a sheet p has an inverse, and that is the whole engine of the
chapter. Two lifts of one map from a connected space that agree at a
point agree everywhere, the points where they agree and the points where
they differ each forming an open set. A path lifts from any point over
its start, and a map of the unit square from any point over the image of
its corner: cut the interval or the square by a Lebesgue number into
pieces each carried into one evenly covered set and lift piece by piece
through the inverse on a sheet. So two paths homotopic with their ends
held lift, from one point, to two paths homotopic with their ends held
and in particular ending at one point, the monodromy theorem; and a
covering map induces an injective map of fundamental groups. Lifting of
homotopies over a general space is not stated: the circle and its
consequences need paths and squares only.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `evenly_covered(T, S, p, u)` | `u ∈ S ∧ ∃v. v ⊆ T ∧ ⋃v = preimage_on(⋃T, p, u) ∧ (∀w w'. w ∈ v ∧ w' ∈ v ∧ w ≠ w' ⇒ w ∩ w' = ∅) ∧ (∀w. w ∈ v ⇒ homeomorphic_map(subtopology(T, w), subtopology(S, u), p))` |
| `covering_map(T, S, p)` | `continuous_map(T, S, p) ∧ ∀b. b ∈ ⋃S ⇒ ∃u. b ∈ u ∧ evenly_covered(T, S, p, u)` |

## Lifting (lifting.go)

| member | statement |
|---|---|
| `LiftsLocallyAgreeOrDiffer` | `covering_map(T, S, p) ∧ is_topology(R)`, f and g continuous from R to T with `p ∘ f = p ∘ g` on ⋃R, and `q ∈ ⋃R` ⇒ some open N holding q on which f and g agree throughout or differ throughout |
| `LiftUnique` | `covering_map(T, S, p) ∧ is_topology(R) ∧ connected_in(R, ⋃R)`, f and g continuous from R to T with `p ∘ f = p ∘ g` on ⋃R and `f(z) = g(z)` at a point z ⇒ `f = g` on ⋃R |
| `PathLifting` | `covering_map(T, S, p) ∧ path_in(S, g) ∧ e ∈ ⋃T ∧ p(e) = g(&0) ⇒ ∃h. path_in(T, h) ∧ h(&0) = e ∧ ∀t. &0 ≤ t ∧ t ≤ &1 ⇒ p(h(t)) = g(t)` — card |
| `SquareLifting` | `covering_map(T, S, p) ∧ continuous_map(product_topology(«I», «I»), S, H) ∧ e ∈ ⋃T ∧ p(e) = H((&0, &0)) ⇒` a continuous K on the square into T with `K((&0, &0)) = e` and `p ∘ K = H` on the square — card |
| `PathHomotopyLifting` | `covering_map(T, S, p) ∧ path_homotopic(S, g, h)`, g' and h' paths of T from one point over g and h ⇒ `path_homotopic(T, g', h')` — card |
| `CoveringFundamentalMapInjective` | `covering_map(T, S, p) ∧ e ∈ ⋃T ⇒ injective_on(fundamental_group(T, e).carrier, fundamental_map(S, p))` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
