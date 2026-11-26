# homotopy — homotopy of maps relative to a set, homotopy of paths with their ends held, homotopy equivalences and contractible spaces

A homotopy from f to g is a continuous map H on the product of the
space with the unit interval that starts at f and ends at g. Holding a
set a still — H((x, t)) = f(x) at every time for x in a — makes it a
homotopy relative to a, `homotopic_rel(T, S, a, f, g)`; with a empty it
is free homotopy, and paths homotopic with their two ends held,
`path_homotopic(T, g, h)`, are the case of the unit interval relative to
{0, 1}. The interval is `subtopology(real_topology, ⟦&0, &1⟧)`, written
«I» in the chapter's table, as path_connected reads it.

Neither map of a homotopy is asked to be continuous: each is H at one end
of the interval, continuous on the space when the space is a topology,
and composed with a path or a singular simplex continuous on any family. Homotopy relative to a set is reflexive on the
continuous maps, symmetric, and transitive on a space that is a
topology, the two homotopies being pasted along the middle of the
interval; composition on the left carries homotopies to homotopies.
For paths no axiom of the target is needed, since the pasting is done on
the square, and homotopy with the ends held is an equivalence on the
paths of any space.

The paths of a space form a groupoid up to this homotopy, and these are
its laws: joining (`path_connected`'s `path_join`) is associative,
the constant paths are units on either side, a path joined with its
reverse (`path_reverse`) is homotopic to a constant path, and joining and
reversing respect homotopy. The unit laws, associativity and the inverse
laws are all one lemma: a path read along two maps of the interval with
the same ends gives two homotopic paths, by the straight line between the
two maps. The other lemma the fundamental group reads is the square a
homotopy sweeps along a path: the image of the path at the end of the
homotopy is homotopic to the track of the path's start run backwards,
the image at the beginning, and the track of its end.

A homotopy equivalence names its inverse, as a chain homotopy
equivalence does: two continuous maps whose composites are homotopic to
the identities. A contractible space is one whose identity is homotopic
to a constant map at one of its points, so the empty space is not
contractible.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `homotopic_rel(T, S, a, f, g)` | `∃H. continuous_map(product_topology(T, «I»), S, H) ∧ (∀x. x ∈ ⋃T ⇒ H((x, &0)) = f(x) ∧ H((x, &1)) = g(x)) ∧ (∀x t. x ∈ a ∧ x ∈ ⋃T ∧ &0 ≤ t ∧ t ≤ &1 ⇒ H((x, t)) = f(x))` |
| `path_homotopic(T, g, h)` | `homotopic_rel(«I», T, {&0, &1}, g, h)` |
| `homotopy_equivalence(T, S, f, g)` | `continuous_map(T, S, f) ∧ continuous_map(S, T, g) ∧ homotopic_rel(T, T, ∅, g ∘ f, λx. x) ∧ homotopic_rel(S, S, ∅, f ∘ g, λy. y)` |
| `contractible_space(T)` | `∃c. c ∈ ⋃T ∧ homotopic_rel(T, T, ∅, λx. x, λx. c)` |

## Homotopy relative to a set (homotopy.go)

| member | statement |
|---|---|
| `HomotopicRelRefl` | `continuous_map(T, S, f) ⇒ homotopic_rel(T, S, a, f, f)` — card |
| `HomotopicRelSym` | `homotopic_rel(T, S, a, f, g) ⇒ homotopic_rel(T, S, a, g, f)` — card |
| `HomotopicRelTrans` | `is_topology(T) ∧ homotopic_rel(T, S, a, f, g) ∧ homotopic_rel(T, S, a, g, h) ⇒ homotopic_rel(T, S, a, f, h)` — card |
| `HomotopicRelComposeLeft` | `homotopic_rel(T, S, a, f, g) ∧ continuous_map(S, U, k) ⇒ homotopic_rel(T, U, a, k ∘ f, k ∘ g)` — card |
| `HomotopyAlongPath` | `continuous_map(product_topology(T, «I»), S, H) ∧ path_in(T, g) ⇒ path_homotopic(S, λt. H((g(t), &1)), path_join(path_join(path_reverse(λs. H((g(&0), s))), λt. H((g(t), &0))), λs. H((g(&1), s))))` — card |

## Paths up to homotopy (paths.go)

| member | statement |
|---|---|
| `PathHomotopicEnds` | `path_homotopic(T, g, h) ⇒ g(&0) = h(&0) ∧ g(&1) = h(&1)` — card |
| `PathHomotopicPaths` | `path_homotopic(T, g, h) ⇒ path_in(T, g) ∧ path_in(T, h)` — card |
| `PathHomotopicEquivalence` | `equivalence_on({g \| path_in(T, g)}, path_homotopic(T))` — card |
| `PathReparametriseHomotopic` | `path_in(T, g) ∧ continuous_map(«I», «I», a) ∧ continuous_map(«I», «I», b) ∧ a(&0) = b(&0) ∧ a(&1) = b(&1) ⇒ path_homotopic(T, g ∘ a, g ∘ b)` |
| `PathJoinHomotopic` | `path_homotopic(T, g, g') ∧ path_homotopic(T, h, h') ∧ g(&1) = h(&0) ⇒ path_homotopic(T, path_join(g, h), path_join(g', h'))` — card |
| `PathReverseHomotopic` | `path_homotopic(T, g, h) ⇒ path_homotopic(T, path_reverse(g), path_reverse(h))` — card |
| `PathJoinAssoc` | for paths g, h, k meeting end to start: `path_homotopic(T, path_join(path_join(g, h), k), path_join(g, path_join(h, k)))` — card |
| `PathJoinConstantLeft` | `path_in(T, g) ⇒ path_homotopic(T, path_join(λt. g(&0), g), g)` — card |
| `PathJoinConstantRight` | `path_in(T, g) ⇒ path_homotopic(T, path_join(g, λt. g(&1)), g)` — card |
| `PathJoinReverseRight` | `path_in(T, g) ⇒ path_homotopic(T, path_join(g, path_reverse(g)), λt. g(&0))` — card |
| `PathJoinReverseLeft` | `path_in(T, g) ⇒ path_homotopic(T, path_join(path_reverse(g), g), λt. g(&1))` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
