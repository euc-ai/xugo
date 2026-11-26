# dag — finite directed acyclic graphs as a vertex set and an edge relation

A directed graph is a vertex set V and an edge relation E with both
ends of every edge in V. It is a DAG when V is finite and no vertex
reaches itself along the edges (`DagOn`). Parents, ancestors and
descendants are read off E and its reflexive–transitive closure; the
ancestors of a set include the set. The operations on a graph are
operations on its edge relation: deleting the edges into a set, the
graph an intervention leaves; deleting the edges out of a set; the
induced subgraph, which is `relation_on`; and adding one root above a
set, on `option(A)` so that no unused vertex has to be assumed.

A concrete graph has one spelling: its vertices are the constructors
of an enumerated datatype, whose distinctness laws decide equality of
vertices, and its edges a finite set literal of pairs read through
`pair_relation`.

| Member | Statement |
|---|---|
| `DagOn` | `dag_on(V, E) ⇔ finite(V) ∧ (∀x y. E(x, y) ⇒ x ∈ V ∧ y ∈ V) ∧ (∀x. ¬transitive_closure(E, x, x))` |
| `ParentsDef` | `dag_parents(E, v) = {u \| E(u, v)}` |
| `AncestorsDef` | `dag_ancestors(E, X) = {u \| ∃x. x ∈ X ∧ reflexive_transitive_closure(E, u, x)}` |
| `AncestralDef` | `dag_ancestral(E, U) ⇔ ∀u v. E(u, v) ∧ v ∈ U ⇒ u ∈ U`: every parent of a point of U lies in U |
| `DescendantsDef` | `dag_descendants(E, X) = {u \| ∃x. x ∈ X ∧ reflexive_transitive_closure(E, x, u)}` |
| `DeleteInDef` | `dag_delete_in(E, X, u, v) ⇔ E(u, v) ∧ v ∉ X` |
| `DeleteOutDef` | `dag_delete_out(E, Z, u, v) ⇔ E(u, v) ∧ u ∉ Z` |
| `AddRootDef` | `dag_add_root(E, Z, p, q) ⇔ (∃u v. p = some(u) ∧ q = some(v) ∧ E(u, v)) ∨ (∃z. p = none ∧ q = some(z) ∧ z ∈ Z)` |
| `PairRelationDef` | `pair_relation(P, x, y) ⇔ (x, y) ∈ P` |

## Well-foundedness, ancestors and deleted edges

A DAG's edges and their transitive closure are well founded by
`FinitePredecessors`, and every nonempty set holds a sink of the edges
restricted to it; these carry the structural equations' solution and
every induction over the graph. A set is ancestral when it holds the
parents of its points (`dag_ancestral`). An ancestral set containing X
contains the ancestors of X, which is how the ancestors are bounded
without a path, and the ancestors of X are themselves ancestral. A set
with no edges into it adds only itself to the ancestors of any other
set, which reduces an intervened graph to the graph without the
intervention. Deleting the edges out of a subset of X keeps X's
ancestors, and so does deleting the edges into a set the ancestors of
X avoid.

| Member | Statement |
|---|---|
| `DagWellfounded` | `wellfounded(E) ∧ wellfounded(transitive_closure(E))` for a DAG |
| `DagSinkExists` | in a DAG, every nonempty set contains a point with no edge to a point of the set |
| `DagSubrelation` | fewer edges on the same vertices are a DAG |
| `AncestorsClosed` | `X ⊆ dag_ancestors(E, X)`, and `dag_ancestors(E, X)` is ancestral |
| `AncestorsUpperBound` | an ancestral U ⊇ X contains `dag_ancestors(E, X)` |
| `AncestorsMonotone` | more edges and a larger set give more ancestors |
| `AncestorsRootUnion` | with no edge into X, `dag_ancestors(E, X ∪ W) = X ∪ dag_ancestors(E, W)` |
| `AncestorsDeleteOut` | for Z ⊆ X, deleting the edges out of Z keeps the ancestors of X |
| `AncestorsDeleteIn` | if the ancestors of X miss Z, deleting the edges into Z keeps them |
| `DescendantsAncestorsDual` | `dag_descendants(E, X) ∩ Z = ∅ ⇔ dag_ancestors(E, Z) ∩ X = ∅` |
| `AddRootDag` | adding a root above Z ⊆ V keeps a DAG |

The framework mechanics (typed cites, recorded deps, the shared family
CNF blob, replay) are the standard ones — see
`library/chapter_constitution.md`.
