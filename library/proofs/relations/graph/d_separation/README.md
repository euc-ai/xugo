# d_separation — separation in a DAG on the moral graph of an ancestral set

Z separates X from Y in a DAG when, on the ancestors U of X ∪ Y ∪ Z,
moral adjacency — an edge in either direction, or a common child in U —
restricted to U ∖ Z connects no point of X to a point of Y
(`DSeparatedDef`). The definition uses ancestors, the edge relation and
the transitive closure, and no path objects; Pearl's reading by open
paths and colliders is a characterization theorem outside this
chapter.

A semigraphoid is a ternary relation on vertex sets that is trivial,
symmetric, and closed under decomposition, weak union and contraction
(`SemigraphoidOn`). Separation is read into any semigraphoid that
satisfies the local Markov condition at every vertex; that theorem is
the one place where graph and probability meet, and it mentions no
probability. The back-door and front-door conditions are separation and
ancestry statements in graphs with edges deleted.

| Member | Statement |
|---|---|
| `MoralDef` | `dag_moral(E, U, u, v) ⇔ u ≠ v ∧ (E(u, v) ∨ E(v, u) ∨ ∃w. w ∈ U ∧ E(u, w) ∧ E(v, w))` |
| `DSeparatedDef` | `d_separated(E, X, Y, Z)`: no point of X reaches a point of Y in `relation_on(U ∖ Z, dag_moral(E, U))`, U = `dag_ancestors(E, X ∪ Y ∪ Z)` |
| `SemigraphoidOn` | `semigraphoid_on(V, R)`: trivial, symmetric, decomposition, weak union and contraction on pairwise disjoint subsets of V |
| `BackdoorCriterionDef` | `backdoor_criterion(E, X, Y, Z) ⇔ dag_ancestors(E, Z) ∩ X = ∅ ∧ d_separated(dag_delete_out(E, X), Y, X, Z)` |
| `FrontdoorCriterionDef` | `frontdoor_criterion(E, X, Y, Z)`: no point of X is an ancestor of Y with the edges into Z deleted; ∅ separates Z from X with the edges out of X deleted; X separates Y from Z with the edges out of Z deleted |

## Certificates, the local-to-global theorem and the regime node

On a concrete graph a separation is shown by a certificate, not a
path: an ancestral set U containing X, Y and Z, and a set S that
contains X, misses Y and holds every moral neighbour it has in U ∖ Z
(`SeparationCertificate`). U need not be the ancestral set of the
three groups. Conversely, a separation of X from Y, with X apart from
Y and Z, yields a certificate inside every U between X and that
ancestral set: the points of U ∖ Z that moral walks from X reach
(`SeparationGivesCertificate`). The local-to-global theorem and both
regime lemmas take their cut from this converse. Deleting edges keeps
a separation.

The local-to-global theorem reads separation into any semigraphoid
with the local Markov property at every vertex. Its proof cuts the
ancestral moral graph by the certificate the separation yields and
inducts on the ancestral set: it removes a sink and reattaches it by
weak union, symmetry and contraction.

Rules 2 and 3 of the do-calculus state their conditions in graphs with
edges deleted. The regime node turns each into a separation in one
graph: the original graph with a root `none` added above Z
(`dag_add_root`, the original vertices embedded by `some`). The root
is the regime indicator, the node whose value chooses between the
observational regime and the one that intervenes on Z. For pairwise
disjoint Y, Z and W, Rule 2's condition becomes separation of Y from
the root given Z ∪ W (`RegimeSeparationExchange`), and Rule 3's
separation of Y from the root given W (`RegimeSeparationDelete`). Both
go through one certificate for the augmented graph
(`AddRootSeparationCertificate`): a set trapping the moral walks from
Y that misses the root's children and has no edge to one of them in U.

A group with no edges into it, and no ancestor of the others, is
separated from them (`DSeparatedIsolatedRoots`). So deleting the edges
into X separates X from every set with no ancestor in X
(`DeleteInSeparatesNonDescendants`), the condition the back-door and
front-door derivations read. Two more lemmas serve the identification
chapter: separation inside an ancestral set is read in the restricted
graph, and removing a set D from the graph is intervening on D and
conditioning on it.

| Member | Statement |
|---|---|
| `DSeparatedSymmetric` | separation of X from Y is separation of Y from X |
| `DSeparatedEdgeMonotone` | deleting edges keeps a separation |
| `SeparationCertificate` | an ancestral U ⊇ X ∪ Y ∪ Z and a set S containing X, disjoint from Y and closed under moral steps into U ∖ Z give `d_separated(E, X, Y, Z)` |
| `SeparationGivesCertificate` | conversely, if Z separates X from Y with X apart from Y and Z, every U with X ⊆ U ⊆ `dag_ancestors(E, X ∪ Y ∪ Z)` holds a set S with X ⊆ S ⊆ U ∖ Z, disjoint from Y and closed under moral steps into U ∖ Z |
| `DSeparatedAncestorsReachConditioningSet` | if W separates disjoint X and Y, each point of X that is an ancestor of Y is an ancestor of W |
| `DSeparatedIsolatedRoots` | a group with no edges into it that is no ancestor of the others is separated from them |
| `DeleteInSeparatesNonDescendants` | deleting the edges into X separates X from every set Y with no ancestor in X |
| `LocalToGlobalMarkov` | on a DAG, a semigraphoid with the local Markov property at every vertex holds at every separation of disjoint sets |
| `AddRootSeparationCertificate` | inside an ancestral U ⊇ Y ∪ W, a set S ⊇ Y that misses Z, has no edge into U ∩ Z and is closed under moral steps into U ∖ W separates `image(some, Y)` from the root `none` above Z by `image(some, W)` |
| `RegimeSeparationExchange` | `d_separated(dag_delete_out(E, Z), Y, Z, W)` gives separation of Y from the root none above Z by Z ∪ W |
| `RegimeSeparationDelete` | `d_separated(dag_delete_in(E, Z ∖ dag_ancestors(E, W)), Y, Z, W)` gives separation of Y from the root none above Z by W |
| `DSeparatedAncestralRestrict` | inside an ancestral set, separation in the graph and in its restriction agree — card |
| `DSeparatedRemoveIntervene` | separation in G[V ∖ D] is separation given D with the edges into D deleted — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
