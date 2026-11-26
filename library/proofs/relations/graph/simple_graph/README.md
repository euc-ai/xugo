# simple_graph — simple undirected graphs

A graph has a vertex set V and an adjacency relation R. On V, R is
symmetric (`symmetric_on(V, R)`) and has no loops. The vertex set
therefore also specifies the isolated vertices. Each edge is the
two-element set of its endpoints.

Reachability is the reflexive–transitive closure of adjacency
restricted to V (`ReachableDef`), so walks concatenate, carry an
invariant and pass into a larger graph by the laws of
`relations/closure`; the first two are restated here for graphs
(`ReachableTransitive`, `ReachablePreserves`). The component of a vertex is its class under
reachability, and the components are the quotient of V by it.
Deleting an edge e keeps exactly the adjacencies whose endpoint pair
is not e.

| Member | Statement |
|---|---|
| `SimpleGraphOn` | `simple_graph_on(V, R) ⇔ symmetric_on(V, R) ∧ (∀v. v ∈ V ⇒ ¬R(v, v))` |
| `Symmetric` | a simple graph's adjacency is symmetric on V |
| `Loopless` | no vertex of a simple graph is adjacent to itself |
| `NeighboursDef` | `graph_neighbours(V, R, v) = {w \| w ∈ V ∧ R(v, w)}` |
| `DegreeDef` | `graph_degree(V, R, v) = card(graph_neighbours(V, R, v))` |
| `EdgesDef` | `graph_edges(V, R) = {e \| ∃u v. u ∈ V ∧ v ∈ V ∧ R(u, v) ∧ e = {u, v}}` |
| `DeleteEdgeDef` | `graph_delete_edge(R, e, x, y) ⇔ R(x, y) ∧ {x, y} ≠ e` |
| `ReachableDef` | `graph_reachable(V, R, u, v) ⇔ reflexive_transitive_closure(relation_on(V, R), u, v)` |
| `ConnectedDef` | `graph_connected(V, R) ⇔ ∀u v. u ∈ V ∧ v ∈ V ⇒ graph_reachable(V, R, u, v)` |
| `ComponentDef` | `graph_component(V, R, u) = equivalence_class(relation_on(V, graph_reachable(V, R)), u)` |
| `ComponentsDef` | `graph_components(V, R) = quotient_on(V, graph_reachable(V, R))` |

## Edges and degrees

The edges of a finite graph are subsets of the vertex set, so there
are finitely many; an edge on a subset of V is an edge on V. Pairing a
vertex with each of its neighbours bijects its neighbourhood with the
set of its incident edges, which needs only symmetry. Counting
incidences by vertices gives the sum of degrees, and counting them by
edges gives twice the number of edges; that second count needs every
edge to have two endpoints, so the handshake lemma asks for a simple
graph. The degree sum is even, so the number of vertices of odd degree
is even.

| Member | Statement |
|---|---|
| `EdgesSubset` | every edge is a subset of V |
| `EdgeSize` | every edge of a simple graph has two elements |
| `EdgesFinite` | a finite vertex set has finitely many edges |
| `EdgesMonotone` | an edge on a subset of V is an edge on V |
| `IncidentEdges` | for adjacency symmetric on V, w ↦ {v, w} is injective on the neighbours of v and maps them onto the edges containing v |
| `DegreeIncidence` | for adjacency symmetric on a finite V, the degree of v counts the edges containing it |
| `Handshake` | in a finite simple graph the degrees sum to twice the number of edges |
| `EvenOddDegreeCount` | a finite simple graph has an even number of vertices of odd degree |

## Connectivity

Symmetry of adjacency on V makes reachability an equivalence on the
vertex set; looplessness plays no part. So the components cover the
vertices and two components are equal or disjoint. A nonempty graph is
connected exactly when its only component is the whole vertex set, and
a connected nonempty graph without edges has one vertex. The component
of a vertex, taken as a graph of its own, is connected, and stays so
under any adjacency that keeps the original edges inside V.

| Member | Statement |
|---|---|
| `InComponent` | z lies in the component of u exactly when u and z are vertices and u reaches z |
| `ComponentInComponents` | the component of a vertex is one of the components |
| `AdjacentReachable` | an adjacency between vertices is a walk |
| `ReachableReflexive` | every point reaches itself |
| `ReachableTransitive` | two walks that meet make one: reachability is transitive |
| `ReachablePreserves` | walk induction: a property that every adjacency between vertices carries forward holds at the end of every walk that starts where it holds |
| `ReachableEquivalence` | for adjacency symmetric on V, reachability is an equivalence on V |
| `AdjacentInComponent` | adjacent vertices lie in a common component |
| `ComponentsPartition` | for adjacency symmetric on V, the components cover V, and two components are equal or disjoint |
| `ConnectedIffSingleComponent` | a nonempty graph is connected exactly when V is its only component |
| `ConnectedEdgelessSingleton` | a nonempty connected graph without edges has one vertex |
| `ConnectedCut` | in a connected graph, every nonempty proper subset S of the vertices has a vertex adjacent to a vertex outside S |
| `ConnectedVerticesFinite` | a connected graph with finitely many edges has finitely many vertices |
| `ComponentConnected` | for adjacency symmetric on V, the component of a vertex is connected under any adjacency that contains the graph's on V |

## Deleting an edge

Deleting an edge keeps adjacency symmetric. In a connected graph,
deleting the edge uv leaves it connected exactly when u still reaches
v. If it does not, the components of u and v in what is left partition
the vertex set, and uv is the only original edge between them. A
partition of a finite vertex set whose only crossing edge is uv splits
the vertices between its two sides and the edges between the two
induced subgraphs, all but uv.

| Member | Statement |
|---|---|
| `DeleteEdgeSymmetric` | deleting an edge keeps adjacency symmetric on V |
| `DeleteEdgeConnectedIff` | in a connected graph whose adjacency stays symmetric on V after deleting uv, the deletion leaves it connected exactly when u still reaches v |
| `BridgeComponents` | in a connected graph whose adjacency stays symmetric on V after deleting uv, if u no longer reaches v, the components of u and v partition V and uv is the only original edge between them |
| `BridgeCutCounts` | for adjacency symmetric on a finite V, a partition into U and W whose only crossing edge is uv gives card(V) = card(U) + card(W) and one edge more than U and W have between them |

## Trees

A tree is a nonempty connected simple graph from which deleting any
edge disconnects it: a structure whose four axioms say so
(`GraphTree`). Deleting an edge of a tree therefore leaves its
endpoints unreachable from each other, and a nonempty connected induced
subgraph of a tree is a tree. Cutting a finite tree at an edge uv
leaves the components of u and v as two trees on proper subsets of the
vertices: their vertex counts add up to the tree's, and their edge
counts add up to one less. Strong induction on the number of vertices
then counts the edges of a finite tree: one fewer than the vertices.

| Member | Statement |
|---|---|
| `GraphTree` | `graph_tree(V, R) ⇔ simple_graph_on(V, R) ∧ V ≠ ∅ ∧ graph_connected(V, R) ∧ (∀e. e ∈ graph_edges(V, R) ⇒ ¬graph_connected(V, graph_delete_edge(R, e)))` |
| `TreeSimple` | a tree is a simple graph |
| `TreeNonempty` | a tree has a vertex |
| `TreeConnected` | a tree is connected |
| `TreeEdgeDisconnects` | deleting any edge of a tree disconnects it |
| `TreeEdgeSeparates` | deleting an edge of a tree leaves its endpoints unreachable from each other |
| `ConnectedInducedSubtree` | a nonempty connected induced subgraph of a tree is a tree |
| `TreeSplitsAtEdge` | cutting a finite tree at an edge uv leaves the components of u and v as two trees on proper subsets of V, with card(V) = card(U) + card(W) and one edge more than U and W have between them |
| `TreeEdgeCount` | `card(graph_edges(V, R)) + 1 = card(V)` for a finite tree |
