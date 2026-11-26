# mixed_graph — mixed graphs of directed and bidirected edges: m-separation, districts and hedges

A mixed graph here is a vertex set with two edge relations: directed
edges D and bidirected edges B, a bidirected edge standing for a
hidden common cause of its ends. It is an acyclic directed mixed graph
(`AdmgOn`) when D is a DAG on the vertices and B is symmetric and
loop-free on them. Only that structure asks for acyclicity: the
augmented graph, m-separation and districts are defined for any two
relations. Mixed graphs arise here as the latent projections of DAGs
(`relations/graph/latent_projection`).

Separation in a mixed graph, m-separation, is defined as `d_separated`
is, with no paths: on the ancestors of the three groups, two vertices
are adjacent in the augmented graph when an edge of either kind joins
them or they are collider-connected there through bidirected edges,
and the augmented graph restricted outside the conditioning set must
not connect the two groups (`MSeparatedDef`, Richardson's criterion).

A district is a class of bidirected reachability inside a set; the
districts of a set partition it (`DistrictDef`, `DistrictsDef`). A
C-forest is a set that is one district of its own bidirected edges and
whose every vertex reaches a root set along its directed edges; two
C-forests with one root set, the smaller missing X and the larger
meeting it, with the roots among the ancestors of Y once the edges
into X are deleted, form a hedge for the effect of X on Y
(`CForestDef`, `HedgeDef`, Shpitser and Pearl's definitions with the
forests given by their vertex sets). The smaller forest can always
serve as the root set (`HedgeRootsWhole`). They are graph conditions, as the
back-door and front-door criteria are; the hedge criterion that reads
them is `causal/hedge_criterion`.

| Member | Statement |
|---|---|
| `AdmgOn` | `admg_on(V, D, B)`: D a DAG on V, B symmetric and loop-free on V |
| `AugmentedDef` | `mixed_graph_augmented(D, B, U, u, v)`: joined by an edge or collider-connected through bidirected edges in U |
| `MSeparatedDef` | `m_separated(D, B, X, Y, Z)`: on the D-ancestors U of X ∪ Y ∪ Z, the augmented graph on U ∖ Z connects no point of X to Y |
| `DistrictDef` | `mixed_graph_district(B, S, v)`: the vertices of S bidirected-reachable from v inside S |
| `DistrictsDef` | `mixed_graph_districts(B, S)`: the districts of the vertices of S |
| `CForestDef` | `mixed_graph_c_forest(D, B, F, R)`: R ⊆ F, F one district of its bidirected edges, every vertex of F reaching R inside F |
| `HedgeDef` | `mixed_graph_hedge(D, B, X, Y, F, F′)`: C-forests with one root set R, F′ ⊆ F, X meets F and misses F′, R among the ancestors of Y with X's in-edges deleted |
| `HedgeRootsWhole` | F and F′ form a hedge exactly when they do with F′ itself as the root set — card |
| `DistrictsPartition` | for symmetric B the districts of S partition S, finitely many when S is finite — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
