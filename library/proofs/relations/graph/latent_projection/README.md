# latent_projection — the latent projection of a DAG onto its observed vertices

A DAG with unobserved vertices is read on its observed ones through
the latent projection: an observed a points to an observed b when a
reaches b through unobserved vertices only, and two observed vertices
are joined by a bidirected edge when an unobserved common cause
reaches both through unobserved vertices only (`LatentDirectedDef`,
`LatentBidirectedDef`). The projection is an acyclic directed mixed
graph (`LatentProjectionAdmg`, on `relations/graph/mixed_graph`'s
`AdmgOn`). Deleting unobserved vertices outright is not the
projection: a hidden common cause would vanish with them.

On observed groups, d-separation in the DAG is m-separation in the
projection (`LatentProjectionSeparation`), so the identification
chapter states its graph conditions on the projection and the
derivation rules read them in the DAG. Projecting commutes with
restricting to an ancestral set and with removing observed vertices,
the two subgraphs ID's recursion enters. In a district of the
projection, a vertex is separated in the DAG from its predecessors
outside the district by those inside it, the edges out of the outside
ones deleted (`DistrictPredecessorSeparation`); the district lines of
ID read it.

| Member | Statement |
|---|---|
| `LatentReachDef` | `latent_reach(E, O, u, v)`: v reached from u along a directed path with interior outside O |
| `LatentDirectedDef` | `latent_proj_directed(E, O, a, b) ⇔ a ∈ O ∧ b ∈ O ∧ latent_reach(E, O, a, b)` |
| `LatentBidirectedDef` | `latent_proj_bidirected(E, O, a, b)`: distinct observed a, b with an unobserved l latently reaching both |
| `LatentProjectionAdmg` | the latent projection of a DAG is an acyclic directed mixed graph — card |
| `LatentProjectionSeparation` | on observed groups, d-separation in the DAG is m-separation in the projection — card |
| `LatentProjectionAncestors` | ancestors in the projection are the observed DAG ancestors — card |
| `LatentProjectionAncestral` | projecting the restriction to an ancestral set is restricting the projection — card |
| `LatentProjectionRemove` | projecting after removing observed vertices is removing them from the projection — card |
| `DistrictPredecessorSeparation` | in a district S, v is separated from its predecessors outside S by those inside, their out-edges deleted — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
