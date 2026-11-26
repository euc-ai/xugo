# d_connection — open paths, Pearl's reading of separation in a DAG

A path of a DAG is a list of distinct vertices, each joined to the next
by an edge in either direction. Given a set Z, an interior vertex b of
the path, between a and c, is a collider when both edges point into it;
the path is open when every collider is an ancestor of Z — itself in Z
or with a descendant there — and every other interior vertex is not in Z
(`OpenPathDef`). Separation, defined in `relations/graph/d_separation`
on the moral graph of an ancestral set with no paths, is exactly the
absence of an open path from X to Y (`DConnectionIff`). This is the
reading the literature gives first; in the corpus it is a theorem about
the path-free definition, which the rules and the identification
chapter read.

| Member | Statement |
|---|---|
| `OpenPathDef` | `d_open_path(E, Z, p)`: distinct vertices, consecutive ones adjacent, each collider an ancestor of Z and each other interior vertex outside Z |
| `DConnectionIff` | on a DAG, Z separates X from Y exactly when no path from X to Y is open given Z — card |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
