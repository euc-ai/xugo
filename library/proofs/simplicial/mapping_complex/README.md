# mapping_complex — the left mapping complex between two vertices of a simplicial set, a Kan complex in a quasi-category, whose components are the morphisms of the homotopy category

The left mapping complex `mapping_complex(X, x, y)` between two
vertices `x` and `y` of a simplicial set `X` is a simplicial set on the
type of `X`. It has for n-simplices the (n + 1)-simplices of `X` whose
vertex 0 is `x` and whose face opposite vertex 0 is the n-simplex
degenerate at `y`, with the faces and degeneracies of `X` shifted past
vertex 0 — Lurie's `Hom^L(x, y)`. Its vertices are the edges from `x` to
`y`, and an edge between two of them is exactly a homotopy of edges as
`quasi_category` states it, so its classes of vertices are the
morphisms from `x` to `y` of the homotopy category.

In a quasi-category the mapping complex is a Kan complex. A horn of it,
with the degenerate face added, is a horn of `X` one dimension up: inner
except when it misses the last face, and then its last edge lies in the
degenerate face and is the degenerate edge at `y`, an equivalence, so
the horn fills by Joyal's lifting (`quasi_category.RightSpecialHornFill`).
No slice or fibration theory is needed.

| member | statement |
|---|---|
| `mappingComplexSimplicesDef` | `mapping_complex_simplices(X, x, y, n)`: the (n + 1)-simplices of `X` with vertex 0 at `x` and the face opposite it degenerate at `y` |
| `mappingComplexFaceDef`, `mappingComplexDegeneracyDef` | the faces and degeneracies of `X` past vertex 0 |
| `MappingComplexDef` | `mapping_complex(X, x, y) = mk_simplicial(mapping_complex_simplices(X, x, y), mapping_complex_face(X.d), mapping_complex_degeneracy(X.s))` |
| `MappingComplexSimplicialSet` | from any `x` to a vertex `y`, the mapping complex is a simplicial set, `simplicial_set(mapping_complex(X, x, y))` |
| `MappingComplexVertices` | its vertices are the edges from `x` to `y` — card |
| `MappingComplexEdges` | an edge of it from `f` to `g` is a homotopy from `f` to `g` — card |
| `MappingComplexKan` | in a quasi-category it is a Kan complex, `kan_complex(mapping_complex(X, x, y))` |
| `MappingComplexComponents` | the morphisms from `x` to `y` of the homotopy category are the classes of its vertices — card |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
