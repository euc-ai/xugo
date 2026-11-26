# segal — spines, the category of a simplicial set with unique inner fillers, and Segal's characterization of the nerves

The spines of a simplicial set, `simplex_spine` and `spine_map`, are
`simplicial_set`'s, and the spine of a chain of the nerve is the
`nerve` family's (`NerveSpine`). A simplicial set with unique inner
fillers is a category on its vertices and edges, composing through the
middle face of the unique filler of `Λ²₁`: any 2-simplex's middle face
is the Segal composite of its other two (`segal_composite`, defined in
`quasi_category`). Its spine map, the chain of
spine edges of a simplex, lands in the nerve of that category,
commutes with the faces and the degeneracies, is one-to-one in every
dimension and onto the nerve, so it is an isomorphism. The nerve of a
category has unique inner fillers (`NerveInnerHornUnique`), so a
simplicial set has unique inner fillers exactly when it is isomorphic
to the nerve of a category.

## Unique inner fillers: the category of vertices and edges

| member | statement |
|---|---|
| `SegalCompositeMiddleFace` | with unique inner fillers the middle face of a 2-simplex is the Segal composite of its other two faces, `X.d(2, 1, w) = segal_composite(X.d(2, 0, w), X.d(2, 2, w))` — the composition law the category below reads |
| `SegalCategoryDef` | `segal_category(X)`: the record of the category of vertices and edges — the ends of an edge its faces 1 and 0, the identity at a vertex its degenerate edge, composition the Segal composite |
| `SegalCategory` | with unique inner fillers the vertices and edges form a category, `category(segal_category(X))`: the identity at a vertex is its degenerate edge (`simplicial_set.VertexDegeneracyFaces`), and g after f the middle face of any 2-simplex with f and g as its faces 2 and 0 (`SegalCompositeMiddleFace`), an edge from the source of f to the target of g (`simplicial_set.TwoSimplexFaceEnds`) |

## The spine map, and Segal's characterization

| member | statement |
|---|---|
| `SpineMapIn` | the spine map lands in the nerve: the spine of an n-simplex is a chain of n composable edges, padded by the degenerate edge at its last vertex (`simplicial_set.VertexDegeneracyFaces`) |
| `FaceSpineComposite` | with unique inner fillers, at the deleted vertex of an inner face its spine edge is the composite of the two spine edges of `x` meeting there |
| `SpineMapFace` | with unique inner fillers the spine map commutes with the faces |
| `SpineMapDegeneracy` | the spine map commutes with the degeneracies — card |
| `SpineMapInjective`, `SpineMapOnto` | with unique inner fillers a simplex is determined by its spine, and every chain of composable edges is a spine — card |
| `SegalIsomorphism` | with unique inner fillers the spine map is an isomorphism onto the nerve of the category of vertices and edges, `simplicial_isomorphism(X, nerve(segal_category(X)), spine_map)` |
| `SegalCharacterization` | `inner_horn_unique(X)` ⇔ `X` is isomorphic to the nerve of a category, `simplicial_isomorphism(X, nerve(C), F)` — card |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
