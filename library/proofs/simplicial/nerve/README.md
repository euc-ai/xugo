# nerve — the nerve of a category and unique inner fillers

The nerve of a category `C`, a record of objects and morphisms, is the
simplicial set `nerve(C)`, one value of `simplicial_ops(num → M)`. It
has for n-simplices the chains of `n` composable morphisms,
`nerve_simplices(C, n)`: a sequence `num → M` whose terms up to
`n` are morphisms, each composable with the next, whose n-th term is
the identity at the end of the chain, and which is constant from `n`
on — the padding of the standard simplices, with the identity for its
zero; at `n = 0` the constant identity chain at an object. The 0-th
face drops the first morphism, the n-th drops the last and re-pads
with the identity at its source, an inner face composes two
neighbours; a degeneracy inserts the identity at the source of a
morphism. The eight axioms of a simplicial set are then the unit and
associativity laws of the category read at the places where a face
composes, and a functor induces a simplicial map, its map of morphisms
applied termwise. The vertices of the nerve are the objects and its
edges the morphisms.

Maps into a nerve are decided on vertices, edges and 2-simplices, so the
functors between two categories are the simplicial maps between their
nerves.

A simplicial set has unique inner fillers, `inner_horn_unique(X)`,
when every inner horn has exactly one filler; the nerve of a category
has them, since an inner horn determines every morphism of the chain.
Segal's characterization of the nerves among the simplicial sets is
the `segal` family's.

## The nerve of a category

| member | statement |
|---|---|
| `NerveSimplicesDef` | `nerve_simplices(C, n)` = the chains of `n` composable morphisms, padded with the identity at the end |
| `NerveFaceDef`, `NerveDegeneracyDef` | the faces drop, re-pad or compose; the degeneracies insert an identity |
| `NerveDef` | `nerve(C) = mk_simplicial(nerve_simplices(C), nerve_face(C), λn. nerve_degeneracy(C))` |
| `NerveFaceIn` | a face of a chain of length `n + 1` is a chain of length `n` |
| `NerveDegeneracyIn` | a degeneracy of a chain of length `n` is a chain of length `n + 1` |
| `NerveFaceFace` | the face identity on chains, from the associativity law |
| `NerveDegeneracyDegeneracy` | the identity for two degeneracies |
| `NerveFaceDegeneracyBelow` | a face below an insertion shifts that insertion down one place, on every sequence |
| `NerveFaceDegeneracyAbove` | a face above an insertion keeps it in place and shifts its own index down one |
| `NerveFaceDegeneracyEqual` | `d_i s_i = id`, by the left unit law |
| `NerveFaceDegeneracyNext` | `d_{i+1} s_i = id`, by the right unit law and terminal identity padding |
| `NerveSimplicialSet` | `simplicial_set(nerve(C))` |
| `NerveVertex`, `NerveEdge` | the vertices are the constant identity chains; the edges the morphisms followed by the identity at their target |
| `NerveFunctor` | a functor `F` induces a simplicial map of the nerves, `simplicial_map(nerve(C), nerve(D), λn f j. F.map(f(j)))` — card |
| `NerveSpine` | the spine of a chain is the chain: its i-th spine edge is the edge of its i-th morphism — card |
| `NerveOuterFacesDetermine` | a sequence is determined, at length `m ≥ 2`, by its 0-th and last nerve faces: the 0-th face is the sequence one index up, and the last face begins with its first term |

## Unique inner fillers

| member | statement |
|---|---|
| `InnerHornUnique` | `inner_horn_unique(X)` ⇔ a simplicial set in which every inner horn has exactly one filler — a structure |
| `UniqueInnerSimplicialSet`, `UniqueInnerFill` | its two axioms |
| `NerveInnerHornUnique` | the nerve of a category has unique inner fillers, `inner_horn_unique(nerve(C))`: a chain of length at least 2 is determined by its 0-th and last faces (`NerveOuterFacesDetermine`), and the chain beginning with the first morphism of `y(n + 1)` and going on as `y(0)` is a filler |

## Maps into a nerve

A simplicial map into the nerve of a category is decided in low
dimensions: a map of vertices to objects and edges to morphisms keeping
the ends and the degenerate edges and sending every 2-simplex to a
commuting triangle extends to exactly one simplicial map, a simplex
sent to the chain of its spine edges. At a nerve the conditions are the
functor laws, so the nerve is full and faithful.

| member | statement |
|---|---|
| `NerveMapDef` | `nerve_map(C, F)`: the map of nerves a functor induces, normalized |
| `NerveMapCriterion` | a map of vertices and edges keeping ends and degenerate edges and sending 2-simplices to commuting triangles extends to exactly one simplicial map into the nerve — card |
| `NerveFullyFaithful` | `nerve_map(C)` is a bijection from the normalized functors `C → D` onto `simplicial_map_set(nerve(C), nerve(D))`, the simplicial maps between the nerves — card |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
