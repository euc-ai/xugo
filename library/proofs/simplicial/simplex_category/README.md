# simplex_category — the simplex category Δ, its objects the natural numbers and its morphisms the monotone maps

The simplex category has an object `[n]` for every natural number, the
ordered set `0, …, n`, and for morphisms from `[m]` to `[n]` the
monotone maps. The corpus already holds these maps: the `m`-simplices
of the standard simplex `Δⁿ` are the monotone sequences `num → num`
into `0 .. n` padded with zero past `m`, `standard_simplex_simplices(n, m)`
(`simplicial_set`), and the padding is the normalization of a map off
`0 .. m` (`functions.normalize_on`). So the hom set `Δ([m], [n])` is
`standard_simplex_simplices(n, m)`, the identity of `[n]` is the identity map
normalized off `0 .. n`, and a composite is the composite of maps
normalized again, since past `l` the inner map is zero and the outer
map need not vanish at zero. The category is assembled from this hom
data (`category.CategoryFromHom`), and its laws are the laws of
composition of maps read on `0 .. l`.

The coface `δⁱ` skips the value `i` and the codegeneracy `σʲ` repeats
the value `j`; the standard simplex acts by precomposition, its faces
and degeneracies being precomposition with them. Every monotone map
is the composite of the cofaces at the values it misses after the
codegeneracies at the positions where it repeats, both lists ascending,
and a factorization by ascending lists within their dimensions is that
one. The ordered set `[n]` is a category, and `Δⁿ` is its nerve.

What Δ is for is stated in `simplicial_operator`: the action of a
monotone map on the simplices of a simplicial set.

## The category

| member | statement |
|---|---|
| `SimplexCategoryDef` | `simplex_category`: `category_from_hom` at the natural numbers, the hom sets `standard_simplex_simplices(n, m)`, the normalized identity and the normalized composite |
| `SimplexCategory` | `category(simplex_category)` — card |

## The generators

| member | statement |
|---|---|
| `CofaceDef`, `CodegeneracyDef` | `coface(i)`: skip the value `i`; `codegeneracy(j)`: repeat the value `j` |
| `CofaceMapDef`, `CodegeneracyMapDef` | `coface_map(n, i): [n] → [n + 1]`; `codegeneracy_map(n, j): [n + 1] → [n]` |
| `SimplexFaceCoface`, `SimplexDegeneracyCodegeneracy` | `simplex_face(i, f) = f ∘ coface(i)`; `simplex_degeneracy(j, f) = f ∘ codegeneracy(j)` — card |
| `CofaceMorphism`, `CodegeneracyMorphism` | the cofaces, and the codegeneracies within their dimension, are morphisms of Δ — card |
| `OrdinalCategoryDef` | `ordinal_category(n)`: `0 .. n` ordered by `≤`, a category |
| `StandardSimplexNerve` | `Δⁿ` is the nerve of `[n]`, `simplicial_isomorphism(standard_simplex(n), nerve(ordinal_category(n)), …)`: a monotone sequence goes to the chain of its steps — card |

## The canonical factorization

| member | statement |
|---|---|
| `CofaceIndicesDef`, `CodegeneracyIndicesDef` | the values a monotone map misses, and the positions where it repeats, ascending |
| `CofaceCompositeDef`, `CodegeneracyCompositeDef` | the composites of the cofaces and of the codegeneracies at an ascending list |
| `CanonicalFactorization` | a monotone map is the cofaces at its missed values after the codegeneracies at its repeats — card |
| `FactorizationUnique` | a factorization by ascending lists within their dimensions is the canonical one — card |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
