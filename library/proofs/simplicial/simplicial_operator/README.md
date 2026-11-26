# simplicial_operator — the action of a monotone map on the simplices, the simplices as maps out of the standard simplices, and horns as maps out of the standard horns

A monotone map `θ: [m] → [n]` acts on the simplices of a simplicial set.
`θ` factors canonically into cofaces after codegeneracies
(`simplex_category.CanonicalFactorization`), and its action on an
n-simplex is the faces at the values `θ` misses, the largest first,
followed by the degeneracies at the positions where it repeats, the
smallest first: two folds over the two canonical index lists, each
carrying the dimension beside the simplex. A coface acts as the face,
a codegeneracy as the degeneracy, the identity as the identity, and on
the standard simplex the action is precomposition.

The law that the action is contravariantly functorial is where the
difficulty sits, and it is split in two: composing a monotone map on the
right with one coface, or with one codegeneracy, acts as the face, or
the degeneracy, after the map's action. Those two laws use the
simplicial identities of `X`, and the general law follows by
induction along the canonical factorization.

The simplicial maps are the families that commute with every operator.
An n-simplex names the map from the standard simplex `Δⁿ` sending `θ`
to its action, and every map from `Δⁿ` is named by its value at the
identity: the Yoneda argument at `Δ`. A compatible family of faces
glues to a map out of the standard horn — a simplex missing some vertex
factors through the coface there, and compatibility is exactly what
makes the choice of vertex not matter — every map out of the horn is
one, and it extends to `Δⁿ⁺¹` exactly when the family has a filler. So
the Kan condition, the quasi-category condition and unique inner filling
are conditions on extending maps out of horns.

## The action of a monotone map

| member | statement |
|---|---|
| `SimplicialOperatorDef` | `simplicial_operator(d, s, t, x)`: the faces at the missed values, then the degeneracies at the repeats, folded with the dimension |
| `SimplicialOperatorIn` | `θ: [m] → [n]` carries an n-simplex to an m-simplex — card |
| `SimplicialOperatorCoface`, `SimplicialOperatorCodegeneracy`, `SimplicialOperatorIdentity` | a coface acts as the face, a codegeneracy as the degeneracy, the identity as the identity — card |
| `OperatorRightCoface`, `OperatorRightCodegeneracy` | `θ ∘ δⁱ` acts as `d_i` after `θ`, and `θ ∘ σʲ` as `s_j` after `θ` — card |
| `SimplicialOperatorCompose` | the action of `u ∘ t` is the action of `t` after that of `u` — card |
| `StandardSimplexOperator` | on the standard simplex the action is precomposition — card |

## Maps and the operators

| member | statement |
|---|---|
| `SimplicialMapIffOperatorNatural` | a family of maps is simplicial ⇔ it commutes with every operator — card |
| `simplexYonedaMapDef` | `simplex_yoneda_map(d, s, n, x)`: the map from `Δⁿ` that `x` names |
| `SimplexYoneda` | the n-simplices are the maps from `Δⁿ`: `x` names its map, a map is named by its value at the identity — card |

## Horns as maps

| member | statement |
|---|---|
| `hornFamilyMapDef` | `horn_family_map(d, s, n, k, y)`: the map out of `Λⁿ⁺¹ₖ` a family of faces gives |
| `HornMapIffCompatibleFaces` | the maps out of a standard horn are the compatible families of faces — card |
| `HornExtensionIffFiller` | the map of a family extends to `Δⁿ⁺¹` ⇔ the family has a filler — card |
| `KanIffHornExtension`, `QuasiIffInnerHornExtension`, `InnerHornUniqueIffUniqueExtension` | the Kan condition, the quasi-category condition and unique inner filling as extension of maps out of horns — card |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
