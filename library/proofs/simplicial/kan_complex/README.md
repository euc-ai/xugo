# kan_complex — the Kan condition in its combinatorial form, and the first Kan complexes and non-examples

A horn of dimension `n + 1` with the `k`-th face missing is a family
`y : num → A` of n-simplices on the faces `horn_faces(n, k)` — the
indices `i ≤ n + 1` other than `k` — whose faces match as the faces of
an (n+1)-simplex do, `X.d(n, i, y(j)) = X.d(n, j − 1, y(i))` for `i < j`: a
face family `face_family(n, horn_faces(n, k), y)` of the simplicial-set
chapter. A filler is an (n+1)-simplex with those faces,
`faces_filler(n, horn_faces(n, k), y, x)`. A Kan complex is a simplicial set in
which every horn, for every `k ≤ n + 1`, has a filler,
`kan_complex(X)`. The condition is stated on the simplices
rather than on maps of the horn `Λⁿₖ` into `X`: the map form needs the
action of an arbitrary monotone map on the simplices, which the corpus
does not build, and the combinatorial form is what every argument of
the homotopy chapters uses.

The faces of a simplex are a compatible family with the simplex as a
filler; a one-dimensional horn is one vertex and is filled by its
degeneracy in any simplicial set, so the condition begins at the
two-dimensional horns; the point is a Kan complex; and no standard
simplex of positive dimension is one, since the horn `Λ²₀` made of the
degenerate edge at 0 and the edge from 0 to 1 would need a 2-simplex
`0 ≤ 1 ≤ 0`.

## The Kan condition

| member | statement |
|---|---|
| `HornFacesDef` | `horn_faces(n, k) = {i \| i ≤ n + 1 ∧ i ≠ k}`, the faces of the horn `Λⁿ⁺¹ₖ` |
| `HornFacesMember` | `i ∈ horn_faces(n, k)` ⇔ `i ≤ n + 1 ∧ i ≠ k` |
| `KanComplex` | `kan_complex(X)` ⇔ a simplicial set in which every face family on `horn_faces(n, k)` in `X.simplices(n)`, `k ≤ n + 1`, has a filler in `X.simplices(n + 1)` — a structure |
| `KanSimplicialSet`, `KanFill` | its two axioms |
| `CommonSourceTriangle` | two edges out of one vertex are the faces 1 and 2 of a triangle: the horn `Λ²₀` fills |
| `CommonTargetTriangle` | two edges into one vertex are the faces 0 and 1 of a triangle: the horn `Λ²₂` fills |

## Examples and non-examples

| member | statement |
|---|---|
| `FacesCompatible` | the faces of a simplex are a compatible family on the faces `horn_faces(n, k)` of every horn with `k ≤ n + 1`: a horn of dimension one has no pair of faces both other than `k`, and above it the face identity holds |
| `MapHorn` | a simplicial map carries a horn of X to a horn of Y: the images of a face family of X on `horn_faces(n, k)` are a face family of Y there — they lie in `Y.simplices(n)`, and a matching pair of faces of `y` goes to a matching pair of faces of the images, since the map commutes with the faces |
| `SimplexFillsOwnHorn` | a simplex fills the horn of its own faces, for every `k` |
| `OneDimensionalHornFill` | a one-dimensional horn is filled by the degeneracy of its vertex, in any simplicial set: the one face of the horn is `1 − k`, and both faces of `X.s(0, 0, y(1 − k))` are `y(1 − k)` |
| `KanPoint` | the point is a Kan complex, `kan_complex(simplicial_point(a))`: it is a simplicial set, and its one simplex `a` fills every horn, every member of a horn being `a` |
| `StandardSimplexNotKan` | `Δⁿ` is not a Kan complex for `1 ≤ n`, `¬kan_complex(standard_simplex(n))`: the horn `Λ²₀` with the edge from 0 to 1 at index 2 and the degenerate edge at 0 at index 1 is compatible, and a filler `w` would have `w(1) = 1` and `w(2) = 0`, against monotonicity |

## The opposite

| member | statement |
|---|---|
| `HornFamilyOpposite` | for `k ≤ n + 1`, `y` is a face family of the opposite `opposite_simplicial_set(X)` on `horn_faces(n, k)` exactly when its reversal `i ↦ y(n + 1 − i)` is a face family of `X` on `horn_faces(n, n + 1 − k)`: a horn of the opposite missing the face `k` is, reversed, a horn of `X` missing the face `n + 1 − k` |
| `HornFillerOpposite` | for `k ≤ n + 1`, an (n+1)-simplex fills the family `y` on `horn_faces(n, k)` under the opposite's faces exactly when it fills its reversal on `horn_faces(n, n + 1 − k)` in `X`: its face `i` in the opposite is its face `n + 1 − i` in `X` |
| `HornFamilyReversed` | for `k ≤ n + 1`, `y` is a face family of `X` on `horn_faces(n, k)` exactly when its reversal is a face family of the opposite on `horn_faces(n, n + 1 − k)`: the same equations read from the other side, `y` itself rather than reversed twice |
| `HornFillerReversed` | for `k ≤ n + 1`, an (n+1)-simplex fills the family `y` on `horn_faces(n, k)` in `X` exactly when it fills its reversal on `horn_faces(n, n + 1 − k)` under the opposite's faces |
| `OppositeKan` | a Kan complex read in the opposite order is a Kan complex, `kan_complex(opposite_simplicial_set(X))`: a horn of the opposite, reversed, is a horn of `X`, filled there, and the filler read back |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
