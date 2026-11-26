# simplicial_homotopy — combinatorial homotopies of simplicial maps, extra degeneracies and the diagonal of a bisimplicial set

A homotopy between two simplicial maps `F, G : X → Y`,
`simplicial_homotopy(X, Y, F, G, H)`, is written in
May's combinatorial form: for an n-simplex `x` and `j ≤ n`,
`H(n, j, x)` is an (n+1)-simplex of `Y`, with `d_0 h_0 = F`,
`d_{n+1} h_n = G` and five identities moving faces and degeneracies
past the `h_j`, each stated on the simplices of `X` with its index
bounds. This relates two maps. The `simplicial_homotopic` of
homotopy_group, which relates two simplices of one simplicial set at a
vertex, is a different notion. On a simplicial set that is not Kan,
homotopy of maps is neither symmetric nor transitive, so the chapter
also takes the equivalence relation it generates:
`simplicial_maps_homotopic(X, Y, F, G)` says that a finite zigzag of
homotopies, each step taken in either direction, joins `F` to `G`. A
simplicial homotopy equivalence is a simplicial map with an inverse up
to that relation on both sides. With this definition the direction of
each homotopy does not matter. Homotopies on free chains become chain
homotopies, and chain homotopy is itself symmetric and transitive, so
that is where the chapter's homotopies are used (simplicial_module).

An extra degeneracy of a simplicial set `X` augmented over a set `S` by
`ε` consists of maps `σ(n, ·) : X.simplices(n) → X.simplices(n + 1)`
and a bottom map `b : S → X.simplices(0)` standing for `σ` in
dimension −1. The predicate `extra_degeneracy(X, S, ε, σ, b)` holds:
- the closures;
- the face identities `d_0 σ = id` and `d_{i+1} σ = σ d_i`;
- the bottom identities `d_1 σ_0 = b ∘ ε` and `ε ∘ b = id`;
- the degeneracy identities `s_{j+1} σ = σ s_j` for `j ≥ 0`.

It does not hold the case `j = −1`, `s_0 σ = σσ`, and nothing in the
chapter needs it. That identity fails for the standard resolution's
`σ(u) = var(u) − var(0)` at every level, because `var` is not additive.
The face identities `d_{i+1} σ = σ d_i`, with the bottom identity
`d_1 σ_0 = b ∘ ε` and `ε ∘ b = id`, make `ε` coequalize the two vertices
of an edge; in a simplicial module the face identities carry a Moore
cycle to a Moore boundary (simplicial_module). The section from the constant simplicial
set on `S` is the degenerate one, `c ↦ base_simplex(X.s, b(c), n)`: the
vertex `b(c)` degenerated `n` times by `s_0`, simplicial by the
simplicial identities and inverted by `ε` of the last vertex. The
iterated extra degeneracy `σ^n(b(c))` would commute with `s_0` only
through `s_0 σ = σσ`. The contraction onto the section is
`h_j = s_0^j ∘ σ ∘ d_0^j`, a simplicial homotopy from the identity of
`X` to the section after the augmentation. Its `j` front degeneracies
absorb every `s_i` with `i ≤ j`, which is where the classical
contraction `σ^{j+1} ∘ d_0^j` would meet `s_0 σ`. So every extra
degeneracy makes the augmentation a simplicial homotopy equivalence of
`X` with the constant simplicial set on `S`. The contraction is
written with two recursions on `k`: the back face `d_0^k`,
simplicial_set's `face_iterate_bottom`, and the front degeneracy `s_0^k`,
`simplicial_front_degeneracy`, minted here.

A bisimplicial set has two directions of faces and degeneracies, held as
one value of the record `bisimplicial_ops(A)`,
`mk_bisimplicial(simplices, dh, sh, dv, sv)`: `X.simplices(p, q)` is the
set of (p, q)-simplices, `X.dh`, `X.sh` the horizontal faces and
degeneracies and `X.dv`, `X.sv` the vertical ones. In
`bisimplicial_set(X)` every row `bisimplicial_row(X, q)` and every
column `bisimplicial_column(X, p)` is a simplicial set, and each
horizontal map commutes with each vertical one. Its diagonal
`bisimplicial_diagonal(X)` takes the (n, n)-simplices, with faces
`dh_i ∘ dv_i` and degeneracies `sh_i ∘ sv_i`. The diagonal is a
simplicial set: in a composite of two diagonal maps the middle pair
commutes, and each identity of the diagonal is the same identity in a
row and in a column. A map of bisimplicial sets
restricts to the diagonals. A vertical homotopy that is natural in the
horizontal direction is a homotopy of the diagonals with components
`sh_j ∘ H(n, n, j)`. So two bisimplicial maps inverse to each other up
to such homotopies give a simplicial homotopy equivalence of the
diagonals.

The constant simplicial set on `S`, `constant_simplicial_set(S)`, with
`S` in every dimension and identity faces and degeneracies, is defined
in simplicial_set, which shows it a simplicial set.

## Homotopies and homotopy equivalences

| member | statement |
|---|---|
| `SimplicialHomotopy` | `simplicial_homotopy(X, Y, F, G, H)`: `F`, `G` simplicial maps, `H(n, j, x) ∈ Y.simplices(n + 1)`, `d_0 h_0 = F`, `d_{n+1} h_n = G` and May's identities on the simplices of `X` |
| `SimplicialMapsHomotopicDef` | `simplicial_maps_homotopic(X, Y, F, G)`: `F`, `G` simplicial maps joined by a zigzag `Φ(0) = F, …, Φ(k) = G` of homotopies taken in either direction |
| `SimplicialHomotopyEquivalenceDef` | `simplicial_homotopy_equivalence(X, Y, F)`: `F` simplicial with a simplicial `G` such that `G ∘ F` and `F ∘ G` are homotopic to the identities |
| `HomotopyTrivial` | a simplicial map is homotopic to itself through `H(n, j, x) = Y.s(n, j, F(n, x))` — card |
| `HomotopyComposeLeft`, `HomotopyComposeRight` | `K ∘ H` is a homotopy from `K ∘ F` to `K ∘ G`, and `H ∘ L` one from `F ∘ L` to `G ∘ L` — card |

## Extra degeneracies

| member | statement |
|---|---|
| `ExtraDegeneracy` | `extra_degeneracy(X, S, ε, σ, b)`: the closures, `ε ∘ b = id` on `S`, `d_1 σ_0 = b ∘ ε` on `X.simplices(0)`, `d_0 σ = id`, `d_{i+1} σ_{n+1} = σ_n d_i`, `s_{j+1} σ_n = σ_{n+1} s_j` |
| `SimplicialFrontDegeneracyDef` | `simplicial_front_degeneracy(s, n, k, x)`: `s_0` applied `k` times to the n-simplex `x`; from a vertex, its base simplex |
| `ExtraDegeneracyCoequalizes` | `ε(d_0 x) = ε(d_1 x)` for every edge `x` |
| `ExtraDegeneracySection` | `c ↦ base_simplex(X.s, b(c), n)` is a simplicial map from `constant_simplicial_set(S)` to `X`, and `ε` of its last vertex is `c` — card |
| `ExtraDegeneracyHomotopy` | `h_j = s_0^j ∘ σ ∘ d_0^j` is a simplicial homotopy from the identity of `X` to `x ↦ base_simplex(X.s, b(ε(last vertex of x)), n)` — card |
| `ExtraDegeneracyHomotopyEquivalence` | `x ↦ ε(last vertex of x)` is a simplicial homotopy equivalence from `X` to `constant_simplicial_set(S)` — card |

## Bisimplicial sets and the diagonal

| member | statement |
|---|---|
| `BisimplicialOps` | the record `bisimplicial_ops(A)`: `mk_bisimplicial(simplices, dh, sh, dv, sv)`, its parts read as the fields `X.simplices`, `X.dh`, `X.sh`, `X.dv` and `X.sv` |
| `BisimplicialRowDef`, `BisimplicialColumnDef` | `bisimplicial_row(X, q)`: the p-simplices `X.simplices(p, q)` with the horizontal faces and degeneracies; `bisimplicial_column(X, p)`: the q-simplices `X.simplices(p, q)` with the vertical ones |
| `BisimplicialSet` | `bisimplicial_set(X)`: every row and every column a simplicial set, horizontal and vertical maps commuting |
| `BisimplicialRows`, `BisimplicialColumns` | every row `bisimplicial_row(X, q)` and every column `bisimplicial_column(X, p)` of a bisimplicial set is a simplicial set |
| `HorizontalFaceVerticalFace`, `HorizontalFaceVerticalDegeneracy`, `HorizontalDegeneracyVerticalFace`, `HorizontalDegeneracyVerticalDegeneracy` | each horizontal face or degeneracy commutes with each vertical face or degeneracy, on the simplices where both composites are read |
| `BisimplicialMap` | `bisimplicial_map(X, Y, F)`: `F(p, q)` carries `X.simplices(p, q)` into `Y.simplices(p, q)` and commutes with the four kinds of map |
| `ColumnFaceIterateBottomIn` | the 0-th vertical face taken `k ≤ q` times carries `X.simplices(p, q)` into `X.simplices(p, q − k)` |
| `RowFaceIterateTopIn` | the last horizontal face taken `k ≤ p` times carries `X.simplices(p, q)` into `X.simplices(p − k, q)` |
| `ColumnFaceIterateBottomHorizontalFace` | a horizontal face passes the 0-th vertical faces taken `k ≤ q` times: on `X.simplices(p + 1, q)`, removing them after `X.dh(p + 1, q, i)` is `X.dh(p + 1, q − k, i)` after removing them |
| `RowFaceIterateTopVerticalFace` | a vertical face passes the last horizontal faces taken `k ≤ p` times: on `X.simplices(p, q + 1)`, removing them after `X.dv(p, q + 1, j)` is `X.dv(p − k, q + 1, j)` after removing them |
| `BisimplicialDiagonalSimplicesDef` | `bisimplicial_diagonal_simplices(X, n) = X.simplices(n, n)` |
| `BisimplicialDiagonalFaceDef` | `bisimplicial_diagonal_face(dh, dv, n, i, x) = dh(n, n − 1, i, dv(n, n, i, x))` |
| `BisimplicialDiagonalDegeneracyDef` | `bisimplicial_diagonal_degeneracy(sh, sv, n, i, x) = sh(n, n + 1, i, sv(n, n, i, x))` |
| `BisimplicialDiagonalDef` | `bisimplicial_diagonal(X) = mk_simplicial(bisimplicial_diagonal_simplices(X), bisimplicial_diagonal_face(X.dh, X.dv), bisimplicial_diagonal_degeneracy(X.sh, X.sv))` |
| `BisimplicialVerticalHomotopy` | `bisimplicial_vertical_homotopy(X, Y, F, G, H)`: on each column a simplicial homotopy from `F` to `G`, commuting with the horizontal faces and degeneracies |
| `DiagonalSimplicialSet` | the diagonal of a bisimplicial set is a simplicial set, `simplicial_set(bisimplicial_diagonal(X))` |
| `DiagonalMap` | a bisimplicial map restricts to a simplicial map of the diagonals — card |
| `DiagonalHomotopy` | a natural vertical homotopy from `F` to `G` gives the homotopy `λn j x. Y.sh(n, n + 1, j, H(n, n, j, x))` of the diagonals — card |
| `DiagonalHomotopyEquivalence` | bisimplicial maps inverse up to natural vertical homotopies from the identities give a simplicial homotopy equivalence of the diagonals — card |
