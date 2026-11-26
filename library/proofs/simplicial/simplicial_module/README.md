# simplicial_module — simplicial and bisimplicial modules, the alternating face complex, the Moore complex, the Alexander–Whitney map and the free chains on a simplicial set

A simplicial module over a ring `R` is a simplicial set `M`,
`simplicial_module(R, V, M)`, whose n-simplices `M.simplices(n)` form a
submodule of one ambient module `V`, with faces and degeneracies that
are homomorphisms of the modules cut out of `V`. So a face or a
degeneracy carries sums to sums and keeps zero, a face carries
differences to differences, and by the simplicial identities a
degeneracy carries a zero face to a zero face on either side of its
index; Moore's horn filling reads these. Since every dimension lives in
the one module, every complex built from a simplicial module is a
`complex_ops` over `V`'s operations, and only the carriers vary with the
degree. The alternating face complex `face_complex(R, V, M)` has
`M.simplices(n)` as its terms and the face boundary $\sum_{i \le n} (-1)^i • M.d(n, i, x)$
as its differential. It is a chain complex, by the
double-sum cancellation that simplicial_chain proves for free modules,
here in any module. A linear simplicial map is a chain map. A linear
simplicial homotopy `H` gives the chain homotopy $\sum_{j \le n} (-1)^j H(n, j)$.
Simplicial maps that are short exact in every dimension give a
short exact sequence of face complexes. A constant simplicial module has
its homology in degree 0.

The Moore complex keeps the simplices all of whose faces but the 0-th
vanish, `moore_terms(V, M, n)`, with `d_0` as its differential. Its
cycles and boundaries are chain_complex's `cycles` and `boundaries` of
the record `moore_complex(V, M)`. A simplicial module is a Kan
complex: Moore's construction fills every horn using only the additive
group. The Moore complex carries the acyclicity of an augmentation and
the homotopy groups; the face complex carries every complex of chains
and of differentials. The two are never compared: the normalization
theorem, that they have one homology, is not stated, and a simplicial
homotopy gives a chain homotopy of face complexes directly.

A compatible sphere of (n+1)-simplices has a simplex filling every face
but the 0-th, and the defect left at face 0 is a Moore cycle. If that
cycle is a Moore boundary, the sphere fills. So in an acyclic
augmentation every positive sphere fills. In degree 0, two vertices
with one image under the augmentation are the two faces of an edge.

`acyclic_augmentation(R, V, M, N, ε)` says three things:
- the Moore complex has cycles equal to boundaries in every positive degree;
- `ε` carries `M.simplices(0)` onto `N`;
- two vertices have one image under `ε` exactly when their difference is a Moore boundary.

This is the definition a resolution stands on. A simplicial homotopy `h`
from the identity to a section `ι` after the augmentation of the last
vertex provides one, once the augmentation is linear on
`M.simplices(0)`, `ι` in degree 0 is a section of it, and `h` keeps zero
(`ι` then keeps zero as well, $d_{n+1} h_n(0) = \iota(n, \varepsilon(0))$). They are
maps of sets: on a Moore cycle `x`, every face of which is zero, the
alternating sum `Σ_j (−1)^j h_j(x)` is a Moore term with `x` as its 0-th
face, the inner terms of each face cancelling in pairs and the outer
ones vanishing at zero, so no additivity is needed. An extra degeneracy
keeping zero gives such a homotopy, `h_j = s_0^j σ d_0^j` onto the
degenerate section `s_0^n b`. The standard resolution's `σ` is not
additive, and this is the route it takes; so does the diagonal of the
relative standard resolution, which has a contraction keeping zero and
no extra degeneracy of its own.

A bisimplicial module `bisimplicial_module(R, V, D)` is a bisimplicial
set whose every row and every column is a simplicial module in one
ambient module. The alternating
face sums of the two directions form a double complex, and the
Alexander–Whitney map carries the face complex of the diagonal, whose
faces are `dh_i ∘ dv_i`, into its total complex: an (n, n)-simplex `x`
goes to the diagonal whose coordinate `p` is the front horizontal
p-face of the back vertical (n − p)-face of `x`. Against
`double_total`'s boundary `h + alternating_sign(p) • v` it is a chain
map with no sign of its own, and it is natural in linear maps of
bisimplicial modules. When every vertical face is the identity its
coordinate n, in bidegree (n, 0), is `x`, and when every horizontal face
is, its coordinate 0, in bidegree (0, n): it is then a section of the
edge that reads that coordinate, so on homology the inverse of an edge
that is a quasi-isomorphism. Only this half of the
Eilenberg–Zilber theorem is stated.

The chains on a simplicial set over a commutative ring are the free
complex on its simplices,
`free_complex(R, X.simplices, simplicial_boundary(…))`. A map of
simplices acts on them by its pushforward. With the pushforwards of the
faces and degeneracies, the chains form a simplicial module,
`free_simplicial_module(R, X)`, and its face complex has the boundary of
the alternating face map complex, so the two have one homology. A
simplicial homotopy then gives a chain homotopy of the chains. The
equivalence relation the homotopies generate gives chain homotopic
pushforwards, and a simplicial homotopy equivalence gives a chain
homotopy equivalence, chain_complex's `chain_homotopy_equivalence`, with
the pushforward of an inverse as its inverse. The chains on a constant
simplicial set have the free module on the set as `H_0` and nothing
above. This bridge to the free chains lives here rather than in
simplicial_chain: this chapter reads simplicial_chain
(AlternatingDoubleSumCancel follows its FaceSumCancel), so
simplicial_chain cannot read this chapter back.

## Simplicial modules and the face complex

| member | statement |
|---|---|
| `SimplicialModule` | `simplicial_module(R, V, M)`: `module_on(R, V)`, each `M.simplices(n)` a submodule of `V`, `simplicial_set(M)`, every face and degeneracy linear between the modules `M.simplices(n)` |
| `AmbientModule` | `module_on(R, V)` |
| `SimplicesSubmodule` | each `M.simplices(n)` is a submodule of `V` |
| `ModuleSimplicialSet` | `simplicial_set(M)` |
| `FaceHom` | every face `M.d(n + 1, i)` is a homomorphism `M.simplices(n + 1) → M.simplices(n)` |
| `DegeneracyHom` | every degeneracy `M.s(n, i)` is a homomorphism `M.simplices(n) → M.simplices(n + 1)` |
| `SimplicesModule` | each `restrict_module(V, M.simplices(n))` is a module |
| `FaceIterateBottomHom` | removing `k ≤ n` bottom vertices, `λx. face_iterate_bottom(n, k, x)`, is a homomorphism `M.simplices(n) → M.simplices(n − k)` |
| `FaceIterateTopHom` | removing `k ≤ n` top vertices, `λx. face_iterate_top(n, k, x)`, is a homomorphism `M.simplices(n) → M.simplices(n − k)` |
| `FaceBoundaryDef` | `face_boundary(R, V, d, n, x) = Σ_{i ≤ n} alternating_sign(i) • d(n, i, x)` |
| `FaceComplexDef` | `face_complex(R, V, M)` packs `V`'s operations, the terms `M.simplices` and the face boundaries of `M.d` |
| `FaceComplexModule` | `complex_module(face_complex(R, V, M), n) = restrict_module(V, M.simplices(n))` |
| `SimplicialModuleMap` | `simplicial_module_map(R, V, M, W, N, F)`: a simplicial map between simplicial modules, linear in every dimension |
| `SimplicialModuleHomotopy` | `simplicial_module_homotopy(R, V, M, W, N, F, G, H)`: a simplicial homotopy between linear simplicial maps with every `H(n, j)` linear |
| `FaceAdd` | a face of a sum is the sum of the faces, `M.d(n + 1, i, x + y) = M.d(n + 1, i, x) + M.d(n + 1, i, y)` on `M.simplices(n + 1)` |
| `FaceSub` | a face of a difference is the difference of the faces, `M.d(n + 1, i, x − y) = M.d(n + 1, i, x) − M.d(n + 1, i, y)` on `M.simplices(n + 1)` |
| `FaceZero` | a face keeps zero, `M.d(n + 1, i, V.zero) = V.zero` |
| `DegeneracyAdd` | a degeneracy of a sum is the sum of the degeneracies, `M.s(n, i, x + y) = M.s(n, i, x) + M.s(n, i, y)` on `M.simplices(n)` |
| `DegeneracyZero` | a degeneracy keeps zero, `M.s(n, i, V.zero) = V.zero` |
| `FaceDegeneracyBelowZero` | `i < j`, `M.d(n + 1, i, z) = V.zero` ⇒ `M.d(n + 2, i, M.s(n + 1, j, z)) = V.zero` |
| `FaceDegeneracyAboveZero` | `j + 1 < i`, `M.d(n + 1, i − 1, z) = V.zero` ⇒ `M.d(n + 2, i, M.s(n + 1, j, z)) = V.zero` |
| `FaceBoundaryHom` | the face boundary out of `n + 1` is a homomorphism `M.simplices(n + 1) → M.simplices(n)` — card |
| `AlternatingDoubleSumCancel` | in any module, $\sum_j \sum_i (-1)^{j+i} d_i d_j x = 0$ once $d_i d_j = d_{j-1} d_i$ for `i < j` — card |
| `FaceComplexChain` | `chain_complex(R, face_complex(R, V, M))` — card |
| `ConstantSimplicialModule` | a submodule `K`, constant with identity faces and degeneracies, is a simplicial module, `simplicial_module(R, V, constant_simplicial_set(K))` — card |
| `ConstantFaceComplexHomology` | its face complex has boundaries `{0}` in degree 0 and cycles equal to boundaries above — card |
| `ConstantAcyclicAugmentation` | a constant simplicial module is acyclic over `K` through the identity — card |
| `SimplicialModuleMapChainMap` | a linear simplicial map is a chain map of the face complexes — card |
| `SimplicialModuleHomotopyChainHomotopy` | a linear simplicial homotopy `H` from `F` to `G` gives the chain homotopy $\sum_{j \le n} (-1)^j H(n, j)$ — card |
| `SimplicialModuleHomotopyEquivalenceChain` | linear maps inverse up to linear homotopies from the identities are a `chain_homotopy_equivalence` of the face complexes — card |
| `DegreewiseShortExactComplexes` | linear simplicial maps short exact in every dimension give `short_exact_complexes` of the face complexes — card |

## The Moore complex, horns, spheres and acyclic augmentations

| member | statement |
|---|---|
| `MooreTermsDef` | `moore_terms(V, M, n)`: the `x ∈ M.simplices(n)` with `M.d(n, i, x) = 0` for `1 ≤ i ≤ n`; all of `M.simplices(0)` at `n = 0` |
| `MooreComplexDef` | `moore_complex(V, M)` packs `V`'s operations, the Moore terms and `M.d(n, 0)` |
| `AcyclicAugmentation` | `acyclic_augmentation(R, V, M, N, ε)`: the simplicial module, Moore cycles equal to Moore boundaries in positive degrees, `ε` onto `N`, and `ε(x) = ε(y) ⇔ x − y` a Moore boundary on `M.simplices(0)` |
| `MooreSubcomplex` | `d_0` carries Moore terms to Moore terms, and `d_0 d_0 = 0` on them |
| `MooreComplexChain` | `chain_complex(R, moore_complex(V, M))` — card |
| `HornFillerExists` | a simplicial module is a Kan complex, `kan_complex(M)` |
| `SphereToMooreCycle` | a compatible sphere of (n+1)-simplices has `w` filling every face but the 0-th, with `y(0) − d_0 w` a Moore cycle |
| `MooreBoundaryFillsSphere` | if that defect is `d_0 v` for a Moore term `v`, then `w + v` fills the sphere — card |
| `SphereFillsInAcyclic` | under an acyclic augmentation every compatible sphere of (n+1)-simplices fills — card |
| `EdgeFillsInAcyclic` | under an acyclic augmentation two vertices with one image under `ε` are the faces of an edge |
| `PointedHomotopyAcyclic` | a simplicial homotopy keeping zero from the identity to `ι` after the augmentation of the last vertex, `ε` linear on `M.simplices(0)` and `ι(0, ·)` a section of `ε` on `N`, gives `acyclic_augmentation` over `N`'s carrier — card |
| `ExtraDegeneracyAcyclic` | an extra degeneracy over a module `N`, `ε` linear on `M.simplices(0)` and `σ` keeping zero, gives `acyclic_augmentation` over `N`'s carrier — card |

## Bisimplicial modules and the Alexander–Whitney map

`bisimplicial.go` holds bisimplicial modules, their laws and their
double complex; `alexander_whitney.go` the Alexander–Whitney map and its
laws, in a file of its own because the chain-map calculation is the
chapter's longest argument and reads as one. At an (n, n)-simplex x the map's coordinate p, in bidegree
(p, n − p), is the front horizontal p-face (`face_iterate_top` along the
row, removing the last horizontal face n − p times) of the back vertical
(n − p)-face (`face_iterate_bottom` along the column, removing the 0-th
vertical face p times). The chain-map calculation commutes the
two directions of iterated faces, then splits the diagonal boundary at
the coordinate p into two disjoint ranges: its faces i ≤ p are
horizontal faces of the coordinate p + 1, its faces i > p vertical faces
of the coordinate p. The horizontal boundary's extra term, the face
p + 1, and the vertical boundary's, the face 0, are one simplex with
opposite signs, and cancel. Linearity and the bounded support in each
total degree assemble the coordinate maps into the total module. The
chapter's table names the two face iterates, «rowLastFaces» (the last
face on a row) and «columnZerothFaces» (the 0-th face in a column).

| member | statement |
|---|---|
| `BisimplicialModule` | `bisimplicial_module(R, V, D)`: `bisimplicial_set(D)` with every row `bisimplicial_row(D, q)` and every column `bisimplicial_column(D, p)` a `simplicial_module` in `V` |
| `BisimplicialUnderlyingSet`, `BisimplicialRows`, `BisimplicialColumns` | the structure's three axioms: `bisimplicial_set(D)`, every row and every column a `simplicial_module` in `V` |
| `BisimplicialAmbientModule`, `BisimplicialSubmodules` | `V` is a module and each `D.simplices(p, q)` a submodule of it |
| `BisimplicialHorizontalHom`, `BisimplicialVerticalHom` | `D.dh(p + 1, q, i)` is linear `D.simplices(p + 1, q) → D.simplices(p, q)`, and `D.dv(p, q + 1, j)` is linear `D.simplices(p, q + 1) → D.simplices(p, q)` |
| `DiagonalFaceHom` | the diagonal face `x ↦ D.dh(n + 1, n, i, D.dv(n + 1, n + 1, i, x))` is linear `D.simplices(n + 1, n + 1) → D.simplices(n, n)` |
| `DiagonalSimplicialModule` | the diagonal is a simplicial module, `simplicial_module(R, V, bisimplicial_diagonal(D))` |
| `BisimplicialModuleDoubleComplex` | the alternating face sums of the two directions form a `double_complex` — card |
| `AlexanderWhitneyDef` | `alexander_whitney(V, dh, dv, n, x, p) = dh_{p+1} ∘ ⋯ ∘ dh_n ((dv_0)^p x)` for `p ≤ n`, `V.zero` past `n` |
| `AlexanderWhitneyChainMap` | `alexander_whitney(V, D.dh, D.dv)` is a `chain_map` from the face complex of the diagonal, `face_complex(R, V, bisimplicial_diagonal(D))`, to the total of the face sums at the alternating sign, `double_total(V, D.simplices, h, v, alternating_sign)` |
| `AlexanderWhitneyNatural` | for a bisimplicial map `F` keeping zero on the bottom row, `F(p, 0, V.zero) = V'.zero`, the map after `F(n, n)` is `double_total_map(F)` after the map — card |
| `AlexanderWhitneyConstantVertical` | when the 0-th vertical face of the column `n` fixes its simplices, the coordinate `n` of the image of `z` is `z` — card |
| `AlexanderWhitneyConstantHorizontal` | when the last horizontal face of the row `n` fixes its simplices, the coordinate `0` of the image of `y` is `y` — card |

## The free chains on a simplicial set

| member | statement |
|---|---|
| `FreeSimplicialModuleDef` | `free_simplicial_module(R, X)`: the chains `simplicial_chains(R.zero, X, R.carrier)` with the pushforwards `free_pushforward(R, X.d(n, i))` and `free_pushforward(R, X.s(n, i))` as faces and degeneracies |
| `FreeChainsSimplicialModule` | the chains on a simplicial set, with the pushforwards of its faces and degeneracies, are a simplicial module, `simplicial_module(R, free_module_record(R, 𝕌), free_simplicial_module(R, X))` — card |
| `SimplicialChainsFaceComplex` | on every chain, `simplicial_boundary` is the face boundary of the pushforwards of the faces — card |
| `SimplicialHomologyFaceComplex` | `simplicial_homology` is the homology of that face complex, `face_complex(R, free_module_record(R, 𝕌), free_simplicial_module(R, X))` — card |
| `SimplicialChainsFreeComplex` | the chains of a simplicial set are a chain complex as `free_complex(R, X.simplices, simplicial_boundary(…))` — card |
| `SimplicialHomotopyChainHomotopy` | a simplicial homotopy `H` from `F` to `G` gives the chain homotopy `Σ_{j ≤ n} (−1)^j` (pushforward of `H(n, j)`) between the pushforwards — card |
| `SimplicialMapsHomotopicChainHomotopic` | homotopic simplicial maps have chain homotopic pushforwards — card |
| `HomotopyEquivalenceChainHomotopyEquivalence` | a simplicial homotopy equivalence `F` gives a `chain_homotopy_equivalence` of the chains between the pushforwards of `F` and of an inverse — card |
| `ConstantSimplicialChainsHomology` | the chains on a constant simplicial set have boundaries `{0}` in degree 0 and cycles equal to boundaries above — card |
