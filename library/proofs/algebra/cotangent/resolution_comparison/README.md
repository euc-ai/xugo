# resolution_comparison — maps and homotopies between polynomial resolutions, built degree by degree

A polynomial simplicial algebra over a commutative ring `R` (algebra/cotangent/simplicial_ring)
is free in every degree, on the variables of a set of names `X(n)`, and its
degeneracies carry generators to generators. That is what makes it free as
a simplicial object: an algebra map out of it is built one degree at a
time, and in each degree only on the generators. A generator of degree
`n + 1` that is a degeneracy `s_j(v)` of a generator below must go to
`s'_j` of the value at `v`, and every presentation of it as a degeneracy
gives the same value; a nondegenerate generator may go to any simplex of
the target whose faces are the values already assigned to its faces. A
resolution is a target where such a simplex always exists: its Moore
complex is exact in positive degrees, so every compatible sphere has a
filler, and its augmentation reads degree 0 modulo the Moore boundaries
onto the algebra it resolves, so two vertices with one image are the ends
of an edge. Hence the comparison theorem: an augmented polynomial
simplicial algebra maps into a resolution over any map of algebras
between the augmentation targets, any two maps that agree after the
target's augmentation are homotopic, and two resolutions of one algebra
are homotopy equivalent over its identity. This is the comparison
theorem for free simplicial algebras as Iyengar's account of
André–Quillen homology gives it: each degree a polynomial algebra on a
set of variables that the degeneracies keep.

The induction carries a map defined up to degree `n`,
`partial_simplicial_algebra_map(…, n, F)`, and its step keeps apart the
two things it uses. The target's acyclicity enters through one filling
lemma, `PartialMapFacesFill`; the source's freeness through the two facts
about degenerate generators and the uniqueness of an algebra map with
given values on generators. In degree 0 the map needs of the target only
that its augmentation be onto, and the homotopy only that its fibres be
the cosets of the Moore boundaries — the two degree-0 conjuncts of
`acyclic_augmentation`, one each. A homotopy, May's combinatorial one with
every component an algebra map, is built the same way up to degree `n`,
`partial_simplicial_algebra_homotopy(…, n, H)`: over a nondegenerate
generator of degree `n + 1` it fills a prism `w(0), …, w(n + 1)`, one
simplex at a time and in that order, an inner induction whose stages are
the prefixes `partial_simplicial_algebra_homotopy_prism(…, u, j, w)`. Each
`w(j)` with `j ≤ n` has every face fixed by `F`, the homotopy below and
`w(j − 1)` but the `(j + 1)`-th, which `w(j + 1)` fixes: a horn, which any
simplicial module fills. The last, `w(n + 1)`, has every face fixed: a
sphere, which only the exactness of the target's Moore complex fills.
Because the target is a resolution the homotopies are single homotopies
in one direction, never zigzags.

Every statement carries `cotangent_universe(R, 𝕌⟨A:U⟩)`, under which the
free algebras in the universe are rings and an algebra map out of one is
fixed by its values on the generators. A generator that is a degeneracy is
read through any presentation, so no statement writes a generator as an
iterated degeneracy of a nondegenerate one or asks that presentation to be
unique.

## Maps and homotopies up to a degree

| member | statement |
|---|---|
| `PartialSimplicialAlgebraMap` | `F(k)` an algebra map from degree `k` of the source to degree `k` of the target for `k ≤ n`, commuting with the faces and degeneracies between degrees up to `n` |
| `PartialSimplicialAlgebraHomotopy` | between two simplicial algebra maps `F` and `G`, every `H(k, j)` with `j ≤ k ≤ n` an algebra map into degree `k + 1`, with May's identities wherever they read degrees up to `n` |
| `partialSimplicialAlgebraHomotopyPrismDef` | `w(0), …, w(j − 1)` the first `j` simplices of the prism over the `(n + 1)`-simplex `u`, meeting every identity of the homotopy at `u` that reads only them, `F` and `G` in degree `n + 1` and `H` in degree `n` |
| `nondegenerateGeneratorDef` | `nondegenerate_generator(R, X, s, n, u)`: `u` a generator of degree `n`, and above degree 0 no degeneracy of a generator of degree `n − 1` |

## A map, one degree at a time

| member | statement |
|---|---|
| `PartialMapZero` | with `ε'` onto `S'` and `g` a map of algebras over `R`, choose generator preimages by `inverse_on` on the target's degree-0 algebra and extend to `F(0)` with `ε' ∘ F(0) = g ∘ ε` — card |
| `PartialMapFacesFill` | under a map up to degree `n` covering `g`, the images of the faces of any `(n + 1)`-simplex of the source are the faces of an `(n + 1)`-simplex of the resolution — card |
| `DegenerateGeneratorWellDefined` | `s_i(u) = s_j(v)` in degree `n + 1` gives `s'_i F(u) = s'_j F(v)` — card |
| `DegenerateGeneratorFaces` | `d'_i s'_j F(v) = F(d_i s_j v)` for every face `i ≤ n + 1` — card |
| `PartialMapExtends` | a map up to degree `n` covering `g` extends to one up to degree `n + 1` agreeing with it below — card |
| `PartialMapsAssemble` | maps up to every degree, each agreeing with the last below its degree, give a simplicial algebra map along the diagonal — card |
| `ComparisonMapExists` | an augmented polynomial simplicial algebra maps into a resolution over every map `g` of algebras over `R`: `ε' ∘ F(0) = g ∘ ε` — card |
| `MapDeterminedByNondegenerateGenerators` | two simplicial algebra maps agreeing on the nondegenerate generators agree everywhere — card |

## A homotopy, one degree at a time

| member | statement |
|---|---|
| `PartialHomotopyZero` | when the target's degree-0 fibres under `ε'` are the cosets of the Moore boundaries, maps agreeing after `ε'` in degree 0 are joined there by an algebra map into the edges — card |
| `DegenerateGeneratorHomotopyWellDefined` | the values May's degeneracy identities force on `s_i(u)`, `s'_i H(j − 1)(u)` for `i < j` and $s'_{i+1} H(j)(u)$ for `j ≤ i`, do not depend on the presentation — card |
| `PartialHomotopyPrismStart` | under a homotopy up to degree `n`, the first simplex of the prism over any `(n + 1)`-simplex exists: a horn with face 0 `F(n + 1, u)` — card |
| `PartialHomotopyPrismStep` | into a resolution, a prefix of length `1 ≤ j ≤ n + 1` extends by one simplex `w(j)`: a horn for `j ≤ n`, a sphere for `j = n + 1` — card |
| `PartialHomotopyPrismFills` | under a homotopy up to degree `n` into a resolution, every `(n + 1)`-simplex of the source has a whole prism, the prefix of length `n + 2` — card |
| `PartialHomotopyExtends` | a homotopy up to degree `n` into a resolution extends to one up to degree `n + 1` agreeing with it below — card |
| `PartialHomotopiesAssemble` | homotopies up to every degree, each agreeing with the last below its degree, give a simplicial algebra homotopy along the diagonal — card |
| `ComparisonHomotopyExists` | two simplicial algebra maps into a resolution that agree after `ε'` in degree 0 are joined by a simplicial algebra homotopy — card |

## Composites, and the comparison of two resolutions

| member | statement |
|---|---|
| `SimplicialAlgebraMapIdentity`, `SimplicialAlgebraMapCompose` | the identity of a polynomial simplicial algebra, and the composite of two simplicial algebra maps, are simplicial algebra maps — card |
| `SimplicialAlgebraMapAugmentationAt` | a map carrying `ε` to `ε'` along `g` in degree 0 does so in every degree, the augmentations read through the 0-th faces — card |
| `ComparisonMapHomotopyInverse` | a map between two resolutions of one algebra keeping the augmentations has a homotopy inverse keeping them, both composites homotopic to the identities — card |
| `ComparisonHomotopyEquivalence` | two resolutions of one algebra are homotopy equivalent over its identity — card |
