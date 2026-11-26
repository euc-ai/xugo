# standard_resolution — the standard free resolution of an algebra and the relative resolution over it

An algebra `S` over a commutative ring `R`, through a ring map `f`, is
resolved by free algebras over `R` built from `S` alone: in degree 0 the
free algebra on the elements of `S`, in degree `n + 1` the free algebra
on the members of the algebra of degree `n`, so that the `n`-simplices
are `R[R[…R[S]…]]` with `n + 1` brackets. Everything lives in the one
host `U` of `simplicial_ring`: an element `y` of `S` is named by its tag
`carrier_tag(S.carrier, y)`, the one naming of `S`'s carrier, a member of
a free algebra is itself a name one degree up with no further naming,
and all the free algebras are subrings of the one ring on `U`, so
the faces and degeneracies are functions of `U` and only the carriers
`standard_terms(R, S, n)` change with `n`. The faces evaluate one
bracket: the 0-th flattens the outer two (the multiplication of the
free algebra as a monad), the face `i + 1` is the face `i` acting inside
the outer bracket, and at the bottom the augmentation `standard_eps`
reads the tags of `S`'s elements back into `S`. The degeneracies double
one bracket by sending a name to its variable. The simplicial
identities are the monad laws; the one place the augmentation enters
is the last face, which is why the face of names in degree 0 is the
tag of the augmentation. The names and the free algebras are read
through the embedding and the tags chosen once in `simplicial_ring`, as
the canonical free resolution of algebra/module/resolution is read
through its chosen `index_embedding`; any other polynomial resolution
of `S` in the universe computes the same homology
(algebra/cotangent/cotangent_complex).

In degree 1 the 1-st face sends the variable of a 0-simplex `u` to
`τ(u) = [tag ε(u)]`, the representative of `u` in the 0-simplices with
its augmentation (`standard_representative`), while the 0-th face sends
it to `u`; in degree 2 the faces of the variable of `w` are `w`,
`[d_0 w]` and `[d_1 w]`. These are the faces the cochains of degrees 0
and 1 read (algebra/cotangent/cohomology_one).

The resolution is acyclic because of an extra degeneracy,
`u ↦ [u] − [0]`, the variable of `u` less the variable of zero, with
its bottom `y ↦ [tag y] − [tag 0]` on `S`. It is not additive and does
not satisfy `s_0 σ = σ σ`, but it satisfies the face identities and
keeps zero, which is all the acyclicity of the underlying simplicial
module reads: a Moore cycle `x` has `σ(x)` with every face but the
0-th zero, so `x` is a Moore boundary. The standard resolution is so a
`polynomial_resolution` of `S`; read in the simplicial flagship's terms,
as the simplicial set `standard_resolution(R, S, f)`, it is a Kan
complex whose homotopy groups vanish above degree 0. An
algebra map `S → S'` over `R` induces a map of standard resolutions,
functorially. A ring map `f : R → S` changes the coefficients instead:
for an algebra `T` over `S` through `g`, the standard resolutions of `T`
over `R` through `g ∘ f` and over `S` through `g` have the same names in
degree 0, the tags of `T`'s elements, so the map that fixes those names
and carries the coefficients along `f`, degree by degree, is a
simplicial map between them over `T` — the map the base change of the
cotangent complex is built on.

The relative standard resolution resolves an algebra `T` over `S`,
through `g`, over every term of `P = standard(S/R)` at once: a
bisimplicial algebra `Q(p, q)` whose column `p` is the standard
resolution of `T` over the `p`-simplices of `P`. The coefficient ring
is not changed: `Q(p, q)` is one free algebra over `R`, on `P`'s names
of degree `p` under the first tag `universe_tag(0)` and the relative
names under the second tag `universe_tag(1)` — the tags of `T`'s
elements in vertical degree 0, the members of the column's algebra
below in vertical degree `q + 1`. The relative names carry no tag of
their own — the tag is put on where they enter the column's names — so
in vertical degree 0 they are literally the names of degree 0 of the
standard resolution of `T` over `S`. The vertical faces and
degeneracies are the standard resolution's, acting through the second
tag and fixing `P`'s variables; the horizontal ones are the maps a row
inherits from `P`'s faces and degeneracies,
`relative_horizontal_map(R, h, q)`, which moves the first-tag names by
`h` and the second-tag names recursively in `q`. Each column is
augmented over `T` through `P`'s augmentation and `g`, and has its own
extra degeneracy `u ↦ [tag₁ u] − [tag₁ 0]`, so it is a resolution of
`T`; the row of `P`'s 0-simplices is augmented over the standard
resolution of `T` over `S`, with coefficients changed to `S` along `f`,
carrying a relative name to itself in vertical degree 0 and to its
augmentation one degree down above; and the standard resolution of `T`
over `R` maps into every column by one function of the host. Every
statement carries `cotangent_universe` of each ring whose embedding or
naming it needs injective, which also makes the two tags' images
disjoint.

The diagonal of `Q`, the `(n, n)`-simplices with a vertical face and
the horizontal map of `P`'s face of the same index taken together, is
itself a resolution of `T` over `R`, augmented by column 0. It has no
extra degeneracy: the columns' contractions `s_0^j ∘ σ ∘ d_0^j`, with
`σ(u) = [tag₁ u] − [tag₁ 0]`, commute with the horizontal maps, and
their diagonal is a contraction that keeps zero, which is what
acyclicity reads. Its degeneracies keep the variables because the
horizontal maps induced by `P`'s degeneracies do. Both `P` under the
first tag and the standard resolution of `T` over `R` map into it as
simplicial algebras, over `g` and over `T`: the two maps the comparison
theorem joins when the left map of the transitivity sequence is
identified.

## The standard resolution: definitions

| member | statement |
|---|---|
| `StandardNamesDef` | `standard_names(R, S, 0) = image(carrier_tag(S.carrier), S.carrier)`, `standard_names(R, S, n + 1) = universe_algebra(R, standard_names(R, S, n))` |
| `StandardTermsDef` | `standard_terms(R, S, n) = universe_algebra(R, standard_names(R, S, n))`, the `n`-simplices |
| `StandardEpsDef` | `standard_eps(R, S, f)` evaluates in `S`, coefficients through `f`, each tag read back by the preimage chosen in `S`'s carrier |
| `StandardFaceDef` | `d(n + 1, 0)` the multiplication, `d(n + 1, i + 1)` the map induced by `d(n, i)`, `d(0, ·)` the tag of the augmentation |
| `StandardDegeneracyDef` | `s(n, 0)` the map induced by the variables, `s(n + 1, j + 1)` the map induced by `s(n, j)` |
| `StandardResolutionDef` | `standard_resolution(R, S, f) = mk_simplicial(λn. standard_terms(R, S, n), standard_face(R, S, f), standard_degeneracy(R))`, the standard resolution as one simplicial set |
| `StandardToBaseDef` | `standard_to_base(R, S, f, n)`, the augmentation read in degree `n` through the 0-th faces |
| `StandardRepresentativeDef` | `standard_representative(R, S, f, u) = [tag ε(u)]`, the 1-st face of degree 1 at the variable of `u` |
| `StandardExtraDef`, `standardExtraBottomDef` | `standard_extra(R, u) = [u] − [0]`; its bottom `standard_extra_bottom(R, S, y) = [tag y] − [tag S.zero]` |
| `StandardMapDef` | `standard_map(R, S, T, g, n)`: the name of `y` in `S`'s carrier to the name of `g(y)` in `T`'s in degree 0, induced upward |
| `StandardBaseChangeDef` | `standard_base_change(R, S, f, n)`: induced by `f` on the coefficients and the identity on the names in degree 0, by `f` and the map of degree `n` in degree `n + 1` |

## The standard resolution: the simplicial algebra

| member | statement |
|---|---|
| `StandardFaceIn`, `StandardDegeneracyIn` | faces and degeneracies land in the adjacent simplices — card |
| `StandardFaceFace`, `StandardFaceDegeneracyBelow`, `StandardFaceDegeneracyEqual`, `StandardFaceDegeneracyAbove`, `StandardDegeneracyDegeneracy` | the simplicial identities, from the monad laws — card |
| `StandardSimplicialSet` | `simplicial_set(standard_resolution(R, S, f))` — card |
| `StandardFacesHom`, `StandardDegeneraciesHom` | faces and degeneracies are algebra maps over `R` — card |
| `StandardGeneratorsClosed` | a degeneracy carries the variable of a name to the variable of a name — card |
| `StandardEpsHom`, `StandardEpsCoequalizes` | the augmentation is a ring map over `f`, and `ε d_0 = ε d_1` — card |
| `StandardPolynomialAlgebra` | `augmented_polynomial_algebra` of the standard resolution over `S` — card |
| `StandardToBaseHom`, `StandardToBaseFaceIndependent` | the augmentation in degree `n` is a ring map over `f`, and after any face it is the augmentation one degree up — card |

## The standard resolution: acyclicity

| member | statement |
|---|---|
| `StandardExtraIn` | the extra degeneracy and its bottom land in the simplices — card |
| `StandardExtraFace` | `d_0 σ = id`, `d_{i+1} σ = σ d_i` — card |
| `StandardExtraDegeneracy` | `s_{j+1} σ = σ s_j`; `s_0 σ = σ σ` fails — card |
| `StandardExtraBottom` | `ε b = id` on `S`, `d_1 σ_0 = b ε` — card |
| `StandardExtraPointed` | `σ` and its bottom keep zero — card |
| `StandardResolution` | `polynomial_resolution(R, standard_names(R, S), …, S, f, standard_eps(R, S, f))` — card |
| `StandardResolutionKan` | the standard resolution is a Kan complex, `kan_complex(standard_resolution(R, S, f))` — card |
| `StandardResolutionHomotopyGroupsTrivial` | at every vertex `x₀`, `simplicial_homotopy_group(standard_resolution(R, S, f), x₀, n) = {simplicial_homotopy_unit(standard_resolution(R, S, f), x₀, n)}` for `0 < n` — card |

## The standard resolution: degrees 1 and 2

| member | statement |
|---|---|
| `StandardLowFaceFormulas` | `d_0[u] = u`, `d_1[u] = τ(u)` for a 0-simplex `u`; `d_0[w] = w`, `d_1[w] = [d_0 w]`, `d_2[w] = [d_1 w]` for a 1-simplex `w`, each in its simplices — card |
| `StandardRepresentativeLaws` | `τ(u)` is a 0-simplex with `ε(τ(u)) = ε(u)` and `τ(τ(u)) = τ(u)`; `τ(x) = τ(0)` on the kernel of `ε`; `τ(d_0 w) = τ(d_1 w)` — card |

## The standard resolution: functoriality

| member | statement |
|---|---|
| `StandardMapAugmentation` | for an algebra map `g` over `R`, `ε' ∘ standard_map(R, S, S', g, 0) = g ∘ ε` — card |
| `StandardMapAlgebraMap` | `standard_map(R, S, S', g)` is a `simplicial_algebra_map` of the two standard resolutions — card |
| `StandardMapIdentity`, `StandardMapCompose` | the identity induces the identity; induced maps compose — card |

## The standard resolution: change of the coefficient ring

| member | statement |
|---|---|
| `StandardBaseChangeAugmentation` | over a tower `R → S → T`, `standard_eps(S, T, g) ∘ standard_base_change(R, S, f, 0) = standard_eps(R, T, g ∘ f)` on the 0-simplices — card |
| `StandardBaseChangeMap` | `standard_base_change(R, S, f)` is a simplicial map from the standard resolution of `T` over `R` through `g ∘ f` to the one over `S` through `g`, `simplicial_map(standard_resolution(R, T, g ∘ f), standard_resolution(S, T, g), standard_base_change(R, S, f))`, in every degree an algebra map over `f` — card |

## The relative resolution: definitions

| member | statement |
|---|---|
| `RelativeNamesDef` | `relative_names(R, S, T, p, 0) = image(carrier_tag(T.carrier), T.carrier)`, `relative_names(R, S, T, p, q + 1) = relative_terms(R, S, T, p, q)`, untagged |
| `RelativeTermsDef` | `relative_terms(R, S, T, p, q) = universe_algebra(R, tag₀(standard_names(R, S, p)) ∪ tag₁(relative_names(R, S, T, p, q)))` |
| `relativeNameMapDef` | `relative_name_map(h)`: `tag₁ w ↦ tag₁ h(w)` for a map `h` of the relative names, every other name fixed |
| `RelativeVerticalEpsDef` | `relative_vertical_eps(R, S, f, T, g, p)`: column `p` onto `T`, `P`'s names through `standard_to_base` and `g`, `T`'s tags read back |
| `RelativeVerticalFaceDef` | vertical faces: untagging in face 0, `relative_name_map` of the face below in face `j + 1`, the tag of the column's augmentation at the bottom |
| `RelativeVerticalDegeneracyDef` | vertical degeneracies, the same in every column: `relative_name_map` of `w ↦ [tag₁ w]`, then of the degeneracy below |
| `relativeExtraDef`, `relativeExtraBottomDef` | `relative_extra(R, u) = [tag₁ u] − [tag₁ 0]`; its bottom `[tag₁ tag t] − [tag₁ tag T.zero]` |
| `RelativeHorizontalMapDef` | `relative_horizontal_map(R, h, q)`: the map of row `q` induced by a map `h` of `P`'s simplices |
| `RelativeHorizontalEpsDef` | `relative_horizontal_eps(R, S, f, q)`: row `q` of column 0 onto `standard_terms(S, T, q)`, coefficients through `f`, `P`'s names to constants of their augmentation |
| `RelativeFromAbsoluteDef` | `relative_from_absolute(R, q)`: the standard resolution of `T` over `R` into every column, through the second tag |

## The relative resolution: the bisimplicial algebra

| member | statement |
|---|---|
| `RelativeNamesZero` | `relative_names(R, S, T, p, 0) = standard_names(S, T, 0)` in every column — card |
| `RelativeVerticalEpsHom` | the column's augmentation is a ring map over `g ∘ f`, and on `P`'s simplices it is `g` after `P`'s augmentation — card |
| `RelativeVerticalFaceIn`, `RelativeHorizontalFaceIn` | the faces of both directions land in the adjacent simplices — card |
| `RelativeVerticalHom`, `RelativeHorizontalHom` | the maps of both directions are algebra maps over `R` — card |
| `RelativeVerticalFixesBase` | the vertical maps fix `P`'s simplices under the first tag — card |
| `RelativeGeneratorsClosed` | a vertical degeneracy carries the second tags of relative names to those one degree up and fixes `P`'s names, on the variables — card |
| `RelativeBaseInclusionHom`, `RelativeBaseInclusionNatural` | the inclusion of `P` under the first tag is an algebra map, and a row's induced map extends the map of `P` along it — card |
| `RelativeVerticalSimplicial`, `RelativeHorizontalSimplicial` | every column and every row is a simplicial set — card |
| `RelativeDirectionsCommute` | the horizontal and the vertical maps commute — card |
| `RelativeBisimplicialSet` | `bisimplicial_set` of the relative standard resolution — card |

## The relative resolution: columns, rows and augmentations

| member | statement |
|---|---|
| `RelativeColumnAugmented` | every column is an `augmented_polynomial_algebra` over `T` through `g ∘ f` — card |
| `RelativeColumnExtra` | every column has the extra degeneracy `[tag₁ u] − [tag₁ 0]` over `T`, keeping zero — card |
| `RelativeColumnResolution` | every column is a `polynomial_resolution` of `T` — card |
| `RelativeHorizontalEpsHom` | the row augmentation is an algebra map over `f` into the standard resolution of `T` over `S` — card |
| `RelativeHorizontalEpsVertical` | the row augmentation commutes with the vertical faces and degeneracies and with the augmentations onto `T` — card |
| `RelativeAugmentationC` | the augmentation onto `T` is the same through any vertical face and in any column — card |
| `RelativeFromAbsoluteMap` | `relative_from_absolute(R)` is a `simplicial_algebra_map` from the standard resolution of `T` over `R` into every column, over `T` — card |
| `RelativeFromAbsoluteNatural` | every horizontal map fixes its values — card |

## The relative resolution: the diagonal

| member | statement |
|---|---|
| `RelativeHorizontalGeneratorsClosed` | the map of row `q` induced by `P`'s degeneracy carries the variable of every name of `(p, q)` to the variable of a name of `(p + 1, q)` — card |
| `RelativeDiagonalResolution` | the diagonal, with `bisimplicial_diagonal_face` and `bisimplicial_diagonal_degeneracy` of the two directions, is a `polynomial_resolution` of `T` over `R` through `g ∘ f`, augmented by column 0 — card |
| `RelativeDiagonalBaseInclusion` | the first tag is a `simplicial_algebra_map` from `P` to the diagonal, read by column 0's augmentation as `g` after `P`'s — card |
| `RelativeDiagonalFromAbsolute` | `relative_from_absolute(R)` is a `simplicial_algebra_map` from the standard resolution of `T` over `R` to the diagonal, over `T` — card |

## Increasing algebra unions

Increasing unions use the induced standard name maps: degree zero relabels the independently chosen carrier tags, and successor degrees use the preceding polynomial map. Names of the union are the union of the images of stage names, with injectivity under the stated host-capacity hypotheses.

| Member | Status | Statement and purpose |
|---|---|---|
| `IncreasingAlgebraUnionDef` | definition | An increasing sequence of R-subalgebras on one host, with union S. |
| `StandardNameMapDef` | definition | Names in degree zero are relabeled by carrier tags; successor names are polynomials and use the preceding standard algebra map. |
| `StandardResolutionUnion` | card | The equality is a union of images under induced maps, not a literal union of independently chosen carrier tags. — card |
