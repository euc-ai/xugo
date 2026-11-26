# transitivity — the transitivity triangle of a tower of rings and its long exact sequences

A tower of commutative rings `R → S → T`, through ring maps `f` and `g`,
with a module `N` over `T`, has three cotangent complexes over `T`:
$L_{S/R} \otimes_S N$ is `cotangent_complex(R, S, f, T, g, N)`, $L_{T/R} \otimes_T N$
is `cotangent_complex(R, T, λa. g(f(a)), T, λc. c, N)`, and $L_{T/S} \otimes_T N$
is `cotangent_complex(S, T, g, T, λc. c, N)`. Their homology, the
André–Quillen homology D_n, fits into one long exact sequence:

$$
\cdots \to D_{n+1}(T/S) \to D_n(S/R) \to D_n(T/R) \to D_n(T/S) \to \cdots \to D_0(T/S) \to 0.
$$

All three live in the one host `U`, a universe for the three rings
(`cotangent_universe`), so the sequence is a single statement, with no
isomorphism between universes.

The proof is built from double complexes, with no spectral sequence; of
the Eilenberg–Zilber theorem only the Alexander–Whitney map is used, to
identify the left map. No base-change theorem for the cotangent complex
enters either: $L_{T/S} \otimes N$ is reached through the rows of the right
term, each contracted onto the names of the standard resolution of `T`
over `S`. Let `P` be the standard resolution of `S`
over `R`, and `Q` the relative standard resolution of `T` over `P`
(algebra/cotangent/standard_resolution). `Q` is bisimplicial: column `p`
is the standard resolution of `T` over `P_p`. Its variables are `P`'s
names under the first tag and the relative names under the second.

At `(p, q)` there are three terms, the finitely supported functions with
values in `N` on three sets of variables:
- the middle term on all the variables of `Q(p, q)`;
- the left term on `P`'s names;
- the right term on the relative names.

The faces of `Q` act on the middle term by their Jacobians, and the
alternating sums of those faces give the two boundaries. The left term
is a sub-double complex under the same boundaries. The right term is the
quotient: the projection reads a function at the second tags, and a
section splits it. So the three totals form a short exact sequence of
complexes, and their homology is long exact.

Each total computes one D:
- **Left.** The columns are constant, with vertical boundaries alternately
  zero and the identity. By the augmented assembly along the columns, the
  left total maps quasi-isomorphically onto $L_{S/R} \otimes N$.
- **Middle.** Each column is the differential complex of a resolution of
  `T` over `R`. The Jacobian of the map from the standard resolution of
  `T` over `R` into it is a chain homotopy equivalence. The double complex
  with $L_{T/R} \otimes N$ in every column therefore maps quasi-isomorphically
  onto the middle term, and onto its own column 0.
- **Right.** Row `q` is the chains with values in `N` on a simplicial set:
  the relative names of row `q`, whose faces are the maps of names that
  `P`'s faces induce. That simplicial set contracts onto the names of
  degree `q` of the standard resolution of `T` over `S`, by induction on
  `q`. The names of row `q + 1` are the diagonal of a bisimplicial set
  (`triangle_auxiliary`), in which `P`'s names move in one direction and
  the names of row `q` in the other. The contraction of row `q` carries
  over by renaming those names, a functor on sets. The free algebras on
  `P`'s names and a fixed set of names (`triangle_fixed_names`) then
  contract through an extra degeneracy that acts on the coefficients;
  that degeneracy does not satisfy `s₀σ = σσ`, and the degenerate section
  is used. The induction is on homotopy equivalences of simplicial sets,
  with the section and the homotopy explicit, because rows from `q = 2`
  on have no extra degeneracy. The rows are then exact, and the right
  total maps quasi-isomorphically onto $L_{T/S} \otimes N$.

The maps of the D-sequence are the totals' maps, carried across these
homology isomorphisms, with each inverse taken on its carrier. Each spot
is then exact because the totals' sequence is. The left map is the one
`g` induces on cotangent complexes. The right map is the one the change
of base from `R` to `S` induces. The cone of the inclusion of totals
computes $L_{T/S} \otimes N$. The triangle is stated on the totals because
there the inclusion and the projection compose to zero on the nose:
the chain map `g` induces between the cotangent complexes, followed by
the one the change of base induces, is zero only on homology — in
degree 0 it carries `d(tag s)` to `d(tag g(s))`, a boundary but not
zero — so the cone is taken of the inclusion of totals, which
`TransitivityLeftMapNatural` identifies on homology with the map `g`
induces.

The left map is identified on the diagonal of `Q`, itself a resolution
of `T` over `R`. `P` maps into it in two ways that cover `g`: under the
first tag, and through the standard resolution of `T` over `R` after
the map `g` induces. The comparison theorem joins the two by a
homotopy, so their Jacobians agree on homology in the differential
complex of the diagonal. That complex is the face complex of the
diagonal of the middle term, read as a bisimplicial module, and the
Alexander–Whitney map carries it into the middle total. The first map
lands in the left term, whose vertical faces are identities, where the
Alexander–Whitney map reads the corner `(n, 0)` and so inverts the left
edge; the second goes through the comparison from the constant rows,
whose horizontal faces are identities, where it reads the corner
`(0, n)` and inverts the constant rows' edge.

The cohomology `D^n` with coefficients in `N` fits into the dual sequence

$$
0 \to D^0(T/S) \to D^0(T/R) \to D^0(S/R) \to D^1(T/S) \to \cdots \to D^n(S/R) \to D^{n+1}(T/S) \to \cdots.
$$

It is read off the same triangle taken at the chain level with
coefficients in `T` itself. The totals and the three cotangent complexes
are then based complexes, free on their names in every degree; the
sequence of totals splits in every degree; the left edge, the right edge
and the comparison of $L_{T/R} \otimes T$ into the middle total — the
Alexander–Whitney section of the constant rows followed by the comparison
of totals — are quasi-isomorphisms; and the two squares commute, the left
one up to a chain homotopy found on the diagonal of `Q`, the right one on
the nose. Dualizing that diagram with coefficients in `N`
([`free_complex_duality`](../../module/free_complex_duality/README.md))
gives the sequence: its two maps are the transposed Jacobians of the
change of base and of the map `g` induces, and its connecting map is the
dual sequence of totals' connecting map carried by the duals of the two
edges. Every map is named, so the sequence says which maps are exact; with
the maps quantified it would say nothing, since at `S = R` every
`D^n(S/R, N)` vanishes.

## The terms and their boundaries

| member | statement |
|---|---|
| `TriangleColumnNamesDef` | `triangle_column_names(R, S, T, p, q)` = `P`'s names of degree `p` under the first tag ∪ the relative names of `(p, q)` under the second: the variables of `Q(p, q)` |
| `triangleLeftDef` | `triangle_left(R, S, N, p, q)` = `finite_supp(N, P`'s names of degree `p` under the first tag`)`, the same in every `q` |
| `triangleMiddleDef` | `triangle_middle(R, S, T, N, p, q)` = `finite_supp(N, triangle_column_names(R, S, T, p, q))` |
| `triangleRightDef` | `triangle_right(R, S, T, N, p, q)` = `finite_supp(N, relative_names(R, S, T, p, q))`, untagged |
| `triangleHorizontalDef` | the horizontal boundary out of `(p, q)`: the alternating sum of `differential_map` at the maps of columns that `P`'s faces induce |
| `TriangleVerticalDef` | the vertical boundary out of `(p, q)`: `differential_boundary` of column `p` |
| `TriangleInclusionDef` | `triangle_inclusion(p, q, u) = u` |
| `TriangleProjectionDef` | `triangle_projection(p, q, u) = λt. u(universe_tag(1, t))` |
| `TriangleSectionDef` | `triangle_section(N, u)`: `u` carried under the second tag, zero elsewhere |
| `triangleRightHorizontalDef` | the right term's horizontal boundary: the boundary of the chains with values in `N` on the relative names of row `q` |
| `TriangleRightVerticalDef` | the right term's vertical boundary: the middle one through the section and the projection |
| `TriangleLeftEpsDef` | `triangle_left_eps(p, u) = λx. u(universe_tag(0, x))`, the augmentation of the left columns |
| `TriangleLeftTotalDef`, `TriangleMiddleTotalDef`, `TriangleRightTotalDef` | the three totals, at `T`'s alternating signs |

The tuples `triangle_left_double`, `triangle_middle_double` and
`triangle_right_double` each name, in one place, the module, the terms
and the two boundaries of a double complex.

## The short exact sequence

| member | statement |
|---|---|
| `TriangleMiddleDouble` | the middle term is a double complex over `T` — card |
| `LeftColumnsConstant` | on the left term every vertical face is the identity; the vertical boundary is zero out of `2q + 1` and the identity out of `2q + 2` — card |
| `TriangleLeftDouble` | the left term is a double complex under the middle boundaries — card |
| `TriangleDegreewiseShortExact` | at every `(p, q)`: left ↪ middle ↠ right exact, split by the section — card |
| `TriangleInclusionDoubleMap` | the inclusion is a map of double complexes — card |
| `TriangleProjectionDoubleMap` | the projection is a map of double complexes — card |
| `TriangleRightDouble` | the right term is a double complex over `T` — card |
| `TriangleTotalShortExact` | `short_exact_complexes` of the three totals under the two maps — card |
| `LeftTotalAugmented` | the hypotheses of `AugmentedAssembly` hold for the left term, augmented onto $L_{S/R} \otimes N$ — card |
| `LeftTotalQuasiIsomorphism` | the left total → $L_{S/R} \otimes N$ is a quasi-isomorphism — card |

## The middle total

| member | statement |
|---|---|
| `constantCotangentDef`, `constantCotangentVerticalDef` | `constant_cotangent(R, T, φ, N, p, q)` and its vertical boundary: the terms and the boundary of `cotangent_complex(R, T, φ, T, λc. c, N)`, the same in every column |
| `constantCotangentHorizontalDef` | the alternating sum of `p + 1` identities |
| `constantCotangentTotalDef` | the total of the double complex with constant rows |
| `triangleMiddleComparisonDef` | the Jacobian of `relative_from_absolute` into column `p` |
| `ConstantCotangentDouble` | the double complex with constant rows is a double complex — card |
| `ConstantRowsTotal` | its total → $L_{T/R} \otimes N$, reading the coordinate 0, is a quasi-isomorphism — card |
| `MiddleColumnComparison` | in every column the comparison is a chain homotopy equivalence — card |
| `MiddleComparisonDoubleMap` | the comparisons are a map of double complexes — card |
| `MiddleTotalQuasiIsomorphism` | the totals' comparison is a quasi-isomorphism — card |

The tuple `constant_cotangent_double` names the double complex with
constant rows.

## The rows of the right term

| member | statement |
|---|---|
| `triangleRowNameDef` | `triangle_row_name(R, h, q)`: the map of the relative names of row `q` induced by `h`, the identity in row 0 |
| `TriangleRowAugmentationDef` | `triangle_row_augmentation(R, S, f, p, q)`: the relative names of `(p, q)` → `standard_names(S, T, q)` |
| `TriangleRightEpsDef` | `triangle_right_eps(R, S, f, T, N, q)`: the chains along the augmentation in column 0 |
| `triangleFixedNamesDef` | `triangle_fixed_names(R, S, W, p)` = the free algebra on `P`'s names under the first tag and `W` under the second |
| `triangleAuxiliaryDef` | `triangle_auxiliary(R, S, T, q, p, p')` = `triangle_fixed_names(R, S, relative_names(R, S, T, p', q), p)` |
| `triangleRenameDef` | `triangle_rename(R, F)`: rename the second-tag variables by `F`, keep the others |
| `AuxiliaryBisimplicial` | `triangle_auxiliary` at row `q` is bisimplicial, with diagonal the relative names of row `q + 1` — card |
| `AuxiliaryColumnHomotopyNatural` | a homotopy of row `q`'s names renames into a vertical homotopy, natural in `p` — card |
| `AuxiliaryToFixedNames` | a contraction of row `q` renames into one of row `q + 1` onto `triangle_fixed_names(R, S, standard_names(S, T, q))` — card |
| `FixedNamesExtra` | the fixed names have an extra degeneracy that acts on the coefficients and keeps zero — card |
| `FixedNamesContractible` | the fixed names contract onto `universe_algebra(S, W)` — card |
| `RightRowHomotopyEquivalence` | every row contracts onto `standard_names(S, T, q)`, with the section and the homotopy explicit — card |
| `RightRowAcyclic` | the augmented rows are exact: the row hypotheses of `AugmentedAssemblyRows` — card |
| `RightRowEpsVertical` | the row augmentations commute with the vertical boundaries — card |
| `RightTotalQuasiIsomorphism` | the right total → $L_{T/S} \otimes N$ is a quasi-isomorphism — card |

## The bisimplicial modules and the diagonal

| member | statement |
|---|---|
| `TriangleMiddleBisimplicial` | the middle term, with the Jacobians of `Q`'s horizontal maps and of its vertical faces and degeneracies, is a `bisimplicial_module` over `T`; its face sums are the middle boundaries — card |
| `TriangleLeftBisimplicial` | the left term is a `bisimplicial_module` under the same maps — card |
| `ConstantCotangentBisimplicial` | the constant rows, with identity horizontal maps and the cotangent complex's faces and degeneracies vertically, are a `bisimplicial_module` — card |
| `MiddleComparisonBisimplicialMap` | the comparison is a `bisimplicial_map` from the constant rows to the middle term — card |
| `MiddleDiagonalDifferential` | on the diagonal of the middle term each face is the face of the differential complex of the diagonal of `Q`, and the comparison read on the diagonal is the Jacobian of `relative_from_absolute` into that resolution — card |

## The long exact sequence

| member | statement |
|---|---|
| `TransitivityLeftMapDef` | `transitivity_left_map(…, n)`: D_n(S/R) → D_n(T/R), the inclusion of totals carried across |
| `TransitivityRightMapDef` | `transitivity_right_map(…, n)`: D_n(T/R) → D_n(T/S), the projection of totals carried across |
| `TransitivityConnectingDef` | `transitivity_connecting(…, n)`: $D_{n+1}(T/S) \to D_n(S/R)$, the totals' connecting map carried across |
| `TransitivityExactAtLeft` | exact at D_n(S/R) — card |
| `TransitivityExactAtMiddle` | exact at D_n(T/R) — card |
| `TransitivityExactAtRight` | exact at $D_{n+1}(T/S)$ — card |
| `TransitivityEnd` | the right map in degree 0 is onto — card |
| `TransitivityLeftMapNatural` | the left map is the map induced by `g` on cotangent complexes — card |
| `TransitivityRightMapNatural` | the right map is the map `standard_base_change(R, S, f)` induces, the change of coefficients from `R` to `S` — card |
| `TransitivityTriangle` | the cone of the inclusion of totals → $L_{T/S} \otimes N$ is a quasi-isomorphism — card |

## The chain-level diagram

| member | statement |
|---|---|
| `constantTotalAWSectionDef`, `leftTotalAWSectionDef` | the Alexander–Whitney sections of the constant rows and of the left term, from the cotangent complexes of `T` and of `S` over `R` into their totals |
| `middleTotalChainComparisonDef` | `middle_total_chain_comparison`: $L_{T/R} \otimes N$ into the middle total, the constant rows' section followed by the comparison of totals |
| `triangleTotalSectionDef`, `triangleTotalRetractionDef` | the splitting of the totals: the section on every coordinate, and the retraction `v − τ(π(v))` |
| `TriangleTotalsBased` | with coefficients in `T` the left, middle and right totals and the total with constant rows are based, cell by cell by the identity — card |
| `TriangleTotalSplit` | the short exact sequence of totals splits in every degree, for any `N` — card |
| `ConstantTotalAWSection` | the constant rows' section is a chain map, a strict section of their edge and a homotopy inverse of it — card |
| `MiddleTotalChainComparison` | the middle comparison is a quasi-isomorphism with a chain homotopy inverse — card |
| `LeftTotalAWSection` | the left section is a chain map, a strict section of the left edge and a homotopy inverse of it — card |
| `TransitivityLeftHomotopyOnSection` | on the left section, the inclusion of totals is chain homotopic to the middle comparison after the map `g` induces — card |
| `TransitivityLeftChainSquare` | the inclusion of totals is chain homotopic to the middle comparison after `g`'s map after the left edge — card |
| `TransitivityRightChainSquare` | the right edge after the projection after the middle comparison is the change of base, on every chain — card |

## The cohomology sequence

| member | statement |
|---|---|
| `CoTransitivityLeftMapDef` | `co_transitivity_left_map(…, n)`: `D^n(T/S) → D^n(T/R)`, the transposed Jacobian of `standard_base_change(R, S, f)` on cohomology |
| `CoTransitivityRightMapDef` | `co_transitivity_right_map(…, n)`: `D^n(T/R) → D^n(S/R)`, the transposed Jacobian of `standard_map(R, S, T, g)` on cohomology |
| `CoTransitivityConnectingDef` | `co_transitivity_connecting(…, n)`: $D^n(S/R) \to D^{n+1}(T/S)$, the dual sequence of totals' connecting map carried across the duals of the two edges |
| `CotangentCohomologyTransitivity` | the long exact sequence, injective at `D^0(T/S)` — card |
| `CotangentCohomologyTransitivityCoefficientNatural` | a linear map of coefficient modules commutes with the three maps — card |

## Restriction to a localization

| member | statement |
|---|---|
| `CotangentCohomologyRestrictionDef` | `cotangent_cohomology_restriction(R, S, f, S', ρ, N', ν, n, x)`: `D^n(S/R, N) → D^n(S'/R, N')`, composition with `ν` followed by the inverse of the right map of `R → S → S'` on the classes |
