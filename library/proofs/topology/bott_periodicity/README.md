# bott_periodicity — the complex Bott class and periodicity through clutching

The Bott representative is the relative triple of two trivial complex lines with map z on the complex plane. The product map sends a virtual bundle over a compact Hausdorff base to its external product with that representative. Its normalization fixes the choice between the Bott class and its dual.

The proof route is the Laurent-polynomial proof of Atiyah and Bott: approximate a clutching matrix without losing invertibility, remove negative powers, linearize a monic matrix polynomial, and split the resulting pencil by its inside-circle spectral projection. This construction uses finite-dimensional algebra and complex analysis, independently of Fredholm and pseudo-differential operators.

## Members

| Member | Statement or role |
|---|---|
| `compactInverseDef` | Definition of `k_to_kc` |
| `bottTripleDef` | Definition of `bott_triple` |
| `BottClassDef` | Definition of `bott_class` |
| `BottMapDef` | Definition of `bott_map` |
| `circleDef` | Definition of `bott_circle` |
| `clutchingDef` | Definition of `bott_clutching` |
| `clutchingTripleDef` | Definition of `bott_clutching_triple` |
| `laurentDef` | Definition of `bott_laurent_matrix` |
| `CompactInverse` | The compact relative comparison has the explicit zero-map inverse — card |
| `BottTriple` | The z triple is supported at the origin — card |
| `ClutchingTriple` | Radial clutching is supported on the zero section — card |
| `LaurentApproximation` | A clutching matrix admits a Laurent approximation preserving its relative class — card |
| `ClutchingRepresentation` | Every compact-support class over X times C has a stabilized clutching representative — card |
| `BottHomomorphism` | The Bott external product is a homomorphism — card |
| `BottSurjective` | The Bott external product is surjective — card |
| `BottInjective` | The Bott external product is injective — card |
| `BottPeriodicity` | The compact-base Bott external product is an isomorphism — card |
| `polynomialDef` | Definition of `bott_polynomial` |
| `polynomialLoopDef` | Definition of `bott_polynomial_loop` |
| `linearLoopDef` | Definition of `bott_linear_loop` |
| `polynomialCoefficientsDef` | Definition of `bott_polynomial_coefficients` |
| `companionDef` | Definition of `bott_companion` |
| `iterateDef` | Definition of `bott_matrix_iterate` |
| `insideProjectionDef` | Definition of `bott_inside_projection` |
| `polynomializationDef` | Definition of `bott_polynomialization` |
| `clutchingIndexDef` | Definition of `bott_clutching_index` |
| `clutchingInverseDef` | Definition of `bott_inverse` |
| `compactSupportBottDef` | Definition of `kc_bott_map` |
| `CompanionInsideBundle` | The companion stable spaces form a continuous projection bundle — card |
| `CompanionLinearLoop` | The companion of a monic loop invertible on the circle has no eigenvalue there — card |
| `InsideProjectionBundle` | For a continuous matrix with no eigenvalue on the circle, the stable spaces form a continuous projection bundle — card |
| `PolynomializationExists` | Every clutching matrix admits a normalized monic polynomialization — card |
| `PolynomializationIndependent` | The corrected companion virtual bundle is independent of polynomialization — card |
| `ClutchingIndexOnPolynomialization` | The selected clutching index equals the corrected companion virtual bundle — card |
| `RelativeClutchingIndex` | Equivalent relative clutching triples have equal candidate indices — card |
| `LaurentClutchingFormula` | A clutching class is the Bott product of its candidate index — card |
| `InverseBottNormalization` | The candidate inverse returns every virtual bundle from its Bott product — card |
| `CompactSupportBott` | The locally compact compact-support Bott map is an isomorphism — card |
