# sobolev_section — Sobolev sections of smooth projection bundles in finite atlas coordinates

A bundle is a smooth Hermitian projection of a fixed finite complex coordinate space ([smooth_projection_bundle](../smooth_projection_bundle/README.md)), including locally varying rank on disconnected bases. Smooth sections are normalized ambient-coordinate functions fixed by that projection. A localization record stores finitely many compatible charts and a subordinate smooth partition; their coordinate images lie in the half-period cube.

The fixed ambient host is the space of sequences indexed by a chart number, a fibre-coordinate number and an integer frequency vector. Localizing a smooth section means taking the Fourier coefficients of each cutoff coordinate function. The Sobolev carrier is the closure of these localized smooth sections in the weighted sequence Hilbert space. This defines global sections through sequence data and does not construct L² as a completion of pointwise functions. Different localization records have canonically inverse bounded transition maps. Smooth bundle isomorphisms likewise extend to bounded isomorphisms at every integer order.

The local-to-global cards make density, order inclusions, compactness, cutoff multiplication and regularity explicit. A single order above half the dimension gives finite differentiability; smooth sections correspond to membership in every integer order. Pointwise realization and uniqueness are asserted where that regularity supplies them.

## Members

| Member | Statement or role |
|---|---|
| `sectionClassDef` | Definition of `projected_section_class` |
| `SmoothSectionDef` | Definition of `smooth_projected_section` |
| `LocalizationDataDef` | Definition of `sobolev_localization_on` |
| `localizationIndicesDef` | Definition of `localization_indices` |
| `localizationModuleDef` | Definition of `localization_sequence_module` |
| `LocalizationInnerDef` | Definition of `localization_sequence_inner` |
| `LocalizationNormDef` | Definition of `localization_sequence_norm` |
| `LocalizeSectionDef` | Definition of `localize_section` |
| `SectionSobolevModuleDef` | Definition of `section_sobolev_module` |
| `sectionChangeDef` | Definition of `section_coordinate_change` |
| `LocalizationExists` | A compact smooth manifold admits a finite localization by small charts and a subordinate smooth partition — card |
| `FiniteRankSequenceNorm` | The ambient squared norm is the finite sum of the chart and fibre component squared Sobolev norms — card |
| `SmoothLocalization` | Localized smooth projected sections belong to every integer-order section space — card |
| `SectionHilbert` | The sequence-closure model of Sobolev sections is Hilbert — card |
| `SectionSmoothDense` | Localized smooth sections are dense in the section space — card |
| `SectionNormEquivalence` | Any two finite localizations give equivalent norms on smooth sections — card |
| `SectionCoordinateIsomorphism` | Change of localization extends to a bounded isomorphism and realizes the identity on smooth sections — card |
| `SectionOrderInclusion` | The inclusion from a higher integer order into a lower one is bounded on global sections — card |
| `SectionRellich` | Strict order decrease gives a compact inclusion of global Sobolev section spaces — card |
| `SectionSobolevEmbedding` | Sufficient finite order gives a unique projected section of class C^k realizing the sequence data — card |
| `SectionSmoothRegularity` | All integer orders are equivalent to realization by a smooth projected section — card |
| `sectionMultiplyDef` | Definition of `section_sobolev_multiply` |
| `SectionSmoothMultiplier` | A smooth scalar multiplier acts boundedly and agrees with pointwise multiplication on smooth sections — card |
| `sectionMatrixActionDef` | Definition of `section_matrix_action` |
| `SectionBundleIsomorphism` | Smooth inverse maps between projection presentations induce boundedly inverse Sobolev maps — card |
| `componentSmoothDef` | Definition of `torus_component_smooth` |
| `componentCodeDef` | Definition of `torus_component_code` |
| `chartExtensionSeedDef` | Definition of `chart_extension_seed` |
| `chartExtensionDef` | Definition of `section_chart_extension` |
| `chartRestrictionDef` | Definition of `section_chart_restriction` |
| `ComponentFourierDense` | Smooth finite-component torus Fourier data are dense in the local sequence space — card |
| `SectionChartExtension` | Chart cutoff, projection and zero extension give a bounded map from arbitrary local Sobolev data to global sections — card |
| `SectionChartRestriction` | A compactly supported chart cutoff gives a bounded local realization of global Sobolev data — card |
| `SectionCoordinateOrderCompatible` | Change of localization commutes with the order inclusions — card |

The localization record has the fields `count`, `charts` and `partition`; its constructor is `sobolev_localization_data`.

| Member | Statement or role |
|---|---|
| `LocalizationCountDef` | The active chart count |
| `LocalizationChartsDef` | The chart family |
| `LocalizationPartitionDef` | The partition functions |
| `LocalizationInduction` | Induction on localization records |
| `LocalizationRecursion` | Recursion on localization records |
| `LocalizationInjective` | Constructor injectivity |
| `LocalizationExtensionality` | Equality from equality of fields |
