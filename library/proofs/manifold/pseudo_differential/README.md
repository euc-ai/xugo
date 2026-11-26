# pseudo_differential — pseudo-differential operators on closed projection bundles

A principal symbol is a smooth homogeneous map on the punctured cotangent bundle, written in the ambient coordinates of two smooth projection bundles. A pseudo-differential operator is a finite localized torus quantization with that symbol, plus an operator improving every integer Sobolev order. Local symbols use continuous covariables before integer-frequency sampling.

The source and target Sobolev spaces are the existing sequence closures. A realization is the unique normalized bounded extension of the action on smooth sections. Ellipticity concerns image fibres and is vacuous on the empty punctured fibre in dimension zero, where the spaces of sections over a closed manifold are finite dimensional.

## Members

| Member | Statement or role |
|---|---|
| `smoothModuleDef` | Definition of `ps_smooth_module` |
| `PuncturedDef` | Definition of `cotangent_punctured` |
| `PrincipalSymbolDef` | Definition of `ps_principal_symbol` |
| `EllipticDef` | Definition of `ps_elliptic_symbol` |
| `SmoothingDef` | Definition of `ps_smoothing` |
| `cutoffsDef` | Definition of `ps_chart_cutoffs` |
| `localSectionDef` | Definition of `ps_local_section` |
| `localPrincipalDef` | Definition of `ps_local_principal` |
| `quantizationDef` | Definition of `ps_quantization_seed` |
| `OperatorDef` | Definition of `pseudo_differential_operator` |
| `RealizationDef` | Definition of `ps_realization` |
| `PseudoDifferentialBounded` | Localized pseudo-differential operators have the stated Sobolev mapping property — card |
| `RealizationOnSmooth` | The chosen Sobolev realization agrees on smooth sections — card |
| `FirstOrderPseudoDifferential` | A first-order differential operator with smooth chart coefficients is pseudo-differential — card |
| `SymbolRealization` | Every smooth homogeneous bundle symbol has a global realization — card |
| `NegativeOrderCompact` | Negative-order operators are compact on a fixed Sobolev space — card |
| `EllipticFredholm` | Elliptic operators have Fredholm Sobolev realizations — card |
| `AdjointDef` | Definition of `ps_formal_adjoint` |
| `PrincipalSymbolCompose` | Composition multiplies principal symbols — card |
| `PrincipalSymbolAdjoint` | The formal adjoint has the adjoint principal symbol — card |
| `SamePrincipalLowerOrder` | Equal principal symbols imply a one-order gain for the difference — card |
| `InverseSymbol` | An elliptic symbol has a smooth inverse homogeneous symbol — card |
| `EllipticParametrixModuloCompact` | Quantized inverse symbols give parametrices modulo compact errors — card |
| `EllipticKernelSmooth` | Every Sobolev kernel vector has a smooth section representative — card |
| `EllipticRegularity` | Elliptic regularity transfers regularity of the output to the input — card |
