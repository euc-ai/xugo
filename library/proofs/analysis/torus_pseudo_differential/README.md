# torus_pseudo_differential — continuous-variable symbols and Fourier quantization on the torus

Symbols have periodic base variables and continuous covariables. The Sᵐ₁,₀ estimates bound every derivative word, counting each covariable derivative once in the order loss. Integer orders use a squared absolute-value estimate with an integer power of 1+|ξ|². Quantization samples the covariable only at integer frequencies.

A homogeneous principal symbol is specified separately; subtracting a smooth radial cutoff times that symbol lowers order by one. The mapping, composition and realization cards provide the local calculus used by compact-manifold operators. The global adjoint statement is [pseudo_differential.PrincipalSymbolAdjoint](../../manifold/pseudo_differential/README.md). These statements do not identify a lattice covariable with a coordinate-invariant cotangent vector.

## Members

| Member | Statement or role |
|---|---|
| `BaseDef` | Definition of `ps_base` |
| `FrequencyDef` | Definition of `ps_frequency` |
| `joinDef` | Definition of `ps_join` |
| `DerivativeDef` | Definition of `ps_derivative_word` |
| `derivativeBoundDef` | Definition of `ps_derivative_bound` |
| `SymbolDef` | Definition of `torus_symbol` |
| `homogeneousDef` | Definition of `torus_homogeneous_symbol` |
| `radialCutoffDef` | Definition of `ps_radial_cutoff` |
| `PrincipalPairDef` | Definition of `torus_principal_pair` |
| `QuantizationDef` | Definition of `torus_quantize` |
| `realizationDef` | Definition of `torus_ps_realization` |
| `QuantizationSmooth` | Torus quantization sends smooth Fourier data to smooth functions — card |
| `FirstOrderQuantization` | A first-order polynomial symbol quantizes to its differential operator — card |
| `PseudoDifferentialBounded` | Order-m quantization has a realization bounded from H^s to H^(s-m), zero off H^s and equal to the Fourier quantization on smooth data — card |
| `PrincipalSymbolCompose` | The principal symbol of a composite is the product — card |
| `SymbolRealization` | A homogeneous principal symbol admits a torus quantization — card |
| `NegativeOrderCompact` | Negative-order torus operators are compact on a fixed Sobolev space — card |
| `Pseudolocality` | A quantization between periodic cutoffs with disjoint supports is smoothing — card |
| `CoordinateChange` | A cut-off quantization conjugated by a diffeomorphism of the small box is a quantization with the transported principal symbol — card |
