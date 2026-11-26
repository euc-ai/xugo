# torus_sobolev — integer-order torus Sobolev sequence spaces and local operators

The fixed host is the type of complex sequences on zero-filled integer vectors. An integer s selects the weight (1+‖k‖²)ˢ; dimension n selects the active frequency carrier. H⁰ is the unweighted sequence Hilbert space. Finite frequency projections yield the quantitative tail estimate and Rellich compactness.

Smooth multiplication is convolution of the rapidly decreasing Fourier coefficients with the Sobolev sequence. Derivatives are frequency multipliers. Local pullback is the unique bounded extension of cutoff pullback on smooth periodic functions; both coordinate boxes lie strictly inside a half-period cube, so periodization introduces no boundary jump. Membership in every integer Sobolev order is equivalent to rapid decay; a single finite order gives only the corresponding finite differentiability.

## Members

| Member | Statement or role |
|---|---|
| `SobolevWeightDef` | Definition of `sobolev_weight` |
| `SobolevModuleDef` | Definition of `sobolev_module` |
| `SobolevInnerDef` | Definition of `sobolev_inner` |
| `SobolevNormDef` | Definition of `sobolev_norm` |
| `frequencyDerivativeDef` | Definition of `frequency_derivative` |
| `sobolevMultiplyDef` | Definition of `sobolev_multiply` |
| `multiplierBoundDef` | Definition of `sobolev_multiplier_bound` |
| `SmallBoxDef` | Definition of `torus_small_box` |
| `PeriodizeDef` | Definition of `torus_periodize` |
| `LocalPullbackSeedDef` | Definition of `local_pullback_seed` |
| `localPullbackDef` | Definition of `sobolev_local_pullback` |
| `PeetreInequality` | Peetre's inequality moves an integer Sobolev weight across a sum of frequencies — card |
| `SobolevHilbert` | Every integer-order torus Sobolev sequence space is Hilbert — card |
| `SobolevInclusion` | Inclusion from a higher integer order into a lower order is bounded and contractive — card |
| `FrequencyProjectionFiniteRank` | Finite frequency projections are bounded finite-rank maps between any two integer orders — card |
| `RellichTailEstimate` | The squared lower-order tail is bounded by the higher-order squared norm times the negative frequency-radius power — card |
| `Rellich` | A strict decrease of Sobolev order gives a compact inclusion — card |
| `RapidIffAllSobolev` | Rapid decay is equivalent to membership in every integer Sobolev order — card |
| `SmoothDense` | Fourier coefficients of smooth periodic functions are dense at every integer order — card |
| `SobolevEmbedding` | Order strictly above half the dimension plus r gives a unique Fourier realization of class C^r — card |
| `SmoothIffAllOrders` | Membership in every integer order is equivalent to the Fourier coefficients of one smooth periodic function — card |
| `SmoothMultiplier` | Multiplication by a smooth periodic function is bounded, with the stated weighted coefficient bound — card |
| `MultiplierRealization` | Sequence convolution represents pointwise multiplication of smooth periodic functions — card |
| `DerivativeOrder` | A coordinate derivative is bounded from order s to order s−1 — card |
| `LocalPullback` | Compactly supported cutoff pullback by a local diffeomorphism is bounded at every integer order and agrees with the smooth realization — card |
| `LocalPullbackOrderCompatible` | Local pullback agrees across Sobolev orders on the stronger carrier — card |
| `derivativeWordDef` | Definition of `frequency_derivative_word` |
| `differentialOperatorDef` | Definition of `sobolev_differential_operator` |
| `DifferentialOperatorOrder` | A finite sum of smooth-coefficient derivatives of order at most m is bounded from order s to order s−m — card |
| `localSobolevCarrierDef` | Definition of `local_sobolev_carrier` |
| `CutoffZeroExtension` | A compact chart cutoff sends Sobolev sequences into the local zero-extension carrier — card |
| `PeriodizedZeroExtensionSmooth` | A compactly supported smooth function in the small box periodizes smoothly and agrees with the original function there — card |
