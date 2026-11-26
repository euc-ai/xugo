# toeplitz_operator — Toeplitz operators on the unilateral sequence space and their index

Symbols are continuous 2π-periodic functions of a real parameter. The coefficient at integer k uses exp(−ikt) and the normalized one-period integral. The Toeplitz operator on ℓ²(ℕ) has matrix entry f-hat(m−j), first on finite-support vectors and then by its unique bounded extension.

Trigonometric symbols give finite-rank semicommutators; uniform approximation and norm limits give compact semicommutators for continuous symbols. A nonvanishing symbol is invertible modulo compact operators. For piecewise smooth symbols the winding integer is identified with `residue.winding_index`, and the index is its negative. Multiplication by exp(it) gives the unilateral shift and fixes the sign at −1.

## Members

| Member | Statement or role |
|---|---|
| `CircleSymbolDef` | Definition of `circle_symbol` |
| `circleCoefficientDef` | Definition of `circle_coefficient` |
| `symbolNormDef` | Definition of `circle_symbol_norm` |
| `HardyModuleDef` | Definition of `hardy_sequence_module` |
| `HardyInnerDef` | Definition of `hardy_sequence_inner` |
| `HardyNormDef` | Definition of `hardy_sequence_norm` |
| `ToeplitzDef` | Definition of `toeplitz_operator` |
| `circlePolynomialDef` | Definition of `circle_polynomial` |
| `CircleWindingDef` | Definition of `circle_winding_number` |
| `UnilateralShiftDef` | Definition of `unilateral_shift` |
| `symbolHomotopyDef` | Definition of `circle_symbol_homotopy` |
| `CircleApproximation` | Circle polynomials approximate every continuous periodic symbol in the symbol norm — card |
| `ToeplitzBounded` | A continuous symbol defines a bounded Toeplitz operator with the stated matrix and operator norm bounded by the symbol supremum norm — card |
| `ToeplitzNormContinuity` | The operator-norm distance of two Toeplitz operators is bounded by the supremum distance of their symbols — card |
| `PolynomialSemicommutator` | For trigonometric symbols the Toeplitz product error has finite rank — card |
| `CompactSemicommutator` | For continuous symbols the Toeplitz product error is compact — card |
| `NonvanishingFredholm` | A continuous nonvanishing symbol gives a Fredholm Toeplitz operator — card |
| `ShiftIndex` | The symbol exp(it) acts as the unilateral shift, which is Fredholm of index −1 — card |
| `LoopWindingInteger` | The winding integral of a nonvanishing piecewise smooth periodic symbol equals the embedded winding integer — card |
| `SymbolHomotopyToPower` | A nonvanishing piecewise smooth symbol is homotopic through nonvanishing continuous symbols to its winding power — card |
| `ToeplitzIndex` | The Fredholm index of a nonvanishing piecewise smooth symbol is the negative winding number — card |
