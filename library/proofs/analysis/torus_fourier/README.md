# torus_fourier — periodic complex functions and their Fourier sequences

The period is 2π in every coordinate. The normalized integral divides by 2π in each iterated one-dimensional integral; the character at k is exp(i k·x), and coefficients use its complex conjugate. Integer frequencies are zero-filled outside the first n coordinates. Functions are likewise zero off the real n-vector carrier.

The normalized integral comes with its own calculus: congruence on the n-vectors, and linearity and the supremum bound for continuous periodic integrands. The one-period integral of a character, on which the characters' orthogonality rests, is path_integral's `CircleCharacterIntegral`. The lattice sum of (1+‖k‖²)^(−σ) is finite exactly when 2σ exceeds the dimension, and a sequence summable against ⟨k⟩ʳ synthesizes a function of class r with that sequence as its coefficients.

Smooth periodic functions correspond bijectively to rapidly decreasing frequency sequences. Integration by parts gives decay; one-dimensional completeness and iteration in the dimension give inversion, with uniform convergence of differentiated series. Parseval for smooth functions follows from this correspondence. Continuous periodic functions enter the uniform trigonometric approximation theorem used by Toeplitz operators.

## Members

| Member | Statement or role |
|---|---|
| `FrequencyLatticeDef` | Definition of `fourier_lattice` |
| `FrequencyLengthDef` | Definition of `frequency_length_squared` |
| `FrequencyBlockDef` | Definition of `fourier_block` |
| `PeriodShiftDef` | Definition of `torus_period_shift` |
| `periodicFunctionDef` | Definition of `torus_periodic` |
| `TorusClassDef` | Definition of `torus_class` |
| `SmoothPeriodicDef` | Definition of `torus_smooth` |
| `TorusIntegralDef` | Definition of `torus_integral` |
| `CharacterDef` | Definition of `torus_character` |
| `CoefficientsDef` | Definition of `torus_coefficients` |
| `RapidSequenceDef` | Definition of `rapid_sequence` |
| `SynthesisDef` | Definition of `torus_synthesis` |
| `TrigonometricPolynomialDef` | Definition of `torus_polynomial` |
| `TorusPartialDef` | Definition of `torus_partial` |
| `TorusIntegralCongruence` | The normalized integral depends only on the integrand's values at n-vectors — card |
| `TorusIntegralLinear` | The normalized integral is complex linear on continuous periodic functions — card |
| `TorusIntegralBound` | A continuous periodic function bounded by B has normalized integral of modulus at most B — card |
| `LatticeSummable` | The finite lattice sums of (1+‖k‖²)^(−σ) are bounded when n < 2σ — card |
| `SummableSynthesis` | A sequence summable against ⟨k⟩ʳ synthesizes a function of class r with that sequence as its coefficients — card |
| `ClassPartial` | A coordinate derivative of a function of class r+1 is of class r — card |
| `FrequencyBlocksFinite` | Each bounded frequency block is finite — card |
| `CharacterOrthogonality` | Normalized integration makes distinct active torus characters orthogonal, each with squared norm one — card |
| `CoefficientDerivative` | A coordinate derivative multiplies the Fourier coefficient by the positive imaginary frequency — card |
| `SmoothCoefficientsRapid` | Fourier coefficients of a smooth periodic function are rapidly decreasing — card |
| `CircleCompleteness` | A continuous periodic function in dimension one with all coefficients zero is zero — card |
| `FourierCompleteness` | In every dimension, continuous periodic functions are determined by their Fourier coefficients — card |
| `RapidSynthesis` | A rapid sequence synthesizes to a smooth periodic function with the original coefficients — card |
| `SmoothFourierInversion` | Fourier synthesis recovers every smooth periodic function — card |
| `UniformFourierConvergence` | Finite frequency-block sums of a rapid sequence converge uniformly — card |
| `SmoothParseval` | The Fourier sequence inner product equals the normalized integral pairing of smooth periodic functions — card |
| `TrigonometricApproximation` | Trigonometric polynomials uniformly approximate continuous periodic functions — card |
