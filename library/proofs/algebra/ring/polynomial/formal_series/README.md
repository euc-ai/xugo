# formal_series — finite coefficient calculus for formal power series

A formal power series is its sequence of coefficients, and its product is the polynomial chapter's convolution `polynomial_mul`, whose laws hold for every sequence with values in the carrier; a power of a series is the polynomial chapter's `polynomial_pow`. Over any commutative ring the chapter adds the substitution T ↦ Tᵈ, with what it does to products, polynomials and the value at one, and the recurrence `series_recurrence(R, a, m)`: a(0) = 1, m(0) = 0 and $n \cdot a(n) = \sum_{0 < i \le n} m(i) \cdot a(n-i)$, that is T·a′ = m·a, where m is the counting sequence. The recurrence determines m from a over any commutative ring and a from m over a characteristic-zero integral domain, and the formal exponential solves it over a characteristic-zero field, where a series with a counting sequence is therefore the formal exponential of its counts over their indices. Counting sequences add over products, subtract over an invertible factor, multiply by r over r-th powers, go to their images under a ring homomorphism, and go to d times their substitution under T ↦ Tᵈ.

Every member binds its ring as a record. The same series read at the real ring, a simple pole at one and the zeta numerator of a Riemann–Roch count, are the chapter real/real_formal_series.

## Members

| Member | Statement |
|---|---|
| `SeriesRecurrenceDef` | `series_recurrence`: ring_ops(A) → (num → A) → (num → A) → bool |
| `SeriesSubstituteDef` | `series_substitute`: ring_ops(A) → (num → A) → num → num → A |
| `FormalExpDef` | `formal_exp_zero`: ring_ops(A) → (num → A) → num → A |
| `RecurrenceSumCongruence` | The recurrence sum at n reads only the coefficients below n: sequences agreeing below n give the same sum of m(i)·a(n − i) over 0 < i ≤ n |
| `RecurrenceDeterminesCounts` | A recurrence determines its counting sequence over any commutative ring |
| `RecurrenceDeterminesCoefficients` | Over a characteristic-zero integral domain, the recurrence determines the coefficient sequence |
| `FormalExpCoefficients` | Over a characteristic-zero field, the formal exponential satisfies its coefficient recurrence |
| `FormalExpOfCounts` | Over a characteristic-zero field, a series with counting sequence m is the formal exponential of m(n)/n, with zero at index zero |
| `EulerDerivativeProduct` | The Euler derivative, weighting the n-th coefficient by n, is a derivation for convolution |
| `RecurrenceEuler` | A recurrence is the Euler equation E(a) = m·a with a(0) = 1, m(0) = 0 and carrier-valued a and m |
| `RecurrenceProduct` | The counting sequence of a product of series is the sum of their counting sequences |
| `RecurrenceQuotient` | Removing an invertible factor from a product subtracts its counting sequence |
| `RecurrenceRingMap` | A ring homomorphism carries a recurrence to the recurrence of the images of a and m |
| `RecurrenceUnit` | The unit series has the zero counting sequence |
| `RecurrencePower` | The r-th power of a series has r times its counting sequence |
| `SeriesSubstituteAtMultiple` | Substituting Tᵈ (d > 0) puts the coefficient of Tʲ at the index d·j |
| `SeriesSubstituteOffMultiples` | After substituting Tᵈ, an index that is not a multiple of d has coefficient zero |
| `SeriesSubstituteBinomial` | Substituting Tᵈ (d > 0) into the binomial 1 − c·T gives 1 − c·Tᵈ |
| `SeriesSubstituteLinearFactor` | Substituting Tᵈ (d > 0) into 1 − T gives 1 − Tᵈ |
| `SeriesSubstituteIn` | Substituting Tᵈ keeps every coefficient of a carrier-valued sequence in the carrier |
| `SeriesSubstituteMul` | Substituting Tᵈ (d > 0) is multiplicative on carrier-valued sequences |
| `SeriesSubstitutePolynomial` | Substituting Tᵈ (d > 0) into a polynomial gives a polynomial with the same value at one |
| `RecurrenceSubstitute` | Substituting Tᵈ (d > 0) takes a counting sequence m to d times the substituted m |
| `EvalSeriesSubstitute` | Substituting T ^ d for the variable and evaluating at x is evaluating at x ^ d |
