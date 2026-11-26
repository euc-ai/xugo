# real_formal_series — formal power series over ℝ: a simple pole at one and the zeta numerator

A real formal power series is its sequence of coefficients `num → real`, multiplied by the polynomial chapter's convolution `polynomial_mul` and substituted T ↦ Tᵈ by algebra/ring/polynomial/formal_series' `series_substitute`, both read at the real ring. The chapter works with a simple pole at one, $a = \frac{P}{(1-T) \cdot Q}$ with P and Q polynomials not vanishing at one and Q(0) ≠ 0: substitution keeps it, and a substitution b(Tᵈ) = a(T)ᵈ between two such series forces d = 1. A series supported on the multiples of d whose tail is geometric less a constant is cleared to a polynomial by (1 − Tᵈ)(1 − qᵈTᵈ) and has a simple pole at one, through the series B with A = B(Tᵈ). For the zeta numerator (1 − T)(1 − qT)·A of a Riemann–Roch count A the chapter gives its support through degree 2g, its constant coefficient and value at one — reaching genus zero through zero extension to negative integer indices — and the reciprocity of its coefficients.

The members read the real ring's components through the family's instance, and a bare `&n` reads as a real (`family.go`).

## Members

| Member | Statement |
|---|---|
| `ZetaNumeratorCoefficientDef` | `zeta_numerator_coefficient`: num → (int → real) → num → real |
| `SeriesSimplePoleDef` | `series_simple_pole_one`: (num → real) → bool |
| `SimplePoleSubstitute` | Substituting Tᵈ (d > 0) into a series with a simple pole at one gives a series with a simple pole at one |
| `SimplePolePowerSubstitution` | If a and b have simple poles at one and b(Tᵈ) = a(T)^d with d > 0, then d = 1 |
| `EventuallyConstantDifference` | A real series equal to C from M on, times 1 − T, vanishes from M + 1 on, is a polynomial, and takes the value C at one |
| `PeriodicTailRationality` | A series on the multiples of d with an eventually geometric tail times (1 − Tᵈ)(1 − qᵈTᵈ) is a polynomial, and the series has a simple pole at one |
| `RiemannRochNumerator` | The numerator is supported through degree 2g, equals (1−T)(1−qT)A, has constant coefficient 1, and evaluates to h at one |
| `RiemannRochReciprocity` | When the count satisfies the Riemann–Roch functional equation, the numerator's coefficients p_n = zeta_numerator_coefficient(q, a, n) satisfy $q^g \cdot p_n = q^n \cdot p_{2g-n}$ for n ≤ 2g |
| `RealIntegralDomain` | The ring of reals is an integral domain on its carrier |
| `RealCharacteristicZero` | The ring of reals has characteristic zero |
| `RealFormalExpOfCounts` | A real series with counting sequence m is the formal exponential of m(n)/n, with zero at index zero |
