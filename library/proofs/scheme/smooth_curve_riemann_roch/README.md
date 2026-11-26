# smooth_curve_riemann_roch — Pic⁰ of a smooth finite-field curve is finite, its canonical divisor from a linear functional, and Riemann–Roch on closed divisors

Through the correspondence of closed divisors with invertible lattice pairs (scheme/divisor_lattice_correspondence), Pic⁰ of a smooth finite-field curve is finite, a nonzero linear functional constructs the canonical model on the given parameter even when it is inseparable, and Riemann–Roch for invertible pairs (scheme/serre_duality) reads on closed divisors with the dual sections identified through the canonical divisor.

## Definitions

| Member | Statement |
|---|---|
| `CanonicalDivisorDef` | `curve_canonical_divisor`: field_ops(A) → set(A) → A → set(A) → set(A) → set(A) → prod(set(A), set(A)) → int |

## Classes

Translating a degree-zero class by a divisor of degree at least g gives a class with a section, so an effective representative of a fixed degree, of which there are finitely many.

| Member | Statement |
|---|---|
| `EffectiveDivisorWeighted` | An effective closed divisor, its coefficients read as natural numbers, is weighted effective on the closed points, and its degree is the cast of the weighted degree |
| `DegreeZeroClassGroupFinite` | Pic⁰ of a smooth curve over a finite field is finite and nonempty |
| `ClassOfDifference` | The class of a difference of closed divisors is the quotient of their classes |

## The functional model

A nonzero k(t)-linear functional l on L pairs L with itself by l(xy). The dual of a chart over its polynomial ring is an invertible fractional ideal, and pairing identifies the dual of the overlap with the dualizing module. The parameter t may be inseparable: no trace enters and separability is never asked.

| Member | Statement |
|---|---|
| `FunctionFieldOverLine` | A smooth curve over its line: one finite set is a basis of the chart over k[t], of L over k(t) and of the overlap over k[t, 1/t] |
| `ChartFunctionalInvertible` | On a chart of a smooth curve the dual of the chart over its polynomial ring is an invertible fractional ideal |
| `OverlapDualIsomorphism` | The pairing identifies the dual of the overlap, valued in k[t, 1/t], with the dualizing container |
| `ChartDualInOverlapDual` | The dual of chart 0 valued inside k[t, 1/t] lies in the dual of the overlap |
| `DualizingFromLinearFunctional` | A nonzero k(t)-linear functional on L gives an invertible pair modelling the dualizing pair |

## Duality

The maps from a pair X into a dualizing model N are the multiplications by sections of N · X⁻¹, so the canonical divisor reads the dual sections of Riemann–Roch.

| Member | Statement |
|---|---|
| `SmoothCurveDualizingInvertible` | The dualizing pair of a smooth curve has an invertible model |
| `CanonicalDivisorModel` | The canonical divisor W is a closed divisor, its pair a dualizing model, of degree 2g − 2, with dim Hom(D, ω) = ℓ(W − D) |

## Riemann–Roch

Riemann–Roch for invertible pairs, read at closed divisors, with the dual sections identified through the canonical divisor.

| Member | Statement |
|---|---|
| `RiemannRochClosedDivisors` | Riemann–Roch on closed divisors: ℓ(D) − ℓ(W − D) = deg D + 1 − g, for W the canonical divisor |
| `SectionsByDivisorDegree` | ℓ(D) vanishes below degree 0 and is deg D + 1 − g above 2g − 2 |
