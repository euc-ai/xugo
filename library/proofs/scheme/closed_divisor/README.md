# closed_divisor — closed divisors on a smooth finite-field curve: their pairs and degrees, and the factorization of an invertible pair inside the charts into closed points

A closed divisor of a smooth finite-field curve (scheme/smooth_curve) is an integer function on its closed points, nonzero at finitely many; its pair is the product of the powers of the ideal pairs of its points and its degree the sum of its coefficients weighted by residue degree. Every closed point is an invertible pair, and every invertible pair inside the charts is the ideal pair of exactly one effective closed divisor.

## Definitions

| Member | Statement |
|---|---|
| `ClosedDivisorDef` | `closed_divisor`: ring_ops(A) → set(A) → set(A) → set(A) → (prod(set(A), set(A)) → int) → bool |
| `ClosedDivisorDegreeDef` | `closed_divisor_degree`: ring_ops(A) → set(A) → set(A) → set(A) → (prod(set(A), set(A)) → int) → int |
| `ClosedDivisorPairDef` | The finite product on lattice pairs of `curve_divisor_pair`, read at closed points |

## Divisor arithmetic

The pair of a closed divisor is a finite product in the commutative monoid of invertible pairs and its degree a finite sum, both read at integer exponents, so the sum of two divisors is one fold over the union of the supports.

| Member | Statement |
|---|---|
| `CurveDivisorPairProduct` | A divisor with finite invertible support has as its pair the product of the powers of its points |
| `ChartPointInvertible` | The ideal a closed point has in a chart is an invertible fractional ideal inside the chart |
| `ChartIdealsInvertiblePair` | Invertible fractional ideals inside the two charts that generate one ideal of the overlap are an invertible pair |
| `ClosedPointInvertible` | A closed point of a smooth curve is an invertible pair |
| `ClosedDivisorPairProduct` | The pair of a closed divisor is invertible and the product of the powers of its closed points |
| `ClosedDivisorZero` | The zero divisor is closed, with the structure pair as its pair and degree 0 |
| `ClosedDivisorOfSupport` | A function supported in a finite set of closed points is a closed divisor |
| `ClosedDivisorAdd` | The sum of two closed divisors is closed, its pair the product of their pairs, its degree the sum of their degrees |
| `ClosedDivisorNegate` | −D is closed, its pair the inverse of the invertible pair of D, its degree −deg D |
| `ClosedDivisorSub` | The difference of two closed divisors is a closed divisor, its pair the pair of D over the pair of E, its degree the difference of their degrees |
| `ClosedDivisorPoint` | n·P is closed of degree n deg P, and −1·P has the pair P itself |

## Factorization

An invertible pair inside the charts lies under a closed point unless it is the structure pair. Dividing by that point lowers the colength, so strong induction on colength factors it, existence and uniqueness in one induction.

| Member | Statement |
|---|---|
| `InvertibleChartMember` | An invertible fractional ideal of a chart holds a nonzero member of the chart |
| `InvertibleChartIdeal` | An invertible fractional ideal inside a chart is a nonzero ideal of it |
| `PairBelowClosedPoint` | A pair under a closed point in a chart where the point is proper lies under it in the other chart |
| `ProperChartBelowPoint` | An invertible pair inside the charts with proper first component lies under a closed point proper in chart 0 |
| `ProperPairBelowPoint` | An invertible pair inside the charts other than the structure pair lies under a closed point |
| `ClosedPointInCharts` | The components of a closed point lie inside the two charts |
| `ClosedPointProper` | The structure pair lies under no closed point |
| `ClosedPointChartBelow` | A closed point under a closed point proper in chart 0 is that point |
| `ClosedPointBelowPoint` | Closed points are pairwise incomparable |
| `ChartIdealProduct` | A product of invertible ideals of a chart lies in its second factor, and a maximal ideal above it lies above a factor |
| `ClosedPointPrime` | A closed point above a product of invertible pairs inside the charts lies above a factor |
| `ChartDivideByIdeal` | The same division inside a chart of a smooth curve |
| `PairQuotient` | Quotients of invertible pairs are invertible, and multiplying and dividing by a pair cancel |
| `PairDivideByPoint` | An invertible pair inside the charts under a closed point divides by it to an invertible pair inside the charts of smaller colength |
| `EffectivePairIn` | The ideal pair of an effective divisor lies in every submonoid of invertible pairs holding its support |
| `PairProductIntegral` | A product of invertible pairs inside the charts is invertible and lies under its second factor |
| `EffectivePairIntegral` | The ideal pair of an effective divisor is an invertible pair inside the charts |
| `EffectivePairAvoidsPoint` | The ideal pair of an effective divisor lies under no closed point outside its support |
| `ClosedDivisorShift` | Raising a divisor by one at a closed point multiplies the pair of its negative by that point |
| `EffectiveDivisorLower` | An effective divisor nonzero at a point stays effective when lowered there by one |
| `EffectivePairBelowSupport` | The ideal pair of an effective divisor lies under each point of its support |
| `IntegralPairHasDivisor` | An invertible pair inside the charts is the ideal pair of exactly one effective closed divisor |
| `ClosedDivisorFactorization` | Closed points are invertible pairs, and an invertible pair inside the charts is the ideal pair of exactly one effective closed divisor |
