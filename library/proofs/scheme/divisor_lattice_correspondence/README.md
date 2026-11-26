# divisor_lattice_correspondence — closed divisors and invertible lattice pairs correspond on a smooth finite-field curve: lattice degree, local order and principal divisors

On a smooth finite-field curve the pair of a closed divisor (scheme/closed_divisor) has the divisor's degree for its lattice degree, the degree of scheme/curve_degree, and extension to the local ring at a closed point reads the divisor's coefficient there. So closed divisors correspond to invertible lattice pairs, degree to lattice degree, principal divisors to the scalings of the structure pair, linear equivalence to pair classes, and coefficients to orders.

## Definitions

| Member | Statement |
|---|---|
| `ClosedPrincipalDivisorDef` | `closed_principal_divisor`: ring_ops(A) → set(A) → set(A) → set(A) → A → prod(set(A), set(A)) → int |
| `ClosedDivisorEquivalentDef` | `closed_divisor_equivalent`: ring_ops(A) → set(A) → set(A) → set(A) → (prod(set(A), set(A)) → int) → (prod(set(A), set(A)) → int) → bool |

## Lattice degree

The ideal pair of a closed point has lattice degree minus its residue degree, by the Euler characteristic of a sub-pair: the two chart colengths less the overlap's, which cancels the second.

| Member | Statement |
|---|---|
| `ChartPointFiniteQuotient` | The ideal a closed point has in a chart has finite colength over the constants |
| `ClosedPointLatticeDegree` | The pair of a closed point has lattice degree minus its residue degree |
| `CurveDegreeOnInvertiblePairs` | Lattice degree is a monoid homomorphism from the invertible pairs to the integers |
| `ClosedPointPowerDegree` | The signed power n of a closed point has lattice degree n times its residue degree |
| `ClosedDivisorLatticeDegree` | The lattice degree of the pair of a closed divisor is the divisor's degree |

## Local order

Extension to the local ring at a closed point is a homomorphism on invertible pairs, killing the other closed points, so it reads a divisor's coefficient at the point.

| Member | Statement |
|---|---|
| `PointComponent` | The component of a pair in a point's chart keeps the structure pair, products, inverses and invertibility |
| `ChartPointsSeparate` | Another closed point's first component holds a function off the first component of a closed point proper in chart 0 |
| `PointsSeparate` | Another closed point's component in P's chart lies in the chart and holds a function off P |
| `LocalExtension` | Extension to the local ring at a closed point is a homomorphism on invertible pairs, takes P to the maximal ideal and other closed points to the ring |
| `LocalPowerInjective` | Distinct integers give distinct powers of the maximal ideal at a closed point |
| `SignedPowerMap` | A map multiplicative on c carries signed powers to signed powers of the images |
| `LocalDivisorPower` | The pair of a closed divisor extends to the signed power of the maximal ideal at minus its coefficient |
| `ClosedDivisorLocalPower` | If the pair of D is f⁻¹ times the structure pair, f times the local ring at P is the signed power of the maximal ideal at D(P) |
| `GeneratorOrderOne` | A generator of a prime point ideal, whose other generator is its multiple by a unit of the local ring, has order one |

## The correspondence

A pair and its inverse each meet the structure pair in an integral pair, so every invertible pair is the pair of one closed divisor.

| Member | Statement |
|---|---|
| `InvertiblePairLaws` | The invertible pairs under product and inverse: inverses are two-sided and unique |
| `ChartMeetInvertible` | The meet of an invertible fractional ideal with its chart is an invertible ideal |
| `InvertibleMeetInvertible` | The meet of an invertible pair with the structure pair is an invertible pair inside the charts |
| `ClosedDivisorPairInjective` | A closed divisor is determined by its pair |
| `InvertiblePairHasDivisor` | An invertible pair is the pair of exactly one closed divisor |
| `ClosedPrincipalDivisorPair` | The principal divisor of a nonzero f is closed, with pair f⁻¹ times the structure pair |
| `EffectiveDivisorOfSection` | A nonzero section s of an invertible pair X writes X as s times the pair of an effective closed divisor |
| `ClosedDivisorEquivalentIff` | Two closed divisors have one pair class exactly when they differ by a principal divisor |
| `ClosedPrincipalDivisorOrder` | The coefficient of a principal divisor at a closed point is the order of the function there |
| `WeightedDivisorLatticeCorrespondence` | Closed divisors correspond to invertible pairs, degree to lattice degree, principal divisors to scaled structure pairs, linear equivalence to pair classes, and coefficients to orders |
| `PrincipalDivisorDegreeZero` | A nonzero function has a closed divisor of degree zero |
