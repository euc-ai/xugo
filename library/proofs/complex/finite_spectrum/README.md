# finite_spectrum — finite complex products and growth of power sums

A finite spectrum is an indexed sequence of complex numbers. Its reciprocal product retains repeated reciprocal roots and has a unit empty product. The Euler derivative of the chapter formal_series, read at the ring ℂ, turns multiplication into addition of counting sequences, and a geometric inverse permits subtraction of a denominator's counting sequence.

An eventually bounded sum of distinct exponentials with nonzero coefficients has every base in the closed unit disk. Equal spectral values are grouped with their positive multiplicities, so power sums bounded along an arithmetic progression bound their bases too, at any radius. A common power absorbs every root-of-unity collision; the curve chapters apply that power and the bound at radius √q together.

Repeated linear division gives the reciprocal-root factorization, retaining multiplicities. `ComplexPolynomialSplitting` joins that with the root theorem of complex_polynomial in the chapter's final splitting statement.

## Reciprocal products and recurrence

| Member | Statement |
|---|---|
| `PowerSumDef` | `finite_power_sum`: the sum of the m-th powers of a finite indexed spectrum |
| `ReciprocalProductDef` | `reciprocal_product`: the finite product of the factors 1 − a(i)T |
| `ReciprocalProductClauses` | Empty and successor clauses for reciprocal products |
| `ReciprocalProductCongruence` | Equal spectrum entries below the product length give equal reciprocal products |
| `PowerSumClauses` | Empty and successor clauses for spectral power sums |
| `ReciprocalLinearConvolution` | Multiplication by 1 − rT takes the coefficient p(n) to p(n) − r·p(n − 1), the second term absent at n = 0 |
| `ReciprocalLinearGeometricInverse` | A reciprocal linear factor times its geometric series is one |
| `ReciprocalDenominatorInverse` | The two geometric series invert the denominator (1 − T)(1 − qT) |
| `ReciprocalLinearRecurrence` | A reciprocal linear factor has negative powers as its counting sequence |
| `ReciprocalProductRecurrence` | A finite reciprocal product has the negative spectral power sums as its counting sequence |
| `ReciprocalProductLogDerivative` | A series c with (1 − T)(1 − qT)c a reciprocal product has counting sequence qᵐ + 1 minus the spectral power sum |
| `ReciprocalProductOfCounts` | A series c with counting sequence qᵐ + 1 minus the spectral power sum has (1 − T)(1 − qT)c equal to the reciprocal product: the converse of `ReciprocalProductLogDerivative` |

## Growth of exponential sums

| Member | Statement |
|---|---|
| `RootOfUnityRatiosKilledByPower` | A positive multiple R of a prescribed exponent makes every collision at a positive exponent already occur at R |
| `BoundedScaledPowers` | An eventually bounded nonzero scalar multiple of complex powers has base modulus at most one |
| `FiniteExponentialSumDifference` | Subtracting a chosen base times the sum from its shift deletes that base and multiplies the remaining coefficients by the base differences |
| `BoundedFiniteExponentialSumGrowth` | Every base of an eventually bounded finite exponential sum with injective bases and nonzero coefficients has modulus at most one |
| `BoundedExponentialSumGrowth` | An eventually bounded indexed sum of exponentials with distinct bases and nonzero coefficients has every base in the closed unit disk |
| `BoundedProgressionPowerSums` | Bounded progression power sums force every base into the closed unit disk when h-th powers separate distinct spectral values |
| `PowerSumModulusBound` | If s complex numbers all have modulus at most c, their m-th power sum has modulus at most s·c^m |
| `ScaledProgressionModulusBound` | Power sums along the multiples R(1 + hn) that are $O(c^{R(1+hn)})$ put all nonzero bases in the closed disk of radius c when a collision of R·h-th powers is already one of R-th powers |
| `ProductModulusAtBound` | Complex numbers of modulus at most c > 0 whose s-fold product has modulus c^s all have modulus c |

## Reciprocal products as polynomials

| Member | Statement |
|---|---|
| `ReciprocalLinearValue` | The reciprocal linear factor 1 − rT is a polynomial whose value at z is 1 − rz |
| `ReciprocalProductOver` | A reciprocal product is a polynomial |
| `ReciprocalProductZero` | A zero of the reciprocal product of a(0), …, a(s−1) is the reciprocal of one of them |
| `ReciprocalProductTop` | A reciprocal product of s factors vanishes past degree s, and its degree-s coefficient is (−1)^s times the product of the a(i) |
| `ReciprocalReverseRoot` | Each a(i), i < s, is a root of the reversed reciprocal product of a(0), …, a(s−1) |

## Reciprocal-root factorization

| Member | Statement |
|---|---|
| `ComplexPolynomialReciprocalFactorization` | A complex polynomial with nonzero constant coefficient is that coefficient times a reciprocal product of nonzero reciprocal roots |
| `ComplexPolynomialSplitting` | Every nonconstant complex polynomial has a root; with nonzero constant coefficient it is that coefficient times a reciprocal product of nonzero reciprocal roots |
