# curve_zeta — closed-divisor counting and the zeta numerator of a smooth curve

Effective divisors, their classes and the point counts over the constant extensions first give the logarithmic recurrence that relates the effective counts to the point counts. Periodic rational tails prove a simple pole before the divisor index is shown to be one. A single coefficient-defined integer numerator then carries rationality, reciprocity and all reciprocal-root trace formulas.

## Definitions

| Member | Statement |
|---|---|
| `degreeClassFibreDef` | `curve_degree_classes`: the classes of the invertible pairs of degree n |
| `divisorIndexDef` | `curve_divisor_index`: the positive generator of the degrees of the closed divisors, chosen by ε |
| `CurveEffectiveCountDef` | `curve_effective_count`: ring_ops(A) → set(A) → set(A) → set(A) → set(A) → int → real |
| `CurveZetaNumeratorDef` | `curve_zeta_numerator`: ring_ops(A) → set(A) → set(A) → set(A) → set(A) → num → real |
| `CurveReciprocalRootsDef` | `curve_reciprocal_roots`: an indexed family of 2g nonzero complex numbers whose reciprocal product is the numerator, multiplicities retained |

## Effective divisors and the Euler product

The sections of a divisor, up to constants, are the effective divisors of its class, so each class holds a projective space's worth of them. The effective counts themselves are the coefficients of an Euler product over the closed points, whose logarithmic derivative reads the extension point counts.

| Member | Statement |
|---|---|
| `ConstantsAtLeastTwo` | The constants of a curve have more than one element |
| `PairMultiplesEqIff` | Two nonzero multiples of an invertible pair agree exactly when their multipliers differ by a constant |
| `SectionLinesCount` | The lines of sections of an invertible pair are finite, and their number times q − 1 is q^ℓ − 1 |
| `EffectiveDivisorsInClass` | The effective divisors of a class are finite, and (q − 1) times their number is q^ℓ − 1 for ℓ the dimension of the sections |
| `ZetaEulerProductAndLogDerivative` | The effective counts satisfy the logarithmic recurrence with the extension point counts, and each is its Euler-product coefficient over the closed points |

## The divisor index

The rationality of the zeta series comes first and needs no divisor of degree one. A constant extension of degree the index then compares two simple poles, which forces the index to be one.

| Member | Statement |
|---|---|
| `DivisorDegreeImage` | The index is positive and the degrees of the closed divisors are exactly its multiples |
| `DegreeClassTranslation` | Translation by the class of an invertible pair X carries Pic⁰ one-to-one onto the classes of the degree of X |
| `DivisorDegreeClasses` | The index is positive and attained by a closed divisor; the classes of degree n are finite, as many as Pic⁰ when the index divides n and none otherwise |
| `InDegreeClasses` | A class has degree n exactly when it is the class of a closed divisor of degree n |
| `ClassComplementBijection` | Multiplying the class of a closed divisor E by inverses carries the classes of degree n one-to-one onto those of degree deg E − n |
| `ClassHasOneDegree` | A closed divisor whose class has degree n has degree n |
| `EffectiveCountOfDivisors` | The effective divisors of degree n are finite, and the effective count of degree n counts them |
| `EffectiveCountOverClasses` | The effective count of degree n is the cast of the sum, over the classes of degree n, of the effective divisors each class holds |
| `EffectiveCountTail` | Past degree 2g − 2, in a degree the index divides, q − 1 times the effective count is $h(q^{n+1-g} - 1)$ |
| `ZetaSimplePole` | With d the index, the series of effective counts has a simple pole at one, is cleared to a polynomial by 1 − Tᵈ and 1 − qᵈTᵈ, and vanishes off the multiples of d |
| `ConstantExtensionCurve` | The curve over the constants with q^r elements is a smooth curve in the composite field, and those constants have q^r elements |
| `IndexBaseChangeZetaIdentity` | For r dividing the divisor index, the zeta series of the curve over the constants with q^r elements, read at T^r, is the r-th power of its zeta series |
| `DegreeOneDivisorExists` | The divisor index of a smooth curve over a finite field is one, so the curve has a closed divisor of degree one |

## Rationality and the functional equation

Index one puts every degree in the tail, which gives the numerator its integrality, its bound and its value at one. Riemann–Roch relates the effective counts in degrees n and 2g − 2 − n once the classes of the two degrees are paired by the class of the canonical divisor, and that symmetry is the numerator's reciprocity.

| Member | Statement |
|---|---|
| `ZetaNumeratorRationality` | The numerator is an integer polynomial of degree at most 2g with constant term one and value h at one, and it is (1 − T)(1 − qT) times the series of effective counts |
| `CanonicalClassCountingSymmetry` | With $z = q^{n+1-g}$, (q − 1)(N(n) − z·N(2g − 2 − n)) = h(z − 1) for the effective counts N, at every integer n |
| `CurveZetaFunctionalEquation` | The numerator has degree exactly 2g and top coefficient q^g, and its coefficients pair across 2g by powers of q |

## Reciprocal roots

Over ℂ the numerator is a reciprocal product. Its logarithmic derivative and the uniqueness of a counting sequence then turn the Euler recurrence into power sums of the reciprocal roots, and the same argument at the extended counts replaces each root by its r-th power.

| Member | Statement |
|---|---|
| `ComplexZetaRecurrence` | The complexified zeta series has the point counts as counting sequence |
| `ComplexZetaProduct` | Over ℂ the numerator is (1 − T)(1 − qT) times the zeta series, in the reciprocal linear form of finite_spectrum |
| `CurveReciprocalRootsExist` | The numerator has reciprocal roots: 2g nonzero complex numbers whose reciprocal product it is |
| `PointCountPowerSum` | The trace formula: the point count over the degree-m extension is q^m + 1 less the m-th power sum of the reciprocal roots |
| `ExtensionReciprocalRoots` | The r-th powers of the reciprocal roots are the reciprocal roots over the constants with q^r elements |
| `CurvePointCountTraceFormula` | Reciprocal roots exist, and any choice of them computes the point counts, has product q^g, gives the numerators of the constant extensions, and lies among the roots of the reversed numerator |
