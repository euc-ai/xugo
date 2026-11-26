# finite_field — finite fields, Frobenius and finite linear counting

A finite field is a field record with finite carrier.
The ambient type may contain elements outside the carrier. Prime characteristic
is asserted on a ring record; Frobenius is its power map. A field's
characteristic is zero or a prime, and at either an integer maps to zero exactly
when the characteristic divides it, so fields are compared by the kernels of
their integer maps. The separability argument reads the quotient by the polynomial as a finite field. Inside
an algebraically closed field (algebra/field/algebraic_closure) above a finite
subfield of q elements, the points fixed by the q^m-th power are the subfield
of q^m elements. The field of p elements is the integers modulo p.

The binomial expansion and prime characteristic give Frobenius and perfectness.
Separability is argued apart from them: the quotient by an irreducible
polynomial is a finite field of Q points, Q a positive power of the
characteristic; the class of X is fixed by the Q-th power, and so the
polynomial divides the separable X^Q−X. Counting over a finite field
uses finite bases of modules on sets. The square laws assume 2 ≠ 0. The prime
binomial divisibility theorem is `nat_prime.PrimeDividesBinomial`.

## Definitions

| Member | Meaning |
|---|---|
| `FiniteFieldDef` | `finite_field`: field_ops(A) → bool |
| `FieldSizeDef` | `field_size`: field_ops(A) → num |
| `PrimeCharacteristicDef` | `ring_prime_characteristic`: ring_ops(A) → num → bool |
| `FieldCharacteristicDef` | `field_characteristic(F, p)`: F has characteristic zero at p = 0, or prime characteristic p; the field axioms are stated separately |
| `SameCharacteristicDef` | `same_characteristic(F, G)`: the integer maps of the two fields have the same kernel |
| `FrobeniusPowerDef` | `frobenius_power`: ring_ops(A) → num → A → A |
| `FiniteConstantsDef` | `finite_constants(R, q, m)`: the points of the carrier fixed by the q^m-th power |
| `LocallyFiniteFieldDef` | `locally_finite_field(F)`: every finite set of elements of the field F lies in a finite subfield |

## Counting

| Member | Statement |
|---|---|
| `FiniteExtensionSize` | A finite extension of degree d of a finite subfield of q elements has q^d elements. |
| `FiniteSubfieldSize` | A finite subfield E above k has $\operatorname{card}(k)^{[E:k]}$ points. |
| `AlgebraicOverFiniteLocallyFinite` | A field algebraic over a finite subfield is locally finite. |
| `FiniteDimensionalSpaceSize` | A finite-dimensional k-module of dimension n has q^n elements. |
| `ProjectiveCount` | The one-dimensional subspaces satisfy $\lvert P(V) \rvert \cdot (q-1) = q^{\dim(V)} - 1$. |

## Frobenius

| Member | Statement |
|---|---|
| `BinomialTheoremRing` | The binomial expansion holds in a commutative ring on a set. |
| `FrobeniusAdditive` | In prime characteristic p, (a+b)^p=a^p+b^p. |
| `FrobeniusRingHomomorphism` | The p^n power map is a ring endomorphism. |
| `FrobeniusFixesIntegers` | In characteristic q, the q-th power map fixes the image of every integer. |
| `FiniteFieldPerfect` | Each p^n-th power map on k is bijective. |
| `PolynomialRingCharacteristic` | The polynomials over a ring of prime characteristic p have characteristic p |
| `PowersInsideSubfield` | A subfield holds the p-th powers of its points |

## Polynomials

| Member | Statement |
|---|---|
| `XPowerMinusXCoefficient` | The coefficient of X^Q−X at i is that of X^Q less that of X. |
| `XPowerMinusXOver` | X^Q−X is a polynomial over a commutative ring R. |
| `XPowerMinusXDegree` | For Q>1, X^Q−X has degree Q and coefficient one at Q. |
| `XPowerMinusXDerivative` | Where Q·1=0, the derivative of X^Q−X is the constant −1. |
| `XPowerMinusXSeparable` | Where Q·1=0, X^Q−X is separable. |
| `XPowerMinusXEval` | At x in R, X^Q−X takes the value x^Q−x. |
| `XPowerMinusXRoots` | The points fixed by the q^m-th power are the roots of $X^{q^m} - X$. |
| `FiniteConstantsBound` | Where q^m > 1, the q^m-th power fixes at most q^m points of a field. |
| `IrreducibleOverFiniteFieldSeparable` | An irreducible polynomial over a finite field has nonzero derivative and is separable. |
| `QuotientByIrreducibleIsFiniteField` | k[X]/(p) is a field with $q^{\deg(p)}$ elements. |
| `FiniteConstantsRootPolynomial` | $X^{q^m} - X$ is a polynomial over every subfield, and its roots in M are `finite_constants(q, m)` |

## Squares

| Member | Statement |
|---|---|
| `FiniteFieldSquares` | In a finite field with 2≠0, half the nonzero elements are squares and a nonzero nonsquare exists. |
| `SquaresAreHalf` | When 2≠0, the nonzero squares of a finite field of q elements number $\frac{q-1}{2}$, and q − 1 is twice that number. |
| `RootsOfUnityBound` | For n > 0, a field has at most n n-th roots of one. |
| `HalfPowerRootsAreSquares` | When 2≠0, the roots of $x^{\frac{q-1}{2}} = 1$ in a finite field are exactly the nonzero squares. |
| `FiniteFieldEulerCriterion` | Euler's criterion: when 2≠0, a nonzero element to the power $\frac{q-1}{2}$ is 1 on the squares and −1 off them. |
| `SquareOrTwistedSquare` | In a finite field with 2≠0, for a nonzero nonsquare e and d≠0, exactly one of d and ed is a square. |
| `SquareRootsWithTwistTotalTwo` | In a finite field with 2≠0, for a nonzero nonsquare e, every d and its twist ed have two square roots between them. |

## Structure

| Member | Statement |
|---|---|
| `FieldCharacteristicCases` | A field has characteristic zero or a prime characteristic. |
| `IntegerMapKernel` | In a field of characteristic p, an integer maps to zero exactly when p divides it. |
| `IntegerMapEqIff` | In a field of characteristic p, two integers have the same image exactly when they are congruent mod p. |
| `OddCharacteristicTwoNonzero` | In a field of odd prime characteristic, 1 + 1 ≠ 0. |
| `SameCharacteristicFromCharacteristic` | Two fields of one characteristic send the same integers to zero. |
| `FiniteFieldCharacteristic` | A finite field has prime characteristic. |
| `PrimeSubfield` | The multiples of one form a p-element subfield. |
| `FiniteFieldSizePower` | A finite field in characteristic p has size p^e with e>0. |
| `PrimePowerVanishes` | In a commutative ring of prime characteristic p, a positive power of p exceeds one and annihilates one. |
| `PrimeSizeCharacteristic` | A field with a prime number p of elements has characteristic p. |
| `IntegerMapOnto` | In a field with a prime number p of elements, every element is the image of an integer. |
| `FiniteFieldLagrange` | For z≠0 in k, $z^{q-1} = 1$. |
| `FiniteFieldFixedByFrobenius` | Every z∈k satisfies z^q=z. |
| `FiniteSubfieldPrimePower` | A finite subfield has p^n elements, n>0 and at least two, p the characteristic of the ambient field. |
| `SubfieldFrobeniusPoints` | For a finite subfield k of q elements, a point x of the field has x^q=x exactly when x∈k. |
| `FrobeniusFixedField` | Inside any overfield, the roots of X^q−X are exactly k. |
| `FrobeniusConstantAutomorphism` | On a finite extension l of a finite subfield k with q elements, c↦c^q is an automorphism of l over k. |
| `SquareFieldFrobenius` | When a finite subfield has size s², raising to the s-th power is a ring map of the whole field and an involution of the subfield. |

## One generator

A finite field over a subfield is generated by one point, by a count: a nongenerator of degree e is fixed by the q^e-th power, which fixes at most q^e points, and these bounds for 0 < e < d sum to less than q^d.

| Member | Statement |
|---|---|
| `FiniteSubfieldSimple` | A finite subfield l above a subfield k is k(z) for one point z of l. |

## Inside an algebraically closed field

| Member | Statement |
|---|---|
| `FiniteConstantsSubfield` | Above a finite subfield k of a closed field, m>0, the fixed points of the card(k)^m-th power are a subfield holding k with card(k)^m points. |
| `ClosedFieldInfinite` | An algebraically closed field is infinite. |
| `FiniteConstantsImage` | A ring map of a closed field M into a field N carries the subfield of q^m elements of M onto the points of N fixed by the q^m-th power, q = \|k\|; N need not be closed. |
| `FiniteConstantsMono` | m∣n puts the fixed points of the q^m-th power among those of the q^n-th. |
| `FiniteConstantsAlgebraic` | Where q^m is not one, a point fixed by the q^m-th power is algebraic over every subfield. |
| `FiniteSubfieldPowerEndomorphism` | Above a finite subfield k, m > 0, card(k)^m exceeds one, its power map is a ring endomorphism, and it is zero as a numeral of M |
| `FiniteConstantsInClosure` | The points fixed by the \|k\|^m-th power, m > 0, lie in the algebraic closure of k |
| `FiniteConstantsShiftedPower` | Where e divides m - 1, the q^m-th power acts as the q-th power on the points fixed by the q^e-th power |
| `FiniteConstantsFermat` | Where q^s > 1, a positive multiple of q^s − 1 as exponent sends a point fixed by the q^s-th power to one, or to zero at zero. |
| `FiniteSubfieldInConstants` | A finite subfield of q^m points lies among the fixed points of the q^m-th power |
| `BoundedDegreeInConstants` | over a finite subfield k, an element of degree at most D lies in the field of q^s elements once every positive m ≤ D divides s |
| `FiniteSubfieldAlgebraic` | A member of a finite subfield is algebraic over every subfield |
| `FiniteSubfieldAtLeastTwo` | A finite subfield has at least two elements |
| `FrobeniusOfFiniteSubfield` | The card(k)-th power is a ring endomorphism of M for a finite subfield k |
| `FiniteConstantsContained` | Inside a closed field, the subfield of q^d elements lies in that of q^n elements exactly when d divides n |
| `FiniteConstantsAutomorphisms` | The subfield of q^d elements has degree d over k and d automorphisms over k |
| `FiniteConstantsTower` | finite_constants(R, q^r, e) = finite_constants(R, q, r·e) |

## The prime field

| Member | Statement |
|---|---|
| `IntegerPrincipalIdeal` | The ideal generated by a natural integer p consists of its integer multiples. |
| `IntegerPrimeIdealMaximal` | A prime p generates a maximal ideal of the integers. |
| `PrimeFieldOn` | The integers modulo a prime p are a finite field with p points. |
| `CongruenceCancel` | Modulo a prime p, a factor that p does not divide cancels from a congruence. |
| `SquareModIff` | In a field with a prime number p of elements, an integer is a square mod p exactly when its image is a square in the field. |

