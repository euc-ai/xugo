# ideal_factorization — finite-height ideal factorization and exponent arithmetic

A finite index or a finite vector-space colength bounds the chains of ideals above an ideal. When every nonzero ideal has finite index, every nonzero ideal contains a product of nonzero primes — in any commutative ring, as are the laws of the exponent products of ideals (`ideal_exponent_product`) — and, inside a field, nonzero primes are maximal (`quotient_ring.FiniteIndexPrimeMaximal`) and an element with a common denominator for its powers is integral; the prime product makes the inverse of a nonzero maximal ideal strictly larger than S and, S being integrally closed, makes the maximal ideal invertible. Dividing by an invertible maximal ideal moves strictly upward, giving factorization by height induction; uniqueness uses cancellation. Integer exponents then describe bounded fractional ideals and their free abelian group. Conversely, a subring with L as its field of fractions whose nonzero ideals are all invertible is integrally closed: an element integral over it multiplies the bounded, hence invertible, fractional ideal S[z] into itself, and only S does that.

Localization is handled by denominator saturation. An element outside a maximal ideal is a unit modulo every power, so a denominator power cannot add elements of S to the power; leastness of ideal span then gives extension and contraction.

## Members

| Member | Statement |
|---|---|
| `idealChainDef` | `ideal_chain`: ring_ops(A) → set(A) → (num → set(A)) → num → bool |
| `FiniteIdealHeightDef` | `finite_ideal_height`: ring_ops(A) → set(A) → bool |
| `IdealHeightDef` | Use only on an ideal with bounded chain length; otherwise Hilbert choice carries no maximum assertion |
| `IdealExponentProductDef` | `ideal_exponent_product`: ring_ops(A) → (set(A) → num) → set(A) |
| `IdealExponentProductIntegral` | In a commutative ring, a finite exponent product of ideals is an ideal |
| `IdealExponentProductZero` | The zero exponent vector has product R.carrier for arbitrary ring operations |
| `IdealExponentProductSplit` | In a commutative ring, one full power splits from a finite exponent product of ideals, leaving its exponent zero |
| `IdealExponentProductInFactor` | In a commutative ring, a finite exponent product of ideals lies in each ideal it raises to a positive power |
| `IdealExponentProductIncrement` | In a commutative ring, raising one exponent by one multiplies a finite exponent product of ideals by that ideal |
| `IdealExponentProductAdd` | In a commutative ring, adding finite natural exponent vectors multiplies their exponent products of ideals |
| `IdealProductSubsetPrime` | In a commutative ring, a prime ideal containing a finite exponent product of ideals contains one of its supported factors |
| `IdealExponentProductInvertible` | Finite exponent products of integral invertible ideals are invertible |
| `IdealInductionByFiniteQuotient` | In a commutative ring whose nonzero ideals have finite quotient, strong induction on the index gives induction from larger nonzero ideals |
| `AlmostIntegralIsIntegral` | A common nonzero denominator for all powers forces integrality when nonzero ideals have finite quotient |
| `IdealContainsNonzeroPrimeProduct` | In a commutative ring whose nonzero ideals have finite quotient, every nonzero ideal contains a finite product of nonzero prime ideals, by induction on the index |
| `MaximalInverseStrict` | The inverse of a nonzero maximal ideal strictly contains the subring |
| `NonzeroIdealStabilizer` | An ambient scalar stabilizing a nonzero ideal belongs to the integrally closed subring |
| `NonzeroMaximalInvertible` | Every nonzero maximal ideal is invertible |
| `DivideByInvertibleIdeal` | Dividing I⊆M by an invertible integral ideal M gives a nonzero integral ideal J⊇I with I=MJ |
| `IntegralMulAsFractional` | Integral and fractional ideal multiplication agree for integral ideals |
| `IntegralPowAsFractional` | Natural powers of an integral ideal agree under integral and fractional ideal multiplication |
| `IdealExponentProductAsFractional` | A finite exponent product of integral ideals at natural exponents is the fractional exponent product at the same exponents read as integers |
| `InvertibleMulCancel` | An invertible fractional factor cancels from a product equation |
| `IntegralFractionalProduct` | Products of integral ideals stay integral and lie in either factor |
| `InvertibleStableChainStep` | A proper invertible ideal fixing I extends every ideal chain above I |
| `DivideByMaximalStrict` | Dividing by an invertible maximal ideal strictly enlarges a nonzero ideal of finite height |
| `IdealFactorizationExists` | A nonzero ideal of finite height factors into invertible nonzero maximal ideals when the maximal ideals containing it are invertible |
| `IdealFactorizationUnique` | Two finite exponent vectors of invertible maximal ideals with equal products are equal |
| `NonzeroIdealInvertible` | Every nonzero ideal is invertible when nonzero ideals have finite height and nonzero maximal ideals are invertible |
| `FractionalIdealInvertibleIffBounded` | when every nonzero integral ideal of `S` is invertible, `invertible_fractional(field_ring(L), S, I) ⇔ bounded_fractional(field_ring(L), S, I)` |
| `InvertibleIdealsIntegrallyClosed` | A subring with L as its field of fractions whose nonzero ideals are all invertible is integrally closed in L |
| `IdealContainmentByExponents` | For finite exponent vectors v, w of invertible maximal ideals, the product of v lies in the product of w exactly when w ≤ v at every ideal — card |
| `FiniteQuotientIdealHeight` | An ideal I of a commutative ring R with finite quotient R/I has finite height: every strict step of a chain above I lowers its index |
| `FiniteColengthIdealHeight` | An ideal of finite colength has finite height, bounded by its quotient dimension over the scalar subfield |
| `GeneratedModuloFiniteColength` | an ideal I above an ideal H whose quotient is finite-dimensional over a subfield k is generated by finitely many of its members modulo H |
| `IdealHeightMaximum` | Bounded ideal height is attained by a chain and bounds every chain length |
| `IdealHeightStrict` | Strict ideal inclusion lowers finite ideal height |
| `QuotientByMaximalStep` | For I ⊆ m with m an invertible maximal ideal, the index of I is the index of m times the index of I·m⁻¹ |
| `fractionalExponentProductDef` | `fractional_exponent_product`: ring_ops(A) → set(A) → (set(A) → int) → set(A) |
| `maximalExponentVectorsDef` | `maximal_exponent_vectors`: ring_ops(A) → set(set(A) → int) |
| `fractionalExponentsDef` | `fractional_exponents`: ring_ops(A) → set(A) → set(A) → (set(A) → int) |
| `FractionalExponentArithmetic` | Split positive and negative exponents into integral products and cancel common maximal factors — card |
| `FractionalExponentsUnique` | Clear a common denominator and subtract the exponent functions of the resulting integral ideal and denominator ideal — card |
| `FractionalIdealsFreeAbelian` | The unique finite integer exponent function is inverse to the product map — card |
| `ComaximalDecomposition` | Comaximal ideals write one as a member of each |
| `ComaximalIntersectionIsProduct` | Comaximal ideals meet in their product: `I ∩ J = ideal_mul(c, I, J)` |
| `MaximalPowerLocalization` | Inverting an element outside a maximal ideal leaves every power unchanged after contraction |
| `DivisionShrinksColength` | Dividing an invertible ideal by an invertible ideal above it does not raise the colength, and lowers it unless the divisor is the ring |
