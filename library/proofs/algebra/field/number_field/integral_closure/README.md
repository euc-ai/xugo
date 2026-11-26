# integral_closure — the algebraic integers of a number field form an integrally closed subring

The algebraic integers of a number field are its elements integral over the integer image. Finitely many of them generate a finite module over the integer image (`FiniteIntegralAlgebra`), so the ring they generate consists of algebraic integers (`GeneratedSubringIntegral`): sums, negatives and products of algebraic integers are algebraic integers. The same finiteness carries integrality across a tower, so the ring of integers is integrally closed in its field, and a positive integer denominator brings every element of the field into it. The stable-module criterion behind these steps is the principal ideal domain chapter's (`IntegralPolynomialModule`, `StableModuleIntegral`).

## Members

| Member | Statement |
|---|---|
| `RingOfIntegersDef` | `ring_of_integers`: ring_ops(A) → set(A) |
| `IntegersAreIntegral` | Integer images, including zero and one, are algebraic integers |
| `FiniteIntegralAlgebra` | Finitely many algebraic integers generate a finite module over the integer image |
| `GeneratedSubringIntegral` | The ring finitely many algebraic integers generate over the integer image consists of algebraic integers |
| `IntegralAddNeg` | Algebraic integers are closed under sums and additive inverses |
| `IntegralMul` | Algebraic integers are closed under multiplication |
| `IntegralClosureSubring` | The algebraic integers form a subring of the number field containing its integer image |
| `IntegralTransitiveOverIntegers` | Integrality over a ring of algebraic integers implies integrality over the integer image |
| `IntegralClosureIntegrallyClosed` | The ring of integers is integrally closed in its number field |
| `ClearDenominator` | Every number-field element becomes an algebraic integer after multiplication by a positive integer |
