# ring_of_integers — the full integer lattice of a number field

The integer ring is defined by monic relations over the integer image. A bounded trace-dual lattice supplies finite generation, and principal ideal domain freeness gives an integral basis and its full rational span.

## Members

| Member | Statement |
|---|---|
| `FinitelyGeneratedFieldSubmoduleFree` | An integer lattice in a number field has a finite integer basis whose size is at most the field degree. |
| `StableFullIntegerLattice` | The span of a finite rational basis over ℤ[x], for an algebraic integer x, is a full integer lattice preserved by multiplication by x |
| `IntegralTraceInInt` | The field trace of an algebraic integer is an integer scalar |
| `FieldNormFromIntegralBasis` | In an integral basis, the field norm of an algebraic integer is the integer determinant of its multiplication matrix, a matrix over the integers |
| `IntegralNormInInt` | The field norm of an algebraic integer lies in the integer image |
| `IntegralRationalBasisExists` | Every number field has a finite rational basis consisting of algebraic integers |
| `RingOfIntegersFractionField` | Every element of a number field is a quotient of two algebraic integers with nonzero denominator: the field is the fraction field of its ring of integers |
| `TraceDualFull` | The trace dual of a full integer lattice is full, and its trace bidual is the original lattice |
| `RingOfIntegersIntegerModule` | The ring of integers is a submodule of the field over the integer image, and a module over the integer image in its own right |
| `RingOfIntegersInTraceDual` | The integer ring contains the integer span of any set of algebraic integers and lies in that span's trace dual |
| `RingOfIntegersFreeRankN` | The integer ring is a full integer lattice with a finite basis of cardinality equal to the field degree |
| `IntegralBasisExists` | The ring of integers of a number field has an integral basis: an integer basis indexed by the numbers below its size |
| `NonzeroIdealFiniteIndex` | Every nonzero ideal has finite additive index and contains a positive integer whose integer-ring multiples remain in the ideal |
| `IntegralBasisDef` | `integral_basis`: ring_ops(A) → num → (num → A) → bool |
