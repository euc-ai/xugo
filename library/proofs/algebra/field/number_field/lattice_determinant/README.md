# lattice_determinant — integer determinants as indices of full lattices

Determinants of matrices whose entries lie in the integer or the rational image inside a number field. A matrix over the integer image has its determinant there, and a matrix of rationals of size at most H has a determinant of size at most n! Hⁿ, each of the n! terms of its Leibniz expansion having size at most Hⁿ. Changing coordinates between two integer bases and back gives inverse integer matrices, so such a change has determinant plus or minus one. For a full lattice N inside a full lattice M, a triangular integer basis of N identifies the quotient M/N with a box of remainders, and comparing change-of-basis matrices turns the size of that box into the absolute determinant of the change from a basis of M to a basis of N: the index of N in M.

## Members

| Member | Statement |
|---|---|
| `DeterminantIntegralEntries` | A matrix over the integer image has its determinant in the integer image. |
| `DeterminantEntryBound` | Entries of rational absolute value at most H give determinant absolute value at most n! H^n. |
| `IntegerBasisChangeDetUnit` | Opposite integer change-of-basis matrices are inverses, so their determinants are integer units. |
| `LatticeIndexEqAbsDet` | A full lattice quotient is finite, and its index is the absolute rational determinant of the given basis change. |
