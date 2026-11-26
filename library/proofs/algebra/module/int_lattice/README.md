# int_lattice — the integers as scalars, integer subgroups, triangular bases and finite index

Coordinate projection and positive pivots give triangular bases for subgroups of finite-rank integer lattices. Remainder boxes then count finite quotients without requiring a full normal-form algorithm.

## Members

| Member | Statement |
|---|---|
| `IntegerLatticeDef` | `integer_lattice`: ring_ops(A) → set(A) → bool |
| `FullIntegerLatticeDef` | `full_integer_lattice`: field_ops(A) → set(A) → bool |
| `IntegerRationalIndependence` | A finite set is independent over the integer image exactly when it is independent over the rational image. |
| `IntegerBasisRationalSpan` | A finite integer basis is a rational basis of the rational span, whose dimension is the basis size. |
| `FullLatticeBasisRational` | An integer basis of a full integer lattice is a rational basis of the field, and on the lattice its rational coordinates are its integer ones |
| `IntegerTriangularBasisDef` | `integer_triangular_basis`: num → set(num → int) → num → (num → num → int) → (num → num) → bool |
| `integerRemainderBoxDef` | `integer_remainder_box`: num → (num → int) → set(num → int) |
| `SubmoduleFreeTriangular` | Every submodule of the integer vectors supported below n has a basis of at most n vectors with positive last pivots in increasing order. |
| `LinearCombinationCoordinate` | A coordinate of an integer combination of integer vectors is the same combination of their coordinates. |
| `TriangularQuotientRepresentatives` | Every coset has a unique representative whose coordinates lie between zero and the positive diagonal pivots. |
| `TriangularIndexProduct` | The finite index is the product of the positive diagonal entries of a full triangular basis. |
| `ConstantSumCardinalityMultiple` | In an integer module, summing one vector over a finite index set gives the vector times the number of indices. |
| `FiniteModuleOrderAnnihilates` | A finite integer module is annihilated by its order: card(M)·x = 0 for every vector x. |
| `IndexAnnihilatesQuotient` | Multiplying by the index of a finite-index submodule sends the whole module into the submodule. |
| `FiniteIndexPositive` | A submodule of an integer module with finitely many cosets has positive index. |
| `IntegerBasisSizeUnique` | Two finite bases of an integer module have the same size. |
| `NonzeroScalarInjective` | Multiplication by a nonzero integer is one-to-one on an integer module with a finite basis. |
| `IndexedBasisIsomorphism` | An indexed basis of n vectors identifies an integer module with the integer vectors supported below n. |
| `FullRankIffFiniteIndex` | A submodule has finite index exactly when it has a finite basis of the ambient rank. |
| `BoundedIndexSubmodulesFinite` | An integer module with a finite basis has only finitely many submodules of finite index at most n. |

## Integer scalar rings

The native integer ring is a principal ideal domain: every ideal is an
additive subgroup of the integers and its nonnegative additive generator
generates the ideal. The integer image of a field of characteristic zero
is a principal ideal domain whose fraction field is the rational image;
the ambient field is a module over each image. Restriction of scalars along
the integer map preserves submodules, spans and finite generation. In
characteristic zero the map is injective, so it also preserves independence
and bases.

| Member | Statement |
|---|---|
| `IntegerRingPrincipalIdealDomain` | The native integer ring is a principal ideal domain |
| `IntegerScalarRestriction` | In characteristic zero, restriction along the integer map preserves submodules, spans, bases and finite generation |
| `IntegerRationalImagesStructure` | The integer image is a principal ideal domain inside the rational image, whose fraction carrier it is |
| `IntegerRationalImageModules` | A field of characteristic zero is a module over its integer image and over its rational image |
