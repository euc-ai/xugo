# ideal_norm — quotient cardinalities and norms of fractional ideals

The integral ideal norm is the cardinality of the actual quotient by the ideal. Invertible quotient preservation gives multiplicativity, and denominators extend the definition to positive rational norms of fractional ideals.

## Members

| Member | Statement |
|---|---|
| `IdealNormDef` | The quotient cardinality is total; finite positive norm laws require a nonzero integral ideal in a number field |
| `NumberIdealNormAsIdealIndex` | `number_ideal_norm(R, I) = ideal_index(restrict_ring(R, ring_of_integers(R)), I)`: the norm is the index of I in the ring of integers |
| `PrincipalIdealIndexAbsNorm` | The norm of a nonzero principal integral ideal equals the absolute rational value of its generator’s field norm |
| `IdealNormPositive` | A nonzero integral ideal has positive norm; the whole integer ring has norm one, and only it does |
| `IdealNormMultiplicative` | The norm of a product of nonzero integral ideals equals the product of their norms |
| `IdealNormAntitone` | A nonzero integral ideal contained in another integral ideal has at least its norm |
| `FractionalNormDef` | `fractional_ideal_norm`: field_ops(A) → set(A) → real |
| `FractionalNormExtension` | Compare two denominators by multiplying both scaled integral ideals to the common product denominator — card |
| `BoundedNormIdealsFinite` | A fixed norm bound admits only finitely many nonzero integral ideals |
