# field_norm — determinants of multiplication in finite field extensions

The norm is the determinant of multiplication on the finite vector space of a field extension. Its basis formula, multiplicativity, scalar law and vanishing criterion use the general determinant interface; positive extension degree is explicit.

## Members

| Member | Statement |
|---|---|
| `FieldNormDef` | `field_norm`: ring_ops(A) → set(A) → A → A |
| `FieldNormFromBasis` | The norm is the determinant of multiplication by a in any indexed finite basis and lies in K |
| `FieldNormMultiplicative` | The norm of a finite extension is multiplicative, and the norm of one is one — card |
| `FieldNormZeroIffZero` | The norm of a member of L is zero exactly when the member is zero — card |
| `FieldNormScalar` | The norm of a base scalar a is a to the power of the extension degree — card |
