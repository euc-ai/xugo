# linear_determinant — basis-independent determinants of linear endomorphisms

An injectively indexed finite basis gives the matrix of a linear map. Change of basis makes its determinant independent of that choice, and matrix multiplication gives composition and scalar formulas.

## Members

| Member | Statement |
|---|---|
| `ModuleBasisMatrixDef` | `module_basis_matrix`: ring_ops(A) → module_ops(A, B) → num → (num → B) → (B → B) → num → num → A |
| `ModuleDeterminantDef` | `module_determinant`: ring_ops(A) → module_ops(A, B) → (B → B) → A |
| `LinearDeterminantFromBasis` | The determinant equals the determinant of its matrix in any indexed finite basis and belongs to the scalar field |
| `LinearDeterminantCompose` | The determinant of a composite of two endomorphisms of a finite-dimensional module over a field is the product of their determinants, and the identity has determinant one — card |
| `LinearDeterminantScalar` | Scaling by a member a of the field has determinant a to the power of the dimension — card |
| `BasisChangeMatrixDef` | `basis_change_matrix`: ring_ops(A) → module_ops(A, B) → num → (num → B) → (num → B) → num → num → A |
| `BasisChangeCompose` | Changing coordinates from a basis of M to a basis of a submodule, and from there to vectors of the submodule, composes to the direct change: the product of the two change matrices is the direct one |
| `BasisChangeIdentity` | The change of coordinates from an indexed basis to itself is the identity matrix |
| `BasisChangeMatrixOver` | The matrix of coordinates of vectors of M in an indexed basis is a matrix over the scalar ring |
| `BasisChangeInverse` | The coordinate changes between two indexed bases, there and back, are inverse matrices over the scalar ring |
| `ModuleBasisMatrixAsChange` | The matrix of an endomorphism in an indexed basis is the coordinate-change matrix from that basis to the images of its vectors |
