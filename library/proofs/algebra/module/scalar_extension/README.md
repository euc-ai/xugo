# scalar_extension — scalar extension of modules and two-term complexes

Scalar extension is the tensor quotient with the larger ring acting on its first factor. The induced map is specified on pure tensors, and over a subfield splitting vector-space sequences identifies its kernel and cokernel. Only the cohomology must be finite dimensional for dimension preservation.

For a subring S of a commutative ring R, every S-linear map into an R-module extends R-linearly across the tensor product. When one is not zero in R, the canonical map v ↦ 1 ⊗ v sends an S-basis injectively onto an R-basis, so over a subfield a finite-dimensional space keeps its dimension.

## Members

| Member | Statement |
|---|---|
| `tensorScalarActionDef` | `tensor_scalar_action`: ring_ops(A) → ring_ops(A) → module_ops(A, B) → A → set(prod(A, B) → A) → set(prod(A, B) → A) |
| `TensorScalarActionSpec` | a ring scalar acts S-linearly on R ⊗ₛ V and sends b ⊗ v to (a · b) ⊗ v |
| `ScalarExtensionDef` | `scalar_extension`: ring_ops(A) → ring_ops(A) → module_ops(A, B) → module_ops(A, set(prod(A, B) → A)) |
| `ScalarExtensionCarrier` | scalar extension has the tensor module's points |
| `ScalarExtensionAdd` | scalar extension adds as the tensor module does |
| `ScalarExtensionZero` | the zero of scalar extension is the tensor module's |
| `ScalarExtensionSmul` | a scalar acts on scalar extension by the chosen action on the first factor |
| `ScalarExtensionHomUnique` | two S-linear maps out of the tensor module agreeing on pure tensors agree on its carrier |
| `TensorScalarActionRestrict` | a subring scalar acts on scalar extension by the underlying tensor-module scaling |
| `ScalarExtensionOn` | extending an S-module to a commutative ring R containing S gives an R-module |
| `ScalarExtensionMapDef` | `scalar_extension_map`: ring_ops(A) → ring_ops(A) → module_ops(A, B) → module_ops(A, C) → (B → C) → set(prod(A, B) → A) → set(prod(A, C) → A) |
| `ScalarExtensionLift` | an S-linear map into an R-module extends R-linearly from scalar extension, with the prescribed pure-tensor values |
| `ScalarExtensionUnitLinear` | the canonical map v ↦ 1 ⊗ v is S-linear into scalar extension |
| `ScalarExtensionMapSpec` | scalar extension takes S-linear maps to R-linear maps, sending a ⊗ v to a ⊗ f(v) |
| `ScalarExtensionMapTensorLinear` | the induced map is also linear between the underlying tensor modules over the subring |
| `ScalarExtensionMapCompose` | extending a composite gives the composite of the induced maps on the scalar-extension carrier |
| `ScalarExtensionMapCongruence` | maps agreeing on the source carrier induce equal maps on the scalar-extension carrier |
| `ScalarExtensionMapIdentity` | extending the identity fixes every element of the scalar-extension carrier |
| `ScalarExtensionMapAdd` | extending a pointwise sum of S-linear maps gives the sum of the induced maps on the scalar-extension carrier |
| `ScalarExtensionMapZero` | extending the zero map gives zero on the scalar-extension carrier |
| `ScalarExtensionMapInverse` | a left inverse of an S-linear map extends to a left inverse of the induced map on the scalar-extension carrier |
| `ScalarExtensionMapComplement` | S-linear maps summing to the identity on V induce maps summing to the identity on the scalar-extension carrier |
| `ScalarExtensionMapVanishes` | an S-linear map vanishing on V induces zero on the scalar-extension carrier |
| `ScalarExtensionSpanning` | the unit image of an S-spanning set spans scalar extension over R |
| `ScalarExtensionBasis` | when one is not zero in R, the unit image of an S-basis is an R-basis, and the unit is injective on that basis |
| `ScalarExtensionFiniteDim` | extending scalars preserves finite dimensionality and dimension |
| `SubfieldLinearInnerInverse` | a map linear over a subfield of L has a linear inner inverse |
| `ScalarExtensionKernel` | extending scalars preserves the kernel of an arbitrary-dimensional linear map over a subfield |
| `ScalarExtensionCokernel` | extending scalars preserves the cokernel of an arbitrary-dimensional linear map over a subfield |
| `TwoTermComplexFieldBaseChange` | kernel and cokernel commute with scalar extension, and each finite cohomology dimension is preserved |
