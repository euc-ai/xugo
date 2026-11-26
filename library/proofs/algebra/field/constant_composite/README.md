# constant_composite — the composite of a function field with a finite extension of its constants

Let K be a subfield of a field M holding a subfield k, and l a finite extension
of k inside M. The composite K(l) (`ConstantCompositeDef`) is the constant
extension of K by l. A finite extension of a perfect field is simple, and the
minimal polynomial of its generator keeps its degree over a field in which the
base is algebraically closed, so [K(l) : K] = [l : k] (`constant_extension.go`);
when the degree is kept, multiplication is an l-linear isomorphism
l ⊗ₖ K ≅ K(l) (`constant_tensor.go`, apart because its vocabulary is tensor
modules: the swap of a tensor product, the composite as the K-span of l); and
for K regular over k the composite is regular over l, a separating parameter of
K staying one of K(l) with the same degree. So a k-basis E of l stays a K-basis
of K(l), and the coordinates of an element along E lie in K, a factor from K
coming out of them (`basis.go`). constant_field_extension reads the subspaces of
K through those coordinates.

## Definitions

| Member | Statement |
|---|---|
| `ConstantCompositeDef` | `constant_composite`: field_ops(A) → set(A) → set(A) → set(A) |

## Members

| Member | Statement |
|---|---|
| `ConstantExtensionDegree` | A finite extension l of a perfect field k, with k algebraically closed in K, keeps its degree over K: K(l) is finite over K and [K(l) : K] = [l : k] |
| `ConstantCompositeTensor` | When the composite Kl has degree [l : k] over K, multiplication is an l-linear isomorphism l ⊗ₖ K ≅ Kl |
| `RegularConstantExtension` | A finite constant extension l of a regular function field K stays regular, multiplication identifies l ⊗ₖ K with the composite Kl, and a separating parameter of K stays one of Kl with the same degree |
| `ConstantCompositeSubfield` | The composite of two subfields is a subfield holding both |
| `ConstantCompositeBasis` | A k-basis of l stays a K-basis of the composite K(l) |
| `ConstantExtensionData` | What a k-basis of l gives the composite of K and l |
| `ConstantCoordinateProduct` | The coordinates of a member of the composite lie in K, and a factor from K comes out of them |
| `ConstantCoordinateScale` | Coordinates of elements of l lie in k, and K-multiples scale them |
