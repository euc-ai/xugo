# clifford_spin — negative Clifford algebra, Spin and its graded spin representation

The real Clifford algebra has the binary subset basis and relation v squared equals minus its Euclidean norm squared. Its product sign counts crossed generators and repeated generators. Spin consists of even products of real unit vectors. The conjugation action on vectors gives its map to the special orthogonal group.

In dimension 2m the complex spin representation acts on Lambda C^m: c(e2j)=wedge_j-contraction_j and c(e2j+1)=i(wedge_j+contraction_j). Exterior parity is its grading. These explicit conventions fix the chirality used by the geometric Dirac chapter.

## Members

| Member | Statement or role |
|---|---|
| `ProductDef` | Definition of `clifford_product` |
| `VectorDef` | Definition of `clifford_vector` |
| `ConjugateDef` | Definition of `clifford_conjugate` |
| `wordDef` | Definition of `clifford_word` |
| `SpinElementDef` | Definition of `spin_element` |
| `SpinGroupDef` | Definition of `spin_group` |
| `ActionDef` | Definition of `spin_vector_action` |
| `GeneratorDef` | Definition of `spinor_generator` |
| `bladeMatrixDef` | Definition of `spinor_blade` |
| `RepresentationDef` | Definition of `spinor_representation` |
| `CliffordSignCocycle` | The sign of the binary-basis product is a cocycle on finite sets of generators — card |
| `CliffordAssociative` | The negative Clifford product is associative — card |
| `CliffordRelation` | Clifford vectors satisfy the negative Euclidean anticommutator relation — card |
| `SpinGroup` | Even products of unit vectors form the Spin group — card |
| `SpinOrthogonal` | Spin conjugation induces a special orthogonal matrix — card |
| `SpinCover` | Every positive-dimensional special orthogonal matrix has a Spin lift — card |
| `RepresentationProduct` | The explicit spinor representation preserves Clifford multiplication — card |
| `SpinRepresentationUnitary` | Spin acts unitarily and preserves exterior parity — card |
