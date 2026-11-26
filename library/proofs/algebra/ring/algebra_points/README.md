# algebra_points — normalized ring maps agreeing with a prescription

An algebra point is a ring map to a specified target ring, agreeing with prescribed values on a chosen set and equal to zero outside the source carrier. Two points that agree on the carrier are then equal as functions, so a set of points is counted as a set of maps. The chapter holds the definition and the facts that read it directly: membership (`AlgebraPointsMember`), the point a ring map agreeing with the prescription gives once it is set to zero off its source (`AlgebraPointsOfRingMap`), the passage between values in a subring and values in the ambient ring (`AlgebraPointsChangeTarget`, `AlgebraPointsInSubring`), and a point with values in l determined by its kernel (`PointDeterminedByKernel`). Points of a field's subring with values in the field, fixing a subfield K, are the K-embeddings that the Galois chapter counts. How many points an algebra has is `algebra_point_bounds`.

## Members

| Member | Statement |
|---|---|
| `AlgebraPointsDef` | `algebra_points`: ring_ops(A) → ring_ops(B) → set(A) → (A → B) → set(A → B) |
| `AlgebraPointsMember` | A point is a ring map agreeing with the prescription and vanishing off the carrier |
| `AlgebraPointsOfRingMap` | A ring map agreeing with the prescription on c ⊆ R is a point once set to zero off R |
| `AlgebraPointsChangeTarget` | A point with values in a part of S lying in a subring of S is a point with values in that subring |
| `AlgebraPointsInSubring` | A point with values in a subring is a point in the ambient ring taking the carrier into the subring |
| `PointDeterminedByKernel` | Two points of a ring over l with values in l and one kernel are equal |
