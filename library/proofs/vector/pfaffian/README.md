# pfaffian — the signed matching polynomial

The Pfaffian is defined over a commutative carrier ring by a signed sum
over perfect matchings. A matching is a permutation whose consecutive
pairs have increasing endpoints, with the first endpoints themselves in
increasing order. Thus each matching occurs once, with no division by a
factorial or a power of two. The dimension argument is the actual matrix
size: the empty Pfaffian is one and odd sizes are assigned zero.

The polynomial identities read `matrix.matrix_alternating`: the matrix is
zero-padded, its active entries lie in the ring, transposition negates
them, and its diagonal is explicitly zero. The last condition matters
in characteristic two. Congruence by Q multiplies the Pfaffian by det(Q),
so an orientation-preserving orthogonal change of frame leaves it fixed.
Its square is the determinant in every characteristic.

The kernel vanishing criterion uses a unimodular vector: Pv = 0 and a
dual vector w with pairing w·v = 1. This formulation also works over
rings with zero divisors, including rings of even-degree forms. The
signed Pfaffian cofactor identity gives pf(P)v = 0, then pairing with w
gives pf(P) = 0; determinant zero alone would not suffice in such a ring.

The Euclidean form chapter `vector/vec_form` supplies the ring of normalized
even forms and applies these identities to matrices of two-forms. Its
curvature closedness law also uses the full graded algebra and Bianchi.

## Members

| Member | Statement |
|---|---|
| `PfaffianDef` | `pfaffian`: ring_ops(A) → num → (num → num → A) → A |
| `PfaffianInCarrier` | The Pfaffian of a matrix over a commutative ring belongs to its carrier — card |
| `PfaffianEmpty` | The empty Pfaffian is one — card |
| `PfaffianCongruence` | pf(QᵀPQ) = det(Q) pf(P) for alternating P — card |
| `PfaffianDeterminant` | det(P) = pf(P)² for an even alternating matrix — card |
| `PfaffianUnimodularKernel` | An even alternating matrix with a unimodular kernel vector has zero Pfaffian — card |
