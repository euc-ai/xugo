# lattice_pair_twist — twisting an invertible lattice pair at a rational point, and the Euler characteristic rising by one at a regular point

Twisting a lattice pair inside a field (scheme/invertible_lattice_pair)
by a point multiplies it by the inverse of the point's ideal pair, chart
by chart: M(P) = M · P⁻¹, the sections allowed a simple pole at P. A
regular point is a rational point (scheme/biaffine_rational_point) whose
ideals are invertible. The algebra of twisting is the product's. At a
regular point each chart and the overlap grow by the point's colength
there, so the three-term formula of a sub-pair
(scheme/lattice_pair_sequence) gives the twist of an invertible pair with
finite cohomology finite cohomology and χ(M(P)) = χ(M) + 1, and at most
one more section.

## Members

### The definitions

| Member | Statement |
|---|---|
| `LatticePairTwistDef` | `lattice_pair_twist(field_ring(L), A₀, A₁, M, P)`: M(P), M times the inverse of the point's ideal pair |
| `BiaffineRegularPointDef` | `biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)`: a rational point whose ideals are invertible |

### The algebra of twisting

| Member | Statement |
|---|---|
| `TwistIsLattice` | M(P) is a lattice pair when P is invertible |
| `TwistInvertible` | M(P) is invertible when M and P are |
| `TwistCommute` | M(P)(Q) = M(Q)(P) — card |
| `TwistInverseTwist` | M(P) · P = M and (M · P)(P) = M — card |

### Twisting at a regular point

| Member | Statement |
|---|---|
| `RationalPointColengthsInField` | over a subfield k of L inside both charts, a rational point's colengths as quotients of L's regular module: a chart modulo the point's ideal has dimension one on a chart the point lies on and zero off it, the overlap modulo the ideal it generates dimension one exactly on both |
| `TwistQuotientDim` | for invertible M at a regular point, M ⊆ M(P), and each chart and the ambient grow by the point's colength in that ring |
| `TwistEuler` | for invertible M with finite cohomology at a regular point, M(P) has finite cohomology and χ(M(P)) = χ(M) + 1 |
| `TwistH0Step` | twisting an invertible pair with finite cohomology at a regular point adds at most one section |
| `TwistInsidePoints` | the twist at P of an invertible pair inside a regular point P lies in the structure pair and in every other regular point the pair lies inside |
| `PairBelowContraction` | A lattice pair under the first component of P lies under the second, where that component is chart 1 inside the ideal the first generates on the overlap |
