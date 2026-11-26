# projective_affine_piece — the Jacobian criterion: the affine pieces of a smooth projective equation curve are integrally closed

The affine piece at a point x of the curve over M with x(j) ≠ 0, the values at the ratios x/x(j) of the polynomials over k, is a subring of M holding k, whose field of fractions is K when the coordinates of x, one of them one, generate K over k; its nonzero ideals have finite quotients, and at each closed point the Jacobian rank makes the cotangent space a line, so the maximal ideal is invertible and the piece is integrally closed.

## The affine pieces

| Member | Statement |
|---|---|
| `AffinePieceFractionField` | the affine piece of a point whose coordinates generate K over k, one of them one, is a subring of K holding k with K as its field of fractions |
| `AffinePieceDegreeFiltration` | the affine piece at a point of M whose j-th coordinate is not zero is a subring holding k, the increasing union of the values at the affine point of the forms of each degree |
| `AffinePieceLayerClasses` | for an ideal H of the affine piece at a point of the curve and a form F of degree r whose value at the affine point is a nonzero member of H, the classes modulo H of the layer of degree r + d span at most h(r + d) − h(d) dimensions |
| `AffinePieceQuotientsFinite` | at a point of the curve over M with x(j) ≠ 0, every nonzero ideal of the affine piece has a quotient of finite dimension over k |
| `AffinePieceGradientRank` | at a point x of the curve over M with x(j) ≠ 0 and a point φ of its affine piece, the gradients of the relations among the ratios x/x(j) span at least n of the n + 1 coordinates |
| `AffinePieceCotangentLine` | at a closed point of the affine piece at a point x of a smooth projective equation curve over M with x(j) ≠ 0, seen through a point φ of the piece in M with nonzero kernel m, m/m² is spanned by one nonzero u ∈ m |
| `AffinePieceMaximalLocallyPrincipal` | a nonzero maximal ideal m of the affine piece at a point x of the curve over M with x(j) ≠ 0, M algebraically closed, has a nonzero member u generating it near its point: some s of the piece outside m carries m into the multiples of u |
| `AffinePiecesIntegrallyClosed` | the Jacobian criterion: for a point x of a smooth projective equation curve over K whose coordinates generate K over k, each affine piece at x is integrally closed in K |
