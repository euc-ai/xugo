# determinant — finite Leibniz determinants over carrier-aware rings

The determinant of an n × n matrix over a commutative ring carrier is its
Leibniz sum: over the permutations of the points below n, the sign times the
product of the entries P(i, p(i)), the fold `module_sum(c.mul, c.one, …)`
of the ring's multiplicative monoid, so every monoid law of module_sum applies
to it. The empty determinant is one.

The sign reads the [parity of a permutation](../../algebra/group/symmetric_group/README.md#inversions-and-parity).
It is the ring's one for an even permutation and minus one for an odd one.

Each Leibniz term reads every column once, so the determinant is additive and
homogeneous in each column. It vanishes on two equal columns because the even
and the odd permutations pair off term by term under the transposition of
those columns; the argument never divides by two and holds in characteristic
two, where d = −d says nothing. An alternating form is therefore determined
by its value at the identity: expanded over the permutations, two forms that
agree at the identity agree at every permutation matrix, column swap by
column swap (`AlternatingFormUniversal`). Multiplicativity, and with it
invariance under a change of basis, follows. The triangular case is read off
the Leibniz sum directly: only the identity permutation avoids a zero below
the diagonal. Over an integral domain, a matrix P whose columns combine to
zero with weights w, w(j) ≠ 0, has determinant zero
(`DeterminantDependentColumns`): the identity with column j replaced by the
weights is a matrix Q with det Q = w(j), and P·Q has column j zero, so
det(P)·w(j) = det(P·Q) = 0, where w(j) ≠ 0 forces det(P) = 0.

The column map of P sends a coordinate vector u to P·u, the vector with
entries Σ_k P(r, k)·u(k): a linear map of the coordinate module to itself
that sends the indicator delta_at(j) of j to column j
(`MatrixColumnMapOnDelta`). Over a field, det(P) ≠ 0 exactly when the
columns of P form a basis and exactly when P has a two-sided inverse
(`DeterminantZeroIffDependent`), the three conditions proved in a cycle: a
nonzero determinant makes the columns a basis, a column basis gives a
two-sided inverse through a linear section of the column map, and a
two-sided inverse makes the determinant nonzero by multiplicativity.

The expansion of a multilinear form, from one column through every column
to the universality of alternating forms, has a file of its own,
`expansion.go`, with a vocabulary of its own: maps pinned at k, the reset of
a map at k, the index-map matrix whose column s is the basis vector at f(s).
Along one column the expansion is the free module's: as a function of that
column the form is a linear map out of the free module on the points below
n (`ColumnMultilinearHom`), so it is the sum of the column's entries times
its values at the indicators (`free_module.FreeHomExpand`), and below n the
indicator of m is the basis vector e_m. Every column at once is an induction
on k whose steps reindex finite sums over the maps pinned at k. The
expansion's products read the entries column by column, as P(p(j), j), where
the Leibniz sum reads P(i, p(i)); the two never meet, because universality
compares two expansions of the same kind. The transpose is where they do:
reindexed by p⁻¹, the product of P(p(i), i) is the product of P(i, p⁻¹(i)),
and p⁻¹ has the parity of p, so the Leibniz sum of the transpose is the
Leibniz sum of P reindexed by inversion.

The adjugate is a concrete cofactor matrix: entry (i, j) is the determinant
after replacing column i by the j-th basis vector, with zero padding outside
the active square. This orientation gives both adj(P)P and P adj(P) equal to
det(P)I over every commutative ring. Over a carrier field, `matrix_inverse`
scales this adjugate by the inverse determinant; its inverse law requires
det(P) ≠ 0. These formulas let smooth matrix families use polynomial entries
and a single reciprocal.

## Members

| Member | Statement |
|---|---|
| `MatrixOverDef` | `matrix_over`: ring_ops(A) → num → (num → num → A) → bool |
| `MatrixIdentityDef` | `matrix_identity`: ring_ops(A) → num → num → num → A |
| `PermutationMatrixDef` | `permutation_matrix`: ring_ops(A) → num → permutation(num) → num → num → A |
| `ColumnReplaceDef` | `matrix_replace_column`: ring_ops(A) → num → (num → num → A) → num → (num → A) → num → num → A |
| `DeterminantDef` | `determinant`: ring_ops(A) → num → (num → num → A) → A |
| `ColumnMultilinearDef` | `column_multilinear`: ring_ops(A) → num → ((num → num → A) → A) → bool |
| `AlternatingFormDef` | `alternating_form`: ring_ops(A) → num → ((num → num → A) → A) → bool |
| `AdjugateDef` | `matrix_adjugate`: ring_ops(A) → num → (num → num → A) → num → num → A |
| `MatrixInverseDef` | `matrix_inverse`: field_ops(A) → num → (num → num → A) → num → num → A |
| `AdjugateOver` | The adjugate remains a matrix over the carrier ring — card |
| `AdjugateIdentity` | P adj(P) = adj(P) P = det(P) I — card |
| `MatrixInverse` | For nonzero determinant the cofactor inverse lies over the field and is a two-sided inverse — card |
| `MatrixOverEntries` | A matrix over c is an array whose entries all lie in c and vanish outside the n × n block |
| `MatrixIdentityOver` | The identity matrix is a matrix over c |
| `MatrixIdentityColumn` | column `m` of the identity matrix, for `m` below `n`, is the indicator `delta_at(m)` |
| `IndexMapMatrixOver` | For a map f fixing every point from n on, the matrix whose column s is the basis vector at f(s) is a matrix over c |
| `LeibnizFactorsIn` | Both factors of a Leibniz term of a matrix over c, the sign as ±1 of the ring and the product of the entries P(k, q(k)), lie in c |
| `SignValueAfterTransposition` | The sign's value in the ring, one or minus one, is negated by composing with a transposition |
| `ReplaceColumnMatrixOver` | Replacing a column of a matrix over R by a vector of the free module on the points below n leaves a matrix over R |
| `DeterminantColumnMultilinear` | The determinant of a matrix over a commutative ring lies in the ring and is additive and homogeneous in each column |
| `DeterminantInCarrier` | A determinant of a matrix over the ring belongs to the ring carrier |
| `DeterminantEqualColumns` | A matrix over c with two equal columns has determinant zero, in every characteristic |
| `AlternatingFormScalarMultiple` | A multiple of an alternating form by a member of the ring is alternating |
| `AlternatingFormSwapColumns` | Exchanging two columns of a matrix changes the sign of an alternating form |
| `DeterminantAlternating` | The determinant is an alternating form of the columns, and swapping two columns negates it |
| `ColumnMultilinearHom` | A form multilinear in the columns is linear in each column: with the other columns of P fixed, u ↦ F(P with column j replaced by u) is a module homomorphism from the free module on the points below n to the ring |
| `MultilinearColumnExpansion` | A form multilinear in the columns expands along any column j below n in the standard basis: F(P) is the sum over m < n of P(m, j) times F at P with column j replaced by the basis vector e_m |
| `PinnedMapsExtension` | The maps sending the points below k + 1 below n and fixing every point from k + 1 on are the maps that do so for k with their value at k reset to a point below n: the reset is one to one on the pairs (f, m), and its image is the larger set |
| `PinnedMapsFinite` | Finitely many maps send the points below k below n and fix every point from k on |
| `MultilinearMapExpansion` | A form multilinear in the columns, at a matrix P over c, is the sum over the maps f of the points below n into themselves, fixed from n on, of the product of the entries P(f(j), j) times the form at the matrix whose column j is the basis vector at f(j) |
| `AlternatingFormPermutationExpansion` | An alternating form at a matrix is the sum over the permutations of the products of the entries P(p(j), j) times the form at the permutation matrix |
| `AlternatingFormUniversal` | An alternating form is its value at the identity times the determinant: `F(P) = F(matrix_identity(c, n)) * determinant(c, n, P)` |
| `MatrixProductOver` | Products of matrices over the ring remain over the ring |
| `MatrixProductRightIdentity` | The identity matrix is a right identity for matrix multiplication |
| `CoordinateVectorMember` | A vector lies in the finite free module exactly when its entries lie in the carrier and vanish from the dimension onward |
| `MatrixColumnMapLinear` | The column map of a matrix over the ring is a linear map of the finite free module to itself: it keeps the finite free module and preserves its sums and scalar multiples |
| `MatrixColumnMapOnDelta` | The column map sends the standard vector at an index below the dimension to that column |
| `DeterminantMultiplicative` | The determinant of a product of two matrices over c is the product of their determinants |
| `DeterminantChangeBasis` | Conjugating a matrix by two matrices whose product is the identity leaves its determinant unchanged: det(Q·(P·U)) = det(P) when Q·U = I |
| `DeterminantTriangular` | A matrix over c that vanishes below the diagonal has the product of its diagonal entries as determinant: `determinant(c, n, P) = module_sum(c.mul, c.one, {i:num \| i < n}, λi:num. P(i, i))` |
| `DeterminantIdentity` | The identity matrix has determinant one |
| `DeterminantTranspose` | A matrix over c and its transpose have the same determinant |
| `DeterminantDependentColumns` | Over an integral domain, a matrix whose columns combine to zero with weights not all zero has determinant zero |
| `DeterminantZeroIffDependent` | Over a field, a matrix has nonzero determinant exactly when its columns form a basis, and exactly when it has a two-sided inverse |
