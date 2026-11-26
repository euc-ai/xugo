# matrix — a linear map written down, and read back

A matrix is a sequence of ROW VECTORS. The carrier `num → num → A` is
`num → (num → A)` read that way, so `P(i)` is the i-th row and `P(i, j)`
the entry at row i, column j — and the two operations that CONTRACT are
`vector/dot`'s form `⟪·, ·⟫_k` applied to rows and columns. The chapter
mints no fold: `matrix_act⟨m⟩(P, x)` is the form of each row against x,
and `matrix_mul(k, P, Q)` the form of a row of P against a column of Q.
What makes a column available as a vector is `transpose`, whose partial
application `transpose(Q, j)` IS the j-th column and which contracts
nothing; `matrix_of` contracts nothing either.

Reading the carrier as rows is what lets the dimension live where it
lives for vectors: in a predicate, not a type. `matrix⟨n, m⟩(P)` is
`vec⟨n⟩(u)` said twice, once per index — the rows run out at n, and each
row is an m-vector — so an n×m matrix is padded with the ring's own zero
on both sides, and the product and the action need no truncation step
and no membership hypothesis in any identity that does not read the
active range.

## The one design decision

`matrix_of(m, f)` — the matrix of a map on m-vectors — is the only
constant here that carries a guard, and it guards ONE index:

```
matrix_of(m, f, i, j) = COND(j < m, f(basis_vector(j), i), zero)
```

The COLUMN index is cut at m because column j is the image of the j-th
basis vector, and past m there is no basis vector in the domain to take
the image of: an arbitrary `f` would be consulted at a junk argument.
That is the rule `vector/dot` already follows for the adjoint. The ROW
index is NOT cut, because nothing is enumerated over it — it reads a
coordinate of f's own output, and that output is a sequence which
already pads itself.

Guarding one index rather than two is what makes the construction both
a matrix of declared shape and FAITHFUL to the map it is built from.
`MatrixWorks` — the matrix acts as the map — is then true as stated,
with no hypothesis about where f lands; guard the row index too and it
becomes true only of the map's truncation, which is a different theorem
wearing this one's name. The price is paid once, in `MatrixOfMatrix`,
whose hypothesis says where f's values live; and that hypothesis is the
pointwise remnant of the type `real^M -> real^N`, which is where a
type-indexed presentation keeps the same fact.

## The definitional layer (definitions.go)

Every operation is defined POINTWISE, at the index, the way the module
chapter defines its own — so a shorter spelling is the same equation
with trailing arguments left off: `matrix_act⟨m⟩(P)` is the map on
vectors that `vec_linear` asks about, `transpose(Q, j)` the j-th column.

| constant | reading |
|---|---|
| `transpose(P, i, j)` | `P(j, i)` — the reflection that turns a column into a row. No component, no dimension: exchanging two indices is not an algebraic act |
| `matrix_act⟨k⟩(P, x, i)` | `⟪P(i), x⟫_k` — coordinate i of the action is the i-th row paired with x, contracted over k |
| `matrix_mul(k, P, Q, i, j)` | `⟪P(i), transpose(Q, j)⟫_k` — the i-th row of P against the j-th column of Q |
| `matrix_of(m, f, i, j)` | column j is the image of the j-th basis vector, cut at m (above) |
| `matrix⟨n, m⟩(P)` | the rows run out at n and each row is an m-vector — `vec` read at both indices |

## The action (action.go)

What a matrix does to a vector. Each of these is a law of the form read
one coordinate at a time, and none of them inducts.

| member | statement |
|---|---|
| `MatrixActVec` | `matrix⟨n, m⟩(P) ⇒ vec⟨n⟩(matrix_act⟨m⟩(P, x))` — nothing is asked of the vector. The row range is what bounds the value, and a row that has run out is the zero VECTOR, so the coordinate is the form against it |
| `MatrixActLinear` | `vec_linear(matrix_act⟨k⟩(P))` — a coordinate is the form at a FIXED first argument, so linearity of the action is the form's additivity and homogeneity in its SECOND. Nothing about the rows is spent, and no dimension appears |
| `MatrixMulMatrix` | `matrix⟨n, k⟩(P) ⇒ matrix⟨k, m⟩(Q) ⇒ matrix⟨n, m⟩(matrix_mul(k, P, Q))` — the two conditions vanish on OPPOSITE sides of the form: past n the left factor has no row, past m the right factor's column is the zero vector — which is where the rows of its transpose, an m×k matrix, run out |
| `MatrixActAssoc` | `matrix_act⟨k⟩(P, matrix_act⟨n⟩(Q, x)) = matrix_act⟨n⟩(matrix_mul(k, P, Q), x)` — acting twice is acting once, by the product; unconditional, and the two bounds stay independent. The interchange of the two sums is never performed in the open: it sits inside `dot.IterateLeft`, which is the fold mechanism's homomorphism law |

## The matrix of a map (representation.go)

The chapter's subject: a linear map written down, and read back.

| member | statement |
|---|---|
| `MatrixOfColumn` | `transpose(matrix_of(zero, one, m, f), j) = COND(j < m, f(basis_vector(zero, one, j)), vec_zero(zero))` — what a COLUMN of a map's matrix IS: below m the image of the j-th basis vector, past m the zero vector. The chapter's central sentence, and the one two other members were each proving inline before it was promoted. Asks for no ring |
| `MatrixOfMatrix` | `(∀u. vec⟨m⟩(zero, u) ⇒ vec⟨n⟩(zero, f(u))) ⇒ matrix⟨n, m⟩(zero, matrix_of(zero, one, m, f))` — the column condition is free, the row condition is what the hypothesis buys. Stated for ANY two values rather than under the ring, and spelling them: `zero` and `one` enter only as what the definitions write and read, and the explicit components are the visible sign that no ring law is spent |
| `MatrixOfAct` | `(∀i. vec⟨m⟩(P(i))) ⇒ matrix_of(m, matrix_act⟨m⟩(P)) = P` — the round trip. It asks only how WIDE the rows are, never where they stop: `matrix_of` cannot see past column m, so that is the only thing it can be blind to, and without the hypothesis the statement is false |
| `MatrixWorks` | `vec_linear(f) ⇒ vec⟨m⟩(x) ⇒ matrix_act⟨m⟩(matrix_of(m, f), x) = f(x)` — the matrix ACTS as the map. `vec⟨m⟩(x)` is spent exactly once, in the basis expansion; everything else is linearity crossing the fold |
| `MatrixCompose` | `vec_linear(g) ⇒ (∀u. vec⟨m⟩(u) ⇒ vec⟨n⟩(f(u))) ⇒ matrix_of(m, g ∘ f) = matrix_mul(n, matrix_of(n, g), matrix_of(m, f))` — the matrix of a composite is the product of the matrices. Entrywise, and short: below m it is `MatrixWorks` at the vector `f(basis_vector(j))`, above m both sides are the padding value. Note what is NOT assumed: `f` need not be linear. It is read only at basis vectors, on both sides, and only where its values land matters — a proof that goes through matrix equality on the composite needs its linearity, and this one does not |

## The transpose (transpose.go)

The reflection on its own, under the product, and as the bridge back to
the form it was built from.

| member | statement |
|---|---|
| `TransposeTranspose` | `transpose(transpose(P)) = P` — the second reflection puts every entry back. No structure carries it |
| `TransposeMatrix` | `matrix⟨n, m⟩(zero, P) ⇒ matrix⟨m, n⟩(zero, transpose(P))` — an n×m matrix transposed is an m×n one. `matrix` is two conditions, one per index, and the reflection EXCHANGES them: the transpose's rows run out at m because P's rows are m-vectors, and each of its rows is an n-vector because P's rows run out at n. Each half spends exactly one of the hypothesis's conditions, crosswise. Asks for no ring, and spells its component to say so |
| `TransposeMatrixMul` | `transpose(matrix_mul(k, P, Q)) = matrix_mul(k, transpose(Q), transpose(P))` — the transpose reverses a product. No commutativity of the ring is spent here either: both sides are the same form at the same pair of vectors, read in the two orders, which is `dot.Sym` |
| `AdjointIsTranspose` | `adjoint(m, n, f, y) = matrix_act⟨n⟩(transpose(matrix_of(m, f)), y)` — the adjoint `vector/dot` BUILDS out of its form is the transposed matrix acting, with nothing asked of f. The two dimensions mean on the right what they mean on the left: m bounds the coordinates the value has, n is the dimension the form is read at. The reflection carries the adjoint's coordinate index into the column index, which is the index `matrix_of` cuts at m — so one condition settles both sides, and the adjoint and the transpose are one idea |

## Where this chapter sits

Above `vector/dot`, whose form every operation here is built from, and
over an arbitrary commutative ring like `vec_space` and `dot` — so a carrier
applies these laws by citing its own ring instance, and ℝ is one
instance among ℂ, ℤ and ℚ. Four members ask for no ring at all:
`MatrixOfColumn`, `MatrixOfMatrix` and `TransposeMatrix`, which spell
their components to say so, and `TransposeTranspose`, which has none to
spell.

## Additional interfaces

An alternating matrix is square and zero-padded, has its active entries in
the specified ring, and satisfies P(j, i) = −P(i, j) with zero diagonal.
The diagonal condition is explicit so the definition works in
characteristic two as well.

| Member | Statement |
|---|---|
| `MatrixProductDef` | The carrier-ring product starts its finite sum at the specified ring zero |
| `AlternatingMatrixDef` | `matrix_alternating`: ring_ops(A) → num → (num → num → A) → bool |
| `MatrixProductAgrees` | on a commutative ring whose carrier is the whole type, the carrier-ring product is the dot-based matrix product: `c.carrier = 𝕌 ⇒ matrix_product(c, n, P, Q) = matrix_mul(n, P, Q)` |
