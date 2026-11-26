// definitions.go — the chapter's definitional layer: the reflection that
// turns a column into a row, what a matrix does to a vector, what two of
// them compose to, the matrix ANY map is read off its basis, and what it
// is to be an n×m matrix.
//
// A matrix is a sequence of ROW VECTORS — the carrier `num → num → A`
// read as `num → (num → A)` — so the two operations that CONTRACT are
// the form `⟪·, ·⟫_k` of vector/dot applied to rows and columns, and the
// chapter mints no fold of its own. `transpose(P, i, j) = P(j, i)` is
// what makes a COLUMN available as a vector: `transpose(Q, j)` is the
// j-th column of Q, and the product reads the i-th row of P against it.
// The reflection itself contracts nothing, and neither does `matrix_of`.
//
// Every operation is defined POINTWISE, at the index, the way the module
// chapter defines its own (`vec_add(add, u, v, i) = add(u(i), v(i))`), and
// the shorter spellings are the same equation with trailing arguments
// left off: `matrix_act⟨m⟩(P, x)` is the vector, `matrix_act⟨m⟩(P)` the
// map on vectors that `vec_linear` asks about.
//
// Only ONE of them carries a guard, and only on ONE index.
// `matrix_of(m, f)` is built out of an arbitrary `f`, and `basis_vector(j)`
// for `j ≥ m` is not in the domain the matrix is taken over — the
// adjoint's rule exactly (vector/dot's definitional table), so the
// COLUMN index is cut at m and each row of the value is an m-vector
// with nothing asked of f. The ROW index is not guarded: nothing is
// enumerated over it, it reads a coordinate of f's own output, and that
// output is a sequence which already pads itself with the ring's zero.
// The chapter pays for that choice exactly once, in `MatrixOfMatrix`,
// whose hypothesis says f lands in dimension n — and is paid back in
// `MatrixWorks`, which is true as stated: the matrix of a map acts as
// the map, not as its truncation.
//
// `matrix⟨n, m⟩(P)` is the exact parallel of `vec⟨n⟩(u)`, one condition
// per index: the rows run out at n — past it a row is the zero VECTOR,
// the padding element of the carrier the rows live in — and each row is
// an m-vector. The second condition is `vec` itself; the first is what
// `vec` would say read at the vectors rather than at the ring, and it is
// written out because the two readings cannot both be spelled here (a
// structure-implicit constant is recognized by the NAME in its component
// slot, so `vec` at a second instance has no spelling in a scope that
// binds the first). It is the only constant here carrying both
// dimensions — which is why it is the one that declares them
// (RowDim/ColumnDim), so the typed surface writes an n×m matrix's two
// dimensions off the matrix itself. The operations declare at most one:
// `matrix_act` declares `Dim: "k"` because it HAS a vector argument to
// anchor there, and `matrix_mul` declares none because it has none — its
// own `k` is the contracted index of two matrices, which no vector reads.

package matrix

import (
	"github.com/euc-ai/xugo/library/registry"
)

// TransposeDef — the reflection that turns a column into a row. No ring
// component is read: swapping two indices is not an algebraic act.
var TransposeDef = transposeDefThm{family.Define(registry.DefEntry{
	Name:      "TransposeDef",
	Key:       "prop_19d350eb0e4aa8ca",
	Const:     "transpose",
	Type:      "(num → num → A) → num → num → A",
	Equations: []string{"∀P:(num → num → A). ∀i j:num. transpose(P, i, j) = P(j, i)"},
})}

// MatrixActDef — the action of a matrix on a vector: coordinate i is
// the i-th row paired with the vector, over the range the product
// contracts. No guard: a row that has run out is the zero vector, and
// the form against it is the ring's zero, so the value stops where the
// matrix does.
var MatrixActDef = matrixActDefThm{family.Define(registry.DefEntry{
	Name:     "MatrixActDef",
	Key:      "prop_43743556bb2f6600",
	Const:    "matrix_act",
	Type:     "(A → A → A) → (A → A → A) → num → (num → num → A) → (num → A) → num → A",
	Implicit: []string{"add", "mul"},
	Dim:      "k",
	Equations: []string{"∀add mul:(A → A → A). ∀k:num. ∀P:(num → num → A). ∀x:(num → A). ∀i:num. " +
		"    matrix_act⟨k⟩(add, mul, P, x, i) = dot⟨k⟩(add, mul, P(i), x)"},
})}

// MatrixMulDef — the product: entry (i, j) is the i-th row of the left
// matrix against the j-th column of the right, contracted over k. The
// column is where `transpose` earns its place in the definitional layer
// rather than in the laws.
var MatrixMulDef = matrixMulDefThm{family.Define(registry.DefEntry{
	Name:     "MatrixMulDef",
	Key:      "prop_cd9b5eaa6e709a64",
	Const:    "matrix_mul",
	Type:     "(A → A → A) → (A → A → A) → num → (num → num → A) → (num → num → A) → num → num → A",
	Implicit: []string{"add", "mul"},
	Equations: []string{"∀add mul:(A → A → A). ∀k:num. ∀P Q:(num → num → A). ∀i j:num. " +
		"    matrix_mul(add, mul, k, P, Q, i, j) = dot⟨k⟩(add, mul, P(i), transpose(Q, j))"},
	Deps: []registry.EntryLike{TransposeDef},
})}

// MatrixOfDef — the matrix of a map on m-vectors: column j is the image
// of the j-th basis vector, and past m there is no basis vector to take
// the image of, so the column is the ring's zero.
var MatrixOfDef = matrixOfDefThm{family.Define(registry.DefEntry{
	Name:     "MatrixOfDef",
	Key:      "prop_5cff042952763bde",
	Const:    "matrix_of",
	Type:     "A → A → num → ((num → A) → (num → A)) → num → num → A",
	Implicit: []string{"zero", "one"},
	Equations: []string{"∀zero one:A. ∀m:num. ∀f:((num → A) → (num → A)). ∀i j:num. " +
		"    matrix_of(zero, one, m, f, i, j) = COND(j < m, f(basis_vector(zero, one, j), i), zero)"},
})}

// MatrixDef — membership in the n×m matrices: the rows run out at n,
// and each row is an m-vector.
var MatrixDef = matrixDefThm{family.Define(registry.DefEntry{
	Name:      "MatrixDef",
	Key:       "prop_931a970ed2c92998",
	Const:     "matrix",
	Type:      "A → num → num → (num → num → A) → bool",
	Implicit:  []string{"zero"},
	RowDim:    "n",
	ColumnDim: "m",
	Equations: []string{"∀zero:A. ∀n m:num. ∀P:(num → num → A). " +
		"    matrix⟨n, m⟩(zero, P) ⇔ " +
		"    (∀i:num. n ≤ i ⇒ P(i) = vec_zero(zero)) ∧ (∀i:num. vec⟨m⟩(zero, P(i)))"},
})}

// AlternatingMatrixDef — a square matrix over a carrier ring whose
// transposed entries are negatives and whose diagonal is zero.
var AlternatingMatrixDef = alternatingMatrixDefThm{family.Define(registry.DefEntry{
	Name:  "AlternatingMatrixDef",
	Key:   "prop_7f71956f34ad347b",
	Const: "matrix_alternating",
	Type:  "ring_ops(A) → num → (num → num → A) → bool",
	Reading: "The diagonal is required to vanish explicitly: skew symmetry alone does not imply " +
		"it in characteristic two. The matrix predicate supplies zero padding outside the active square.",
	Deps: []registry.EntryLike{MatrixDef},
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P:(num → num → A). " +
			"    matrix_alternating(R, n, P) ⇔ " +
			"    matrix⟨n, n⟩(R.zero, P) ∧ " +
			"    (∀i j:num. i < n ∧ j < n ⇒ P(i, j) ∈ R.carrier ∧ P(j, i) = R.neg(P(i, j))) ∧ " +
			"    (∀i:num. i < n ⇒ P(i, i) = R.zero)",
	},
})}
