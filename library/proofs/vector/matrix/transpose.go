// transpose.go — the reflection that exchanges a matrix's two indices.
//
// `transpose(P, i, j) = P(j, i)` is the hinge between a carrier read as
// a sequence of ROWS and the columns the product contracts against: it
// is what makes a column available as a vector. What is collected here
// is how that reflection behaves: on its own, under the product, and as
// the bridge back to the form it was all built from — `vector/dot` BUILDS
// an adjoint out of its form, and that adjoint turns out to be the
// transposed matrix acting, with nothing asked of the map.

package matrix

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// TransposeTranspose — the transpose is an involution: the second
// reflection puts every entry back in its own place, so the two
// readings are the same matrix. No structure carries the statement,
// because exchanging two indices asks nothing of a ring.
var TransposeTranspose = transposeTransposeThm{family.Add(registry.ProofEntry{
	Name: "TransposeTranspose",
	Key:  "prop_40e3abd669c88b59",
	Build: family.Theorem("∀P:(num → num → A). transpose(transpose(P)) = P",
		func(a *Argument) {
			a.Show(
				"the double reflection at (i, j) is the single one at (j, i), which is P at (i, j) again",
				Unfold(TransposeDef))
		}),
})}

// TransposeMatrix — the reflection carries the n×m matrices to the m×n
// ones, and the whole content is that it EXCHANGES the two conditions
// `matrix` is made of.
//
// The transpose's rows run out at m because each row of P is an
// m-vector: row j of the transpose collects one entry from each row of
// P, and past m they have all vanished, so the row IS the zero vector.
// And each row of the transpose is an n-vector because P's rows run out
// at n: the coordinate at a row past n is read off the zero row
// standing there. So each half spends exactly one of the hypothesis's
// two conditions, crosswise — which is why the exchange is worth
// stating rather than unfolding at each use.
//
// No ring: exchanging two indices reads no component, and `zero` enters
// only as the padding value `matrix` and `vec` write. The components
// are spelled rather than left implicit, which is this chapter's sign
// for that.
var TransposeMatrix = transposeMatrixThm{family.Add(registry.ProofEntry{
	Name: "TransposeMatrix",
	Key:  "prop_486b525ecdaf5366",
	Build: family.Theorem(
		Statement{
			Binders: "∀zero:A. ∀n m:num. ∀P:(num → num → A).",
			Hypotheses: []string{
				"matrix⟨n, m⟩(zero, P)",
			},
			Conclusion: "matrix⟨m, n⟩(zero, transpose(P))",
		},
		func(a *Argument, zero *Expr[A], n, m *Expr[Nat], P *Mat[A, DimN, DimM], member Fact) {
			rowsEnd := a.Have(
				"past P's column range the transpose has no row left",
				"∀j:num. m ≤ j ⇒ transpose(P, j) = vec_zero",
				Derive(func(b *Argument) {
					entriesVanish := b.Have(
						"each row of P is an m-vector, so past the column range its entries are the padding value",
						"∀i j:num. m ≤ j ⇒ P(i, j) = zero",
						By(member, MatrixDef, vec_space.VecDef))
					b.Fix("j")
					past := b.Assume()
					// A row of the transpose is a sequence whose values
					// are those entries, one from each row of P.
					b.Do(Funext())
					b.Fix("i")
					b.Show(
						"so the row agrees with the zero vector at every coordinate",
						By(entriesVanish, past, TransposeDef, vec_space.VecZeroDef))
				}))

			rowsAreVectors := a.Have(
				"and each row of the transpose is an n-vector",
				"∀j:num. vec⟨n⟩(transpose(P, j))",
				Derive(func(b *Argument) {
					rowsVanish := b.Have(
						"past its row range P's own row is the zero vector",
						"∀i:num. n ≤ i ⇒ P(i) = vec_zero",
						By(member, MatrixDef))
					b.Fix("j")
					b.Do(Unfold(vec_space.VecDef))
					b.Fix("i")
					past := b.Assume()
					b.Show(
						"so the coordinate at a row past n is an entry of that zero row",
						By(rowsVanish, past, TransposeDef, vec_space.VecZeroDef))
				}))

			a.Show(
				"the two conditions together are membership in the m×n matrices",
				By(rowsEnd, rowsAreVectors, MatrixDef))
		}),
})}

// TransposeMatrixMul — the transpose reverses a product, and the whole
// of the reason is that the form is symmetric. At one entry the two
// sides pair the SAME two vectors: the (i, j) entry of the transposed
// product is the j-th row of P against the i-th column of Q, and the
// (i, j) entry of the reversed product is the i-th column of Q against
// the j-th row of P — that row being what the second reflection gives
// back. So the reversal is the form read at one pair of vectors in the
// two orders, and the ring's commutativity is spent once, inside the
// form's symmetry, rather than again here.
var TransposeMatrixMul = transposeMatrixMulThm{family.Add(registry.ProofEntry{
	Name: "TransposeMatrixMul",
	Key:  "prop_4009165d2211dbb9",
	Build: comm_ring.CommRing.Law(
		"∀k:num. ∀P Q:(num → num → A). "+
			"    transpose(matrix_mul(k, P, Q)) = matrix_mul(k, transpose(Q), transpose(P))",
		func(a *Argument, ring Fact, k *Expr[Nat], P, Q *Arrow2[Nat, Nat, A]) {
			a.Do(Funext())
			a.Fix("i")
			a.Fix("j")

			row := a.VecAs[A, DimK]("P(j)")
			column := a.VecAs[A, DimK]("transpose(Q, i)")

			a.Show(
				"the two entries are one form at one pair of vectors, read in the two orders",
				CalcEq(
					Leg(
						a.Term("⟪P(j), transpose(Q, i)⟫_k"),
						"the (i, j) entry of the transpose is the (j, i) entry of the "+
							"product, which pairs the j-th row of P with the i-th column of Q",
						By(TransposeDef, MatrixMulDef)),
					Leg(
						a.Term("⟪transpose(Q, i), P(j)⟫_k"),
						"the form is symmetric, so those two may be paired the other way round",
						By(dot.Sym.Read(ring).At(row, column))),
					FinalLeg(
						"and that is the reversed product's (i, j) entry — its second "+
							"factor is transpose(P), whose i-th column is P's i-th row",
						Simp(Fwd(MatrixMulDef), Fwd(TransposeTranspose)),
						Refl()),
				))
		}),
})}

// AdjointIsTranspose — the adjoint that vector/dot BUILDS out of the
// form is the transposed matrix acting, and the two dimensions mean on
// the right exactly what they mean on the left: m bounds the
// coordinates the value has, n is the dimension the form is read at.
//
// Both sides are sequences, so they are compared one coordinate at a
// time, and the coordinate is where the adjoint's guard sits. Either
// way the action reads the form against the row the transpose offers
// at that coordinate — which is the corresponding COLUMN of the matrix
// of the map — so each branch is a question about that column, and the
// same condition settles it on both sides: the reflection puts the
// adjoint's coordinate in the COLUMN index, which is the index
// `matrix_of` cuts at m. What the column is there is `MatrixOfColumn`,
// and it leaves each branch with one step — below m the two forms are
// one form, and past m the form against the zero vector is the ring's
// zero, which is what the adjoint writes.
//
// Nothing is asked of f: not linearity, not where its values land. The
// adjoint is built rather than demanded, and so is the matrix, so this
// is an identity between two constructions rather than a theorem about
// a map.
var AdjointIsTranspose = adjointIsTransposeThm{family.Add(registry.ProofEntry{
	Name: "AdjointIsTranspose",
	Key:  "prop_87d36e3b11c5fe3d",
	Build: comm_ring.CommRing.Law(
		"∀m n:num. ∀f:((num → A) → (num → A)). ∀y:(num → A). "+
			"    adjoint(m, n, f, y) = matrix_act⟨n⟩(transpose(matrix_of(m, f)), y)",
		func(a *Argument, ring Fact, m, n *Expr[Nat], f *Arrow[Fun[Nat, A], Fun[Nat, A]], y *Vec[A, DimN]) {
			a.Do(Funext())
			a.Fix("j")
			a.Cases(a.Term("j < m"))
			a.When(
				"j < m: the column is the image of the basis vector "+
					"there, which is the vector the adjoint pairs with y",
				func(b *Argument, below Fact) {
					// The action's coordinate is the form against the column,
					// so the column is what the branch has to identify —
					// and only once the action has been read as that form,
					// which is why the unfold comes first.
					b.Do(Unfold(MatrixActDef))
					column := b.Have(
						"below m the column the action reads is the image of the basis vector standing there",
						"transpose(matrix_of(m, f), j) = f(basis_vector(j))",
						By(below, MatrixOfColumn))
					b.Show(
						"so the action reads the form at that image, which is the coordinate the adjoint writes below m",
						column.Rw(),
						Unfold(dot.AdjointDef),
						By(below))
				})
			a.Otherwise(
				"past m: the column is the zero vector, and the form "+
					"against it is the padding value the adjoint writes",
				func(b *Argument, past Fact) {
					b.Do(Unfold(MatrixActDef))
					column := b.Have(
						"past m the column the action reads is the zero vector",
						"transpose(matrix_of(m, f), j) = vec_zero",
						By(past, MatrixOfColumn))
					b.Show(
						"and the form annihilates the zero vector, landing on the ring's zero — the coordinate past m",
						column.Rw(),
						Unfold(dot.AdjointDef),
						By(past, dot.ZeroLeft.Read(ring).At(y)))
				})
		}),
})}
