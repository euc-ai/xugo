// action.go — what a matrix does to a vector, and what two of them do
// in succession.
//
// The action is the form applied row by row, so everything here is a
// law of `⟪·, ·⟫_k` re-read one coordinate at a time: the value stops
// where the matrix's rows stop, and it is linear in the vector because
// the form is linear in its second argument. The product joins the file
// because it is where the action leads — an n×k matrix after a k×m one
// is the action of a single n×m matrix, and both facts about the
// product here are facts about the form.
//
// The interchange of the two sums that associativity looks like is
// never performed in the open. It sits inside `dot.IterateLeft` —
// pairing against a fixed vector crosses a fold of vectors — which is
// the fold mechanism's homomorphism law wearing the form's clothes, and
// which costs neither a ring rearrangement nor a second congruence.

package matrix

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// MatrixActVec — an n×m matrix sends every vector into dimension n.
//
// No hypothesis on the vector: the row range is what bounds the value,
// and past n there is no row left to read. The chapter's one design
// decision pays here — a row that has run out is the zero VECTOR rather
// than junk, so the coordinate is the form against the zero vector,
// which is the ring's zero.
var MatrixActVec = matrixActVecThm{family.Add(registry.ProofEntry{
	Name: "MatrixActVec",
	Key:  "prop_f7cc774d9f784192",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀n m:num. ∀P:(num → num → A). ∀x:(num → A).",
			Hypotheses: []string{
				"matrix⟨n, m⟩(R.zero, P)",
			},
			Conclusion: "vec⟨n⟩(R.zero, matrix_act⟨m⟩(R.add, R.mul, P, x))",
		},
		func(a *Argument, ring Fact, n, m *Expr[Nat], P *Mat[A, DimN, DimM], x *Vec[A, DimM], member Fact) {
			rowsEnd := a.Have(
				"past the row range a row is the zero vector",
				"∀i:num. n ≤ i ⇒ P(i) = vec_zero(R.zero)",
				By(member, MatrixDef))

			a.Do(Unfold(vec_space.VecDef))
			a.Fix("i")
			past := a.Assume()
			rowIsZero := a.Have(
				"so this row is the zero vector",
				"P(i) = vec_zero(R.zero)",
				By(rowsEnd, past))
			a.Show(
				"and the coordinate is the form against the zero vector, which is the ring's zero",
				Unfold(MatrixActDef),
				rowIsZero.Rw(),
				By(dot.ZeroLeft.Read(ring).At(x)))
		}),
})}

// MatrixActLinear — nothing about the rows is spent here, and no
// dimension hypothesis appears: the rows are an arbitrary sequence.
//
// A coordinate of the value is the form read at a FIXED first
// argument — the row standing at that coordinate — so the two things
// linearity asks of a map on sequences are the form's additivity and
// its homogeneity in the SECOND argument. Each half is an equality of
// maps, settled at an arbitrary coordinate; the pointwise sum and the
// scalar action are what the other side reads there, which is where
// the two sides meet.
var MatrixActLinear = matrixActLinearThm{family.Add(registry.ProofEntry{
	Name: "MatrixActLinear",
	Key:  "prop_50162cb645df4556",
	Build: comm_ring.CommRing.Law("∀k:num. ∀P:(num → num → A). vec_linear(matrix_act⟨k⟩(P))",
		func(a *Argument, ring Fact, k *Expr[Nat], P *Arrow2[Nat, Nat, A]) {
			a.Show(
				"linearity asks two things of a map on sequences, "+
					"and each is a law of the form in its second argument",
				Unfold(vec_space.VecLinearDef),
				SplitConj(
					Case(
						"the action carries a pointwise sum to the pointwise sum",
						Derive(func(b *Argument) {
							u := b.VecFixAs[A, DimK]("u")
							v := b.VecFixAs[A, DimK]("v")
							b.Do(Funext())
							b.Fix("i")
							row := b.VecAs[A, DimK]("P(i)")
							b.Show(
								"coordinate i is the i-th row paired with the sum, where the form splits",
								Unfold(MatrixActDef),
								CalcEq(
									Leg(
										b.Term("⟪P(i), u⟫_k + ⟪P(i), v⟫_k"),
										"the form is additive in its second argument",
										By(dot.AddRight.Read(ring).At(row, u, v))),
									FinalLeg(
										"and that sum is the two coordinates of the pointwise sum, each read at i",
										Unfold(vec_space.VecAddDef)),
								))
						})),
					Case(
						"and commutes with the scalar action",
						Derive(func(b *Argument) {
							c := b.FixAs[A]("c")
							u := b.VecFixAs[A, DimK]("u")
							b.Do(Funext())
							b.Fix("i")
							row := b.VecAs[A, DimK]("P(i)")
							b.Show(
								"coordinate i is that same row paired with the scaled vector, and the scalar comes out",
								Unfold(MatrixActDef),
								CalcEq(
									Leg(
										b.Term("c * ⟪P(i), u⟫_k"),
										"the form gives up a scalar on its second argument",
										By(dot.SmulRight.Read(ring).At(c, row, u))),
									FinalLeg(
										"and the scalar multiple is the coordinate read at i",
										Unfold(vec_space.VecScalarMulDef)),
								))
						})),
				))
		}),
})}

// MatrixMulMatrix — the two halves are the same argument on opposite
// sides of the form, and what separates them belongs to the carrier
// rather than to the form: a row of the left matrix is already a
// vector, so the row half has its zero vector for the asking, while a
// column of the right matrix is a vector only through the reflection.
// Transposed, the right factor is an m×k matrix, and the zero vector
// the column half wants is where THAT matrix's rows run out.
var MatrixMulMatrix = matrixMulMatrixThm{family.Add(registry.ProofEntry{
	Name: "MatrixMulMatrix",
	Key:  "prop_702b6f93d919247a",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀n k m:num. ∀P Q:(num → num → A).",
			Hypotheses: []string{
				"matrix⟨n, k⟩(P)",
				"matrix⟨k, m⟩(Q)",
			},
			Conclusion: "matrix⟨n, m⟩(matrix_mul(k, P, Q))",
		},
		func(
			a *Argument,
			ring Fact,
			n, k, m *Expr[Nat],
			P *Mat[A, DimN, DimK],
			Q *Mat[A, DimK, DimM],
			left, right Fact,
		) {
			rowsEnd := a.Have(
				"past the row range the left matrix's row is the zero vector",
				"∀i:num. n ≤ i ⇒ P(i) = vec_zero",
				By(left, MatrixDef))
			columnsEnd := a.Have(
				"and past the column range the right matrix's column "+
					"— a row of its m×k transpose — is the zero vector",
				"∀j:num. m ≤ j ⇒ transpose(Q, j) = vec_zero",
				By(right, TransposeMatrix, MatrixDef))

			rowsVanish := a.Have(
				"past the row range the product has no row left",
				"∀i:num. n ≤ i ⇒ matrix_mul(k, P, Q, i) = vec_zero",
				Derive(func(b *Argument) {
					b.Fix("i")
					past := b.Assume()
					rowIsZero := b.Have(
						"the left matrix's row here is the zero vector",
						"P(i) = vec_zero",
						By(rowsEnd, past))
					b.Do(Funext())
					b.Fix("j")
					column := b.VecAs[A, DimK]("transpose(Q, j)")
					b.Show(
						"and each entry of that row is the form annihilating the zero vector on the left",
						Unfold(MatrixMulDef),
						rowIsZero.Rw(),
						By(dot.ZeroLeft.Read(ring).At(column), vec_space.VecZeroDef))
				}))

			rowsAreVectors := a.Have(
				"and each row of the product is an m-vector",
				"∀i:num. vec⟨m⟩(matrix_mul(k, P, Q, i))",
				Derive(func(b *Argument) {
					b.Fix("i")
					b.Do(Unfold(vec_space.VecDef))
					b.Fix("j")
					past := b.Assume()
					b.Do(Unfold(MatrixMulDef))
					columnIsZero := b.Have(
						"the right matrix's column here is the zero vector",
						"transpose(Q, j) = vec_zero",
						By(columnsEnd, past))
					row := b.VecAs[A, DimK]("P(i)")
					b.Show(
						"and the entry is the form annihilating the zero vector on the right",
						columnIsZero.Rw(),
						By(dot.ZeroRight.Read(ring).At(row)))
				}))

			a.Show(
				"the two conditions together are membership in the n×m matrices",
				By(rowsVanish, rowsAreVectors, MatrixDef))
		}),
})}

// MatrixActAssoc — no hypothesis: neither matrix is asked to have a
// dimension, and the two contracted ranges stay independent, k on the
// outside and n on the inside. The ring is asked for two things and no
// more — that its addition folds, and that the form gives up a scalar
// from its first argument; everything else is the fold mechanism.
//
// At a coordinate the composite is the left matrix's row paired with the
// vector the inner action produced, which is the fold over the outer
// range of that row's entries scaling the inner forms. Each entry goes
// back inside the form, so the summands become the forms of the right
// matrix's rows, each scaled by an entry, against the vector — and
// pairing against a fixed vector is additive, so it crosses that fold of
// vectors. What is left
// is the form at a single vector, the right matrix's rows folded with
// the row of the left one as weights, and that vector is the product's
// row: its entry at a column is the fold read there, which is the row
// against the column the product is defined as. So the interchange of
// the two summations is never performed in the open; it sits inside the
// law that carries the form across a fold.
var MatrixActAssoc = matrixActAssocThm{family.Add(registry.ProofEntry{
	Name: "MatrixActAssoc",
	Key:  "prop_28ced6f2f8269a02",
	Build: comm_ring.CommRing.Law(
		"∀k n:num. ∀P Q:(num → num → A). ∀x:(num → A). "+
			"    matrix_act⟨k⟩(P, matrix_act⟨n⟩(Q, x)) = matrix_act⟨n⟩(matrix_mul(k, P, Q), x)",
		func(a *Argument, ring Fact, k, n *Expr[Nat], P, Q *Arrow2[Nat, Nat, A], x *Vec[A, DimN]) {
			a.Do(Funext())
			a.Fix("i")

			finite := a.Have(
				"the contracted range is finite",
				"finite({l:num | l < k})",
				Cite(num_segment.FiniteBelowStrict))

			rowOfProduct := a.Have(
				"the product's i-th row is the right factor's rows weighted by the left factor's i-th row",
				"matrix_mul(k, P, Q, i) = Σ_{l<k} P(i, l) • Q(l)",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.Fix("j")
					b.Show(
						"at column j the entry is the row against the column, and the "+
							"weighted fold of rows read at j is that same fold of entries",
						Unfold(MatrixMulDef),
						Unfold(TransposeDef),
						Unfold(dot.DotDef),
						Unfold(vec_space.VecScalarMulDef),
						By(finite, vec_space.IterateAt.Read(ring)))
				}))

			scalarIn := a.Have(
				"everywhere the outer fold reads, its summand is the form at the row scaled by that entry",
				"∀l:num. l ∈ {m:num | m < k} ⇒ P(i, l) * ⟪Q(l), x⟫_n = ⟪P(i, l) • Q(l), x⟫_n",
				By(dot.SmulLeft.Read(ring)))

			a.Show(
				"so at that coordinate the two actions come to one",
				CalcEq(
					Leg(
						a.Term("Σ_{l<k} P(i, l) * ⟪Q(l), x⟫_n"),
						"acting twice is, at i, the fold of the left factor's "+
							"entries against the inner action's coordinates",
						Unfold(MatrixActDef),
						Unfold(dot.DotDef)),
					Leg(
						a.Term("Σ_{l<k} ⟪P(i, l) • Q(l), x⟫_n"),
						"whose summands, each entry having gone back inside the form, agree everywhere the fold reads them",
						By(scalarIn, comm_ring.MonoidalAdd.Read(ring), monoidal.Congruence)),
					Leg(
						a.Term("⟪Σ_{l<k} P(i, l) • Q(l), x⟫_n"),
						"pairing against x is additive, so it crosses the fold of those weighted rows",
						By(finite, dot.IterateLeft.Read(ring))),
					Leg(
						a.Term("⟪matrix_mul(k, P, Q, i), x⟫_n"),
						"and the vector it is now read at is the product's i-th row",
						By(rowOfProduct)),
					FinalLeg(
						"and that row against x is the product acting on x, read at i",
						Unfold(MatrixActDef)),
				))
		}),
})}
