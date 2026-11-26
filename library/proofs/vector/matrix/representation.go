// representation.go — the matrix a map is read off its basis, and the
// matrix that reading gives back.
//
// `matrix_of(zero, one, m, f)` is built one column at a time, and the
// first theorem below reads a column back off it. What the definition
// writes past m is `zero`, guarding the COLUMN index and nothing
// else, and the second theorem is what that costs: membership in the
// n×m matrices asks two things, and they come from opposite places.
//
// The third reads the construction backwards, at a matrix rather than
// at an arbitrary map: let the matrix act, and take the matrix of that
// action. Below m each column comes back off the basis vector standing
// at it; past m there is no column to recover, and a sequence of rows
// that are m wide has nothing there either.
//
// Then the two theorems the construction exists for. That the matrix
// ACTS as the map is what makes `matrix_of` a representation rather
// than a table of numbers, and it is true of the map itself — not of
// its truncation — because only the column index is guarded. And the
// matrix of a COMPOSITE is the product of the matrices, which is the
// first of those two read at one vector: the image of a basis vector
// under the inner map. Nothing in that argument asks the inner map to be
// linear; it is consulted only at basis vectors, and only where its
// values land matters.

package matrix

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// MatrixOfColumn — column j of a map's matrix is the image of the
// j-th basis vector, and past m it is the zero vector.
//
// The column is read one coordinate at a time: the reflection puts the
// coordinate in the row slot and j in the column slot, which is the
// index the definition guards. The guard does not read the coordinate,
// so all that is being said is that it commutes with taking one.
//
// One guarded equation rather than two implications: the two members
// that read a column — the matrix of a composite, and the adjoint as a
// transpose — each meet it inside a branch that has already decided
// the guard, and each was proving its own half inline.
//
// Nothing is asked of f, and no ring law is spent — the components are
// spelled rather than left implicit, which is this chapter's sign for
// that.
var MatrixOfColumn = matrixOfColumnThm{family.Add(registry.ProofEntry{
	Name: "MatrixOfColumn",
	Key:  "prop_12a49996011363e7",
	Build: family.Theorem(
		"∀zero one:A. ∀m j:num. ∀f:((num → A) → (num → A)). "+
			"    transpose(matrix_of(zero, one, m, f), j) = "+
			"    COND(j < m, f(basis_vector(zero, one, j)), vec_zero(zero))",
		func(a *Argument, zero, one *Expr[A], m, j *Expr[Nat], f *Arrow[Fun[Nat, A], Fun[Nat, A]]) {
			a.Do(Funext())
			a.Cases(a.Term("j < m"))
			a.When(
				"a column below m, where the guard passes whatever coordinate is read",
				func(b *Argument, below Fact) {
					b.Show(
						"so each entry is the coordinate the image has there",
						By(Normalized, below, TransposeDef, MatrixOfDef))
				})
			a.Otherwise(
				"a column at or past m, where the guard fails whatever coordinate is read",
				func(b *Argument, past Fact) {
					b.Show(
						"so each entry is the padding value, which is what the zero vector carries",
						By(Normalized, past, TransposeDef, MatrixOfDef, vec_space.VecZeroDef))
				})
		}),
})}

// MatrixOfMatrix — the matrix of a map between two dimensions has
// those dimensions.
//
// The column condition is free: past m the guard fails on its own and
// the entry is the padding value, so every row is an m-vector with
// nothing asked of f at all.
//
// The row condition is what the hypothesis buys, and is the only place
// it is spent. Past a column m the entry is that same padding value;
// below m it is a coordinate of f at the basis vector there, which is
// an m-vector, so the hypothesis places its image in dimension n and
// the coordinate — read at a row past n — vanishes. Either way every
// entry of the row is the padding value, and the row is the zero
// vector.
//
// So the hypothesis says only where the values of f live, which is the
// whole price of guarding on one index. Linearity is not among the
// hypotheses and is not needed: where the rows stop is decided by f's
// values, never by how f combines its arguments. Nor is either value
// asked to be a ring element — `zero` and `one` enter only as what the
// definitions write and read — so the statement holds over ANY two
// values and spells them explicitly, which is the visible sign that no
// ring law is spent.
var MatrixOfMatrix = matrixOfMatrixThm{family.Add(registry.ProofEntry{
	Name: "MatrixOfMatrix",
	Key:  "prop_39a95cad39a3903a",
	Build: family.Theorem(
		Statement{
			Binders: "∀zero one:A. ∀n m:num. ∀f:((num → A) → num → A).",
			Hypotheses: []string{
				"∀u:(num → A). vec⟨m⟩(zero, u) ⇒ vec⟨n⟩(zero, f(u))",
			},
			Conclusion: "matrix⟨n, m⟩(zero, matrix_of(zero, one, m, f))",
		},
		func(
			a *Argument,
			zero, one *Expr[A],
			n, m *Expr[Nat],
			f *Arrow[Fun[Nat, A], Fun[Nat, A]],
			bounded Fact,
		) {
			rowsAreVectors := a.Have(
				"every row is an m-vector, and f is never consulted for it",
				"∀i:num. vec⟨m⟩(matrix_of(m, f)(i))",
				Derive(func(b *Argument) {
					b.Fix("i")
					b.Do(Unfold(vec_space.VecDef))
					j := b.FixAs[Nat]("j")
					past := b.Assume()
					b.Show(
						"a column at or past m is not below m, so the guard fails and the entry is the padding value",
						Unfold(MatrixOfDef),
						By(past, nat_order.NotLessThan.At(j, m)))
				}))

			rowsEnd := a.Have(
				"and past the row range every entry of the row vanishes, so the row is the zero vector",
				"∀i:num. n ≤ i ⇒ matrix_of(m, f)(i) = vec_zero",
				Derive(func(b *Argument) {
					b.Fix("i")
					past := b.Assume()
					b.Do(Funext())
					b.Fix("j")
					b.Do(Unfold(MatrixOfDef), Unfold(vec_space.VecZeroDef))
					below := b.Assuming(
						b.Term("j < m"),
						"a column at or past m, where the entry is the padding value and f is not read at all",
						Given(func(c *Argument, beyond Fact) {
							c.Show(
								"the guard decides it on its own",
								By(beyond))
						}))
					inRange := b.Have(
						"the basis vector at a column below m is an m-vector",
						"vec⟨m⟩(basis_vector(j))",
						By(below, vec_space.VecBasisVector))
					image := b.Have(
						"so the hypothesis places its image in dimension n",
						"vec⟨n⟩(f(basis_vector(j)))",
						By(inRange, bounded))
					b.Show(
						"and a coordinate of an n-vector at a row past n is the padding value",
						By(Normalized, below, past, image, vec_space.VecDef))
				}))

			a.Show(
				"which are the two conditions membership in the n×m matrices asks for",
				By(rowsEnd, rowsAreVectors, MatrixDef))
		}),
})}

// MatrixOfAct — the round trip: a matrix is the matrix of the map it
// defines.
//
// Both sides are read entry by entry, so the argument runs at one
// entry, and the guard on the column index splits it in two.
//
// Below m the entry is the i-th row paired with the basis vector
// standing at column j, and a form against a basis vector reads the
// coordinate there. The law that says so keeps the basis vector on the
// LEFT of the form, where the action leaves it on the right, so one
// application of symmetry turns the pairing round before the law can
// speak; what it reads is then the entry the right-hand side has at
// (i, j).
//
// At or past m the left entry is the padding value the definition
// writes where there is no basis vector to take the image of, and the
// right entry is whatever the sequence of rows carries there. That the
// two agree is exactly what the hypothesis says, and it is the only
// thing the hypothesis is asked for: without it the statement is
// false, since a row may carry anything past column m and `matrix_of`,
// which never looks past m, cannot see it.
//
// So all that is asked is how WIDE the rows are. Where they stop is
// never consulted — nothing here enumerates the rows, and the round
// trip is blind to a bound on them — so the statement asks for the
// width alone rather than for membership in the n×m matrices.
var MatrixOfAct = matrixOfActThm{family.Add(registry.ProofEntry{
	Name: "MatrixOfAct",
	Key:  "prop_397f74105875d9c7",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀m:num. ∀P:(num → num → A).",
			Hypotheses: []string{
				"∀i:num. vec⟨m⟩(P(i))",
			},
			Conclusion: "matrix_of(m, matrix_act⟨m⟩(P)) = P",
		},
		func(a *Argument, ring Fact, m *Expr[Nat], P *Arrow2[Nat, Nat, A], rows Fact) {
			a.Do(Funext())
			i := a.FixAs[Nat]("i")
			j := a.FixAs[Nat]("j")

			// What the construction writes at that entry is decided by
			// one guard, on the column index alone, so the definition is
			// opened in each branch of the split on it.
			a.Cases(a.Term("j < m"))
			a.When(
				"a column below m, where the entry is the action read at the basis vector standing there",
				func(b *Argument, below Fact) {
					row := b.VecAs[A, DimM]("P(i)")
					basis := b.VecAs[A, DimM]("basis_vector(j)")
					// Opened as a rule, the construction's guard is decided by the
					// branch's hypothesis as the rule fires.
					b.Show(
						"and that action is the i-th row paired with the basis vector",
						Simp(Fwd(MatrixOfDef), Fwd(MatrixActDef)),
						CalcEq(
							Leg(
								b.Term("⟪basis_vector(j), P(i)⟫_m"),
								"the form is symmetric, which puts the basis vector where the law reads it",
								By(dot.Sym.Read(ring).At(row, basis))),
							FinalLeg(
								"and against the basis vector standing at j the form is the row's own entry there",
								By(below, dot.BasisVectorLeft.Read(ring).At(j, row))),
						))
				})
			a.Otherwise(
				"a column at or past m, where the entry is the padding value",
				func(b *Argument, past Fact) {
					b.Show(
						"and the row is an m-vector, so it carries that same "+
							"value at j — the one place the hypothesis is spent",
						Unfold(MatrixOfDef),
						By(Normalized, past, rows.At(i), nat_order.NotLessThan.At(j, m), vec_space.VecDef))
				})
		}),
})}

// MatrixWorks — both sides are vectors, so the argument runs at one
// coordinate, where the two descend to the same fold over the column
// range.
//
// On the left, the action at a coordinate is the row of the matrix
// paired with the vector, which is the fold of the products of the
// entries; inside the column range the definition's guard passes, so
// each entry there is a coordinate of the image of a basis vector. On
// the right, the vector is read through the standard basis — the one
// place the hypothesis on it is spent, and the reason the statement
// carries it — linearity carries the map across that fold and takes
// each coordinate out of its summand, and the fold of vectors is read
// at a coordinate by crossing to the ring's own fold. What separates
// the two families of summands is then the order of one product, which
// commutativity settles inside the range the fold reads.
var MatrixWorks = matrixWorksThm{family.Add(registry.ProofEntry{
	Name: "MatrixWorks",
	Key:  "prop_e39403f46c6e1a17",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀m:num. ∀f:((num → A) → num → A). ∀x:(num → A).",
			Hypotheses: []string{
				"vec_linear(f)",
				"vec⟨m⟩(x)",
			},
			Conclusion: "matrix_act⟨m⟩(matrix_of(m, f), x) = f(x)",
		},
		func(a *Argument, ring Fact, m *Expr[Nat], f *Arrow[Fun[Nat, A], Fun[Nat, A]],
			x *Vec[A, DimM], linear Fact, member Fact) {
			// The vector carries its membership, so the one cite that
			// spends it travels with the evidence.
			xM := proof.Inhabit(x, member)

			finite := a.Have(
				"the column range is finite",
				"finite({j:num | j < m})",
				Cite(num_segment.FiniteBelowStrict))

			// The half of linearity this argument spends in the open; the
			// other half rides inside the fold law below.
			homogeneous := a.Have(
				"f commutes with the scalar action",
				"∀c:A. ∀u:(num → A). f(c • u) = c • f(u)",
				By(linear, vec_space.VecLinearDef))
			expansion := a.Have(
				"and x is the sum of its coordinates against the standard basis",
				"x = Σ_{j<m} x(j) • basis_vector(j)",
				By(vec_space.BasisExpansion.Read(ring).At(xM)))

			imageAsFold := a.Have(
				"so the image of x is the fold of its coordinates against the images of the basis vectors",
				"f(x) = Σ_{j<m} x(j) • f(basis_vector(j))",
				CalcEq(
					Leg(
						a.Term("f(Σ_{j<m} x(j) • basis_vector(j))"),
						"read x through the basis",
						By(expansion)),
					Leg(
						a.Term("Σ_{j<m} f(x(j) • basis_vector(j))"),
						"a linear map carries that sum to the sum of the images",
						By(linear, finite, vec_space.LinearIterate.Read(ring))),
					FinalLeg(
						"and takes the coordinate out of every summand, so the two families of summands are one family",
						Congr(),
						Funext(),
						By(homogeneous)),
				))

			a.Do(Funext())
			i := a.FixAs[Nat]("i")

			summand := a.Have(
				"each summand inside the column range is the i-th coordinate of the scaled image of a basis vector",
				"∀k:num. k ∈ {j:num | j < m} ⇒ matrix_of(m, f, i, k) * x(k) = (x(k) • f(basis_vector(k)))(i)",
				Derive(func(b *Argument) {
					b.Fix("k")
					inRange := b.Assume()
					below := b.Have(
						"the index lies below m",
						"k < m",
						BySets(inRange))
					b.Show(
						"the guard the definition asks about is the range "+
							"condition itself, and the two products differ only in order",
						Unfold(MatrixOfDef),
						Unfold(vec_space.VecScalarMulDef),
						By(below, comm_ring.MulMonoid.Read(ring), comm_monoid.Comm))
				}))

			// The fold of vectors the right-hand side is, read once as the Σ
			// the reading of the image shows: its range and its summand are
			// what the coordinatewise law takes.
			fold := a.BigOpAs[Nat, Fun[Nat, A]]("Σ_{j<m} x(j) • f(basis_vector(j))")

			a.Show(
				"so the two vectors agree at that coordinate",
				CalcEq(
					Leg(
						a.Term("⟪matrix_of(m, f, i), x⟫_m"),
						"the action at i pairs the i-th row of the matrix with x",
						Unfold(MatrixActDef)),
					Leg(
						a.Term("Σ_{j<m} matrix_of(m, f, i, j) * x(j)"),
						"and that pairing is the fold of the products over the column range",
						Unfold(dot.DotDef)),
					Leg(
						a.Term("Σ_{j<m} (x(j) • f(basis_vector(j)))(i)"),
						"the summands agree on the column range, which is everywhere the fold reads them",
						By(summand, comm_ring.MonoidalAdd.Read(ring), monoidal.Congruence)),
					Leg(
						a.Term("(Σ_{j<m} x(j) • f(basis_vector(j)))(i)"),
						"so that fold of coordinates is the i-th coordinate of the fold of vectors",
						By(finite, vec_space.IterateAt.Read(ring).At(fold.Range(), fold.Summand(), i))),
					FinalLeg(
						"which is the image of x",
						By(imageAsFold)),
				))
		}),
})}

// MatrixCompose — the contracted dimension is n, the one the two
// matrices are read at, and the column index is cut at m on both
// sides, so the case split the guard asks for is the whole shape of
// the proof.
//
// Only g is asked to be linear. f enters through its VALUES alone:
// each side reads it at a basis vector and nowhere else, and the
// hypothesis on it says only where those values live — which is what
// puts them in the dimension `MatrixWorks` wants. How f combines its
// arguments is never consulted, so linearity of f is neither assumed
// nor needed.
var MatrixCompose = matrixComposeThm{family.Add(registry.ProofEntry{
	Name: "MatrixCompose",
	Key:  "prop_cc762419ee125082",
	Build: comm_ring.CommRing.Law(
		Statement{
			Binders: "∀m n:num. ∀f g:((num → A) → num → A).",
			Hypotheses: []string{
				"vec_linear(g)",
				"∀u:(num → A). vec⟨m⟩(u) ⇒ vec⟨n⟩(f(u))",
			},
			Conclusion: "matrix_of(m, g ∘ f) = matrix_mul(n, matrix_of(n, g), matrix_of(m, f))",
		},
		func(a *Argument, ring Fact, m, n *Expr[Nat], f, g *Arrow[Fun[Nat, A], Fun[Nat, A]],
			linear, bounded Fact) {
			// An entry of the product is the i-th row of g's matrix paired
			// with the j-th column of f's.
			a.Do(Funext())
			a.Fix("i")
			a.Fix("j")
			a.Do(Unfold(MatrixMulDef))

			below := a.Assuming(
				a.Term("j < m"),
				"a column at or past m, where neither side reads f: the left entry "+
					"is the padding value, and the right column is the zero vector",
				Given(func(b *Argument, past Fact) {
					columnIsZero := b.Have(
						"past the column range the column the product contracts against is the zero vector",
						"transpose(matrix_of(m, f), j) = vec_zero",
						By(past, MatrixOfColumn))
					b.Show(
						"and the form against the zero vector is the ring's "+
							"zero, which is what the guard leaves on the left",
						By(past, columnIsZero, MatrixOfDef, dot.ZeroRight.Read(ring)))
				}))

			// Below m the column is not padding: it is the image of the
			// basis vector standing there.
			columnIsImage := a.Have(
				"below m the j-th column of f's matrix is the image of the j-th basis vector",
				"transpose(matrix_of(m, f), j) = f(basis_vector(j))",
				By(below, MatrixOfColumn))

			basisIsVector := a.Have(
				"the basis vector at a column below m is an m-vector",
				"vec⟨m⟩(basis_vector(j))",
				By(below, vec_space.VecBasisVector))
			imageInN := a.Have(
				"so the hypothesis places its image in dimension n",
				"vec⟨n⟩(f(basis_vector(j)))",
				By(bounded, basisIsVector))
			actsAsG := a.Have(
				"and there g's matrix acts as g does — the one place linearity is spent",
				"matrix_act⟨n⟩(matrix_of(n, g), f(basis_vector(j))) = g(f(basis_vector(j)))",
				By(linear, imageInN, MatrixWorks.Read(ring)))

			a.Show(
				"so both entries are the composite's value at the basis vector, read at the row",
				CalcEq(
					Leg(
						a.Term("g(f(basis_vector(j)), i)"),
						"below m the guard passes, and the composite at a point is g of f of it",
						Unfold(functions.ComposeApply),
						By(below, MatrixOfDef)),
					FinalLeg(
						"which is g's matrix acting on that column, and that action is the form the product contracts",
						By(Normalized, columnIsImage, actsAsG, MatrixActDef)),
				))
		}),
})}
