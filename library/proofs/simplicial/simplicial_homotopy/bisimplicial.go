// bisimplicial.go — the structure: a family of sets indexed by two
// dimensions with horizontal and vertical faces and degeneracies, and
// its axioms, each row and each column a simplicial set and each
// horizontal face or degeneracy commuting with each vertical one; maps
// of bisimplicial sets; iterated faces in a column or a row, the bottom
// vertices removed in a column and the top ones on a row, which land in
// the expected bidegree and pass a face of the other direction; the
// diagonal simplicial set, whose faces and degeneracies are the
// horizontal and vertical ones applied together; homotopies in the
// vertical direction that are natural in the horizontal one; and the
// diagonal's simplicial set, maps, homotopies and homotopy
// equivalences, read off the bisimplicial ones.

package simplicial_homotopy

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure and its axioms
// ---------------------------------------------------------------------------

// BisimplicialSet — `bisimplicial_set(X)`: `X.simplices(p, q)`, written
// X(p, q) here, is the set of (p, q)-simplices of a type A;
// `X.dh(p, q, i, x)` is the i-th horizontal face of x, in X(p − 1, q),
// and `X.sh(p, q, i, x)` its i-th horizontal degeneracy, in X(p + 1, q);
// `X.dv(p, q, j, x)` and `X.sv(p, q, j, x)` are the vertical ones, in
// X(p, q − 1) and X(p, q + 1). Every row q and every column p is a
// simplicial set, and each horizontal map commutes with each vertical
// one.
var BisimplicialSet = bisimplicialSetThm{family.DefineStructure(registry.DefEntry{
	Name:  "BisimplicialSet",
	Key:   "prop_f5de2d9ff742c22e",
	Const: "bisimplicial_set",
	Type:  "bisimplicial_ops(A) → bool",
	Equations: []string{
		"∀X:bisimplicial_ops(A). " +
			"    bisimplicial_set(X) ⇔ " +
			"    (∀q:num. simplicial_set(bisimplicial_row(X, q))) ∧ " +
			"    (∀p:num. simplicial_set(bisimplicial_column(X, p))) ∧ " +
			"    (∀p q i j:num. ∀x:A. " +
			"        x ∈ X.simplices(p + 1, q + 1) ∧ i ≤ p + 1 ∧ j ≤ q + 1 ⇒ " +
			"        X.dh(p + 1, q, i, X.dv(p + 1, q + 1, j, x)) = " +
			"        X.dv(p, q + 1, j, X.dh(p + 1, q + 1, i, x))) ∧ " +
			"    (∀p q i j:num. ∀x:A. " +
			"        x ∈ X.simplices(p + 1, q) ∧ i ≤ p + 1 ∧ j ≤ q ⇒ " +
			"        X.dh(p + 1, q + 1, i, X.sv(p + 1, q, j, x)) = X.sv(p, q, j, X.dh(p + 1, q, i, x))) ∧ " +
			"    (∀p q i j:num. ∀x:A. " +
			"        x ∈ X.simplices(p, q + 1) ∧ i ≤ p ∧ j ≤ q + 1 ⇒ " +
			"        X.sh(p, q, i, X.dv(p, q + 1, j, x)) = X.dv(p + 1, q + 1, j, X.sh(p, q + 1, i, x))) ∧ " +
			"    (∀p q i j:num. ∀x:A. " +
			"        x ∈ X.simplices(p, q) ∧ i ≤ p ∧ j ≤ q ⇒ " +
			"        X.sh(p, q + 1, i, X.sv(p, q, j, x)) = X.sv(p + 1, q, j, X.sh(p, q, i, x)))",
	},
	Reading: "The four commutation conjuncts are stated on the simplices where " +
		"both composites are read; the row and column conjuncts carry the closures, so " +
		"a horizontal map keeps the vertical dimension and a vertical one the horizontal.",
	Deps: append(
		[]registry.EntryLike{BisimplicialRowDef, BisimplicialColumnDef}, bisimplicialFields...),
})}

// BisimplicialRows — every row of a bisimplicial set is a simplicial set.
var BisimplicialRows = bisimplicialRowsThm{family.Add(registry.ProofEntry{
	Name:  "BisimplicialRows",
	Key:   "prop_6bc181c71afc590c",
	Build: BisimplicialSet.Axiom("∀q:num. simplicial_set(bisimplicial_row(X, q))"),
})}

// BisimplicialColumns — every column of a bisimplicial set is a simplicial
// set.
var BisimplicialColumns = bisimplicialColumnsThm{family.Add(registry.ProofEntry{
	Name:  "BisimplicialColumns",
	Key:   "prop_ad87c2d303166e33",
	Build: BisimplicialSet.Axiom("∀p:num. simplicial_set(bisimplicial_column(X, p))"),
})}

// HorizontalFaceVerticalFace — a horizontal face and a vertical face
// commute on the (p + 1, q + 1)-simplices.
var HorizontalFaceVerticalFace = horizontalFaceVerticalFaceThm{family.Add(registry.ProofEntry{
	Name: "HorizontalFaceVerticalFace",
	Key:  "prop_704d552ea481fdf",
	Build: BisimplicialSet.Axiom(Statement{
		Binders: "∀p q i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(p + 1, q + 1)",
			"i ≤ p + 1",
			"j ≤ q + 1",
		},
		Conclusion: "X.dh(p + 1, q, i, X.dv(p + 1, q + 1, j, x)) = " +
			"X.dv(p, q + 1, j, X.dh(p + 1, q + 1, i, x))",
	}),
})}

// HorizontalFaceVerticalDegeneracy — a horizontal face and a vertical
// degeneracy commute on the (p + 1, q)-simplices.
var HorizontalFaceVerticalDegeneracy = horizontalFaceVerticalDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "HorizontalFaceVerticalDegeneracy",
	Key:  "prop_97dcad9d9ee003",
	Build: BisimplicialSet.Axiom(Statement{
		Binders: "∀p q i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(p + 1, q)",
			"i ≤ p + 1",
			"j ≤ q",
		},
		Conclusion: "X.dh(p + 1, q + 1, i, X.sv(p + 1, q, j, x)) = X.sv(p, q, j, X.dh(p + 1, q, i, x))",
	}),
})}

// HorizontalDegeneracyVerticalFace — a horizontal degeneracy and a
// vertical face commute on the (p, q + 1)-simplices.
var HorizontalDegeneracyVerticalFace = horizontalDegeneracyVerticalFaceThm{family.Add(registry.ProofEntry{
	Name: "HorizontalDegeneracyVerticalFace",
	Key:  "prop_8f24c2d3197b5548",
	Build: BisimplicialSet.Axiom(Statement{
		Binders: "∀p q i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(p, q + 1)",
			"i ≤ p",
			"j ≤ q + 1",
		},
		Conclusion: "X.sh(p, q, i, X.dv(p, q + 1, j, x)) = X.dv(p + 1, q + 1, j, X.sh(p, q + 1, i, x))",
	}),
})}

// HorizontalDegeneracyVerticalDegeneracy — a horizontal degeneracy and a
// vertical degeneracy commute on the (p, q)-simplices.
var HorizontalDegeneracyVerticalDegeneracy = horizontalDegeneracyVerticalDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "HorizontalDegeneracyVerticalDegeneracy",
	Key:  "prop_8ccbb019d6f633d7",
	Build: BisimplicialSet.Axiom(Statement{
		Binders: "∀p q i j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(p, q)",
			"i ≤ p",
			"j ≤ q",
		},
		Conclusion: "X.sh(p, q + 1, i, X.sv(p, q, j, x)) = X.sv(p + 1, q, j, X.sh(p, q, i, x))",
	}),
})}

// ---------------------------------------------------------------------------
// Maps of bisimplicial sets
// ---------------------------------------------------------------------------

// BisimplicialMap — `bisimplicial_map(X, Y, F)`: a map
// `F : num → num → A → B` of bisimplicial sets on two types, F(p, q)
// carrying X.simplices(p, q) into Y.simplices(p, q) and commuting with
// the faces and degeneracies of both directions.
var BisimplicialMap = bisimplicialMapThm{family.DefineStructure(registry.DefEntry{
	Name:  "BisimplicialMap",
	Key:   "prop_f08a3b58d9bb4a1f",
	Const: "bisimplicial_map",
	Type:  "bisimplicial_ops(A) → bisimplicial_ops(B) → (num → num → A → B) → bool",
	Equations: []string{
		"∀X:bisimplicial_ops(A). ∀Y:bisimplicial_ops(B). ∀F:(num → num → A → B). " +
			"    bisimplicial_map(X, Y, F) ⇔ " +
			"    bisimplicial_set(X) ∧ " +
			"    bisimplicial_set(Y) ∧ " +
			"    (∀p q:num. ∀x:A. x ∈ X.simplices(p, q) ⇒ F(p, q, x) ∈ Y.simplices(p, q)) ∧ " +
			"    (∀p q i:num. ∀x:A. " +
			"        x ∈ X.simplices(p + 1, q) ∧ i ≤ p + 1 ⇒ " +
			"        F(p, q, X.dh(p + 1, q, i, x)) = Y.dh(p + 1, q, i, F(p + 1, q, x))) ∧ " +
			"    (∀p q i:num. ∀x:A. " +
			"        x ∈ X.simplices(p, q) ∧ i ≤ p ⇒ " +
			"        F(p + 1, q, X.sh(p, q, i, x)) = Y.sh(p, q, i, F(p, q, x))) ∧ " +
			"    (∀p q j:num. ∀x:A. " +
			"        x ∈ X.simplices(p, q + 1) ∧ j ≤ q + 1 ⇒ " +
			"        F(p, q, X.dv(p, q + 1, j, x)) = Y.dv(p, q + 1, j, F(p, q + 1, x))) ∧ " +
			"    (∀p q j:num. ∀x:A. " +
			"        x ∈ X.simplices(p, q) ∧ j ≤ q ⇒ " +
			"        F(p, q + 1, X.sv(p, q, j, x)) = Y.sv(p, q, j, F(p, q, x)))",
	},
	Deps: []registry.EntryLike{BisimplicialSet},
})}

// ---------------------------------------------------------------------------
// Iterated faces in a column or a row
// ---------------------------------------------------------------------------

// ColumnFaceIterateBottomIn — removing k ≤ q bottom vertices of a
// (p, q)-simplex in its column, the 0-th vertical face taken k times,
// leaves a (p, q − k)-simplex: the column p is a simplicial set.
var ColumnFaceIterateBottomIn = columnFaceIterateBottomInThm{family.Add(registry.ProofEntry{
	Name: "ColumnFaceIterateBottomIn",
	Key:  "prop_693b1c2b2803b5bb",
	Build: BisimplicialSet.Law(Statement{
		Binders: "∀p q k:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(p, q)",
			"k ≤ q",
		},
		Conclusion: "face_iterate_bottom(λm:num. λj:num. X.dv(p, m, j), q, k, x) ∈ X.simplices(p, q - k)",
	},
		func(a *Argument, bisimplicial Fact, p, q, k *Expr[Nat], x *Expr[A], given Fact) {
			column := a.Have(
				"the column p is a simplicial set",
				"simplicial_set(bisimplicial_column(X, p))",
				By(BisimplicialColumns.Read(bisimplicial).At(p)))
			a.Show(
				"in the column p, removing k bottom vertices of a q-simplex leaves a (q − k)-simplex",
				By(given, simplicial_set.FaceIterateBottomIn.Read(column).At(q, k, x)))
		}),
})}

// RowFaceIterateTopIn — removing k ≤ p top vertices of a (p, q)-simplex
// on its row, the last horizontal face taken k times, leaves a
// (p − k, q)-simplex: the row q is a simplicial set.
var RowFaceIterateTopIn = rowFaceIterateTopInThm{family.Add(registry.ProofEntry{
	Name: "RowFaceIterateTopIn",
	Key:  "prop_bd95a27341d17473",
	Build: BisimplicialSet.Law(Statement{
		Binders: "∀p q k:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(p, q)",
			"k ≤ p",
		},
		Conclusion: "face_iterate_top(λm:num. λi:num. X.dh(m, q, i), p, k, x) ∈ X.simplices(p - k, q)",
	},
		func(a *Argument, bisimplicial Fact, p, q, k *Expr[Nat], x *Expr[A], given Fact) {
			row := a.Have(
				"the row q is a simplicial set",
				"simplicial_set(bisimplicial_row(X, q))",
				By(BisimplicialRows.Read(bisimplicial).At(q)))
			a.Show(
				"on the row q, removing k top vertices of a p-simplex leaves a (p − k)-simplex",
				By(given, simplicial_set.FaceIterateTopIn.Read(row).At(p, k, x)))
		}),
})}

// ColumnFaceIterateBottomHorizontalFace — a horizontal face passes the
// removal of k bottom vertices in the column: removing them from the
// i-th horizontal face of a (p + 1, q)-simplex x, in the column p, is the
// i-th horizontal face of x with them removed in the column p + 1. By
// induction on k: each 0-th vertical face commutes with the horizontal
// face, the two directions commuting.
var ColumnFaceIterateBottomHorizontalFace = columnFaceIterateBottomHorizontalFaceThm{family.Add(registry.ProofEntry{
	Name: "ColumnFaceIterateBottomHorizontalFace",
	Key:  "prop_d558516e8be07e1d",
	Build: BisimplicialSet.Law(Statement{
		Binders: "∀p q k i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(p + 1, q)",
			"k ≤ q",
			"i ≤ p + 1",
		},
		Conclusion: "face_iterate_bottom(λm:num. λj:num. X.dv(p, m, j), q, k, X.dh(p + 1, q, i, x)) = " +
			"X.dh(p + 1, q - k, i, face_iterate_bottom(λm:num. λj:num. X.dv(p + 1, m, j), q, k, x))",
	},
		func(a *Argument, bisimplicial Fact, p, q *Expr[Nat]) {
			a.Induct("k")
			a.Base(
				"with no vertex removed both sides are the horizontal face of x",
				Simp(Fwd(nat_monus.Sub), Fwd(simplicial_set.FaceIterateBottomDef)),
				Basic())
			a.Step(
				"commute one further 0-th vertical face across the horizontal face",
				func(b *Argument, ih Fact) {
					i := b.FixAs[Nat]("i")
					x := b.FixAs[A]("x")
					given := b.Conjuncts(
						b.Assume(),
						"the original simplex",
						"the successor iterate is in range",
						"the horizontal face is in range")
					dimensions := b.Have(
						"the preceding vertical degree is a successor",
						"k ≤ q ∧ q - k = q - suc(k) + 1",
						ByArith(given[1]))
					backCarrier := b.Have(
						"the preceding vertical iterate has its expected bidegree",
						"face_iterate_bottom(λm:num. λj:num. X.dv(p + 1, m, j), q, k, x) ∈ X.simplices(p + 1, q - k)",
						By(
							given[0],
							dimensions,
							ColumnFaceIterateBottomIn.Read(bisimplicial).At(b.TermAs[Nat]("p + 1"), q, b.TermAs[Nat]("k"), x)))
					square := b.Have(
						"the next vertical and horizontal faces commute",
						"X.dh(p + 1, "+
							"    q - suc(k), "+
							"    i, "+
							"    X.dv(p + 1, q - k, 0, face_iterate_bottom(λm:num. λj:num. X.dv(p + 1, m, j), q, k, x))) = "+
							"X.dv(p, "+
							"    q - k, "+
							"    0, "+
							"    X.dh(p + 1, q - k, i, face_iterate_bottom(λm:num. λj:num. X.dv(p + 1, m, j), q, k, x)))",
						Derive(func(c *Argument) {
							degree := c.Conjuncts(
								dimensions,
								"the previous iterate is in range",
								"the previous degree equals the next successor degree")[1]
							alignedCarrier := c.Simplified(backCarrier, Fwd(degree))
							c.Do(degree.Rw())
							zeroFace := c.Have(
								"the zeroth face is in range",
								"0 ≤ q - suc(k) + 1",
								ByArith())
							c.Show(
								"the commuting square of the two directions applies at this successor degree",
								By(
									given[2],
									zeroFace,
									alignedCarrier,
									HorizontalFaceVerticalFace.Read(bisimplicial).At(
										p,
										c.TermAs[Nat]("q - suc(k)"),
										i,
										c.TermAs[Nat]("0"),
										c.TermAs[A]("face_iterate_bottom(λm:num. λj:num. X.dv(p + 1, m, j), q, k, x)"))))
						}))
					b.Show(
						"the bottom recursion extends the commuting iterate",
						Simp(Fwd(simplicial_set.FaceIterateBottomDef)),
						By(given[2], given[0], dimensions, ih.At(i, x), square))
				})
		}),
})}

// RowFaceIterateTopVerticalFace — a vertical face passes the removal of k
// top vertices on the row: removing them from the j-th vertical face of a
// (p, q + 1)-simplex x, on the row q, is the j-th vertical face of x with
// them removed on the row q + 1. By induction on k: each last horizontal
// face commutes with the vertical face, the two directions commuting.
var RowFaceIterateTopVerticalFace = rowFaceIterateTopVerticalFaceThm{family.Add(registry.ProofEntry{
	Name: "RowFaceIterateTopVerticalFace",
	Key:  "prop_1a4081fe81a4f414",
	Build: BisimplicialSet.Law(Statement{
		Binders: "∀p q k j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(p, q + 1)",
			"k ≤ p",
			"j ≤ q + 1",
		},
		Conclusion: "face_iterate_top(λm:num. λi:num. X.dh(m, q, i), p, k, X.dv(p, q + 1, j, x)) = " +
			"X.dv(p - k, q + 1, j, face_iterate_top(λm:num. λi:num. X.dh(m, q + 1, i), p, k, x))",
	},
		func(a *Argument, bisimplicial Fact, p, q *Expr[Nat]) {
			a.Induct("k")
			a.Base(
				"with no vertex removed both sides are the vertical face of x",
				Simp(Fwd(nat_monus.Sub), Fwd(simplicial_set.FaceIterateTopDef)),
				Basic())
			a.Step(
				"commute one further last horizontal face across the vertical face",
				func(b *Argument, ih Fact) {
					j := b.FixAs[Nat]("j")
					x := b.FixAs[A]("x")
					given := b.Conjuncts(
						b.Assume(),
						"the original simplex",
						"the successor iterate is in range",
						"the vertical face is in range")
					dimensions := b.Have(
						"the preceding horizontal degree is a successor",
						"k ≤ p ∧ p - k = p - suc(k) + 1",
						ByArith(given[1]))
					frontCarrier := b.Have(
						"the preceding horizontal iterate has its expected bidegree",
						"face_iterate_top(λm:num. λi:num. X.dh(m, q + 1, i), p, k, x) ∈ X.simplices(p - k, q + 1)",
						By(
							given[0],
							dimensions,
							RowFaceIterateTopIn.Read(bisimplicial).At(p, b.TermAs[Nat]("q + 1"), b.TermAs[Nat]("k"), x)))
					square := b.Have(
						"the next horizontal and vertical faces commute",
						"X.dh(p - k, "+
							"    q, "+
							"    p - k, "+
							"    X.dv(p - k, q + 1, j, face_iterate_top(λm:num. λi:num. X.dh(m, q + 1, i), p, k, x))) = "+
							"X.dv(p - suc(k), "+
							"    q + 1, "+
							"    j, "+
							"    X.dh(p - k, q + 1, p - k, face_iterate_top(λm:num. λi:num. X.dh(m, q + 1, i), p, k, x)))",
						Derive(func(c *Argument) {
							degree := c.Conjuncts(
								dimensions,
								"the previous iterate is in range",
								"the previous degree equals the next successor degree")[1]
							alignedCarrier := c.Simplified(frontCarrier, Fwd(degree))
							c.Do(degree.Rw())
							lastFace := c.Have(
								"the last face is in range",
								"p - suc(k) + 1 ≤ p - suc(k) + 1",
								ByArith())
							c.Show(
								"the commuting square of the two directions applies at this successor degree",
								By(
									given[2],
									lastFace,
									alignedCarrier,
									HorizontalFaceVerticalFace.Read(bisimplicial).At(
										c.TermAs[Nat]("p - suc(k)"),
										q,
										c.TermAs[Nat]("p - suc(k) + 1"),
										j,
										c.TermAs[A]("face_iterate_top(λm:num. λi:num. X.dh(m, q + 1, i), p, k, x)"))))
						}))
					b.Show(
						"the top recursion extends the commuting iterate",
						Simp(Fwd(simplicial_set.FaceIterateTopDef)),
						By(given[2], given[0], dimensions, ih.At(j, x), square))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The diagonal
// ---------------------------------------------------------------------------

// BisimplicialDiagonalSimplicesDef — `bisimplicial_diagonal_simplices(X,
// n)`: the n-simplices of the diagonal, the (n, n)-simplices of X.
var BisimplicialDiagonalSimplicesDef = bisimplicialDiagonalSimplicesDefThm{family.Define(registry.DefEntry{
	Name:  "BisimplicialDiagonalSimplicesDef",
	Key:   "prop_42e4574bed1b32b7",
	Const: "bisimplicial_diagonal_simplices",
	Type:  "bisimplicial_ops(A) → num → set(A)",
	Equations: []string{
		"∀X:bisimplicial_ops(A). ∀n:num. bisimplicial_diagonal_simplices(X, n) = X.simplices(n, n)",
	},
	Deps: bisimplicialFields,
})}

// BisimplicialDiagonalFaceDef — `bisimplicial_diagonal_face(dh, dv, n, i,
// x)`: the i-th face of the diagonal n-simplex x, its i-th vertical face
// followed by the i-th horizontal one, X(n, n) → X(n, n − 1) →
// X(n − 1, n − 1).
var BisimplicialDiagonalFaceDef = bisimplicialDiagonalFaceDefThm{family.Define(registry.DefEntry{
	Name:  "BisimplicialDiagonalFaceDef",
	Key:   "prop_eaf9dbbd5022b3a",
	Const: "bisimplicial_diagonal_face",
	Type:  "(num → num → num → A → A) → (num → num → num → A → A) → num → num → A → A",
	Equations: []string{
		"∀dh dv:(num → num → num → A → A). ∀n i:num. ∀x:A. " +
			"    bisimplicial_diagonal_face(dh, dv, n, i, x) = dh(n, n - 1, i, dv(n, n, i, x))",
	},
	Reading: "The two directions commute on X(n, n) for n ≥ 1, so the horizontal face " +
		"could equally come first; at n = 0 the value is a face of a vertex, which no axiom reads.",
})}

// BisimplicialDiagonalDegeneracyDef — `bisimplicial_diagonal_degeneracy(sh,
// sv, n, i, x)`: the i-th degeneracy of the diagonal n-simplex x, its
// i-th vertical degeneracy followed by the i-th horizontal one,
// X(n, n) → X(n, n + 1) → X(n + 1, n + 1).
var BisimplicialDiagonalDegeneracyDef = bisimplicialDiagonalDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "BisimplicialDiagonalDegeneracyDef",
	Key:   "prop_7c31889123845c29",
	Const: "bisimplicial_diagonal_degeneracy",
	Type:  "(num → num → num → A → A) → (num → num → num → A → A) → num → num → A → A",
	Equations: []string{
		"∀sh sv:(num → num → num → A → A). ∀n i:num. ∀x:A. " +
			"    bisimplicial_diagonal_degeneracy(sh, sv, n, i, x) = sh(n, n + 1, i, sv(n, n, i, x))",
	},
})}

// ---------------------------------------------------------------------------
// Vertical homotopies natural in the horizontal direction
// ---------------------------------------------------------------------------

// BisimplicialVerticalHomotopy — `bisimplicial_vertical_homotopy(X, Y,
// F, G, H)`: H is a homotopy from the bisimplicial map F to G in the
// vertical direction, natural in the horizontal one. On each column p,
// `λq j x. H(p, q, j, x)` is a simplicial homotopy from the column of F
// to the column of G, and each H(·, q, j) commutes with the horizontal
// faces and degeneracies.
var BisimplicialVerticalHomotopy = bisimplicialVerticalHomotopyThm{family.DefineStructure(registry.DefEntry{
	Name:  "BisimplicialVerticalHomotopy",
	Key:   "prop_8c6143641c225239",
	Const: "bisimplicial_vertical_homotopy",
	Type: "bisimplicial_ops(A) → " +
		"bisimplicial_ops(B) → " +
		"(num → num → A → B) → " +
		"(num → num → A → B) → " +
		"(num → num → num → A → B) → " +
		"bool",
	Equations: []string{
		"∀X:bisimplicial_ops(A). " +
			"∀Y:bisimplicial_ops(B). " +
			"∀F G:(num → num → A → B). " +
			"∀H:(num → num → num → A → B). " +
			"    bisimplicial_vertical_homotopy(X, Y, F, G, H) ⇔ " +
			"    bisimplicial_map(X, Y, F) ∧ " +
			"    bisimplicial_map(X, Y, G) ∧ " +
			"    (∀p:num. " +
			"        simplicial_homotopy(bisimplicial_column(X, p), " +
			"            bisimplicial_column(Y, p), " +
			"            λq:num. F(p, q), " +
			"            λq:num. G(p, q), " +
			"            λq:num. λj:num. H(p, q, j))) ∧ " +
			"    (∀p q i j:num. ∀x:A. " +
			"        x ∈ X.simplices(p + 1, q) ∧ i ≤ p + 1 ∧ j ≤ q ⇒ " +
			"        Y.dh(p + 1, q + 1, i, H(p + 1, q, j, x)) = H(p, q, j, X.dh(p + 1, q, i, x))) ∧ " +
			"    (∀p q i j:num. ∀x:A. " +
			"        x ∈ X.simplices(p, q) ∧ i ≤ p ∧ j ≤ q ⇒ " +
			"        Y.sh(p, q + 1, i, H(p, q, j, x)) = H(p + 1, q, j, X.sh(p, q, i, x)))",
	},
	Reading: "Naturality makes H a map of bisimplicial sets from X ×_v Δ[1] to Y, whose " +
		"diagonal is a simplicial homotopy of the diagonals with components h_j = sh_j ∘ H(n, n, j).",
	Deps: []registry.EntryLike{BisimplicialMap, SimplicialHomotopy, BisimplicialColumnDef},
})}

// ---------------------------------------------------------------------------
// The diagonal: a simplicial set, maps and homotopies
// ---------------------------------------------------------------------------

// DiagonalSimplicialSet — the diagonal of a bisimplicial set is a
// simplicial set. A face of the diagonal is a vertical face followed by a
// horizontal one, and a degeneracy a vertical degeneracy followed by a
// horizontal one, so the closures are a column's and then a row's. In a
// composite of two diagonal maps the two directions commute past each
// other in the middle, and the composite is the two horizontal maps after
// the two vertical ones (the four interchange lemmas below). Each
// simplicial identity of the diagonal is then the same identity in a row
// and in a column, read back through the interchange; the two identities
// d_i s_i = d_{i+1} s_i = id take one commutation and the identity in the
// column and in the row.
var DiagonalSimplicialSet = diagonalSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "DiagonalSimplicialSet",
	Key:  "prop_6c884d3fb453a572",
	Build: family.Sections(BisimplicialSet.Statement("simplicial_set(bisimplicial_diagonal(X))"),
		func(ctx *Script, headline string) *GoalStackNode {
			// A law of a column or a commutation read at n + 1 spells n + 1 + 1
			// where these statements write n + 2, so each such reading is
			// installed as a hypothesis and the RingNf of the close folds it to
			// n + 2.
			//
			// Two diagonal faces. The lemma also concludes where the vertical
			// composite lies, X(n + 2, n), which the face identity in the row n
			// reads in the middle leg of its case.
			twoFaces := ctx.Lemma(BisimplicialSet.Statement(Statement{
				Binders: "∀n i j:num. ∀x:A.",
				Hypotheses: []string{
					"x ∈ X.simplices(n + 2, n + 2)",
					"i ≤ n + 1",
					"j ≤ n + 2",
				},
				Conclusion: "X.dv(n + 2, n + 1, i, X.dv(n + 2, n + 2, j, x)) ∈ X.simplices(n + 2, n) ∧ " +
					"bisimplicial_diagonal_face(X.dh, " +
					"    X.dv, " +
					"    n + 1, " +
					"    i, " +
					"    bisimplicial_diagonal_face(X.dh, X.dv, n + 2, j, x)) = " +
					"X.dh(n + 1, n, i, X.dh(n + 2, n, j, X.dv(n + 2, n + 1, i, X.dv(n + 2, n + 2, j, x))))",
			}),
				func(
					a *Argument,
					_ *Expr[BisimplicialOps[A]],
					bisimplicial Fact,
					n, i, j *Expr[Nat],
					x *Expr[A],
					given Fact,
				) {
					column := a.Have(
						"the column n + 2 is a simplicial set",
						"simplicial_set(bisimplicial_column(X, n + 2))",
						By(BisimplicialColumns.Read(bisimplicial).At(a.TermAs[Nat]("n + 2"))))
					next := a.TermAs[Nat]("n + 1")
					faceJ := a.TermAs[A]("X.dv(n + 2, n + 2, j, x)")
					faceJIn := a.Simplified(simplicial_set.FaceIn.Read(column).At(next, j, x))
					commute := a.Simplified(GroupPremises(
						given,
						HorizontalFaceVerticalFace.Read(bisimplicial).At(next, n, j, i, faceJ)))
					a.Show(
						"the two vertical faces stay in the column n + 2, "+
							"and the vertical face i passes the horizontal face j",
						Simp(Fwd(BisimplicialDiagonalFaceDef)),
						RingNf(),
						ByArith(given, faceJIn, commute, simplicial_set.FaceIn.Read(column).At(n, i, faceJ)))
				})

			// Two diagonal degeneracies. The lemma also concludes where the
			// vertical composite lies, X(n, n + 2), which the degeneracy identity
			// in the row n + 2 reads in the middle leg of its case.
			twoDegeneracies := ctx.Lemma(BisimplicialSet.Statement(Statement{
				Binders: "∀n i j:num. ∀x:A.",
				Hypotheses: []string{
					"x ∈ X.simplices(n, n)",
					"i ≤ n + 1",
					"j ≤ n",
				},
				Conclusion: "X.sv(n, n + 1, i, X.sv(n, n, j, x)) ∈ X.simplices(n, n + 2) ∧ " +
					"bisimplicial_diagonal_degeneracy(X.sh, " +
					"    X.sv, " +
					"    n + 1, " +
					"    i, " +
					"    bisimplicial_diagonal_degeneracy(X.sh, X.sv, n, j, x)) = " +
					"X.sh(n + 1, n + 2, i, X.sh(n, n + 2, j, X.sv(n, n + 1, i, X.sv(n, n, j, x))))",
			}),
				func(
					a *Argument,
					_ *Expr[BisimplicialOps[A]],
					bisimplicial Fact,
					n, i, j *Expr[Nat],
					x *Expr[A],
					given Fact,
				) {
					column := a.Have(
						"the column n is a simplicial set",
						"simplicial_set(bisimplicial_column(X, n))",
						By(BisimplicialColumns.Read(bisimplicial).At(n)))
					next := a.TermAs[Nat]("n + 1")
					degeneracyJ := a.TermAs[A]("X.sv(n, n, j, x)")
					degeneracyIIn := a.Simplified(GroupPremises(
						given,
						simplicial_set.DegeneracyIn.Read(column).At(next, i, degeneracyJ)))
					commute := a.Simplified(GroupPremises(
						given,
						HorizontalDegeneracyVerticalDegeneracy.Read(bisimplicial).At(n, next, j, i, degeneracyJ)))
					a.Show(
						"the two vertical degeneracies stay in the column n, and "+
							"the vertical degeneracy i passes the horizontal degeneracy j",
						Simp(Fwd(BisimplicialDiagonalDegeneracyDef)),
						RingNf(),
						ByArith(given, degeneracyIIn, commute, simplicial_set.DegeneracyIn.Read(column).At(n, j, x)))
				})

			// A diagonal face of a diagonal degeneracy. The lemma also concludes
			// where the vertical composite lies, X(n + 1, n + 1), which the
			// identity in the row n + 1 reads in the middle leg of both cases
			// that cite it.
			faceOfDegeneracy := ctx.Lemma(BisimplicialSet.Statement(Statement{
				Binders: "∀n i j:num. ∀x:A.",
				Hypotheses: []string{
					"x ∈ X.simplices(n + 1, n + 1)",
					"i ≤ n + 2",
					"j ≤ n + 1",
				},
				Conclusion: "X.dv(n + 1, n + 2, i, X.sv(n + 1, n + 1, j, x)) ∈ X.simplices(n + 1, n + 1) ∧ " +
					"bisimplicial_diagonal_face(X.dh, " +
					"    X.dv, " +
					"    n + 2, " +
					"    i, " +
					"    bisimplicial_diagonal_degeneracy(X.sh, X.sv, n + 1, j, x)) = " +
					"X.dh(n + 2, n + 1, i, X.sh(n + 1, n + 1, j, X.dv(n + 1, n + 2, i, X.sv(n + 1, n + 1, j, x))))",
			}),
				func(
					a *Argument,
					_ *Expr[BisimplicialOps[A]],
					bisimplicial Fact,
					n, i, j *Expr[Nat],
					x *Expr[A],
					given Fact,
				) {
					next := a.TermAs[Nat]("n + 1")
					column := a.Have(
						"the column n + 1 is a simplicial set",
						"simplicial_set(bisimplicial_column(X, n + 1))",
						By(BisimplicialColumns.Read(bisimplicial).At(next)))
					degeneracyJ := a.TermAs[A]("X.sv(n + 1, n + 1, j, x)")
					degeneracyJIn := a.Simplified(
						GroupPremises(given, simplicial_set.DegeneracyIn.Read(column).At(next, j, x)))
					faceIIn := a.Simplified(GroupPremises(
						degeneracyJIn,
						simplicial_set.FaceIn.Read(column).At(next, i, degeneracyJ)))
					commute := a.Simplified(GroupPremises(
						degeneracyJIn,
						given,
						HorizontalDegeneracyVerticalFace.Read(bisimplicial).At(next, next, j, i, degeneracyJ)))
					a.Show(
						"the vertical face i of the vertical degeneracy j stays in "+
							"the column n + 1, and passes the horizontal degeneracy j",
						Simp(Fwd(BisimplicialDiagonalFaceDef), Fwd(BisimplicialDiagonalDegeneracyDef)),
						RingNf(),
						ByArith(given, degeneracyJIn, faceIIn, commute))
				})

			// A diagonal degeneracy of a diagonal face. Its cases read it only at
			// their last leg, so it concludes the interchange alone.
			degeneracyOfFace := ctx.Lemma(BisimplicialSet.Statement(Statement{
				Binders: "∀n i j:num. ∀x:A.",
				Hypotheses: []string{
					"x ∈ X.simplices(n + 1, n + 1)",
					"i ≤ n + 1",
					"j ≤ n",
				},
				Conclusion: "bisimplicial_diagonal_degeneracy(X.sh, " +
					"    X.sv, " +
					"    n, " +
					"    j, " +
					"    bisimplicial_diagonal_face(X.dh, X.dv, n + 1, i, x)) = " +
					"X.sh(n, n + 1, j, X.dh(n + 1, n + 1, i, X.sv(n + 1, n, j, X.dv(n + 1, n + 1, i, x))))",
			}),
				func(
					a *Argument,
					_ *Expr[BisimplicialOps[A]],
					bisimplicial Fact,
					n, i, j *Expr[Nat],
					x *Expr[A],
					given Fact,
				) {
					column := a.Have(
						"the column n + 1 is a simplicial set",
						"simplicial_set(bisimplicial_column(X, n + 1))",
						By(BisimplicialColumns.Read(bisimplicial).At(a.TermAs[Nat]("n + 1"))))
					a.Show(
						"the vertical face i of x lies in X(n + 1, n), where "+
							"the vertical degeneracy j passes the horizontal face i",
						Simp(Fwd(BisimplicialDiagonalFaceDef), Fwd(BisimplicialDiagonalDegeneracyDef)),
						ByArith(
							given,
							simplicial_set.FaceIn.Read(column).At(n, i, x),
							HorizontalFaceVerticalDegeneracy.Read(bisimplicial).At(
								n, n, i, j, a.TermAs[A]("X.dv(n + 1, n + 1, i, x)"))))
				})

			return ctx.Theorem(headline, func(a *Argument, _ *Expr[BisimplicialOps[A]], bisimplicial Fact) {
				a.Show(
					"the diagonal meets the eight axioms of a simplicial set",
					Simp(Fwd(simplicial_set.SimplicialSet), Fwd(BisimplicialDiagonalSimplicesDef)),
					SplitConjAll(
						Case(
							"a diagonal face is a vertical face, closed in the "+
								"column n + 1, then a horizontal face, closed in the row n",
							Derive(func(b *Argument) {
								n, i, x := b.FixAs[Nat]("n"), b.FixAs[Nat]("i"), b.FixAs[A]("x")
								given := b.Assume()
								column := b.Have(
									"the column n + 1 is a simplicial set",
									"simplicial_set(bisimplicial_column(X, n + 1))",
									By(BisimplicialColumns.Read(bisimplicial).At(b.TermAs[Nat]("n + 1"))))
								row := b.Have(
									"the row n is a simplicial set",
									"simplicial_set(bisimplicial_row(X, n))",
									By(BisimplicialRows.Read(bisimplicial).At(n)))
								b.Show(
									"the vertical face i of x lies in X(n + 1, n), and its horizontal face i in X(n, n)",
									Simp(Fwd(BisimplicialDiagonalFaceDef)),
									ByArith(
										given,
										simplicial_set.FaceIn.Read(column).At(n, i, x),
										simplicial_set.FaceIn.Read(row).At(n, i, b.TermAs[A]("X.dv(n + 1, n + 1, i, x)"))))
							})),
						Case(
							"a diagonal degeneracy is a vertical degeneracy, closed in "+
								"the column n, then a horizontal one, closed in the row n + 1",
							Derive(func(b *Argument) {
								n, i, x := b.FixAs[Nat]("n"), b.FixAs[Nat]("i"), b.FixAs[A]("x")
								given := b.Assume()
								column := b.Have(
									"the column n is a simplicial set",
									"simplicial_set(bisimplicial_column(X, n))",
									By(BisimplicialColumns.Read(bisimplicial).At(n)))
								row := b.Have(
									"the row n + 1 is a simplicial set",
									"simplicial_set(bisimplicial_row(X, n + 1))",
									By(BisimplicialRows.Read(bisimplicial).At(b.TermAs[Nat]("n + 1"))))
								b.Show(
									"the vertical degeneracy i of x lies in X(n, n + 1), "+
										"and its horizontal degeneracy i in X(n + 1, n + 1)",
									Simp(Fwd(BisimplicialDiagonalDegeneracyDef)),
									By(
										given,
										simplicial_set.DegeneracyIn.Read(column).At(n, i, x),
										simplicial_set.DegeneracyIn.Read(row).At(n, i, b.TermAs[A]("X.sv(n, n, i, x)"))))
							})),
						Case(
							"d_i d_j = d_{j−1} d_i: the face identity in the row n and in the column n + 2",
							Derive(func(b *Argument) {
								n, i, j, x := b.FixAs[Nat]("n"), b.FixAs[Nat]("i"), b.FixAs[Nat]("j"), b.FixAs[A]("x")
								given := b.Assume()
								column := b.Have(
									"the column n + 2 is a simplicial set",
									"simplicial_set(bisimplicial_column(X, n + 2))",
									By(BisimplicialColumns.Read(bisimplicial).At(b.TermAs[Nat]("n + 2"))))
								row := b.Have(
									"the row n is a simplicial set",
									"simplicial_set(bisimplicial_row(X, n))",
									By(BisimplicialRows.Read(bisimplicial).At(n)))
								facesIJ := Read(twoFaces, bisimplicial).At(n, i, j, x)
								b.Show(
									"both sides are two horizontal faces after two vertical ones",
									CalcEq(
										Leg(
											b.TermAs[A](
												"X.dh(n + 1, n, i, X.dh(n + 2, n, j, X.dv(n + 2, n + 1, i, X.dv(n + 2, n + 2, j, x))))"),
											"the faces i and j of the diagonal",
											ByArith(given, facesIJ)),
										Leg(
											b.TermAs[A](
												"X.dh(n + 1, n, j - 1, X.dh(n + 2, n, i, X.dv(n + 2, n + 1, i, X.dv(n + 2, n + 2, j, x))))"),
											"the face identity in the row n",
											ByArith(
												given,
												facesIJ,
												simplicial_set.FaceFace.Read(row).At(
													n,
													i,
													j,
													b.TermAs[A]("X.dv(n + 2, n + 1, i, X.dv(n + 2, n + 2, j, x))")))),
										Leg(
											b.TermAs[A](
												"X.dh(n + 1, n, j - 1, X.dh(n + 2, n, i, X.dv(n + 2, n + 1, j - 1, X.dv(n + 2, n + 2, i, x))))"),
											"the face identity in the column n + 2",
											By(given, simplicial_set.FaceFace.Read(column).At(n, i, j, x))),
										FinalLeg(
											"the faces j − 1 and i of the diagonal",
											ByArith(given, Read(twoFaces, bisimplicial).At(n, b.TermAs[Nat]("j - 1"), i, x)))))
							})),
						Case(
							"s_i s_j = s_{j+1} s_i: the degeneracy identity in the row n + 2 and in the column n",
							Derive(func(b *Argument) {
								n, i, j, x := b.FixAs[Nat]("n"), b.FixAs[Nat]("i"), b.FixAs[Nat]("j"), b.FixAs[A]("x")
								given := b.Assume()
								column := b.Have(
									"the column n is a simplicial set",
									"simplicial_set(bisimplicial_column(X, n))",
									By(BisimplicialColumns.Read(bisimplicial).At(n)))
								row := b.Have(
									"the row n + 2 is a simplicial set",
									"simplicial_set(bisimplicial_row(X, n + 2))",
									By(BisimplicialRows.Read(bisimplicial).At(b.TermAs[Nat]("n + 2"))))
								degeneraciesIJ := Read(twoDegeneracies, bisimplicial).At(n, i, j, x)
								b.Show(
									"both sides are two horizontal degeneracies after two vertical ones",
									CalcEq(
										Leg(
											b.TermAs[A]("X.sh(n + 1, n + 2, i, X.sh(n, n + 2, j, X.sv(n, n + 1, i, X.sv(n, n, j, x))))"),
											"the degeneracies i and j of the diagonal",
											ByArith(given, degeneraciesIJ)),
										Leg(
											b.TermAs[A]("X.sh(n + 1, n + 2, j + 1, X.sh(n, n + 2, i, X.sv(n, n + 1, i, X.sv(n, n, j, x))))"),
											"the degeneracy identity in the row n + 2",
											ByArith(
												given,
												degeneraciesIJ,
												simplicial_set.DegeneracyDegeneracy.Read(row).At(
													n,
													i,
													j,
													b.TermAs[A]("X.sv(n, n + 1, i, X.sv(n, n, j, x))")))),
										Leg(
											b.TermAs[A](
												"X.sh(n + 1, n + 2, j + 1, X.sh(n, n + 2, i, X.sv(n, n + 1, j + 1, X.sv(n, n, i, x))))"),
											"the degeneracy identity in the column n",
											By(given, simplicial_set.DegeneracyDegeneracy.Read(column).At(n, i, j, x))),
										FinalLeg(
											"the degeneracies j + 1 and i of the diagonal",
											ByArith(given, Read(twoDegeneracies, bisimplicial).At(n, b.TermAs[Nat]("j + 1"), i, x)))))
							})),
						Case(
							"d_i s_j = s_{j−1} d_i for i < j: the identity in the row n + 1 and in the column n + 1",
							Derive(func(b *Argument) {
								n, i, j, x := b.FixAs[Nat]("n"), b.FixAs[Nat]("i"), b.FixAs[Nat]("j"), b.FixAs[A]("x")
								given := b.Assume()
								column := b.Have(
									"the column n + 1 is a simplicial set",
									"simplicial_set(bisimplicial_column(X, n + 1))",
									By(BisimplicialColumns.Read(bisimplicial).At(b.TermAs[Nat]("n + 1"))))
								row := b.Have(
									"the row n + 1 is a simplicial set",
									"simplicial_set(bisimplicial_row(X, n + 1))",
									By(BisimplicialRows.Read(bisimplicial).At(b.TermAs[Nat]("n + 1"))))
								faceOfDegeneracyIJ := Read(faceOfDegeneracy, bisimplicial).At(n, i, j, x)
								b.Show(
									"both sides are a horizontal degeneracy and face after a vertical face and degeneracy",
									CalcEq(
										Leg(
											b.TermAs[A](
												"X.dh(n + 2, n + 1, i, X.sh(n + 1, n + 1, j, X.dv(n + 1, n + 2, i, X.sv(n + 1, n + 1, j, x))))"),
											"the face i of the degeneracy j of the diagonal",
											ByArith(given, faceOfDegeneracyIJ)),
										Leg(
											b.TermAs[A](
												"X.sh(n, n + 1, j - 1, X.dh(n + 1, n + 1, i, X.dv(n + 1, n + 2, i, X.sv(n + 1, n + 1, j, x))))"),
											"the identity in the row n + 1",
											ByArith(
												given,
												faceOfDegeneracyIJ,
												simplicial_set.FaceDegeneracyBelow.Read(row).At(
													n,
													i,
													j,
													b.TermAs[A]("X.dv(n + 1, n + 2, i, X.sv(n + 1, n + 1, j, x))")))),
										Leg(
											b.TermAs[A](
												"X.sh(n, n + 1, j - 1, X.dh(n + 1, n + 1, i, X.sv(n + 1, n, j - 1, X.dv(n + 1, n + 1, i, x))))"),
											"the identity in the column n + 1",
											By(given, simplicial_set.FaceDegeneracyBelow.Read(column).At(n, i, j, x))),
										FinalLeg(
											"the degeneracy j − 1 of the face i of the diagonal",
											ByArith(given, Read(degeneracyOfFace, bisimplicial).At(n, i, b.TermAs[Nat]("j - 1"), x)))))
							})),
						Case(
							"d_i s_i = id: the vertical face i passes the horizontal "+
								"degeneracy i, then the identity in the column n and in the row n",
							Derive(func(b *Argument) {
								n, i, x := b.FixAs[Nat]("n"), b.FixAs[Nat]("i"), b.FixAs[A]("x")
								given := b.Assume()
								column := b.Have(
									"the column n is a simplicial set",
									"simplicial_set(bisimplicial_column(X, n))",
									By(BisimplicialColumns.Read(bisimplicial).At(n)))
								row := b.Have(
									"the row n is a simplicial set",
									"simplicial_set(bisimplicial_row(X, n))",
									By(BisimplicialRows.Read(bisimplicial).At(n)))
								b.Show(
									"the face i of the degeneracy i of the diagonal is x",
									Simp(Fwd(BisimplicialDiagonalFaceDef), Fwd(BisimplicialDiagonalDegeneracyDef)),
									CalcEq(
										Leg(
											b.TermAs[A]("X.dh(n + 1, n, i, X.sh(n, n, i, X.dv(n, n + 1, i, X.sv(n, n, i, x))))"),
											"the vertical face i passes the horizontal degeneracy i",
											ByArith(
												given,
												simplicial_set.DegeneracyIn.Read(column).At(n, i, x),
												HorizontalDegeneracyVerticalFace.Read(bisimplicial).At(
													n, n, i, i, b.TermAs[A]("X.sv(n, n, i, x)")))),
										Leg(
											b.TermAs[A]("X.dh(n + 1, n, i, X.sh(n, n, i, x))"),
											"d_i s_i = id in the column n",
											By(Normalized, given, simplicial_set.FaceDegeneracyEqual.Read(column).At(n, i, x))),
										FinalLeg(
											"d_i s_i = id in the row n",
											By(given, simplicial_set.FaceDegeneracyEqual.Read(row).At(n, i, x)))))
							})),
						Case(
							"d_{i+1} s_i = id: the vertical face i + 1 passes the horizontal "+
								"degeneracy i, then the identity in the column n and in the row n",
							Derive(func(b *Argument) {
								n, i, x := b.FixAs[Nat]("n"), b.FixAs[Nat]("i"), b.FixAs[A]("x")
								given := b.Assume()
								column := b.Have(
									"the column n is a simplicial set",
									"simplicial_set(bisimplicial_column(X, n))",
									By(BisimplicialColumns.Read(bisimplicial).At(n)))
								row := b.Have(
									"the row n is a simplicial set",
									"simplicial_set(bisimplicial_row(X, n))",
									By(BisimplicialRows.Read(bisimplicial).At(n)))
								b.Show(
									"the face i + 1 of the degeneracy i of the diagonal is x",
									Simp(Fwd(BisimplicialDiagonalFaceDef), Fwd(BisimplicialDiagonalDegeneracyDef)),
									CalcEq(
										Leg(
											b.TermAs[A]("X.dh(n + 1, n, i + 1, X.sh(n, n, i, X.dv(n, n + 1, i + 1, X.sv(n, n, i, x))))"),
											"the vertical face i + 1 passes the horizontal degeneracy i",
											ByArith(
												given,
												simplicial_set.DegeneracyIn.Read(column).At(n, i, x),
												HorizontalDegeneracyVerticalFace.Read(bisimplicial).At(
													n,
													n,
													i,
													b.TermAs[Nat]("i + 1"),
													b.TermAs[A]("X.sv(n, n, i, x)")))),
										Leg(
											b.TermAs[A]("X.dh(n + 1, n, i + 1, X.sh(n, n, i, x))"),
											"d_{i+1} s_i = id in the column n",
											By(Normalized, given, simplicial_set.FaceDegeneracyNext.Read(column).At(n, i, x))),
										FinalLeg(
											"d_{i+1} s_i = id in the row n",
											By(given, simplicial_set.FaceDegeneracyNext.Read(row).At(n, i, x)))))
							})),
						Case(
							"d_i s_j = s_j d_{i−1} for i > j + 1: the identity in the row n + 1 and in the column n + 1",
							Derive(func(b *Argument) {
								n, i, j, x := b.FixAs[Nat]("n"), b.FixAs[Nat]("i"), b.FixAs[Nat]("j"), b.FixAs[A]("x")
								given := b.Assume()
								column := b.Have(
									"the column n + 1 is a simplicial set",
									"simplicial_set(bisimplicial_column(X, n + 1))",
									By(BisimplicialColumns.Read(bisimplicial).At(b.TermAs[Nat]("n + 1"))))
								row := b.Have(
									"the row n + 1 is a simplicial set",
									"simplicial_set(bisimplicial_row(X, n + 1))",
									By(BisimplicialRows.Read(bisimplicial).At(b.TermAs[Nat]("n + 1"))))
								faceOfDegeneracyIJ := Read(faceOfDegeneracy, bisimplicial).At(n, i, j, x)
								b.Show(
									"both sides are a horizontal degeneracy and face after a vertical face and degeneracy",
									CalcEq(
										Leg(
											b.TermAs[A](
												"X.dh(n + 2, n + 1, i, X.sh(n + 1, n + 1, j, X.dv(n + 1, n + 2, i, X.sv(n + 1, n + 1, j, x))))"),
											"the face i of the degeneracy j of the diagonal",
											ByArith(given, faceOfDegeneracyIJ)),
										Leg(
											b.TermAs[A](
												"X.sh(n, n + 1, j, X.dh(n + 1, n + 1, i - 1, X.dv(n + 1, n + 2, i, X.sv(n + 1, n + 1, j, x))))"),
											"the identity in the row n + 1",
											ByArith(
												given,
												faceOfDegeneracyIJ,
												simplicial_set.FaceDegeneracyAbove.Read(row).At(
													n,
													i,
													j,
													b.TermAs[A]("X.dv(n + 1, n + 2, i, X.sv(n + 1, n + 1, j, x))")))),
										Leg(
											b.TermAs[A](
												"X.sh(n, n + 1, j, X.dh(n + 1, n + 1, i - 1, X.sv(n + 1, n, j, X.dv(n + 1, n + 1, i - 1, x))))"),
											"the identity in the column n + 1",
											By(given, simplicial_set.FaceDegeneracyAbove.Read(column).At(n, i, j, x))),
										FinalLeg(
											"the degeneracy j of the face i − 1 of the diagonal",
											ByArith(given, Read(degeneracyOfFace, bisimplicial).At(n, b.TermAs[Nat]("i - 1"), j, x)))))
							})),
					))
			})
		}),
})}

// DiagonalMap — a map of bisimplicial sets restricts to a simplicial map
// of the diagonals.
var DiagonalMap = diagonalMapThm{family.Add(registry.ProofEntry{
	Name: "DiagonalMap",
	Key:  "prop_bfd72fbd1044fb30",
	Deps: []registry.EntryLike{
		BisimplicialMap,
		DiagonalSimplicialSet,
		BisimplicialDiagonalSimplicesDef,
		BisimplicialDiagonalFaceDef,
		BisimplicialDiagonalDegeneracyDef,
		simplicial_set.SimplicialMap,
	},
	Build: family.Card(
		BisimplicialMap.Statement(
			"simplicial_map(bisimplicial_diagonal(X), bisimplicial_diagonal(Y), λn:num. F(n, n))"),
		"both diagonals are simplicial sets (DiagonalSimplicialSet); F(n, "+
			"n) carries X(n, n) into Y(n, n), and commutes with a vertical face "+
			"and then with a horizontal one, likewise with the degeneracies"),
})}

// DiagonalHomotopy — a vertical homotopy natural in the horizontal
// direction gives a simplicial homotopy of the diagonals, with
// components h_j = sh'_j ∘ H(n, n, j).
var DiagonalHomotopy = diagonalHomotopyThm{family.Add(registry.ProofEntry{
	Name: "DiagonalHomotopy",
	Key:  "prop_5f3c51e6d67fa1cd",
	Reading: "Each of May's identities on the diagonal reads, in turn, " +
		"a mixed commutation of Y moving dv'_i or sv'_i past sh'_j, a " +
		"column identity of H, a row identity of Y, and the naturality of H.",
	Deps: []registry.EntryLike{
		BisimplicialVerticalHomotopy,
		SimplicialHomotopy,
		DiagonalMap,
		BisimplicialDiagonalSimplicesDef,
		BisimplicialDiagonalFaceDef,
		BisimplicialDiagonalDegeneracyDef,
		BisimplicialSet,
		HorizontalDegeneracyVerticalFace,
		HorizontalDegeneracyVerticalDegeneracy,
		BisimplicialRows,
		BisimplicialColumns,
	},
	Build: family.Card(
		BisimplicialVerticalHomotopy.Statement(
			"simplicial_homotopy(bisimplicial_diagonal(X), "+
				"    bisimplicial_diagonal(Y), "+
				"    λn:num. F(n, n), "+
				"    λn:num. G(n, n), "+
				"    λn:num. λj:num. λx:A. Y.sh(n, n + 1, j, H(n, n, j, x)))"),
		"each of May's identities for h_j = sh'_j H_j on the diagonal is a column identity of the "+
			"vertical homotopy times a row identity of Y: a diagonal face dh'_i dv'_i meets sh'_j "+
			"H_j, dv'_i commutes past sh'_j, the column identity moves it past H_j, the row identity "+
			"moves dh'_i past sh'_j, and naturality moves it past H; the ends are d_0 h_0 = dv'_0 H_0 "+
			"= F and d_{n+1} h_n = dv'_{n+1} H_n = G. The ends are simplicial maps by DiagonalMap"),
})}

// DiagonalHomotopyEquivalence — bisimplicial maps F and G whose composites
// are joined to the identities by vertical homotopies natural in the
// horizontal direction give a simplicial homotopy equivalence of the
// diagonals.
var DiagonalHomotopyEquivalence = diagonalHomotopyEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "DiagonalHomotopyEquivalence",
	Key:  "prop_fa63981250cee2b4",
	Reading: "The vertical homotopies run from the identities to the composites; a " +
		"consumer holding one the other way round reaches the same conclusion through " +
		"DiagonalHomotopy, since the zigzag of the conclusion takes a step in either direction.",
	Deps: []registry.EntryLike{
		DiagonalMap,
		DiagonalHomotopy,
		SimplicialHomotopyEquivalenceDef,
		SimplicialMapsHomotopicDef,
	},
	Build: family.Card(Statement{
		Binders: "∀X:bisimplicial_ops(A). " +
			"∀Y:bisimplicial_ops(B). " +
			"∀F:(num → num → A → B). " +
			"∀G:(num → num → B → A). " +
			"∀H:(num → num → num → A → A). " +
			"∀K:(num → num → num → B → B).",
		Hypotheses: []string{
			"bisimplicial_map(X, Y, F)",
			"bisimplicial_map(Y, X, G)",
			"bisimplicial_vertical_homotopy(X, " +
				"    X, " +
				"    λp:num. λq:num. λx:A. x, " +
				"    λp:num. λq:num. λx:A. G(p, q, F(p, q, x)), " +
				"    H)",
			"bisimplicial_vertical_homotopy(Y, " +
				"    Y, " +
				"    λp:num. λq:num. λy:B. y, " +
				"    λp:num. λq:num. λy:B. F(p, q, G(p, q, y)), " +
				"    K)",
		},
		Conclusion: "simplicial_homotopy_equivalence(bisimplicial_diagonal(X), " +
			"    bisimplicial_diagonal(Y), " +
			"    λn:num. F(n, n))",
	},
		"DiagonalMap gives the diagonal maps of F and G, and DiagonalHomotopy "+
			"turns H and K into simplicial homotopies of the diagonals from the "+
			"identities to the composites, each a zigzag of one step"),
})}
