// mapping_complex.go — the left mapping complex of a simplicial set,
// with its simplicial and Kan structures and its edge interpretation.

package mapping_complex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/quasi_category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// mappingComplexSimplicesDef — `mapping_complex_simplices(X, x, y)`: the (n +
// 1)-simplices with vertex 0 at x and the face opposite it degenerate
// at y.
var mappingComplexSimplicesDef = mappingComplexSimplicesDefThm{family.Define(registry.DefEntry{
	Name:  "mappingComplexSimplicesDef",
	Key:   "prop_c940fc111261271a",
	Const: "mapping_complex_simplices",
	Type:  "simplicial_ops(A) → A → A → num → set(A)",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀x y:A. " +
			"    mapping_complex_simplices(X, x, y) = " +
			"    λn:num. " +
			"        {σ:A | " +
			"            σ ∈ X.simplices(n + 1) ∧ " +
			"            face_iterate_top(X.d, n + 1, n + 1, σ) = x ∧ " +
			"            X.d(n + 1, 0, σ) = base_simplex(X.s, y, n)}",
	},
	Reading: "Lurie's left mapping space Hom^L(x, y). An edge of it, a 2-simplex σ, runs from " +
		"its face 2 to its face 1 with face 0 degenerate at y: the homotopy edge_homotopic states.",
})}

// mappingComplexFaceDef — `mapping_complex_face(d)`: the faces of X past
// vertex 0.
var mappingComplexFaceDef = mappingComplexFaceDefThm{family.Define(registry.DefEntry{
	Name:  "mappingComplexFaceDef",
	Key:   "prop_79f212cb2c4852e8",
	Const: "mapping_complex_face",
	Type:  "(num → num → A → A) → num → num → A → A",
	Equations: []string{
		"∀d:(num → num → A → A). mapping_complex_face(d) = λn:num. λi:num. λσ:A. d(n + 1, i + 1, σ)",
	},
})}

// mappingComplexDegeneracyDef — `mapping_complex_degeneracy(s)`: the
// degeneracies of X past vertex 0.
var mappingComplexDegeneracyDef = mappingComplexDegeneracyDefThm{family.Define(registry.DefEntry{
	Name:  "mappingComplexDegeneracyDef",
	Key:   "prop_3c33481e21dcf3d9",
	Const: "mapping_complex_degeneracy",
	Type:  "(num → num → A → A) → num → num → A → A",
	Equations: []string{
		"∀s:(num → num → A → A). mapping_complex_degeneracy(s) = λn:num. λi:num. λσ:A. s(n + 1, i + 1, σ)",
	},
})}

// MappingComplexSimplicialSet — the mapping complex from x to a vertex y
// is a simplicial set: shifted operators preserve its first vertex and
// its opposite degenerate face, and inherit the identities of X.
var MappingComplexSimplicialSet = mappingComplexSimplicialSetThm{family.Add(registry.ProofEntry{
	Name: "MappingComplexSimplicialSet",
	Key:  "prop_62a4c4745ee2b89e",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"y ∈ X.simplices(0)",
		},
		Conclusion: "simplicial_set(mapping_complex(X, x, y))",
	},
		func(a *Argument, simplicial Fact, x, y *Expr[A], yIn Fact) {
			a.Show(
				"the shifted operators satisfy the eight simplicial-set axioms",
				Simp(Fwd(simplicial_set.SimplicialSet)),
				SplitConjAll(
					Case(
						"a shifted face preserves the first vertex and the opposite degenerate face",
						Derive(func(b *Argument) {
							n, i := b.FixAs[Nat]("n"), b.FixAs[Nat]("i")
							σ := b.FixAs[A]("σ")
							given := b.Assume()
							data := b.Have(
								"read the ambient simplex, its first vertex and its opposite face",
								"σ ∈ X.simplices(n + 1 + 1) ∧ "+
									"face_iterate_top(n + 1 + 1, n + 1 + 1, σ) = x ∧ "+
									"X.d(n + 1 + 1, 0, σ) = base_simplex(y, n + 1)",
								BySets(b.Unfolded(given, mappingComplexSimplicesDef)))
							parts := b.Conjuncts(
								data,
								"σ has the ambient dimension",
								"its first vertex is x",
								"its opposite face is degenerate at y")
							membership, first, opposite := parts[0], parts[1], parts[2]
							degree, shifted := b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("i + 1")
							inAmbient := b.Have(
								"the shifted face has the required ambient dimension",
								"X.d(n + 1 + 1, i + 1, σ) ∈ X.simplices(n + 1)",
								ByArith(simplicial_set.FaceIn.Read(simplicial).At(degree, shifted, σ), membership, given))
							retains := b.Have(
								"the shifted face retains the first vertex",
								"face_iterate_top(n + 1, n + 1, X.d(n + 1 + 1, i + 1, σ)) = x",
								CalcEq(
									Leg(
										b.TermAs[A]("face_iterate_top(n + 1 + 1, n + 1 + 1, σ)"),
										"absorb the shifted face into the removal of the top vertices",
										ByArith(
											simplicial_set.FaceIterateTopAbove.Read(simplicial).At(degree, degree, shifted, σ),
											membership,
											given)),
									FinalLeg(
										"the remaining vertex is x",
										By(first)),
								))
							dimension := b.Have(
								"write the ambient input dimension as n + 2",
								"n + 1 + 1 = n + 2",
								ByArith())
							b.Do(Simp(Fwd(mappingComplexFaceDef)), dimension.Rw())
							based := b.Have(
								"the opposite face remains degenerate at y",
								"X.d(n + 1, 0, X.d(n + 2, i + 1, σ)) = base_simplex(y, n)",
								CalcEq(
									Leg(
										b.TermAs[A]("X.d(n + 1, i, X.d(n + 2, 0, σ))"),
										"the face identity moves the opposite face past the shifted face",
										ByArith(
											simplicial_set.FaceFace.Read(simplicial).At(n, b.TermAs[Nat]("0"), shifted, σ),
											membership,
											given)),
									Leg(
										b.TermAs[A]("X.d(n + 1, i, base_simplex(y, n + 1))"),
										"the input opposite face is degenerate at y",
										By(opposite)),
									FinalLeg(
										"a face of the base simplex is the lower base simplex",
										ByArith(simplicial_set.BaseSimplexFace.Read(simplicial).At(y, n, i), yIn, given)),
								))
							b.Show(
								"the shifted face satisfies the three carrier conditions",
								Unfold(mappingComplexSimplicesDef),
								BySets(inAmbient, retains, based))
						})),
					Case(
						"a shifted degeneracy preserves the first vertex and the opposite degenerate face",
						Derive(func(b *Argument) {
							n, i := b.FixAs[Nat]("n"), b.FixAs[Nat]("i")
							σ := b.FixAs[A]("σ")
							given := b.Assume()
							data := b.Have(
								"read the ambient simplex, its first vertex and its opposite face",
								"σ ∈ X.simplices(n + 1) ∧ "+
									"face_iterate_top(n + 1, n + 1, σ) = x ∧ "+
									"X.d(n + 1, 0, σ) = base_simplex(y, n)",
								BySets(b.Unfolded(given, mappingComplexSimplicesDef)))
							parts := b.Conjuncts(
								data,
								"σ has the ambient dimension",
								"its first vertex is x",
								"its opposite face is degenerate at y")
							membership, first, opposite := parts[0], parts[1], parts[2]
							degree, shifted := b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("i + 1")
							inAmbient := b.Have(
								"the shifted degeneracy has the required ambient dimension",
								"X.s(n + 1, i + 1, σ) ∈ X.simplices(n + 1 + 1)",
								ByArith(simplicial_set.DegeneracyIn.Read(simplicial).At(degree, shifted, σ), membership, given))
							retains := b.Have(
								"the shifted degeneracy retains the first vertex",
								"face_iterate_top(n + 1 + 1, n + 1 + 1, X.s(n + 1, i + 1, σ)) = x",
								CalcEq(
									Leg(
										b.TermAs[A]("face_iterate_top(n + 1, n + 1, σ)"),
										"the top iteration absorbs the repeated vertex",
										ByArith(
											simplicial_set.FaceIterateTopDegeneracyAbove.Read(simplicial).At(degree, degree, shifted, σ),
											membership,
											given)),
									FinalLeg(
										"the remaining vertex is x",
										By(first)),
								))
							dimension := b.Have(
								"write the ambient output dimension as n + 2",
								"n + 1 + 1 = n + 2",
								ByArith())
							b.Do(Simp(Fwd(mappingComplexDegeneracyDef)), dimension.Rw())
							based := b.Have(
								"the opposite face remains degenerate at y",
								"X.d(n + 2, 0, X.s(n + 1, i + 1, σ)) = base_simplex(y, n + 1)",
								CalcEq(
									Leg(
										b.TermAs[A]("X.s(n, i, X.d(n + 1, 0, σ))"),
										"the mixed identity moves the opposite face past the shifted degeneracy",
										ByArith(
											simplicial_set.FaceDegeneracyBelow.Read(simplicial).At(n, b.TermAs[Nat]("0"), shifted, σ),
											membership,
											given)),
									Leg(
										b.TermAs[A]("X.s(n, i, base_simplex(y, n))"),
										"the input opposite face is degenerate at y",
										By(Normalized, opposite)),
									FinalLeg(
										"a degeneracy of the base simplex is the upper base simplex",
										ByArith(simplicial_set.BaseSimplexDegeneracy.Read(simplicial).At(y, n, i), yIn, given)),
								))
							b.Show(
								"the shifted degeneracy satisfies the three carrier conditions",
								Unfold(mappingComplexSimplicesDef),
								dimension.Rw(),
								BySets(inAmbient, retains, based))
						})),
					Case(
						"two shifted faces satisfy the face identity",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							σ := b.FixAs[A]("σ")
							given := b.Assume()
							membership := b.Have(
								"σ has the ambient input dimension",
								"σ ∈ X.simplices(n + 2 + 1)",
								BySets(b.Unfolded(given, mappingComplexSimplicesDef)))
							b.Do(Simp(Fwd(mappingComplexFaceDef)))
							dimension := b.Have(
								"align the third ambient degree",
								"n + 2 + 1 = n + 1 + 2",
								ByArith())
							index := b.Have(
								"shifting the predecessor of j returns j",
								"j - 1 + 1 = j",
								ByArith(given))
							b.Show(
								"the ambient face identity applies at the shifted indices",
								dimension.Rw(),
								index.Rw(),
								ByArith(
									simplicial_set.FaceFace.Read(simplicial).At(
										b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("i + 1"), b.TermAs[Nat]("j + 1"), σ),
									membership,
									given))
						})),
					Case(
						"two shifted degeneracies satisfy the degeneracy identity",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							σ := b.FixAs[A]("σ")
							given := b.Assume()
							membership := b.Have(
								"σ has the ambient input dimension",
								"σ ∈ X.simplices(n + 1)",
								BySets(b.Unfolded(given, mappingComplexSimplicesDef)))
							b.Show(
								"the ambient degeneracy identity applies at the shifted indices",
								Simp(Fwd(mappingComplexDegeneracyDef)),
								ByArith(
									simplicial_set.DegeneracyDegeneracy.Read(simplicial).At(
										b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("i + 1"), b.TermAs[Nat]("j + 1"), σ),
									membership,
									given))
						})),
					Case(
						"a lower shifted face passes a shifted degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							σ := b.FixAs[A]("σ")
							given := b.Assume()
							membership := b.Have(
								"σ has the ambient input dimension",
								"σ ∈ X.simplices(n + 1 + 1)",
								BySets(b.Unfolded(given, mappingComplexSimplicesDef)))
							b.Do(Simp(Fwd(mappingComplexFaceDef), Fwd(mappingComplexDegeneracyDef)))
							dimension := b.Have(
								"align the third ambient degree",
								"n + 2 + 1 = n + 1 + 2",
								ByArith())
							index := b.Have(
								"shifting the predecessor of j returns j",
								"j - 1 + 1 = j",
								ByArith(given))
							b.Show(
								"the ambient lower mixed identity applies at the shifted indices",
								dimension.Rw(),
								index.Rw(),
								ByArith(
									simplicial_set.FaceDegeneracyBelow.Read(simplicial).At(
										b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("i + 1"), b.TermAs[Nat]("j + 1"), σ),
									membership,
									given))
						})),
					Case(
						"the repeated shifted face cancels its degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							σ := b.FixAs[A]("σ")
							given := b.Assume()
							membership := b.Have(
								"σ has the ambient input dimension",
								"σ ∈ X.simplices(n + 1)",
								BySets(b.Unfolded(given, mappingComplexSimplicesDef)))
							b.Show(
								"the ambient cancellation identity applies at the shifted index",
								Simp(Fwd(mappingComplexFaceDef), Fwd(mappingComplexDegeneracyDef)),
								ByArith(
									simplicial_set.FaceDegeneracyEqual.Read(simplicial).At(
										b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("i + 1"), σ),
									membership,
									given))
						})),
					Case(
						"the next shifted face cancels its degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							σ := b.FixAs[A]("σ")
							given := b.Assume()
							membership := b.Have(
								"σ has the ambient input dimension",
								"σ ∈ X.simplices(n + 1)",
								BySets(b.Unfolded(given, mappingComplexSimplicesDef)))
							b.Show(
								"the ambient next-face cancellation applies at the shifted index",
								Simp(Fwd(mappingComplexFaceDef), Fwd(mappingComplexDegeneracyDef)),
								ByArith(
									simplicial_set.FaceDegeneracyNext.Read(simplicial).At(
										b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("i + 1"), σ),
									membership,
									given))
						})),
					Case(
						"an upper shifted face passes a shifted degeneracy",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							b.FixAs[Nat]("i")
							b.FixAs[Nat]("j")
							σ := b.FixAs[A]("σ")
							given := b.Assume()
							membership := b.Have(
								"σ has the ambient input dimension",
								"σ ∈ X.simplices(n + 1 + 1)",
								BySets(b.Unfolded(given, mappingComplexSimplicesDef)))
							b.Do(Simp(Fwd(mappingComplexFaceDef), Fwd(mappingComplexDegeneracyDef)))
							dimension := b.Have(
								"align the third ambient degree",
								"n + 2 + 1 = n + 1 + 2",
								ByArith())
							index := b.Have(
								"shifting the predecessor of i returns i",
								"i - 1 + 1 = i",
								ByArith(given))
							b.Show(
								"the ambient upper mixed identity applies at the shifted indices",
								dimension.Rw(),
								index.Rw(),
								ByArith(
									simplicial_set.FaceDegeneracyAbove.Read(simplicial).At(
										b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("i + 1"), b.TermAs[Nat]("j + 1"), σ),
									membership,
									given))
						})),
				))
		}),
	Reading: "Only y is asked to be a vertex: the faces of the " +
		"degenerate simplex at y are read through the simplicial identities, " +
		"which ask that. When x is not a vertex the mapping complex is empty.",
})}

// MappingComplexVertices — the vertices of the mapping complex are the
// edges from x to y.
var MappingComplexVertices = mappingComplexVerticesThm{family.Add(registry.ProofEntry{
	Name: "MappingComplexVertices",
	Key:  "prop_434c7dd241a8880a",
	Deps: []registry.EntryLike{
		mappingComplexSimplicesDef,
		simplicial_set.FaceIterateTopDef,
		simplicial_set.BaseSimplexDef,
	},
	Build: family.Card(
		simplicial_set.SimplicialSet.Statement(
			"∀x y f:A. "+
				"    f ∈ mapping_complex_simplices(X, x, y, 0) ⇔ "+
				"    f ∈ X.simplices(1) ∧ X.d(1, 1, f) = x ∧ X.d(1, 0, f) = y"),
		"at n = 0 vertex 0 of an edge is its face 1 and the degenerate 0-simplex at y is y"),
})}

// MappingComplexEdges — an edge of the mapping complex from f to g is a
// homotopy from f to g.
var MappingComplexEdges = mappingComplexEdgesThm{family.Add(registry.ProofEntry{
	Name: "MappingComplexEdges",
	Key:  "prop_ad9aeef25fd4b772",
	Deps: []registry.EntryLike{
		mappingComplexSimplicesDef,
		mappingComplexFaceDef,
		quasi_category.EdgeHomotopicDef,
		quasi_category.EdgeHomotopicEnds,
		simplicial_set.FaceFace,
		simplicial_set.VertexDegeneracyFaces,
	},
	Build: family.Card(simplicial_set.SimplicialSet.Statement(Statement{
		Binders: "∀x y f g:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(0)",
			"y ∈ X.simplices(0)",
		},
		Conclusion: "(∃σ:A. " +
			"    σ ∈ mapping_complex_simplices(X, x, y, 1) ∧ " +
			"    mapping_complex_face(X.d, 1, 1, σ) = f ∧ " +
			"    mapping_complex_face(X.d, 1, 0, σ) = g) ⇔ " +
			"edge_homotopic(X, f, g) ∧ X.d(1, 1, f) = x ∧ X.d(1, 0, f) = y",
	}),
		"σ is a 2-simplex with face 2 = f, face 1 = g and face 0 degenerate at y, "+
			"vertex 0 being x: exactly a homotopy from f to g, whose ends are those "+
			"of f (EdgeHomotopicEnds); the face identities read the ends of f off σ"),
})}

// MappingComplexKan — the left mapping complex in a quasi-category is
// Kan. Adjoining the base simplex at y turns a mapping horn into an
// ambient horn. The last-face case has a degenerate last edge, with
// degenerate inverse triangles, so the special outer-horn theorem applies.
var MappingComplexKan = mappingComplexKanThm{family.Add(registry.ProofEntry{
	Name: "MappingComplexKan",
	Key:  "prop_d6366da638d7bf73",
	Build: family.Sections(quasi_category.QuasiCategory.Statement(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"y ∈ X.simplices(0)",
		},
		Conclusion: "kan_complex(mapping_complex(X, x, y))",
	}),
		func(ctx *Script, headline string) *GoalStackNode {
			bottomBase := ctx.Lemma(simplicial_set.SimplicialSet.Statement(Statement{
				Binders: "∀k n:num. ∀y:A.",
				Hypotheses: []string{
					"y ∈ X.simplices(0)",
					"k ≤ n",
				},
				Conclusion: "face_iterate_bottom(n, k, base_simplex(y, n)) = base_simplex(y, n - k)",
			}),
				func(a *Argument, X *Expr[simplicial_set.SimplicialOps[A]], simplicial Fact) {
					a.Induct("k")
					a.Base(
						"removing no bottom vertices leaves the base simplex",
						Simp(Fwd(simplicial_set.FaceIterateBottomDef)),
						ByArith())
					a.Step(
						"one further bottom face lowers the remaining base simplex",
						func(b *Argument, ih Fact) {
							n, y := b.FixAs[Nat]("n"), b.FixAs[A]("y")
							given := b.Assume()
							previous := b.Have(
								"the first k removals leave the base simplex of degree n − k",
								"face_iterate_bottom(n, k, base_simplex(y, n)) = base_simplex(y, n - k)",
								ByArith(ih.At(n, y), given))
							degree := b.Have(
								"the remaining degree is a successor",
								"n - k = n - suc(k) + 1",
								ByArith(given))
							b.Show(
								"the next face is a face of that base simplex",
								Simp(Fwd(simplicial_set.FaceIterateBottomDef)),
								previous.Rw(),
								degree.Rw(),
								ByArith(
									simplicial_set.BaseSimplexFace.Read(simplicial).At(
										y, b.TermAs[Nat]("n - suc(k)"), b.TermAs[Nat]("0")),
									given))
						})
				})

			degenerateEquivalence := ctx.Lemma(quasi_category.QuasiCategory.Statement(Statement{
				Binders: "∀y:A.",
				Hypotheses: []string{
					"y ∈ X.simplices(0)",
				},
				Conclusion: "edge_equivalence(X, X.s(0, 0, y))",
			}),
				func(a *Argument, X *Expr[simplicial_set.SimplicialOps[A]], quasi Fact, y *Expr[A], vertex Fact) {
					simplicial := a.Have(
						"the ambient quasi-category is simplicial",
						"simplicial_set(X)",
						By(quasi_category.QuasiSimplicialSet.Read(quasi)))
					e := a.TermAs[A]("X.s(0, 0, y)")
					t := a.TermAs[A]("X.s(1, 0, X.s(0, 0, y))")
					ends := a.Have(
						"the degenerate edge has both ends at y",
						"X.s(0, 0, y) ∈ X.simplices(1) ∧ X.d(1, 0, X.s(0, 0, y)) = y ∧ X.d(1, 1, X.s(0, 0, y)) = y",
						By(simplicial_set.VertexDegeneracyFaces.Read(simplicial).At(y), vertex))
					triangle := a.Have(
						"its first degeneracy supplies both inverse triangles",
						"X.s(1, 0, X.s(0, 0, y)) ∈ X.simplices(2) ∧ "+
							"X.d(2, 0, X.s(1, 0, X.s(0, 0, y))) = X.s(0, 0, y) ∧ "+
							"X.d(2, 1, X.s(1, 0, X.s(0, 0, y))) = X.s(0, 0, y) ∧ "+
							"X.d(2, 2, X.s(1, 0, X.s(0, 0, y))) = X.s(0, 0, X.d(1, 1, X.s(0, 0, y)))",
						By(simplicial_set.EdgeFirstDegeneracyFaces.Read(simplicial).At(e), ends))
					a.Show(
						"the degenerate edge is its own inverse",
						Simp(Fwd(quasi_category.EdgeEquivalenceIffInverseTriangles.Read(quasi))),
						SplitConj(
							Case(
								"the degenerate edge belongs to X",
								By(ends)),
							Case(
								"the same degenerate triangle gives both inverses",
								Derive(func(b *Argument) {
									b.Take(e)
									b.Take(t)
									b.Take(t)
									b.Show(
										"the face and endpoint equations give the two inverse triangles",
										By(ends, triangle))
								})),
						))
				})

			ambientFill := ctx.Lemma(quasi_category.QuasiCategory.Statement(
				Statement{
					Binders: "∀x y:A. ∀n k:num. ∀h:(num → A).",
					Hypotheses: []string{
						"y ∈ X.simplices(0)",
						"k ≤ n + 1",
						"face_family(mapping_complex(X, x, y), n, horn_faces(n, k), h)",
					},
					Conclusion: "∃σ:A. " +
						"    σ ∈ mapping_complex_simplices(X, x, y, n + 1) ∧ " +
						"    faces_filler(mapping_complex_face(X.d), n, horn_faces(n, k), h, σ)",
				}),
				func(
					a *Argument,
					X *Expr[simplicial_set.SimplicialOps[A]],
					quasi Fact,
					x *Expr[A],
					y *Expr[A],
					n *Expr[Nat],
					k *Expr[Nat],
					h *Arrow[Nat, A],
					given Fact,
				) {
					parts := a.Conjuncts(
						given,
						"y is a vertex",
						"the missing face is in range",
						"h is a mapping horn")
					vertex, bounded := parts[0], parts[1]
					horn := a.Conjuncts(
						a.Unfolded(parts[2], simplicial_set.FaceFamilyDef),
						"the faces belong to the mapping complex",
						"the mapping faces are compatible")
					members := horn[0]
					compatible := a.Unfolded(
						a.Unfolded(horn[1], simplicial_set.FacesCompatibleDef), mappingComplexFaceDef)
					simplicial := a.Have(
						"the ambient quasi-category is simplicial",
						"simplicial_set(X)",
						By(quasi_category.QuasiSimplicialSet.Read(quasi)))
					H, definition := a.LetAs[Fun[Nat, A]]("H", "λj:num. COND(j = 0, base_simplex(y, n + 1), h(j - 1))")
					zero := a.Have(
						"the added face is the base simplex at y",
						"H(0) = base_simplex(y, n + 1)",
						By(definition))
					successor := a.Have(
						"the positive faces are those of the mapping horn",
						"∀j:num. H(j + 1) = h(j)",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("j")
							b.Show(
								"the positive branch selects the original face",
								definition.Rw(),
								ByArith())
						}))
					positive := a.Have(
						"a positive ambient index selects its predecessor",
						"∀i:num. 0 < i ⇒ H(i) = h(i - 1)",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("i")
							above := b.Assume()
							b.Show(
								"the positive branch of H applies",
								definition.Rw(),
								ByArith(above))
						}))
					data := a.Have(
						"each mapping face has its ambient dimension and prescribed ends",
						Statement{
							Binders: "∀j:num.",
							Hypotheses: []string{
								"j ∈ horn_faces(n, k)",
							},
							Conclusion: "h(j) ∈ X.simplices(n + 1) ∧ " +
								"face_iterate_top(n + 1, n + 1, h(j)) = x ∧ " +
								"X.d(n + 1, 0, h(j)) = base_simplex(y, n)",
						},
						Derive(func(b *Argument) {
							j := b.FixAs[Nat]("j")
							live := b.Assume()
							inMapping := b.Have(
								"the j-th face is a mapping simplex",
								"h(j) ∈ mapping_complex_simplices(X, x, y, n)",
								By(members.At(j), live))
							b.Show(
								"read its three carrier conditions",
								BySets(b.Unfolded(inMapping, mappingComplexSimplicesDef)))
						}))

					ambient := a.Have(
						"adjoining the base simplex gives an ambient horn",
						"face_family(X, n + 1, horn_faces(n + 1, k + 1), H)",
						Unfold(simplicial_set.FaceFamilyDef),
						SplitConj(
							Case(
								"each ambient horn face has dimension n + 1",
								Derive(func(b *Argument) {
									i := b.FixAs[Nat]("i")
									live := b.Assume()
									b.Cases(b.Term("i = 0"))
									b.When(
										"the added face is the base simplex",
										func(c *Argument, atZero Fact) {
											c.Show(
												"the base simplex has the required dimension",
												atZero.Rw(),
												zero.Rw(),
												By(simplicial_set.BaseSimplexIn.Read(simplicial), vertex))
										})
									b.Otherwise(
										"a positive face is an original mapping face",
										func(c *Argument, nonzero Fact) {
											predecessor := c.TermAs[Nat]("i - 1")
											oldLive := c.Have(
												"its predecessor is a live mapping-horn index",
												"i - 1 ∈ horn_faces(n, k)",
												ByArith(
													nonzero,
													live,
													kan_complex.HornFacesMember.At(c.TermAs[Nat]("n + 1"), c.TermAs[Nat]("k + 1"), i),
													kan_complex.HornFacesMember.At(n, k, predecessor)))
											value := c.Have(
												"H selects that original face",
												"H(i) = h(i - 1)",
												ByArith(positive.At(i), nonzero))
											c.Show(
												"the original face has the required ambient dimension",
												By(data.At(predecessor), oldLive, value))
										})
								})),
							Case(
								"the added face is compatible with all original faces",
								Unfold(simplicial_set.FacesCompatibleDef),
								Derive(func(b *Argument) {
									i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
									live := b.Assume()
									jOld := b.TermAs[Nat]("j - 1")
									jInfo := b.Have(
										"j is positive and has a live predecessor",
										"0 < j ∧ j - 1 ∈ horn_faces(n, k)",
										ByArith(
											live,
											kan_complex.HornFacesMember.At(b.TermAs[Nat]("n + 1"), b.TermAs[Nat]("k + 1"), j),
											kan_complex.HornFacesMember.At(n, k, jOld)))
									jValue := b.Have(
										"H at j is its original face",
										"H(j) = h(j - 1)",
										ByArith(positive.At(j), jInfo))
									b.Cases(b.Term("i = 0"))
									b.When(
										"a face of the base simplex matches the opposite face of an original simplex",
										func(c *Argument, atZero Fact) {
											c.Show(
												"both composites are the base simplex one degree lower",
												atZero.Rw(),
												zero.Rw(),
												jValue.Rw(),
												CalcEq(
													Leg(
														c.TermAs[A]("base_simplex(y, n)"),
														"the original mapping face has this opposite face",
														By(data.At(jOld), jInfo)),
													FinalLeg(
														"a face of the added base simplex is the same base simplex",
														ByArith(
															simplicial_set.BaseSimplexFace.Read(simplicial).At(y, n, jOld),
															vertex,
															jInfo,
															kan_complex.HornFacesMember.At(n, k, jOld))),
												))
										})
									b.Otherwise(
										"two positive faces inherit the mapping horn's compatibility",
										func(c *Argument, nonzero Fact) {
											iOld := c.TermAs[Nat]("i - 1")
											iInfo := c.Have(
												"i has a live predecessor below that of j",
												"0 < i ∧ i - 1 ∈ horn_faces(n, k) ∧ i - 1 < j - 1",
												ByArith(
													nonzero,
													live,
													kan_complex.HornFacesMember.At(c.TermAs[Nat]("n + 1"), c.TermAs[Nat]("k + 1"), i),
													kan_complex.HornFacesMember.At(n, k, iOld)))
											iValue := c.Have(
												"H at i is its original face",
												"H(i) = h(i - 1)",
												ByArith(positive.At(i), iInfo))
											oldEquation := c.Have(
												"the predecessor faces satisfy the shifted compatibility equation",
												"X.d(n + 1, i - 1 + 1, h(j - 1)) = X.d(n + 1, j - 1 - 1 + 1, h(i - 1))",
												By(compatible.At(iOld, jOld), iInfo, jInfo))
											indices := c.Have(
												"the positive indices cancel their predecessor shifts",
												"i - 1 + 1 = i ∧ j - 1 - 1 + 1 = j - 1",
												ByArith(iInfo, live))
											bridges := c.Conjuncts(
												indices,
												"the shifted predecessor of i is i",
												"the twice-lowered index of j returns to j − 1")
											c.Show(
												"the original equation is exactly ambient compatibility",
												iValue.Rw(),
												jValue.Rw(),
												bridges[0].Rw(),
												bridges[1].Rw(),
												By(oldEquation))
										})
								})),
						))

					σ, filling := a.ObtainAs[A](
						"the ambient horn has a filler",
						"∃σ:A. σ ∈ X.simplices(n + 1 + 1) ∧ faces_filler(n + 1, horn_faces(n + 1, k + 1), H, σ)",
						Derive(func(b *Argument) {
							b.Cases(b.Term("k ≤ n"))
							b.When(
								"the shifted missing face is inner",
								func(c *Argument, inner Fact) {
									c.Show(
										"inner-horn filling applies",
										ByArith(
											quasi_category.InnerFill.Read(quasi).At(c.TermAs[Nat]("n + 1"), c.TermAs[Nat]("k + 1"), H),
											inner,
											ambient))
								})
							b.Otherwise(
								"the shifted horn misses its last face",
								func(c *Argument, outer Fact) {
									last := c.Have(
										"the missing mapping face is the last one",
										"k = n + 1",
										ByArith(outer, bounded))
									c.Do(last.Rw())
									one := c.Have(
										"one is the successor of zero",
										"1 = suc(0)",
										ByArith())
									baseOne := c.Have(
										"the base 1-simplex is the degenerate edge at y",
										"base_simplex(y, 1) = X.s(0, 0, y)",
										one.Rw(),
										Simp(Fwd(simplicial_set.BaseSimplexDef)),
										Basic())
									degree := c.Have(
										"removing all but one bottom vertex leaves degree one",
										"n + 1 - (n + 1 - 1) = 1",
										ByArith())
									count, dimension := c.TermAs[Nat]("n + 1 - 1"), c.TermAs[Nat]("n + 1")
									lastEdge := c.Have(
										"the ambient last edge is degenerate at y",
										"face_iterate_bottom(n + 1, n + 1 - 1, H(0)) = X.s(0, 0, y)",
										CalcEq(
											Leg(
												c.TermAs[A]("face_iterate_bottom(n + 1, n + 1 - 1, base_simplex(y, n + 1))"),
												"the added face is the base simplex",
												By(Normalized, zero)),
											Leg(
												c.TermAs[A]("base_simplex(y, n + 1 - (n + 1 - 1))"),
												"bottom removals lower a base simplex",
												ByArith(At(bottomBase, X, count, dimension, y), simplicial, vertex)),
											Leg(
												c.TermAs[A]("base_simplex(y, 1)"),
												"the remaining dimension is one",
												By(degree)),
											FinalLeg(
												"the remaining base simplex is the degenerate edge",
												By(baseOne)),
										))
									equivalence := c.Have(
										"that last edge is an equivalence",
										"edge_equivalence(X, face_iterate_bottom(n + 1, n + 1 - 1, H(0)))",
										lastEdge.Rw(),
										By(At(degenerateEquivalence, X, y), quasi, vertex))
									c.Show(
										"the special last-horn theorem supplies the filler",
										ByArith(quasi_category.RightSpecialHornFill.Read(quasi).At(dimension, H), ambient, equivalence))
								})
						}))
					filled := a.Conjuncts(
						filling,
						"σ has the ambient dimension",
						"σ fills the ambient horn")
					ambientIn := filled[0]
					faces := a.Unfolded(filled[1], simplicial_set.FacesFillerDef)
					j, live := a.ObtainAs[Nat](
						"an original horn face survives",
						"∃j:num. j ∈ horn_faces(n, k)",
						Derive(func(b *Argument) {
							b.Cases(b.Term("k = 0"))
							b.When(
								"face one survives when face zero is missing",
								func(c *Argument, missingZero Fact) {
									c.Take(c.TermAs[Nat]("1"))
									c.Show(
										"one is in the horn",
										ByArith(missingZero, kan_complex.HornFacesMember.At(n, k, c.TermAs[Nat]("1"))))
								})
							b.Otherwise(
								"face zero survives when another face is missing",
								func(c *Argument, notZero Fact) {
									c.Take(c.TermAs[Nat]("0"))
									c.Show(
										"zero is in the horn",
										ByArith(notZero, kan_complex.HornFacesMember.At(n, k, c.TermAs[Nat]("0"))))
								})
						}))
					upperDegree, missing, shifted :=
						a.TermAs[Nat]("n + 1"), a.TermAs[Nat]("k + 1"), a.TermAs[Nat]("j + 1")
					liveFaces := a.Have(
						"the added face and a shifted original face are both prescribed",
						"0 ∈ horn_faces(n + 1, k + 1) ∧ j + 1 ∈ horn_faces(n + 1, k + 1) ∧ j ≤ n + 1",
						ByArith(
							live,
							kan_complex.HornFacesMember.At(n, k, j),
							kan_complex.HornFacesMember.At(upperDegree, missing, a.TermAs[Nat]("0")),
							kan_complex.HornFacesMember.At(upperDegree, missing, shifted)))
					opposite := a.Have(
						"σ has the prescribed opposite base simplex",
						"X.d(n + 1 + 1, 0, σ) = base_simplex(y, n + 1)",
						By(faces.At(a.TermAs[Nat]("0")), liveFaces, zero))
					retained := a.Have(
						"a retained shifted face of σ is the original mapping simplex",
						"X.d(n + 1 + 1, j + 1, σ) = h(j)",
						By(faces.At(shifted), liveFaces, successor.At(j)))
					first := a.Have(
						"the first vertex of σ is x",
						"face_iterate_top(n + 1 + 1, n + 1 + 1, σ) = x",
						CalcEq(
							Leg(
								a.TermAs[A]("face_iterate_top(n + 1, n + 1, X.d(n + 1 + 1, j + 1, σ))"),
								"a retained positive face has the same first vertex",
								ByArith(
									simplicial_set.FaceIterateTopAbove.Read(simplicial).At(upperDegree, upperDegree, shifted, σ),
									ambientIn,
									liveFaces)),
							Leg(
								a.TermAs[A]("face_iterate_top(n + 1, n + 1, h(j))"),
								"that face is the original mapping simplex",
								By(retained)),
							FinalLeg(
								"its first vertex is x",
								By(data.At(j), live)),
						))
					a.Take(σ)
					a.Show(
						"σ is the required mapping-horn filler",
						SplitConj(
							Case(
								"the ambient filler belongs to the mapping complex",
								Unfold(mappingComplexSimplicesDef),
								BySets(ambientIn, first, opposite)),
							Case(
								"its shifted faces are exactly the prescribed mapping faces",
								Unfold(simplicial_set.FacesFillerDef),
								Derive(func(b *Argument) {
									i := b.FixAs[Nat]("i")
									live := b.Assume()
									b.Do(Simp(Fwd(mappingComplexFaceDef)))
									shiftedIndex := b.TermAs[Nat]("i + 1")
									shiftedLive := b.Have(
										"the shifted index is prescribed by the ambient horn",
										"i + 1 ∈ horn_faces(n + 1, k + 1)",
										ByArith(
											live,
											kan_complex.HornFacesMember.At(n, k, i),
											kan_complex.HornFacesMember.At(upperDegree, missing, shiftedIndex)))
									b.Show(
										"the ambient face equation is the mapping face equation",
										By(faces.At(shiftedIndex), shiftedLive, successor.At(i)))
								})),
						))
				})

			return ctx.Lemma(headline, func(
				a *Argument,
				X *Expr[simplicial_set.SimplicialOps[A]],
				quasi Fact,
				x *Expr[A],
				y *Expr[A],
				vertex Fact,
			) {
				simplicial := a.Have(
					"the quasi-category is simplicial",
					"simplicial_set(X)",
					By(quasi_category.QuasiSimplicialSet.Read(quasi)))
				mapping := a.Have(
					"the mapping complex is simplicial",
					"simplicial_set(mapping_complex(X, x, y))",
					By(MappingComplexSimplicialSet.Read(simplicial).At(x, y), vertex))
				a.Show(
					"the mapping complex satisfies the Kan conditions",
					Simp(Fwd(kan_complex.KanComplex)),
					SplitConj(
						Case(
							"its shifted operators form a simplicial set",
							By(mapping)),
						Case(
							"every mapping horn fills",
							Derive(func(b *Argument) {
								n, k := b.FixAs[Nat]("n"), b.FixAs[Nat]("k")
								h := b.FixAs[Fun[Nat, A]]("h")
								given := b.Assume()
								b.Show(
									"adjoin the base face and fill the ambient horn",
									ByArith(At(ambientFill, X, x, y, n, k, h), quasi, vertex, given))
							})),
					))
			})
		}),
	Reading: "No slice or fibration theory is needed: the outer horns " +
		"that arise are exactly the special ones with a degenerate last edge.",
})}

// MappingComplexComponents — the morphisms from x to y of the homotopy
// category are the classes of vertices of the mapping complex.
var MappingComplexComponents = mappingComplexComponentsThm{family.Add(registry.ProofEntry{
	Name: "MappingComplexComponents",
	Key:  "prop_8cbb3c63126dc232",
	Deps: []registry.EntryLike{
		MappingComplexVertices,
		quasi_category.HomotopyCategoryDef,
		quasi_category.HomotopyCategoryMorphismsDef,
		quasi_category.EdgeClassMorphism,
		quasi_category.EdgeHomotopicEnds,
		quasi_category.EdgeRepresentative,
	},
	Build: family.Card(quasi_category.QuasiCategory.Statement(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(0)",
			"y ∈ X.simplices(0)",
		},
		Conclusion: "category_hom(homotopy_category(X), x, y) = " +
			"quotient_on(mapping_complex_simplices(X, x, y, 0), edge_homotopic(X))",
	}),
		"a morphism from x to y is the class of an edge with those ends "+
			"(EdgeClassMorphism, EdgeRepresentative), a vertex of the mapping complex "+
			"(MappingComplexVertices); homotopic edges have the same ends "+
			"(EdgeHomotopicEnds), so its class among the edges is its class among the vertices"),
	Reading: "The zero-dimensional homotopy set simplicial_homotopy_group(…, 0) " +
		"reads its edges in the other direction, so the two are not equal by definition.",
})}
