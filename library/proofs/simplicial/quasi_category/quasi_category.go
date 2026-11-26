// quasi_category.go — quasi-categories, the simplicial sets in which
// every inner horn has a filler, and the homotopy category of one: the
// vertices are its objects, the classes of edges under homotopy its
// morphisms, the composite of two classes the class of the middle face
// of a 2-simplex filling the inner horn of two representatives, the
// composite `segal_composite(g, f)` of two edges. Two edges are
// homotopic when a 2-simplex has them as its last and middle faces and
// the degenerate edge at the second one's target as its 0-th, and
// homotopic edges have the same ends; in a quasi-category the relation
// is an equivalence and the composite is well defined, by filling inner
// 3-horns — one each for symmetry and transitivity, three for the
// composite. Every Kan complex and every nerve is a quasi-category, and
// the homotopy category of the nerve of a category is the category
// itself. The functors from the homotopy category to a category C are
// the simplicial maps into the nerve of C.

package quasi_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/nerve"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The structure and its first examples
// ---------------------------------------------------------------------------

// QuasiCategory — `quasi_category(X)`: a simplicial set in which
// every inner horn, 0 < k < n + 1, has a filler.
var QuasiCategory = quasiCategoryThm{family.DefineStructure(registry.DefEntry{
	Name:    "QuasiCategory",
	Key:     "prop_3736b67d508b164c",
	Const:   "quasi_category",
	Type:    "simplicial_ops(A) → bool",
	Subject: "X",
	Equations: []string{
		"∀X:simplicial_ops(A). " +
			"    quasi_category(X) ⇔ " +
			"    simplicial_set(X) ∧ " +
			"    (∀n k:num. ∀y:(num → A). " +
			"        0 < k ∧ k ≤ n ∧ face_family(X, n, horn_faces(n, k), y) ⇒ " +
			"        ∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(X.d, n, horn_faces(n, k), y, x))",
	},
	Reading: "The inner horns begin in dimension 2 with Λ²₁, two composable edges; " +
		"nothing is asked of the outer horns, so the nerve of a category qualifies.",
})}

// QuasiSimplicialSet — a quasi-category is a simplicial set.
var QuasiSimplicialSet = quasiSimplicialSetThm{family.Add(registry.ProofEntry{
	Name:  "QuasiSimplicialSet",
	Key:   "prop_e0620f468b3d7a21",
	Build: QuasiCategory.Axiom("simplicial_set(X)"),
})}

// InnerFill — every inner horn has a filler.
var InnerFill = innerFillThm{family.Add(registry.ProofEntry{
	Name: "InnerFill",
	Key:  "prop_9faad423bc293895",
	Build: QuasiCategory.Axiom(Statement{
		Binders: "∀n k:num. ∀y:(num → A).",
		Hypotheses: []string{
			"0 < k",
			"k ≤ n",
			"face_family(X, n, horn_faces(n, k), y)",
		},
		Conclusion: "∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x)",
	}),
})}

// KanQuasi — every inner horn is a horn. Unfolding the quasi-category
// leaves the Kan complex's own simplicial set and the inner horns,
// 0 < k ≤ n; each is a horn of the Kan condition, which asks of the
// missing face only k ≤ n + 1.
var KanQuasi = kanQuasiThm{family.Add(registry.ProofEntry{
	Name: "KanQuasi",
	Key:  "prop_93dc2c07a419f36e",
	Build: kan_complex.KanComplex.Law("quasi_category(X)",
		func(a *Argument, kan Fact) {
			a.Do(Unfold(QuasiCategory), SplitConjAll(
				Case(
					"a Kan complex is a simplicial set",
					By(kan_complex.KanSimplicialSet.Read(kan))),
				Case(
					"an inner horn is a horn, its missing face k ≤ n below n + 1, so the Kan condition fills it",
					ByArith(kan_complex.KanFill.Read(kan))),
			))
		}),
})}

// NerveQuasi — the nerve of a category is a quasi-category: its unique
// inner fillers supply inner fillers.
var NerveQuasi = nerveQuasiThm{family.Add(registry.ProofEntry{
	Name: "NerveQuasi",
	Key:  "prop_df39e267dac68c94",
	Build: category.Category.Law("quasi_category(nerve(C))",
		func(a *Argument, cat Fact) {
			unique := a.Have(
				"the nerve has unique inner fillers",
				"inner_horn_unique(nerve(C))",
				By(nerve.NerveInnerHornUnique.Read(cat)))
			a.Show(
				"unique inner fillers supply inner fillers",
				By(UniqueInnerQuasi.Read(unique)))
		}),
})}

// UniqueInnerQuasi — unique inner fillers are inner fillers. Both
// definitions ask for a simplicial set; where the one asks that every
// inner horn have exactly one filler, the other asks only for one.
var UniqueInnerQuasi = uniqueInnerQuasiThm{family.Add(registry.ProofEntry{
	Name: "UniqueInnerQuasi",
	Key:  "prop_9942525afa593fec",
	Build: nerve.InnerHornUnique.Law("quasi_category(X)",
		func(a *Argument, unique Fact) {
			a.Do(Simp(Fwd(QuasiCategory)), SplitConjAll(
				Case(
					"X is a simplicial set",
					By(nerve.UniqueInnerSimplicialSet.Read(unique))),
				Case(
					"an inner horn's one filler is a filler",
					Derive(func(b *Argument) {
						n, k, y := b.FixAs[Nat](), b.FixAs[Nat](), b.FixAs[Fun[Nat, A]]()
						b.Show(
							"the horn y in dimension n + 1 missing the face k has one filler, so it has a filler",
							By(nerve.UniqueInnerFill.Read(unique).At(n, k, y)))
					})),
			))
		}),
})}

// ---------------------------------------------------------------------------
// Homotopy of edges and the homotopy category
// ---------------------------------------------------------------------------

// EdgeHomotopicDef — `edge_homotopic(X, f, g)`: a 2-simplex has
// f as its last face, g as its middle face and the degenerate edge at
// the target of g as its 0-th. Under the structure the text writes
// `edge_homotopic(f, g)`.
var EdgeHomotopicDef = edgeHomotopicDefThm{family.Define(registry.DefEntry{
	Name:     "EdgeHomotopicDef",
	Key:      "prop_4ac905947e53d796",
	Const:    "edge_homotopic",
	Type:     "simplicial_ops(A) → A → A → bool",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀f g:A. " +
			"    edge_homotopic(X, f, g) ⇔ " +
			"    (∃h:A. " +
			"        h ∈ X.simplices(2) ∧ " +
			"        X.d(2, 2, h) = f ∧ " +
			"        X.d(2, 1, h) = g ∧ " +
			"        X.d(2, 0, h) = X.s(0, 0, X.d(1, 0, g)))",
	},
	Reading: "Homotopic edges have the same source and the same target (EdgeHomotopicEnds); " +
		"the relation is stated on the type and is an equivalence on the edges of a quasi-category.",
})}

// EdgeHomotopicEnds — homotopic edges are edges with the same ends. Both
// are faces of the homotopy h, a 2-simplex, whose faces are edges meeting
// at its vertices (simplicial_set.TwoSimplexFaceEnds): f and g, its
// faces 2 and 1, start at one vertex, and f ends where the face 0 starts,
// the degenerate edge at the target of g, which starts at that target
// (simplicial_set.VertexDegeneracyFaces).
var EdgeHomotopicEnds = edgeHomotopicEndsThm{family.Add(registry.ProofEntry{
	Name: "EdgeHomotopicEnds",
	Key:  "prop_e66a0a060a16a2e6",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀f g:A.",
		Hypotheses: []string{
			"edge_homotopic(f, g)",
		},
		Conclusion: "f ∈ X.simplices(1) ∧ " +
			"g ∈ X.simplices(1) ∧ " +
			"X.d(1, 1, f) = X.d(1, 1, g) ∧ " +
			"X.d(1, 0, f) = X.d(1, 0, g)",
	},
		func(a *Argument, simplicial Fact, _, g *Expr[A], homotopic Fact) {
			zero := a.TermAs[Nat]("0")
			h, faces := a.UnpackAs[A](a.Unfolded(homotopic, EdgeHomotopicDef), "h")
			parts := a.Conjuncts(
				faces,
				"h is a 2-simplex",
				"f is its face 2",
				"g its face 1",
				"and the degenerate edge at the target of g its face 0")
			simplex, last, middle, first := parts[0], parts[1], parts[2], parts[3]
			hEnds := simplicial_set.TwoSimplexFaceEnds.Read(simplicial).At(h)
			fEdge := a.Have(
				"f, the face 2 of the 2-simplex h, is an edge",
				"f ∈ X.simplices(1)",
				By(Normalized, hEnds, simplex, last))
			gEdge := a.Have(
				"and so is g, its middle face",
				"g ∈ X.simplices(1)",
				By(Normalized, hEnds, simplex, middle))
			source := a.Have(
				"the middle face of h starts where its face 2 does: f and g have one source",
				"X.d(1, 1, f) = X.d(1, 1, g)",
				By(Normalized, hEnds, simplex, last, middle))
			vertex := a.Have(
				"the target of g, a face of an edge, is a vertex",
				"X.d(1, 0, g) ∈ X.simplices(0)",
				By(simplicial_set.FaceIn.Read(simplicial).At(zero, zero, g), gEdge))
			target := a.Have(
				"and one target, through the degenerate edge at the target of g",
				"X.d(1, 0, f) = X.d(1, 0, g)",
				CalcEq(
					Leg(
						a.TermAs[A]("X.d(1, 1, X.s(0, 0, X.d(1, 0, g)))"),
						"faces 2 and 0 of h share a vertex: the target of f is the source of h's face 0",
						By(Normalized, hEnds, simplex, last, first)),
					FinalLeg(
						"and the source of the degenerate edge at a vertex is that vertex",
						By(simplicial_set.VertexDegeneracyFaces.Read(simplicial).At(a.TermAs[A]("X.d(1, 0, g)")), vertex)),
				))
			a.Show(
				"so f and g are edges with the same ends",
				By(fEdge, gEdge, source, target))
		}),
})}

// EdgeHomotopicRefl — an edge is homotopic to itself, its last
// degeneracy the homotopy (EdgeLastDegeneracyFaces).
var EdgeHomotopicRefl = edgeHomotopicReflThm{family.Add(registry.ProofEntry{
	Name: "EdgeHomotopicRefl",
	Key:  "prop_bb5c2da5697fc533",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀f:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
		},
		Conclusion: "edge_homotopic(f, f)",
	},
		func(a *Argument, simplicial Fact, f *Expr[A], edge Fact) {
			a.Do(Unfold(EdgeHomotopicDef))
			a.Take(a.TermAs[A]("X.s(1, 1, f)"))
			a.Show(
				"so the last degeneracy s(1, 1, f) of the edge f is a homotopy from f to itself",
				By(edge, simplicial_set.EdgeLastDegeneracyFaces.Read(simplicial).At(f)))
		}),
})}

// ThreeHornFillOne — the inner horn Λ³₁ fills: three 2-simplices a, b, c
// placed as the faces 3, 2 and 0 of a 3-simplex, meeting along their
// edges as those faces do, have a fourth 2-simplex w, the face 1 of a
// filler, whose faces are the ones the identity d_i d_j = d_{j−1} d_i
// prescribes. An edge homotopy argument below is one such fill followed
// by a reading of w's faces.
var ThreeHornFillOne = threeHornFillOneThm{family.Add(registry.ProofEntry{
	Name: "ThreeHornFillOne",
	Reading: "The three equations are the compatibility of the horn whose faces " +
		"3, 2 and 0 are a, b and c: faces 2 of a and b meet, face 0 of a meets face " +
		"2 of c, face 0 of b meets face 1 of c. The conclusion reads the filler's " +
		"face 1 through the face identity at the pairs (1, 3), (1, 2) and (0, 1).",
	Key: "prop_616a74e125f57135",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀a b c:A.",
		Hypotheses: []string{
			"a ∈ X.simplices(2)",
			"b ∈ X.simplices(2)",
			"c ∈ X.simplices(2)",
			"X.d(2, 2, a) = X.d(2, 2, b)",
			"X.d(2, 0, a) = X.d(2, 2, c)",
			"X.d(2, 0, b) = X.d(2, 1, c)",
		},
		Conclusion: "∃w:A. " +
			"    w ∈ X.simplices(2) ∧ " +
			"    X.d(2, 2, w) = X.d(2, 1, a) ∧ " +
			"    X.d(2, 1, w) = X.d(2, 1, b) ∧ " +
			"    X.d(2, 0, w) = X.d(2, 0, c)",
	},
		func(a *Argument, quasi Fact, _, _, _ *Expr[A], glued Fact) {
			zero, one, two, three :=
				a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2"), a.TermAs[Nat]("3")
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			parts := a.Conjuncts(
				glued,
				"a is a 2-simplex",
				"so is b",
				"and c",
				"faces 2 of a and b meet",
				"face 0 of a meets face 2 of c",
				"face 0 of b meets face 1 of c")
			aSimplex, bSimplex, cSimplex, meet23, meet03, meet02 :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]

			// The horn: a at 3, b at 2, c at every other index; its value at 1
			// is never read.
			y, yDef := a.LetAs[Fun[Nat, A]]("y", "λi:num. COND(i = 3, a, COND(i = 2, b, c))")
			values := a.Have(
				"the family read at 3, 2 and 0",
				"y(3) = a ∧ y(2) = b ∧ y(0) = c",
				yDef.Rw(),
				ByArith())
			members := a.Have(
				"each member of y is one of the three 2-simplices",
				"∀i:num. y(i) ∈ X.simplices(2)",
				yDef.Rw(),
				By(aSimplex, bSimplex, cSimplex))
			compatible := a.Have(
				"and y is compatible on the faces of the horn, the face 1 missing",
				"faces_compatible(2, horn_faces(2, 1), y)",
				Derive(func(inner *Argument) {
					inner.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
					i, j := inner.FixAs[Nat]("i"), inner.FixAs[Nat]("j")
					pair := inner.Assume()
					pairs := inner.Have(
						"the faces i < j of the horn, the indices up to 3 other than 1, are (2, 3), (0, 3) and (0, 2)",
						"(i = 2 ∧ j = 3 ∨ i = 0 ∧ j = 3) ∨ i = 0 ∧ j = 2",
						ByArith(
							pair,
							kan_complex.HornFacesMember.At(two, one, i),
							kan_complex.HornFacesMember.At(two, one, j)))
					inner.Show(
						"at each of the three pairs the two faces meet",
						pairs.SplitDisj(
							LeftHolds(
								"j = 3, against a face of a",
								Given(func(atJ *Argument, atThree Fact) {
									atJ.Show(
										"i is 2 or 0",
										atThree.SplitDisj(
											LeftHolds(
												"at (2, 3), faces 2 of a and b",
												Given(func(e *Argument, at Fact) {
													e.Do(ByArith(at, values, meet23))
												})),
											RightHolds(
												"at (0, 3), face 0 of a and face 2 of c",
												Given(func(e *Argument, at Fact) {
													e.Do(ByArith(at, values, meet03))
												})),
										))
								})),
							RightHolds(
								"at (0, 2), face 0 of b and face 1 of c",
								Given(func(e *Argument, at Fact) {
									e.Do(ByArith(at, values, meet02))
								})),
						))
				}))

			horn := a.Have(
				"so y is a face family on the faces of the horn Λ³₁",
				"face_family(2, horn_faces(2, 1), y)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(members, compatible))

			// The filler, and the three faces of it the horn prescribes.
			x, filler := a.ObtainAs[A](
				"so the inner horn y has a filler, a 3-simplex",
				"∃x:A. x ∈ X.simplices(3) ∧ faces_filler(2, horn_faces(2, 1), y, x)",
				By(InnerFill.Read(quasi).At(two, one, y), horn))
			fills := a.Conjuncts(
				filler,
				"x is a 3-simplex",
				"whose faces on the horn are the members of y")
			xSimplex := fills[0]
			faceOf := a.Have(
				"at each face i of the horn the face i of x is y(i)",
				"∀i:num. i ∈ horn_faces(2, 1) ⇒ X.d(3, i, x) = y(i)",
				By(a.Unfolded(fills[1], simplicial_set.FacesFillerDef)))
			hornFaces := a.Have(
				"3, 2 and 0, indices up to 3 other than 1, are faces of the horn",
				"3 ∈ horn_faces(2, 1) ∧ 2 ∈ horn_faces(2, 1) ∧ 0 ∈ horn_faces(2, 1)",
				By(kan_complex.HornFacesMember))
			prescribed := a.Have(
				"so its faces 3, 2 and 0 are a, b and c",
				"X.d(3, 3, x) = a ∧ X.d(3, 2, x) = b ∧ X.d(3, 0, x) = c",
				By(faceOf.At(three), faceOf.At(two), faceOf.At(zero), hornFaces, values))

			// Its face 1, w: each face of w is a face of a prescribed face of x.
			w := a.TermAs[A]("X.d(3, 1, x)")
			wSimplex := a.Have(
				"w = d(3, 1, x), a face of a 3-simplex, is a 2-simplex",
				"X.d(3, 1, x) ∈ X.simplices(2)",
				By(simplicial_set.FaceIn.Read(simplicial).At(two, one, x), xSimplex))
			wLast := a.Have(
				"faces 1 and 3 of x meet along an edge: face 2 of w is face 1 of a",
				"X.d(2, 2, X.d(3, 1, x)) = X.d(2, 1, a)",
				ByArith(simplicial_set.FaceFace.Read(simplicial).At(one, one, three, x), xSimplex, prescribed))
			wMiddle := a.Have(
				"faces 1 and 2 of x meet along an edge: face 1 of w is face 1 of b",
				"X.d(2, 1, X.d(3, 1, x)) = X.d(2, 1, b)",
				ByArith(simplicial_set.FaceFace.Read(simplicial).At(one, one, two, x), xSimplex, prescribed))
			wFirst := a.Have(
				"faces 0 and 1 of x meet along an edge: face 0 of w is face 0 of c",
				"X.d(2, 0, X.d(3, 1, x)) = X.d(2, 0, c)",
				ByArith(simplicial_set.FaceFace.Read(simplicial).At(one, zero, one, x), xSimplex, prescribed))
			a.Take(w)
			a.Show(
				"so w is the fourth face the horn asks for",
				By(wSimplex, wLast, wMiddle, wFirst))
		}),
})}

// ThreeHornFillTwo — the inner horn Λ³₂ fills: three 2-simplices a, b, c
// placed as the faces 3, 1 and 0 of a 3-simplex, meeting along their
// edges as those faces do, have a fourth 2-simplex w, the face 2 of a
// filler, whose faces are the ones the identity d_i d_j = d_{j−1} d_i
// prescribes.
var ThreeHornFillTwo = threeHornFillTwoThm{family.Add(registry.ProofEntry{
	Name: "ThreeHornFillTwo",
	Reading: "The three equations are the compatibility of the horn whose faces " +
		"3, 1 and 0 are a, b and c: face 1 of a meets face 2 of b, face 0 of a meets " +
		"face 2 of c, faces 0 of b and c meet. The conclusion reads the filler's " +
		"face 2 through the face identity at the pairs (2, 3), (1, 2) and (0, 2).",
	Key: "prop_1819e4d55f7c26e3",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀a b c:A.",
		Hypotheses: []string{
			"a ∈ X.simplices(2)",
			"b ∈ X.simplices(2)",
			"c ∈ X.simplices(2)",
			"X.d(2, 1, a) = X.d(2, 2, b)",
			"X.d(2, 0, a) = X.d(2, 2, c)",
			"X.d(2, 0, b) = X.d(2, 0, c)",
		},
		Conclusion: "∃w:A. " +
			"    w ∈ X.simplices(2) ∧ " +
			"    X.d(2, 2, w) = X.d(2, 2, a) ∧ " +
			"    X.d(2, 1, w) = X.d(2, 1, b) ∧ " +
			"    X.d(2, 0, w) = X.d(2, 1, c)",
	},
		func(a *Argument, quasi Fact, _, _, _ *Expr[A], glued Fact) {
			zero, one, two, three :=
				a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2"), a.TermAs[Nat]("3")
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			parts := a.Conjuncts(
				glued,
				"a is a 2-simplex",
				"so is b",
				"and c",
				"face 1 of a meets face 2 of b",
				"face 0 of a meets face 2 of c",
				"faces 0 of b and c meet")
			aSimplex, bSimplex, cSimplex, meet13, meet03, meet01 :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]

			// The horn: a at 3, b at 1, c at every other index; its value at 2
			// is never read.
			y, yDef := a.LetAs[Fun[Nat, A]]("y", "λi:num. COND(i = 3, a, COND(i = 1, b, c))")
			values := a.Have(
				"the family read at 3, 1 and 0",
				"y(3) = a ∧ y(1) = b ∧ y(0) = c",
				yDef.Rw(),
				ByArith())
			members := a.Have(
				"each member of y is one of the three 2-simplices",
				"∀i:num. y(i) ∈ X.simplices(2)",
				yDef.Rw(),
				By(aSimplex, bSimplex, cSimplex))
			compatible := a.Have(
				"and y is compatible on the faces of the horn, the face 2 missing",
				"faces_compatible(2, horn_faces(2, 2), y)",
				Derive(func(inner *Argument) {
					inner.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
					i, j := inner.FixAs[Nat]("i"), inner.FixAs[Nat]("j")
					pair := inner.Assume()
					pairs := inner.Have(
						"the faces i < j of the horn, the indices up to 3 other than 2, are (1, 3), (0, 3) and (0, 1)",
						"(i = 1 ∧ j = 3 ∨ i = 0 ∧ j = 3) ∨ i = 0 ∧ j = 1",
						ByArith(
							pair,
							kan_complex.HornFacesMember.At(two, two, i),
							kan_complex.HornFacesMember.At(two, two, j)))
					inner.Show(
						"at each of the three pairs the two faces meet",
						pairs.SplitDisj(
							LeftHolds(
								"j = 3, against a face of a",
								Given(func(atJ *Argument, atThree Fact) {
									atJ.Show(
										"i is 1 or 0",
										atThree.SplitDisj(
											LeftHolds(
												"at (1, 3), face 1 of a and face 2 of b",
												Given(func(e *Argument, at Fact) {
													e.Do(ByArith(at, values, meet13))
												})),
											RightHolds(
												"at (0, 3), face 0 of a and face 2 of c",
												Given(func(e *Argument, at Fact) {
													e.Do(ByArith(at, values, meet03))
												})),
										))
								})),
							RightHolds(
								"at (0, 1), the faces 0 of b and c",
								Given(func(e *Argument, at Fact) {
									e.Do(ByArith(at, values, meet01))
								})),
						))
				}))

			horn := a.Have(
				"so y is a face family on the faces of the horn Λ³₂",
				"face_family(2, horn_faces(2, 2), y)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(members, compatible))

			// The filler, and the three faces of it the horn prescribes.
			x, filler := a.ObtainAs[A](
				"so the inner horn y has a filler, a 3-simplex",
				"∃x:A. x ∈ X.simplices(3) ∧ faces_filler(2, horn_faces(2, 2), y, x)",
				By(InnerFill.Read(quasi).At(two, two, y), horn))
			fills := a.Conjuncts(
				filler,
				"x is a 3-simplex",
				"whose faces on the horn are the members of y")
			xSimplex := fills[0]
			faceOf := a.Have(
				"at each face i of the horn the face i of x is y(i)",
				"∀i:num. i ∈ horn_faces(2, 2) ⇒ X.d(3, i, x) = y(i)",
				By(a.Unfolded(fills[1], simplicial_set.FacesFillerDef)))
			hornFaces := a.Have(
				"3, 1 and 0, indices up to 3 other than 2, are faces of the horn",
				"3 ∈ horn_faces(2, 2) ∧ 1 ∈ horn_faces(2, 2) ∧ 0 ∈ horn_faces(2, 2)",
				By(kan_complex.HornFacesMember))
			prescribed := a.Have(
				"so its faces 3, 1 and 0 are a, b and c",
				"X.d(3, 3, x) = a ∧ X.d(3, 1, x) = b ∧ X.d(3, 0, x) = c",
				By(faceOf.At(three), faceOf.At(one), faceOf.At(zero), hornFaces, values))

			// Its face 2, w: each face of w is a face of a prescribed face of x.
			w := a.TermAs[A]("X.d(3, 2, x)")
			wSimplex := a.Have(
				"w = d(3, 2, x), a face of a 3-simplex, is a 2-simplex",
				"X.d(3, 2, x) ∈ X.simplices(2)",
				By(simplicial_set.FaceIn.Read(simplicial).At(two, two, x), xSimplex))
			wLast := a.Have(
				"faces 2 and 3 of x meet along an edge: face 2 of w is face 2 of a",
				"X.d(2, 2, X.d(3, 2, x)) = X.d(2, 2, a)",
				ByArith(simplicial_set.FaceFace.Read(simplicial).At(one, two, three, x), xSimplex, prescribed))
			wMiddle := a.Have(
				"faces 1 and 2 of x meet along an edge: face 1 of w is face 1 of b",
				"X.d(2, 1, X.d(3, 2, x)) = X.d(2, 1, b)",
				ByArith(simplicial_set.FaceFace.Read(simplicial).At(one, one, two, x), xSimplex, prescribed))
			wFirst := a.Have(
				"faces 0 and 2 of x meet along an edge: face 0 of w is face 1 of c",
				"X.d(2, 0, X.d(3, 2, x)) = X.d(2, 1, c)",
				ByArith(simplicial_set.FaceFace.Read(simplicial).At(one, zero, two, x), xSimplex, prescribed))
			a.Take(w)
			a.Show(
				"so w is the fourth face the horn asks for",
				By(wSimplex, wLast, wMiddle, wFirst))
		}),
})}

// EdgeHomotopicSym — in a quasi-category the relation is symmetric. With
// h a homotopy from f to g, the inner horn Λ³₁ whose faces are h at 3,
// the last degeneracy s(1, 1, f) at 2 and the degenerate 2-simplex at
// the common target at 0 fills (ThreeHornFillOne); its fourth face has
// g, f and the degenerate edge at the target of f as its faces 2, 1
// and 0, a homotopy from g to f.
var EdgeHomotopicSym = edgeHomotopicSymThm{family.Add(registry.ProofEntry{
	Name: "EdgeHomotopicSym",
	Key:  "prop_a6f7a6f117e11d45",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀f g:A.",
		Hypotheses: []string{
			"edge_homotopic(f, g)",
		},
		Conclusion: "edge_homotopic(g, f)",
	},
		func(a *Argument, quasi Fact, f, g *Expr[A], homotopic Fact) {
			zero := a.TermAs[Nat]("0")
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			h, faces := a.UnpackAs[A](a.Unfolded(homotopic, EdgeHomotopicDef), "h")
			parts := a.Conjuncts(
				faces,
				"h is a 2-simplex",
				"f is its face 2",
				"g its face 1",
				"and the degenerate edge at the target of g its face 0")
			simplex, last, middle, first := parts[0], parts[1], parts[2], parts[3]
			ends := a.Conjuncts(
				a.Have(
					"homotopic edges are edges with the same ends",
					"f ∈ X.simplices(1) ∧ "+
						"g ∈ X.simplices(1) ∧ "+
						"X.d(1, 1, f) = X.d(1, 1, g) ∧ "+
						"X.d(1, 0, f) = X.d(1, 0, g)",
					By(homotopic, EdgeHomotopicEnds.Read(simplicial).At(f, g))),
				"f is an edge",
				"so is g",
				"the two share a source",
				"and a target")
			fEdge, gEdge, sameTarget := ends[0], ends[1], ends[3]

			// The faces of the horn: h, the last degeneracy of f, and the
			// degenerate 2-simplex at the target, the first degeneracy of the
			// degenerate edge there.
			targetVertex, targetEdge := a.TermAs[A]("X.d(1, 0, g)"), a.TermAs[A]("X.s(0, 0, X.d(1, 0, g))")
			fDegenerate, targetSimplex :=
				a.TermAs[A]("X.s(1, 1, f)"), a.TermAs[A]("X.s(1, 0, X.s(0, 0, X.d(1, 0, g)))")
			vertex := a.Have(
				"the target of g, a face of an edge, is a vertex",
				"X.d(1, 0, g) ∈ X.simplices(0)",
				By(simplicial_set.FaceIn.Read(simplicial).At(zero, zero, g), gEdge))
			degenerateEdgeEnds := simplicial_set.VertexDegeneracyFaces.Read(simplicial).At(targetVertex)
			targetEdgeIn := a.Have(
				"its degenerate edge is an edge",
				"X.s(0, 0, X.d(1, 0, g)) ∈ X.simplices(1)",
				By(degenerateEdgeEnds, vertex))
			targetSimplexFaces := simplicial_set.EdgeFirstDegeneracyFaces.Read(simplicial).At(targetEdge)
			byF := a.Conjuncts(
				a.Have(
					"the last degeneracy of the edge f is a 2-simplex with f as its faces 1 and 2",
					"X.s(1, 1, f) ∈ X.simplices(2) ∧ "+
						"X.d(2, 0, X.s(1, 1, f)) = X.s(0, 0, X.d(1, 0, f)) ∧ "+
						"X.d(2, 1, X.s(1, 1, f)) = f ∧ "+
						"X.d(2, 2, X.s(1, 1, f)) = f",
					By(fEdge, simplicial_set.EdgeLastDegeneracyFaces.Read(simplicial).At(f))),
				"s(1, 1, f) is a 2-simplex",
				"its face 0 is the degenerate edge at the target of f",
				"its face 1 is f",
				"and its face 2 is f")
			fSimplexIn, fFirst, fMiddle, fLast := byF[0], byF[1], byF[2], byF[3]

			// The three pairs of faces the horn glues agree.
			meet23 := a.Have(
				"faces 2 of h and of s(1, 1, f) are both f",
				"X.d(2, 2, h) = X.d(2, 2, X.s(1, 1, f))",
				By(Normalized, last, fLast))
			meet03 := a.Have(
				"face 0 of h and face 2 of the degenerate 2-simplex "+
					"at the target are both the degenerate edge there",
				"X.d(2, 0, h) = X.d(2, 2, X.s(1, 0, X.s(0, 0, X.d(1, 0, g))))",
				CalcEq(
					Leg(
						targetEdge,
						"face 0 of h is the degenerate edge at the target",
						By(first)),
					Leg(
						a.TermAs[A]("X.s(0, 0, X.d(1, 1, X.s(0, 0, X.d(1, 0, g))))"),
						"whose source is the target itself",
						By(degenerateEdgeEnds, vertex)),
					FinalLeg(
						"and the degenerate edge at that source is face 2 of the degenerate 2-simplex at the target",
						By(targetEdgeIn, targetSimplexFaces)),
				))
			meet02 := a.Have(
				"face 0 of s(1, 1, f) and face 1 of the degenerate "+
					"2-simplex at the target are both the degenerate edge there",
				"X.d(2, 0, X.s(1, 1, f)) = X.d(2, 1, X.s(1, 0, X.s(0, 0, X.d(1, 0, g))))",
				CalcEq(
					Leg(
						targetEdge,
						"face 0 of s(1, 1, f) is the degenerate edge at the target f shares with g",
						sameTarget.RwRev(),
						By(fFirst)),
					FinalLeg(
						"which is face 1 of the degenerate 2-simplex at the target",
						By(targetEdgeIn, targetSimplexFaces)),
				))

			// The horn fills; the faces of its fourth face w are faces of the
			// three glued 2-simplices, read off them in turn.
			w, wFaces := a.ObtainAs[A](
				"so the horn on h, s(1, 1, f) and the degenerate 2-simplex at the target fills, with fourth face w",
				"∃w:A. "+
					"    w ∈ X.simplices(2) ∧ "+
					"    X.d(2, 2, w) = X.d(2, 1, h) ∧ "+
					"    X.d(2, 1, w) = X.d(2, 1, X.s(1, 1, f)) ∧ "+
					"    X.d(2, 0, w) = X.d(2, 0, X.s(1, 0, X.s(0, 0, X.d(1, 0, g))))",
				By(
					ThreeHornFillOne.Read(quasi).At(h, fDegenerate, targetSimplex),
					simplex,
					fSimplexIn,
					targetEdgeIn,
					targetSimplexFaces,
					meet23,
					meet03,
					meet02))
			wParts := a.Conjuncts(
				wFaces,
				"w is a 2-simplex",
				"its face 2 is face 1 of h",
				"its face 1 is face 1 of s(1, 1, f)",
				"and its face 0 is face 0 of the degenerate 2-simplex at the target")
			wSimplex, wLastOfH, wMiddleOfDegenerate, wFirstOfDegenerate :=
				wParts[0], wParts[1], wParts[2], wParts[3]
			wLast := a.Have(
				"face 2 of w is g, the face 1 of h",
				"X.d(2, 2, w) = g",
				By(wLastOfH, middle))
			wMiddle := a.Have(
				"face 1 of w is f, the face 1 of s(1, 1, f)",
				"X.d(2, 1, w) = f",
				By(Normalized, wMiddleOfDegenerate, fMiddle))
			wFirst := a.Have(
				"face 0 of w is the degenerate edge at the target of f",
				"X.d(2, 0, w) = X.s(0, 0, X.d(1, 0, f))",
				CalcEq(
					Leg(
						targetEdge,
						"face 0 of w is face 0 of the degenerate 2-simplex "+
							"at the target: the degenerate edge at the target of g",
						By(wFirstOfDegenerate, targetEdgeIn, targetSimplexFaces)),
					FinalLeg(
						"a target f shares with g",
						By(Normalized, sameTarget)),
				))
			a.Do(Simp(Fwd(EdgeHomotopicDef)))
			a.Take(w)
			a.Show(
				"so w is a homotopy from g to f",
				By(wSimplex, wLast, wMiddle, wFirst))
		}),
})}

// EdgeHomotopicTrans — and transitive. With h a homotopy from f to g and
// h' one from g to k, the inner horn Λ³₂ whose faces are h at 3, h' at 1
// and the degenerate 2-simplex at the common target at 0 fills
// (ThreeHornFillTwo); its fourth face has f, k and the degenerate edge at
// the target of k as its faces 2, 1 and 0, a homotopy from f to k.
var EdgeHomotopicTrans = edgeHomotopicTransThm{family.Add(registry.ProofEntry{
	Name: "EdgeHomotopicTrans",
	Key:  "prop_896f6e78255934c8",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀f g k:A.",
		Hypotheses: []string{
			"edge_homotopic(f, g)",
			"edge_homotopic(g, k)",
		},
		Conclusion: "edge_homotopic(f, k)",
	},
		func(a *Argument, quasi Fact, f, g, k *Expr[A], homotopic Fact) {
			zero := a.TermAs[Nat]("0")
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			both := a.Conjuncts(
				homotopic,
				"f is homotopic to g",
				"and g to k")
			fToG, gToK := both[0], both[1]
			h, facesH := a.UnpackAs[A](a.Unfolded(fToG, EdgeHomotopicDef), "h")
			byH := a.Conjuncts(
				facesH,
				"h is a 2-simplex",
				"f is its face 2",
				"g its face 1",
				"and the degenerate edge at the target of g its face 0")
			hSimplex, hLast, hMiddle, hFirst := byH[0], byH[1], byH[2], byH[3]
			hPrime, facesHPrime := a.UnpackAs[A](a.Unfolded(gToK, EdgeHomotopicDef), "h'")
			byHPrime := a.Conjuncts(
				facesHPrime,
				"h' is a 2-simplex",
				"g is its face 2",
				"k its face 1",
				"and the degenerate edge at the target of k its face 0")
			hPrimeSimplex, hPrimeLast, hPrimeMiddle, hPrimeFirst :=
				byHPrime[0], byHPrime[1], byHPrime[2], byHPrime[3]
			sameTarget := a.Have(
				"homotopic edges have the same ends: g and k share a target",
				"X.d(1, 0, g) = X.d(1, 0, k)",
				By(gToK, EdgeHomotopicEnds.Read(simplicial).At(g, k)))

			// The faces of the horn: the two homotopies and the degenerate
			// 2-simplex at the common target, the first degeneracy of the
			// degenerate edge there.
			targetVertex, targetEdge := a.TermAs[A]("X.d(1, 0, g)"), a.TermAs[A]("X.s(0, 0, X.d(1, 0, g))")
			targetSimplex := a.TermAs[A]("X.s(1, 0, X.s(0, 0, X.d(1, 0, g)))")
			vertex := a.Have(
				"the target of g, a face of an edge, is a vertex",
				"X.d(1, 0, g) ∈ X.simplices(0)",
				By(
					simplicial_set.FaceIn.Read(simplicial).At(zero, zero, g),
					fToG,
					EdgeHomotopicEnds.Read(simplicial).At(f, g)))
			degenerateEdgeEnds := simplicial_set.VertexDegeneracyFaces.Read(simplicial).At(targetVertex)
			targetEdgeIn := a.Have(
				"its degenerate edge is an edge",
				"X.s(0, 0, X.d(1, 0, g)) ∈ X.simplices(1)",
				By(degenerateEdgeEnds, vertex))
			targetSimplexFaces := simplicial_set.EdgeFirstDegeneracyFaces.Read(simplicial).At(targetEdge)

			// The three pairs of faces the horn glues agree.
			meet13 := a.Have(
				"face 1 of h and face 2 of h' are both g",
				"X.d(2, 1, h) = X.d(2, 2, h')",
				By(Normalized, hMiddle, hPrimeLast))
			meet03 := a.Have(
				"face 0 of h and face 2 of the degenerate 2-simplex "+
					"at the target are both the degenerate edge there",
				"X.d(2, 0, h) = X.d(2, 2, X.s(1, 0, X.s(0, 0, X.d(1, 0, g))))",
				CalcEq(
					Leg(
						targetEdge,
						"face 0 of h is the degenerate edge at the target",
						By(hFirst)),
					Leg(
						a.TermAs[A]("X.s(0, 0, X.d(1, 1, X.s(0, 0, X.d(1, 0, g))))"),
						"whose source is the target itself",
						By(degenerateEdgeEnds, vertex)),
					FinalLeg(
						"and the degenerate edge at that source is face 2 of the degenerate 2-simplex at the target",
						By(targetEdgeIn, targetSimplexFaces)),
				))
			meet01 := a.Have(
				"face 0 of h' and face 0 of the degenerate 2-simplex "+
					"at the target are both the degenerate edge there",
				"X.d(2, 0, h') = X.d(2, 0, X.s(1, 0, X.s(0, 0, X.d(1, 0, g))))",
				CalcEq(
					Leg(
						targetEdge,
						"face 0 of h' is the degenerate edge at the target of k, which g shares",
						sameTarget.Rw(),
						By(hPrimeFirst)),
					FinalLeg(
						"which is face 0 of the degenerate 2-simplex at the target",
						By(targetEdgeIn, targetSimplexFaces)),
				))

			// The horn fills; the faces of its fourth face w are faces of the
			// three glued 2-simplices, read off them in turn.
			w, wFaces := a.ObtainAs[A](
				"so the horn on h, h' and the degenerate 2-simplex at the target fills, with fourth face w",
				"∃w:A. "+
					"    w ∈ X.simplices(2) ∧ "+
					"    X.d(2, 2, w) = X.d(2, 2, h) ∧ "+
					"    X.d(2, 1, w) = X.d(2, 1, h') ∧ "+
					"    X.d(2, 0, w) = X.d(2, 1, X.s(1, 0, X.s(0, 0, X.d(1, 0, g))))",
				By(
					ThreeHornFillTwo.Read(quasi).At(h, hPrime, targetSimplex),
					hSimplex,
					hPrimeSimplex,
					targetEdgeIn,
					targetSimplexFaces,
					meet13,
					meet03,
					meet01))
			wParts := a.Conjuncts(
				wFaces,
				"w is a 2-simplex",
				"its face 2 is face 2 of h",
				"its face 1 is face 1 of h'",
				"and its face 0 is face 1 of the degenerate 2-simplex at the target")
			wSimplex, wLastOfH, wMiddleOfHPrime, wFirstOfDegenerate :=
				wParts[0], wParts[1], wParts[2], wParts[3]
			wLast := a.Have(
				"face 2 of w is f, the face 2 of h",
				"X.d(2, 2, w) = f",
				By(Normalized, wLastOfH, hLast))
			wMiddle := a.Have(
				"face 1 of w is k, the face 1 of h'",
				"X.d(2, 1, w) = k",
				By(Normalized, wMiddleOfHPrime, hPrimeMiddle))
			wFirst := a.Have(
				"face 0 of w is the degenerate edge at the target of k",
				"X.d(2, 0, w) = X.s(0, 0, X.d(1, 0, k))",
				CalcEq(
					Leg(
						targetEdge,
						"face 0 of w is face 1 of the degenerate 2-simplex "+
							"at the target: the degenerate edge at the target of g",
						By(wFirstOfDegenerate, targetEdgeIn, targetSimplexFaces)),
					FinalLeg(
						"a target k shares with g",
						By(Normalized, sameTarget)),
				))
			a.Do(Simp(Fwd(EdgeHomotopicDef)))
			a.Take(w)
			a.Show(
				"so w is a homotopy from f to k",
				By(wSimplex, wLast, wMiddle, wFirst))
		}),
})}

// EdgeHomotopicEquivalenceOn — in a quasi-category homotopy is an
// equivalence on the edges: reflexive there (EdgeHomotopicRefl),
// symmetric and transitive on any simplices (EdgeHomotopicSym,
// EdgeHomotopicTrans). The morphisms of the homotopy category are its
// quotient.
var EdgeHomotopicEquivalenceOn = edgeHomotopicEquivalenceOnThm{family.Add(registry.ProofEntry{
	Name: "EdgeHomotopicEquivalenceOn",
	Key:  "prop_31640550ebb7e691",
	Build: QuasiCategory.Law("equivalence_on(X.simplices(1), edge_homotopic)",
		func(a *Argument, quasi Fact) {
			a.Do(Unfold(equivalence.EquivalenceOn), SplitConjAll(
				Case(
					"reflexive on the edges: an edge is homotopic to itself",
					By(EdgeHomotopicRefl.Read(QuasiSimplicialSet.Read(quasi)))),
				Case(
					"symmetric, as on any two simplices",
					By(EdgeHomotopicSym.Read(quasi))),
				Case(
					"and transitive, as on any three",
					By(EdgeHomotopicTrans.Read(quasi))),
			))
		}),
})}

// EdgeClassEqIff — two edges have one class exactly when they are
// homotopic. Homotopy is an equivalence on the edges
// (EdgeHomotopicEquivalenceOn), and an edge homotopic to anything is an
// edge (EdgeHomotopicEnds): on a set closed under an equivalence two
// points have one class exactly when they are related
// (equivalence.ClassEqIffClosed).
var EdgeClassEqIff = edgeClassEqIffThm{family.Add(registry.ProofEntry{
	Name: "EdgeClassEqIff",
	Reading: "One membership is load-bearing: an edge homotopic to " +
		"anything is an edge (EdgeHomotopicEnds), so the class of a non-edge " +
		"is empty and two non-edges share a class without being homotopic.",
	Key: "prop_2434f78322b32222",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀f g:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
			"g ∈ X.simplices(1)",
		},
		Conclusion: "equivalence_class(edge_homotopic, f) = equivalence_class(edge_homotopic, g) ⇔ " +
			"edge_homotopic(f, g)",
	},
		func(a *Argument, quasi Fact, f, g *Expr[A], edges Fact) {
			equiv := a.Have(
				"homotopy is an equivalence on the edges",
				"equivalence_on(X.simplices(1), edge_homotopic)",
				By(EdgeHomotopicEquivalenceOn, quasi))
			closed := a.Have(
				"an edge homotopic to anything is an edge",
				"∀u v:A. u ∈ X.simplices(1) ∧ edge_homotopic(u, v) ⇒ v ∈ X.simplices(1)",
				By(EdgeHomotopicEnds.Read(QuasiSimplicialSet.Read(quasi))))
			a.Show(
				"the edges being closed under homotopy, two of them have one class exactly when they are homotopic",
				By(equivalence.ClassEqIffClosed.Read(equiv).AsFact().At(f, g), closed, edges))
		}),
})}

// HomotopyCategoryMorphismsDef — the morphisms of the homotopy
// category: the quotient of the edges by homotopy, the relations
// chapter's `quotient_on` at the edges and the homotopy relation. Its
// members are the classes of edges (InHomotopyCategoryMorphisms).
var HomotopyCategoryMorphismsDef = homotopyCategoryMorphismsDefThm{family.Define(registry.DefEntry{
	Name:     "HomotopyCategoryMorphismsDef",
	Key:      "prop_6d7a45bdf8a7a2e1",
	Const:    "homotopy_category_morphisms",
	Type:     "simplicial_ops(A) → set(set(A))",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). " +
			"    homotopy_category_morphisms(X) = quotient_on(X.simplices(1), edge_homotopic(X))",
	},
	Deps: []registry.EntryLike{EdgeHomotopicDef},
})}

// InHomotopyCategoryMorphisms — a morphism of the homotopy category is
// the class of an edge. An edge homotopic to anything is an edge
// (EdgeHomotopicEnds), so the edges are closed under homotopy, and the
// quotient of a set closed under a relation is its image under the class
// map (equivalence.QuotientOnClosed).
var InHomotopyCategoryMorphisms = inHomotopyCategoryMorphismsThm{family.Add(registry.ProofEntry{
	Name: "InHomotopyCategoryMorphisms",
	Key:  "prop_b40fdfae8e06d922",
	Build: simplicial_set.SimplicialSet.Law("∀E:set(A). "+
		"    E ∈ homotopy_category_morphisms(X) ⇔ "+
		"    ∃f:A. f ∈ X.simplices(1) ∧ E = equivalence_class(edge_homotopic, f)",
		func(a *Argument, simplicial Fact, _ *Expr[Set[A]]) {
			closed := a.Have(
				"an edge homotopic to anything is an edge",
				"∀f g:A. f ∈ X.simplices(1) ∧ edge_homotopic(f, g) ⇒ g ∈ X.simplices(1)",
				By(EdgeHomotopicEnds.Read(simplicial)))
			asImage := a.Have(
				"so the morphisms, the quotient of the edges, are their image under the class map",
				"homotopy_category_morphisms(X) = image(equivalence_class(edge_homotopic), X.simplices(1))",
				Unfold(HomotopyCategoryMorphismsDef),
				By(closed, equivalence.QuotientOnClosed))
			a.Show(
				"and a member of that image is the class of some edge",
				asImage.Rw(),
				BySets())
		}),
})}

// ClassInHomotopyCategoryMorphisms — the class of an edge is a morphism
// of the homotopy category. The edges are closed under homotopy
// (EdgeHomotopicEnds), and the class of a point of a set closed under a
// relation is a member of its quotient
// (equivalence.ClassInQuotientOnClosed).
var ClassInHomotopyCategoryMorphisms = classInHomotopyCategoryMorphismsThm{family.Add(registry.ProofEntry{
	Name: "ClassInHomotopyCategoryMorphisms",
	Key:  "prop_30752b40bc1b4fc8",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀f:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
		},
		Conclusion: "equivalence_class(edge_homotopic, f) ∈ homotopy_category_morphisms(X)",
	},
		func(a *Argument, simplicial Fact, f *Expr[A], edge Fact) {
			edges := a.TermAs[Set[A]]("X.simplices(1)")
			homotopic := a.TermAs[Fun2[A, A, Bool]]("edge_homotopic")
			closed := a.Have(
				"an edge homotopic to anything is an edge",
				"∀u v:A. u ∈ X.simplices(1) ∧ edge_homotopic(u, v) ⇒ v ∈ X.simplices(1)",
				By(EdgeHomotopicEnds.Read(simplicial)))
			a.Show(
				"so the class of the edge f is a member of the quotient of the edges, a morphism",
				Unfold(HomotopyCategoryMorphismsDef),
				By(closed, edge, equivalence.ClassInQuotientOnClosed.At(edges, homotopic, f)))
		}),
})}

// edgeClassSourceDef — the source of a class of edges, read at a chosen
// representative. Under the structure the text writes
// `edge_class_source(E)`.
var edgeClassSourceDef = edgeClassSourceDefThm{family.Define(registry.DefEntry{
	Name:     "edgeClassSourceDef",
	Key:      "prop_98e20bbb8e3b5ba9",
	Const:    "edge_class_source",
	Type:     "(num → num → A → A) → set(A) → A",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀E:set(A). edge_class_source(d, E) = d(1, 1, εf:A. f ∈ E)",
	},
})}

// edgeClassTargetDef — the target of a class of edges.
var edgeClassTargetDef = edgeClassTargetDefThm{family.Define(registry.DefEntry{
	Name:     "edgeClassTargetDef",
	Key:      "prop_5e84d0ecf582a947",
	Const:    "edge_class_target",
	Type:     "(num → num → A → A) → set(A) → A",
	Implicit: []string{"d"},
	Equations: []string{
		"∀d:(num → num → A → A). ∀E:set(A). edge_class_target(d, E) = d(1, 0, εf:A. f ∈ E)",
	},
})}

// edgeClassIdentityDef — the identity at a vertex, the class of its
// degenerate edge.
var edgeClassIdentityDef = edgeClassIdentityDefThm{family.Define(registry.DefEntry{
	Name:     "edgeClassIdentityDef",
	Key:      "prop_ef01a1c2b30593c0",
	Const:    "edge_class_identity",
	Type:     "simplicial_ops(A) → A → set(A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀x:A. " +
			"    edge_class_identity(X, x) = equivalence_class(edge_homotopic(X), X.s(0, 0, x))",
	},
	Deps: []registry.EntryLike{EdgeHomotopicDef},
})}

// SegalCompositeDef — `segal_composite(X, d, g, f)`: the composite of
// two edges in a simplicial set with inner fillers, the middle face of a
// chosen 2-simplex with f as its last face and g as its 0-th. Under the
// structure the text writes `segal_composite(g, f)`.
var SegalCompositeDef = segalCompositeDefThm{family.Define(registry.DefEntry{
	Name:     "SegalCompositeDef",
	Key:      "prop_dd3175f9a0febc35",
	Const:    "segal_composite",
	Type:     "simplicial_ops(A) → A → A → A",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀g f:A. " +
			"    segal_composite(X, g, f) = " +
			"    X.d(2, 1, εw:A. w ∈ X.simplices(2) ∧ X.d(2, 2, w) = f ∧ X.d(2, 0, w) = g)",
	},
	Reading: "g after f: the 2-simplex has f from vertex 0 to 1 and g from 1 " +
		"to 2, and its middle face goes from 0 to 2. With unique inner fillers the " +
		"choice is forced; in a quasi-category it is one of the homotopic composites.",
})}

// edgeClassComposeDef — the composite of two classes, G after F: the
// class of the composite of chosen representatives, the middle face of
// a chosen 2-simplex with F's representative as its last face and G's
// as its 0-th.
var edgeClassComposeDef = edgeClassComposeDefThm{family.Define(registry.DefEntry{
	Name:     "edgeClassComposeDef",
	Key:      "prop_5899abfc4b7feb55",
	Const:    "edge_class_compose",
	Type:     "simplicial_ops(A) → set(A) → set(A) → set(A)",
	Implicit: []string{"X"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀G F:set(A). " +
			"    edge_class_compose(X, G, F) = " +
			"    equivalence_class(edge_homotopic(X), segal_composite(X, εg:A. g ∈ G, εf:A. f ∈ F))",
	},
	Deps: []registry.EntryLike{EdgeHomotopicDef},
})}

// EdgeRepresentative — E is the class of an edge f, which is homotopic
// to itself, so to the member e chosen in E
// (equivalence.ChosenRepresentative); e therefore lies in E, and is an
// edge (EdgeHomotopicEnds) whose class is the class of f
// (EdgeClassEqIff).
var EdgeRepresentative = edgeRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "EdgeRepresentative",
	Key:  "prop_7df32429e30057c9",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀E:set(A).",
		Hypotheses: []string{
			"E ∈ homotopy_category_morphisms(X)",
		},
		Conclusion: "(εf:A. f ∈ E) ∈ E ∧ " +
			"(εf:A. f ∈ E) ∈ X.simplices(1) ∧ " +
			"E = equivalence_class(edge_homotopic, εf:A. f ∈ E)",
	},
		func(a *Argument, quasi Fact, E *Expr[Set[A]], morphism Fact) {
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			homotopic := a.TermAs[Fun2[A, A, Bool]]("edge_homotopic")
			e, chosen := a.LetAs[A]("e", "εf:A. f ∈ E")
			f, represented := a.ObtainAs[A](
				"E is a morphism: the class of an edge f",
				"∃f:A. f ∈ X.simplices(1) ∧ E = equivalence_class(edge_homotopic, f)",
				By(morphism, InHomotopyCategoryMorphisms.Read(simplicial).At(E)))
			parts := a.Conjuncts(
				represented,
				"f is an edge",
				"and E is its class")
			edge, class := parts[0], parts[1]
			toE := a.Have(
				"f is homotopic to itself, so to the member e chosen in E, its class",
				"edge_homotopic(f, e)",
				chosen.Rw(),
				class.Rw(),
				By(
					EdgeHomotopicRefl.Read(simplicial).At(f),
					edge,
					equivalence.ChosenRepresentative.At(homotopic, f)))
			eIn := a.Have(
				"so e lies in E, the class of f",
				"e ∈ E",
				class.Rw(),
				By(equivalence.InClass, toE))
			eEdge := a.Have(
				"so e is an edge",
				"e ∈ X.simplices(1)",
				By(toE, EdgeHomotopicEnds.Read(simplicial).At(f, e)))
			sameClass := a.Have(
				"and homotopic edges have one class",
				"equivalence_class(edge_homotopic, f) = equivalence_class(edge_homotopic, e)",
				By(edge, eEdge, toE, EdgeClassEqIff.Read(quasi).At(f, e)))
			a.Show(
				"so e lies in E, is an edge, and E, the class of f, is its class",
				By(Normalized, eIn, eEdge, class, sameClass))
		}),
})}

// EdgeClassMorphism — the class of an edge is a morphism
// (ClassInHomotopyCategoryMorphisms), with the edge's ends for its
// source and target. The ends of a class are those of its chosen
// member; the edge, homotopic to itself, is homotopic to that member
// (equivalence.ChosenRepresentative), and the two share their ends.
var EdgeClassMorphism = edgeClassMorphismThm{family.Add(registry.ProofEntry{
	Name: "EdgeClassMorphism",
	Key:  "prop_6925fae85c606ba1",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀f:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
		},
		Conclusion: "equivalence_class(edge_homotopic, f) ∈ homotopy_category_morphisms(X) ∧ " +
			"edge_class_source(equivalence_class(edge_homotopic, f)) = X.d(1, 1, f) ∧ " +
			"edge_class_target(equivalence_class(edge_homotopic, f)) = X.d(1, 0, f)",
	},
		func(a *Argument, simplicial Fact, f *Expr[A], edge Fact) {
			morphism := a.Have(
				"the class of the edge f is a morphism",
				"equivalence_class(edge_homotopic, f) ∈ homotopy_category_morphisms",
				By(edge, ClassInHomotopyCategoryMorphisms.Read(simplicial).At(f)))
			homotopic := a.TermAs[Fun2[A, A, Bool]]("edge_homotopic")
			e := a.TermAs[A]("εe:A. e ∈ equivalence_class(edge_homotopic, f)")
			toChosen := a.Have(
				"f is homotopic to itself, so to the member chosen in its class",
				"edge_homotopic(f, εe:A. e ∈ equivalence_class(edge_homotopic, f))",
				By(
					EdgeHomotopicRefl.Read(simplicial).At(f),
					edge,
					equivalence.ChosenRepresentative.At(homotopic, f)))
			a.Show(
				"the ends of the class are those of its chosen member, which homotopic edges share with f",
				Simp(Fwd(edgeClassSourceDef), Fwd(edgeClassTargetDef)),
				By(morphism, toChosen, EdgeHomotopicEnds.Read(simplicial).At(f, e)))
		}),
})}

// CompositeExists — composable edges have a composite 2-simplex, the
// filler of Λ²₁: the family y with f at 2 and g at 0 is an inner horn of
// dimension 2, its one pair of faces meeting where the target of f is
// the source of g, and InnerFill fills it.
var CompositeExists = compositeExistsThm{family.Add(registry.ProofEntry{
	Name: "CompositeExists",
	Key:  "prop_182ba62bec014498",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀f g:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
			"g ∈ X.simplices(1)",
			"X.d(1, 0, f) = X.d(1, 1, g)",
		},
		Conclusion: "∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 2, w) = f ∧ X.d(2, 0, w) = g",
	},
		func(a *Argument, quasi Fact, _, _ *Expr[A], composable Fact) {
			zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")
			// The horn: f at 2, g everywhere else, its value at 1 never read.
			y, yDef := a.LetAs[Fun[Nat, A]]("y", "λi:num. COND(i = 2, f, g)")
			values := a.Have(
				"the family read at 2 and at 0",
				"y(2) = f ∧ y(0) = g",
				yDef.Rw(),
				ByArith())
			edges := a.Have(
				"each member of y is f or g, an edge",
				"∀i:num. y(i) ∈ X.simplices(1)",
				By(yDef, composable))
			compatible := a.Have(
				"and compatible on the faces of the horn, the face 1 missing: one pair of them avoids 1",
				"faces_compatible(1, horn_faces(1, 1), y)",
				Derive(func(b *Argument) {
					b.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
					i, j := b.FixAs[Nat]("i"), b.FixAs[Nat]("j")
					pair := b.Assume()
					ends := b.Have(
						"the faces i < j of the horn, the indices up to 2 other than 1, are the pair (0, 2)",
						"i = 0 ∧ j = 2",
						ByArith(
							pair,
							kan_complex.HornFacesMember.At(one, one, i),
							kan_complex.HornFacesMember.At(one, one, j)))
					b.Show(
						"where the condition is d(1, 0, y(2)) = d(1, 1, y(0)): the target of f is the source of g",
						ByArith(values, ends, composable))
				}))
			horn := a.Have(
				"so y is a face family on the faces of the horn Λ²₁",
				"face_family(1, horn_faces(1, 1), y)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(edges, compatible))
			w, filler := a.ObtainAs[A](
				"so the inner horn y has a filler, a 2-simplex",
				"∃w:A. w ∈ X.simplices(2) ∧ faces_filler(1, horn_faces(1, 1), y, w)",
				By(InnerFill.Read(quasi).At(one, one, y), horn))
			parts := a.Conjuncts(
				filler,
				"w is a 2-simplex",
				"whose faces on the horn are the members of y")
			simplex := parts[0]
			faceOf := a.Have(
				"at each face i of the horn the face i of w is y(i)",
				"∀i:num. i ∈ horn_faces(1, 1) ⇒ X.d(2, i, w) = y(i)",
				By(a.Unfolded(parts[1], simplicial_set.FacesFillerDef)))
			hornFaces := a.Have(
				"2 and 0, indices up to 2 other than 1, are faces of the horn",
				"2 ∈ horn_faces(1, 1) ∧ 0 ∈ horn_faces(1, 1)",
				By(kan_complex.HornFacesMember))
			faces := a.Have(
				"so its faces 2 and 0 are y(2) = f and y(0) = g",
				"X.d(2, 2, w) = f ∧ X.d(2, 0, w) = g",
				By(faceOf.At(two), faceOf.At(zero), hornFaces, values))
			a.Take(w)
			a.Show(
				"so w is a composite 2-simplex of f and g",
				By(simplex, faces))
		}),
})}

// CompositeHomotopic — the composite of classes is well defined. With h
// a homotopy from f to f' and k one from g to g', three inner horns fill
// in turn, each through a 3-simplex: Λ³₁ on h, w and s(1, 0, g) gives a
// composite w₁ of f' and g with the middle face m of w; Λ³₂ on w₁,
// s(1, 1, m) and k a composite u of f' and g' with the same middle face;
// Λ³₁ on u, w' and s(1, 1, g') a 2-simplex v whose faces are m, the
// middle face of w' and the degenerate edge at its target — a homotopy.
var CompositeHomotopic = compositeHomotopicThm{family.Add(registry.ProofEntry{
	Name: "CompositeHomotopic",
	Key:  "prop_413db82cfeca7efd",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀f f' g g' w w':A.",
		Hypotheses: []string{
			"edge_homotopic(f, f')",
			"edge_homotopic(g, g')",
			"w ∈ X.simplices(2)",
			"X.d(2, 2, w) = f",
			"X.d(2, 0, w) = g",
			"w' ∈ X.simplices(2)",
			"X.d(2, 2, w') = f'",
			"X.d(2, 0, w') = g'",
		},
		Conclusion: "edge_homotopic(X.d(2, 1, w), X.d(2, 1, w'))",
	},
		func(a *Argument, quasi Fact, f, fPrime, g, gPrime, w, wPrime *Expr[A], given Fact) {
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			parts := a.Conjuncts(
				given,
				"f is homotopic to f'",
				"and g to g'",
				"w is a 2-simplex",
				"with f as its face 2",
				"and g as its face 0",
				"w' is a 2-simplex",
				"with f' as its face 2",
				"and g' as its face 0")
			homotopicF, homotopicG, wSimplex, wLast, wFirst := parts[0], parts[1], parts[2], parts[3], parts[4]
			wPrimeSimplex, wPrimeLast, wPrimeFirst := parts[5], parts[6], parts[7]
			h, facesH := a.UnpackAs[A](a.Unfolded(homotopicF, EdgeHomotopicDef), "h")
			byH := a.Conjuncts(
				facesH,
				"h is a 2-simplex",
				"f is its face 2",
				"f' its face 1",
				"and the degenerate edge at the target of f' its face 0")
			hSimplex, hLast, hMiddle, hFirst := byH[0], byH[1], byH[2], byH[3]
			k, facesK := a.UnpackAs[A](a.Unfolded(homotopicG, EdgeHomotopicDef), "k")
			byK := a.Conjuncts(
				facesK,
				"k is a 2-simplex",
				"g is its face 2",
				"g' its face 1",
				"and the degenerate edge at the target of g' its face 0")
			kSimplex, kLast, kMiddle, kFirst := byK[0], byK[1], byK[2], byK[3]

			// The ends the three fills glue along.
			sameTargetF := a.Have(
				"homotopic edges have the same ends: f and f' share a target",
				"X.d(1, 0, f) = X.d(1, 0, f')",
				By(homotopicF, EdgeHomotopicEnds.Read(simplicial).At(f, fPrime)))
			endsG := a.Conjuncts(
				a.Have(
					"and g and g' are edges sharing a target",
					"g ∈ X.simplices(1) ∧ g' ∈ X.simplices(1) ∧ X.d(1, 0, g) = X.d(1, 0, g')",
					By(homotopicG, EdgeHomotopicEnds.Read(simplicial).At(g, gPrime))),
				"g is an edge",
				"so is g'",
				"and the two share a target")
			gEdge, gPrimeEdge, sameTargetG := endsG[0], endsG[1], endsG[2]
			m := a.TermAs[A]("X.d(2, 1, w)")
			faceEnds := simplicial_set.TwoSimplexFaceEnds.Read(simplicial)
			wEnds := faceEnds.At(w)
			composable := a.Have(
				"faces 2 and 0 of w share a vertex: the target of f', that of f, is the source of g",
				"X.d(1, 0, f') = X.d(1, 1, g)",
				By(Normalized, wEnds, wSimplex, wLast, wFirst, sameTargetF))
			mTarget := a.Have(
				"faces 1 and 0 of w share a vertex: its middle face m ends where g, and so g', does",
				"X.d(1, 0, X.d(2, 1, w)) = X.d(1, 0, g')",
				By(wEnds, wSimplex, wFirst, sameTargetG))
			mPrimeTarget := a.Have(
				"and faces 1 and 0 of w' share one: its middle face ends where g' does",
				"X.d(1, 0, X.d(2, 1, w')) = X.d(1, 0, g')",
				By(faceEnds.At(wPrime), wPrimeSimplex, wPrimeFirst))

			// The degenerate 2-simplices the horns take as faces, and their faces.
			gDegenerate, mDegenerate, gPrimeDegenerate :=
				a.TermAs[A]("X.s(1, 0, g)"), a.TermAs[A]("X.s(1, 1, X.d(2, 1, w))"), a.TermAs[A]("X.s(1, 1, g')")
			byG := a.Conjuncts(
				a.Have(
					"the first degeneracy of the edge g is a 2-simplex with g as its faces 0 and 1",
					"X.s(1, 0, g) ∈ X.simplices(2) ∧ "+
						"X.d(2, 0, X.s(1, 0, g)) = g ∧ "+
						"X.d(2, 1, X.s(1, 0, g)) = g ∧ "+
						"X.d(2, 2, X.s(1, 0, g)) = X.s(0, 0, X.d(1, 1, g))",
					By(gEdge, simplicial_set.EdgeFirstDegeneracyFaces.Read(simplicial).At(g))),
				"s(1, 0, g) is a 2-simplex",
				"its face 0 is g",
				"so is its face 1",
				"and its face 2 is the degenerate edge at the source of g")
			gDegenerateIn, gDegenerateFirst, gDegenerateMiddle, gDegenerateLast :=
				byG[0], byG[1], byG[2], byG[3]
			byM := a.Conjuncts(
				a.Have(
					"the last degeneracy of the edge m, a face of w, is a 2-simplex with m as its faces 1 and 2",
					"X.s(1, 1, X.d(2, 1, w)) ∈ X.simplices(2) ∧ "+
						"X.d(2, 0, X.s(1, 1, X.d(2, 1, w))) = X.s(0, 0, X.d(1, 0, X.d(2, 1, w))) ∧ "+
						"X.d(2, 1, X.s(1, 1, X.d(2, 1, w))) = X.d(2, 1, w) ∧ "+
						"X.d(2, 2, X.s(1, 1, X.d(2, 1, w))) = X.d(2, 1, w)",
					By(wEnds, wSimplex, simplicial_set.EdgeLastDegeneracyFaces.Read(simplicial).At(m))),
				"s(1, 1, m) is a 2-simplex",
				"its face 0 is the degenerate edge at the target of m",
				"its face 1 is m",
				"and its face 2 is m")
			mDegenerateIn, mDegenerateFirst, mDegenerateMiddle, mDegenerateLast :=
				byM[0], byM[1], byM[2], byM[3]
			byGPrime := a.Conjuncts(
				a.Have(
					"and the last degeneracy of g' a 2-simplex with g' as its faces 1 and 2",
					"X.s(1, 1, g') ∈ X.simplices(2) ∧ "+
						"X.d(2, 0, X.s(1, 1, g')) = X.s(0, 0, X.d(1, 0, g')) ∧ "+
						"X.d(2, 1, X.s(1, 1, g')) = g' ∧ "+
						"X.d(2, 2, X.s(1, 1, g')) = g'",
					By(gPrimeEdge, simplicial_set.EdgeLastDegeneracyFaces.Read(simplicial).At(gPrime))),
				"s(1, 1, g') is a 2-simplex",
				"its face 0 is the degenerate edge at the target of g'",
				"its face 1 is g'",
				"and its face 2 is g'")
			gPrimeDegenerateIn, gPrimeDegenerateFirst, gPrimeDegenerateMiddle, gPrimeDegenerateLast :=
				byGPrime[0], byGPrime[1], byGPrime[2], byGPrime[3]

			// The first fill: Λ³₁ on h, w and s(1, 0, g). Its fourth face w₁
			// composes f' and g with the middle face m.
			meet23W1 := a.Have(
				"faces 2 of h and w are both f",
				"X.d(2, 2, h) = X.d(2, 2, w)",
				By(Normalized, hLast, wLast))
			meet03W1 := a.Have(
				"face 0 of h, the degenerate edge at the target of f', "+
					"is face 2 of s(1, 0, g), the one at the source of g",
				"X.d(2, 0, h) = X.d(2, 2, X.s(1, 0, g))",
				By(hFirst, composable, gDegenerateLast))
			meet02W1 := a.Have(
				"face 0 of w and face 1 of s(1, 0, g) are both g",
				"X.d(2, 0, w) = X.d(2, 1, X.s(1, 0, g))",
				By(Normalized, wFirst, gDegenerateMiddle))
			w1, w1Faces := a.ObtainAs[A](
				"so the horn on h, w and s(1, 0, g) fills, with fourth face w₁",
				"∃w₁:A. "+
					"    w₁ ∈ X.simplices(2) ∧ "+
					"    X.d(2, 2, w₁) = X.d(2, 1, h) ∧ "+
					"    X.d(2, 1, w₁) = X.d(2, 1, w) ∧ "+
					"    X.d(2, 0, w₁) = X.d(2, 0, X.s(1, 0, g))",
				By(
					ThreeHornFillOne.Read(quasi).At(h, w, gDegenerate),
					hSimplex,
					wSimplex,
					gDegenerateIn,
					meet23W1,
					meet03W1,
					meet02W1))
			w1Parts := a.Conjuncts(
				w1Faces,
				"w₁ is a 2-simplex",
				"its face 2 is face 1 of h",
				"its face 1 is m",
				"and its face 0 is face 0 of s(1, 0, g)")
			w1Simplex, w1LastOfH, w1Middle, w1FirstOfDegenerate :=
				w1Parts[0], w1Parts[1], w1Parts[2], w1Parts[3]
			w1Last := a.Have(
				"face 2 of w₁ is f', the face 1 of h",
				"X.d(2, 2, w₁) = f'",
				By(w1LastOfH, hMiddle))
			w1First := a.Have(
				"face 0 of w₁ is g, the face 0 of s(1, 0, g)",
				"X.d(2, 0, w₁) = g",
				By(Normalized, w1FirstOfDegenerate, gDegenerateFirst))

			// The second fill: Λ³₂ on w₁, s(1, 1, m) and k. Its fourth face u
			// composes f' and g' with the same middle face m.
			meet13U := a.Have(
				"face 1 of w₁ and face 2 of s(1, 1, m) are both m",
				"X.d(2, 1, w₁) = X.d(2, 2, X.s(1, 1, X.d(2, 1, w)))",
				By(w1Middle, mDegenerateLast))
			meet03U := a.Have(
				"faces 0 of w₁ and 2 of k are both g",
				"X.d(2, 0, w₁) = X.d(2, 2, k)",
				By(Normalized, w1First, kLast))
			meet01U := a.Have(
				"face 0 of s(1, 1, m), the degenerate edge at the "+
					"target of m, is face 0 of k, the one at the target of g'",
				"X.d(2, 0, X.s(1, 1, X.d(2, 1, w))) = X.d(2, 0, k)",
				By(mDegenerateFirst, mTarget, kFirst))
			u, uFaces := a.ObtainAs[A](
				"so the horn on w₁, s(1, 1, m) and k fills, with fourth face u",
				"∃u:A. "+
					"    u ∈ X.simplices(2) ∧ "+
					"    X.d(2, 2, u) = X.d(2, 2, w₁) ∧ "+
					"    X.d(2, 1, u) = X.d(2, 1, X.s(1, 1, X.d(2, 1, w))) ∧ "+
					"    X.d(2, 0, u) = X.d(2, 1, k)",
				By(
					ThreeHornFillTwo.Read(quasi).At(w1, mDegenerate, k),
					w1Simplex,
					mDegenerateIn,
					kSimplex,
					meet13U,
					meet03U,
					meet01U))
			uParts := a.Conjuncts(
				uFaces,
				"u is a 2-simplex",
				"its face 2 is face 2 of w₁",
				"its face 1 is face 1 of s(1, 1, m)",
				"and its face 0 is face 1 of k")
			uSimplex, uLastOfW1, uMiddleOfDegenerate, uFirstOfK := uParts[0], uParts[1], uParts[2], uParts[3]
			uLast := a.Have(
				"face 2 of u is f', the face 2 of w₁",
				"X.d(2, 2, u) = f'",
				By(uLastOfW1, w1Last))
			uMiddle := a.Have(
				"face 1 of u is m, the face 1 of s(1, 1, m)",
				"X.d(2, 1, u) = X.d(2, 1, w)",
				By(uMiddleOfDegenerate, mDegenerateMiddle))
			uFirst := a.Have(
				"face 0 of u is g', the face 1 of k",
				"X.d(2, 0, u) = g'",
				By(Normalized, uFirstOfK, kMiddle))

			// The third fill: Λ³₁ on u, w' and s(1, 1, g'). Its fourth face v
			// is the homotopy.
			meet23V := a.Have(
				"faces 2 of u and w' are both f'",
				"X.d(2, 2, u) = X.d(2, 2, w')",
				By(Normalized, uLast, wPrimeLast))
			meet03V := a.Have(
				"face 0 of u and face 2 of s(1, 1, g') are both g'",
				"X.d(2, 0, u) = X.d(2, 2, X.s(1, 1, g'))",
				By(Normalized, uFirst, gPrimeDegenerateLast))
			meet02V := a.Have(
				"face 0 of w' and face 1 of s(1, 1, g') are both g'",
				"X.d(2, 0, w') = X.d(2, 1, X.s(1, 1, g'))",
				By(Normalized, wPrimeFirst, gPrimeDegenerateMiddle))
			v, vFaces := a.ObtainAs[A](
				"so the horn on u, w' and s(1, 1, g') fills, with fourth face v",
				"∃v:A. "+
					"    v ∈ X.simplices(2) ∧ "+
					"    X.d(2, 2, v) = X.d(2, 1, u) ∧ "+
					"    X.d(2, 1, v) = X.d(2, 1, w') ∧ "+
					"    X.d(2, 0, v) = X.d(2, 0, X.s(1, 1, g'))",
				By(
					ThreeHornFillOne.Read(quasi).At(u, wPrime, gPrimeDegenerate),
					uSimplex,
					wPrimeSimplex,
					gPrimeDegenerateIn,
					meet23V,
					meet03V,
					meet02V))
			vParts := a.Conjuncts(
				vFaces,
				"v is a 2-simplex",
				"its face 2 is face 1 of u",
				"its face 1 is the middle face of w'",
				"and its face 0 is face 0 of s(1, 1, g')")
			vSimplex, vLastOfU, vMiddle, vFirstOfDegenerate := vParts[0], vParts[1], vParts[2], vParts[3]
			vLast := a.Have(
				"face 2 of v is m, the face 1 of u",
				"X.d(2, 2, v) = X.d(2, 1, w)",
				By(vLastOfU, uMiddle))
			vFirst := a.Have(
				"face 0 of v is the degenerate edge at the target of g', which the middle face of w' shares",
				"X.d(2, 0, v) = X.s(0, 0, X.d(1, 0, X.d(2, 1, w')))",
				By(vFirstOfDegenerate, gPrimeDegenerateFirst, mPrimeTarget))
			a.Do(Simp(Fwd(EdgeHomotopicDef)))
			a.Take(v)
			a.Show(
				"so v is a homotopy from m to the middle face of w'",
				By(vSimplex, vLast, vMiddle, vFirst))
		}),
})}

// ComposeClass — the composite of the classes of two composable edges
// is the class of the middle face of any composite 2-simplex. By
// definition it is the class of the middle face of u, the chosen
// 2-simplex on the chosen members f' and g' of the two classes. Each
// edge is homotopic to itself, so to the member chosen in its class
// (equivalence.ChosenRepresentative): f, g are homotopic to f', g',
// edges with the same ends, hence composable, and u is a composite of
// them (CompositeExists). Then u and w compose
// homotopic edges, so their middle faces are homotopic
// (CompositeHomotopic) and have one class (EdgeClassEqIff).
var ComposeClass = composeClassThm{family.Add(registry.ProofEntry{
	Name: "ComposeClass",
	Key:  "prop_ba1d28ef50571eb9",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀f g w:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
			"g ∈ X.simplices(1)",
			"X.d(1, 0, f) = X.d(1, 1, g)",
			"w ∈ X.simplices(2)",
			"X.d(2, 2, w) = f",
			"X.d(2, 0, w) = g",
		},
		Conclusion: "edge_class_compose(equivalence_class(edge_homotopic, g), " +
			"    equivalence_class(edge_homotopic, f)) = " +
			"equivalence_class(edge_homotopic, X.d(2, 1, w))",
	},
		func(a *Argument, quasi Fact, f, g, w *Expr[A], given Fact) {
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			parts := a.Conjuncts(
				given,
				"f is an edge",
				"so is g",
				"the target of f is the source of g",
				"w is a 2-simplex",
				"with f as its face 2",
				"and g as its face 0")
			fEdge, gEdge, composable, wSimplex, wLast, wFirst :=
				parts[0], parts[1], parts[2], parts[3], parts[4], parts[5]

			// Unfolded, the composite is the class of the middle face of the
			// chosen 2-simplex u on the chosen members f', g' of the classes
			// of f and g; the goal is that class against the class of w's.
			a.Do(Simp(Fwd(edgeClassComposeDef), Fwd(SegalCompositeDef)))
			fPrime, fDef := a.LetAs[A]("f'", "εx:A. x ∈ equivalence_class(edge_homotopic, f)")
			gPrime, gDef := a.LetAs[A]("g'", "εx:A. x ∈ equivalence_class(edge_homotopic, g)")
			u, uDef := a.LetAs[A]("u", "εv:A. v ∈ X.simplices(2) ∧ X.d(2, 2, v) = f' ∧ X.d(2, 0, v) = g'")

			// f and g are homotopic to the chosen members, so they share
			// their ends.
			homotopic := a.TermAs[Fun2[A, A, Bool]]("edge_homotopic")
			toF := a.Have(
				"the edge f is homotopic to itself, so to the member f' chosen in its class",
				"edge_homotopic(f, f')",
				fDef.Rw(),
				By(
					EdgeHomotopicRefl.Read(simplicial).At(f),
					fEdge,
					equivalence.ChosenRepresentative.At(homotopic, f)))
			toG := a.Have(
				"and likewise g to g'",
				"edge_homotopic(g, g')",
				gDef.Rw(),
				By(
					EdgeHomotopicRefl.Read(simplicial).At(g),
					gEdge,
					equivalence.ChosenRepresentative.At(homotopic, g)))
			endsF := a.Have(
				"homotopic edges have the same ends: f' is an edge with the target of f",
				"f' ∈ X.simplices(1) ∧ X.d(1, 0, f) = X.d(1, 0, f')",
				By(toF, EdgeHomotopicEnds.Read(simplicial).At(f, fPrime)))
			endsG := a.Have(
				"and g' an edge with the source of g",
				"g' ∈ X.simplices(1) ∧ X.d(1, 1, g) = X.d(1, 1, g')",
				By(toG, EdgeHomotopicEnds.Read(simplicial).At(g, gPrime)))
			composablePrime := a.Have(
				"so f' and g' are composable: f' ends where f does, at the source of g, which is the source of g'",
				"X.d(1, 0, f') = X.d(1, 1, g')",
				By(Normalized, endsF, composable, endsG))

			// The chosen composite, and its middle face against w's.
			_, composite := a.ObtainChosen(
				"composable edges have a composite 2-simplex, and the chosen one is a composite",
				"∃v:A. v ∈ X.simplices(2) ∧ X.d(2, 2, v) = f' ∧ X.d(2, 0, v) = g'",
				endsF,
				endsG,
				composablePrime,
				CompositeExists.Read(quasi).At(fPrime, gPrime))
			uFaces := a.Have(
				"so u is a 2-simplex with f' as its face 2 and g' as its face 0",
				"u ∈ X.simplices(2) ∧ X.d(2, 2, u) = f' ∧ X.d(2, 0, u) = g'",
				By(Normalized, uDef, composite))
			wMiddle, uMiddle := a.TermAs[A]("X.d(2, 1, w)"), a.TermAs[A]("X.d(2, 1, u)")
			middle := a.Have(
				"w and u compose homotopic edges, so their middle faces are homotopic",
				"edge_homotopic(X.d(2, 1, w), X.d(2, 1, u))",
				By(
					toF,
					toG,
					wSimplex,
					wLast,
					wFirst,
					uFaces,
					CompositeHomotopic.Read(quasi).At(f, fPrime, g, gPrime, w, u)))
			middleEdges := a.Have(
				"homotopic edges are edges: both middle faces are",
				"X.d(2, 1, w) ∈ X.simplices(1) ∧ X.d(2, 1, u) ∈ X.simplices(1)",
				By(middle, EdgeHomotopicEnds.Read(simplicial).At(wMiddle, uMiddle)))
			a.Show(
				"so the two middle faces, homotopic edges, have one class",
				By(middleEdges, middle, EdgeClassEqIff.Read(quasi).At(wMiddle, uMiddle)))
		}),
})}

// HomotopyCategoryDef — `homotopy_category(X)`: the record of the
// homotopy category — the vertices for objects, the classes of edges
// for morphisms, with the ends, identities and composites of classes
// above.
var HomotopyCategoryDef = homotopyCategoryDefThm{family.Define(registry.DefEntry{
	Name:  "HomotopyCategoryDef",
	Key:   "prop_98cc1f5bf34f0e70",
	Const: "homotopy_category",
	Type:  "simplicial_ops(A) → category_ops(A, set(A))",
	Equations: []string{
		"∀X:simplicial_ops(A). " +
			"    homotopy_category(X) = " +
			"    mk_category(X.simplices(0), " +
			"        homotopy_category_morphisms, " +
			"        edge_class_source, " +
			"        edge_class_target, " +
			"        edge_class_identity, " +
			"        edge_class_compose)",
	},
	Deps: []registry.EntryLike{
		HomotopyCategoryMorphismsDef,
		edgeClassSourceDef,
		edgeClassTargetDef,
		edgeClassIdentityDef,
		edgeClassComposeDef,
	},
})}

// HomotopyCategory — the homotopy category of a quasi-category is a
// category on its vertices and classes of edges. A morphism is the class
// of an edge, and has that edge's ends (EdgeClassMorphism); the identity
// at a vertex is the class of its degenerate edge, an edge from the
// vertex to itself (simplicial_set.VertexDegeneracyFaces); the composite
// of two classes is the class of the middle face of any composite
// 2-simplex of representatives (ComposeClass), whose faces give it its
// ends (simplicial_set.TwoSimplexFaceEnds). The unit laws read the two
// degeneracies of an edge as composite 2-simplices with the edge as
// middle face. Associativity is one 3-simplex: composite 2-simplices u
// of f and g, w of g∘f and k, and v of g and k form the inner horn Λ³₂,
// and its fourth face composes f and k∘g with the middle face of w.
var HomotopyCategory = homotopyCategoryThm{family.Add(registry.ProofEntry{
	Name: "HomotopyCategory",
	Key:  "prop_a14b71aab9d89160",
	Build: QuasiCategory.Law("category(homotopy_category(X))",
		func(a *Argument, quasi Fact) {
			zero, one := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			faceIn, faceEnds :=
				simplicial_set.FaceIn.Read(simplicial), simplicial_set.TwoSimplexFaceEnds.Read(simplicial)
			degenerateEdgeEnds := simplicial_set.VertexDegeneracyFaces.Read(simplicial)
			classMorphism := EdgeClassMorphism.Read(simplicial)

			edgeOf := a.Have(
				"every morphism is the class of an edge, with that edge's ends",
				Statement{
					Binders: "∀F:set(A).",
					Hypotheses: []string{
						"F ∈ homotopy_category_morphisms",
					},
					Conclusion: "∃f:A. " +
						"    f ∈ X.simplices(1) ∧ " +
						"    F = equivalence_class(edge_homotopic, f) ∧ " +
						"    edge_class_source(F) = X.d(1, 1, f) ∧ " +
						"    edge_class_target(F) = X.d(1, 0, f)",
				},
				Derive(func(b *Argument) {
					F := b.FixAs[Set[A]]()
					morphism := b.Assume()
					f, represents := b.ObtainAs[A](
						"F is the class of an edge f",
						"∃f:A. f ∈ X.simplices(1) ∧ F = equivalence_class(edge_homotopic, f)",
						By(morphism, InHomotopyCategoryMorphisms.Read(simplicial).At(F)))
					b.Take(f)
					b.Show(
						"and the class of an edge has the edge's ends",
						By(Normalized, represents, classMorphism.At(f)))
				}))

			// The clauses of a category, in the order the definition states them.
			ends := a.Have(
				"the ends of a morphism are vertices, faces of its chosen representative",
				Statement{
					Binders: "∀F:set(A).",
					Hypotheses: []string{
						"F ∈ homotopy_category_morphisms",
					},
					Conclusion: "edge_class_source(F) ∈ X.simplices(0) ∧ edge_class_target(F) ∈ X.simplices(0)",
				},
				Derive(func(b *Argument) {
					F := b.FixAs[Set[A]]()
					morphism := b.Assume()
					chosen := b.TermAs[A]("εf:A. f ∈ F")
					b.Show(
						"the chosen representative of F is an edge, and the faces of an edge are vertices",
						Simp(Fwd(edgeClassSourceDef), Fwd(edgeClassTargetDef)),
						By(
							morphism,
							EdgeRepresentative.Read(quasi).At(F),
							faceIn.At(zero, one, chosen),
							faceIn.At(zero, zero, chosen)))
				}))
			identities := a.Have(
				"the identity at a vertex x, the class of its degenerate edge, is a morphism from x to x",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ X.simplices(0)",
					},
					Conclusion: "edge_class_identity(x) ∈ homotopy_category_morphisms ∧ " +
						"edge_class_source(edge_class_identity(x)) = x ∧ " +
						"edge_class_target(edge_class_identity(x)) = x",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]()
					vertex := b.Assume()
					degenerate := b.TermAs[A]("X.s(0, 0, x)")
					b.Show(
						"the degenerate edge at x is an edge from x to x, so its class is a morphism from x to x",
						Simp(Fwd(edgeClassIdentityDef)),
						By(classMorphism.At(degenerate), degenerateEdgeEnds.At(x), vertex))
				}))
			composites := a.Have(
				"composable morphisms compose to a morphism from the first source to the second target",
				Statement{
					Binders: "∀F G:set(A).",
					Hypotheses: []string{
						"F ∈ homotopy_category_morphisms",
						"G ∈ homotopy_category_morphisms",
						"edge_class_target(F) = edge_class_source(G)",
					},
					Conclusion: "edge_class_compose(G, F) ∈ homotopy_category_morphisms ∧ " +
						"edge_class_source(edge_class_compose(G, F)) = edge_class_source(F) ∧ " +
						"edge_class_target(edge_class_compose(G, F)) = edge_class_target(G)",
				},
				Derive(func(b *Argument) {
					F, G := b.FixAs[Set[A]](), b.FixAs[Set[A]]()
					given := b.Conjuncts(
						b.Assume(),
						"F is a morphism",
						"so is G",
						"and G follows F")
					fMorphism, gMorphism, follows := given[0], given[1], given[2]
					f, fRepresents := b.ObtainAs[A](
						"F is the class of an edge f, with its ends",
						"∃f:A. "+
							"    f ∈ X.simplices(1) ∧ "+
							"    F = equivalence_class(edge_homotopic, f) ∧ "+
							"    edge_class_source(F) = X.d(1, 1, f) ∧ "+
							"    edge_class_target(F) = X.d(1, 0, f)",
						By(edgeOf.At(F), fMorphism))
					fParts := b.Conjuncts(
						fRepresents,
						"f is an edge",
						"whose class is F",
						"F starts where f does",
						"and ends where f does")
					fEdge, fClass, fSource, fTarget := fParts[0], fParts[1], fParts[2], fParts[3]
					g, gRepresents := b.ObtainAs[A](
						"G is the class of an edge g, with its ends",
						"∃g:A. "+
							"    g ∈ X.simplices(1) ∧ "+
							"    G = equivalence_class(edge_homotopic, g) ∧ "+
							"    edge_class_source(G) = X.d(1, 1, g) ∧ "+
							"    edge_class_target(G) = X.d(1, 0, g)",
						By(edgeOf.At(G), gMorphism))
					gParts := b.Conjuncts(
						gRepresents,
						"g is an edge",
						"whose class is G",
						"G starts where g does",
						"and ends where g does")
					gEdge, gClass, gSource, gTarget := gParts[0], gParts[1], gParts[2], gParts[3]
					composable := b.Have(
						"f ends at the target of F, the source of G, where g starts",
						"X.d(1, 0, f) = X.d(1, 1, g)",
						By(Normalized, fTarget, follows, gSource))
					w, composite := b.ObtainAs[A](
						"composable edges have a composite 2-simplex w",
						"∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 2, w) = f ∧ X.d(2, 0, w) = g",
						By(CompositeExists.Read(quasi).At(f, g), fEdge, gEdge, composable))
					middle := b.TermAs[A]("X.d(2, 1, w)")
					class := b.Have(
						"G after F is the class of the middle face of w",
						"edge_class_compose(G, F) = equivalence_class(edge_homotopic, X.d(2, 1, w))",
						By(ComposeClass.Read(quasi).At(f, g, w), fEdge, fClass, gEdge, gClass, composable, composite))
					b.Show(
						"so G after F, the class of the middle face of w, an edge from "+
							"the source of f to the target of g, is a morphism with those ends",
						class.Rw(),
						By(classMorphism.At(middle), faceEnds.At(w), composite, fSource, gTarget))
				}))
			leftUnit := a.Have(
				"the identity at the target is a left unit: the last degeneracy "+
					"of an edge composes it with the degenerate edge there",
				Statement{
					Binders: "∀F:set(A).",
					Hypotheses: []string{
						"F ∈ homotopy_category_morphisms",
					},
					Conclusion: "edge_class_compose(edge_class_identity(edge_class_target(F)), F) = F",
				},
				Derive(func(b *Argument) {
					F := b.FixAs[Set[A]]()
					morphism := b.Assume()
					f, represents := b.ObtainAs[A](
						"F is the class of an edge f, with its ends",
						"∃f:A. "+
							"    f ∈ X.simplices(1) ∧ "+
							"    F = equivalence_class(edge_homotopic, f) ∧ "+
							"    edge_class_source(F) = X.d(1, 1, f) ∧ "+
							"    edge_class_target(F) = X.d(1, 0, f)",
						By(edgeOf.At(F), morphism))
					parts := b.Conjuncts(
						represents,
						"f is an edge",
						"whose class is F",
						"F starts where f does",
						"and ends where f does")
					edge, class, target := parts[0], parts[1], parts[3]
					targetVertex, degenerate, degeneracy :=
						b.TermAs[A]("X.d(1, 0, f)"), b.TermAs[A]("X.s(0, 0, X.d(1, 0, f))"), b.TermAs[A]("X.s(1, 1, f)")
					vertex := b.Have(
						"a face of an edge, a vertex",
						"X.d(1, 0, f) ∈ X.simplices(0)",
						By(faceIn.At(zero, zero, f), edge))
					faces := b.Have(
						"the last degeneracy of f is a 2-simplex with f as its "+
							"faces 1 and 2 and the degenerate edge as its face 0",
						"X.s(1, 1, f) ∈ X.simplices(2) ∧ "+
							"X.d(2, 0, X.s(1, 1, f)) = X.s(0, 0, X.d(1, 0, f)) ∧ "+
							"X.d(2, 1, X.s(1, 1, f)) = f ∧ "+
							"X.d(2, 2, X.s(1, 1, f)) = f",
						By(edge, simplicial_set.EdgeLastDegeneracyFaces.Read(simplicial).At(f)))
					unit := b.Have(
						"s(1, 1, f) composes f with the degenerate edge at its target, "+
							"with middle face f: the composite class is the class of f",
						"edge_class_compose(equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 0, f))), "+
							"    equivalence_class(edge_homotopic, f)) = "+
							"equivalence_class(edge_homotopic, f)",
						By(
							ComposeClass.Read(quasi).At(f, degenerate, degeneracy),
							edge,
							degenerateEdgeEnds.At(targetVertex),
							vertex,
							faces))
					b.Show(
						"the identity at the target of F is the class of the degenerate edge there",
						By(target, unit, class, edgeClassIdentityDef))
				}))
			rightUnit := a.Have(
				"and the identity at the source a right unit: the first "+
					"degeneracy of an edge composes the degenerate edge there with it",
				Statement{
					Binders: "∀F:set(A).",
					Hypotheses: []string{
						"F ∈ homotopy_category_morphisms",
					},
					Conclusion: "edge_class_compose(F, edge_class_identity(edge_class_source(F))) = F",
				},
				Derive(func(b *Argument) {
					F := b.FixAs[Set[A]]()
					morphism := b.Assume()
					f, represents := b.ObtainAs[A](
						"F is the class of an edge f, with its ends",
						"∃f:A. "+
							"    f ∈ X.simplices(1) ∧ "+
							"    F = equivalence_class(edge_homotopic, f) ∧ "+
							"    edge_class_source(F) = X.d(1, 1, f) ∧ "+
							"    edge_class_target(F) = X.d(1, 0, f)",
						By(edgeOf.At(F), morphism))
					parts := b.Conjuncts(
						represents,
						"f is an edge",
						"whose class is F",
						"F starts where f does",
						"and ends where f does")
					edge, class, source := parts[0], parts[1], parts[2]
					sourceVertex, degenerate, degeneracy :=
						b.TermAs[A]("X.d(1, 1, f)"), b.TermAs[A]("X.s(0, 0, X.d(1, 1, f))"), b.TermAs[A]("X.s(1, 0, f)")
					vertex := b.Have(
						"a face of an edge, a vertex",
						"X.d(1, 1, f) ∈ X.simplices(0)",
						By(faceIn.At(zero, one, f), edge))
					faces := b.Have(
						"the first degeneracy of f is a 2-simplex with f as "+
							"its faces 0 and 1 and the degenerate edge as its face 2",
						"X.s(1, 0, f) ∈ X.simplices(2) ∧ "+
							"X.d(2, 0, X.s(1, 0, f)) = f ∧ "+
							"X.d(2, 1, X.s(1, 0, f)) = f ∧ "+
							"X.d(2, 2, X.s(1, 0, f)) = X.s(0, 0, X.d(1, 1, f))",
						By(edge, simplicial_set.EdgeFirstDegeneracyFaces.Read(simplicial).At(f)))
					unit := b.Have(
						"s(1, 0, f) composes the degenerate edge at the source of f with "+
							"f, with middle face f: the composite class is the class of f",
						"edge_class_compose(equivalence_class(edge_homotopic, f), "+
							"    equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 1, f)))) = "+
							"equivalence_class(edge_homotopic, f)",
						By(
							ComposeClass.Read(quasi).At(degenerate, f, degeneracy),
							degenerateEdgeEnds.At(sourceVertex),
							vertex,
							edge,
							faces))
					b.Show(
						"the identity at the source of F is the class of the degenerate edge there",
						By(source, unit, class, edgeClassIdentityDef))
				}))
			assoc := a.Have(
				"composition associates: composite 2-simplices of three composable edges form an inner horn Λ³₂",
				Statement{
					Binders: "∀F G H:set(A).",
					Hypotheses: []string{
						"F ∈ homotopy_category_morphisms",
						"G ∈ homotopy_category_morphisms",
						"H ∈ homotopy_category_morphisms",
						"edge_class_target(F) = edge_class_source(G)",
						"edge_class_target(G) = edge_class_source(H)",
					},
					Conclusion: "edge_class_compose(H, edge_class_compose(G, F)) = " +
						"edge_class_compose(edge_class_compose(H, G), F)",
				},
				Derive(func(b *Argument) {
					F, G, H := b.FixAs[Set[A]](), b.FixAs[Set[A]](), b.FixAs[Set[A]]()
					given := b.Conjuncts(
						b.Assume(),
						"F is a morphism",
						"so is G",
						"and H",
						"G follows F",
						"and H follows G")
					fMorphism, gMorphism, hMorphism, gFollows, hFollows :=
						given[0], given[1], given[2], given[3], given[4]
					f, fRepresents := b.ObtainAs[A](
						"F is the class of an edge f, with its ends",
						"∃f:A. "+
							"    f ∈ X.simplices(1) ∧ "+
							"    F = equivalence_class(edge_homotopic, f) ∧ "+
							"    edge_class_source(F) = X.d(1, 1, f) ∧ "+
							"    edge_class_target(F) = X.d(1, 0, f)",
						By(edgeOf.At(F), fMorphism))
					fParts := b.Conjuncts(
						fRepresents,
						"f is an edge",
						"whose class is F",
						"F starts where f does",
						"and ends where f does")
					fEdge, fClass, fTarget := fParts[0], fParts[1], fParts[3]
					g, gRepresents := b.ObtainAs[A](
						"G is the class of an edge g, with its ends",
						"∃g:A. "+
							"    g ∈ X.simplices(1) ∧ "+
							"    G = equivalence_class(edge_homotopic, g) ∧ "+
							"    edge_class_source(G) = X.d(1, 1, g) ∧ "+
							"    edge_class_target(G) = X.d(1, 0, g)",
						By(edgeOf.At(G), gMorphism))
					gParts := b.Conjuncts(
						gRepresents,
						"g is an edge",
						"whose class is G",
						"G starts where g does",
						"and ends where g does")
					gEdge, gClass, gSource, gTarget := gParts[0], gParts[1], gParts[2], gParts[3]
					k, kRepresents := b.ObtainAs[A](
						"H is the class of an edge k, with its ends",
						"∃k:A. "+
							"    k ∈ X.simplices(1) ∧ "+
							"    H = equivalence_class(edge_homotopic, k) ∧ "+
							"    edge_class_source(H) = X.d(1, 1, k) ∧ "+
							"    edge_class_target(H) = X.d(1, 0, k)",
						By(edgeOf.At(H), hMorphism))
					kParts := b.Conjuncts(
						kRepresents,
						"k is an edge",
						"whose class is H",
						"H starts where k does",
						"and ends where k does")
					kEdge, kClass, kSource := kParts[0], kParts[1], kParts[2]
					fg := b.Have(
						"f ends at the target of F, the source of G, where g starts",
						"X.d(1, 0, f) = X.d(1, 1, g)",
						By(Normalized, fTarget, gFollows, gSource))
					gk := b.Have(
						"and g ends where k starts",
						"X.d(1, 0, g) = X.d(1, 1, k)",
						By(Normalized, gTarget, hFollows, kSource))

					// The composite 2-simplices u of f and g and v of g and k,
					// and w of the middle face g∘f of u and k.
					u, uFaces := b.ObtainAs[A](
						"a composite 2-simplex u of f and g",
						"∃u:A. u ∈ X.simplices(2) ∧ X.d(2, 2, u) = f ∧ X.d(2, 0, u) = g",
						By(CompositeExists.Read(quasi).At(f, g), fEdge, gEdge, fg))
					uParts := b.Conjuncts(
						uFaces,
						"u is a 2-simplex",
						"with f as its face 2",
						"and g as its face 0")
					uSimplex, uFirst := uParts[0], uParts[2]
					v, vFaces := b.ObtainAs[A](
						"one v of g and k",
						"∃v:A. v ∈ X.simplices(2) ∧ X.d(2, 2, v) = g ∧ X.d(2, 0, v) = k",
						By(CompositeExists.Read(quasi).At(g, k), gEdge, kEdge, gk))
					vParts := b.Conjuncts(
						vFaces,
						"v is a 2-simplex",
						"with g as its face 2",
						"and k as its face 0")
					vSimplex, vLast := vParts[0], vParts[1]
					gAfterF, kAfterG := b.TermAs[A]("X.d(2, 1, u)"), b.TermAs[A]("X.d(2, 1, v)")
					gAfterFEdge := b.Have(
						"the middle face g∘f of u is an edge",
						"X.d(2, 1, u) ∈ X.simplices(1)",
						By(faceEnds.At(u), uSimplex))
					gAfterFTarget := b.Have(
						"faces 0 and 1 of u share a vertex: g∘f ends where g does",
						"X.d(1, 0, X.d(2, 1, u)) = X.d(1, 0, g)",
						By(faceEnds.At(u), uSimplex, uFirst))
					w, wFaces := b.ObtainAs[A](
						"so g∘f and k compose, by a 2-simplex w",
						"∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 2, w) = X.d(2, 1, u) ∧ X.d(2, 0, w) = k",
						By(CompositeExists.Read(quasi).At(gAfterF, k), gAfterFEdge, kEdge, gAfterFTarget, gk))
					kAfterGSource := b.Have(
						"faces 1 and 2 of v share a vertex: its middle face k∘g starts where g does",
						"X.d(1, 1, X.d(2, 1, v)) = X.d(1, 1, g)",
						By(Normalized, faceEnds.At(v), vSimplex, vLast))

					// u, w and v meet as the faces 3, 1 and 0 of a 3-simplex: the
					// inner horn Λ³₂ fills, and its fourth face z composes f and k∘g
					// with the middle face of w.
					z, zFaces := b.ObtainAs[A](
						"the inner horn on u, w and v fills, with fourth face z",
						"∃z:A. "+
							"    z ∈ X.simplices(2) ∧ "+
							"    X.d(2, 2, z) = X.d(2, 2, u) ∧ "+
							"    X.d(2, 1, z) = X.d(2, 1, w) ∧ "+
							"    X.d(2, 0, z) = X.d(2, 1, v)",
						By(ThreeHornFillTwo.Read(quasi).At(u, w, v), uFaces, wFaces, vFaces))
					b.Show(
						"both bracketings are the class of the middle face of w",
						CalcEq(
							Leg(
								b.TermAs[Set[A]]("edge_class_compose(H, equivalence_class(edge_homotopic, X.d(2, 1, u)))"),
								"G after F is the class of g∘f, by u",
								By(ComposeClass.Read(quasi).At(f, g, u), fEdge, fClass, gEdge, gClass, fg, uFaces)),
							Leg(
								b.TermAs[Set[A]]("equivalence_class(edge_homotopic, X.d(2, 1, w))"),
								"H after that is the class of the middle face of w",
								By(
									ComposeClass.Read(quasi).At(gAfterF, k, w),
									gAfterFEdge,
									kEdge,
									kClass,
									gAfterFTarget,
									gk,
									wFaces)),
							Leg(
								b.TermAs[Set[A]]("edge_class_compose(equivalence_class(edge_homotopic, X.d(2, 1, v)), F)"),
								"which z, a composite of f and k∘g, has as its middle face",
								By(
									ComposeClass.Read(quasi).At(f, kAfterG, z),
									fEdge,
									fClass,
									faceEnds.At(v),
									vSimplex,
									fg,
									kAfterGSource,
									uFaces,
									zFaces)),
							FinalLeg(
								"and H after G is the class of k∘g, by v",
								By(ComposeClass.Read(quasi).At(g, k, v), gEdge, gClass, kEdge, kClass, gk, vFaces)),
						))
				}))

			a.Do(Simp(Fwd(HomotopyCategoryDef)), Simp(Fwd(category.Category)))
			a.Show(
				"so the vertices and the classes of edges form a category: the record's "+
					"parts are the maps above, and its six clauses are the six facts",
				By(ends, identities, composites, leftUnit, rightUnit, assoc))
		}),
})}

// NerveEdgeHomotopicEq — f is homotopic to an edge g of a category
// nerve exactly when f = g: the homotopy triangle's degenerate side is
// an identity, so its composite is the other side by the left-unit law.
var NerveEdgeHomotopicEq = nerveEdgeHomotopicEqThm{family.Add(registry.ProofEntry{
	Name: "NerveEdgeHomotopicEq",
	Key:  "prop_23fcc59894695417",
	Build: family.Theorem(Statement{
		Binders: "∀C:category(A, M). ∀f g:(num → M).",
		Hypotheses: []string{
			"g ∈ nerve_simplices(C, 1)",
		},
		Conclusion: "edge_homotopic(nerve(C), f, g) ⇔ f = g",
	}, func(a *Argument, cat Fact, f, g Term, gEdge Fact) {
		C := a.Term("C")
		zero, one, two := a.TermAs[Nat]("0"), a.TermAs[Nat]("1"), a.TermAs[Nat]("2")
		a.Iff()
		a.Forward(
			"the identity side of the homotopy triangle makes its other sides equal",
			func(b *Argument, homotopic Fact) {
				h, triangle := b.Unpack(b.Unfolded(homotopic, EdgeHomotopicDef), "h")
				faces := b.Conjuncts(
					triangle,
					"h is a nerve triangle",
					"its last face is f",
					"its middle face is g",
					"its first face is degenerate")
				inNerve, last, middle, first := faces[0], faces[1], faces[2], faces[3]
				clauses := b.Conjuncts(
					b.Have(
						"h is a chain of two composable arrows with identity padding",
						"(∀i:num. i ≤ 2 ⇒ h(i) ∈ C.morphisms) ∧ "+
							"(∀i:num. i < 2 ⇒ C.target(h(i)) = C.source(h(i + 1))) ∧ "+
							"(∃x:A. x ∈ C.objects ∧ h(2) = C.identity(x)) ∧ "+
							"(∀i:num. 2 < i ⇒ h(i) = h(2))",
						BySets(b.Simplified(inNerve, Fwd(nerve.NerveSimplicesDef)))),
					"its arrows are morphisms",
					"successive arrows compose",
					"it ends with an identity",
					"and is constant beyond the endpoint")
				morphisms, composable, ending, constant := clauses[0], clauses[1], clauses[2], clauses[3]
				x, endpoint := b.UnpackAs[A](ending, "x")
				middleEnd := b.Have(
					"the middle face keeps the triangle's endpoint",
					"g(1) = h(2)",
					ByArith(middle, At(nerve.NerveFaceDef, C, two, one, h, one)))
				degenerate := b.Have(
					"the first face is the degenerate edge at the endpoint of g",
					"h(1) = C.identity(C.source(g(1)))",
					ByArith(
						first,
						At(nerve.NerveFaceDef, C, two, zero, h, zero),
						At(nerve.NerveDegeneracyDef, C, zero, b.Term("nerve_face(C, 1, 0, g)"), zero),
						At(nerve.NerveFaceDef, C, one, zero, g, zero)))
				identity := b.Have(
					"the second arrow is the identity at the triangle's endpoint",
					"h(1) = C.identity(x) ∧ C.source(h(1)) = x",
					By(Normalized, middleEnd, degenerate, endpoint, category.IdentityMorphism.Read(cat).AsFact().At(x)))
				unit := b.Have(
					"the first arrow composed with that identity is itself",
					"C.compose(h(1), h(0)) = h(0)",
					Derive(func(c *Argument) {
						firstArrow := c.Conjuncts(
							c.Have(
								"the first arrow is a morphism ending at x",
								"h(0) ∈ C.morphisms ∧ C.target(h(0)) = x",
								ByArith(composable.At(zero), morphisms.At(zero), identity)),
							"the first arrow is a morphism",
							"its target is x")
						c.Show(
							"composition with the identity at its target fixes the first arrow",
							Simp(Fwd(identity), Rev(firstArrow[1])),
							By(category.LeftUnit.Read(cat), firstArrow[0]))
					}))

				b.Do(Funext())
				b.FixAs[Nat]("j")
				b.Do(Simp(Rev(last), Rev(middle), Fwd(nerve.NerveFaceDef)))
				b.Cases(b.Term("j = 0"))
				b.When(
					"at zero the first arrow equals the composite with its identity",
					func(c *Argument, atZero Fact) {
						c.Show(
							"the first arrows agree by the left-unit equation",
							ByArith(atZero, unit))
					})
				b.Otherwise(
					"past zero both faces have the same identity padding",
					func(c *Argument, positive Fact) {
						padded := c.Have(
							"the triangle has reached its constant tail",
							"h(j + 1) = h(2)",
							Derive(func(d *Argument) {
								d.Cases(d.Term("j = 1"))
								d.When(
									"the first padding position is the endpoint itself",
									func(e *Argument, atOne Fact) {
										e.Show(
											"the term at two is itself",
											atOne.Rw(),
											ByArith())
									})
								d.Otherwise(
									"later positions lie beyond the endpoint",
									func(e *Argument, later Fact) {
										beyond := e.Have(
											"the next index is beyond two",
											"2 < j + 1",
											ByArith(positive, later))
										e.Show(
											"the constant-tail clause identifies this term with the endpoint",
											By(beyond, constant.At(e.TermAs[Nat]("j + 1"))))
									})
							}))
						c.Show(
							"both faces carry the identity at x",
							ByArith(positive, padded, identity, endpoint))
					})
			})
		a.Backward(
			"equal edges are homotopic by reflexivity",
			func(b *Argument, equal Fact) {
				b.Show(
					"the common edge is homotopic to itself",
					equal.Rw(),
					By(EdgeHomotopicRefl.Read(QuasiSimplicialSet.Read(NerveQuasi.Read(cat))), gEdge))
			})
	}),
})}

// NerveHomotopyCategory — the canonical identity chains and edge classes
// give an isomorphism from a category to the homotopy category of its
// nerve: the two-arrow chain preserves composition, and homotopic nerve
// edges are equal, so the object and morphism maps are bijections.
var NerveHomotopyCategory = nerveHomotopyCategoryThm{family.Add(registry.ProofEntry{
	Name: "NerveHomotopyCategory",
	Key:  "prop_7b254c7762e3d51c",
	Build: family.Theorem(Statement{
		Binders: "∀C:category(A, M).",
		Conclusion: "∃F:functor_ops(A, M, num → M, set(num → M)). " +
			"    functor(C, homotopy_category(nerve(C)), F) ∧ " +
			"    injective_on(C.objects, F.obj) ∧ " +
			"    image(F.obj, C.objects) = nerve_simplices(C, 0) ∧ " +
			"    injective_on(C.morphisms, F.map) ∧ " +
			"    image(F.map, C.morphisms) = homotopy_category_morphisms(nerve(C))",
		Abbrev: Abbrev{
			{Name: "R", Text: "edge_homotopic(nerve(C))"},
			{Name: "V", Text: "λx:A. λj:num. C.identity(x)"},
			{Name: "E", Text: "λf:M. λj:num. COND(j = 0, f, C.identity(C.target(f)))"},
			{Name: "P", Text: "λf:M. equivalence_class(«R», «E»(f))"},
			{Name: "T", Text: "λf:M. λg:M. λj:num. COND(j = 0, f, COND(j = 1, g, C.identity(C.target(g))))"},
			{Name: "F", Text: "mk_functor(«V», «P»)"},
		},
	}, func(a *Argument, cat Fact) {
		quasi := NerveQuasi.Read(cat)
		simplicial := QuasiSimplicialSet.Read(quasi)
		vertices := a.Have(
			"identity chains are vertices",
			"∀x:A. x ∈ C.objects ⇒ «V»(x) ∈ nerve_simplices(C, 0)",
			Derive(func(b *Argument) {
				b.FixAs[A]()
				object := b.Assume()
				b.Show(
					"the vertex characterization applies to the identity chain at x",
					By(object, At(nerve.NerveVertex.Read(cat), b.Term("«V»(x)"))))
			}))
		edges := a.Have(
			"a morphism gives its canonical padded edge",
			"∀f:M. f ∈ C.morphisms ⇒ «E»(f) ∈ nerve_simplices(C, 1)",
			Derive(func(b *Argument) {
				b.Fix()
				morphism := b.Assume()
				b.Show(
					"the edge characterization applies to the padded chain of f",
					By(morphism, At(nerve.NerveEdge.Read(cat), b.Term("«E»(f)"))))
			}))
		ends := a.Have(
			"the faces of a canonical edge are the vertices at its ends",
			"∀f:M. "+
				"    nerve_face(C, 1, 1, «E»(f)) = «V»(C.source(f)) ∧ "+
				"    nerve_face(C, 1, 0, «E»(f)) = «V»(C.target(f))",
			Derive(func(b *Argument) {
				b.Fix()
				b.Do(SplitConj(
					Case(
						"the last face is the identity chain at the source",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("j")
							c.Show(
								"the last face pads with the identity at the source of f",
								Simp(Fwd(nerve.NerveFaceDef)),
								ByArith())
						})),
					Case(
						"the first face is the identity chain at the target",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("j")
							c.Show(
								"dropping f leaves its identity padding",
								Simp(Fwd(nerve.NerveFaceDef)),
								ByArith())
						})),
				))
			}))
		identities := a.Have(
			"the canonical edge of an identity is the degenerate vertex",
			"∀x:A. x ∈ C.objects ⇒ «E»(C.identity(x)) = «s»(0, 0, «V»(x))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]()
				object := b.Assume()
				b.Do(Funext())
				b.FixAs[Nat]("j")
				b.Show(
					"the source and target of the identity at x are x",
					Simp(Fwd(nerve.NerveDegeneracyDef)),
					ByArith(object, category.IdentityMorphism.Read(cat).AsFact().At(x)))
			}))

		triangle := a.Have(
			"two composable morphisms give a triangle with their composite as middle face",
			Statement{
				Binders: "∀f g:M.",
				Hypotheses: []string{
					"f ∈ C.morphisms",
					"g ∈ C.morphisms",
					"C.target(f) = C.source(g)",
				},
				Conclusion: "«T»(f, g) ∈ nerve_simplices(C, 2) ∧ " +
					"nerve_face(C, 2, 2, «T»(f, g)) = «E»(f) ∧ " +
					"nerve_face(C, 2, 0, «T»(f, g)) = «E»(g) ∧ " +
					"nerve_face(C, 2, 1, «T»(f, g)) = «E»(C.compose(g, f))",
			},
			Derive(func(b *Argument) {
				f, g := b.Fix(), b.Fix()
				given := b.Assume()
				b.Do(SplitConjAll(
					Case(
						"the two-arrow chain is a nerve triangle",
						Derive(func(c *Argument) {
							padding := c.Have(
								"the identity at the target of g is a morphism from that object to itself",
								"C.target(g) ∈ C.objects ∧ "+
									"C.identity(C.target(g)) ∈ C.morphisms ∧ "+
									"C.source(C.identity(C.target(g))) = C.target(g) ∧ "+
									"C.target(C.identity(C.target(g))) = C.target(g)",
								By(
									given,
									At(category.MorphismEnds.Read(cat), g),
									category.IdentityMorphism.Read(cat).AsFact().At(c.TermAs[A]("C.target(g)"))))
							clauses := c.Have(
								"the chain has two composable arrows and constant identity padding",
								"(∀i:num. i ≤ 2 ⇒ «T»(f, g, i) ∈ C.morphisms) ∧ "+
									"(∀i:num. i < 2 ⇒ C.target(«T»(f, g, i)) = C.source(«T»(f, g, i + 1))) ∧ "+
									"(∃x:A. x ∈ C.objects ∧ «T»(f, g, 2) = C.identity(x)) ∧ "+
									"(∀i:num. 2 < i ⇒ «T»(f, g, i) = «T»(f, g, 2))",
								SplitConjAll(
									Case(
										"each entry up to two is a morphism",
										Derive(func(d *Argument) {
											d.FixAs[Nat]()
											d.Assume()
											d.Cases(d.Term("i = 0"))
											d.When(
												"the first entry is f",
												func(e *Argument, atZero Fact) {
													e.Show(
														"f is a morphism",
														ByArith(atZero, given))
												})
											d.Otherwise(
												"the remaining entries are g or the terminal identity",
												func(e *Argument, notZero Fact) {
													e.Cases(e.Term("i = 1"))
													e.When(
														"the second entry is g",
														func(h *Argument, atOne Fact) {
															h.Show(
																"g is a morphism",
																ByArith(atOne, given))
														})
													e.Otherwise(
														"the later entry is the identity",
														func(h *Argument, notOne Fact) {
															h.Show(
																"the terminal identity is a morphism",
																ByArith(notZero, notOne, padding))
														})
												})
										})),
									Case(
										"successive entries compose",
										Derive(func(d *Argument) {
											d.FixAs[Nat]()
											inside := d.Assume()
											d.Cases(d.Term("i = 0"))
											d.When(
												"f is followed by g",
												func(e *Argument, atZero Fact) {
													e.Show(
														"the given arrows are composable",
														ByArith(atZero, given))
												})
											d.Otherwise(
												"g is followed by its target identity",
												func(e *Argument, notZero Fact) {
													e.Show(
														"that identity starts at the target of g",
														ByArith(notZero, inside, padding))
												})
										})),
									Case(
										"the chain ends at the identity of the target of g",
										Derive(func(d *Argument) {
											d.Take(d.TermAs[A]("C.target(g)"))
											d.Show(
												"the entry at two is that identity",
												ByArith(padding))
										})),
									Case(
										"the chain is constant beyond two",
										Derive(func(d *Argument) {
											d.FixAs[Nat]()
											beyond := d.Assume()
											d.Show(
												"both entries are the same terminal identity",
												ByArith(beyond))
										})),
								))
							c.Show(
								"the four clauses give nerve membership",
								Simp(Fwd(nerve.NerveSimplicesDef)),
								BySets(clauses))
						})),
					Case(
						"the last face is the canonical edge of f",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("j")
							c.Do(Simp(Fwd(nerve.NerveFaceDef)))
							c.Cases(c.Term("j = 0"))
							c.When(
								"at zero the last face keeps f",
								func(d *Argument, atZero Fact) {
									d.Show(
										"both chains begin with f",
										ByArith(atZero, given))
								})
							c.Otherwise(
								"past zero it pads at the source of g",
								func(d *Argument, notZero Fact) {
									d.Show(
										"that source is the target of f",
										ByArith(notZero, given))
								})
						})),
					Case(
						"the first face is the canonical edge of g",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("j")
							c.Do(Simp(Fwd(nerve.NerveFaceDef)))
							c.Cases(c.Term("j = 0"))
							c.When(
								"at zero the shifted chain begins with g",
								func(d *Argument, atZero Fact) {
									d.Show(
										"the first entry is g",
										ByArith(atZero))
								})
							c.Otherwise(
								"past zero it has g's terminal padding",
								func(d *Argument, notZero Fact) {
									d.Show(
										"both entries are the identity at the target of g",
										ByArith(notZero))
								})
						})),
					Case(
						"the middle face is the canonical edge of the composite",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("j")
							c.Do(Simp(Fwd(nerve.NerveFaceDef)))
							c.Cases(c.Term("j = 0"))
							c.When(
								"at zero the middle face composes g after f",
								func(d *Argument, atZero Fact) {
									d.Show(
										"both chains begin with that composite",
										ByArith(atZero, given, At(category.CompositeMorphism.Read(cat), f, g)))
								})
							c.Otherwise(
								"past zero it has the composite's terminal identity",
								func(d *Argument, notZero Fact) {
									d.Show(
										"the composite ends at the target of g",
										ByArith(notZero, given, At(category.CompositeMorphism.Read(cat), f, g)))
								})
						})),
				))
			}))

		classMap := a.Have(
			"the class map takes category morphisms to morphism classes",
			"∀f:M. f ∈ C.morphisms ⇒ «P»(f) ∈ homotopy_category_morphisms(nerve(C))",
			Derive(func(b *Argument) {
				f := b.Fix()
				morphism := b.Assume()
				b.Show(
					"the class of the canonical edge is a morphism",
					By(morphism, edges.At(f), At(ClassInHomotopyCategoryMorphisms.Read(simplicial), b.Term("«E»(f)"))))
			}))
		isFunctor := a.Have(
			"the identity chains and edge classes define the canonical functor",
			"functor(C, «H», «F»)",
			Simp(Fwd(category.FunctorDef)),
			SplitConjAll(
				Case(
					"the source is the given category",
					By(cat)),
				Case(
					"the target is the nerve's homotopy category",
					By(HomotopyCategory.Read(quasi))),
				Case(
					"objects are sent to nerve vertices",
					By(vertices)),
				Case(
					"morphisms are sent to morphism classes",
					Derive(func(b *Argument) {
						f := b.Fix()
						morphism := b.Assume()
						b.Show(
							"the class map sends f to a morphism",
							By(morphism, classMap.At(f)))
					})),
				Case(
					"the class map preserves sources",
					Derive(func(b *Argument) {
						f := b.Fix()
						morphism := b.Assume()
						b.Show(
							"the source of the edge class is the edge's last face",
							By(morphism, edges.At(f), ends.At(f), At(EdgeClassMorphism.Read(simplicial), b.Term("«E»(f)"))))
					})),
				Case(
					"the class map preserves targets",
					Derive(func(b *Argument) {
						f := b.Fix()
						morphism := b.Assume()
						b.Show(
							"the target of the edge class is the edge's first face",
							By(morphism, edges.At(f), ends.At(f), At(EdgeClassMorphism.Read(simplicial), b.Term("«E»(f)"))))
					})),
				Case(
					"identities are sent to identities",
					Derive(func(b *Argument) {
						x := b.FixAs[A]()
						object := b.Assume()
						b.Show(
							"the identity class is the class of the degenerate vertex",
							Simp(Fwd(edgeClassIdentityDef)),
							By(object, identities.At(x)))
					})),
				Case(
					"composition is preserved by the two-arrow triangle",
					Derive(func(b *Argument) {
						f, g := b.Fix(), b.Fix()
						given := b.Assume()
						junction := b.Have(
							"the canonical edges meet at their common vertex",
							"nerve_face(C, 1, 0, «E»(f)) = nerve_face(C, 1, 1, «E»(g))",
							By(given, ends.At(f), ends.At(g)))
						b.Show(
							"the composite of the two classes is the class of the triangle's middle face",
							By(
								given,
								edges.At(f),
								edges.At(g),
								triangle.At(f, g),
								junction,
								At(ComposeClass.Read(quasi), b.Term("«E»(f)"), b.Term("«E»(g)"), b.Term("«T»(f, g)"))))
					})),
			))

		objectInjective := a.Have(
			"the object map is injective",
			"injective_on(C.objects, «V»)",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				x, y := b.FixAs[A](), b.FixAs[A]()
				given := b.Assume()
				b.Show(
					"equal constant identity chains have equal identity sources",
					By(
						given,
						category.IdentityMorphism.Read(cat).AsFact().At(x),
						category.IdentityMorphism.Read(cat).AsFact().At(y)))
			}))
		objectImage := a.Have(
			"every nerve vertex is an identity chain",
			"image(«V», C.objects) = nerve_simplices(C, 0)",
			BySets(nerve.NerveVertex.Read(cat)))
		morphismInjective := a.Have(
			"the morphism class map is injective",
			"injective_on(C.morphisms, «P»)",
			Simp(Fwd(functions.InjectiveOnDef)),
			Derive(func(b *Argument) {
				x, y := b.Fix(), b.Fix()
				given := b.Assume()
				homotopic := b.Have(
					"equal edge classes have homotopic canonical edges",
					"«R»(«E»(x), «E»(y))",
					By(given, edges.At(x), edges.At(y), EdgeClassEqIff.Read(quasi)))
				equal := b.Have(
					"homotopic nerve edges are equal",
					"«E»(x) = «E»(y)",
					By(given, edges.At(y), homotopic, NerveEdgeHomotopicEq.Read(cat)))
				b.Show(
					"the equal chains have the same first arrow",
					By(equal))
			}))
		morphismImage := a.Have(
			"every morphism class is the image of a category morphism",
			"image(«P», C.morphisms) = homotopy_category_morphisms(nerve(C))",
			Derive(func(b *Argument) {
				onto := b.Have(
					"a representative edge supplies an underlying category morphism",
					"∀Z:set(num → M). Z ∈ homotopy_category_morphisms(nerve(C)) ⇒ ∃f:M. f ∈ C.morphisms ∧ Z = «P»(f)",
					Derive(func(c *Argument) {
						Z := c.Fix()
						morphism := c.Assume()
						e, represents := c.Obtain(
							"Z is the class of an edge",
							"∃e:(num → M). e ∈ nerve_simplices(C, 1) ∧ Z = equivalence_class(«R», e)",
							By(morphism, At(InHomotopyCategoryMorphisms.Read(simplicial), Z)))
						f, canonical := c.Obtain(
							"that edge is the canonical edge of a category morphism",
							"∃f:M. f ∈ C.morphisms ∧ e = «E»(f)",
							By(represents, At(nerve.NerveEdge.Read(cat), e)))
						c.Take(f)
						c.Show(
							"the class of this canonical edge is Z",
							By(represents, canonical))
					}))
				b.Show(
					"the image has exactly the homotopy category's morphisms",
					BySets(onto, classMap))
			}))

		a.Take(a.Term("«F»"))
		a.Show(
			"the canonical functor is a bijection on objects and on morphisms",
			By(isFunctor, objectInjective, objectImage, morphismInjective, morphismImage))
	}),
})}

// ---------------------------------------------------------------------------
// The homotopy category and the nerve
// ---------------------------------------------------------------------------

// homotopyNerveAdjunctDef — `homotopy_nerve_adjunct(X, F)`: the map
// from X to the nerve of C a functor from the homotopy category gives,
// an n-simplex sent to the images of the classes of its spine edges.
var homotopyNerveAdjunctDef = homotopyNerveAdjunctDefThm{family.Define(registry.DefEntry{
	Name:  "homotopyNerveAdjunctDef",
	Key:   "prop_e6113b2b5bdf0976",
	Const: "homotopy_nerve_adjunct",
	Type:  "simplicial_ops(A) → functor_ops(A, set(A), B, N) → num → A → num → N",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀F:functor_ops(A, set(A), B, N). " +
			"    homotopy_nerve_adjunct(X, F) = " +
			"    λn:num. " +
			"        normalize_on(X.simplices(n), " +
			"            junk, " +
			"            λx:A. λj:num. " +
			"                F.map(equivalence_class(edge_homotopic(X), spine_map(X.d, X.s, n, x, j))))",
	},
	Deps: []registry.EntryLike{EdgeHomotopicDef},
})}

// HomotopyNerveAdjunction — h ⊣ N on quasi-categories: the functors
// from the homotopy category of X to a category C are the simplicial
// maps from X to the nerve of C.
var HomotopyNerveAdjunction = homotopyNerveAdjunctionThm{family.Add(registry.ProofEntry{
	Name: "HomotopyNerveAdjunction",
	Key:  "prop_8673d7710172aaaf",
	Deps: []registry.EntryLike{
		homotopyNerveAdjunctDef,
		nerve.NerveMapCriterion,
		ComposeClass,
		EdgeClassMorphism,
		EdgeClassEqIff,
		HomotopyCategory,
		HomotopyCategoryDef,
		category.FunctorSetDef,
		simplicial_set.SimplicialMapSetDef,
	},
	Build: family.Card(QuasiCategory.Statement(Statement{
		Binders: "∀C:category_ops(B, N).",
		Hypotheses: []string{
			"category(C)",
		},
		Conclusion: "injective_on(functor_set(homotopy_category(X), C), homotopy_nerve_adjunct(X)) ∧ " +
			"image(homotopy_nerve_adjunct(X), functor_set(homotopy_category(X), C)) = " +
			"simplicial_map_set(X, nerve(C))",
	}),
		"a functor F gives a map of vertices and edges, e sent to F of its class, which keeps the "+
			"ends and the degenerate edges and sends a 2-simplex to a commuting triangle, the class of "+
			"the middle face being the composite of the classes (ComposeClass); NerveMapCriterion extends "+
			"it to the adjunct. A simplicial map into the nerve sends homotopic edges to equal morphisms, "+
			"the homotopy 2-simplex going to a triangle with an identity edge, so its values on edges "+
			"define a functor on the classes, whose adjunct it is by the uniqueness half of the criterion"),
})}
