// segal.go — Segal's characterization of the nerves of categories among
// the simplicial sets, read through the spines of simplicial_set. A
// simplicial set with unique inner fillers is a category on its vertices and
// edges, composing through the unique filler of Λ²₁; its spine map
// commutes with the faces and the degeneracies, is one-to-one, and is
// onto the nerve of that category, so it is an isomorphism. The nerve
// of a category has unique inner fillers, so a simplicial set has unique
// inner fillers exactly when it is isomorphic to the nerve of a
// category.

package segal

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/nerve"
	"github.com/euc-ai/xugo/library/proofs/simplicial/quasi_category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Unique inner fillers: the category of vertices and edges
// ---------------------------------------------------------------------------

// SegalCompositeMiddleFace — with unique inner fillers the middle face
// of a 2-simplex is the Segal composite of its other two faces. The
// faces of w other than the middle one form an inner horn Λ²₁,
// compatible as the faces of a simplex are, and w fills it; so does the
// 2-simplex segal_composite chooses, which exists since w has the faces
// 2 and 0 it asks for. The horn has one filler, so the two are equal and
// so are their middle faces.
var SegalCompositeMiddleFace = segalCompositeMiddleFaceThm{family.Add(registry.ProofEntry{
	Name: "SegalCompositeMiddleFace",
	Key:  "prop_367ac70ae12da5b8",
	Build: nerve.InnerHornUnique.Law(Statement{
		Binders: "∀w:A.",
		Hypotheses: []string{
			"w ∈ X.simplices(2)",
		},
		Conclusion: "X.d(2, 1, w) = segal_composite(X.d(2, 0, w), X.d(2, 2, w))",
		Abbrev: Abbrev{
			{Name: "choice", Text: "∃v:A. " +
				"    v ∈ X.simplices(2) ∧ X.d(2, 2, v) = X.d(2, 2, w) ∧ X.d(2, 0, v) = X.d(2, 0, w)"},
		},
	},
		func(a *Argument, X *Expr[simplicial_set.SimplicialOps[A]], unique Fact, w *Expr[A], simplex Fact) {
			d := a.TermAs[Fun3[Nat, Nat, A, A]]("X.d")
			simplicial := nerve.UniqueInnerSimplicialSet.Read(unique)
			one := a.TermAs[Nat]("1")

			// y: the horn Λ²₁ of the faces of w other than the middle one.
			y, yDef := a.LetAs[Fun[Nat, A]]("y", "λi:num. X.d(2, i, w)")
			edges := a.Have(
				"the faces of w other than the middle one are edges",
				"∀i:num. i ∈ horn_faces(1, 1) ⇒ y(i) ∈ X.simplices(1)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					index := b.Assume()
					b.Show(
						"a face of a 2-simplex, at most 2, is an edge",
						yDef.Rw(),
						By(
							simplicial_set.FaceIn.Read(simplicial).At(one, i, w),
							index,
							kan_complex.HornFacesMember.At(one, one, i),
							simplex))
				}))
			compatible := a.Have(
				"they meet at their common vertex, as the faces of a simplex do",
				"faces_compatible(1, horn_faces(1, 1), y)",
				yDef.Rw(),
				By(kan_complex.FacesCompatible.Read(simplicial).At(one, one, w), simplex))
			horn := a.Have(
				"so y is a horn of X, a face family on the faces of Λ²₁",
				"face_family(1, horn_faces(1, 1), y)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(edges, compatible))
			z, filler := a.ObtainAs[A](
				"so the horn y has exactly one filler z",
				"∃z:A. "+
					"    z ∈ X.simplices(2) ∧ "+
					"    faces_filler(1, horn_faces(1, 1), y, z) ∧ "+
					"    (∀v:A. v ∈ X.simplices(2) ∧ faces_filler(1, horn_faces(1, 1), y, v) ⇒ v = z)",
				By(nerve.UniqueInnerFill.Read(unique).At(one, one, y), horn))
			only := a.Conjuncts(
				filler,
				"z is a 2-simplex",
				"filling the horn",
				"and every 2-simplex filling it is z")[2]
			wFills := a.Have(
				"w fills the horn of its own faces",
				"faces_filler(1, horn_faces(1, 1), y, w)",
				yDef.Rw(),
				By(kan_complex.SimplexFillsOwnHorn.At(d, one, one, w)))
			fills := a.Have(
				"and so does any v with the faces 0 and 2 of w",
				Statement{
					Binders: "∀v:A.",
					Hypotheses: []string{
						"X.d(2, 0, v) = X.d(2, 0, w)",
						"X.d(2, 2, v) = X.d(2, 2, w)",
					},
					Conclusion: "faces_filler(1, horn_faces(1, 1), y, v)",
				},
				Derive(func(b *Argument) {
					b.FixAs[A]()
					outer := b.Assume()
					b.Do(yDef.Rw(), Simp(Fwd(simplicial_set.FacesFillerDef)))
					i := b.FixAs[Nat]("i")
					index := b.Have(
						"a face i of the horn is at most 2 and not 1",
						"i ≤ 2 ∧ ¬(i = 1)",
						By(b.Assume(), kan_complex.HornFacesMember.At(one, one, i)))
					b.Cases(b.Term("i = 0"))
					b.When(
						"at the face 0 the two agree",
						func(c *Argument, isZero Fact) {
							c.Show(
								"v has the face 0 of w",
								ByArith(isZero, outer))
						})
					b.Otherwise(
						"and the only other face of the horn is the face 2",
						func(c *Argument, notZero Fact) {
							isTwo := c.Have(
								"the index, at most 2 and neither 0 nor 1, is 2",
								"i = 2",
								ByArith(notZero, index))
							c.Show(
								"v has the face 2 of w",
								ByArith(isTwo, outer))
						})
				}))

			possible := a.Have(
				"w is a 2-simplex with the faces 2 and 0 the composite asks for",
				"«choice»",
				Derive(func(b *Argument) {
					b.Take(w)
					b.Show(
						"w itself",
						By(simplex))
				}))
			chosen, chosenFaces := a.ObtainChosen(
				"so the chosen 2-simplex has them too",
				"«choice»",
				possible)
			same := a.Have(
				"the chosen 2-simplex and w both fill the horn, so both are z",
				MakeProp(Equal(chosen, w)),
				CalcEq(
					Leg(
						z,
						"the chosen 2-simplex, with the faces 0 and 2 of w, fills the horn",
						By(only.At(chosen), chosenFaces, fills.At(chosen))),
					FinalLeg(
						"and so does w",
						By(only.At(w), simplex, wFills)),
				))
			a.Show(
				"so the composite, the middle face of the chosen 2-simplex, is that of w",
				Simp(Fwd(quasi_category.SegalCompositeDef)),
				same.Rw(),
				Basic())
		}),
})}

// SegalCategoryDef — `segal_category(X)`: the record of the
// category of vertices and edges of X — the source and the target of an
// edge its last and 0-th faces, the identity at a vertex its degenerate
// edge, composition the Segal composite.
var SegalCategoryDef = segalCategoryDefThm{family.Define(registry.DefEntry{
	Name:  "SegalCategoryDef",
	Key:   "prop_91d16a3a21ac3b56",
	Const: "segal_category",
	Type:  "simplicial_ops(A) → category_ops(A, A)",
	Equations: []string{
		"∀X:simplicial_ops(A). " +
			"    segal_category(X) = " +
			"    mk_category(X.simplices(0), " +
			"        X.simplices(1), " +
			"        λe:A. X.d(1, 1, e), " +
			"        λe:A. X.d(1, 0, e), " +
			"        λv:A. X.s(0, 0, v), " +
			"        segal_composite)",
	},
})}

// SegalCategory — a simplicial set with unique inner fillers is a
// category on its vertices and edges. The ends of an edge are its faces
// 1 and 0, the identity at a vertex is its degenerate edge
// (simplicial_set.VertexDegeneracyFaces), and g after f is the middle
// face of any 2-simplex with f and g as its faces 2 and 0
// (SegalCompositeMiddleFace), an edge from the source of f to the
// target of g (simplicial_set.TwoSimplexFaceEnds); composable edges are
// such faces, of a filler of the horn Λ²₁ they form
// (quasi_category.CompositeExists, X being a quasi-category by
// UniqueInnerQuasi). The unit laws read the degeneracies of an edge as
// such 2-simplices. For associativity the 2-simplices u of f and g, v of
// g and h, and w of f and h∘g meet as the faces 3, 0 and 2 of a
// 3-simplex: the inner horn Λ³₁ they form fills
// (quasi_category.ThreeHornFillOne), and the face 1 of the filler has h
// and g∘f as its faces 0 and 2 and the middle face of w as its own; so
// h∘(g∘f) is the middle face of w, (h∘g)∘f. Uniqueness enters only
// through SegalCompositeMiddleFace.
var SegalCategory = segalCategoryThm{family.Add(registry.ProofEntry{
	Name: "SegalCategory",
	Key:  "prop_9eb8726887cfb81",
	Build: nerve.InnerHornUnique.Law("category(segal_category(X))",
		func(a *Argument, unique Fact) {
			zero, one := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
			simplicial := nerve.UniqueInnerSimplicialSet.Read(unique)
			quasi := quasi_category.UniqueInnerQuasi.Read(unique)
			faceIn := simplicial_set.FaceIn.Read(simplicial)
			faceEnds := simplicial_set.TwoSimplexFaceEnds.Read(simplicial)
			middle := SegalCompositeMiddleFace.Read(unique)
			spans := quasi_category.CompositeExists.Read(quasi)

			// The clauses of a category, in the order the definition states them.
			ends := a.Have(
				"the ends of an edge, its faces 1 and 0, are vertices",
				"∀f:A. f ∈ X.simplices(1) ⇒ X.d(1, 1, f) ∈ X.simplices(0) ∧ X.d(1, 0, f) ∈ X.simplices(0)",
				Derive(func(b *Argument) {
					f := b.FixAs[A]()
					edge := b.Assume()
					b.Show(
						"faces of an edge are vertices",
						By(edge, faceIn.At(zero, one, f), faceIn.At(zero, zero, f)))
				}))
			// The identity at a vertex is its degenerate edge.
			identities := simplicial_set.VertexDegeneracyFaces.Read(simplicial)
			composites := a.Have(
				"composable edges compose to an edge from the source of the first to the target of the second",
				Statement{
					Binders: "∀f g:A.",
					Hypotheses: []string{
						"f ∈ X.simplices(1)",
						"g ∈ X.simplices(1)",
						"X.d(1, 0, f) = X.d(1, 1, g)",
					},
					Conclusion: "segal_composite(g, f) ∈ X.simplices(1) ∧ " +
						"X.d(1, 1, segal_composite(g, f)) = X.d(1, 1, f) ∧ " +
						"X.d(1, 0, segal_composite(g, f)) = X.d(1, 0, g)",
				},
				Derive(func(b *Argument) {
					f, g := b.FixAs[A](), b.FixAs[A]()
					composable := b.Assume()
					w, wFaces := b.ObtainAs[A](
						"f and g are the faces 2 and 0 of a 2-simplex w, a filler of the horn they form",
						"∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 2, w) = f ∧ X.d(2, 0, w) = g",
						By(spans.At(f, g), composable))
					composite := b.Have(
						"g after f is the middle face of w",
						"segal_composite(g, f) = X.d(2, 1, w)",
						By(Normalized, middle.At(w), wFaces))
					b.Show(
						"so g after f, the middle face of w, is an edge from the "+
							"source of its face 2, f, to the target of its face 0, g",
						By(Normalized, composite, wFaces, faceEnds.At(w)))
				}))
			leftUnit := a.Have(
				"the identity at the target is a left unit: the last "+
					"degeneracy of an edge f has f as its faces 1 and 2",
				"∀f:A. f ∈ X.simplices(1) ⇒ segal_composite(X.s(0, 0, X.d(1, 0, f)), f) = f",
				Derive(func(b *Argument) {
					f := b.FixAs[A]()
					edge := b.Assume()
					b.Show(
						"so the composite of f and the identity is the middle face f",
						By(
							Normalized,
							edge,
							simplicial_set.EdgeLastDegeneracyFaces.Read(simplicial).At(f),
							middle.At(b.TermAs[A]("X.s(1, 1, f)"))))
				}))
			rightUnit := a.Have(
				"and the identity at the source a right unit: the first degeneracy of f has f as its faces 0 and 1",
				"∀f:A. f ∈ X.simplices(1) ⇒ segal_composite(f, X.s(0, 0, X.d(1, 1, f))) = f",
				Derive(func(b *Argument) {
					f := b.FixAs[A]()
					edge := b.Assume()
					b.Show(
						"so the composite of the identity and f is the middle face f",
						By(
							edge,
							simplicial_set.EdgeFirstDegeneracyFaces.Read(simplicial).At(f),
							middle.At(b.TermAs[A]("X.s(1, 0, f)"))))
				}))
			assoc := a.Have(
				"composition associates: both bracketings are the middle face of one 2-simplex",
				Statement{
					Binders: "∀f g h:A.",
					Hypotheses: []string{
						"f ∈ X.simplices(1)",
						"g ∈ X.simplices(1)",
						"h ∈ X.simplices(1)",
						"X.d(1, 0, f) = X.d(1, 1, g)",
						"X.d(1, 0, g) = X.d(1, 1, h)",
					},
					Conclusion: "segal_composite(h, segal_composite(g, f)) = segal_composite(segal_composite(h, g), f)",
				},
				Derive(func(b *Argument) {
					f, g, h := b.FixAs[A](), b.FixAs[A](), b.FixAs[A]()
					given := b.Conjuncts(
						b.Assume(),
						"f is an edge",
						"so is g",
						"and h",
						"g follows f",
						"and h follows g")
					fEdge, gEdge, hEdge, gFollowsF, hFollowsG := given[0], given[1], given[2], given[3], given[4]

					u, uFaces := b.ObtainAs[A](
						"a 2-simplex u with f and g as its faces 2 and 0",
						"∃u:A. u ∈ X.simplices(2) ∧ X.d(2, 2, u) = f ∧ X.d(2, 0, u) = g",
						By(spans.At(f, g), fEdge, gEdge, gFollowsF))
					v, vFaces := b.ObtainAs[A](
						"one v with g and h as its faces 2 and 0",
						"∃v:A. v ∈ X.simplices(2) ∧ X.d(2, 2, v) = g ∧ X.d(2, 0, v) = h",
						By(spans.At(g, h), gEdge, hEdge, hFollowsG))
					hAfterG := b.TermAs[A]("X.d(2, 1, v)")
					hAfterGEdge := b.Have(
						"the middle face h∘g of v is an edge",
						"X.d(2, 1, v) ∈ X.simplices(1)",
						By(faceEnds.At(v), vFaces))
					hAfterGSource := b.Have(
						"and starts where its face 2, g, does: at the target of f",
						"X.d(1, 0, f) = X.d(1, 1, X.d(2, 1, v))",
						By(Normalized, faceEnds.At(v), vFaces, gFollowsF))
					w, wFaces := b.ObtainAs[A](
						"and one w with f and h∘g as its faces 2 and 0",
						"∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 2, w) = f ∧ X.d(2, 0, w) = X.d(2, 1, v)",
						By(spans.At(f, hAfterG), fEdge, hAfterGEdge, hAfterGSource))

					t, tFaces := b.ObtainAs[A](
						"u, w and v, placed as the faces 3, 2 and 0 of a 3-simplex, have its face 1, a 2-simplex t",
						"∃t:A. "+
							"    t ∈ X.simplices(2) ∧ "+
							"    X.d(2, 2, t) = X.d(2, 1, u) ∧ "+
							"    X.d(2, 1, t) = X.d(2, 1, w) ∧ "+
							"    X.d(2, 0, t) = X.d(2, 0, v)",
						By(quasi_category.ThreeHornFillOne.Read(quasi).At(u, w, v), uFaces, vFaces, wFaces))
					tMiddle := b.Conjuncts(
						tFaces,
						"t is a 2-simplex",
						"with g∘f as its face 2",
						"the middle face of w as its middle face",
						"and h as its face 0")[2]
					b.Show(
						"both bracketings are the middle face of w",
						CalcEq(
							Leg(
								b.TermAs[A]("segal_composite(h, X.d(2, 1, u))"),
								"g after f is the middle face of u",
								By(Normalized, middle.At(u), uFaces)),
							Leg(
								b.TermAs[A]("X.d(2, 1, t)"),
								"h after that is the middle face of t",
								By(middle.At(t), tFaces, vFaces)),
							Leg(
								b.TermAs[A]("X.d(2, 1, w)"),
								"which is the middle face of w",
								By(tMiddle)),
							Leg(
								b.TermAs[A]("segal_composite(X.d(2, 1, v), f)"),
								"the composite of f and h∘g, by w",
								By(Normalized, middle.At(w), wFaces)),
							FinalLeg(
								"and h∘g is the composite of g and h, by v",
								By(Normalized, middle.At(v), vFaces)),
						))
				}))

			a.Do(Simp(Fwd(SegalCategoryDef)), Simp(Fwd(category.Category)))
			a.Show(
				"so the vertices and edges form a category: the record's parts "+
					"are the maps above, and its six clauses are the six facts",
				By(ends, identities, composites, leftUnit, rightUnit, assoc))
		}),
})}

// ---------------------------------------------------------------------------
// The spine map, and Segal's characterization
// ---------------------------------------------------------------------------

// SpineMapIn — the spine of an n-simplex is a chain of n composable
// edges: the spine map lands in the nerve of the category of vertices
// and edges. Membership in category_nerve reads the ends, the identities
// and the edges, never the composition, so no filler condition is
// needed. The four clauses of the nerve are checked at the chain one by
// one: its terms below n are spine edges and those from n on the
// degenerate edge at the last vertex, an edge starting there
// (simplicial_set.VertexDegeneracyFaces); consecutive spine edges share
// a vertex, and the last spine edge ends at the last vertex, the source
// of the degenerate edge that follows it.
var SpineMapIn = spineMapInThm{family.Add(registry.ProofEntry{
	Name: "SpineMapIn",
	Key:  "prop_68e11e0d1802f93f",
	Build: simplicial_set.SimplicialSet.Law(Statement{
		Binders: "∀n:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
		},
		Conclusion: "spine_map(n, x) ∈ nerve_simplices(segal_category(X), n)",
	},
		func(
			a *Argument,
			X *Expr[simplicial_set.SimplicialOps[A]],
			simplicial Fact,
			n *Expr[Nat],
			x *Expr[A],
			member Fact,
		) {
			d := a.TermAs[Fun3[Nat, Nat, A, A]]("X.d")
			s := a.TermAs[Fun3[Nat, Nat, A, A]]("X.s")
			degenerateEdgeEnds := simplicial_set.VertexDegeneracyFaces.Read(simplicial)
			lastVertex := a.TermAs[A]("face_iterate_bottom(n, n, x)")
			vertex := a.Have(
				"the last vertex of x is a vertex",
				"face_iterate_bottom(n, n, x) ∈ X.simplices(0)",
				ByArith(member, simplicial_set.FaceIterateBottomIn.Read(simplicial).At(n, n, x)))
			lastStep := a.Have(
				"the last spine edge of an (m + 1)-simplex ends at its "+
					"last vertex, the source of the degenerate edge there",
				Statement{
					Binders: "∀m:num. ∀y:A.",
					Hypotheses: []string{
						"y ∈ X.simplices(m + 1)",
					},
					Conclusion: "X.d(1, 0, spine_map(m + 1, y, m)) = X.d(1, 1, spine_map(m + 1, y, m + 1))",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Nat]()
					y := b.FixAs[A]()
					simplex := b.Assume()
					next := b.TermAs[Nat]("m + 1")
					yLastVertex := b.TermAs[A]("face_iterate_bottom(m + 1, m + 1, y)")
					guards := b.Have(
						"the m-th term is a spine edge and the next one is not",
						"m < m + 1 ∧ ¬(m + 1 < m + 1)",
						ByArith())
					indices := b.Have(
						"the last spine edge removes no top vertex, and its last bottom face acts on a 1-simplex",
						"suc(m) - 1 - m = 0 ∧ suc(m) - m = 1",
						ByArith())
					target := b.Have(
						"the last spine edge is y with its bottom m vertices removed, and its 0-th face removes one more",
						"X.d(1, 0, simplex_spine(m + 1, y, m)) = face_iterate_bottom(m + 1, m + 1, y)",
						Simp(
							Fwd(simplicial_set.SimplexSpineDef),
							Rev(nat_arith.Add1),
							Fwd(simplicial_set.FaceIterateBottomDef)),
						By(Normalized, indices, simplicial_set.FaceIterateTopDef))
					source := b.Have(
						"the last vertex is the source of its degenerate edge",
						"X.d(1, 1, X.s(0, 0, face_iterate_bottom(m + 1, m + 1, y))) = face_iterate_bottom(m + 1, m + 1, y)",
						ByArith(
							simplex,
							simplicial_set.FaceIterateBottomIn.Read(simplicial).At(next, next, y),
							degenerateEdgeEnds.At(yLastVertex)))
					b.Show(
						"the m-th term is the last spine edge and the next one the degenerate edge at its target",
						By(
							target,
							source,
							guards,
							simplicial_set.SpineMapDef.At(d, s, next, y, m),
							simplicial_set.SpineMapDef.At(d, s, next, y, next)))
				}))
			edges := a.Have(
				"its terms up to n are edges",
				"∀i:num. i ≤ n ⇒ spine_map(n, x, i) ∈ X.simplices(1)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					b.Assume()
					b.Cases(b.Term("i < n"))
					b.When(
						"below n the term is the i-th spine edge",
						func(c *Argument, below Fact) {
							c.Show(
								"a spine edge is an edge",
								By(
									Normalized,
									below,
									member,
									simplicial_set.SpineMapDef.At(d, s, n, x, i),
									simplicial_set.SpineIn.Read(simplicial).At(n, i, x)))
						})
					b.Otherwise(
						"at n the term is the degenerate edge at the last vertex",
						func(c *Argument, past Fact) {
							c.Show(
								"the degenerate edge at a vertex is an edge",
								ByArith(
									past,
									vertex,
									simplicial_set.SpineMapDef.At(d, s, n, x, i),
									degenerateEdgeEnds.At(lastVertex)))
						})
				}))
			composable := a.Have(
				"consecutive terms below n are composable",
				"∀i:num. i < n ⇒ X.d(1, 0, spine_map(n, x, i)) = X.d(1, 1, spine_map(n, x, i + 1))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					below := b.Assume()
					next := b.TermAs[Nat]("i + 1")
					b.Cases(b.Term("i + 1 < n"))
					b.When(
						"two consecutive spine edges share a vertex",
						func(c *Argument, inner Fact) {
							c.Show(
								"the target of the i-th spine edge is the source of the next",
								By(
									below,
									inner,
									member,
									simplicial_set.SpineMapDef.At(d, s, n, x, i),
									simplicial_set.SpineMapDef.At(d, s, n, x, next),
									simplicial_set.SpineEnds.Read(simplicial).At(n, i, x)))
						})
					b.Otherwise(
						"the i-th spine edge is the last one",
						func(c *Argument, outer Fact) {
							lastIndex := c.Have(
								"so n is i + 1",
								"n = i + 1",
								ByArith(below, outer))
							c.Show(
								"it ends at the last vertex, where the degenerate edge starts",
								ByArith(lastIndex, member, lastStep.At(i, x)))
						})
				}))
			end := a.Have(
				"its n-th term is the degenerate edge at a vertex",
				"∃v:A. v ∈ X.simplices(0) ∧ spine_map(n, x, n) = X.s(0, 0, v)",
				Derive(func(b *Argument) {
					b.Take(lastVertex)
					b.Show(
						"take the last vertex of x: the n-th term is its degenerate edge",
						ByArith(vertex, simplicial_set.SpineMapDef.At(d, s, n, x, n)))
				}))
			padded := a.Have(
				"and it is constant from n on",
				"∀i:num. n < i ⇒ spine_map(n, x, i) = spine_map(n, x, n)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					beyond := b.Assume()
					b.Show(
						"past n every term is the degenerate edge at the last vertex",
						ByArith(
							beyond,
							simplicial_set.SpineMapDef.At(d, s, n, x, i),
							simplicial_set.SpineMapDef.At(d, s, n, x, n)))
				}))
			a.Show(
				"so the spine is a chain of the nerve",
				Simp(Fwd(nerve.NerveSimplicesDef)),
				BySets(edges, composable, end, padded))
		}),
})}

// FaceSpineComposite — at the vertex a face deletes, its spine edge is
// the composite of the two spine edges of x meeting there. The vertices
// j, j + 1, j + 2 of x span a 2-simplex t whose faces 0 and 2 are the
// spine edges j + 1 and j of x, and whose face 1, by the face identities
// iterated, is the spine edge j of the face j + 1 of x; with unique inner
// fillers the face 1 of a 2-simplex is the composite of the other two
// (SegalCompositeMiddleFace).
var FaceSpineComposite = faceSpineCompositeThm{family.Add(registry.ProofEntry{
	Name: "FaceSpineComposite",
	Key:  "prop_171131643dfec208",
	Build: nerve.InnerHornUnique.Law(Statement{
		Binders: "∀n j:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"j < n",
		},
		Conclusion: "simplex_spine(n, X.d(n + 1, j + 1, x), j) = " +
			"segal_composite(simplex_spine(n + 1, x, j + 1), simplex_spine(n + 1, x, j))",
	},
		func(a *Argument, unique Fact, n, j *Expr[Nat], x *Expr[A], given Fact) {
			simplicial := nerve.UniqueInnerSimplicialSet.Read(unique)
			parts := a.Conjuncts(
				given,
				"x is an (n + 1)-simplex",
				"and j is a spine index of the face")
			simplex, inside := parts[0], parts[1]
			// q: the number of vertices of x past the vertex j + 2.
			q, qDef := a.LetAs[Nat]("q", "n - 1 - j")
			next, top := a.TermAs[Nat]("j + 1"), a.TermAs[Nat]("j + 1 + 1")
			y := a.TermAs[A]("face_iterate_top(n + 1, q, x)")
			dimension := a.Have(
				"x with its top q vertices removed has dimension j + 2",
				"n + 1 - q = j + 1 + 1",
				ByArith(qDef, inside))
			ranges := a.Have(
				"q is at most n + 1, j at most j + 2, and j + 1 + q at most n",
				"q ≤ n + 1 ∧ j ≤ j + 1 + 1 ∧ j + 1 + q ≤ n",
				ByArith(qDef, inside))
			yIn := a.Have(
				"which is a (j + 2)-simplex",
				"face_iterate_top(n + 1, q, x) ∈ X.simplices(j + 1 + 1)",
				By(
					simplicial_set.FaceIterateTopIn.Read(simplicial).At(a.TermAs[Nat]("n + 1"), q, x),
					simplex,
					ranges,
					dimension))

			// t: x restricted to its vertices j, j + 1, j + 2.
			t, tDef := a.LetAs[A]("t", "face_iterate_bottom(j + 1 + 1, j, face_iterate_top(n + 1, q, x))")
			tIn := a.Have(
				"t is a 2-simplex",
				"t ∈ X.simplices(2)",
				ByArith(simplicial_set.FaceIterateBottomIn.Read(simplicial).At(top, j, y), yIn, ranges, tDef))
			first := a.Have(
				"the face 0 of t is the spine edge j + 1 of x",
				"simplex_spine(n + 1, x, j + 1) = X.d(2, 0, t)",
				Derive(func(b *Argument) {
					count := b.Have(
						"the spine edge j + 1 of x removes its top q vertices",
						"n + 1 - 1 - (j + 1) = q",
						ByArith(qDef, inside))
					bottom := b.Have(
						"and then its bottom j + 1, the 0-th face after the bottom j",
						"face_iterate_bottom(j + 1 + 1, j + 1, face_iterate_top(n + 1, q, x)) = "+
							"X.d(j + 1 + 1 - j, 0, face_iterate_bottom(j + 1 + 1, j, face_iterate_top(n + 1, q, x)))",
						Simp(Rev(nat_arith.Add1), Fwd(simplicial_set.FaceIterateBottomDef)),
						Basic())
					two := b.Have(
						"what is left of the bottom j has dimension 2",
						"j + 1 + 1 - j = 2",
						ByArith())
					b.Show(
						"the 0-th face of t",
						Simp(Fwd(simplicial_set.SimplexSpineDef)),
						count.Rw(),
						By(bottom, two, tDef))
				}))
			last := a.Have(
				"the face 2 of t is the spine edge j of x",
				"simplex_spine(n + 1, x, j) = X.d(2, 2, t)",
				Derive(func(b *Argument) {
					count := b.Have(
						"the spine edge j of x removes its top q + 1 vertices",
						"n + 1 - 1 - j = q + 1",
						ByArith(qDef, inside))
					topStep := b.Have(
						"which is one last face past the top q",
						"face_iterate_top(n + 1, q + 1, x) = X.d(n + 1 - q, n + 1 - q, face_iterate_top(n + 1, q, x))",
						Simp(Rev(nat_arith.Add1), Fwd(simplicial_set.FaceIterateTopDef)),
						Basic())
					b.Show(
						"the last face commutes with the removal of the bottom j, as the face 2",
						Simp(Fwd(simplicial_set.SimplexSpineDef)),
						count.Rw(),
						topStep.Rw(),
						dimension.Rw(),
						ByArith(
							simplicial_set.FaceIterateBottomFace.Read(simplicial).At(next, j, top, y),
							yIn,
							ranges,
							tDef))
				}))
			middle := a.Have(
				"the face 1 of t is the spine edge j of the face j + 1 of x",
				"simplex_spine(n, X.d(n + 1, j + 1, x), j) = X.d(2, 1, t)",
				Derive(func(b *Argument) {
					commuted := b.Have(
						"the face j + 1 commutes with the removal of the top q vertices",
						"face_iterate_top(n, q, X.d(n + 1, j + 1, x)) = "+
							"X.d(n + 1 - q, j + 1, face_iterate_top(n + 1, q, x))",
						ByArith(simplicial_set.FaceIterateTopFace.Read(simplicial).At(n, q, next, x), simplex, ranges))
					b.Show(
						"and with the removal of the bottom j, as the face 1",
						Simp(Fwd(simplicial_set.SimplexSpineDef)),
						qDef.RwRev(),
						commuted.Rw(),
						dimension.Rw(),
						ByArith(
							simplicial_set.FaceIterateBottomFace.Read(simplicial).At(next, j, next, y),
							yIn,
							ranges,
							tDef))
				}))
			a.Show(
				"the face 1 of the 2-simplex t is the composite of its faces 0 and 2",
				middle.Rw(),
				first.Rw(),
				last.Rw(),
				By(SegalCompositeMiddleFace.Read(unique).At(t), tIn))
		}),
})}

// SpineMapFace — the spine map commutes with the faces: the spine of a
// face of x is that face of the spine of x. Index by index: below the
// deleted vertex the spine edges of the face are those of x, past it
// those of x one index up, and at it the edge of an inner face is the
// composite of the two edges of x meeting there; past its last spine
// edge the face is padded at its last vertex, which is the last vertex
// of x, or for the last face the source of the last spine edge of x.
var SpineMapFace = spineMapFaceThm{family.Add(registry.ProofEntry{
	Name: "SpineMapFace",
	Key:  "prop_60bd22c5e9b7fa1e",
	Build: nerve.InnerHornUnique.Law(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n + 1)",
			"i ≤ n + 1",
		},
		Conclusion: "spine_map(n, X.d(n + 1, i, x)) = " +
			"nerve_face(segal_category(X), n + 1, i, spine_map(n + 1, x))",
	},
		func(a *Argument, unique Fact, n, i *Expr[Nat], x *Expr[A], given Fact) {
			simplicial := nerve.UniqueInnerSimplicialSet.Read(unique)
			parts := a.Conjuncts(
				given,
				"x is an (n + 1)-simplex",
				"and i indexes one of its faces")
			simplex, face := parts[0], parts[1]
			a.Show(
				"index by index, the spine of the face against the face of the spine",
				Funext(),
				Simp(Fwd(simplicial_set.SpineMapDef), Fwd(nerve.NerveFaceDef)),
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]("j")
					b.Cases(b.Term("j + 1 < i"))
					b.When(
						"below the deleted vertex the spine edges of the face are those of x",
						func(c *Argument, below Fact) {
							edge := c.Have(
								"the spine edge j of the face is that of x",
								"simplex_spine(n, X.d(n + 1, i, x), j) = simplex_spine(n + 1, x, j)",
								ByArith(simplicial_set.FaceSpineBelow.Read(simplicial).At(n, i, j, x), simplex, below, face))
							c.Show(
								"both sides read it",
								edge.Rw(),
								ByArith(below, face))
						})
					b.Otherwise(
						"at or past the deleted vertex",
						func(c *Argument, notBelow Fact) {
							c.Cases(c.Term("i = n + 1"))
							c.When(
								"past the last spine edge the last face is padded at the source of the last edge of x",
								func(e *Argument, last Fact) {
									top := e.TermAs[Nat]("n + 1")
									vertex := e.Have(
										"the last vertex of the last face is the source of the last spine edge of x",
										"face_iterate_bottom(n, n, X.d(n + 1, i, x)) = X.d(1, 1, simplex_spine(n + 1, x, n))",
										Derive(func(g *Argument) {
											none := g.Have(
												"the last spine edge of x removes no top vertex",
												"n + 1 - 1 - n = 0",
												ByArith())
											g.Show(
												"the last face passes the removal of the bottom n, as the face 1",
												Simp(Fwd(simplicial_set.SimplexSpineDef)),
												none.Rw(),
												Simp(Fwd(simplicial_set.FaceIterateTopDef)),
												ByArith(simplicial_set.FaceIterateBottomFace.Read(simplicial).At(n, n, top, x), simplex, last))
										}))
									e.Show(
										"both sides are the degenerate edge there",
										vertex.Rw(),
										ByArith(notBelow, last))
								})
							c.Otherwise(
								"an inner face or the 0-th",
								func(e *Argument, notLast Fact) {
									e.Cases(e.Term("j + 1 = i"))
									e.When(
										"at the deleted vertex an inner face composes the two edges of x meeting there",
										func(g *Argument, at Fact) {
											inside := g.Have(
												"the vertex j + 1 is inner, so j < n",
												"j < n",
												ByArith(at, face, notLast))
											composite := g.Have(
												"the spine edge j of the face is the composite of the edges j and j + 1 of x",
												"simplex_spine(n, X.d(n + 1, j + 1, x), j) = "+
													"segal_composite(simplex_spine(n + 1, x, j + 1), simplex_spine(n + 1, x, j))",
												By(FaceSpineComposite.Read(unique).At(n, j, x), simplex, inside))
											g.Show(
												"both sides are that composite",
												at.RwRev(),
												composite.Rw(),
												ByArith(inside))
										})
									e.Otherwise(
										"past the deleted vertex",
										func(g *Argument, past Fact) {
											g.Cases(g.Term("j < n"))
											g.When(
												"the spine edges of the face are those of x one index up",
												func(h *Argument, inside Fact) {
													edge := h.Have(
														"the spine edge j of the face is the edge j + 1 of x",
														"simplex_spine(n, X.d(n + 1, i, x), j) = simplex_spine(n + 1, x, j + 1)",
														ByArith(
															simplicial_set.FaceSpineAbove.Read(simplicial).At(n, i, j, x),
															simplex,
															notBelow,
															past,
															inside))
													h.Show(
														"both sides read it",
														edge.Rw(),
														ByArith(notBelow, past, inside, face, notLast))
												})
											g.Otherwise(
												"past the last spine edge both are padded at the last vertex of x",
												func(h *Argument, outside Fact) {
													vertex := h.Have(
														"the face keeps the last vertex of x",
														"face_iterate_bottom(n, n, X.d(n + 1, i, x)) = face_iterate_bottom(n + 1, n + 1, x)",
														ByArith(
															simplicial_set.FaceIterateBottomBelow.Read(simplicial).At(n, n, i, x),
															simplex,
															face,
															notLast))
													h.Show(
														"both sides are the degenerate edge there",
														vertex.Rw(),
														ByArith(notBelow, past, outside, face, notLast))
												})
										})
								})
						})
				}))
		}),
})}

// SpineMapDegeneracy — the spine map commutes with the degeneracies: a
// degeneracy repeats a vertex, which inserts its degenerate edge into
// the spine.
var SpineMapDegeneracy = spineMapDegeneracyThm{family.Add(registry.ProofEntry{
	Name: "SpineMapDegeneracy",
	Key:  "prop_e786e7d4cde39412",
	Deps: []registry.EntryLike{
		simplicial_set.DegeneracyIn,
		simplicial_set.SpineMapDef,
		nerve.NerveDegeneracyDef,
		simplicial_set.SimplexSpineDef,
		simplicial_set.FaceIterateTopDef,
		simplicial_set.FaceIterateBottomDef,
		simplicial_set.FaceIterateTopIn,
		simplicial_set.FaceIterateBottomIn,
		simplicial_set.FaceDegeneracyBelow,
		simplicial_set.FaceDegeneracyEqual,
		simplicial_set.FaceDegeneracyNext,
		simplicial_set.FaceDegeneracyAbove,
		simplicial_set.VertexDegeneracyFaces,
	},
	Build: family.Card(simplicial_set.SimplicialSet.Statement(Statement{
		Binders: "∀n i:num. ∀x:A.",
		Hypotheses: []string{
			"x ∈ X.simplices(n)",
			"i ≤ n",
		},
		Conclusion: "spine_map(n + 1, X.s(n, i, x)) = " +
			"nerve_degeneracy(segal_category(X), i, spine_map(n, x))",
	}),
		"extensionality at j and cases on j against i, the positions the COND of nerve_degeneracy reads. "+
			"The i-th degeneracy of x repeats its vertex i: its spine edges below i are those of x, its i-th "+
			"spine edge is the degenerate edge s(0, 0, ·) at the vertex i, the source of the i-th spine edge "+
			"of x (or the last vertex itself when i = n), and its edges above i are those of x shifted by "+
			"one; the padding is the degenerate edge at the last vertex of both. Each identification moves "+
			"the iterated faces of simplex_spine past the degeneracy by induction on the iterations, as "+
			"FaceIterateTopFace moves them past a face: a last face passes it by FaceDegeneracyAbove and a "+
			"0-th face by FaceDegeneracyBelow, which lowers its index by one, until an iteration reaches the "+
			"repeated vertex, where FaceDegeneracyNext (a last face) or FaceDegeneracyEqual (a 0-th face) "+
			"cancels it, the simplices along the way lying in their dimensions by FaceIterateTopIn and "+
			"FaceIterateBottomIn; the source of a degenerate edge is its vertex (VertexDegeneracyFaces)"),
})}

// SpineMapInjective — with unique inner fillers a simplex is determined
// by its spine.
var SpineMapInjective = spineMapInjectiveThm{family.Add(registry.ProofEntry{
	Name: "SpineMapInjective",
	Key:  "prop_2d8ff34452d051c8",
	Deps: []registry.EntryLike{
		functions.InjectiveOnDef,
		nerve.UniqueInnerSimplicialSet,
		nerve.UniqueInnerFill,
		SpineMapFace,
		simplicial_set.SpineMapDef,
		kan_complex.FacesCompatible,
		kan_complex.SimplexFillsOwnHorn,
		simplicial_set.FaceFamilyDef,
		simplicial_set.FacesFillerDef,
		kan_complex.HornFacesMember,
		simplicial_set.FaceIn,
		simplicial_set.VertexDegeneracyFaces,
	},
	Build: family.Card(
		nerve.InnerHornUnique.Statement("∀n:num. injective_on(X.simplices(n), spine_map(n))"),
		"by induction on n: a vertex is the source of its degenerate edge (VertexDegeneracyFaces) and "+
			"an edge is its own spine; an (m + 2)-simplex x is the unique filler of the inner horn of its "+
			"faces other than the face 1 (UniqueInnerFill at m + 1 and k = 1: the horn is a face family "+
			"on horn_faces(m + 1, 1) (FaceFamilyDef), its members (m + 1)-simplices by FaceIn and "+
			"compatible by FacesCompatible, and x fills it by SimplexFillsOwnHorn), and each face of x is "+
			"an (m + 1)-simplex (FaceIn) whose spine is nerve_face of the spine of x (SpineMapFace); so "+
			"two simplices with one spine have the same faces by the induction hypothesis, both fill that "+
			"horn (FacesFillerDef, read at each face of the horn through HornFacesMember), and are equal"),
})}

// SpineMapOnto — with unique inner fillers every chain of composable
// edges is the spine of a simplex.
var SpineMapOnto = spineMapOntoThm{family.Add(registry.ProofEntry{
	Name: "SpineMapOnto",
	Key:  "prop_7bd4f4d42338c6bb",
	Deps: []registry.EntryLike{
		nerve.NerveSimplicesDef,
		nerve.UniqueInnerFill,
		SegalCategory,
		nerve.NerveFaceIn,
		nerve.NerveFaceFace,
		nerve.NerveOuterFacesDetermine,
		SpineMapFace,
		SpineMapInjective,
		simplicial_set.SpineMapDef,
		simplicial_set.FaceFamilyDef,
		simplicial_set.FacesCompatibleDef,
		simplicial_set.FacesFillerDef,
		kan_complex.HornFacesMember,
		simplicial_set.FaceIn,
		simplicial_set.VertexDegeneracyFaces,
	},
	Build: family.Card(nerve.InnerHornUnique.Statement(Statement{
		Binders: "∀n:num. ∀f:(num → A).",
		Hypotheses: []string{
			"f ∈ nerve_simplices(segal_category(X), n)",
		},
		Conclusion: "∃x:A. x ∈ X.simplices(n) ∧ spine_map(n, x) = f",
	}),
		"by induction on n: a chain of length 0 is the degenerate edge at a vertex, the spine of "+
			"that vertex, and a chain of length 1 is the spine of its edge: its padding is the "+
			"degenerate edge at a vertex, the source of that degenerate edge (VertexDegeneracyFaces), "+
			"where the edge ends; for a chain f of length m + 2, each face nerve_face(m + 2, i, f) is a "+
			"chain of length m + 1 (NerveFaceIn under SegalCategory), the spine of an (m + 1)-simplex "+
			"y(i) by the induction hypothesis; the y(i) for i other than 1 are compatible "+
			"(FacesCompatibleDef), since the faces of two of them have the spines that NerveFaceFace "+
			"equates (SpineMapFace) and are equal (SpineMapInjective); so they form an inner horn of "+
			"dimension m + 2 missing the face 1, a face family on horn_faces(m + 1, 1) (FaceFamilyDef), "+
			"whose filler x (UniqueInnerFill) has spine f: by SpineMapFace the 0-th and last nerve faces "+
			"of the spine of x are the spines of its faces y(0) and y(m + 2) (FacesFillerDef, at the "+
			"faces 0 and m + 2 of the horn by HornFacesMember), which are those of f, and a sequence of "+
			"length m + 2 ≥ 2 is determined by its 0-th and last nerve faces (NerveOuterFacesDetermine)"),
})}

// SegalIsomorphism — with unique inner fillers the spine map is an
// isomorphism onto the nerve of the category of vertices and edges: a
// simplicial map into the nerve, a simplicial set (NerveSimplicialSet at
// SegalCategory), since spines are chains and the spine map commutes
// with the faces and the degeneracies, one-to-one in every dimension,
// and onto the nerve since every chain is a spine.
var SegalIsomorphism = segalIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SegalIsomorphism",
	Key:  "prop_f6fa56759facfe8f",
	Build: nerve.InnerHornUnique.Law("simplicial_isomorphism(X, nerve(segal_category(X)), spine_map)",
		func(a *Argument, X *Expr[simplicial_set.SimplicialOps[A]], unique Fact) {
			// The nerve of the category of vertices and edges, its faces and
			// degeneracies, and the spine map, as the terms the definitions of
			// simplicial_map and simplicial_isomorphism are read at.
			spine := a.TermAs[Fun3[Nat, A, Nat, A]]("spine_map")

			simplicial := nerve.UniqueInnerSimplicialSet.Read(unique)
			mapping := a.Have(
				"the spine map is a simplicial map into the nerve: spines are "+
					"chains, and it commutes with the faces and the degeneracies",
				"simplicial_map(X, nerve(segal_category(X)), spine_map)",
				By(
					simplicial,
					nerve.NerveSimplicialSet.Read(SegalCategory.Read(unique)),
					SpineMapIn.Read(simplicial),
					SpineMapFace.Read(unique),
					SpineMapDegeneracy.Read(simplicial),
					At(simplicial_set.SimplicialMap, X, a.Term("nerve(segal_category(X))"), spine)))
			onto := a.Have(
				"in every dimension the spines of the simplices are exactly the chains of the nerve",
				"∀n:num. image(spine_map(n), X.simplices(n)) = nerve_simplices(segal_category(X), n)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					spineAt := b.TermAs[Fun[A, Fun[Nat, A]]]("spine_map(n)")
					spines := b.Have(
						"a chain is the spine of an n-simplex exactly when it lies "+
							"in the nerve: every spine is a chain, every chain a spine",
						"∀f:(num → A). f ∈ image(spine_map(n), X.simplices(n)) ⇔ f ∈ nerve_simplices(segal_category(X), n)",
						b.ForEach(func(f *Expr[Fun[Nat, A]]) Action {
							// Whichever n-simplex f is the spine of, that spine is a
							// chain: SpineMapIn is cited at n alone.
							return By(
								set_basic.InImage.At(spineAt, b.TermAs[Set[A]]("X.simplices(n)"), f),
								Read(SpineMapIn, simplicial).At(n),
								SpineMapOnto.Read(unique).At(n, f))
						}))
					b.Show(
						"so the image is the nerve, by extensionality",
						By(spines, set_basic.Extension))
				}))
			a.Show(
				"a simplicial map one-to-one in every dimension and onto the nerve is an isomorphism",
				By(
					mapping,
					SpineMapInjective.Read(unique),
					onto,
					At(simplicial_set.SimplicialIsomorphismDef, X, a.Term("nerve(segal_category(X))"), spine)))
		}),
})}

// SegalCharacterization — a simplicial set has unique inner fillers
// exactly when it is isomorphic to the nerve of a category.
var SegalCharacterization = segalCharacterizationThm{family.Add(registry.ProofEntry{
	Name: "SegalCharacterization",
	Key:  "prop_964dd37e35fe6a17",
	Reading: "The categories on the right are those on the carrier type A, objects and morphisms " +
		"alike: what SegalCategory produces. A category on other types is not quantified here.",
	Deps: []registry.EntryLike{
		nerve.InnerHornUnique,
		SegalCategory,
		SegalIsomorphism,
		nerve.NerveInnerHornUnique,
		simplicial_set.IsomorphismInverse,
		simplicial_set.SimplicialIsomorphismDef,
		simplicial_set.MapIn,
		simplicial_set.MapFace,
		simplicial_set.FaceFamilyDef,
		simplicial_set.FacesCompatibleDef,
		simplicial_set.FacesFillerDef,
	},
	Build: family.Card(Statement{
		Binders: "∀X:simplicial_ops(A).",
		Hypotheses: []string{
			"simplicial_set(X)",
		},
		Conclusion: "inner_horn_unique(X) ⇔ " +
			"∃C:category_ops(A, A). ∃F:(num → A → num → A). " +
			"    category(C) ∧ simplicial_isomorphism(X, nerve(C), F)",
	},
		"⇒: the category of vertices and edges (SegalCategory) and the spine map "+
			"(SegalIsomorphism). ⇐: an isomorphism carries a horn of X to a horn of "+
			"the nerve, whose unique filler (NerveInnerHornUnique) comes back along "+
			"the inverse map (IsomorphismInverse) as the unique filler in X"),
})}
