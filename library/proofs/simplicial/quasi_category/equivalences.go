// equivalences.go — equivalences in a quasi-category. An edge is an
// equivalence when its class is an isomorphism of the homotopy category;
// a compositional equality of classes is realized by a triangle with the
// given edges, so an equivalence has an inverse edge and two inverse
// triangles. The opposite of a quasi-category is a quasi-category with
// the same equivalences.

package quasi_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// EdgeEquivalenceDef — `edge_equivalence(X, f)`: f is an edge
// whose class is an isomorphism of the homotopy category.
var EdgeEquivalenceDef = edgeEquivalenceDefThm{family.Define(registry.DefEntry{
	Name:  "EdgeEquivalenceDef",
	Key:   "prop_be3ac09d69bff463",
	Const: "edge_equivalence",
	Type:  "simplicial_ops(A) → A → bool",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀f:A. " +
			"    edge_equivalence(X, f) ⇔ " +
			"    f ∈ X.simplices(1) ∧ " +
			"    category_isomorphism(homotopy_category(X), equivalence_class(edge_homotopic(X), f))",
	},
	Deps: []registry.EntryLike{HomotopyCategoryDef, EdgeHomotopicDef},
})}

// CompositeTriangleExists — for edges f and g that meet and an edge h
// ending where g ends, the class of g after the class of f is the class of h exactly when one
// triangle has f, h and g as its faces 2, 1 and 0: the middle edge of a
// composite triangle of f and g is then homotopic to h, and filling the
// inner horn Λ³₂ on that triangle, the homotopy and the last degeneracy
// of g replaces it by h; conversely the middle edge of a triangle
// represents the composite of the classes of its outer edges.
var CompositeTriangleExists = compositeTriangleExistsThm{family.Add(registry.ProofEntry{
	Name: "CompositeTriangleExists",
	Key:  "prop_f961d91c3890c784",
	Reading: "All three edges are prescribed before choosing the triangle. " +
		"The middle face equals h as an edge, not only as a homotopy class.",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀f g h:A.",
		Hypotheses: []string{
			"f ∈ X.simplices(1)",
			"g ∈ X.simplices(1)",
			"h ∈ X.simplices(1)",
			"X.d(1, 0, f) = X.d(1, 1, g)",
			"X.d(1, 0, h) = X.d(1, 0, g)",
		},
		Conclusion: "edge_class_compose(equivalence_class(edge_homotopic, g), " +
			"    equivalence_class(edge_homotopic, f)) = " +
			"equivalence_class(edge_homotopic, h) ⇔ " +
			"∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 2, w) = f ∧ X.d(2, 0, w) = g ∧ X.d(2, 1, w) = h",
	},
		func(
			a *Argument,
			X *Expr[simplicial_set.SimplicialOps[A]],
			quasi Fact,
			f *Expr[A],
			g *Expr[A],
			h *Expr[A],
			edges Fact,
		) {
			a.Iff()
			a.Forward(
				"replace the composite edge along its homotopy to h",
				func(b *Argument, composeEq Fact) {
					u, composite := b.ObtainAs[A](
						"choose a triangle composing f and g",
						"∃u:A. u ∈ X.simplices(2) ∧ X.d(2, 2, u) = f ∧ X.d(2, 0, u) = g",
						By(edges, CompositeExists.Read(quasi).At(f, g)))
					middle := b.TermAs[A]("X.d(2, 1, u)")
					compositeClass := b.Have(
						"the class of the middle edge is the composite of the two classes",
						"edge_class_compose(equivalence_class(edge_homotopic, g), "+
							"    equivalence_class(edge_homotopic, f)) = "+
							"equivalence_class(edge_homotopic, X.d(2, 1, u))",
						By(composite, edges, ComposeClass.Read(quasi).At(f, g, u)))
					simplicial := b.Have(
						"a quasi-category is a simplicial set",
						"simplicial_set(X)",
						By(QuasiSimplicialSet.Read(quasi)))
					homotopic := b.Have(
						"the middle edge, a face of the composite triangle, has the class of h, so it is homotopic to h",
						"edge_homotopic(X.d(2, 1, u), h)",
						By(
							composeEq,
							compositeClass,
							composite,
							simplicial_set.TwoSimplexFaceEnds.Read(simplicial).At(u),
							edges,
							EdgeClassEqIff.Read(quasi).At(middle, h)))
					v, homotopy := b.ObtainAs[A](
						"choose a triangle witnessing that homotopy",
						"∃v:A. "+
							"    v ∈ X.simplices(2) ∧ "+
							"    X.d(2, 2, v) = X.d(2, 1, u) ∧ "+
							"    X.d(2, 1, v) = h ∧ "+
							"    X.d(2, 0, v) = X.s(0, 0, X.d(1, 0, h))",
						By(homotopic, At(EdgeHomotopicDef, X, middle, h)))
					degenerate := b.TermAs[A]("X.s(1, 1, g)")
					degenerateFaces := b.Have(
						"the last degeneracy of g has g as faces 1 and 2",
						"X.s(1, 1, g) ∈ X.simplices(2) ∧ "+
							"X.d(2, 0, X.s(1, 1, g)) = X.s(0, 0, X.d(1, 0, g)) ∧ "+
							"X.d(2, 1, X.s(1, 1, g)) = g ∧ "+
							"X.d(2, 2, X.s(1, 1, g)) = g",
						By(edges, simplicial_set.EdgeLastDegeneracyFaces.Read(simplicial).At(g)))
					meetMiddle := b.Have(
						"the composite triangle meets the homotopy along its middle edge",
						"X.d(2, 1, u) = X.d(2, 2, v)",
						By(homotopy))
					meetG := b.Have(
						"the composite triangle meets the degeneracy along g",
						"X.d(2, 0, u) = X.d(2, 2, X.s(1, 1, g))",
						By(Normalized, composite, degenerateFaces))
					meetTarget := b.Have(
						"the homotopy and the degeneracy meet along the degenerate edge at the common target of h and g",
						"X.d(2, 0, v) = X.d(2, 0, X.s(1, 1, g))",
						By(homotopy, degenerateFaces, edges))
					w, fourthFace := b.ObtainAs[A](
						"fill the inner horn on the composite, homotopy and degeneracy",
						"∃w:A. "+
							"    w ∈ X.simplices(2) ∧ "+
							"    X.d(2, 2, w) = X.d(2, 2, u) ∧ "+
							"    X.d(2, 1, w) = X.d(2, 1, v) ∧ "+
							"    X.d(2, 0, w) = X.d(2, 1, X.s(1, 1, g))",
						By(
							meetTarget,
							meetG,
							meetMiddle,
							composite,
							homotopy,
							degenerateFaces,
							ThreeHornFillTwo.Read(quasi).At(u, v, degenerate)))
					b.Take(w)
					b.Show(
						"its fourth face has exactly f, g and h as its edges",
						By(Normalized, composite, homotopy, fourthFace, degenerateFaces))
				})
			a.Backward(
				"a triangle identifies the composite class with the class of h",
				func(b *Argument, triangle Fact) {
					w, faces := b.UnpackAs[A](triangle)
					b.Show(
						"the class of its middle edge is the composite",
						By(faces, edges, ComposeClass.Read(quasi).At(f, g, w)))
				})
		}),
})}

// EdgeEquivalenceIffInverseTriangles — an edge f is an equivalence
// exactly when one edge g makes two triangles with it, f then g and g then
// f, whose middle edges are the degenerate edges at the source and at the
// target of f: an inverse of the class of f is the class of an edge g,
// and each inverse equation of the homotopy category is realized by a
// triangle with exactly the edges it names (CompositeTriangleExists);
// conversely the two triangles give the inverse equations on classes
// (ComposeClass), so the class of g is an inverse.
var EdgeEquivalenceIffInverseTriangles = edgeEquivalenceIffInverseTrianglesThm{family.Add(registry.ProofEntry{
	Name: "EdgeEquivalenceIffInverseTriangles",
	Key:  "prop_92d17f89715dea20",
	Reading: "The same edge g occurs in both triangles. No coherence between the two triangles " +
		"is required; their middle faces are actual degeneracies at the source and target of f.",
	Build: QuasiCategory.Law("∀f:A. "+
		"    edge_equivalence(X, f) ⇔ "+
		"    f ∈ X.simplices(1) ∧ "+
		"    (∃g a b:A. "+
		"        g ∈ X.simplices(1) ∧ "+
		"        a ∈ X.simplices(2) ∧ "+
		"        b ∈ X.simplices(2) ∧ "+
		"        X.d(2, 2, a) = f ∧ "+
		"        X.d(2, 0, a) = g ∧ "+
		"        X.d(2, 1, a) = X.s(0, 0, X.d(1, 1, f)) ∧ "+
		"        X.d(2, 2, b) = g ∧ "+
		"        X.d(2, 0, b) = f ∧ "+
		"        X.d(2, 1, b) = X.s(0, 0, X.d(1, 0, f)))",
		func(p *Argument, X *Expr[simplicial_set.SimplicialOps[A]], quasi Fact, f *Expr[A]) {
			C := p.TermAs[CategoryOps[A, Set[A]]]("homotopy_category(X)")
			F := p.TermAs[Set[A]]("equivalence_class(edge_homotopic, f)")
			p.Iff()
			p.Forward(
				"represent the inverse class by one edge and realize both inverse equations",
				func(q *Argument, equivalence Fact) {
					parts := q.Conjuncts(
						q.Unfolded(equivalence, EdgeEquivalenceDef),
						"f is an edge",
						"its class is an isomorphism")
					fEdge, isomorphism := parts[0], parts[1]
					G, inverse := q.ObtainAs[Set[A]](
						"choose the inverse morphism G of the class of f",
						"∃G:set(A). "+
							"    G ∈ homotopy_category(X).morphisms ∧ "+
							"    homotopy_category(X).source(G) = "+
							"    homotopy_category(X).target(equivalence_class(edge_homotopic, f)) ∧ "+
							"    homotopy_category(X).target(G) = "+
							"    homotopy_category(X).source(equivalence_class(edge_homotopic, f)) ∧ "+
							"    homotopy_category(X).compose(G, equivalence_class(edge_homotopic, f)) = "+
							"    homotopy_category(X).identity( "+
							"        homotopy_category(X).source(equivalence_class(edge_homotopic, f))) ∧ "+
							"    homotopy_category(X).compose(equivalence_class(edge_homotopic, f), G) = "+
							"    homotopy_category(X).identity( "+
							"        homotopy_category(X).target(equivalence_class(edge_homotopic, f)))",
						By(isomorphism, category.CategoryIsomorphismDef.At(C, F)))
					classInverse := q.Simplified(inverse, Fwd(edgeClassIdentityDef))
					simplicial := q.Have(
						"a quasi-category is a simplicial set",
						"simplicial_set(X)",
						By(QuasiSimplicialSet.Read(quasi)))
					g, represents := q.ObtainAs[A](
						"represent G by an edge g",
						"∃g:A. g ∈ X.simplices(1) ∧ G = equivalence_class(edge_homotopic, g)",
						By(classInverse, InHomotopyCategoryMorphisms.Read(simplicial).At(G)))
					fClass := q.Have(
						"the class of f has the ends of f",
						"equivalence_class(edge_homotopic, f) ∈ homotopy_category_morphisms ∧ "+
							"edge_class_source(equivalence_class(edge_homotopic, f)) = X.d(1, 1, f) ∧ "+
							"edge_class_target(equivalence_class(edge_homotopic, f)) = X.d(1, 0, f)",
						By(fEdge, EdgeClassMorphism.Read(simplicial).At(f)))
					gClass := q.Have(
						"and the class of g has the ends of g",
						"equivalence_class(edge_homotopic, g) ∈ homotopy_category_morphisms ∧ "+
							"edge_class_source(equivalence_class(edge_homotopic, g)) = X.d(1, 1, g) ∧ "+
							"edge_class_target(equivalence_class(edge_homotopic, g)) = X.d(1, 0, g)",
						By(represents, EdgeClassMorphism.Read(simplicial).At(g)))
					edgeInverse := q.Simplified(classInverse, Fwd(represents), Fwd(fClass), Fwd(gClass))
					ends := q.Have(
						"g runs from the target of f back to its source",
						"X.d(1, 1, g) = X.d(1, 0, f) ∧ X.d(1, 0, g) = X.d(1, 1, f)",
						By(edgeInverse))
					leftInverse := q.Have(
						"the class of g composed after the class of f is the identity at the source",
						"edge_class_compose(equivalence_class(edge_homotopic, g), "+
							"    equivalence_class(edge_homotopic, f)) = "+
							"equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 1, f)))",
						By(edgeInverse))
					rightInverse := q.Have(
						"the reverse composite is the identity at the target",
						"edge_class_compose(equivalence_class(edge_homotopic, f), "+
							"    equivalence_class(edge_homotopic, g)) = "+
							"equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 0, f)))",
						By(edgeInverse))

					sourceIdentity, targetIdentity :=
						q.TermAs[A]("X.s(0, 0, X.d(1, 1, f))"), q.TermAs[A]("X.s(0, 0, X.d(1, 0, f))")
					endIdentities := simplicial_set.EdgeEndIdentities.Read(simplicial).At(f)
					a, facesA := q.ObtainAs[A](
						"realize the left inverse equation by a triangle",
						"∃a:A. "+
							"    a ∈ X.simplices(2) ∧ "+
							"    X.d(2, 2, a) = f ∧ "+
							"    X.d(2, 0, a) = g ∧ "+
							"    X.d(2, 1, a) = X.s(0, 0, X.d(1, 1, f))",
						By(
							fEdge,
							represents,
							ends,
							endIdentities,
							leftInverse,
							CompositeTriangleExists.Read(quasi).At(f, g, sourceIdentity)))
					b, facesB := q.ObtainAs[A](
						"realize the right inverse equation by a second triangle with the same g",
						"∃b:A. "+
							"    b ∈ X.simplices(2) ∧ "+
							"    X.d(2, 2, b) = g ∧ "+
							"    X.d(2, 0, b) = f ∧ "+
							"    X.d(2, 1, b) = X.s(0, 0, X.d(1, 0, f))",
						By(
							fEdge,
							represents,
							ends,
							endIdentities,
							rightInverse,
							CompositeTriangleExists.Read(quasi).At(g, f, targetIdentity)))
					q.Show(
						"f is an edge and the same g occurs in both inverse triangles",
						SplitConj(
							Case(
								"f is an edge",
								By(fEdge)),
							Case(
								"g and the two triangles are the required witnesses",
								Derive(func(r *Argument) {
									r.Take(g)
									r.Take(a)
									r.Take(b)
									r.Show(
										"the two triangles have the prescribed edges",
										By(represents, facesA, facesB))
								})),
						))
				})
			p.Backward(
				"the two inverse triangles make the class of f an isomorphism",
				func(q *Argument, given Fact) {
					parts := q.Conjuncts(
						given,
						"f is an edge",
						"one edge occurs in the two inverse triangles")
					fEdge := parts[0]
					g, a, b, triangles := q.Unpack3As[A, A, A](parts[1])
					simplicial := q.Have(
						"a quasi-category is a simplicial set",
						"simplicial_set(X)",
						By(QuasiSimplicialSet.Read(quasi)))
					ends := q.Have(
						"the outer faces of the two triangles give reversed endpoints",
						"X.d(1, 0, f) = X.d(1, 1, g) ∧ X.d(1, 0, g) = X.d(1, 1, f)",
						By(
							Normalized,
							triangles,
							simplicial_set.TwoSimplexFaceEnds.Read(simplicial).At(a),
							simplicial_set.TwoSimplexFaceEnds.Read(simplicial).At(b)))
					leftInverse := q.Have(
						"the first triangle gives the left inverse equation on classes",
						"edge_class_compose(equivalence_class(edge_homotopic, g), "+
							"    equivalence_class(edge_homotopic, f)) = "+
							"equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 1, f)))",
						By(fEdge, triangles, ends, ComposeClass.Read(quasi).At(f, g, a)))
					rightInverse := q.Have(
						"the second triangle gives the right inverse equation",
						"edge_class_compose(equivalence_class(edge_homotopic, f), "+
							"    equivalence_class(edge_homotopic, g)) = "+
							"equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 0, f)))",
						By(fEdge, triangles, ends, ComposeClass.Read(quasi).At(g, f, b)))
					fClass := q.Have(
						"the class of f is a morphism with the ends of f",
						"equivalence_class(edge_homotopic, f) ∈ homotopy_category_morphisms ∧ "+
							"edge_class_source(equivalence_class(edge_homotopic, f)) = X.d(1, 1, f) ∧ "+
							"edge_class_target(equivalence_class(edge_homotopic, f)) = X.d(1, 0, f)",
						By(fEdge, EdgeClassMorphism.Read(simplicial).At(f)))
					gClass := q.Have(
						"likewise the class of g is a morphism with the ends of g",
						"equivalence_class(edge_homotopic, g) ∈ homotopy_category_morphisms ∧ "+
							"edge_class_source(equivalence_class(edge_homotopic, g)) = X.d(1, 1, g) ∧ "+
							"edge_class_target(equivalence_class(edge_homotopic, g)) = X.d(1, 0, g)",
						By(triangles, EdgeClassMorphism.Read(simplicial).At(g)))
					G := q.TermAs[Set[A]]("equivalence_class(edge_homotopic, g)")
					isomorphism := q.Have(
						"the class of g is an inverse to the class of f",
						"category_isomorphism(homotopy_category(X), equivalence_class(edge_homotopic, f))",
						Simp(Fwd(edgeClassIdentityDef), Fwd(category.CategoryIsomorphismDef)),
						SplitConj(
							Case(
								"the class of f is a morphism",
								By(fClass)),
							Case(
								"the class of g supplies the inverse",
								Witness(G),
								By(Normalized, fClass, gClass, ends, leftInverse, rightInverse)),
						))
					q.Show(
						"therefore f is an equivalence",
						By(isomorphism, fEdge, At(EdgeEquivalenceDef, X, f)))
				})
		}),
})}

// OppositeQuasi — the opposite of a quasi-category is a quasi-category:
// it is a simplicial set, and an inner horn of the opposite missing the
// face k, its faces reindexed by i ↦ n + 1 − i, is an inner horn of X
// missing the face n + 1 − k, whose filler in X fills the original horn
// in the opposite.
var OppositeQuasi = oppositeQuasiThm{family.Add(registry.ProofEntry{
	Name: "OppositeQuasi",
	Key:  "prop_523f7e28963f332e",
	Build: QuasiCategory.Law("quasi_category(opposite_simplicial_set(X))",
		func(a *Argument, X *Expr[simplicial_set.SimplicialOps[A]], quasi Fact) {
			d := a.TermAs[Fun3[Nat, Nat, A, A]]("X.d")
			a.Do(Simp(Fwd(QuasiCategory)), SplitConj(
				Case(
					"the opposite has the required simplicial structure",
					By(simplicial_set.OppositeSimplicialSet.Read(QuasiSimplicialSet.Read(quasi)))),
				Case(
					"an inner horn is filled by reversing it, filling in X, and reversing back",
					Derive(func(b *Argument) {
						n, k := b.FixAs[Nat]("n"), b.FixAs[Nat]("k")
						y := b.FixAs[Fun[Nat, A]]("y")
						horn := b.Conjuncts(
							b.Assume(),
							"the missing face k is positive",
							"and at most n",
							"y is a face family of the opposite on the faces of the horn missing k")
						positive, below, opposite := horn[0], horn[1], horn[2]
						reversedFace := b.TermAs[Nat]("n + 1 - k")
						reversed := b.TermAs[Fun[Nat, A]]("λi:num. y(n + 1 - i)")
						bound := b.Have(
							"the missing face k is at most n + 1",
							"k ≤ n + 1",
							ByArith(below))
						inner := b.Have(
							"the reversed missing face n + 1 − k is inner",
							"0 < n + 1 - k ∧ n + 1 - k ≤ n",
							ByArith(positive, below))
						reversedHorn := b.Have(
							"reversed, y is a face family of X on the faces of the horn missing n + 1 − k",
							"face_family(X, n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i))",
							By(At(kan_complex.HornFamilyOpposite, X, n, k, y), bound, opposite))
						x, filled := b.ObtainAs[A](
							"so X, a quasi-category, fills the reversed inner horn",
							"∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, n + 1 - k), λi:num. y(n + 1 - i), x)",
							By(InnerFill.Read(quasi).At(n, reversedFace, reversed), inner, reversedHorn))
						filler := b.Conjuncts(
							filled,
							"x is an (n+1)-simplex of X",
							"filling the reversed horn")
						fills := b.Have(
							"read back through the reversal, x fills the horn of the opposite",
							"faces_filler(opposite_face(X.d), n, horn_faces(n, k), y, x)",
							By(kan_complex.HornFillerOpposite.At(d, n, k, y, x), bound, filler[1]))
						b.Take(x)
						b.Show(
							"so x is a filler of the horn in the opposite",
							By(filler[0], fills))
					}))))
		}),
})}

// EdgeEquivalenceOpposite — the equivalences of the opposite are those
// of X: read in both by inverse triangles (EdgeEquivalenceIffInverseTriangles,
// the opposite a quasi-category by OppositeQuasi), face reversal keeps the
// inverse edge and exchanges its two inverse triangles.
var EdgeEquivalenceOpposite = edgeEquivalenceOppositeThm{family.Add(registry.ProofEntry{
	Name: "EdgeEquivalenceOpposite",
	Key:  "prop_3ac9ec7fd8d30040",
	Build: QuasiCategory.Law("∀f:A. "+
		"    edge_equivalence(opposite_simplicial_set(X), f) ⇔ edge_equivalence(X, f)",
		func(q *Argument, quasi Fact, f *Expr[A]) {
			opposite := q.Have(
				"the opposite is a quasi-category",
				"quasi_category(opposite_simplicial_set(X))",
				By(OppositeQuasi.Read(quasi)))
			q.Do(Simp(
				Fwd(EdgeEquivalenceIffInverseTriangles.Read(quasi)),
				Fwd(EdgeEquivalenceIffInverseTriangles.Read(opposite)),
				Fwd(simplicial_set.OppositeFaceDef),
				Fwd(simplicial_set.OppositeDegeneracyDef)))
			// Both directions are the same exchange of the two inverse triangles.
			exchange := func(r *Argument, criterion Fact) {
				parts := r.Conjuncts(
					criterion,
					"f is an edge",
					"f has an inverse edge g with inverse triangles a and b")
				g, a, b, triangles := r.Unpack3As[A, A, A](parts[1])
				r.Do(SplitConj(
					Case(
						"f remains an edge",
						By(parts[0])),
					Case(
						"g, with its two inverse triangles exchanged, is an inverse edge on the other side",
						Derive(func(t *Argument) {
							t.Take(g)
							t.Take(b)
							t.Take(a)
							t.Show(
								"face reversal swaps the outer faces and the two identity vertices",
								By(triangles))
						})),
				))
			}
			q.Iff()
			q.Forward(
				"inverse triangles in the opposite give inverse triangles in X",
				exchange)
			q.Backward(
				"inverse triangles in X give inverse triangles in the opposite",
				exchange)
		}),
})}
