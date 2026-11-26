// left_fibrations.go — a left fibration over a quasi-category has a
// quasi-category as its total space, reflects equivalences, and lifts
// an equivalence to a prescribed target vertex.

package quasi_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_fibration"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// LeftFibrationTotalQuasi — the total space of a left fibration over a
// quasi-category is a quasi-category: an inner horn of X maps to an
// inner horn of Y, which fills there, and the filler lifts back with
// the horn fixed, an inner horn being among the non-last horns a left
// fibration lifts.
var LeftFibrationTotalQuasi = leftFibrationTotalQuasiThm{family.Add(registry.ProofEntry{
	Name: "LeftFibrationTotalQuasi",
	Key:  "prop_4453e68749eceb73",
	Build: kan_fibration.LeftFibration.Law(Statement{
		Hypotheses: []string{
			"quasi_category(Y)",
		},
		Conclusion: "quasi_category(X)",
	},
		func(a *Argument, left, base Fact) {
			mapFact := a.Have(
				"a left fibration is a simplicial map",
				"simplicial_map(p)",
				By(kan_fibration.LeftFibrationMap.Read(left)))
			a.Do(Simp(Fwd(QuasiCategory)), SplitConj(
				Case(
					"X is a simplicial set, the source of the simplicial map p",
					By(simplicial_set.MapSource.Read(mapFact))),
				Case(
					"every inner horn of X fills",
					Derive(func(b *Argument) {
						n, k := b.FixAs[Nat](), b.FixAs[Nat]()
						y := b.FixAs[Fun[Nat, A]]()
						horn := b.Assume()
						given := b.Conjuncts(
							horn,
							"the missing face k is positive",
							"and at most n",
							"y is a face family of X on the faces of the horn")
						positive, innerBound, faces := given[0], given[1], given[2]
						bound := b.Have(
							"the inner index is also at most n + 1",
							"k ≤ n + 1",
							ByArith(innerBound))
						image := b.TermAs[Fun[Nat, B]]("λi:num. p(n, y(i))")
						imageHorn := b.Have(
							"p carries the horn to the corresponding inner horn in Y",
							"face_family(Y, n, horn_faces(n, k), λi:num. p(n, y(i)))",
							By(bound, faces, kan_complex.MapHorn.Read(mapFact).At(n, k, y)))
						z, fills := b.ObtainAs[B](
							"fill the mapped inner horn in the quasi-category Y",
							"∃z:B. z ∈ Y.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), λi:num. p(n, y(i)), z)",
							By(positive, innerBound, imageHorn, InnerFill.Read(base).At(n, k, image)))
						x, lifted := b.ObtainAs[A](
							"lift that simplex along the left fibration with the horn fixed",
							"∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, k), y, x) ∧ p(n + 1, x) = z",
							By(innerBound, faces, fills, kan_fibration.LeftFibrationLift.Read(left).At(n, k, y, z)))
						b.Take(x)
						b.Show(
							"the lifted simplex fills the original inner horn",
							By(lifted))
					})),
			))
		}),
})}

// LeftFibrationReflectsEquivalence — an edge above an equivalence is
// itself an equivalence: lift left inverses twice, then identify the
// second inverse with the original edge class by inverse uniqueness.
var LeftFibrationReflectsEquivalence = leftFibrationReflectsEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "LeftFibrationReflectsEquivalence",
	Key:  "prop_9fa1135007b32cf4",
	Reading: "Membership f ∈ X(1) is essential: p is defined off the simplices " +
		"too, with arbitrary values there. The two lifts are two-dimensional, but " +
		"the homotopy category uses the quasi-category structure of the total space.",
	Build: family.Sections(kan_fibration.LeftFibration.Statement(Statement{
		Binders: "∀f:A.",
		Hypotheses: []string{
			"quasi_category(Y)",
			"f ∈ X.simplices(1)",
			"edge_equivalence(Y, p(1, f))",
		},
		Conclusion: "edge_equivalence(X, f)",
	}),
		func(ctx *Script, headline string) *GoalStackNode {
			leftInverseLift := ctx.Lemma(kan_fibration.LeftFibration.Statement(Statement{
				Binders: "∀a:A.",
				Hypotheses: []string{
					"quasi_category(Y)",
					"a ∈ X.simplices(1)",
					"edge_equivalence(Y, p(1, a))",
				},
				Conclusion: "∃b:A. " +
					"    b ∈ X.simplices(1) ∧ " +
					"    X.d(1, 1, b) = X.d(1, 0, a) ∧ " +
					"    X.d(1, 0, b) = X.d(1, 1, a) ∧ " +
					"    edge_class_compose(equivalence_class(edge_homotopic, b), " +
					"        equivalence_class(edge_homotopic, a)) = " +
					"    equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 1, a))) ∧ " +
					"    edge_equivalence(Y, p(1, b))",
			}),
				func(
					q *Argument,
					X *Expr[simplicial_set.SimplicialOps[A]],
					Y *Expr[simplicial_set.SimplicialOps[B]],
					p *Arrow2[Nat, A, B],
					left Fact,
					base Fact,
					a *Expr[A],
					given Fact,
				) {
					mapFact := q.Have(
						"a left fibration is a simplicial map",
						"simplicial_map(p)",
						By(kan_fibration.LeftFibrationMap.Read(left)))
					simplicial := q.Have(
						"its source is a simplicial set",
						"simplicial_set(X)",
						By(simplicial_set.MapSource.Read(mapFact)))
					quasi := q.Have(
						"its total space X is a quasi-category",
						"quasi_category(X)",
						By(base, LeftFibrationTotalQuasi.Read(left)))
					zero, one := q.TermAs[Nat]("0"), q.TermAs[Nat]("1")
					image := q.TermAs[B]("p(1, a)")
					criterion := q.Have(
						"the image of a has an inverse and two inverse triangles",
						"p(1, a) ∈ Y.simplices(1) ∧ "+
							"(∃gbar t t':B. "+
							"    gbar ∈ Y.simplices(1) ∧ "+
							"    t ∈ Y.simplices(2) ∧ "+
							"    t' ∈ Y.simplices(2) ∧ "+
							"    Y.d(2, 2, t) = p(1, a) ∧ "+
							"    Y.d(2, 0, t) = gbar ∧ "+
							"    Y.d(2, 1, t) = Y.s(0, 0, Y.d(1, 1, p(1, a))) ∧ "+
							"    Y.d(2, 2, t') = gbar ∧ "+
							"    Y.d(2, 0, t') = p(1, a) ∧ "+
							"    Y.d(2, 1, t') = Y.s(0, 0, Y.d(1, 0, p(1, a))))",
						By(given, EdgeEquivalenceIffInverseTriangles.Read(base).At(image)))
					inverseData := q.Conjuncts(
						criterion,
						"the image of a is an edge",
						"one inverse edge occurs in both triangles")
					gbar, t, tPrime, triangles := q.Unpack3As[B, B, B](inverseData[1])
					source := q.TermAs[A]("X.d(1, 1, a)")
					identityFaces := q.Have(
						"the source of a is a vertex, and the identity edge there has both ends at it",
						"X.d(1, 1, a) ∈ X.simplices(0) ∧ "+
							"X.s(0, 0, X.d(1, 1, a)) ∈ X.simplices(1) ∧ "+
							"X.d(1, 0, X.s(0, 0, X.d(1, 1, a))) = X.d(1, 1, a) ∧ "+
							"X.d(1, 1, X.s(0, 0, X.d(1, 1, a))) = X.d(1, 1, a)",
						By(given, simplicial_set.EdgeEndIdentities.Read(simplicial).At(a)))
					sourceImage := q.Have(
						"p preserves the source of a",
						"p(0, X.d(1, 1, a)) = Y.d(1, 1, p(1, a))",
						By(given, simplicial_set.MapFace.Read(mapFact).At(zero, one, a)))
					identityImage := q.Have(
						"p preserves that identity edge",
						"p(1, X.s(0, 0, X.d(1, 1, a))) = Y.s(0, 0, p(0, X.d(1, 1, a)))",
						By(identityFaces, simplicial_set.MapDegeneracy.Read(mapFact).At(zero, zero, source)))
					reversedEnds := q.Have(
						"the two triangles give gbar the reversed endpoints",
						"Y.d(1, 1, gbar) = Y.d(1, 0, p(1, a)) ∧ Y.d(1, 0, gbar) = Y.d(1, 1, p(1, a))",
						By(
							Normalized,
							triangles,
							simplicial_set.TwoSimplexFaceEnds.Read(QuasiSimplicialSet.Read(base)).At(t),
							simplicial_set.TwoSimplexFaceEnds.Read(QuasiSimplicialSet.Read(base)).At(tPrime)))

					identity := q.TermAs[A]("X.s(0, 0, X.d(1, 1, a))")
					w, lift := q.ObtainAs[A](
						"lift the inverse triangle t with the identity at the source of a and a as its faces 1 and 2",
						"∃w:A. "+
							"    w ∈ X.simplices(2) ∧ X.d(2, 1, w) = X.s(0, 0, X.d(1, 1, a)) ∧ X.d(2, 2, w) = a ∧ p(2, w) = t",
						By(
							identityFaces,
							given,
							triangles,
							identityImage,
							sourceImage,
							kan_fibration.LeftFibrationTriangleLift.Read(left).At(identity, a, t)))
					liftData := q.Conjuncts(
						lift,
						"w is a 2-simplex",
						"its face 1 is the identity at the source of a",
						"its face 2 is a",
						"w lies over t")
					wIn, middle, last, wImage := liftData[0], liftData[1], liftData[2], liftData[3]
					b := q.TermAs[A]("X.d(2, 0, w)")
					bEnds := q.Have(
						"the missing face is an edge with reversed endpoints",
						"X.d(2, 0, w) ∈ X.simplices(1) ∧ "+
							"X.d(1, 1, X.d(2, 0, w)) = X.d(1, 0, a) ∧ "+
							"X.d(1, 0, X.d(2, 0, w)) = X.d(1, 1, a)",
						By(wIn, middle, last, identityFaces, simplicial_set.TwoSimplexFaceEnds.Read(simplicial).At(w)))
					mappedFace := q.Have(
						"p preserves the missing face",
						"p(1, X.d(2, 0, w)) = Y.d(2, 0, p(2, w))",
						By(wIn, simplicial_set.MapFace.Read(mapFact).At(one, zero, w)))
					bImage := q.Have(
						"the missing face maps to gbar",
						"p(1, X.d(2, 0, w)) = gbar",
						Simp(Fwd(mappedFace), Fwd(wImage), Fwd(triangles)),
						Basic())
					leftInverse := q.Have(
						"the triangle makes the missing face a left inverse in hX",
						"edge_class_compose(equivalence_class(edge_homotopic, X.d(2, 0, w)), "+
							"    equivalence_class(edge_homotopic, a)) = "+
							"equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 1, a)))",
						By(wIn, middle, last, bEnds, given, ComposeClass.Read(quasi).At(a, b, w)))
					swapped := q.Have(
						"swap the inverse triangles to exhibit an inverse of gbar",
						"∃r u v:B. "+
							"    r ∈ Y.simplices(1) ∧ "+
							"    u ∈ Y.simplices(2) ∧ "+
							"    v ∈ Y.simplices(2) ∧ "+
							"    Y.d(2, 2, u) = gbar ∧ "+
							"    Y.d(2, 0, u) = r ∧ "+
							"    Y.d(2, 1, u) = Y.s(0, 0, Y.d(1, 1, gbar)) ∧ "+
							"    Y.d(2, 2, v) = r ∧ "+
							"    Y.d(2, 0, v) = gbar ∧ "+
							"    Y.d(2, 1, v) = Y.s(0, 0, Y.d(1, 0, gbar))",
						Derive(func(c *Argument) {
							c.Take(image)
							c.Take(tPrime)
							c.Take(t)
							c.Show(
								"the same two triangles have the required swapped faces",
								By(triangles, reversedEnds, inverseData[0]))
						}))
					inverseImage := q.Have(
						"gbar is itself an equivalence",
						"edge_equivalence(Y, gbar)",
						By(swapped, triangles, EdgeEquivalenceIffInverseTriangles.Read(base).At(gbar)))
					bImageEquivalence := q.Have(
						"the image of b is an equivalence",
						"edge_equivalence(Y, p(1, X.d(2, 0, w)))",
						By(Normalized, inverseImage, bImage))
					q.Take(b)
					q.Show(
						"b has the reversed ends, the left inverse equation, and an equivalence as image",
						By(bEnds, leftInverse, bImageEquivalence))
				})

			return ctx.Theorem(headline,
				func(
					q *Argument,
					X *Expr[simplicial_set.SimplicialOps[A]],
					Y *Expr[simplicial_set.SimplicialOps[B]],
					p *Arrow2[Nat, A, B],
					left, base Fact,
					f *Expr[A],
					given Fact,
				) {
					mapFact := q.Have(
						"a left fibration is a simplicial map",
						"simplicial_map(p)",
						By(kan_fibration.LeftFibrationMap.Read(left)))
					simplicial := q.Have(
						"its source is a simplicial set",
						"simplicial_set(X)",
						By(simplicial_set.MapSource.Read(mapFact)))
					quasi := q.Have(
						"its total space X is a quasi-category",
						"quasi_category(X)",
						By(base, LeftFibrationTotalQuasi.Read(left)))
					g, firstLift := q.ObtainAs[A](
						"lift a left inverse of the image of f",
						"∃g:A. "+
							"    g ∈ X.simplices(1) ∧ "+
							"    X.d(1, 1, g) = X.d(1, 0, f) ∧ "+
							"    X.d(1, 0, g) = X.d(1, 1, f) ∧ "+
							"    edge_class_compose(equivalence_class(edge_homotopic, g), "+
							"        equivalence_class(edge_homotopic, f)) = "+
							"    equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 1, f))) ∧ "+
							"    edge_equivalence(Y, p(1, g))",
						By(given, left, base, At(leftInverseLift, X, Y, p, f)))
					h, secondLift := q.ObtainAs[A](
						"apply the same construction to g",
						"∃h:A. "+
							"    h ∈ X.simplices(1) ∧ "+
							"    X.d(1, 1, h) = X.d(1, 0, g) ∧ "+
							"    X.d(1, 0, h) = X.d(1, 1, g) ∧ "+
							"    edge_class_compose(equivalence_class(edge_homotopic, h), "+
							"        equivalence_class(edge_homotopic, g)) = "+
							"    equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 1, g))) ∧ "+
							"    edge_equivalence(Y, p(1, h))",
						By(given, left, base, firstLift, At(leftInverseLift, X, Y, p, g)))
					cDef := q.Let("C", q.TermAs[CategoryOps[A, Set[A]]]("homotopy_category(X)"))
					F, fDef := q.LetAs[Set[A]]("F", "equivalence_class(edge_homotopic, f)")
					G, gDef := q.LetAs[Set[A]]("G", "equivalence_class(edge_homotopic, g)")
					H, hDef := q.LetAs[Set[A]]("H", "equivalence_class(edge_homotopic, h)")
					categoryX := q.Have(
						"hX is a category",
						"category(C)",
						Simp(Fwd(cDef)),
						By(HomotopyCategory.Read(quasi)))
					fMorphism := q.Have(
						"F is a morphism with the ends of f",
						"F ∈ C.morphisms ∧ C.source(F) = X.d(1, 1, f) ∧ C.target(F) = X.d(1, 0, f)",
						Simp(Fwd(cDef), Fwd(fDef), Fwd(HomotopyCategoryDef)),
						By(given, EdgeClassMorphism.Read(simplicial).At(f)))
					gMorphism := q.Have(
						"G is a morphism with the ends of g",
						"G ∈ C.morphisms ∧ C.source(G) = X.d(1, 1, g) ∧ C.target(G) = X.d(1, 0, g)",
						Simp(Fwd(cDef), Fwd(gDef), Fwd(HomotopyCategoryDef)),
						By(firstLift, EdgeClassMorphism.Read(simplicial).At(g)))
					hMorphism := q.Have(
						"H is a morphism with the ends of h",
						"H ∈ C.morphisms ∧ C.source(H) = X.d(1, 1, h) ∧ C.target(H) = X.d(1, 0, h)",
						Simp(Fwd(cDef), Fwd(hDef), Fwd(HomotopyCategoryDef)),
						By(secondLift, EdgeClassMorphism.Read(simplicial).At(h)))
					firstInverse := q.Have(
						"G is a left inverse of F",
						"C.compose(G, F) = C.identity(C.source(F))",
						Simp(
							Fwd(fMorphism),
							Fwd(cDef),
							Fwd(fDef),
							Fwd(gDef),
							Fwd(HomotopyCategoryDef),
							Fwd(edgeClassIdentityDef)),
						By(firstLift, fDef, gDef))
					secondInverse := q.Have(
						"H is a left inverse of G",
						"C.compose(H, G) = C.identity(C.source(G))",
						Simp(Fwd(gMorphism), Fwd(cDef), Fwd(HomotopyCategoryDef), Fwd(edgeClassIdentityDef)),
						By(secondLift))
					ends := q.Have(
						"the three morphisms have the endpoints required for inverse uniqueness",
						"C.source(H) = C.target(G) ∧ C.target(F) = C.source(G) ∧ C.source(F) = C.target(G)",
						Simp(Fwd(fMorphism), Fwd(gMorphism), Fwd(hMorphism)),
						By(firstLift, secondLift))
					rightInverseOfG := q.Have(
						"F is a right inverse of G",
						"C.compose(G, F) = C.identity(C.target(G))",
						Simp(Fwd(firstInverse), Fwd(ends)),
						Basic())
					unique := q.Have(
						"the left and right inverses of G coincide",
						"H = F",
						By(
							fMorphism,
							gMorphism,
							hMorphism,
							ends,
							secondInverse,
							rightInverseOfG,
							category.InverseUnique.Read(categoryX).AsFact().At(G, H, F)))
					rightInverseOfF := q.Have(
						"G is also a right inverse of F",
						"C.compose(F, G) = C.identity(C.target(F))",
						Simp(Fwd(ends), Rev(unique), Fwd(secondInverse)),
						Basic())
					isomorphism := q.Have(
						"G witnesses that F is an isomorphism",
						"category_isomorphism(C, F)",
						Simp(Fwd(category.CategoryIsomorphismDef)),
						SplitConj(
							Case(
								"F is a morphism",
								By(fMorphism)),
							Case(
								"G is a two-sided inverse",
								Derive(func(r *Argument) {
									r.Take(G)
									r.Show(
										"G has the required ends and both inverse equations",
										By(gMorphism, ends, firstInverse, rightInverseOfF))
								})),
						))
					q.Show(
						"f is an equivalence in X",
						Simp(Fwd(EdgeEquivalenceDef), Rev(cDef), Rev(fDef)),
						By(isomorphism, given))
				})
		}),
})}

// LeftFibrationLiftEquivalenceToTarget — lift an equivalence with its
// target prescribed, keeping its image equal to the specified edge:
// lift the inverse edge from that vertex, then lift its inverse triangle.
var LeftFibrationLiftEquivalenceToTarget = leftFibrationLiftEquivalenceToTargetThm{family.Add(registry.ProofEntry{
	Name: "LeftFibrationLiftEquivalenceToTarget",
	Key:  "prop_45beb7dbe93662f6",
	Reading: "The lifted edge maps strictly to e and has target v; " +
		"neither conclusion is an equality merely of homotopy classes.",
	Build: kan_fibration.LeftFibration.Law(Statement{
		Binders: "∀e:B. ∀v:A.",
		Hypotheses: []string{
			"quasi_category(Y)",
			"edge_equivalence(Y, e)",
			"v ∈ X.simplices(0)",
			"p(0, v) = Y.d(1, 0, e)",
		},
		Conclusion: "∃f:A. f ∈ X.simplices(1) ∧ X.d(1, 0, f) = v ∧ p(1, f) = e",
	},
		func(q *Argument, left Fact, e *Expr[B], v *Expr[A], given Fact) {
			parts := q.Conjuncts(
				given,
				"Y is a quasi-category",
				"e is an equivalence",
				"v is a vertex of X",
				"v lies over the target of e")
			base, equivalence, vIn, vertexImage := parts[0], parts[1], parts[2], parts[3]
			mapFact := q.Have(
				"a left fibration is a simplicial map",
				"simplicial_map(p)",
				By(kan_fibration.LeftFibrationMap.Read(left)))
			simplicial := q.Have(
				"its source is a simplicial set",
				"simplicial_set(X)",
				By(simplicial_set.MapSource.Read(mapFact)))
			zero, one := q.TermAs[Nat]("0"), q.TermAs[Nat]("1")

			criterion := q.Have(
				"choose an inverse edge and its two inverse triangles in Y",
				"e ∈ Y.simplices(1) ∧ "+
					"(∃g a b:B. "+
					"    g ∈ Y.simplices(1) ∧ "+
					"    a ∈ Y.simplices(2) ∧ "+
					"    b ∈ Y.simplices(2) ∧ "+
					"    Y.d(2, 2, a) = e ∧ "+
					"    Y.d(2, 0, a) = g ∧ "+
					"    Y.d(2, 1, a) = Y.s(0, 0, Y.d(1, 1, e)) ∧ "+
					"    Y.d(2, 2, b) = g ∧ "+
					"    Y.d(2, 0, b) = e ∧ "+
					"    Y.d(2, 1, b) = Y.s(0, 0, Y.d(1, 0, e)))",
				By(equivalence, EdgeEquivalenceIffInverseTriangles.Read(base).At(e)))
			inverseData := q.Conjuncts(
				criterion,
				"e is an edge",
				"one inverse edge occurs in both triangles")
			g, a, b, triangles := q.Unpack3As[B, B, B](inverseData[1])
			rightTriangle := q.Have(
				"b has g and e as outer faces and the identity at the target as middle face",
				"g ∈ Y.simplices(1) ∧ "+
					"b ∈ Y.simplices(2) ∧ "+
					"Y.d(2, 2, b) = g ∧ "+
					"Y.d(2, 0, b) = e ∧ "+
					"Y.d(2, 1, b) = Y.s(0, 0, Y.d(1, 0, e))",
				By(triangles))
			gSource := q.Have(
				"the other inverse triangle makes g start at the vertex below v",
				"Y.d(1, 1, g) = p(0, v)",
				By(
					Normalized,
					vertexImage,
					triangles,
					simplicial_set.TwoSimplexFaceEnds.Read(QuasiSimplicialSet.Read(base)).At(a)))

			// The horn Λ¹₀ with the vertex v at its one face 1.
			vertexHorn := q.TermAs[Fun[Nat, A]]("λi:num. v")
			vertexMembers := q.Have(
				"the prescribed vertex of the first horn lies in X",
				"∀i:num. i ∈ horn_faces(0, 0) ⇒ v ∈ X.simplices(0)",
				By(vIn))
			vertexCompatible := q.Have(
				"a one-dimensional horn has no compatibility pair",
				"faces_compatible(0, horn_faces(0, 0), λi:num. v)",
				Derive(func(r *Argument) {
					r.Do(Simp(Fwd(simplicial_set.FacesCompatibleDef)))
					i, j := r.FixAs[Nat](), r.FixAs[Nat]()
					pair := r.Assume()
					r.Show(
						"faces i < j of the horn, at most 1 and neither 0, do not exist",
						ByArith(
							pair,
							kan_complex.HornFacesMember.At(zero, zero, i),
							kan_complex.HornFacesMember.At(zero, zero, j)))
				}))
			vertexFamily := q.Have(
				"so v is a horn of X",
				"face_family(0, horn_faces(0, 0), λi:num. v)",
				Simp(Fwd(simplicial_set.FaceFamilyDef)),
				By(vertexMembers, vertexCompatible))
			vertexFaces := q.Have(
				"g fills the image of the horn: its face 1 is the vertex below v",
				"faces_filler(0, horn_faces(0, 0), λi:num. p(0, v), g)",
				Derive(func(r *Argument) {
					// The condition at n = 0 reads the faces d'(0 + 1, i, g); fold the numerals.
					r.Do(Simp(Fwd(simplicial_set.FacesFillerDef)), RingNf())
					i := r.FixAs[Nat]()
					index := r.Assume()
					atOne := r.Have(
						"the only face of the horn is 1",
						"i = 1",
						ByArith(index, kan_complex.HornFacesMember.At(zero, zero, i)))
					r.Show(
						"that face is the vertex below v",
						Simp(Fwd(atOne)),
						By(gSource))
				}))
			u, inverseLift := q.ObtainAs[A](
				"lift the inverse edge g from v",
				"∃u:A. u ∈ X.simplices(1) ∧ faces_filler(0, horn_faces(0, 0), λi:num. v, u) ∧ p(1, u) = g",
				By(
					vertexFamily,
					vertexFaces,
					rightTriangle,
					kan_fibration.LeftFibrationLift.Read(left).At(zero, zero, vertexHorn, g)))
			liftData := q.Conjuncts(
				inverseLift,
				"u is an edge",
				"its source vertex is prescribed",
				"u maps to g")
			uEdge, uHorn, uImage := liftData[0], liftData[1], liftData[2]
			uFaces := q.Unfolded(uHorn, simplicial_set.FacesFillerDef)
			sourceFace := q.Have(
				"1 is the face of the horn, at most 1 and not 0",
				"1 ∈ horn_faces(0, 0)",
				By(kan_complex.HornFacesMember.At(zero, zero, one)))
			uSource := q.Have(
				"u starts at v",
				"X.d(1, 1, u) = v",
				By(uFaces.At(one), sourceFace))
			identityFaces := q.Have(
				"the degenerate edge at v starts and ends at v",
				"X.s(0, 0, v) ∈ X.simplices(1) ∧ X.d(1, 0, X.s(0, 0, v)) = v ∧ X.d(1, 1, X.s(0, 0, v)) = v",
				By(vIn, simplicial_set.VertexDegeneracyFaces.Read(simplicial).At(v)))
			identityImage := q.Have(
				"p preserves the degenerate edge at v",
				"p(1, X.s(0, 0, v)) = Y.s(0, 0, p(0, v))",
				By(vIn, simplicial_set.MapDegeneracy.Read(mapFact).At(zero, zero, v)))

			identity := q.TermAs[A]("X.s(0, 0, v)")
			w, triangleLift := q.ObtainAs[A](
				"lift b with the identity at v and u as its faces 1 and 2",
				"∃w:A. w ∈ X.simplices(2) ∧ X.d(2, 1, w) = X.s(0, 0, v) ∧ X.d(2, 2, w) = u ∧ p(2, w) = b",
				By(
					identityFaces,
					uEdge,
					uSource,
					rightTriangle,
					identityImage,
					vertexImage,
					uImage,
					kan_fibration.LeftFibrationTriangleLift.Read(left).At(identity, u, b)))
			triangleData := q.Conjuncts(
				triangleLift,
				"w is a 2-simplex",
				"its face 1 is the identity at v",
				"its face 2 is u",
				"w maps to b")
			wSimplex, middle, wImage := triangleData[0], triangleData[1], triangleData[3]

			f := q.TermAs[A]("X.d(2, 0, w)")
			fTarget := q.Have(
				"the target of the missing face is the target v of the middle face",
				"X.d(1, 0, X.d(2, 0, w)) = v",
				By(wSimplex, middle, identityFaces, simplicial_set.TwoSimplexFaceEnds.Read(simplicial).At(w)))
			mappedFace := q.Have(
				"p carries the missing face to the missing face of the image triangle",
				"p(1, X.d(2, 0, w)) = Y.d(2, 0, p(2, w))",
				By(wSimplex, simplicial_set.MapFace.Read(mapFact).At(one, zero, w)))
			fImage := q.Have(
				"the missing face of b is e, so f maps strictly to e",
				"p(1, X.d(2, 0, w)) = e",
				Simp(Fwd(mappedFace), Fwd(wImage), Fwd(rightTriangle)),
				Basic())
			q.Take(f)
			q.Show(
				"f is the required edge over e with target v",
				By(wSimplex, simplicial_set.TwoSimplexFaceEnds.Read(simplicial).At(w), fTarget, fImage))
		}),
})}
