// special_horns.go — the special outer horns and Joyal's theorem. The
// homotopy category of a Kan complex is a groupoid. In a quasi-category
// an outer horn whose last edge is an equivalence fills, by the left
// fibrations of the cones under its last face; one whose first edge is
// an equivalence fills by the same theorem in the opposite. With both, a
// quasi-category is a Kan complex exactly when its homotopy category is a
// groupoid; so the nerve of a category is a Kan complex exactly when the
// category is a groupoid.

package quasi_category

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/category/category"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/simplicial/kan_complex"
	"github.com/euc-ai/xugo/library/proofs/simplicial/simplicial_set"
	"github.com/euc-ai/xugo/library/registry"
)

// KanHomotopyGroupoid — the homotopy category of a Kan complex is a
// groupoid: an edge e and the identity at its source start at one
// vertex, so the outer horn Λ²₀ they form fills, and the face 0 of the
// filler is a left inverse of e; e and the identity at its target end at
// one vertex, so the outer horn Λ²₂ they form fills, and the face 2 of
// the filler is a right inverse; a morphism with a left and a right
// inverse is an isomorphism.
var KanHomotopyGroupoid = kanHomotopyGroupoidThm{family.Add(registry.ProofEntry{
	Name: "KanHomotopyGroupoid",
	Key:  "prop_3ea6418b13763254",
	Build: kan_complex.KanComplex.Law("groupoid(homotopy_category(X))",
		func(q *Argument, kan Fact) {
			quasi := q.Have(
				"a Kan complex is a quasi-category",
				"quasi_category(X)",
				By(KanQuasi.Read(kan)))
			simplicial := q.Have(
				"it is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			cDef := q.Let("C", q.TermAs[CategoryOps[A, Set[A]]]("homotopy_category(X)"))
			categoryX := q.Have(
				"hX is a category",
				"category(C)",
				Simp(Fwd(cDef)),
				By(HomotopyCategory.Read(quasi)))
			q.Do(Simp(Fwd(category.GroupoidDef)), SplitConj(
				Case(
					"hX is a category",
					By(categoryX)),
				Case(
					"every morphism of hX has an inverse",
					Derive(func(r *Argument) {
						F := r.FixAs[Set[A]]("F")
						inC := r.Assume()
						rawMorphism := r.Simplified(inC, Fwd(cDef))
						e, representative := r.ObtainAs[A](
							"choose an edge representing F",
							"∃e:A. e ∈ X.simplices(1) ∧ F = equivalence_class(edge_homotopic, e)",
							By(rawMorphism, InHomotopyCategoryMorphisms.Read(simplicial).At(F)))
						rep := r.Conjuncts(
							representative,
							"e is an edge",
							"F is its class")
						eIn, represents := rep[0], rep[1]
						sourceIdentity, targetIdentity :=
							r.TermAs[A]("X.s(0, 0, X.d(1, 1, e))"), r.TermAs[A]("X.s(0, 0, X.d(1, 0, e))")
						endIdentities := simplicial_set.EdgeEndIdentities.Read(simplicial).At(e)
						fMorphism := r.Have(
							"F has the endpoints of e",
							"F ∈ C.morphisms ∧ C.source(F) = X.d(1, 1, e) ∧ C.target(F) = X.d(1, 0, e)",
							Simp(Fwd(cDef), Fwd(represents)),
							By(eIn, EdgeClassMorphism.Read(simplicial).At(e)))

						// A left inverse, from the outer horn Λ²₀.
						u, leftTriangle := r.ObtainAs[A](
							"the identity at the source of e and e start at one vertex, so the "+
								"horn Λ²₀ they form fills: a triangle u has them as its faces 1 and 2",
							"∃u:A. u ∈ X.simplices(2) ∧ X.d(2, 1, u) = X.s(0, 0, X.d(1, 1, e)) ∧ X.d(2, 2, u) = e",
							By(eIn, endIdentities, kan_complex.CommonSourceTriangle.Read(kan).At(sourceIdentity, e)))
						g, gDef := r.LetAs[A]("g", "X.d(2, 0, u)")
						gEnds := r.Have(
							"g is an edge with the reversed endpoints",
							"g ∈ X.simplices(1) ∧ X.d(1, 1, g) = X.d(1, 0, e) ∧ X.d(1, 0, g) = X.d(1, 1, e)",
							Simp(Fwd(gDef)),
							By(eIn, leftTriangle, endIdentities, simplicial_set.TwoSimplexFaceEnds.Read(simplicial).At(u)))
						leftClass := r.Have(
							"the triangle u gives a left inverse class",
							"edge_class_compose(equivalence_class(edge_homotopic, g), "+
								"    equivalence_class(edge_homotopic, e)) = "+
								"equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 1, e)))",
							By(gDef, leftTriangle, gEnds, eIn, ComposeClass.Read(quasi).At(e, g, u)))
						G, gClass := r.LetAs[Set[A]]("G", "equivalence_class(edge_homotopic, g)")
						gMorphism := r.Have(
							"G has the endpoints of g",
							"G ∈ C.morphisms ∧ C.source(G) = X.d(1, 1, g) ∧ C.target(G) = X.d(1, 0, g)",
							Simp(Fwd(cDef), Fwd(gClass)),
							By(gEnds, EdgeClassMorphism.Read(simplicial).At(g)))
						leftInverse := r.Have(
							"G is a left inverse of F",
							"C.compose(G, F) = C.identity(C.source(F))",
							Simp(Fwd(fMorphism), Fwd(cDef), Fwd(edgeClassIdentityDef)),
							By(leftClass, represents))

						// A right inverse, from the outer horn Λ²₂.
						v, rightTriangle := r.ObtainAs[A](
							"e and the identity at the target of e end at one vertex, so the "+
								"horn Λ²₂ they form fills: a triangle v has them as its faces 0 and 1",
							"∃v:A. v ∈ X.simplices(2) ∧ X.d(2, 0, v) = e ∧ X.d(2, 1, v) = X.s(0, 0, X.d(1, 0, e))",
							By(eIn, endIdentities, kan_complex.CommonTargetTriangle.Read(kan).At(e, targetIdentity)))
						h, hDef := r.LetAs[A]("h", "X.d(2, 2, v)")
						hEnds := r.Have(
							"h is an edge with the reversed endpoints",
							"h ∈ X.simplices(1) ∧ X.d(1, 1, h) = X.d(1, 0, e) ∧ X.d(1, 0, h) = X.d(1, 1, e)",
							Simp(Fwd(hDef)),
							By(eIn, rightTriangle, endIdentities, simplicial_set.TwoSimplexFaceEnds.Read(simplicial).At(v)))
						rightClass := r.Have(
							"the triangle v gives a right inverse class",
							"edge_class_compose(equivalence_class(edge_homotopic, e), "+
								"    equivalence_class(edge_homotopic, h)) = "+
								"equivalence_class(edge_homotopic, X.s(0, 0, X.d(1, 0, e)))",
							By(hDef, rightTriangle, hEnds, eIn, ComposeClass.Read(quasi).At(h, e, v)))
						H, hClass := r.LetAs[Set[A]]("H", "equivalence_class(edge_homotopic, h)")
						hMorphism := r.Have(
							"H has the endpoints of h",
							"H ∈ C.morphisms ∧ C.source(H) = X.d(1, 1, h) ∧ C.target(H) = X.d(1, 0, h)",
							Simp(Fwd(cDef), Fwd(hClass)),
							By(hEnds, EdgeClassMorphism.Read(simplicial).At(h)))
						rightInverse := r.Have(
							"H is a right inverse of F",
							"C.compose(F, H) = C.identity(C.target(F))",
							Simp(Fwd(fMorphism), Fwd(cDef), Fwd(edgeClassIdentityDef)),
							By(rightClass, represents))

						ends := r.Have(
							"G starts at the target of F and H ends at its source",
							"C.source(G) = C.target(F) ∧ C.target(H) = C.source(F)",
							Simp(Fwd(fMorphism), Fwd(gMorphism), Fwd(hMorphism)),
							By(gEnds, hEnds))
						r.Show(
							"so F, with the left inverse G and the right inverse H, is an isomorphism",
							By(
								fMorphism,
								gMorphism,
								hMorphism,
								ends,
								leftInverse,
								rightInverse,
								category.IsomorphismFromInverses.Read(categoryX).AsFact().At(F, G, H)))
					})),
			))
		}),
})}

// RightSpecialHornFill — in a quasi-category an outer horn Λⁿ⁺¹ₙ₊₁ whose
// last edge is an equivalence has a filler. With n = r + 1, v the last
// face of the horn and k the last face of v, v is a vertex of the cone
// under k, and the faces y(0), …, y(r) form an edge e of the cone under
// the boundary of k that ends at the restriction of v. The projection of
// the boundary cone to X is a left fibration taking e to the last edge of
// the horn, so e is an equivalence; along the restriction, a left
// fibration too, e lifts to an edge of the cone ending at v, which is an
// (n+1)-simplex whose faces are y(0), …, y(n).
var RightSpecialHornFill = rightSpecialHornFillThm{family.Add(registry.ProofEntry{
	Name: "RightSpecialHornFill",
	Key:  "prop_6fda6fd8a6e34760",
	Reading: "The last edge of the horn, between its vertices n and n + 1, lies " +
		"in the face y(0); face_iterate_bottom removes its first n − 1 vertices.",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀n:num. ∀y:(num → A).",
		Hypotheses: []string{
			"1 ≤ n",
			"face_family(n, horn_faces(n, n + 1), y)",
			"edge_equivalence(X, face_iterate_bottom(n, n - 1, y(0)))",
		},
		Conclusion: "∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, n + 1), y, x)",
	},
		func(
			a *Argument,
			X *Expr[simplicial_set.SimplicialOps[A]],
			quasi Fact,
			n *Expr[Nat],
			y *Arrow[Nat, A],
			given Fact,
		) {
			parts := a.Conjuncts(
				given,
				"the horn has positive degree",
				"y is a face family on the faces of the horn missing n + 1",
				"its last edge is an equivalence")
			positive, horn, lastEdge := parts[0], parts[1], parts[2]
			simplicial := a.Have(
				"the quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			r, nIs := a.ObtainAs[Nat](
				"write n = r + 1",
				"∃r:num. n = r + 1",
				ByArith(positive, nat_arith.NonzeroIsSucc.At(n)))
			a.Do(nIs.Rw())
			last, missing := a.TermAs[Nat]("r + 1"), a.TermAs[Nat]("r + 1 + 1")
			zero, one := a.TermAs[Nat]("0"), a.TermAs[Nat]("1")
			family := a.Conjuncts(
				a.Unfolded(horn, simplicial_set.FaceFamilyDef),
				"the faces of the horn are n-simplices",
				"and they are compatible")
			faces, compatible := family[0], a.Unfolded(family[1], simplicial_set.FacesCompatibleDef)
			retained := a.Have(
				"the horn keeps every face up to n",
				"∀j:num. j ≤ r + 1 ⇒ j ∈ horn_faces(r + 1, r + 1 + 1)",
				a.ForEach(
					func(j *Expr[Nat]) Action { return ByArith(kan_complex.HornFacesMember.At(last, missing, j)) }))
			v, vIs := a.LetAs[A]("v", "y(r + 1)")
			k, kIs := a.LetAs[A]("k", "X.d(r + 1, r + 1, v)")
			e, eIs := a.LetAs[Fun[Nat, A]]("e", "normalize_on(0 .. r, junk, y)")
			vIn := a.Have(
				"the last face v of the horn is an n-simplex",
				"v ∈ X.simplices(r + 1)",
				ByArith(faces.At(last), retained.At(last), vIs))
			links := a.Have(
				"by compatibility, the last face of y(j) is the face j of v for j ≤ r",
				"∀j:num. j ≤ r ⇒ X.d(r + 1, r, y(j)) = X.d(r + 1, j, v)",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]()
					live := b.Assume()
					b.Show(
						"the faces j and n of the horn are compatible",
						ByArith(live, compatible.At(j, last), retained.At(j), retained.At(last), vIs))
				}))
			liveValues := a.Have(
				"e is y on 0 .. r",
				"∀j:num. j ≤ r ⇒ e(j) = y(j)",
				eIs.Rw(),
				By(num_segment.NormalizeOnSegmentIn))
			zeroDegree := a.Have(
				"in degree zero the cone adds nothing to the dimension r",
				"r + 0 = r",
				ByArith())
			oneVertex := a.Have(
				"and removes one top vertex",
				"0 + 1 = 1",
				ByArith())

			// (i) The vertex v of the cone.
			vertex := a.Have(
				"v is a vertex of the cone under k",
				"v ∈ simplex_cone_simplices(r, k, 0)",
				Derive(func(b *Argument) {
					oneIs := b.Have(
						"one removal is the successor of zero",
						"1 = suc(0)",
						ByArith())
					top := b.Have(
						"removing the top vertex of v leaves its last face k",
						"face_iterate_top(r + 1, 1, v) = k",
						oneIs.Rw(),
						Simp(Fwd(simplicial_set.FaceIterateTopDef)),
						ByArith(kIs, oneIs))
					b.Show(
						"so v lies in the cone in degree zero",
						Unfold(simplicial_set.SimplexConeSimplicesDef),
						Simp(Fwd(zeroDegree), Fwd(oneVertex)),
						BySets(vIn, top))
				}))

			// (ii) The edge e of the boundary cone.
			edge := a.Have(
				"e is an edge of the boundary cone under k whose target is the restriction of v",
				"e ∈ simplex_boundary_cone_simplices(r, k, 1) ∧ "+
					"simplex_cone_restriction(r, 0, v) = simplex_boundary_cone_face(r, 1, 0, e)",
				SplitConj(
					Case(
						"e is an edge of the boundary cone under k",
						Derive(func(b *Argument) {
							prefix := b.Have(
								"the faces y(0), …, y(r) of the horn form a face family",
								"face_family(r + 1, 0 .. r, y)",
								Unfold(simplicial_set.FaceFamilyDef),
								Unfold(simplicial_set.FacesCompatibleDef),
								Simp(Fwd(num_segment.MembershipFromZero)),
								SplitConj(
									Case(
										"they are n-simplices, as faces of the horn",
										b.ForEach(func(i *Expr[Nat]) Action {
											return ByArith(faces.At(i), retained.At(i))
										})),
									Case(
										"they are compatible, as faces of the horn",
										Derive(func(c *Argument) {
											i, j := c.FixAs[Nat](), c.FixAs[Nat]()
											ranges := c.Assume()
											c.Show(
												"the faces i and j of the horn are compatible",
												ByArith(ranges, compatible.At(i, j), retained.At(i), retained.At(j)))
										})),
								))
							restriction := b.Have(
								"the restriction from the cone to the boundary cone is simplicial",
								"simplicial_map(simplex_cone(X, r, k), "+
									"    simplex_boundary_cone(X, r, k), "+
									"    simplex_cone_restriction(r))",
								By(simplicial_set.ConeRestrictionMap.Read(simplicial).At(r, k)))
							restricted := b.Have(
								"so the restriction of v is a vertex of the boundary cone under k",
								"simplex_cone_restriction(r, 0, v) ∈ simplex_boundary_cone_simplices(r, k, 0)",
								By(vertex, simplicial_set.MapIn.Read(restriction).At(zero, v)))
							restrictedTops := b.Have(
								"so the faces j ≤ r of v, their top vertex removed, are the faces of k",
								Statement{
									Binders: "∀j:num.",
									Hypotheses: []string{
										"0 < r",
										"j ≤ r",
									},
									Conclusion: "face_iterate_top(r + 0, 0 + 1, simplex_cone_restriction(r, 0, v, j)) = X.d(r, j, k)",
								},
								BySets(b.Unfolded(restricted, simplicial_set.SimplexBoundaryConeSimplicesDef)))
							tops := b.Have(
								"so are the faces y(j), j ≤ r, their two top vertices removed",
								"∀j:num. 0 < r ∧ j ≤ r ⇒ face_iterate_top(r + 1, 1 + 1, y(j)) = X.d(r, j, k)",
								Derive(func(c *Argument) {
									j := c.FixAs[Nat]()
									bounds := c.Assume()
									c.Show(
										"removing the top vertex of y(j) and then of its last face",
										CalcEq(
											Leg(
												c.TermAs[A]("face_iterate_top(r, 1, X.d(r + 1, r, y(j)))"),
												"the second removal follows the last face",
												ByArith(
													bounds,
													faces.At(j),
													retained.At(j),
													simplicial_set.FaceIterateTopAbove.Read(simplicial).At(r, one, r, y.Apply(j)))),
											Leg(
												c.TermAs[A]("face_iterate_top(r, 1, X.d(r + 1, j, v))"),
												"the last face of y(j) is the face j of v",
												By(bounds, links.At(j))),
											FinalLeg(
												"the face j of v, its top vertex removed, is the face j of k",
												GroupPremises(bounds, restrictedTops.At(j)).Simp(
													Fwd(simplicial_set.SimplexConeRestrictionDef),
													Fwd(zeroDegree),
													Fwd(oneVertex),
													Fwd(num_segment.NormalizeOnSegmentIn)),
												Basic()),
										))
								}))
							b.Show(
								"so e, which is y normalized on 0 .. r, lies in the boundary cone",
								eIs.Rw(),
								By(prefix, tops, At(simplicial_set.BoundaryConeMembership, X, r, one, k, y)))
						})),
					Case(
						"v lies over the target of e",
						Simp(Fwd(simplicial_set.SimplexConeRestrictionDef), Fwd(simplicial_set.SimplexBoundaryConeFaceDef)),
						Simp(Fwd(zeroDegree)),
						Simp(Fwd(functions.NormalizeOnEqIff), Fwd(num_segment.MembershipFromZero)),
						Derive(func(b *Argument) {
							j := b.FixAs[Nat]("j")
							live := b.Assume()
							b.Show(
								"the face j of v is the last face of y(j)",
								Simp(Fwd(liveValues)),
								By(live, links.At(j)))
						})),
				))

			// (iii) e is an equivalence, reflected along the projection.
			projectionFibration := a.Have(
				"the projection of the boundary cone to X is a left fibration",
				"left_fibration(simplex_boundary_cone(X, r, k), X, simplex_boundary_cone_projection(r))",
				By(ConeProjectionLeftFibration.Read(quasi).At(r, k)))
			equivalence := a.Have(
				"e is an equivalence of the boundary cone",
				"edge_equivalence(simplex_boundary_cone(X, r, k), e)",
				Derive(func(b *Argument) {
					first := b.Have(
						"e begins with the first face of the horn",
						"e(0) = y(0)",
						ByArith(liveValues.At(zero)))
					projects := b.Have(
						"the projection takes e to the last edge of the horn",
						"simplex_boundary_cone_projection(r, 1, e) = face_iterate_bottom(r + 1, r, y(0))",
						Simp(Fwd(simplicial_set.SimplexBoundaryConeProjectionDef)),
						first.Rw(),
						Basic())
					projected := b.Have(
						"so the image of e is an equivalence",
						"edge_equivalence(X, simplex_boundary_cone_projection(r, 1, e))",
						projects.Rw(),
						ByArith(lastEdge))
					b.Show(
						"which the left fibration reflects to e",
						By(quasi, edge, projected, LeftFibrationReflectsEquivalence.Read(projectionFibration).At(e)))
				}))

			// (iv) The lift u of e along the restriction.
			restrictionFibration := a.Have(
				"the restriction from the cone to the boundary cone is a left fibration",
				"left_fibration(simplex_cone(X, r, k), "+
					"    simplex_boundary_cone(X, r, k), "+
					"    simplex_cone_restriction(r))",
				By(ConeRestrictionLeftFibration.Read(quasi).At(r, k)))
			boundaryQuasi := a.Have(
				"the boundary cone, the total space of a left fibration over X, is a quasi-category",
				"quasi_category(simplex_boundary_cone(X, r, k))",
				By(quasi, LeftFibrationTotalQuasi.Read(projectionFibration)))
			u, lifted := a.ObtainAs[A](
				"so the equivalence e lifts to an edge u of the cone ending at v",
				"∃u:A. "+
					"    u ∈ simplex_cone_simplices(r, k, 1) ∧ "+
					"    simplex_cone_face(r, 1, 0, u) = v ∧ "+
					"    simplex_cone_restriction(r, 1, u) = e",
				By(
					boundaryQuasi,
					equivalence,
					vertex,
					edge,
					LeftFibrationLiftEquivalenceToTarget.Read(restrictionFibration).At(e, v)))

			// (v) The lift fills the horn.
			lift := a.Conjuncts(
				lifted,
				"u is an edge of the cone under k",
				"ending at v",
				"and restricting to e")
			prescribed := a.Have(
				"restricting to e, u has the face y(j) at each j ≤ r",
				"∀j:num. j ≤ r ⇒ X.d(r + 1 + 1, j, u) = y(j)",
				lift[2].Simp(Fwd(simplicial_set.SimplexConeRestrictionDef), Fwd(eIs)),
				lift[2].Simp(Fwd(functions.NormalizeOnEqIff), Fwd(num_segment.MembershipFromZero)),
				Basic())
			lastFace := a.Have(
				"ending at v, u has the face v at n",
				"X.d(r + 1 + 1, r + 1, u) = v",
				lift[1].Simp(Fwd(simplicial_set.SimplexConeFaceDef)),
				ByArith(lift[1]))
			a.Take(u)
			a.Show(
				"u, an (n+1)-simplex, fills the horn",
				SplitConj(
					Case(
						"u is an (n+1)-simplex",
						BySets(a.Unfolded(lift[0], simplicial_set.SimplexConeSimplicesDef))),
					Case(
						"its faces other than the missing face n + 1 are those of the horn",
						Unfold(simplicial_set.FacesFillerDef),
						Derive(func(b *Argument) {
							i := b.FixAs[Nat]()
							face := b.Have(
								"i is at most n + 1 and is not n + 1",
								"i ≤ r + 1 + 1 ∧ ¬(i = r + 1 + 1)",
								By(b.Assume(), kan_complex.HornFacesMember.At(last, missing, i)))
							b.Cases(b.TermAs[Bool]("i ≤ r"))
							b.When(
								"a face i ≤ r is the face y(i) u restricts to",
								func(c *Argument, inside Fact) {
									c.Show(
										"u has the face y(i) at i",
										By(inside, prescribed.At(i)))
								})
							b.Otherwise(
								"the remaining face is n, where u ends at v",
								func(c *Argument, outside Fact) {
									index := c.Have(
										"so i is n",
										"i = r + 1",
										ByArith(face, outside))
									c.Show(
										"u has the face v = y(n) at n",
										index.Rw(),
										By(Normalized, lastFace, vIs))
								})
						})),
				))
		}),
})}

// LeftSpecialHornFill — in a quasi-category an outer horn Λⁿ⁺¹₀ whose
// first edge is an equivalence has a filler: reversed, the horn is a horn
// of the opposite missing its last face, whose last edge is the first
// edge of the horn, an equivalence of the opposite as of X; the opposite
// is a quasi-category, so RightSpecialHornFill fills the reversed horn
// there, and the filler, read back through the reversal, fills the horn.
var LeftSpecialHornFill = leftSpecialHornFillThm{family.Add(registry.ProofEntry{
	Name: "LeftSpecialHornFill",
	Key:  "prop_2f7fb3e17fa9c8ec",
	Build: QuasiCategory.Law(Statement{
		Binders: "∀n:num. ∀y:(num → A).",
		Hypotheses: []string{
			"1 ≤ n",
			"face_family(n, horn_faces(n, 0), y)",
			"edge_equivalence(X, face_iterate_top(n, n - 1, y(n + 1)))",
		},
		Conclusion: "∃x:A. x ∈ X.simplices(n + 1) ∧ faces_filler(n, horn_faces(n, 0), y, x)",
	},
		func(
			a *Argument,
			X *Expr[simplicial_set.SimplicialOps[A]],
			quasi Fact,
			n *Expr[Nat],
			y *Arrow[Nat, A],
			datum Fact,
		) {
			d := a.TermAs[Fun3[Nat, Nat, A, A]]("X.d")
			given := a.Conjuncts(
				datum,
				"the horn has positive degree",
				"y is a face family on the faces of the horn missing 0",
				"its first edge is an equivalence")
			positive, horn, firstEdge := given[0], given[1], given[2]
			zero := a.TermAs[Nat]("0")
			reversal := a.TermAs[Fun[Nat, A]]("λi:num. y(n + 1 - i)")
			edge := a.TermAs[A]("face_iterate_top(n, n - 1, y(n + 1))")
			reversedHorn := a.Have(
				"reversed, y is a horn of the opposite missing its last face n + 1",
				"face_family(opposite_simplicial_set(X), n, horn_faces(n, n + 1), λi:num. y(n + 1 - i))",
				ByArith(At(kan_complex.HornFamilyReversed, X, n, zero, y), horn))
			lastEdge := a.Have(
				"its last edge, the first edge of y, is an equivalence of the opposite",
				"edge_equivalence(opposite_simplicial_set(X), "+
					"    face_iterate_bottom(opposite_face(X.d), n, n - 1, y(n + 1)))",
				By(
					simplicial_set.FaceIterateBottomOpposite.At(
						d, n, a.TermAs[Nat]("n - 1"), y.Apply(a.TermAs[Nat]("n + 1"))),
					EdgeEquivalenceOpposite.Read(quasi).At(edge),
					firstEdge))
			x, filled := a.ObtainAs[A](
				"so the opposite, a quasi-category, fills the reversed horn",
				"∃x:A. "+
					"    x ∈ X.simplices(n + 1) ∧ "+
					"    faces_filler(opposite_face(X.d), n, horn_faces(n, n + 1), λi:num. y(n + 1 - i), x)",
				ByArith(
					RightSpecialHornFill.Read(OppositeQuasi.Read(quasi)).At(n, reversal),
					positive,
					reversedHorn,
					lastEdge))
			filler := a.Conjuncts(
				filled,
				"x is an (n+1)-simplex",
				"filling the reversed horn in the opposite")
			fills := a.Have(
				"read back through the reversal, x fills the horn y in X",
				"faces_filler(n, horn_faces(n, 0), y, x)",
				ByArith(kan_complex.HornFillerReversed.At(d, n, zero, y, x), filler[1]))
			a.Take(x)
			a.Show(
				"so x is a filler of the horn",
				By(filler[0], fills))
		}),
})}

// KanIffHomotopyGroupoid — Joyal's theorem, that a quasi-category is a
// Kan complex exactly when its homotopy category is a groupoid: the homotopy
// category of a Kan complex is one (KanHomotopyGroupoid); conversely,
// when it is a groupoid every edge is an equivalence, so an outer horn
// missing its first face fills by LeftSpecialHornFill and one missing
// its last face by RightSpecialHornFill, an inner horn fills in any
// quasi-category, and a horn of dimension one by the degeneracy of its
// vertex.
var KanIffHomotopyGroupoid = kanIffHomotopyGroupoidThm{family.Add(registry.ProofEntry{
	Name: "KanIffHomotopyGroupoid",
	Key:  "prop_603a0397a43d30b5",
	Build: QuasiCategory.Law("kan_complex(X) ⇔ groupoid(homotopy_category(X))",
		func(a *Argument, quasi Fact) {
			simplicial := a.Have(
				"a quasi-category is a simplicial set",
				"simplicial_set(X)",
				By(QuasiSimplicialSet.Read(quasi)))
			a.Iff()
			a.Forward(
				"a Kan complex has a groupoid as homotopy category",
				func(b *Argument, kan Fact) {
					b.Show(
						"the two outer horns supply inverse classes",
						By(KanHomotopyGroupoid.Read(kan)))
				})
			a.Backward(
				"a groupoid homotopy category makes every horn fill",
				func(b *Argument, groupoid Fact) {
					groupoidData := b.Conjuncts(
						b.Unfolded(groupoid, category.GroupoidDef),
						"hX is a category",
						"every morphism of hX is an isomorphism")
					isomorphisms := groupoidData[1]
					allEdges := b.Have(
						"every edge of X is an equivalence",
						"∀f:A. f ∈ X.simplices(1) ⇒ edge_equivalence(X, f)",
						Derive(func(c *Argument) {
							f := c.FixAs[A]()
							fIn := c.Assume()
							class := c.TermAs[Set[A]]("equivalence_class(edge_homotopic, f)")
							invertible := c.Have(
								"the class of f, a morphism of hX, is an isomorphism",
								"category_isomorphism(homotopy_category(X), equivalence_class(edge_homotopic, f))",
								By(isomorphisms.At(class), fIn, EdgeClassMorphism.Read(simplicial).At(f)))
							c.Show(
								"f is an equivalence",
								Simp(Fwd(EdgeEquivalenceDef)),
								By(fIn, invertible))
						}))
					b.Do(Simp(Fwd(kan_complex.KanComplex)), SplitConj(
						Case(
							"X has the required simplicial structure",
							By(simplicial)),
						Case(
							"every horn fills",
							Derive(func(c *Argument) {
								n, k := c.FixAs[Nat]("n"), c.FixAs[Nat]("k")
								y := c.FixAs[Fun[Nat, A]]("y")
								parts := c.Conjuncts(
									c.Assume(),
									"the missing face k is at most n + 1",
									"y is a face family on the faces of the horn missing k")
								bound, horn := parts[0], parts[1]
								members := c.Conjuncts(
									c.Unfolded(horn, simplicial_set.FaceFamilyDef),
									"the members of y on the faces of the horn are n-simplices",
									"and they are compatible")[0]
								nonzero := c.Unless(
									c.TermAs[Bool]("n = 0").Core(),
									"a one-dimensional horn fills in any simplicial set",
									Given(func(q *Argument, zero Fact) {
										q.Show(
											"fill the horn with the degeneracy of its one vertex",
											ByArith(zero, bound, horn, kan_complex.OneDimensionalHornFill.Read(simplicial).At(k, y)))
									}))
								positive := c.Have(
									"the face dimension is at least one",
									"1 ≤ n",
									ByArith(nonzero))
								c.Cases(c.TermAs[Bool]("k = 0"))
								c.When(
									"the first missing face is a special left horn",
									func(q *Argument, first Fact) {
										lastIndex := q.TermAs[Nat]("n + 1")
										lastFace := q.TermAs[A]("y(n + 1)")
										lastIn := q.Have(
											"the last face n + 1, not the missing 0, carries an n-simplex",
											"y(n + 1) ∈ X.simplices(n)",
											ByArith(members.At(lastIndex), kan_complex.HornFacesMember.At(n, k, lastIndex), first))
										count := q.TermAs[Nat]("n - 1")
										edge := q.TermAs[A]("face_iterate_top(n, n - 1, y(n + 1))")
										iterated := q.Have(
											"removing the last n−1 vertices leaves the first edge",
											"face_iterate_top(n, n - 1, y(n + 1)) ∈ X.simplices(n - (n - 1))",
											ByArith(lastIn, simplicial_set.FaceIterateTopIn.Read(simplicial).At(n, count, lastFace)))
										dimension := q.Have(
											"the remaining simplex has dimension one",
											"n - (n - 1) = 1",
											ByArith(positive))
										equivalence := q.Have(
											"the first edge is an equivalence",
											"edge_equivalence(X, face_iterate_top(n, n - 1, y(n + 1)))",
											By(allEdges.At(edge), iterated, dimension))
										q.Show(
											"the special left horn fills",
											first.Rw(),
											By(positive, horn, equivalence, LeftSpecialHornFill.Read(quasi).At(n, y)))
									})
								c.Otherwise(
									"the missing index is positive",
									func(q *Argument, notFirst Fact) {
										q.Cases(q.TermAs[Bool]("k = n + 1"))
										q.When(
											"the last missing face is a special right horn",
											func(r *Argument, last Fact) {
												firstIndex := r.TermAs[Nat]("0")
												firstFace := r.TermAs[A]("y(0)")
												firstIn := r.Have(
													"the first face 0, not the missing n + 1, carries an n-simplex",
													"y(0) ∈ X.simplices(n)",
													ByArith(members.At(firstIndex), kan_complex.HornFacesMember.At(n, k, firstIndex), last))
												count := r.TermAs[Nat]("n - 1")
												edge := r.TermAs[A]("face_iterate_bottom(n, n - 1, y(0))")
												iterated := r.Have(
													"removing the first n−1 vertices leaves the last edge",
													"face_iterate_bottom(n, n - 1, y(0)) ∈ X.simplices(n - (n - 1))",
													ByArith(firstIn, simplicial_set.FaceIterateBottomIn.Read(simplicial).At(n, count, firstFace)))
												dimension := r.Have(
													"the remaining simplex has dimension one",
													"n - (n - 1) = 1",
													ByArith(positive))
												equivalence := r.Have(
													"the last edge is an equivalence",
													"edge_equivalence(X, face_iterate_bottom(n, n - 1, y(0)))",
													By(allEdges.At(edge), iterated, dimension))
												r.Show(
													"the special right horn fills",
													last.Rw(),
													By(positive, horn, equivalence, RightSpecialHornFill.Read(quasi).At(n, y)))
											})
										q.Otherwise(
											"all remaining indices are inner",
											func(r *Argument, notLast Fact) {
												inner := r.Have(
													"the missing index is strictly between the two ends",
													"0 < k ∧ k ≤ n",
													ByArith(notFirst, notLast, bound))
												r.Show(
													"the quasi-category fills this inner horn",
													By(inner, horn, InnerFill.Read(quasi).At(n, k, y)))
											})
									})
							})),
					))
				})
		}),
})}

// NerveKanIffGroupoid — the nerve of a category is a Kan complex
// exactly when the category is a groupoid: the canonical functor to
// its homotopy category transports inverses, and its injective object
// and morphism maps reflect them.
var NerveKanIffGroupoid = nerveKanIffGroupoidThm{family.Add(registry.ProofEntry{
	Name: "NerveKanIffGroupoid",
	Key:  "prop_4480773d3440629c",
	Build: family.Theorem(Statement{
		Binders:    "∀C:category(A, M).",
		Conclusion: "kan_complex(nerve(C)) ⇔ groupoid(C)",
	}, func(a *Argument, cat Fact) {
		C, H := a.Term("C"), a.Term("«H»")
		criterion := KanIffHomotopyGroupoid.Read(NerveQuasi.Read(cat))
		_, bijective := a.Obtain(
			"the canonical functor is bijective on objects and morphisms",
			"∃F:functor_ops(A, M, num → M, set(num → M)). "+
				"    functor(C, «H», F) ∧ "+
				"    injective_on(C.objects, F.obj) ∧ "+
				"    image(F.obj, C.objects) = «H».objects ∧ "+
				"    injective_on(C.morphisms, F.map) ∧ "+
				"    image(F.map, C.morphisms) = «H».morphisms",
			By(NerveHomotopyCategory.Read(cat), HomotopyCategoryDef))
		parts := a.Conjuncts(
			bijective,
			"F is a functor",
			"the object map is injective",
			"its object image is the target carrier",
			"the morphism map is injective",
			"its morphism image is the target carrier")
		preservation := a.Simplified(parts[0], Fwd(category.FunctorDef))
		morphisms := a.Have(
			"F preserves morphisms and their endpoints",
			Statement{
				Binders: "∀f:M.",
				Hypotheses: []string{
					"f ∈ C.morphisms",
				},
				Conclusion: "F.map(f) ∈ «H».morphisms ∧ " +
					"«H».source(F.map(f)) = F.obj(C.source(f)) ∧ " +
					"«H».target(F.map(f)) = F.obj(C.target(f))",
			},
			By(preservation))
		identities := a.Have(
			"F preserves identities",
			"∀x:A. x ∈ C.objects ⇒ F.map(C.identity(x)) = «H».identity(F.obj(x))",
			By(preservation))
		composition := a.Have(
			"F preserves composition",
			Statement{
				Binders: "∀f g:M.",
				Hypotheses: []string{
					"f ∈ C.morphisms",
					"g ∈ C.morphisms",
					"C.target(f) = C.source(g)",
				},
				Conclusion: "F.map(C.compose(g, f)) = «H».compose(F.map(g), F.map(f))",
			},
			By(preservation))

		a.Iff()
		a.Forward(
			"a Kan nerve makes every source morphism invertible",
			func(b *Argument, kan Fact) {
				targetGroupoid := b.Have(
					"the homotopy category is a groupoid",
					"groupoid(«H»)",
					By(kan, criterion))
				invertible := b.Have(
					"every morphism of C has an inverse",
					"∀f:M. f ∈ C.morphisms ⇒ category_isomorphism(C, f)",
					Derive(func(c *Argument) {
						f := c.Fix()
						fIn := c.Assume()
						mappedF := c.Have(
							"the image of f is a morphism with the preserved endpoints",
							"F.map(f) ∈ «H».morphisms ∧ "+
								"«H».source(F.map(f)) = F.obj(C.source(f)) ∧ "+
								"«H».target(F.map(f)) = F.obj(C.target(f))",
							By(fIn, morphisms.At(f)))
						_, inverse := c.Obtain(
							"the image of f has an inverse in the homotopy groupoid",
							"∃β:set(num → M). "+
								"    β ∈ «H».morphisms ∧ "+
								"    «H».source(β) = «H».target(F.map(f)) ∧ "+
								"    «H».target(β) = «H».source(F.map(f)) ∧ "+
								"    «H».compose(β, F.map(f)) = «H».identity(«H».source(F.map(f))) ∧ "+
								"    «H».compose(F.map(f), β) = «H».identity(«H».target(F.map(f)))",
							By(
								targetGroupoid,
								mappedF,
								At(category.GroupoidDef, H),
								At(category.CategoryIsomorphismDef, H, c.Term("F.map(f)"))))
						g, lifted := c.Obtain(
							"the inverse is the image of a source morphism",
							"∃g:M. g ∈ C.morphisms ∧ F.map(g) = β",
							BySets(parts[4], inverse))
						mappedG := c.Have(
							"the lift has the preserved endpoints",
							"F.map(g) ∈ «H».morphisms ∧ "+
								"«H».source(F.map(g)) = F.obj(C.source(g)) ∧ "+
								"«H».target(F.map(g)) = F.obj(C.target(g))",
							By(lifted, morphisms.At(g)))
						objects := c.Have(
							"all four endpoints are objects of C",
							"C.source(f) ∈ C.objects ∧ "+
								"C.target(f) ∈ C.objects ∧ "+
								"C.source(g) ∈ C.objects ∧ "+
								"C.target(g) ∈ C.objects",
							By(fIn, lifted, At(category.MorphismEnds.Read(cat), f), At(category.MorphismEnds.Read(cat), g)))
						objectInjective := c.Simplified(parts[1], Fwd(functions.InjectiveOnDef))
						ends := c.Have(
							"the lifted inverse reverses the endpoints of f",
							"C.source(g) = C.target(f) ∧ C.target(g) = C.source(f)",
							By(
								lifted,
								mappedF,
								mappedG,
								objects,
								inverse,
								objectInjective.At(c.TermAs[A]("C.source(g)"), c.TermAs[A]("C.target(f)")),
								objectInjective.At(c.TermAs[A]("C.target(g)"), c.TermAs[A]("C.source(f)"))))
						mappedEquations := c.Have(
							"the two inverse equations hold after applying F",
							"F.map(C.compose(g, f)) = F.map(C.identity(C.source(f))) ∧ "+
								"F.map(C.compose(f, g)) = F.map(C.identity(C.target(f)))",
							Derive(func(d *Argument) {
								concreteInverse := d.Simplified(inverse, Fwd(HomotopyCategoryDef))
								imageF := d.Simplified(mappedF, Fwd(HomotopyCategoryDef))
								d.Do(SplitConj(
									Case(
										"the inverse after f maps to the identity at its source",
										Derive(func(e *Argument) {
											e.Show(
												"composition and identity preservation give the first mapped equation",
												By(
													Normalized,
													fIn,
													ends,
													lifted,
													imageF,
													objects,
													concreteInverse,
													composition.At(f, g),
													identities.At(e.TermAs[A]("C.source(f)"))))
										})),
									Case(
										"f after its inverse maps to the identity at its target",
										Derive(func(e *Argument) {
											e.Show(
												"composition and identity preservation give the second mapped equation",
												By(
													Normalized,
													fIn,
													ends,
													lifted,
													imageF,
													objects,
													concreteInverse,
													composition.At(g, f),
													identities.At(e.TermAs[A]("C.target(f)"))))
										})),
								))
							}))
						carriers := c.Have(
							"the composites and comparison identities are morphisms",
							"C.compose(g, f) ∈ C.morphisms ∧ "+
								"C.compose(f, g) ∈ C.morphisms ∧ "+
								"C.identity(C.source(f)) ∈ C.morphisms ∧ "+
								"C.identity(C.target(f)) ∈ C.morphisms",
							By(
								fIn,
								lifted,
								ends,
								objects,
								At(category.CompositeMorphism.Read(cat), f, g),
								At(category.CompositeMorphism.Read(cat), g, f),
								category.IdentityMorphism.Read(cat).AsFact().At(c.TermAs[A]("C.source(f)")),
								category.IdentityMorphism.Read(cat).AsFact().At(c.TermAs[A]("C.target(f)"))))
						morphismInjective := c.Simplified(parts[3], Fwd(functions.InjectiveOnDef))
						equations := c.Have(
							"injectivity reflects both inverse equations",
							"C.compose(g, f) = C.identity(C.source(f)) ∧ C.compose(f, g) = C.identity(C.target(f))",
							By(
								carriers,
								mappedEquations,
								morphismInjective.At(c.Term("C.compose(g, f)"), c.Term("C.identity(C.source(f))")),
								morphismInjective.At(c.Term("C.compose(f, g)"), c.Term("C.identity(C.target(f))"))))
						c.Do(Simp(Fwd(category.CategoryIsomorphismDef)))
						c.Do(SplitConj(
							Case(
								"f is a morphism",
								By(fIn)),
							Case(
								"g witnesses its inverse",
								Derive(func(d *Argument) {
									d.Take(g)
									d.Show(
										"the lift has the required endpoints and inverse equations",
										By(lifted, ends, equations))
								})),
						))
					}))
				b.Show(
					"C is a category in which every morphism is invertible",
					By(cat, invertible, category.GroupoidDef))
			})
		a.Backward(
			"a source groupoid makes its nerve Kan",
			func(b *Argument, sourceGroupoid Fact) {
				invertible := b.Have(
					"every homotopy-category morphism is invertible",
					"∀α:set(num → M). α ∈ «H».morphisms ⇒ category_isomorphism(«H», α)",
					Derive(func(c *Argument) {
						c.Fix()
						alphaIn := c.Assume()
						f, represented := c.Obtain(
							"an arbitrary target morphism is the image of a source morphism",
							"∃f:M. f ∈ C.morphisms ∧ F.map(f) = α",
							BySets(parts[4], alphaIn))
						g, inverse := c.Obtain(
							"f has an inverse in C",
							"∃g:M. "+
								"    g ∈ C.morphisms ∧ "+
								"    C.source(g) = C.target(f) ∧ "+
								"    C.target(g) = C.source(f) ∧ "+
								"    C.compose(g, f) = C.identity(C.source(f)) ∧ "+
								"    C.compose(f, g) = C.identity(C.target(f))",
							By(
								sourceGroupoid,
								represented,
								At(category.GroupoidDef, C),
								At(category.CategoryIsomorphismDef, C, f)))
						mappedF := c.Have(
							"the image of f has its preserved endpoints",
							"F.map(f) ∈ «H».morphisms ∧ "+
								"«H».source(F.map(f)) = F.obj(C.source(f)) ∧ "+
								"«H».target(F.map(f)) = F.obj(C.target(f))",
							By(represented, morphisms.At(f)))
						imageF := c.Simplified(mappedF, Fwd(HomotopyCategoryDef))
						mappedG := c.Have(
							"the image of g has its preserved endpoints",
							"F.map(g) ∈ «H».morphisms ∧ "+
								"«H».source(F.map(g)) = F.obj(C.source(g)) ∧ "+
								"«H».target(F.map(g)) = F.obj(C.target(g))",
							By(inverse, morphisms.At(g)))
						imageG := c.Simplified(mappedG, Fwd(HomotopyCategoryDef))
						objects := c.Have(
							"the endpoints of f are objects of C",
							"C.source(f) ∈ C.objects ∧ C.target(f) ∈ C.objects",
							By(represented, At(category.MorphismEnds.Read(cat), f)))
						c.Do(Simp(Fwd(category.CategoryIsomorphismDef), Fwd(HomotopyCategoryDef)))
						c.Do(SplitConj(
							Case(
								"the represented class is a target morphism",
								By(Normalized, represented, imageF)),
							Case(
								"the image of g is its inverse",
								Derive(func(d *Argument) {
									d.Take(d.Term("F.map(g)"))
									d.Do(SplitConjAll(
										Case(
											"the image of the inverse is a morphism",
											By(imageG)),
										Case(
											"its source is the target of the represented morphism",
											By(Normalized, represented, inverse, imageF, imageG)),
										Case(
											"its target is the source of the represented morphism",
											By(Normalized, represented, inverse, imageF, imageG)),
										Case(
											"its composite after the represented morphism is the source identity",
											By(
												Normalized,
												represented,
												inverse,
												imageF,
												objects,
												composition.At(f, g),
												identities.At(d.TermAs[A]("C.source(f)")))),
										Case(
											"its composite before the represented morphism is the target identity",
											By(
												Normalized,
												represented,
												inverse,
												imageF,
												objects,
												composition.At(g, f),
												identities.At(d.TermAs[A]("C.target(f)")))),
									))
								})),
						))
					}))
				targetGroupoid := b.Have(
					"the homotopy category is a groupoid",
					"groupoid(«H»)",
					By(invertible, preservation, category.GroupoidDef))
				b.Show(
					"the homotopy groupoid criterion makes the nerve Kan",
					By(targetGroupoid, criterion))
			})
	}),
})}
