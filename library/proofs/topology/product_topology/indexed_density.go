// indexed_density.go — dense subsets of the product of an indexed family.
// The points that differ from one point of the product at finitely many
// active coordinates, each changed value taken from a dense subset of its
// factor, are dense, since an open set holds a finite intersection of
// cylinders and those constrain finitely many coordinates; with the
// prescribed point and the whole factors, the finitely supported points of
// the product are dense. Over a countable index set with countable dense
// factor sets there are countably many such points, so a countable product
// of separable spaces is separable.

package product_topology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_algebra"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// IndexedFiniteModificationsDense — the points that differ from a fixed
// point a of the product at finitely many active coordinates, each changed
// coordinate taken from a dense subset C(i) of its factor, are dense in the
// product. A nonempty open set contains a finite intersection of cylinders
// around one of its points x, and the cylinders constrain finitely many
// coordinates. Several of them may constrain one coordinate i: their open
// sides, with the whole factor, form a finite family S(i), whose
// intersection W(i) = ⋂S(i) is an open set holding x(i), so it meets the
// dense set C(i). Changing a on the constrained coordinates to such values
// gives a finite modification of a inside the intersection.
var IndexedFiniteModificationsDense = indexedFiniteModificationsDenseThm{family.Add(registry.ProofEntry{
	Name: "IndexedFiniteModificationsDense",
	Key:  "prop_f50887b2d780758d",
	Build: family.Sections(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))). ∀a:(I → A). ∀C:(I → set(A)).",
		Hypotheses: []string{
			"a ∈ «Carrier»",
			"∀i:I. i ∈ J ⇒ is_topology(T(i)) ∧ closure(T(i), C(i)) = ⋃T(i)",
		},
		Conclusion: "closure(indexed_product_topology(J, z, T), «Modifications»(a, C)) = «Carrier»",
		Abbrev: Abbrev{
			{Name: "Modifications", Text: "λa:(I → A). λC:(I → set(A)). " +
				"    {f:(I → A) | finite({i:I | f(i) ≠ a(i)}) ∧ (∀i:I. f(i) ≠ a(i) ⇒ i ∈ J ∧ f(i) ∈ C(i))}"},
			{Name: "Carrier", Text: "indexed_functions(J, z, λi:I. ⋃T(i))"},
			{Name: "Cylinders", Text: "{u:set(I → A) | " +
				"    ∃i:I. ∃v:set(A). " +
				"        i ∈ J ∧ " +
				"        v ∈ T(i) ∧ " +
				"        u = {f:(I → A) | f ∈ indexed_functions(J, z, λj:I. ⋃T(j)) ∧ f(i) ∈ v}}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		modificationsInSpace := ctx.Lemma(Statement{
			Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))). ∀a:(I → A). ∀C:(I → set(A)).",
			Hypotheses: []string{
				"a ∈ «Carrier»",
				"∀i:I. i ∈ J ⇒ C(i) ⊆ ⋃T(i)",
			},
			Conclusion: "«Modifications»(a, C) ⊆ «Carrier»",
		}, func(
			b *Argument,
			J *Expr[Set[I]],
			z *Expr[Fun[I, A]],
			T *Expr[Fun[I, Set[Set[A]]]],
			a *Expr[Fun[I, A]],
			C *Expr[Fun[I, Set[A]]],
			assumptions Fact,
		) {
			parts := b.Conjuncts(
				assumptions,
				"the base point lies in the product",
				"the chosen values lie in their factor spaces")
			b.Do(Simp(Fwd(set_basic.SubsetDef)))
			b.FixAs[Fun[I, A]]("f")
			member := b.Assume()
			baseCoordinates := b.Unfolded(parts[0], indexed_functions.IndexedFunctionsDef)
			b.Show(
				"a modification preserves every coordinate condition",
				Unfold(indexed_functions.IndexedFunctionsDef),
				BySets(parts[1], baseCoordinates, member))
		})
		modificationInIntersection := ctx.Lemma(Statement{
			Binders: "∀J:set(I). " +
				"∀z:(I → A). " +
				"∀T:(I → set(set(A))). " +
				"∀a:(I → A). " +
				"∀C:(I → set(A)). " +
				"∀F:set(set(I → A)). " +
				"∀x:(I → A).",
			Hypotheses: []string{
				"a ∈ «Carrier»",
				"x ∈ «Carrier»",
				"∀i:I. i ∈ J ⇒ is_topology(T(i)) ∧ closure(T(i), C(i)) = ⋃T(i)",
				"∀i:I. i ∈ J ⇒ C(i) ⊆ ⋃T(i)",
				"finite(F)",
				"F ⊆ «Cylinders» ∪ {«Carrier»}",
				"x ∈ ⋂F",
			},
			Conclusion: "∃y:(I → A). y ∈ «Modifications»(a, C) ∧ y ∈ ⋂F",
		}, func(
			b *Argument,
			J *Expr[Set[I]],
			z *Expr[Fun[I, A]],
			T *Expr[Fun[I, Set[Set[A]]]],
			a *Expr[Fun[I, A]],
			C *Expr[Fun[I, Set[A]]],
			F *Expr[Set[Set[Fun[I, A]]]],
			x *Expr[Fun[I, A]],
			assumptions Fact,
		) {
			parts := b.Conjuncts(
				assumptions,
				"the base point lies in the product",
				"the intersection point lies in the product",
				"the coordinate sets are dense",
				"the coordinate sets lie in their factors",
				"the cylinder family is finite",
				"every constraint is a cylinder or the carrier",
				"the point satisfies every constraint")
			represents := b.Have(
				"every proper constraint has a coordinate and an open side",
				Statement{
					Binders: "∀u:set(I → A).",
					Hypotheses: []string{
						"u ∈ F",
						"u ≠ «Carrier»",
					},
					Conclusion: "∃i:I. ∃v:set(A). i ∈ J ∧ v ∈ T(i) ∧ u = {f:(I → A) | f ∈ «Carrier» ∧ f(i) ∈ v}",
				},
				Derive(func(c *Argument) {
					c.FixAs[Set[Fun[I, A]]]("u")
					guard := c.Assume()
					cylinder := c.Have(
						"the proper constraint belongs to the cylinder family",
						"u ∈ «Cylinders»",
						BySets(DenotedAs("cylinders", c.TermAs[Set[Set[Fun[I, A]]]]("«Cylinders»")), parts[5], guard))
					c.Show(
						"a cylinder is described by its coordinate and its open side",
						BySets(cylinder))
				}))
			k, V, representation := b.Obtain2As[Fun[Set[Fun[I, A]], I], Fun[Set[Fun[I, A]], Set[A]]](
				"choose a coordinate and side for each proper constraint",
				"∃k:(set(I → A) → I). ∃V:(set(I → A) → set(A)). ∀u:set(I → A). "+
					"    u ∈ F ∧ u ≠ «Carrier» ⇒ "+
					"    k(u) ∈ J ∧ V(u) ∈ T(k(u)) ∧ u = {f:(I → A) | f ∈ «Carrier» ∧ f(k(u)) ∈ V(u)}",
				By(represents))
			L, lDef := b.LetAs[Set[Set[Fun[I, A]]]]("L", "F ∖ {«Carrier»}")
			K, kDef := b.LetAs[Set[I]]("K", "image(k, L)")
			_, sDef := b.LetAs[Fun[I, Set[Set[A]]]](
				"S", "λi:I. insert(⋃T(i), image(V, {u:set(I → A) | u ∈ L ∧ k(u) = i}))")
			_, wDef := b.LetAs[Fun[I, Set[A]]]("W", "λi:I. ⋂S(i)")
			finiteL := b.Have(
				"the proper constraints form a finite family",
				"finite(L)",
				By(
					Normalized,
					parts[4],
					lDef,
					finite_set.FiniteDiff.At(F, b.TermAs[Set[Set[Fun[I, A]]]]("{«Carrier»}"))))
			sideData := b.Have(
				"each proper side is open and holds the corresponding coordinate of x",
				"∀u:set(I → A). u ∈ L ⇒ k(u) ∈ J ∧ V(u) ∈ T(k(u)) ∧ x(k(u)) ∈ V(u)",
				Derive(func(c *Argument) {
					u := c.FixAs[Set[Fun[I, A]]]("u")
					inL := c.Assume()
					guard := c.Have(
						"a member of L is a proper constraint",
						"u ∈ F ∧ u ≠ «Carrier»",
						By(
							Normalized,
							c.Simplified(
								inL,
								Fwd(lDef),
								Fwd(set_basic.InDiff),
								Fwd(set_basic.InInsert),
								Fwd(set_basic.NotInEmpty))))
					c.Show(
						"its side is open and contains the coordinate of x",
						BySets(guard, representation.At(u), parts[6]))
				}))
			activeCoordinates := b.Have(
				"the constrained coordinates form a finite subset of J",
				"finite(K) ∧ K ⊆ J",
				SplitConj(
					Case(
						"the coordinate image is finite",
						By(Normalized, finiteL, kDef, finite_set.FiniteImage.At(k, L))),
					Case(
						"every constrained coordinate is active",
						BySets(sideData, kDef))))
			neighborhoods := b.Have(
				"intersecting all sides on a coordinate gives an open neighborhood",
				"∀i:I. i ∈ J ⇒ W(i) ∈ T(i) ∧ x(i) ∈ W(i)",
				Derive(func(c *Argument) {
					i := c.FixAs[I]("i")
					active := c.Assume()
					intersected := c.TermAs[Set[Set[A]]]("S(i)")
					fiber := c.TermAs[Set[Set[Fun[I, A]]]]("{u:set(I → A) | u ∈ L ∧ k(u) = i}")
					sides := c.TermAs[Set[Set[A]]]("image(V, {u:set(I → A) | u ∈ L ∧ k(u) = i})")
					carrier := c.TermAs[Set[A]]("⋃T(i)")
					factor := c.TermAs[Set[Set[A]]]("T(i)")
					finiteFamily := c.Have(
						"only finitely many sides are intersected",
						"finite(S(i))",
						Simp(Fwd(sDef)),
						By(
							finiteL,
							finite_set.FiniteRestrict.At(L, c.TermAs[Fun[Set[Fun[I, A]], Bool]]("λu:set(I → A). k(u) = i")),
							finite_set.FiniteImage.At(V, fiber),
							finite_set.FiniteInsert.At(carrier, sides)))
					openAndPoint := c.Have(
						"all sides are open and hold x at this coordinate",
						"S(i) ⊆ T(i) ∧ x(i) ∈ ⋂S(i)",
						SplitConj(
							Case(
								"every side is open",
								Simp(Fwd(sDef), Fwd(set_order.InsertSubset), Fwd(set_image.ImageSubsetIff)),
								SplitConj(
									Case(
										"the factor carrier is open",
										By(active, parts[2].At(i), topological_space.SpaceOpen.At(factor))),
									Case(
										"each selected side is open",
										Derive(func(d *Argument) {
											u := d.FixAs[Set[Fun[I, A]]]("u")
											inFiber := d.Assume()
											d.Show(
												"the side is open in this factor",
												BySets(inFiber, sideData.At(u)))
										})))),
							Case(
								"the coordinate of x lies in every side",
								Simp(
									Fwd(sDef),
									Fwd(set_basic.InInters),
									Fwd(set_basic.ForallInInsert),
									Fwd(set_image.ForallInImage)),
								SplitConj(
									Case(
										"the coordinate lies in its carrier",
										By(
											active,
											parts[1],
											indexed_functions.IndexedFunctionsCoordinate.At(
												J, z, c.TermAs[Fun[I, Set[A]]]("λj:I. ⋃T(j)"), i, x))),
									Case(
										"each selected side contains the coordinate",
										Derive(func(d *Argument) {
											u := d.FixAs[Set[Fun[I, A]]]("u")
											inFiber := d.Assume()
											d.Show(
												"x satisfies this coordinate constraint",
												BySets(inFiber, sideData.At(u)))
										}))))))
					nonemptyFamily := c.Have(
						"the family includes the factor carrier",
						"S(i) ≠ ∅",
						Simp(Fwd(sDef)),
						Cite(set_algebra.InsertNotEmpty.Inst[Set[A]]()))
					c.Show(
						"the finite intersection is an open neighborhood",
						Simp(Fwd(wDef)),
						SplitConj(
							Case(
								"the intersection is open",
								By(
									active,
									parts[2].At(i),
									finiteFamily,
									nonemptyFamily,
									openAndPoint,
									topological_space.IntersOpen.At(factor, intersected))),
							Case(
								"the coordinate belongs to the intersection",
								By(openAndPoint))))
				}))
			coordinateChoice := b.Have(
				"each neighborhood meets the chosen dense coordinate set",
				"∀i:I. i ∈ J ⇒ ∃d:A. d ∈ C(i) ∧ d ∈ W(i)",
				Derive(func(c *Argument) {
					i := c.FixAs[I]("i")
					active := c.Assume()
					meets := c.Have(
						"density makes every nonempty open side meet C(i)",
						"∀u:set(A). u ∈ T(i) ∧ u ≠ ∅ ⇒ u ∩ C(i) ≠ ∅",
						By(
							active,
							parts[2].At(i),
							parts[3].At(i),
							topological_space.DenseMeetsOpen.At(c.TermAs[Set[Set[A]]]("T(i)"), c.TermAs[Set[A]]("C(i)"))))
					c.Show(
						"the open neighborhood contains a chosen coordinate value",
						BySets(active, neighborhoods.At(i), meets.At(c.TermAs[Set[A]]("W(i)"))))
				}))
			_, chosen := b.ObtainAs[Fun[I, A]](
				"choose a value in each dense neighborhood",
				"∃h:(I → A). ∀i:I. i ∈ J ⇒ h(i) ∈ C(i) ∧ h(i) ∈ W(i)",
				By(coordinateChoice))
			y, yDef := b.LetAs[Fun[I, A]]("y", "λi:I. COND(i ∈ K, h(i), a(i))")
			patch := b.Have(
				"the patch uses the chosen values on K and the base point elsewhere",
				"(∀i:I. i ∈ K ⇒ y(i) = h(i)) ∧ (∀i:I. i ∉ K ⇒ y(i) = a(i))",
				By(yDef))
			support := b.TermAs[Set[I]]("{i:I | y(i) ≠ a(i)}")
			supportIn := b.Have(
				"the patch changes only coordinates in K",
				"{i:I | y(i) ≠ a(i)} ⊆ K",
				BySets(patch))
			yInModifications := b.Have(
				"the patched function is a finite modification",
				"y ∈ «Modifications»(a, C)",
				BySets(chosen, supportIn, activeCoordinates, patch, finite_set.FiniteSubset.At(support, K)))
			yInCarrier := b.Have(
				"the patched function lies in the product",
				"y ∈ «Carrier»",
				BySets(At(modificationsInSpace, J, z, T, a, C), parts[0], parts[3], yInModifications))
			sideContainment := b.Have(
				"the coordinate neighborhood lies in every side contributing to it",
				"∀u:set(I → A). u ∈ L ⇒ W(k(u)) ⊆ V(u)",
				Derive(func(c *Argument) {
					u := c.FixAs[Set[Fun[I, A]]]("u")
					inL := c.Assume()
					intersected := c.TermAs[Set[Set[A]]]("S(k(u))")
					includesSide := c.Have(
						"the side V(u) occurs in the intersected family",
						"∃t:set(A). t ∈ S(k(u)) ∧ t ⊆ V(u)",
						Witness(c.TermAs[Set[A]]("V(u)")),
						SplitConj(
							Case(
								"the side belongs to the family",
								Simp(Fwd(sDef)),
								By(
									inL,
									set_image.FunInImage.At(
										V, c.TermAs[Set[Set[Fun[I, A]]]]("{v:set(I → A) | v ∈ L ∧ k(v) = k(u)}"), u),
									set_basic.InInsert.At(
										c.TermAs[Set[Set[A]]]("image(V, {v:set(I → A) | v ∈ L ∧ k(v) = k(u)})"),
										c.TermAs[Set[A]]("⋃T(k(u))"),
										c.TermAs[Set[A]]("V(u)")))),
							Case(
								"the side contains itself",
								Cite(set_order.SubsetRefl))))
					c.Show(
						"the intersection is contained in this side",
						Simp(Fwd(wDef)),
						By(includesSide, set_order.IntersSubsetStrong.At(intersected, c.TermAs[Set[A]]("V(u)"))))
				}))
			b.Take(y)
			b.Show(
				"the patch is a finite modification satisfying every constraint",
				SplitConj(Case(
					"the patch is a finite modification",
					By(yInModifications)),
					Case(
						"the patch satisfies every cylinder constraint",
						Simp(Fwd(set_basic.InInters)),
						Derive(func(c *Argument) {
							u := c.FixAs[Set[Fun[I, A]]]("u")
							inF := c.Assume()
							proper := c.Unless(
								c.TermAs[Bool]("u = «Carrier»"),
								"the carrier constraint is already satisfied",
								Given(func(d *Argument, isCarrier Fact) {
									d.Show(
										"the patch is in the carrier",
										By(Normalized, isCarrier, yInCarrier))
								}))
							inL := c.Have(
								"a proper constraint belongs to L",
								"u ∈ L",
								Simp(Fwd(lDef), Fwd(set_basic.InDiff), Fwd(set_basic.InInsert), Fwd(set_basic.NotInEmpty)),
								By(Normalized, inF, proper))
							constrained := c.Have(
								"its coordinate belongs to K",
								"k(u) ∈ K",
								By(Normalized, inL, kDef, set_image.FunInImage.At(k, L, u)))
							sideMember := c.Have(
								"the patch lies in this constraint's side",
								"y(k(u)) ∈ V(u)",
								BySets(
									inL,
									constrained,
									sideData.At(u),
									chosen.At(c.TermAs[I]("k(u)")),
									patch,
									sideContainment.At(u)))
							c.Show(
								"the cylinder holds the patched point",
								BySets(proper, inF, representation.At(u), yInCarrier, sideMember))
						}))))
		})
		return ctx.Theorem(headline, func(
			b *Argument,
			J *Expr[Set[I]],
			z *Expr[Fun[I, A]],
			T *Expr[Fun[I, Set[Set[A]]]],
			a *Expr[Fun[I, A]],
			C *Expr[Fun[I, Set[A]]],
			assumptions Fact,
		) {
			parts := b.Conjuncts(
				assumptions,
				"the base point lies in the product",
				"the coordinate sets are dense")
			inFactors := b.Have(
				"each dense set lies in its closure, the space of its factor",
				"∀i:I. i ∈ J ⇒ C(i) ⊆ ⋃T(i)",
				Derive(func(c *Argument) {
					i := c.FixAs[I]("i")
					active := c.Assume()
					c.Show(
						"C(i) lies in its closure, which is the space of T(i)",
						By(
							Normalized,
							active,
							parts[1].At(i),
							topological_space.SubsetClosure.At(c.TermAs[Set[Set[A]]]("T(i)"), c.TermAs[Set[A]]("C(i)"))))
				}))
			within := b.Have(
				"the modifications lie in the product carrier",
				"«Modifications»(a, C) ⊆ «Carrier»",
				By(inFactors, parts[0], At(modificationsInSpace, J, z, T, a, C)))
			meets := b.Have(
				"every nonempty product open set meets the modifications",
				"∀u:set(I → A). u ∈ indexed_product_topology(J, z, T) ∧ u ≠ ∅ ⇒ u ∩ «Modifications»(a, C) ≠ ∅",
				Derive(func(c *Argument) {
					u := c.FixAs[Set[Fun[I, A]]]("u")
					openNonempty := c.Assume()
					uParts := c.Conjuncts(
						openNonempty,
						"the set is open",
						"the set is nonempty")
					x, xInU := c.ObtainAs[Fun[I, A]](
						"choose a point of the open set",
						"∃x:(I → A). x ∈ u",
						By(uParts[1], set_basic.MemberNotEmpty.At(u)))
					xInCarrier := c.Have(
						"a point of a product open set lies in its carrier",
						"x ∈ «Carrier»",
						BySets(xInU, uParts[0], IndexedProductCarrier.At(J, z, T)))
					generated := c.Simplified(
						uParts[0],
						Fwd(IndexedProductTopologyDef),
						Fwd(topological_space.TopologyGeneratedOnDef.Inst[Fun[I, A]]()))
					cover, coverData := c.ObtainAs[Set[Set[Fun[I, A]]]](
						"write the generated open set as a union of finite intersections",
						"∃W:set(set(I → A)). "+
							"    u = ⋃W ∧ "+
							"    (∀w:set(I → A). "+
							"        w ∈ W ⇒ ∃F:set(set(I → A)). finite(F) ∧ F ≠ ∅ ∧ F ⊆ «Cylinders» ∪ {«Carrier»} ∧ w = ⋂F)",
						By(generated, topological_space.GeneratedOpenIff.Inst[Fun[I, A]]()))
					coverParts := c.Conjuncts(
						coverData,
						"the basic sets cover u",
						"each basic set is a finite intersection")
					w, wData := c.ObtainAs[Set[Fun[I, A]]](
						"choose a basic set containing x",
						"∃w:set(I → A). w ∈ W ∧ x ∈ w",
						BySets(coverParts[0], xInU))
					F, fData := c.ObtainAs[Set[Set[Fun[I, A]]]](
						"choose its finite family of constraints",
						"∃F:set(set(I → A)). finite(F) ∧ F ≠ ∅ ∧ F ⊆ «Cylinders» ∪ {«Carrier»} ∧ w = ⋂F",
						By(wData, coverParts[1].At(w)))
					xInIntersection := c.Have(
						"x satisfies the finite family",
						"x ∈ ⋂F",
						By(wData, fData))
					y, yData := c.ObtainAs[Fun[I, A]](
						"find a finite modification in that basic set",
						"∃y:(I → A). y ∈ «Modifications»(a, C) ∧ y ∈ ⋂F",
						By(
							parts[1],
							inFactors,
							parts[0],
							xInCarrier,
							xInIntersection,
							fData,
							At(modificationInIntersection, J, z, T, a, C, F, x)))
					yParts := c.Conjuncts(
						yData,
						"the point is a finite modification",
						"the point satisfies all constraints")
					yInW := c.Have(
						"the modification belongs to the basic set",
						"y ∈ w",
						By(yParts[1], fData))
					c.Show(
						"this modification witnesses the required intersection",
						Simp(Rev(set_basic.MemberNotEmpty), Fwd(set_basic.InInter)),
						Witness(y),
						SplitConj(
							Case(
								"the basic set lies in the open set",
								BySets(yInW, coverParts[0], wData, set_order.MemberSubsetUnions.At(cover, w))),
							Case(
								"the point is a finite modification",
								By(Normalized, yParts[0]))))
				}))
			withinSpace := b.Have(
				"the modifications lie in the space of the product topology",
				"«Modifications»(a, C) ⊆ ⋃indexed_product_topology(J, z, T)",
				Simp(Fwd(IndexedProductCarrier)),
				By(within))
			b.Show(
				"meeting all nonempty open sets establishes density",
				Simp(Rev(IndexedProductCarrier)),
				By(
					IndexedProductTopology.At(J, z, T),
					withinSpace,
					meets,
					topological_space.DenseMeetsOpen.At(
						b.TermAs[Set[Set[Fun[I, A]]]]("indexed_product_topology(J, z, T)"),
						b.TermAs[Set[Fun[I, A]]]("«Modifications»(a, C)"))))
		})
	}),
})}

// ProductFiniteSupportDense — in a product of spaces whose prescribed
// values are points of the active factors, the points that differ from the
// prescribed point at only finitely many coordinates are dense. They are
// the finite modifications of z by points of the factors, and each factor
// space is dense in itself.
var ProductFiniteSupportDense = productFiniteSupportDenseThm{family.Add(registry.ProofEntry{
	Name: "ProductFiniteSupportDense",
	Key:  "prop_1c6c452f7408b3e2",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))).",
		Hypotheses: []string{
			"∀i:I. i ∈ J ⇒ is_topology(T(i)) ∧ z(i) ∈ ⋃T(i)",
		},
		Conclusion: "closure(indexed_product_topology(J, z, T), " +
			"    {x:(I → A) | x ∈ indexed_functions(J, z, λi:I. ⋃T(i)) ∧ finite({i:I | x(i) ≠ z(i)})}) = " +
			"indexed_functions(J, z, λi:I. ⋃T(i))",
	},
		func(a *Argument, J *Expr[Set[I]], z *Arrow[I, A], T *Arrow2[I, Set[A], Bool], factors Fact) {
			carriers := a.TermAs[Fun2[I, A, Bool]]("λi:I. ⋃T(i)")
			points := a.Have(
				"a point of the product departs from z only at active coordinates, and there within the factor",
				"∀f:(I → A). f ∈ indexed_functions(J, z, λi:I. ⋃T(i)) ⇔ (∀i:I. f(i) ≠ z(i) ⇒ i ∈ J ∧ f(i) ∈ ⋃T(i))",
				By(factors, At(indexed_functions.IndexedFunctionsChangedCoordinates, J, z, carriers)))
			base := a.Have(
				"z departs from itself nowhere, so it is a point of the product",
				"z ∈ indexed_functions(J, z, λi:I. ⋃T(i))",
				By(points.At(z)))
			spaces := a.Have(
				"each active factor space is its own closure",
				"∀i:I. i ∈ J ⇒ closure(T(i), ⋃T(i)) = ⋃T(i)",
				Derive(func(b *Argument) {
					b.FixAs[I]()
					active := b.Assume()
					topology := b.Have(
						"the active factor is a topology",
						"is_topology(T(i))",
						By(factors, active))
					b.Show(
						"its whole space is closed",
						By(
							topological_space.SpaceClosed.Read(topology),
							topological_space.ClosureOfClosed.At(b.TermAs[Set[Set[A]]]("T(i)"), b.TermAs[Set[A]]("⋃T(i)"))))
				}))
			modifications := a.Have(
				"the finitely supported points of the product are the "+
					"finite modifications of z by points of the factors",
				"{x:(I → A) | x ∈ indexed_functions(J, z, λi:I. ⋃T(i)) ∧ finite({i:I | x(i) ≠ z(i)})} = "+
					"{f:(I → A) | finite({i:I | f(i) ≠ z(i)}) ∧ (∀i:I. f(i) ≠ z(i) ⇒ i ∈ J ∧ f(i) ∈ ⋃T(i))}",
				By(Normalized, points))
			dense := a.Have(
				"the finite modifications of z by points of the factors are dense",
				"closure(indexed_product_topology(J, z, T), "+
					"    {f:(I → A) | finite({i:I | f(i) ≠ z(i)}) ∧ (∀i:I. f(i) ≠ z(i) ⇒ i ∈ J ∧ f(i) ∈ ⋃T(i))}) = "+
					"indexed_functions(J, z, λi:I. ⋃T(i))",
				By(spaces, factors, base, IndexedFiniteModificationsDense.At(J, z, T, z, carriers)))
			a.Show(
				"so are the finitely supported points of the product",
				By(modifications, dense))
		}),
})}

// IndexedProductSeparable — a countable product of separable spaces is
// separable. An empty product is separable by its empty subset. Otherwise
// choose a point a of the product and a countable dense subset C(i) of each
// active factor: the finite modifications of a by values from the C(i) are
// dense (IndexedFiniteModificationsDense) and countably many
// (cardinal.CountableFiniteModifications), a countable dense subset of the
// product.
var IndexedProductSeparable = indexedProductSeparableThm{family.Add(registry.ProofEntry{
	Name: "IndexedProductSeparable",
	Key:  "prop_a333760ba390d152",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))).",
		Hypotheses: []string{
			"countable(J)",
			"∀i:I. i ∈ J ⇒ is_topology(T(i)) ∧ separable_space(T(i))",
		},
		Conclusion: "separable_space(indexed_product_topology(J, z, T))",
		Abbrev: Abbrev{
			{Name: "Modifications", Text: "λa:(I → A). λC:(I → set(A)). " +
				"    {f:(I → A) | finite({i:I | f(i) ≠ a(i)}) ∧ (∀i:I. f(i) ≠ a(i) ⇒ i ∈ J ∧ f(i) ∈ C(i))}"},
			{Name: "Carrier", Text: "indexed_functions(J, z, λi:I. ⋃T(i))"},
		},
	}, func(
		b *Argument,
		J *Expr[Set[I]],
		z *Expr[Fun[I, A]],
		T *Expr[Fun[I, Set[Set[A]]]],
		assumptions Fact,
	) {
		parts := b.Conjuncts(
			assumptions,
			"the active coordinates are countable",
			"the active factors are separable topologies")
		product := b.TermAs[Set[Set[Fun[I, A]]]]("indexed_product_topology(J, z, T)")
		nonempty := b.Unless(
			b.TermAs[Bool]("«Carrier» = ∅"),
			"the empty product space has a countable dense empty subset",
			Given(func(c *Argument, emptyCarrier Fact) {
				c.Do(Simp(
					Fwd(countability.SeparableSpaceDef),
					Fwd(IndexedProductCarrier)), Witness(c.TermAs[Set[Fun[I, A]]]("∅")))
				emptyClosure := c.Have(
					"the empty subset is closed and equals its closure",
					"closure(indexed_product_topology(J, z, T), ∅) = ∅",
					By(
						IndexedProductTopology.At(J, z, T),
						topological_space.EmptyClosed.At(product),
						topological_space.ClosureOfClosed.At(product, c.TermAs[Set[Fun[I, A]]]("∅"))))
				c.Show(
					"the empty set is countable and dense in the empty carrier",
					BySets(emptyClosure, emptyCarrier, cardinal.CountableEmpty))
			}))
		a, aIn := b.ObtainAs[Fun[I, A]](
			"choose a base point of the nonempty product",
			"∃a:(I → A). a ∈ «Carrier»",
			By(nonempty, set_basic.MemberNotEmpty.At(b.TermAs[Set[Fun[I, A]]]("«Carrier»"))))
		denseChoices := b.Have(
			"each active factor supplies a countable dense subset",
			"∀i:I. i ∈ J ⇒ ∃c:set(A). countable(c) ∧ c ⊆ ⋃T(i) ∧ closure(T(i), c) = ⋃T(i)",
			Simp(Rev(countability.SeparableSpaceDef)),
			By(parts[1]))
		C, chosen := b.ObtainAs[Fun[I, Set[A]]](
			"choose countable dense subsets in the active factors",
			"∃C:(I → set(A)). ∀i:I. i ∈ J ⇒ countable(C(i)) ∧ C(i) ⊆ ⋃T(i) ∧ closure(T(i), C(i)) = ⋃T(i)",
			By(denseChoices))
		modificationsCountable := b.Have(
			"the finite modifications form a countable set",
			"countable(«Modifications»(a, C))",
			By(parts[0], chosen, cardinal.CountableFiniteModifications.At(J, a, C)))
		factorData := b.Have(
			"the chosen coordinate sets are dense in their factor topologies",
			"∀i:I. i ∈ J ⇒ is_topology(T(i)) ∧ closure(T(i), C(i)) = ⋃T(i)",
			By(parts[1], chosen))
		modificationsDense := b.Have(
			"the finite modifications are dense in the product",
			"closure(indexed_product_topology(J, z, T), «Modifications»(a, C)) = «Carrier»",
			By(factorData, aIn, IndexedFiniteModificationsDense.At(J, z, T, a, C)))
		within := b.Have(
			"all finite modifications lie in the product",
			"«Modifications»(a, C) ⊆ «Carrier»",
			By(
				modificationsDense,
				topological_space.SubsetClosure.At(product, b.TermAs[Set[Fun[I, A]]]("«Modifications»(a, C)"))))
		b.Show(
			"this countable dense subset proves product separability",
			Simp(Fwd(countability.SeparableSpaceDef), Fwd(IndexedProductCarrier)),
			Witness(b.TermAs[Set[Fun[I, A]]]("«Modifications»(a, C)")),
			By(modificationsCountable, modificationsDense, within))
	}),
})}
