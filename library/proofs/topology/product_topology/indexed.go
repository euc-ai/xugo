// indexed.go — the product of an indexed family of spaces. All factors
// live in one type A: T(i) is a topology on a subset of A for each index
// i of J, and the points of the product are the functions that pick a
// point of the i-th space at each i ∈ J and take the prescribed value
// z(i) off J (sets/indexed_functions). The topology is generated on that
// carrier by the coordinate cylinders, the points whose i-th coordinate
// lies in an open set of T(i).

package product_topology

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// IndexedProductTopologyDef — Coordinate cylinders are restricted to the normalized product carrier.
var IndexedProductTopologyDef = indexedProductTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "IndexedProductTopologyDef",
	Key:   "prop_3c87109d4ff9f6cc",
	Const: "indexed_product_topology",
	Type:  "set(I) → (I → A) → (I → set(set(A))) → set(set(I → A))",
	Equations: []string{
		"∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))). " +
			"    indexed_product_topology(J, z, T) = " +
			"    topology_generated_on(indexed_functions(J, z, λi:I. ⋃T(i)), " +
			"        {u:set(I → A) | " +
			"            ∃i:I. ∃v:set(A). " +
			"                i ∈ J ∧ " +
			"                v ∈ T(i) ∧ " +
			"                u = {f:I → A | f ∈ indexed_functions(J, z, λj:I. ⋃T(j)) ∧ f(i) ∈ v}})",
	},
	Reading: "Coordinate cylinders are restricted to the normalized product carrier.",
})}

// IndexedProductCarrier — the points of the product are the indexed
// functions: every cylinder is a set of indexed functions, and generators
// inside a carrier generate exactly that carrier.
var IndexedProductCarrier = indexedProductCarrierThm{family.Add(registry.ProofEntry{
	Name: "IndexedProductCarrier",
	Key:  "prop_fe0f58bf6a5868a5",
	Build: family.Theorem("∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))). "+
		"    ⋃indexed_product_topology(J, z, T) = indexed_functions(J, z, λi:I. ⋃T(i))",
		func(a *Argument, J *Expr[Set[I]], z *Arrow[I, A], T *Arrow2[I, Set[A], Bool]) {
			a.Do(Unfold(IndexedProductTopologyDef))
			a.LetAs[Set[Fun[I, A]]]("X", "indexed_functions(J, z, λi:I. ⋃T(i))")
			_, cylinders := a.LetAs[Set[Set[Fun[I, A]]]](
				"C",
				"{u:set(I → A) | ∃i:I. ∃v:set(A). i ∈ J ∧ v ∈ T(i) ∧ u = {f:I → A | f ∈ X ∧ f(i) ∈ v}}")
			within := a.Have(
				"every cylinder is a set of points of the product",
				"C ⊆ {s:set(I → A) | s ⊆ X}",
				BySets(cylinders))
			a.Show(
				"generators inside the carrier generate exactly the carrier",
				By(within, topological_space.GeneratedOnSpace))
		}),
})}

// IndexedProductTopology — the product of an indexed family is a topology,
// whatever its factors: it is the topology the coordinate cylinders
// generate on the indexed functions.
var IndexedProductTopology = indexedProductTopologyThm{family.Add(registry.ProofEntry{
	Name: "IndexedProductTopology",
	Key:  "prop_d1df5d03ece4cb00",
	Build: family.Theorem("∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))). "+
		"    is_topology(indexed_product_topology(J, z, T))",
		func(a *Argument, J *Expr[Set[I]], z *Arrow[I, A], T *Arrow2[I, Set[A], Bool]) {
			a.Show(
				"the product topology is generated on its carrier",
				By(IndexedProductTopologyDef.At(J, z, T), topological_space.GeneratedOnTopology))
		}),
})}

// IndexedProductTopologyCongruence — the product reads its factors only at
// the indices of J: factors that agree there have the same carrier, and over
// it a cylinder of either is a cylinder of the other, at the same index and
// side; so the two generate the same topology.
var IndexedProductTopologyCongruence = indexedProductTopologyCongruenceThm{family.Add(registry.ProofEntry{
	Name: "IndexedProductTopologyCongruence",
	Key:  "prop_64e0b43ed8879a76",
	Build: family.Theorem(Statement{
		Binders:    "∀J:set(I). ∀z:(I → A). ∀T U:(I → set(set(A))).",
		Hypotheses: []string{"∀i:I. i ∈ J ⇒ T(i) = U(i)"},
		Conclusion: "indexed_product_topology(J, z, T) = indexed_product_topology(J, z, U)",
		Abbrev: Abbrev{
			{Name: "CarrierT", Text: "indexed_functions(J, z, λi:I. ⋃T(i))"},
			{Name: "CarrierU", Text: "indexed_functions(J, z, λi:I. ⋃U(i))"},
			{Name: "Cylinders", Text: "λX:set(I → A). λF:(I → set(set(A))). " +
				"    {u:set(I → A) | ∃i:I. ∃v:set(A). i ∈ J ∧ v ∈ F(i) ∧ u = {f:I → A | f ∈ X ∧ f(i) ∈ v}}"},
		},
	}, func(a *Argument, J *Expr[Set[I]], z *Arrow[I, A], T, U *Arrow2[I, Set[A], Bool], equal Fact) {
		carriers := a.Have(
			"active factor carriers agree and inactive values are prescribed",
			"«CarrierT» = «CarrierU»",
			By(
				equal,
				indexed_functions.IndexedFunctionsCongruence.At(
					J,
					z,
					a.TermAs[Fun[I, Set[A]]]("λi:I. ⋃T(i)"),
					a.TermAs[Fun[I, Set[A]]]("λi:I. ⋃U(i)"))))
		cylinders := a.Have(
			"over the common carrier, T and U have the same cylinders: the same active index and open side",
			"«Cylinders»(«CarrierU», T) = «Cylinders»(«CarrierU», U)",
			Simp(Fwd(set_basic.Extension)),
			Derive(func(b *Argument) {
				b.FixAs[Set[Fun[I, A]]]("u")
				b.Iff()
				b.Forward(
					"a cylinder of T is a cylinder of U",
					func(c *Argument, source Fact) {
						i, v, description := c.Obtain2As[I, Set[A]](
							"a source cylinder has an active index and an open side",
							"∃i:I. ∃v:set(A). i ∈ J ∧ v ∈ T(i) ∧ u = {f:I → A | f ∈ «CarrierU» ∧ f(i) ∈ v}",
							BySets(source),
							Named("i", "v"))
						matching := c.Have(
							"the same side is open in the equal active factor",
							"∃i:I. ∃v:set(A). i ∈ J ∧ v ∈ U(i) ∧ u = {f:I → A | f ∈ «CarrierU» ∧ f(i) ∈ v}",
							Witness(i),
							Witness(v),
							By(Normalized, equal.At(i), description))
						c.Show(
							"the common index and side give the required cylinder",
							BySets(matching))
					})
				b.Backward(
					"a cylinder of U is a cylinder of T",
					func(c *Argument, target Fact) {
						i, v, description := c.Obtain2As[I, Set[A]](
							"a target cylinder has an active index and an open side",
							"∃i:I. ∃v:set(A). i ∈ J ∧ v ∈ U(i) ∧ u = {f:I → A | f ∈ «CarrierU» ∧ f(i) ∈ v}",
							BySets(target),
							Named("i", "v"))
						matching := c.Have(
							"the same side is open in the equal active factor",
							"∃i:I. ∃v:set(A). i ∈ J ∧ v ∈ T(i) ∧ u = {f:I → A | f ∈ «CarrierU» ∧ f(i) ∈ v}",
							Witness(i),
							Witness(v),
							By(Normalized, equal.At(i), description))
						c.Show(
							"the common index and side give the required cylinder",
							BySets(matching))
					})
			}))
		a.Show(
			"the two products are generated by the same cylinders on the same carrier",
			Unfold(IndexedProductTopologyDef),
			carriers.Rw(),
			cylinders.Rw(),
			Basic())
	}),
})}

// IndexedCylinderOpen — a coordinate cylinder over an open set of its
// factor is open in the product, being one of the sets the product
// topology is generated by.
var IndexedCylinderOpen = indexedCylinderOpenThm{family.Add(registry.ProofEntry{
	Name: "IndexedCylinderOpen",
	Key:  "prop_655ba450d040f6e9",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))). ∀i:I. ∀v:set(A).",
		Hypotheses: []string{
			"i ∈ J",
			"v ∈ T(i)",
		},
		Conclusion: "{f:I → A | f ∈ indexed_functions(J, z, λj:I. ⋃T(j)) ∧ f(i) ∈ v} ∈ " +
			"indexed_product_topology(J, z, T)",
	},
		func(
			a *Argument,
			J *Expr[Set[I]],
			z *Arrow[I, A],
			T *Arrow2[I, Set[A], Bool],
			i *Expr[I],
			v *Expr[Set[A]],
			index, open Fact,
		) {
			a.Do(Unfold(IndexedProductTopologyDef))
			a.LetAs[Set[Fun[I, A]]]("X", "indexed_functions(J, z, λj:I. ⋃T(j))")
			_, cylinders := a.LetAs[Set[Set[Fun[I, A]]]](
				"C",
				"{u:set(I → A) | ∃k:I. ∃w:set(A). k ∈ J ∧ w ∈ T(k) ∧ u = {f:I → A | f ∈ X ∧ f(k) ∈ w}}")
			generator := a.Have(
				"the cylinder is the generating cylinder at the index i and the open set v",
				"{f:I → A | f ∈ X ∧ f(i) ∈ v} ∈ C",
				cylinders.Rw(),
				BySets(index, open))
			a.Show(
				"a generator is open in the topology it generates",
				BySets(generator, topological_space.GeneratedOnContains))
		}),
})}

// IndexedProjectionContinuous — each coordinate of the product is
// continuous: a point of the product is an indexed function, whose i-th
// coordinate lies in the i-th space, and the preimage of an open set of
// the i-th space is the cylinder over it.
var IndexedProjectionContinuous = indexedProjectionContinuousThm{family.Add(registry.ProofEntry{
	Name: "IndexedProjectionContinuous",
	Key:  "prop_6ff524e44274ba68",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))). ∀i:I.",
		Hypotheses: []string{
			"i ∈ J",
		},
		Conclusion: "continuous_map(indexed_product_topology(J, z, T), T(i), λf:I → A. f(i))",
	},
		func(
			a *Argument,
			J *Expr[Set[I]],
			z *Arrow[I, A],
			T *Arrow2[I, Set[A], Bool],
			i *Expr[I],
			index Fact,
		) {
			a.Show(
				"the i-th coordinate is continuous",
				continuous.ContinuousMap.Intro(
					Case(
						"a point of the product is an indexed function, which picks a point of the i-th space at i",
						Simp(Fwd(IndexedProductCarrier)),
						By(
							index,
							At(
								indexed_functions.IndexedFunctionsCoordinate, J, z, a.TermAs[Fun[I, Set[A]]]("λj:I. ⋃T(j)"), i))),
					Case(
						"the preimage of an open set v of the i-th space is the cylinder at i over v",
						Derive(func(b *Argument) {
							b.FixAs[Set[A]]("v")
							open := b.Assume()
							b.Show(
								"which is open",
								Simp(Fwd(IndexedProductCarrier)),
								Unfold(functions.PreimageOnDef),
								By(index, open, IndexedCylinderOpen))
						}))))
		}),
})}

// IndexedContinuousIff — the universal property of the product: a map
// into the product is continuous exactly when its values are indexed
// functions and each of its coordinates is continuous. Forward, a
// coordinate is the map followed by a projection. Backward, continuity
// into the topology the cylinders and the carrier generate is read on
// the generators: the carrier pulls back to the whole space, open since
// the domain is a topology, and the cylinder at k over w to the preimage
// of w under the k-th coordinate.
var IndexedContinuousIff = indexedContinuousIffThm{family.Add(registry.ProofEntry{
	Name: "IndexedContinuousIff",
	Key:  "prop_229a20d60a068075",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))). ∀R:set(set(B)). ∀h:(B → I → A).",
		Hypotheses: []string{
			"is_topology(R)",
		},
		Conclusion: "continuous_map(R, indexed_product_topology(J, z, T), h) ⇔ " +
			"(∀x:B. x ∈ ⋃R ⇒ h(x) ∈ indexed_functions(J, z, λi:I. ⋃T(i))) ∧ " +
			"(∀i:I. i ∈ J ⇒ continuous_map(R, T(i), λx:B. h(x, i)))",
	},
		func(
			a *Argument,
			J *Expr[Set[I]],
			z *Arrow[I, A],
			T *Arrow2[I, Set[A], Bool],
			R *Expr[Set[Set[B]]],
			topology topological_space.IsTopologyFact[on.R],
			h *Arrow2[B, I, A],
		) {
			a.Iff()
			a.Forward(
				"a continuous map into the product has its values in the product and continuous coordinates",
				func(b *Argument, continuity Fact) {
					b.Do(SplitConj(
						Case(
							"h carries the space into the product's points, the indexed functions",
							By(continuous.MapsInto.Read(continuity), IndexedProductCarrier)),
						Case(
							"the i-th coordinate of h is h followed by the i-th projection",
							Derive(func(c *Argument) {
								i := c.FixAs[I]("i")
								index := c.Assume()
								composite := c.Have(
									"h followed by the i-th projection is continuous",
									"continuous_map(R, T(i), (λf:I → A. f(i)) ∘ h)",
									By(index, continuous.Compose.Read(continuity), At(IndexedProjectionContinuous, J, z, T, i)))
								c.Show(
									"and that composite is the i-th coordinate of h",
									By(composite, functions.ComposeApply))
							})),
					))
				})
			a.Backward(
				"a map with its values in the product and continuous "+
					"coordinates is continuous, read on the generators",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"h carries the space into the indexed functions",
						"each coordinate of h is continuous")
					points, coordinates := parts[0], parts[1]
					b.Do(Unfold(IndexedProductTopologyDef), Unfold(topological_space.TopologyGeneratedOnDef))
					b.LetAs[Set[Fun[I, A]]]("X", "indexed_functions(J, z, λi:I. ⋃T(i))")
					_, cylinders := b.LetAs[Set[Set[Fun[I, A]]]](
						"C",
						"{u:set(I → A) | ∃k:I. ∃w:set(A). k ∈ J ∧ w ∈ T(k) ∧ u = {f:I → A | f ∈ X ∧ f(k) ∈ w}}")
					generatorsOpen := b.Have(
						"each generator pulls back to an open set",
						"∀v:set(I → A). v ∈ C ∪ {X} ⇒ preimage_on(⋃R, h, v) ∈ R",
						Derive(func(c *Argument) {
							c.FixAs[Set[Fun[I, A]]]("v")
							generator := c.Assume()
							either := c.Have(
								"v is a cylinder or the carrier",
								"v ∈ C ∨ v = X",
								BySets(generator))
							c.Show(
								"in either case its preimage is open",
								either.SplitDisj(
									LeftHolds(
										"a cylinder at an index k over an open set w pulls "+
											"back to the preimage of w under the k-th coordinate",
										Given(func(d *Argument, isCylinder Fact) {
											k, w, cylinder := d.Unpack2As[I, Set[A]](d.Simplified(isCylinder, Fwd(cylinders)), "k", "w")
											facts := d.Conjuncts(
												cylinder,
												"k is an index",
												"w is open in the k-th space",
												"v is the cylinder at k over w")
											coordinate := d.Have(
												"the k-th coordinate of h is continuous",
												"continuous_map(R, T(k), λx:B. h(x, k))",
												By(coordinates.At(k), facts[0]))
											pulledBack := d.Have(
												"the cylinder pulls back to the preimage of w under the k-th coordinate",
												"preimage_on(⋃R, h, {f:I → A | f ∈ X ∧ f(k) ∈ w}) = preimage_on(⋃R, λx:B. h(x, k), w)",
												BySets(points))
											d.Show(
												"which is open, the k-th coordinate being continuous",
												facts[2].Rw(),
												By(pulledBack, continuous.PreimageOpen.Read(coordinate).At(d.MemberOf[on.Any](w, facts[1]))))
										})),
									RightHolds(
										"the carrier pulls back to the whole space, which is open",
										Given(func(d *Argument, isCarrier Fact) {
											whole := d.Have(
												"h carries the whole space into the carrier",
												"preimage_on(⋃R, h, X) = ⋃R",
												BySets(points))
											d.Show(
												"the whole space is open in the topology R",
												isCarrier.Rw(),
												By(Normalized, whole, topological_space.SpaceOpen.Read(topology)))
										})),
								))
						}))
					into := b.Have(
						"h carries the space into the union of the generators",
						"∀x:B. x ∈ ⋃R ⇒ h(x) ∈ ⋃(C ∪ {X})",
						BySets(points))
					b.Show(
						"continuity into a generated topology is read on its generators",
						By(
							topology,
							into,
							generatorsOpen,
							continuous.ContinuousIntoGenerated.At(R, b.TermAs[Set[Set[Fun[I, A]]]]("C ∪ {X}"), h)))
				})
		}),
})}

// IndexedHausdorff — a product of Hausdorff spaces is Hausdorff. Two
// distinct points of the product differ at an index of J, since off J
// both take the prescribed value; disjoint open sets about their
// coordinates there give disjoint open cylinders about the two points.
var IndexedHausdorff = indexedHausdorffThm{family.Add(registry.ProofEntry{
	Name: "IndexedHausdorff",
	Key:  "prop_c4a7373f0c00bdd7",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))).",
		Hypotheses: []string{
			"∀i:I. i ∈ J ⇒ hausdorff(T(i))",
		},
		Conclusion: "hausdorff(indexed_product_topology(J, z, T))",
	},
		func(a *Argument, J *Expr[Set[I]], z *Arrow[I, A], T *Arrow2[I, Set[A], Bool], factors Fact) {
			a.Do(Simp(Fwd(topological_space.HausdorffDef)), Simp(Fwd(IndexedProductCarrier)))
			x := a.FixAs[Fun[I, A]]("x")
			y := a.FixAs[Fun[I, A]]("y")
			points := a.Conjuncts(
				a.Assume(),
				"x is a point of the product",
				"so is y",
				"x and y are distinct")
			carriers := a.TermAs[Fun[I, Set[A]]]("λj:I. ⋃T(j)")
			i, differ := a.ObtainAs[I](
				"x and y differ at an index of J, since off J both take the prescribed value",
				"∃i:I. i ∈ J ∧ x(i) ≠ y(i)",
				By(
					points[0],
					points[1],
					points[2],
					indexed_functions.IndexedFunctionsExtensional.At(J, z, carriers, x, y)))
			at := a.Conjuncts(
				differ,
				"i is an index",
				"x and y differ at i")
			coordinates := a.Have(
				"the i-th coordinates of x and y are points of the i-th space",
				"x(i) ∈ ⋃T(i) ∧ y(i) ∈ ⋃T(i)",
				By(
					at[0],
					points[0],
					points[1],
					indexed_functions.IndexedFunctionsCoordinate.At(J, z, carriers, i, x),
					indexed_functions.IndexedFunctionsCoordinate.At(J, z, carriers, i, y)))
			_, _, separated := a.Obtain2As[Set[A], Set[A]](
				"the i-th space is Hausdorff, so disjoint open sets u and v hold the two coordinates",
				"∃u v:set(A). u ∈ T(i) ∧ v ∈ T(i) ∧ x(i) ∈ u ∧ y(i) ∈ v ∧ u ∩ v = ∅",
				By(at[1], factors, at[0], coordinates, topological_space.HausdorffDef))
			sides := a.Conjuncts(
				separated,
				"u is open",
				"v is open",
				"x(i) lies in u",
				"y(i) lies in v",
				"u and v are disjoint")
			a.Take(a.TermAs[Set[Fun[I, A]]]("{f:I → A | f ∈ indexed_functions(J, z, λj:I. ⋃T(j)) ∧ f(i) ∈ u}"))
			a.Take(a.TermAs[Set[Fun[I, A]]]("{f:I → A | f ∈ indexed_functions(J, z, λj:I. ⋃T(j)) ∧ f(i) ∈ v}"))
			a.Do(SplitConjAll(
				Case(
					"the cylinder at i over u is open",
					By(at[0], sides[0], IndexedCylinderOpen)),
				Case(
					"so is the cylinder at i over v",
					By(at[0], sides[1], IndexedCylinderOpen)),
				Case(
					"x lies in the cylinder over u",
					BySets(points[0], sides[2])),
				Case(
					"y lies in the cylinder over v",
					BySets(points[1], sides[3])),
				Case(
					"the two cylinders are disjoint, as u and v are",
					BySets(sides[4])),
			))
		}),
})}

// Tychonoff — a product of compact spaces is compact. By the Alexander
// subbase lemma it is enough that every cover of the product by cylinders
// has a finite subcover; suppose a cover c by cylinders has none. At an
// index i of J, the sides at i — the open sets of the i-th space whose
// cylinders lie in c — do not cover the i-th space: finitely many would, by
// its compactness, and their cylinders would be a finite subcover. So one
// choice picks, at every index of J, a point of the i-th space outside the
// sides at i, and the prescribed value off J. That point of the product lies
// in a member of c, a cylinder at some index k over a side at k holding its
// k-th coordinate — a contradiction. The factors need not be topologies.
var Tychonoff = tychonoffThm{family.Add(registry.ProofEntry{
	Name: "Tychonoff",
	Key:  "prop_ed4ffb85dc50572d",
	Build: family.Theorem(Statement{
		Binders: "∀J:set(I). ∀z:(I → A). ∀T:(I → set(set(A))).",
		Hypotheses: []string{
			"∀i:I. i ∈ J ⇒ compact_in(T(i), ⋃T(i))",
		},
		Conclusion: "compact_in(indexed_product_topology(J, z, T), indexed_functions(J, z, λi:I. ⋃T(i)))",
	},
		func(a *Argument, J *Expr[Set[I]], z *Arrow[I, A], T *Arrow2[I, Set[A], Bool], factors Fact) {
			a.Do(Unfold(IndexedProductTopologyDef))
			X, xDef := a.LetAs[Set[Fun[I, A]]]("X", "indexed_functions(J, z, λi:I. ⋃T(i))")
			C, cylinders := a.LetAs[Set[Set[Fun[I, A]]]](
				"C",
				"{u:set(I → A) | ∃k:I. ∃w:set(A). k ∈ J ∧ w ∈ T(k) ∧ u = {f:I → A | f ∈ X ∧ f(k) ∈ w}}")
			points := a.Have(
				"a point of X picks a point of the i-th space at each index i of J, and the prescribed value off J",
				"∀f:I → A. f ∈ X ⇔ (∀i:I. i ∈ J ⇒ f(i) ∈ ⋃T(i)) ∧ (∀i:I. i ∉ J ⇒ f(i) = z(i))",
				xDef.Rw(),
				Unfold(indexed_functions.IndexedFunctionsDef),
				BySets())
			subcovers := a.Have(
				"every cover of X by cylinders has a finite subcover",
				"∀c:set(set(I → A)). c ⊆ C ∧ X ⊆ ⋃c ⇒ ∃d:set(set(I → A)). d ⊆ c ∧ finite(d) ∧ X ⊆ ⋃d",
				Derive(func(b *Argument) {
					b.FixAs[Set[Set[Fun[I, A]]]]("c")
					cover := b.Conjuncts(
						b.Assume(),
						"the members of c are cylinders",
						"c covers X")
					ofCylinders, covers := cover[0], cover[1]
					noFiniteSubcover := b.SupposeNot()
					_, sidesDef := b.LetAs[Fun[I, Set[Set[A]]]](
						"sides",
						"λi:I. {v:set(A) | v ∈ T(i) ∧ {f:I → A | f ∈ X ∧ f(i) ∈ v} ∈ c}")
					uncovered := b.Have(
						"at an index of J the sides do not cover the space: finitely "+
							"many would, and their cylinders would be a finite subcover",
						"∀i:I. i ∈ J ⇒ ∃y:A. y ∈ ⋃T(i) ∧ y ∉ ⋃sides(i)",
						Derive(func(g *Argument) {
							i := g.FixAs[I]("i")
							index := g.Assume()
							covered := g.SupposeNot()
							compactness := g.Conjuncts(
								g.Unfolded(GroupPremises(index, factors.At(i)), compact.CompactInDef),
								"the i-th space lies in itself",
								"every open cover of the i-th space has a finite subcover")[1]
							sidesCover := g.Have(
								"the sides at i are open sets of the i-th space, and they cover it",
								"sides(i) ⊆ T(i) ∧ ⋃T(i) ⊆ ⋃sides(i)",
								BySets(covered, sidesDef))
							e, finitely := g.ObtainAs[Set[Set[A]]](
								"so finitely many sides e cover the i-th space",
								"∃e:set(set(A)). e ⊆ sides(i) ∧ finite(e) ∧ ⋃T(i) ⊆ ⋃e",
								By(compactness.At(g.TermAs[Set[Set[A]]]("sides(i)")), sidesCover))
							few := g.Conjuncts(
								finitely,
								"e consists of sides",
								"e is finite",
								"e covers the i-th space")
							inC := g.Have(
								"the cylinders at i over the members of e are members of c",
								"image(λv:set(A). {f:I → A | f ∈ X ∧ f(i) ∈ v}, e) ⊆ c",
								Simp(Fwd(set_image.ImageSubsetIff)),
								BySets(few[0], sidesDef))
							coverX := g.Have(
								"and they cover X, the i-th coordinate of a point of X lying in a member of e",
								"X ⊆ ⋃image(λv:set(A). {f:I → A | f ∈ X ∧ f(i) ∈ v}, e)",
								Simp(Fwd(set_image.UnionsImage)),
								BySets(points, index, few[2]))
							g.Show(
								"so they are a finite subcover of c",
								By(
									noFiniteSubcover,
									inC,
									coverX,
									few[1],
									finite_set.FiniteImage.At(
										g.TermAs[Fun[Set[A], Set[Fun[I, A]]]]("λv:set(A). {f:I → A | f ∈ X ∧ f(i) ∈ v}"), e)))
						}))
					values := b.Have(
						"so at every index there is a value: a point of the "+
							"space outside the sides on J, the prescribed value off J",
						"∀i:I. ∃y:A. (i ∈ J ⇒ y ∈ ⋃T(i) ∧ y ∉ ⋃sides(i)) ∧ (i ∉ J ⇒ y = z(i))",
						By(uncovered))
					_, chosen := b.ObtainAs[Fun[I, A]](
						"one choice picks a value at every index",
						"∃x:I → A. ∀i:I. (i ∈ J ⇒ x(i) ∈ ⋃T(i) ∧ x(i) ∉ ⋃sides(i)) ∧ (i ∉ J ⇒ x(i) = z(i))",
						By(values))
					inX := b.Have(
						"so x is a point of X",
						"x ∈ X",
						By(chosen, points))
					_, member := b.ObtainAs[Set[Fun[I, A]]](
						"c covers X, so a member w of c holds x",
						"∃w:set(I → A). w ∈ c ∧ x ∈ w",
						BySets(inX, covers))
					holds := b.Conjuncts(
						member,
						"w is a member of c",
						"x lies in w")
					isCylinder := b.Have(
						"w is a cylinder",
						"w ∈ C",
						BySets(holds[0], ofCylinders))
					k, _, cylinder := b.Unpack2As[I, Set[A]](b.Simplified(isCylinder, Fwd(cylinders)), "k", "v")
					parts := b.Conjuncts(
						cylinder,
						"k is an index",
						"v is open in the k-th space",
						"w is the cylinder at k over v")
					cylinderInC := b.Have(
						"the cylinder at k over v is a member of c",
						"{f:I → A | f ∈ X ∧ f(k) ∈ v} ∈ c",
						By(parts[2], holds[0]))
					side := b.Have(
						"so v is a side at k, and it holds the k-th coordinate of x",
						"x(k) ∈ v ∧ v ∈ sides(k)",
						BySets(sidesDef, parts[1], parts[2], holds[1], cylinderInC))
					b.Show(
						"but the k-th coordinate of x lies outside every side at k",
						BySets(chosen.At(k), parts[0], side))
				}))
			a.Show(
				"so X is compact in the topology the cylinders generate on it, by the Alexander subbase lemma",
				By(subcovers, compact.AlexanderSubbase.At(X, C)))
		}),
})}
