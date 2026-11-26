// torus.go — the torus as the plane wrapped by the integer lattice,
// ℝ²/ℤ² ≅ S¹ × S¹: the circle map taken in each coordinate identifies the
// classes of the lattice with the points of the product of two circles.

package standard_quotient_spaces

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// TorusQuotient — the plane modulo the integer lattice is the torus, the
// product of two circles: ℝ²/ℤ² ≅ S¹ × S¹. The circle map in each
// coordinate, (s, t) ↦ (e(s), e(t)), is continuous from the plane to the
// torus, a Hausdorff space, and already onto from the compact unit square,
// as e is onto from ⟦0, 1⟧ (CircleMapOnto); two pairs have the same image
// exactly when both their coordinates differ by integers (CircleMapFibres),
// so the fibres of the map are the classes of the lattice, and the quotient
// by them is the torus (continuous.FibreQuotientHomeomorphic).
var TorusQuotient = torusQuotientThm{family.Add(registry.ProofEntry{
	Name: "TorusQuotient",
	Key:  "prop_8502624ca4540617",
	Build: family.Theorem(Statement{
		Conclusion: "homeomorphic(quotient_topology(product_topology(real_topology, real_topology), " +
			"        λp:prod(real, real). " +
			"            {q:prod(real, real) | integer(fst(q) - fst(p)) ∧ integer(snd(q) - snd(p))}), " +
			"    product_topology(euclidean_sphere_topology(1), euclidean_sphere_topology(1)))",
		Abbrev: Abbrev{
			{Name: "circle", Text: "λt:real. λi:num. " +
				"    COND(i = 0, cos(&2 * pi * t), COND(i = 1, sin(&2 * pi * t), &0))"},
			{Name: "torus", Text: "λp:prod(real, real). («circle»(fst(p)), «circle»(snd(p)))"},
		},
	}, func(a *Argument) {
		type point = Fun[Nat, Real]
		type pair = Prod[point, point]
		two := a.TermAs[Nat]("2")
		line := a.TermAs[Set[Set[Real]]]("real_topology")
		plane := a.TermAs[Set[Set[point]]]("euclidean_topology(2)")
		sphere := a.TermAs[Set[point]]("euclidean_sphere(1)")
		circleSpace := a.TermAs[Set[Set[point]]]("euclidean_sphere_topology(1)")
		circle := a.TermAs[Fun2[Real, Nat, Real]]("«circle»")
		torus := a.TermAs[Fun[Prod[Real, Real], pair]]("«torus»")
		unit := a.TermAs[Set[Real]]("⟦&0, &1⟧")
		square := a.TermAs[Set[Prod[Real, Real]]]("set_cross(⟦&0, &1⟧, ⟦&0, &1⟧)")
		circleSpaceDef := a.Have(
			"the circle as a space is the plane's subspace on the unit circle",
			"euclidean_sphere_topology(1) = subtopology(euclidean_topology(2), euclidean_sphere(1))",
			By(euclidean_topology.EuclideanSphereTopologyDef.At(a.TermAs[Nat]("1"))))
		torusSpace := a.Have(
			"the torus S¹ × S¹ is a space, the circle being a subspace of the plane",
			"is_topology(product_topology(euclidean_sphere_topology(1), euclidean_sphere_topology(1)))",
			By(
				circleSpaceDef,
				topological_space.SubtopologyTopology,
				euclidean_topology.EuclideanTopology.At(two),
				product_topology.ProductTopology.At(circleSpace, circleSpace)))
		separated := a.Have(
			"and a Hausdorff one, the circle being a subspace of the Hausdorff plane",
			"hausdorff(product_topology(euclidean_sphere_topology(1), euclidean_sphere_topology(1)))",
			By(
				circleSpaceDef,
				topological_space.HausdorffSubtopology.At(plane, sphere),
				euclidean_topology.EuclideanHausdorff.At(two),
				product_topology.HausdorffProduct.At(circleSpace, circleSpace)))
		continuity := a.Have(
			"the circle map in each coordinate is continuous from the plane to the torus",
			"continuous_map(product_topology(real_topology, real_topology), "+
				"    product_topology(euclidean_sphere_topology(1), euclidean_sphere_topology(1)), "+
				"    «torus»)",
			By(
				product_topology.ProductMapContinuous.At(line, line, circleSpace, circleSpace, circle, circle),
				CircleMapContinuous))
		compactSquare := a.Have(
			"the unit square is compact, a product of compact intervals",
			"compact_in(product_topology(real_topology, real_topology), set_cross(⟦&0, &1⟧, ⟦&0, &1⟧))",
			By(
				product_topology.CompactProduct.At(line, line, unit, unit),
				real_topology.RealTopology,
				real_topology.ClosedIntervalCompact.At(a.TermAs[Real]("&0"), a.TermAs[Real]("&1"))))
		into := a.Have(
			"the map carries the square into the product of two unit circles",
			"image(«torus», set_cross(⟦&0, &1⟧, ⟦&0, &1⟧)) ⊆ "+
				"set_cross(euclidean_sphere(1), euclidean_sphere(1))",
			Simp(Fwd(set_image.ImageSubsetIff)),
			By(CircleMapOnCircle, set_product.InCross))
		onto := a.Have(
			"every pair of points of the unit circle is the image of a point of the square",
			Statement{
				Binders: "∀q:prod(num → real, num → real).",
				Hypotheses: []string{
					"q ∈ set_cross(euclidean_sphere(1), euclidean_sphere(1))",
				},
				Conclusion: "q ∈ image(«torus», set_cross(⟦&0, &1⟧, ⟦&0, &1⟧))",
			},
			Derive(func(b *Argument) {
				q := b.FixAs[pair]("q")
				onCircles := b.Assume()
				coordinates := b.Have(
					"both coordinates of q are values of e on ⟦0, 1⟧",
					"fst(q) ∈ image(«circle», ⟦&0, &1⟧) ∧ snd(q) ∈ image(«circle», ⟦&0, &1⟧)",
					By(onCircles, CircleMapOnto, set_product.InCrossProjections.At(sphere, sphere, q)))
				_, first := b.ObtainAs[Real](
					"the first is e(s) for some s in ⟦0, 1⟧",
					"∃s:real. fst(q) = «circle»(s) ∧ s ∈ ⟦&0, &1⟧",
					By(coordinates, set_basic.InImage.At(circle, unit, b.TermAs[point]("fst(q)"))))
				_, second := b.ObtainAs[Real](
					"the second is e(t) for some t in ⟦0, 1⟧",
					"∃t:real. snd(q) = «circle»(t) ∧ t ∈ ⟦&0, &1⟧",
					By(coordinates, set_basic.InImage.At(circle, unit, b.TermAs[point]("snd(q)"))))
				firstParts := b.Conjuncts(
					first,
					"fst(q) is e(s)",
					"s lies in ⟦0, 1⟧")
				secondParts := b.Conjuncts(
					second,
					"snd(q) is e(t)",
					"t lies in ⟦0, 1⟧")
				image := b.Have(
					"q is the image of (s, t)",
					"«torus»((s, t)) = q",
					Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
					By(firstParts[0], secondParts[0], pairs.PairEta.At(q)))
				b.Show(
					"and (s, t) lies in the square",
					image.RwRev(),
					By(
						firstParts[1],
						secondParts[1],
						set_product.InCross,
						set_image.FunInImage.At(torus, square, b.TermAs[Prod[Real, Real]]("(s, t)"))))
			}))
		rectangle := a.Have(
			"so the map carries the square onto the product of two unit circles",
			"image(«torus», set_cross(⟦&0, &1⟧, ⟦&0, &1⟧)) = "+
				"set_cross(euclidean_sphere(1), euclidean_sphere(1))",
			By(into, onto, set_order.SubsetAntisym, set_basic.SubsetDef))
		circlePoints := a.Have(
			"the points of the circle are the plane's points on the unit circle",
			"⋃euclidean_sphere_topology(1) = euclidean_sphere(1)",
			circleSpaceDef.Rw(),
			BySets(
				topological_space.SubtopologySpace.At(plane, sphere),
				euclidean_topology.EuclideanSpace.At(two),
				UnitCircleEquation))
		onTorus := a.Have(
			"which are the points of the torus",
			"image(«torus», set_cross(⟦&0, &1⟧, ⟦&0, &1⟧)) = "+
				"⋃product_topology(euclidean_sphere_topology(1), euclidean_sphere_topology(1))",
			By(rectangle, circlePoints, product_topology.ProductSpace.At(circleSpace, circleSpace)))
		sameImage := a.Have(
			"two pairs have the same image exactly when both coordinates differ by integers",
			"∀p q:prod(real, real). "+
				"    «torus»(q) = «torus»(p) ⇔ integer(fst(q) - fst(p)) ∧ integer(snd(q) - snd(p))",
			Derive(func(b *Argument) {
				b.FixAs[Prod[Real, Real]]("p")
				b.FixAs[Prod[Real, Real]]("q")
				b.Show(
					"pairs are equal when their coordinates are, and e(x) = e(y) when x − y is an integer",
					By(
						pairs.PairEq.At(
							b.TermAs[point]("«circle»(fst(q))"),
							b.TermAs[point]("«circle»(snd(q))"),
							b.TermAs[point]("«circle»(fst(p))"),
							b.TermAs[point]("«circle»(snd(p))")),
						At(CircleMapFibres, b.TermAs[Real]("fst(q)"), b.TermAs[Real]("fst(p)")),
						At(CircleMapFibres, b.TermAs[Real]("snd(q)"), b.TermAs[Real]("snd(p)"))))
			}))
		planePoints := a.Have(
			"every pair of reals is a point of the plane ℝ × ℝ",
			"⋃product_topology(real_topology, real_topology) = 𝕌",
			Simp(Fwd(product_topology.ProductSpace), Fwd(real_topology.RealSpace)),
			BySets(set_product.InCrossProjections))
		classes := a.Have(
			"so the fibre of the map through p is the class of p modulo the lattice",
			"(λp:prod(real, real). "+
				"    {q:prod(real, real) | "+
				"        q ∈ ⋃product_topology(real_topology, real_topology) ∧ «torus»(q) = «torus»(p)}) = "+
				"(λp:prod(real, real). {q:prod(real, real) | integer(fst(q) - fst(p)) ∧ integer(snd(q) - snd(p))})",
			By(sameImage, planePoints, set_basic.InUniv))
		a.Show(
			"so the quotient of the plane by the lattice is the torus",
			classes.RwRev(),
			By(
				torusSpace,
				separated,
				continuity,
				compactSquare,
				onTorus,
				real_topology.RealTopology,
				product_topology.ProductTopology.At(line, line),
				continuous.FibreQuotientHomeomorphic.At(
					a.TermAs[Set[Set[Prod[Real, Real]]]]("product_topology(real_topology, real_topology)"),
					a.TermAs[Set[Set[pair]]](
						"product_topology(euclidean_sphere_topology(1), euclidean_sphere_topology(1))"),
					torus,
					square)))
	}),
})}
