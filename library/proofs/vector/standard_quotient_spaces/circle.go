// circle.go — the line wound onto the unit circle by e(t) = (cos 2πt,
// sin 2πt), and the circle as the line modulo the integers. The unit circle
// of the plane is cut out by x² + y² = 1; e takes its values on it, is
// continuous, already reaches every point of it from ⟦0, 1⟧, and gives two
// reals the same point exactly when they differ by an integer, so it
// identifies ℝ/ℤ with S¹.

package standard_quotient_spaces

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_polynomial"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// UnitCircleEquation — the unit circle is the set of vectors of the plane
// whose two coordinates have squares summing to 1. The form at a vector of
// the plane is the sum over its two coordinates, which the sum's recursion
// unrolls; a norm of 1 squares to a form of 1, and a form of 1 has the
// root 1.
var UnitCircleEquation = unitCircleEquationThm{family.Add(registry.ProofEntry{
	Name: "UnitCircleEquation",
	Key:  "prop_c7815260c104c8ec",
	Build: family.Theorem(
		"∀u:(num → real). u ∈ euclidean_sphere(1) ⇔ vec⟨2⟩(u) ∧ u(0) * u(0) + u(1) * u(1) = &1",
		func(a *Argument, u *Arrow[Nat, Real]) {
			plane := a.VecAt[Real](a.TermAs[Nat]("2"), "u")
			steps := a.Conjuncts(
				real_sum.BelowClauses.At(a.TermAs[Fun[Nat, Real]]("λi:num. u(i) * u(i)")),
				"the sum over no index is 0",
				"one index more adds its term")
			successors := a.Have(
				"2 and 1 are the successors of 1 and 0",
				"suc(1) = 2 ∧ suc(0) = 1",
				ByArith())
			squares := a.Have(
				"the form at u is the sum of the squares of its two coordinates",
				"⟪u, u⟫_2 = u(0) * u(0) + u(1) * u(1)",
				ByArith(
					steps[1].At(a.TermAs[Nat]("1")),
					steps[1].At(a.TermAs[Nat]("0")),
					steps[0],
					successors,
					euclidean.DotIsSum.At(plane, plane)))
			unitNorm := a.Have(
				"so u has norm 1 exactly when the squares of its coordinates sum to 1",
				"‖u‖_2 = &1 ⇔ u(0) * u(0) + u(1) * u(1) = &1",
				Derive(func(b *Argument) {
					one := b.TermAs[Real]("&1")
					b.Iff()
					b.Forward(
						"a norm of 1 squares to a form of 1",
						func(c *Argument, normOne Fact) {
							c.Show(
								"the form is the square of the norm",
								ByArith(normOne, squares, euclidean.NormPow2.At(plane)))
						})
					b.Backward(
						"a form of 1 has the root 1",
						func(c *Argument, sumOne Fact) {
							c.Show(
								"the norm is the root of the form, and 1 is the root of 1",
								ByArith(sumOne, squares, euclidean.VecNormDef.At(plane), real_sqrt.SqrtUnique.At(one, one)))
						})
				}))
			twoDimensions := a.Have(
				"the circle S¹ sits in the plane, of dimension 1 + 1 = 2",
				"1 + 1 = 2",
				ByArith())
			a.Show(
				"the unit circle is the plane's vectors of norm 1",
				Simp(Fwd(euclidean_topology.EuclideanSphereDef), Fwd(twoDimensions)),
				By(unitNorm))
		}),
})}

// CircleMapOnCircle — the circle map e(t) = (cos 2πt, sin 2πt) takes its
// values on the unit circle: e(t) is a vector of the plane, and
// cos² 2πt + sin² 2πt = 1.
var CircleMapOnCircle = circleMapOnCircleThm{family.Add(registry.ProofEntry{
	Name: "CircleMapOnCircle",
	Key:  "prop_9d984709de475152",
	Build: family.Theorem(Statement{
		Binders:    "∀t:real.",
		Conclusion: "«circle»(t) ∈ euclidean_sphere(1)",
		Abbrev: Abbrev{
			{Name: "circle", Text: "λt:real. λi:num. " +
				"    COND(i = 0, cos(&2 * pi * t), COND(i = 1, sin(&2 * pi * t), &0))"},
		},
	}, func(a *Argument, t *Expr[Real]) {
		plane := a.Have(
			"e(t) is a vector of the plane: its coordinates from 2 on are 0",
			"vec⟨2⟩(«circle»(t))",
			Unfold(vec_space.VecDef),
			ByArith())
		squares := a.Have(
			"its coordinates are cos 2πt and sin 2πt, whose squares sum to 1",
			"«circle»(t)(0) * «circle»(t)(0) + «circle»(t)(1) * «circle»(t)(1) = &1",
			ByArith(real_trigonometry.SinSquareAddCosSquare.At(a.TermAs[Real]("&2 * pi * t"))))
		a.Show(
			"so e(t) satisfies the equation of the unit circle",
			By(plane, squares, At(UnitCircleEquation, a.TermAs[Fun[Nat, Real]]("«circle»(t)"))))
	}),
})}

// CircleMapContinuous — the circle map is a continuous map of the line to
// the unit circle. A map into the plane is continuous as its two
// coordinates are, and here they are t ↦ cos 2πt and t ↦ sin 2πt, the
// cosine and the sine after the polynomial t ↦ 2πt; a continuous map into
// the plane with its values on the circle is continuous into the circle.
var CircleMapContinuous = circleMapContinuousThm{family.Add(registry.ProofEntry{
	Name: "CircleMapContinuous",
	Key:  "prop_5bae9b7c796c6bae",
	Build: family.Theorem(Statement{
		Conclusion: "continuous_map(real_topology, euclidean_sphere_topology(1), «circle»)",
		Abbrev: Abbrev{
			{Name: "circle", Text: "λt:real. λi:num. " +
				"    COND(i = 0, cos(&2 * pi * t), COND(i = 1, sin(&2 * pi * t), &0))"},
		},
	}, func(a *Argument) {
		type point = Fun[Nat, Real]
		line := a.TermAs[Set[Set[Real]]]("real_topology")
		circle := a.TermAs[Fun2[Real, Nat, Real]]("«circle»")
		linear := a.Have(
			"t ↦ 2πt is continuous, a polynomial",
			"continuous_map(real_topology, real_topology, λt:real. &2 * pi * t)",
			By(
				real_continuous.PolynomialFunctionContinuous,
				real_polynomial.ScalarLeft.At(a.TermAs[Fun[Real, Real]]("λx:real. x"), a.TermAs[Real]("&2 * pi")),
				real_polynomial.Id))
		cosine := a.Have(
			"so is t ↦ cos 2πt, the cosine after it",
			"continuous_map(real_topology, real_topology, λt:real. cos(&2 * pi * t))",
			By(
				continuous.Compose.Read(linear).At(line, a.TermAs[Fun[Real, Real]]("real_cos")),
				real_trigonometry.CosContinuous,
				functions.ComposeApply))
		sine := a.Have(
			"and t ↦ sin 2πt, the sine after it",
			"continuous_map(real_topology, real_topology, λt:real. sin(&2 * pi * t))",
			By(
				continuous.Compose.Read(linear).At(line, a.TermAs[Fun[Real, Real]]("real_sin")),
				real_trigonometry.SinContinuous,
				functions.ComposeApply))
		coordinates := a.Have(
			"each coordinate of e below 2 is continuous",
			"∀i:num. i < 2 ⇒ continuous_map(real_topology, real_topology, λt:real. «circle»(t)(i))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("i")
				below := b.Assume()
				notFirst := b.Unless(
					b.Term("i = 0"),
					"coordinate 0 is t ↦ cos 2πt",
					Given(func(c *Argument, first Fact) {
						c.Show(
							"which is continuous",
							By(first, cosine))
					}))
				second := b.Have(
					"a coordinate below 2 other than 0 is coordinate 1",
					"i = 1",
					ByArith(below, notFirst))
				b.Show(
					"coordinate 1 is t ↦ sin 2πt, which is continuous",
					By(second, sine, nat_arith.OneNotZero))
			}))
		planar := a.Have(
			"e takes its values in the plane, being on the unit circle",
			"∀t:real. vec⟨2⟩(«circle»(t))",
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				b.Show(
					"a point of the unit circle is a vector of the plane",
					By(At(CircleMapOnCircle, t), At(UnitCircleEquation, b.TermAs[point]("«circle»(t)"))))
			}))
		circleSpaceDef := a.Have(
			"the circle as a space is the plane's subspace on the unit circle",
			"euclidean_sphere_topology(1) = subtopology(euclidean_topology(2), euclidean_sphere(1))",
			By(euclidean_topology.EuclideanSphereTopologyDef.At(a.TermAs[Nat]("1"))))
		a.Show(
			"so e is continuous into the plane, coordinate by coordinate, with its values on the unit circle",
			circleSpaceDef.Rw(),
			By(
				Normalized,
				coordinates,
				planar,
				CircleMapOnCircle,
				real_topology.RealTopology,
				continuous.IntoSubtopology.At(
					line,
					a.TermAs[Set[Set[point]]]("euclidean_topology(2)"),
					circle,
					a.TermAs[Set[point]]("euclidean_sphere(1)")),
				euclidean_topology.ContinuousIffCoordinates.At(a.TermAs[Nat]("2"), line, circle)))
	}),
})}

// CircleMapFibres — two reals have the same point on the circle exactly
// when they differ by an integer. The points agree when their coordinates
// do, that is when cos and sin agree at 2πs and 2πt, which is when
// (2πs − 2πt)/2π = s − t is an integer (real_trigonometry.CosSinEqIff).
var CircleMapFibres = circleMapFibresThm{family.Add(registry.ProofEntry{
	Name: "CircleMapFibres",
	Key:  "prop_3448f7f874875823",
	Build: family.Theorem(Statement{
		Binders:    "∀s t:real.",
		Conclusion: "«circle»(s) = «circle»(t) ⇔ integer(s - t)",
		Abbrev: Abbrev{
			{Name: "circle", Text: "λt:real. λi:num. " +
				"    COND(i = 0, cos(&2 * pi * t), COND(i = 1, sin(&2 * pi * t), &0))"},
		},
	}, func(a *Argument, s, t *Expr[Real]) {
		angleS, angleT := a.TermAs[Real]("&2 * pi * s"), a.TermAs[Real]("&2 * pi * t")
		turns := a.Have(
			"the angles 2πs and 2πt are s − t turns apart",
			"(&2 * pi * s - &2 * pi * t) / (&2 * pi) = s - t",
			ByArith(real_trigonometry.PiBounds))
		a.Iff()
		a.Forward(
			"equal points have equal coordinates, so the angles are a whole number of turns apart",
			func(b *Argument, equal Fact) {
				b.Show(
					"cos and sin agree at 2πs and 2πt",
					By(equal, turns, nat_arith.OneNotZero, real_trigonometry.CosSinEqIff.At(angleS, angleT)))
			})
		a.Backward(
			"a whole number of turns leaves cos and sin unchanged, so every coordinate agrees",
			func(b *Argument, integral Fact) {
				b.Show(
					"cos and sin agree at 2πs and 2πt",
					By(integral, turns, real_trigonometry.CosSinEqIff.At(angleS, angleT)))
			})
	}),
})}

// CircleMapOnto — the circle map carries ⟦0, 1⟧ onto the unit circle. Its
// values lie on the circle (CircleMapOnCircle); and a point u of the circle
// has u(0)² + u(1)² = 1, so it is (cos s, sin s) for some s in ⟦0, 2π⟭
// (real_trigonometry.CircleParametrization), and then u is e(s/2π)
// coordinate by coordinate, both being 0 from 2 on.
var CircleMapOnto = circleMapOntoThm{family.Add(registry.ProofEntry{
	Name: "CircleMapOnto",
	Key:  "prop_f08244e410546b3f",
	Build: family.Theorem(Statement{
		Conclusion: "image(«circle», ⟦&0, &1⟧) = euclidean_sphere(1)",
		Abbrev: Abbrev{
			{Name: "circle", Text: "λt:real. λi:num. " +
				"    COND(i = 0, cos(&2 * pi * t), COND(i = 1, sin(&2 * pi * t), &0))"},
		},
	}, func(a *Argument) {
		circle := a.TermAs[Fun2[Real, Nat, Real]]("«circle»")
		interval := a.TermAs[Set[Real]]("⟦&0, &1⟧")
		into := a.Have(
			"e carries ⟦0, 1⟧ into the circle",
			"image(«circle», ⟦&0, &1⟧) ⊆ euclidean_sphere(1)",
			By(CircleMapOnCircle, set_image.ImageSubsetIff))
		onto := a.Have(
			"every point of the circle is e(t) for some t in ⟦0, 1⟧",
			"∀u:(num → real). u ∈ euclidean_sphere(1) ⇒ u ∈ image(«circle», ⟦&0, &1⟧)",
			Derive(func(b *Argument) {
				u := b.FixAs[Fun[Nat, Real]]("u")
				onCircle := b.Assume()
				equation := b.Conjuncts(
					b.Have(
						"u is a vector of the plane on the circle x² + y² = 1",
						"vec⟨2⟩(u) ∧ u(0) * u(0) + u(1) * u(1) = &1",
						By(onCircle, At(UnitCircleEquation, u))),
					"u is a vector of the plane",
					"the squares of its coordinates sum to 1")
				_, angle := b.ObtainAs[Real](
					"so u is (cos s, sin s) for some s in ⟦0, 2π⟭",
					"∃s:real. &0 ≤ s ∧ s < &2 * pi ∧ cos(s) = u(0) ∧ sin(s) = u(1)",
					By(
						equation[1],
						real_trigonometry.CircleParametrization.At(b.TermAs[Real]("u(0)"), b.TermAs[Real]("u(1)"))))
				parts := b.Conjuncts(
					angle,
					"0 ≤ s",
					"s < 2π",
					"cos s is u(0)",
					"sin s is u(1)")
				t := b.TermAs[Real]("s / (&2 * pi)")
				scale := b.Have(
					"2π · s/2π is s",
					"&2 * pi * (s / (&2 * pi)) = s",
					ByArith(real_trigonometry.PiBounds))
				bounds := b.Have(
					"s/2π lies in ⟦0, 1⟧, as s lies in ⟦0, 2π⟭",
					"&0 ≤ s / (&2 * pi) ∧ s / (&2 * pi) ≤ &1",
					ByArith(parts[0], parts[1], real_trigonometry.PiBounds))
				vanish := b.Unfolded(equation[0], vec_space.VecDef)
				equal := b.Have(
					"e(s/2π) is u, coordinate by coordinate",
					"«circle»(s / (&2 * pi)) = u",
					Funext(),
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						notFirst := c.Unless(
							c.Term("i = 0"),
							"coordinate 0 is cos s = u(0)",
							Given(func(d *Argument, first Fact) {
								d.Show(
									"at 0 both are the cosine",
									By(Normalized, first, parts[2], scale))
							}))
						notSecond := c.Unless(
							c.Term("i = 1"),
							"coordinate 1 is sin s = u(1)",
							Given(func(d *Argument, second Fact) {
								d.Show(
									"at 1 both are the sine",
									By(second, parts[3], scale, nat_arith.OneNotZero))
							}))
						c.Show(
							"from 2 on both coordinates are 0",
							ByArith(notFirst, notSecond, vanish.At(i)))
					}))
				b.Show(
					"so u is e(t) for t = s/2π in ⟦0, 1⟧",
					By(equal, bounds, set_image.FunInImage.At(circle, interval, t)))
			}))
		a.Show(
			"the image and the circle each contain the other",
			By(into, onto, set_order.SubsetAntisym, set_basic.SubsetDef))
	}),
})}

// CircleQuotient — the circle is the line modulo the integers, ℝ/ℤ ≅ S¹.
// The circle map is continuous onto the circle, a Hausdorff space, already
// from the compact interval ⟦0, 1⟧ (CircleMapOnto); the fibre of the map
// through x is the class of the reals an integer away from x
// (CircleMapFibres), so the quotient of the line by these classes is the
// circle (continuous.FibreQuotientHomeomorphic).
var CircleQuotient = circleQuotientThm{family.Add(registry.ProofEntry{
	Name: "CircleQuotient",
	Key:  "prop_29f53adcc831fcae",
	Build: family.Theorem(Statement{
		Conclusion: "homeomorphic(quotient_topology(real_topology, λx:real. {y:real | integer(y - x)}), " +
			"    euclidean_sphere_topology(1))",
		Abbrev: Abbrev{
			{Name: "circle", Text: "λt:real. λi:num. " +
				"    COND(i = 0, cos(&2 * pi * t), COND(i = 1, sin(&2 * pi * t), &0))"},
		},
	}, func(a *Argument) {
		type point = Fun[Nat, Real]
		two := a.TermAs[Nat]("2")
		line := a.TermAs[Set[Set[Real]]]("real_topology")
		plane := a.TermAs[Set[Set[point]]]("euclidean_topology(2)")
		sphere := a.TermAs[Set[point]]("euclidean_sphere(1)")
		circleSpaceDef := a.Have(
			"the circle as a space is the plane's subspace on the unit circle",
			"euclidean_sphere_topology(1) = subtopology(euclidean_topology(2), euclidean_sphere(1))",
			By(euclidean_topology.EuclideanSphereTopologyDef.At(a.TermAs[Nat]("1"))))
		space := a.Have(
			"the circle is a space, a subspace of the plane",
			"is_topology(subtopology(euclidean_topology(2), euclidean_sphere(1)))",
			By(topological_space.SubtopologyTopology, euclidean_topology.EuclideanTopology.At(two)))
		separated := a.Have(
			"and a Hausdorff one, as the plane is",
			"hausdorff(subtopology(euclidean_topology(2), euclidean_sphere(1)))",
			By(
				topological_space.HausdorffSubtopology.At(plane, sphere),
				euclidean_topology.EuclideanHausdorff.At(two)))
		onto := a.Have(
			"e carries ⟦0, 1⟧ onto the points of the circle, which are the plane's points on the unit circle",
			"image(«circle», ⟦&0, &1⟧) = ⋃subtopology(euclidean_topology(2), euclidean_sphere(1))",
			BySets(
				topological_space.SubtopologySpace.At(plane, sphere),
				euclidean_topology.EuclideanSpace.At(two),
				UnitCircleEquation,
				CircleMapOnto))
		classes := a.Have(
			"the fibre of e through x is the class of x, the reals an integer away from it",
			"(λx:real. {y:real | y ∈ ⋃real_topology ∧ «circle»(y) = «circle»(x)}) = "+
				"(λx:real. {y:real | integer(y - x)})",
			BySets(real_topology.RealSpace, CircleMapFibres))
		mapInto := a.Have(
			"e is continuous into the circle, the subspace of the plane",
			"continuous_map(real_topology, subtopology(euclidean_topology(2), euclidean_sphere(1)), «circle»)",
			circleSpaceDef.RwRev(),
			By(CircleMapContinuous))
		a.Show(
			"so the quotient of the line by the classes is the circle",
			circleSpaceDef.Rw(),
			classes.RwRev(),
			By(
				space,
				separated,
				onto,
				real_topology.RealTopology,
				mapInto,
				real_topology.ClosedIntervalCompact.At(a.TermAs[Real]("&0"), a.TermAs[Real]("&1")),
				continuous.FibreQuotientHomeomorphic.At(
					line,
					a.TermAs[Set[Set[point]]]("subtopology(euclidean_topology(2), euclidean_sphere(1))"),
					a.TermAs[Fun2[Real, Nat, Real]]("«circle»"),
					a.TermAs[Set[Real]]("⟦&0, &1⟧"))))
	}),
})}
