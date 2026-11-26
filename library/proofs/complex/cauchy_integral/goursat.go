// goursat.go — Goursat's theorem: a function holomorphic on a closed
// triangle has integral zero round its boundary. The integral round a
// triangle is linear in the function; one of the four quarters of a
// triangle keeps a quarter of its boundary integral at half its perimeter;
// repeating the choice gives nested triangles with a common point, where the
// function is its tangent line to within any ε.

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/registry"
)

// SegmentIntegralSub — along a segment, the integral of the difference of
// two functions continuous there is the difference of their integrals: the
// integrand of f − g is the difference of the integrands, and integrals
// subtract.
var SegmentIntegralSub = segmentIntegralSubThm{family.Add(registry.ProofEntry{
	Name: "SegmentIntegralSub",
	Key:  "prop_5dbf69d8b8789a4e",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀z w:complex.",
		Hypotheses: []string{
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(g, segment_path(z, w, t))",
		},
		Conclusion: "«segInt»(λu:complex. f(u) - g(u), z, w) = «segInt»(f, z, w) - «segInt»(g, z, w)",
	},
		func(
			arg *Argument,
			f, g *Arrow[Complex, Complex],
			z, w *Expr[Complex],
			fContinuous, gContinuous Fact,
		) {
			segment := arg.TermAs[Fun[Real, Complex]]("segment_path(z, w)")
			velocity := arg.TermAs[Fun[Real, Complex]]("λt:real. w - z")
			zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
			ofF := arg.TermAs[Fun[Real, Complex]]("λt:real. f(segment_path(z, w, t)) * (w - z)")
			ofG := arg.TermAs[Fun[Real, Complex]]("λt:real. g(segment_path(z, w, t)) * (w - z)")
			ofDifference := arg.TermAs[Fun[Real, Complex]](
				"λt:real. f(segment_path(z, w, t)) * (w - z) - g(segment_path(z, w, t)) * (w - z)")
			smooth := path_integral.SegmentPiecewiseSmooth.At(z, w)
			I, toI := arg.ObtainAs[Complex](
				"f has an integral I along the segment",
				"∃I:complex. complex_has_integral(λt:real. f(segment_path(z, w, t)) * (w - z), &0, &1, I)",
				By(smooth, fContinuous, path_integral.PathIntegrable.At(f, segment, velocity, zero, one)),
				Named("I"))
			J, toJ := arg.ObtainAs[Complex](
				"and g an integral J",
				"∃J:complex. complex_has_integral(λt:real. g(segment_path(z, w, t)) * (w - z), &0, &1, J)",
				By(smooth, gContinuous, path_integral.PathIntegrable.At(g, segment, velocity, zero, one)),
				Named("J"))
			distributed := arg.Have(
				"the integrand of f − g is the difference of the integrands",
				"(λt:real. (f(segment_path(z, w, t)) - g(segment_path(z, w, t))) * (w - z)) = "+
					"(λt:real. f(segment_path(z, w, t)) * (w - z) - g(segment_path(z, w, t)) * (w - z))",
				Funext(),
				ByArith())
			arg.Show(
				"so the integral of f − g is I − J, integrals subtracting",
				Unfold(path_integral.PathIntegralDef),
				distributed.Rw(),
				By(
					toI,
					toJ,
					path_integral.ComplexHasIntegralSub.At(ofF, ofG, zero, one, I, J),
					path_integral.ComplexHasIntegralValue.At(ofF, zero, one, I),
					path_integral.ComplexHasIntegralValue.At(ofG, zero, one, J),
					path_integral.ComplexHasIntegralValue.At(ofDifference, zero, one, arg.TermAs[Complex]("I - J"))))
		}),
})}

// BoundaryIntegralSub — round a triangle, the integral of the difference of
// two functions continuous on the triangle is the difference of their
// integrals: each side lies in the triangle, and along it the integrals
// subtract.
var BoundaryIntegralSub = boundaryIntegralSubThm{family.Add(registry.ProofEntry{
	Name: "BoundaryIntegralSub",
	Key:  "prop_60e4eff92e73bac0",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀a b c:complex.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)",
			"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(g, z)",
		},
		Conclusion: "«boundaryInt»(λu:complex. f(u) - g(u), a, b, c) = " +
			"«boundaryInt»(f, a, b, c) - «boundaryInt»(g, a, b, c)",
	},
		func(
			arg *Argument,
			f, g *Arrow[Complex, Complex],
			a, b, c *Expr[Complex],
			fContinuous, gContinuous Fact,
		) {
			triangle := arg.TermAs[Set[Complex]]("«triangle»(a, b, c)")
			convex := At(TriangleConvex, a, b, c)
			alongF := arg.Have(
				"f is continuous along a segment between two points of the triangle, the triangle being convex",
				Statement{
					Binders: "∀z w:complex.",
					Hypotheses: []string{
						"z ∈ «triangle»(a, b, c)",
						"w ∈ «triangle»(a, b, c)",
					},
					Conclusion: "∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(f, segment_path(z, w, t))",
				},
				By(fContinuous, convex, At(ContinuousAlongSegment, triangle, f)))
			alongG := arg.Have(
				"and so is g",
				Statement{
					Binders: "∀z w:complex.",
					Hypotheses: []string{
						"z ∈ «triangle»(a, b, c)",
						"w ∈ «triangle»(a, b, c)",
					},
					Conclusion: "∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(g, segment_path(z, w, t))",
				},
				By(gContinuous, convex, At(ContinuousAlongSegment, triangle, g)))
			vertices := arg.Conjuncts(
				TriangleVertices.At(a, b, c),
				"a lies in the triangle",
				"so does b",
				"and so does c")
			arg.Show(
				"side by side the integrals subtract",
				ByArith(
					vertices[0],
					vertices[1],
					vertices[2],
					alongF.At(a, b),
					alongF.At(b, c),
					alongF.At(c, a),
					alongG.At(a, b),
					alongG.At(b, c),
					alongG.At(c, a),
					SegmentIntegralSub.At(f, g, a, b),
					SegmentIntegralSub.At(f, g, b, c),
					SegmentIntegralSub.At(f, g, c, a)))
		}),
})}

// TriangleQuarter — the quarter step of Goursat's argument: for f continuous
// on a triangle, one of the four triangles its midpoints cut it into keeps
// at least a quarter of its boundary integral; its vertices lie in the
// triangle, and it has half the perimeter. The boundary integral is the sum
// of the four quarters', so by the triangle inequality they cannot all be
// below a quarter of it. The quarters' vertices are vertices and midpoints
// of the triangle, all in it; the sides of a corner quarter are half the
// triangle's sides, those of the middle quarter minus half.
var TriangleQuarter = triangleQuarterThm{family.Add(registry.ProofEntry{
	Name: "TriangleQuarter",
	Key:  "prop_52eca18a956fc4e0",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a b c:complex.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)",
		},
		Conclusion: "∃p q r:complex. " +
			"    p ∈ «triangle»(a, b, c) ∧ " +
			"    q ∈ «triangle»(a, b, c) ∧ " +
			"    r ∈ «triangle»(a, b, c) ∧ " +
			"    |«boundaryInt»(f, a, b, c)| ≤ &4 * |«boundaryInt»(f, p, q, r)| ∧ " +
			"    «perimeter»(p, q, r) = «perimeter»(a, b, c) / &2",
		Abbrev: Abbrev{
			{Name: "m_ab", Text: "segment_path(a, b, &1 / &2)"},
			{Name: "m_bc", Text: "segment_path(b, c, &1 / &2)"},
			{Name: "m_ca", Text: "segment_path(a, c, &1 / &2)"},
		},
	},
		func(arg *Argument, f *Arrow[Complex, Complex], a, b, c *Expr[Complex], continuous Fact) {
			half := arg.TermAs[Real]("&1 / &2")
			mAB, mBC, mCA :=
				arg.TermAs[Complex]("«m_ab»"), arg.TermAs[Complex]("«m_bc»"), arg.TermAs[Complex]("«m_ca»")
			vertices := arg.Conjuncts(
				TriangleVertices.At(a, b, c),
				"a lies in the triangle",
				"so does b",
				"and so does c")
			midpoints := arg.Have(
				"so do the midpoints of the sides, the triangle being convex",
				"«m_ab» ∈ «triangle»(a, b, c) ∧ «m_bc» ∈ «triangle»(a, b, c) ∧ «m_ca» ∈ «triangle»(a, b, c)",
				By(
					vertices[0],
					vertices[1],
					vertices[2],
					TriangleConvex.At(a, b, c, a, b, half),
					TriangleConvex.At(a, b, c, b, c, half),
					TriangleConvex.At(a, b, c, a, c, half)))
			realHalves := arg.Have(
				"two halves make a whole",
				"&1 / &2 + &1 / &2 = &1",
				ByArith())
			halves := arg.Have(
				"in ℂ too",
				"&(&1 / &2) + &(&1 / &2) = &1",
				By(realHalves, complex_field.OfRealAdd.At(half, half)))
			sides := arg.Have(
				"the sides of the corner quarters are halves of the "+
					"triangle's sides, and those of the middle quarter minus halves",
				"«m_ab» - a = &(&1 / &2) * (b - a) ∧ "+
					"«m_ca» - «m_ab» = &(&1 / &2) * (c - b) ∧ "+
					"a - «m_ca» = &(&1 / &2) * (a - c) ∧ "+
					"b - «m_ab» = &(&1 / &2) * (b - a) ∧ "+
					"«m_bc» - b = &(&1 / &2) * (c - b) ∧ "+
					"«m_ab» - «m_bc» = &(&1 / &2) * (a - c) ∧ "+
					"«m_bc» - «m_ca» = &(&1 / &2) * (b - a) ∧ "+
					"c - «m_bc» = &(&1 / &2) * (c - b) ∧ "+
					"«m_ca» - c = &(&1 / &2) * (a - c) ∧ "+
					"«m_ca» - «m_bc» = &(-(&1 / &2)) * (b - a) ∧ "+
					"«m_ab» - «m_ca» = &(-(&1 / &2)) * (c - b) ∧ "+
					"«m_bc» - «m_ab» = &(-(&1 / &2)) * (a - c)",
				Simp(
					Fwd(path_integral.SegmentPathDef),
					Fwd(real_ring.RealSubDef),
					Fwd(complex_field.OfRealAdd),
					Fwd(complex_field.OfRealNeg)),
				ByArith(
					Scaled(arg.TermAs[Complex]("b - a"), halves),
					Scaled(arg.TermAs[Complex]("c - b"), halves),
					Scaled(arg.TermAs[Complex]("a - c"), halves)))
			scale := arg.Have(
				"a triangle whose sides are k times the triangle's has |k| times its perimeter",
				Statement{
					Binders: "∀p q r:complex. ∀k:real.",
					Hypotheses: []string{
						"q - p = &k * (b - a)",
						"r - q = &k * (c - b)",
						"p - r = &k * (a - c)",
					},
					Conclusion: "«perimeter»(p, q, r) = |k| * «perimeter»(a, b, c)",
				},
				Derive(func(d *Argument) {
					d.FixAs[Complex]("p")
					d.FixAs[Complex]("q")
					d.FixAs[Complex]("r")
					d.FixAs[Real]("k")
					sides := d.Conjuncts(
						d.Assume(),
						"the side from p to q is k·(b − a)",
						"the side from q to r is k·(c − b)",
						"the side from r to p is k·(a − c)")
					d.Show(
						"the modulus of a product is the product of the moduli",
						sides[0].Rw(),
						sides[1].Rw(),
						sides[2].Rw(),
						ByArith())
				}))
			scaled := arg.Have(
				"so each quarter's perimeter is |1/2| times the triangle's, or |−1/2| times for the middle one",
				"«perimeter»(a, «m_ab», «m_ca») = |&1 / &2| * «perimeter»(a, b, c) ∧ "+
					"«perimeter»(«m_ab», b, «m_bc») = |&1 / &2| * «perimeter»(a, b, c) ∧ "+
					"«perimeter»(«m_ca», «m_bc», c) = |&1 / &2| * «perimeter»(a, b, c) ∧ "+
					"«perimeter»(«m_bc», «m_ca», «m_ab») = |-(&1 / &2)| * «perimeter»(a, b, c)",
				By(
					sides,
					scale.At(a, mAB, mCA, half),
					scale.At(mAB, b, mBC, half),
					scale.At(mCA, mBC, c, half),
					scale.At(mBC, mCA, mAB, arg.TermAs[Real]("-(&1 / &2)"))))
			perimeters := arg.Have(
				"that is, each quarter has half the perimeter",
				"«perimeter»(a, «m_ab», «m_ca») = «perimeter»(a, b, c) / &2 ∧ "+
					"«perimeter»(«m_ab», b, «m_bc») = «perimeter»(a, b, c) / &2 ∧ "+
					"«perimeter»(«m_ca», «m_bc», c) = «perimeter»(a, b, c) / &2 ∧ "+
					"«perimeter»(«m_bc», «m_ca», «m_ab») = «perimeter»(a, b, c) / &2",
				ByArith(scaled))
			total := arg.Have(
				"the boundary integral is the sum of the quarters', so at most the sum of their sizes",
				"|«boundaryInt»(f, a, b, c)| ≤ "+
					"|«boundaryInt»(f, a, «m_ab», «m_ca»)| + "+
					"|«boundaryInt»(f, «m_ab», b, «m_bc»)| + "+
					"|«boundaryInt»(f, «m_ca», «m_bc», c)| + "+
					"|«boundaryInt»(f, «m_bc», «m_ca», «m_ab»)|",
				ByArith(
					continuous,
					TriangleQuadrisection.At(f, a, b, c),
					complex_abs.AbsTriangle.At(
						arg.TermAs[Complex](
							"«boundaryInt»(f, a, «m_ab», «m_ca») + "+
								"«boundaryInt»(f, «m_ab», b, «m_bc») + "+
								"«boundaryInt»(f, «m_ca», «m_bc», c)"),
						arg.TermAs[Complex]("«boundaryInt»(f, «m_bc», «m_ca», «m_ab»)")),
					complex_abs.AbsTriangle.At(
						arg.TermAs[Complex]("«boundaryInt»(f, a, «m_ab», «m_ca») + «boundaryInt»(f, «m_ab», b, «m_bc»)"),
						arg.TermAs[Complex]("«boundaryInt»(f, «m_ca», «m_bc», c)")),
					complex_abs.AbsTriangle.At(
						arg.TermAs[Complex]("«boundaryInt»(f, a, «m_ab», «m_ca»)"),
						arg.TermAs[Complex]("«boundaryInt»(f, «m_ab», b, «m_bc»)"))))
			arg.Cases(arg.Term("|«boundaryInt»(f, a, b, c)| ≤ &4 * |«boundaryInt»(f, a, «m_ab», «m_ca»)|"))
			arg.When(
				"the corner quarter at a will do if it keeps a quarter of the integral",
				func(d *Argument, keeps Fact) {
					d.Take(a)
					d.Take(mAB)
					d.Take(mCA)
					d.Show(
						"its vertices lie in the triangle and it has half the perimeter",
						By(vertices[0], vertices[1], vertices[2], midpoints, keeps, perimeters))
				})
			arg.Otherwise(
				"otherwise one of the other three does",
				func(d *Argument, notA Fact) {
					d.Cases(d.Term("|«boundaryInt»(f, a, b, c)| ≤ &4 * |«boundaryInt»(f, «m_ab», b, «m_bc»)|"))
					d.When(
						"the corner quarter at b will do if it keeps a quarter",
						func(e *Argument, keeps Fact) {
							e.Take(mAB)
							e.Take(b)
							e.Take(mBC)
							e.Show(
								"its vertices lie in the triangle and it has half the perimeter",
								By(vertices[0], vertices[1], vertices[2], midpoints, keeps, perimeters))
						})
					d.Otherwise(
						"otherwise the corner quarter at c or the middle one does",
						func(e *Argument, notB Fact) {
							e.Cases(e.Term("|«boundaryInt»(f, a, b, c)| ≤ &4 * |«boundaryInt»(f, «m_ca», «m_bc», c)|"))
							e.When(
								"the corner quarter at c will do if it keeps a quarter",
								func(g *Argument, keeps Fact) {
									g.Take(mCA)
									g.Take(mBC)
									g.Take(c)
									g.Show(
										"its vertices lie in the triangle and it has half the perimeter",
										By(vertices[0], vertices[1], vertices[2], midpoints, keeps, perimeters))
								})
							e.Otherwise(
								"otherwise the middle quarter keeps a quarter, the four together keeping the whole",
								func(g *Argument, notC Fact) {
									keeps := g.Have(
										"the middle quarter keeps at least a quarter of the integral",
										"|«boundaryInt»(f, a, b, c)| ≤ &4 * |«boundaryInt»(f, «m_bc», «m_ca», «m_ab»)|",
										ByArith(total, notA, notB, notC))
									g.Take(mBC)
									g.Take(mCA)
									g.Take(mAB)
									g.Show(
										"its vertices lie in the triangle and it has half the perimeter",
										By(vertices[0], vertices[1], vertices[2], midpoints, keeps, perimeters))
								})
						})
				})
		}),
})}

// TriangleNest — the nested triangles of Goursat's argument: for f
// continuous on a triangle there are triangles T(n) with vertices p(n), q(n),
// r(n), all inside the triangle and each inside the one before, whose
// boundary integrals are at least 4⁻ⁿ times the triangle's and whose
// perimeters are 2⁻ⁿ times its perimeter. The quarter step applies to every
// triangle inside the triangle, f being continuous there; a quarter is chosen
// for each, the choice is iterated from the triangle by recursion, and an
// induction carries the three properties along, each quarter having its
// vertices, so itself, in the triangle before.
var TriangleNest = triangleNestThm{family.Add(registry.ProofEntry{
	Name: "TriangleNest",
	Key:  "prop_6a53f03c8e4d4a4a",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a b c:complex.",
		Hypotheses: []string{
			"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)",
		},
		Conclusion: "∃p q r:(num → complex). " +
			"    (∀n:num. «triangle»(p(n), q(n), r(n)) ⊆ «triangle»(a, b, c)) ∧ " +
			"    (∀n:num. «triangle»(p(n + 1), q(n + 1), r(n + 1)) ⊆ «triangle»(p(n), q(n), r(n))) ∧ " +
			"    (∀n:num. " +
			"        |«boundaryInt»(f, a, b, c)| * real_pow(&1 / &2, n) * real_pow(&1 / &2, n) ≤ " +
			"        |«boundaryInt»(f, p(n), q(n), r(n))|) ∧ " +
			"    (∀n:num. «perimeter»(p(n), q(n), r(n)) = «perimeter»(a, b, c) * real_pow(&1 / &2, n))",
		Abbrev: Abbrev{
			{Name: "first", Text: "λn:num. fst(X(n))"},
			{Name: "second", Text: "λn:num. fst(snd(X(n)))"},
			{Name: "third", Text: "λn:num. snd(snd(X(n)))"},
		},
	},
		func(arg *Argument, f *Arrow[Complex, Complex], a, b, c *Expr[Complex], continuous Fact) {
			quarterInside := arg.Have(
				"the quarter step applies to every triangle inside the triangle, f being continuous there",
				Statement{
					Binders: "∀u v w:complex.",
					Hypotheses: []string{
						"«triangle»(u, v, w) ⊆ «triangle»(a, b, c)",
					},
					Conclusion: "∃p q r:complex. " +
						"    p ∈ «triangle»(u, v, w) ∧ " +
						"    q ∈ «triangle»(u, v, w) ∧ " +
						"    r ∈ «triangle»(u, v, w) ∧ " +
						"    |«boundaryInt»(f, u, v, w)| ≤ &4 * |«boundaryInt»(f, p, q, r)| ∧ " +
						"    «perimeter»(p, q, r) = «perimeter»(u, v, w) / &2",
				},
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					v := d.FixAs[Complex]("v")
					w := d.FixAs[Complex]("w")
					inside := d.Assume()
					onIt := d.Have(
						"f is continuous at the points of the smaller triangle",
						"∀z:complex. z ∈ «triangle»(u, v, w) ⇒ complex_continuous_at(f, z)",
						By(d.Unfolded(inside, set_basic.SubsetDef), continuous))
					d.Show(
						"so the quarter step applies to it",
						By(onIt, TriangleQuarter.At(f, u, v, w)))
				}))
			_, _, _, chosen := arg.Obtain3(
				"choose such a quarter for every triangle inside the triangle",
				"∃U V W:(complex → complex → complex → complex). ∀u v w:complex. "+
					"    «triangle»(u, v, w) ⊆ «triangle»(a, b, c) ⇒ "+
					"    U(u, v, w) ∈ «triangle»(u, v, w) ∧ "+
					"    V(u, v, w) ∈ «triangle»(u, v, w) ∧ "+
					"    W(u, v, w) ∈ «triangle»(u, v, w) ∧ "+
					"    |«boundaryInt»(f, u, v, w)| ≤ &4 * |«boundaryInt»(f, U(u, v, w), V(u, v, w), W(u, v, w))| ∧ "+
					"    «perimeter»(U(u, v, w), V(u, v, w), W(u, v, w)) = «perimeter»(u, v, w) / &2",
				By(quarterInside))
			_, recursion := arg.ObtainAs[Fun[Nat, Prod[Complex, Prod[Complex, Complex]]]](
				"iterate the choice from the triangle: X(0) is (a, "+
					"(b, c)), and X(n + 1) the quarter chosen for X(n)",
				"∃X:(num → prod(complex, prod(complex, complex))). "+
					"    X(0) = (a, (b, c)) ∧ "+
					"    ∀n:num. "+
					"        X(n + 1) = "+
					"        (U(fst(X(n)), fst(snd(X(n))), snd(snd(X(n)))), "+
					"            (V(fst(X(n)), fst(snd(X(n))), snd(snd(X(n)))), "+
					"                W(fst(X(n)), fst(snd(X(n))), snd(snd(X(n))))))",
				By(
					peano.Recursion.At(
						arg.TermAs[Fun2[Prod[Complex, Prod[Complex, Complex]], Nat, Prod[Complex, Prod[Complex, Complex]]]](
							"λx:prod(complex, prod(complex, complex)). λn:num. "+
								"    (U(fst(x), fst(snd(x)), snd(snd(x))), "+
								"        (V(fst(x), fst(snd(x)), snd(snd(x))), W(fst(x), fst(snd(x)), snd(snd(x)))))"),
						arg.TermAs[Prod[Complex, Prod[Complex, Complex]]]("(a, (b, c))")),
					nat_arith.Add1))
			threads := arg.Conjuncts(
				recursion,
				"X(0) is the triangle",
				"X(n + 1) is the quarter chosen for X(n)")
			invariant := arg.Have(
				"every X(n) lies in the triangle, keeps 4⁻ⁿ of its boundary integral and has 2⁻ⁿ of its perimeter",
				"∀n:num. "+
					"    «triangle»(«first»(n), «second»(n), «third»(n)) ⊆ «triangle»(a, b, c) ∧ "+
					"    |«boundaryInt»(f, a, b, c)| * real_pow(&1 / &2, n) * real_pow(&1 / &2, n) ≤ "+
					"    |«boundaryInt»(f, «first»(n), «second»(n), «third»(n))| ∧ "+
					"    «perimeter»(«first»(n), «second»(n), «third»(n)) = "+
					"    «perimeter»(a, b, c) * real_pow(&1 / &2, n)",
				Derive(func(d *Argument) {
					d.Induct("n")
					d.Base(
						"X(0) is the triangle itself",
						threads[0].Rw(),
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
						ByArith(set_order.SubsetRefl.At(d.TermAs[Set[Complex]]("«triangle»(a, b, c)"))))
					d.Step(
						"X(n + 1) is the quarter chosen for X(n), which lies in the triangle",
						func(e *Argument, ih Fact) {
							n := e.TermAs[Nat]("n")
							was := e.Conjuncts(
								ih,
								"X(n) lies in the triangle",
								"it keeps 4⁻ⁿ of the boundary integral",
								"and has 2⁻ⁿ of the perimeter")
							quarter := e.Conjuncts(
								GroupPremises(
									was[0],
									chosen.At(
										e.TermAs[Complex]("«first»(n)"),
										e.TermAs[Complex]("«second»(n)"),
										e.TermAs[Complex]("«third»(n)"))),
								"the first vertex of its quarter lies in X(n)",
								"so does the second",
								"and the third",
								"the quarter keeps a quarter of its boundary integral",
								"and has half its perimeter")
							e.Do(Simp(Fwd(nat_arith.Add1)), threads[1].At(n).Rw(), Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)))
							inside := e.Have(
								"the quarter lies in X(n), so in the triangle",
								"«triangle»(U(«first»(n), «second»(n), «third»(n)), "+
									"    V(«first»(n), «second»(n), «third»(n)), "+
									"    W(«first»(n), «second»(n), «third»(n))) ⊆ "+
									"«triangle»(a, b, c)",
								By(
									was[0],
									quarter[0],
									quarter[1],
									quarter[2],
									TriangleSubset.At(e.TermAs[Complex]("«first»(n)"),
										e.TermAs[Complex]("«second»(n)"),
										e.TermAs[Complex]("«third»(n)"),
										e.TermAs[Complex]("U(«first»(n), «second»(n), «third»(n))"),
										e.TermAs[Complex]("V(«first»(n), «second»(n), «third»(n))"),
										e.TermAs[Complex]("W(«first»(n), «second»(n), «third»(n))")),
									set_order.SubsetTrans.At(
										e.TermAs[Set[Complex]](
											"«triangle»(U(«first»(n), «second»(n), «third»(n)), "+
												"    V(«first»(n), «second»(n), «third»(n)), "+
												"    W(«first»(n), «second»(n), «third»(n)))"),
										e.TermAs[Set[Complex]]("«triangle»(«first»(n), «second»(n), «third»(n))"),
										e.TermAs[Set[Complex]]("«triangle»(a, b, c)"))))
							e.Show(
								"a quarter of 4⁻ⁿ is 4⁻⁽ⁿ⁺¹⁾, and half of 2⁻ⁿ is 2⁻⁽ⁿ⁺¹⁾",
								Simp(Fwd(real_pow.PowAddOne)),
								ByArith(inside, was[1], was[2], quarter[3], quarter[4]))
						})
				}))
			nested := arg.Have(
				"each X(n + 1), a quarter of X(n), lies in X(n)",
				"∀n:num. "+
					"    «triangle»(«first»(n + 1), «second»(n + 1), «third»(n + 1)) ⊆ "+
					"    «triangle»(«first»(n), «second»(n), «third»(n))",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]("n")
					quarter := d.Conjuncts(
						GroupPremises(
							d.Conjuncts(
								invariant.At(n),
								"X(n) lies in the triangle",
								"it keeps 4⁻ⁿ of the boundary integral",
								"and has 2⁻ⁿ of the perimeter")[0],
							chosen.At(
								d.TermAs[Complex]("«first»(n)"),
								d.TermAs[Complex]("«second»(n)"),
								d.TermAs[Complex]("«third»(n)"))),
						"the first vertex of its quarter lies in X(n)",
						"so does the second",
						"and the third",
						"the quarter keeps a quarter of its boundary integral",
						"and has half its perimeter")
					d.Do(threads[1].At(n).Rw(), Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)))
					d.Show(
						"a triangle whose vertices lie in X(n) lies in it",
						By(
							quarter[0],
							quarter[1],
							quarter[2],
							TriangleSubset.At(d.TermAs[Complex]("«first»(n)"),
								d.TermAs[Complex]("«second»(n)"),
								d.TermAs[Complex]("«third»(n)"),
								d.TermAs[Complex]("U(«first»(n), «second»(n), «third»(n))"),
								d.TermAs[Complex]("V(«first»(n), «second»(n), «third»(n))"),
								d.TermAs[Complex]("W(«first»(n), «second»(n), «third»(n))"))))
				}))
			arg.Take(arg.TermAs[Fun[Nat, Complex]]("«first»"))
			arg.Take(arg.TermAs[Fun[Nat, Complex]]("«second»"))
			arg.Take(arg.TermAs[Fun[Nat, Complex]]("«third»"))
			arg.Show(
				"the vertices of the X(n) are the triangles sought",
				By(invariant, nested))
		}),
})}

// Goursat — a function holomorphic on a closed triangle has integral zero
// round its boundary. Having a derivative at every point, f is continuous
// on the triangle, so the nested triangles T(n) exist: inside the triangle,
// each inside the one before, keeping 4⁻ⁿ of the boundary integral at 2⁻ⁿ of
// the perimeter P. They are closed and shrink, so they have a common point
// z₀, a point of the triangle, where f has a derivative l. Given ε, f is its
// tangent line at z₀ to within ε·|z − z₀| on a disc about z₀ holding T(N)
// once N is large; the tangent line, being linear, has integral zero round
// T(N), so the boundary integral of f round T(N) is at most ε times the
// square of its perimeter, and scaled back by 4ᴺ that of the triangle is at
// most P²·ε. As ε is arbitrary, its size is at most 0, so it is zero.
var Goursat = goursatThm{family.Add(registry.ProofEntry{
	Name: "Goursat",
	Key:  "prop_4b545b5435cfe495",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀a b c:complex.",
		Hypotheses: []string{
			"holomorphic_on(«triangle»(a, b, c), f)",
		},
		Conclusion: "«boundaryInt»(f, a, b, c) = &0",
		Abbrev: Abbrev{
			{Name: "P", Text: "«perimeter»(a, b, c)"},
		},
	},
		func(arg *Argument, f *Arrow[Complex, Complex], a, b, c *Expr[Complex], holomorphic Fact) {
			half := arg.TermAs[Real]("&1 / &2")
			derivatives := arg.Unfolded(holomorphic, complex_derivative.HolomorphicOnDef)
			continuous := arg.Have(
				"f is continuous on the triangle, having a derivative at each of its points",
				"∀z:complex. z ∈ «triangle»(a, b, c) ⇒ complex_continuous_at(f, z)",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					inside := d.Assume()
					l, derivative := d.UnpackAs[Complex](GroupPremises(inside, derivatives.At(z)), "l")
					d.Show(
						"a function with a derivative at a point is continuous there",
						By(derivative, complex_derivative.DerivativeContinuous.At(f, z, l)))
				}))
			_, _, _, nest := arg.Obtain3(
				"the nested triangles T(n) with vertices p(n), q(n), r(n)",
				"∃p q r:(num → complex). "+
					"    (∀n:num. «triangle»(p(n), q(n), r(n)) ⊆ «triangle»(a, b, c)) ∧ "+
					"    (∀n:num. «triangle»(p(n + 1), q(n + 1), r(n + 1)) ⊆ «triangle»(p(n), q(n), r(n))) ∧ "+
					"    (∀n:num. "+
					"        |«boundaryInt»(f, a, b, c)| * real_pow(&1 / &2, n) * real_pow(&1 / &2, n) ≤ "+
					"        |«boundaryInt»(f, p(n), q(n), r(n))|) ∧ "+
					"    (∀n:num. «perimeter»(p(n), q(n), r(n)) = «P» * real_pow(&1 / &2, n))",
				By(continuous, TriangleNest.At(f, a, b, c)))
			nested := arg.Conjuncts(
				nest,
				"every T(n) lies in the triangle",
				"each lies in the one before",
				"T(n) keeps 4⁻ⁿ of the boundary integral",
				"and has 2⁻ⁿ of the perimeter")
			halfSmall := arg.Have(
				"1/2 is less than 1 in size",
				"|&1 / &2| < &1",
				ByArith())
			shrinking := arg.Have(
				"the perimeters P·2⁻ⁿ tend to 0",
				"(λn:num. «P» * real_pow(&1 / &2, n)) ⟶ «P» * &0",
				By(
					halfSmall,
					real_sequences.PowerTendsToZero.At(half),
					real_sequences.LimitScale.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(&1 / &2, n)"),
						arg.TermAs[Real]("&0"),
						arg.TermAs[Real]("«P»"))))
			eventually := arg.Unfolded(shrinking, real_sequences.RealConvergesToDef)
			closedNested := arg.Have(
				"the T(n) are closed, non-empty and nested",
				"∀n:num. "+
					"    closed_in(metric_topology(𝕌, complex_dist), «triangle»(p(n), q(n), r(n))) ∧ "+
					"    ¬(«triangle»(p(n), q(n), r(n)) = ∅) ∧ "+
					"    «triangle»(p(n + 1), q(n + 1), r(n + 1)) ⊆ «triangle»(p(n), q(n), r(n))",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]("n")
					pn, qn, rn := d.TermAs[Complex]("p(n)"), d.TermAs[Complex]("q(n)"), d.TermAs[Complex]("r(n)")
					closed := d.Have(
						"T(n) is closed",
						"closed_in(metric_topology(𝕌, complex_dist), «triangle»(p(n), q(n), r(n)))",
						Simp(Rev(complex_topology.ComplexTopologyDef)),
						By(TriangleClosed.At(pn, qn, rn)))
					corners := d.Conjuncts(
						TriangleVertices.At(pn, qn, rn),
						"p(n) lies in T(n)",
						"so does q(n)",
						"and so does r(n)")
					nonempty := d.Have(
						"T(n) holds its vertex p(n), so is non-empty",
						"¬(«triangle»(p(n), q(n), r(n)) = ∅)",
						BySets(corners[0]))
					d.Show(
						"and T(n + 1) lies in T(n)",
						By(closed, nonempty, nested[1].At(n)))
				}))
			small := arg.Have(
				"for every ε > 0 some T(n) has all its points within ε of one another",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃n:num. ∀x y:complex. " +
						"    x ∈ «triangle»(p(n), q(n), r(n)) ∧ y ∈ «triangle»(p(n), q(n), r(n)) ⇒ complex_dist(x, y) < ε",
				},
				Derive(func(d *Argument) {
					d.FixAs[Real]("ε")
					positive := d.Assume()
					N, beyond := d.ObtainAs[Nat](
						"past some N the perimeter P·2⁻ⁿ is below ε",
						"∃N:num. ∀n:num. N ≤ n ⇒ |«P» * real_pow(&1 / &2, n) - «P» * &0| < ε",
						By(eventually, positive))
					d.Take(N)
					x := d.FixAs[Complex]("x")
					y := d.FixAs[Complex]("y")
					both := d.Conjuncts(
						d.Assume(),
						"x lies in T(N)",
						"and so does y")
					d.Show(
						"two points of T(N) are at most its perimeter P·2⁻ᴺ apart",
						Unfold(complex_topology.ComplexDistDef),
						ByArith(
							TriangleDiameter.At(
								d.TermAs[Complex]("p(N)"), d.TermAs[Complex]("q(N)"), d.TermAs[Complex]("r(N)"), x, y),
							both[0],
							both[1],
							nested[3].At(N),
							beyond.At(N)))
				}))
			z0, common := arg.ObtainAs[Complex](
				"closed, non-empty, nested and shrinking in the complete plane, the T(n) have a common point z₀",
				"∃z₀:complex. ∀n:num. z₀ ∈ «triangle»(p(n), q(n), r(n))",
				By(
					complex_topology.ComplexMetric,
					complex_topology.ComplexComplete,
					closedNested,
					small,
					complete_metric.CantorIntersection.At(
						arg.TermAs[Set[Complex]]("𝕌"),
						arg.TermAs[Fun2[Complex, Complex, Real]]("complex_dist"),
						arg.TermAs[Fun2[Nat, Complex, Bool]]("λn:num. «triangle»(p(n), q(n), r(n))"))))
			zero := arg.TermAs[Nat]("0")
			inTriangle := arg.Have(
				"z₀ lies in the triangle, as T(0) does",
				"z₀ ∈ «triangle»(a, b, c)",
				By(common.At(zero), arg.Unfolded(nested[0].At(zero), set_basic.SubsetDef)))
			l, derivative := arg.UnpackAs[Complex](GroupPremises(inTriangle, derivatives.At(z0)), "l")
			linear := arg.TermAs[Fun[Complex, Complex]]("λz:complex. f(z₀) - l * z₀ + l * z")
			estimate := arg.Have(
				"for every ε > 0 the boundary integral is at most P²·ε",
				"∀ε:real. &0 < ε ⇒ |«boundaryInt»(f, a, b, c)| ≤ «P» * «P» * ε",
				Derive(func(d *Argument) {
					d.FixAs[Real]("ε")
					positive := d.Assume()
					_, near := d.ObtainAs[Real](
						"near z₀, f is its tangent line to within ε·|z − z₀|",
						"∃δ:real. "+
							"    &0 < δ ∧ "+
							"    ∀z:complex. &0 < |z - z₀| ∧ |z - z₀| < δ ⇒ |f(z) - f(z₀) - l * (z - z₀)| < ε * |z - z₀|",
						By(derivative, positive, complex_derivative.DerivativeIncrement.At(f, z0, l)))
					tangent := d.Conjuncts(
						near,
						"δ is positive",
						"within δ of z₀, f is its tangent line to within ε·|z − z₀|")
					N, beyond := d.ObtainAs[Nat](
						"past some N the perimeter P·2⁻ⁿ is below δ",
						"∃N:num. ∀n:num. N ≤ n ⇒ |«P» * real_pow(&1 / &2, n) - «P» * &0| < δ",
						By(eventually, tangent[0]))
					pN, qN, rN := d.TermAs[Complex]("p(N)"), d.TermAs[Complex]("q(N)"), d.TermAs[Complex]("r(N)")
					centre := d.Have(
						"z₀ lies in T(N)",
						"z₀ ∈ «triangle»(p(N), q(N), r(N))",
						By(common.At(N)))
					onTN := d.Have(
						"f is continuous at the points of T(N), which lie in the triangle",
						"∀z:complex. z ∈ «triangle»(p(N), q(N), r(N)) ⇒ complex_continuous_at(f, z)",
						By(d.Unfolded(nested[0].At(N), set_basic.SubsetDef), continuous))
					lineContinuous := d.Have(
						"the tangent line is continuous",
						Statement{
							Binders: "∀w:complex.",
							Hypotheses: []string{
								"w ∈ «triangle»(p(N), q(N), r(N))",
							},
							Conclusion: "complex_continuous_at(λz:complex. f(z₀) - l * z₀ + l * z, w)",
						},
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("w")
							e.Assume()
							e.Show(
								"a constant plus a constant times z is continuous",
								By(
									complex_topology.ContinuousAtConst.At(z, e.TermAs[Complex]("f(z₀) - l * z₀")),
									complex_topology.ContinuousAtConst.At(z, l),
									complex_topology.ContinuousAtId.At(z),
									complex_topology.ContinuousAtMul.At(
										e.TermAs[Fun[Complex, Complex]]("λz:complex. l"),
										e.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
										z),
									complex_topology.ContinuousAtAdd.At(
										e.TermAs[Fun[Complex, Complex]]("λz:complex. f(z₀) - l * z₀"),
										e.TermAs[Fun[Complex, Complex]]("λz:complex. l * z"),
										z)))
						}))
					deviation := d.Have(
						"on T(N), f minus its tangent line is continuous and at most ε times the perimeter of T(N)",
						Statement{
							Binders: "∀w:complex.",
							Hypotheses: []string{
								"w ∈ «triangle»(p(N), q(N), r(N))",
							},
							Conclusion: "complex_continuous_at(λu:complex. f(u) - (f(z₀) - l * z₀ + l * u), w) ∧ " +
								"|f(w) - (f(z₀) - l * z₀ + l * w)| ≤ ε * «perimeter»(p(N), q(N), r(N))",
						},
						Derive(func(e *Argument) {
							z := e.FixAs[Complex]("w")
							inside := e.Assume()
							stillContinuous := e.Have(
								"f minus its tangent line is continuous at w",
								"complex_continuous_at(λu:complex. f(u) - (f(z₀) - l * z₀ + l * u), w)",
								By(
									GroupPremises(inside, onTN.At(z)),
									GroupPremises(inside, lineContinuous.At(z)),
									complex_topology.ContinuousAtSub.At(f, linear, z)))
							closeBy := e.Have(
								"w is at most the perimeter of T(N) from z₀, which is below δ",
								"|w - z₀| ≤ «perimeter»(p(N), q(N), r(N)) ∧ |w - z₀| < δ",
								ByArith(TriangleDiameter.At(pN, qN, rN, z, z0), inside, centre, nested[3].At(N), beyond.At(N)))
							regrouped := e.Have(
								"f minus its tangent line at w is f(w) − f(z₀) − l·(w − z₀)",
								"f(w) - (f(z₀) - l * z₀ + l * w) = f(w) - f(z₀) - l * (w - z₀)",
								ByArith())
							e.Cases(e.Term("w = z₀"))
							e.When(
								"at z₀ itself f and its tangent line agree",
								func(g *Argument, same Fact) {
									vanishes := g.Have(
										"f(z₀) − f(z₀) − l·(z₀ − z₀) is 0",
										"f(z₀) - f(z₀) - l * (z₀ - z₀) = &0",
										ByArith())
									g.Show(
										"the difference is 0 there",
										regrouped.Rw(),
										same.Rw(),
										vanishes.Rw(),
										ByArith(
											stillContinuous,
											same,
											positive,
											closeBy,
											complex_abs.AbsOfReal.At(g.TermAs[Real]("&0")),
											complex_abs.AbsNonneg.At(g.TermAs[Complex]("q(N) - p(N)")),
											complex_abs.AbsNonneg.At(g.TermAs[Complex]("r(N) - q(N)")),
											complex_abs.AbsNonneg.At(g.TermAs[Complex]("p(N) - r(N)"))))
								})
							e.Otherwise(
								"elsewhere it is within ε·|w − z₀|, at most ε times the perimeter",
								func(g *Argument, apart Fact) {
									away := g.Have(
										"w is not z₀, so at positive distance from it",
										"&0 < |w - z₀|",
										ByArith(apart, complex_abs.AbsPosIffNonzero.At(g.TermAs[Complex]("w - z₀"))))
									g.Show(
										"w is within δ of z₀ without being z₀",
										regrouped.Rw(),
										ByArith(stillContinuous, closeBy, positive, away, tangent[1].At(z)))
								})
						}))
					sameIntegral := d.Have(
						"the tangent line, being linear, has integral 0 round T(N), so f minus it has the integral of f",
						"«boundaryInt»(λu:complex. f(u) - (f(z₀) - l * z₀ + l * u), p(N), q(N), r(N)) = "+
							"«boundaryInt»(f, p(N), q(N), r(N))",
						ByArith(
							onTN,
							lineContinuous,
							BoundaryIntegralSub.At(f, linear, pN, qN, rN),
							TriangleBoundaryLinear.At(d.TermAs[Complex]("f(z₀) - l * z₀"), l, pN, qN, rN)))
					aroundTN := d.Have(
						"so round T(N) the integral of f is at most ε times the square of its perimeter P·2⁻ᴺ",
						"|«boundaryInt»(f, p(N), q(N), r(N))| ≤ "+
							"ε * («P» * real_pow(&1 / &2, N)) * («P» * real_pow(&1 / &2, N))",
						nested[3].At(N).RwRev(),
						sameIntegral.RwRev(),
						By(
							deviation,
							TriangleBoundaryBound.At(
								d.TermAs[Fun[Complex, Complex]]("λu:complex. f(u) - (f(z₀) - l * z₀ + l * u)"),
								pN,
								qN,
								rN,
								d.TermAs[Real]("ε * «perimeter»(p(N), q(N), r(N))"))))
					scaled := d.Have(
						"so the boundary integral, scaled by 4⁻ᴺ, is at most ε·P² scaled by 4⁻ᴺ",
						"|«boundaryInt»(f, a, b, c)| * (real_pow(&1 / &2, N) * real_pow(&1 / &2, N)) ≤ "+
							"ε * («P» * «P») * (real_pow(&1 / &2, N) * real_pow(&1 / &2, N))",
						ByArith(aroundTN, nested[2].At(N)))
					d.Show(
						"4⁻ᴺ being positive, the boundary integral is at most P²·ε",
						ByArith(scaled, positive, real_pow.PowPos.At(half, N)))
				}))
			integral := arg.TermAs[Complex]("«boundaryInt»(f, a, b, c)")
			nonpositive := arg.Have(
				"a size at most P²·ε for every ε in ⟬0, 1⟧ is at most 0",
				"|«boundaryInt»(f, a, b, c)| ≤ &0",
				By(
					estimate,
					real_order_ring.ZeroLessThanOne,
					real_order_field.NonposOfSmallMultiples.At(
						arg.TermAs[Real]("|«boundaryInt»(f, a, b, c)|"),
						arg.TermAs[Real]("«P» * «P»"),
						arg.TermAs[Real]("&1"))))
			arg.Show(
				"so the boundary integral is 0",
				ByArith(nonpositive, complex_abs.AbsNonneg.At(integral), complex_abs.AbsEqZero.At(integral)))
		}),
})}
