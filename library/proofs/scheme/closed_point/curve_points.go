// curve_points.go — the Weierstrass datum's closed points, degrees and
// Frobenius counts are those of the smooth finite curve it is, read at its
// charts: the junction between this chapter, which counts inside the
// Weierstrass model, and scheme/smooth_curve, which the Weil theorems read.

package closed_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

// ClosedPointsAreCurveClosedPoints — the closed points of the Weierstrass
// model are the closed points of scheme/smooth_curve read at its charts,
// with the same degrees. A closed point of the curve proper in chart 0 has
// the contraction of its chart-0 component's span for its chart-1 component,
// read off smooth_curve.ClosedPointSecondComponent, and the one closed point
// whole in chart 0 is the origin, its chart-1 component being the maximal
// ideal that holds 1/x. An affine maximal ideal is the first component of a
// closed point of the curve, which is then the elliptic one; the degrees are
// the same quotient's dimension, one at the origin on both sides.
var ClosedPointsAreCurveClosedPoints = closedPointsAreCurveClosedPointsThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointsAreCurveClosedPoints",
	Key:  "prop_f2c67a2647110460",
	Reading: "The degree clause is read only at closed points. The general " +
		"degree is the dimension of the quotient by the component that is a maximal " +
		"ideal: at the origin, chart 1 modulo the origin's ideal, of dimension one.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "(elliptic_closed_point(L, k, x, y, P) ⇔ «closedPoint»(P)) ∧ " +
			"(elliptic_closed_point(L, k, x, y, P) ⇒ " +
			"    elliptic_point_degree(L, k, x, y, P) = " +
			"    curve_closed_degree(field_ring(L), k, «curveChart0», «curveChart1», P))",
		Abbrev: Abbrev{
			{Name: "closedPoint", Text: "curve_closed_point(field_ring(L), " +
				"    «curveChart0», " +
				"    «curveChart1», " +
				"    «curveOverlap»)"},
			{Name: "origin", Text: "weierstrass_origin(L, k, x, y)"},
		},
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			smooth, finite Fact,
		) {
			datum := arg.Simplified(elliptic_curve.SmoothWeierstrassDatum.Read(smooth).AsFact())
			fieldOps := arg.TermAs[FieldOps[A]]("L")
			ring := arg.TermAs[module_record.RingOps[A]]("field_ring(L)")
			chart := arg.TermAs[module_record.RingOps[A]]("restrict_ring(field_ring(L), «curveChart0»)")
			A0 := arg.TermAs[Set[A]]("«curveChart0»")
			A1 := arg.TermAs[Set[A]]("«curveChart1»")
			A01 := arg.TermAs[Set[A]]("«curveOverlap»")
			origin := arg.TermAs[Prod[Set[A], Set[A]]]("«origin»")
			first := arg.TermAs[Set[A]]("fst(P)")
			curve := arg.Have(
				"the Weierstrass datum is a smooth finite curve on its two charts",
				"smooth_finite_curve(L, k, x, «curveChart0», «curveChart1», «curveOverlap»)",
				By(smooth, finite, WeierstrassSmoothFiniteCurve.Read(L).At(k, x, y, a, b)))
			originPoint := arg.Have(
				"the origin, a rational point, is a closed point of the curve of degree one, whole in chart 0",
				"«closedPoint»(«origin») ∧ "+
					"curve_closed_degree(field_ring(L), k, «curveChart0», «curveChart1», «origin») = 1 ∧ "+
					"fst(«origin») = «curveChart0»",
				By(
					datum,
					curve,
					elliptic_curve.OriginMaximal.Read(L).At(k, x, y, a, b),
					smooth_curve.DegreeOneClosedPointsRational.Read(L).At(k, A0, A1, A01, x, origin),
					elliptic_curve.WeierstrassOriginDef.At(fieldOps, k, x, y),
					pairs.Fst))
			proper := arg.Have(
				"a maximal ideal of chart 0 is a proper part of it",
				Statement{
					Binders:    "∀m:set(A).",
					Hypotheses: []string{"maximal_ideal(restrict_ring(field_ring(L), «curveChart0»), m)"},
					Conclusion: "m ⊆ «curveChart0» ∧ m ≠ «curveChart0»",
				},
				Derive(func(c *Argument) {
					m := c.FixAs[Set[A]]("m")
					maximal := c.Assume()
					c.Show(
						"as an ideal it lies in the chart, a subring of L, "+
							"and a maximal ideal of a subring is not all of it",
						BySets(
							maximal,
							curve,
							ring_ideal.MaximalIdealIdeal.At(chart, m),
							ring_ideal.IdealSubset.At(chart, m),
							smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, x),
							ring_ideal.MaximalIdealNotWhole.At(ring, A0, m)))
				}))
			atOrigin := arg.Have(
				"a closed point whole in chart 0 is the origin",
				"∀Q:prod(set(A), set(A)). «closedPoint»(Q) ∧ fst(Q) = «curveChart0» ⇒ Q = «origin»",
				Derive(func(c *Argument) {
					Q := c.FixAs[Prod[Set[A], Set[A]]]("Q")
					given := c.Conjuncts(
						c.Assume(),
						"Q is a closed point",
						"whole in chart 0")
					second := c.TermAs[Set[A]]("snd(Q)")
					holdsInverse := c.Have(
						"its second component is a maximal ideal of chart 1 holding 1/x",
						"maximal_ideal(restrict_ring(field_ring(L), «curveChart1»), snd(Q)) ∧ L.inv(x) ∈ snd(Q)",
						By(
							curve,
							given[0],
							given[1],
							smooth_curve.ClosedPointContraction.Read(L).At(k, A0, A1, A01, x, Q),
							smooth_curve.ClosedPointMaximal.At(ring, A0, A1, A01, Q),
							biaffine_rational_point.PointChartDef.At(A0, A1, Q),
							biaffine_rational_point.PointIdealDef.At(A0, Q)))
					originIdeal := c.Have(
						"so it is the origin's ideal",
						"snd(Q) = snd(«origin»)",
						By(datum, holdsInverse, ClosedPointsOffOrigin.Read(L).At(k, x, y, a, b, second)))
					c.Show(
						"so Q and the origin agree in both components",
						By(Normalized, given[1], originIdeal, originPoint, pairs.PairEta.At(Q), pairs.PairEta.At(origin)))
				}))
			affinePoint := arg.Have(
				"an elliptic closed point other than the origin is a maximal "+
					"ideal of chart 0 paired with the contraction of its span",
				Statement{
					Binders: "∀Q:prod(set(A), set(A)).",
					Hypotheses: []string{
						"elliptic_closed_point(L, k, x, y, Q)",
						"Q ≠ «origin»",
					},
					Conclusion: "maximal_ideal(restrict_ring(field_ring(L), «curveChart0»), fst(Q)) ∧ " +
						"snd(Q) = «curveChart1» ∩ ideal_span(«curveOverlapRing», fst(Q))",
				},
				arg.ForEach(func(Q *Expr[Prod[Set[A], Set[A]]]) Action {
					return By(ClosedPointDef.At(fieldOps, k, x, y, Q))
				}))
			closedPoints := arg.Have(
				"the elliptic closed points are the closed points of the curve",
				"elliptic_closed_point(L, k, x, y, P) ⇔ «closedPoint»(P)",
				Derive(func(c *Argument) {
					c.Iff()
					c.Forward(
						"an elliptic closed point is a closed point of the curve",
						func(d *Argument, elliptic Fact) {
							d.Cases(d.Term("P = «origin»"))
							d.When(
								"P is the origin",
								func(e *Argument, isOrigin Fact) {
									e.Show(
										"the origin is a closed point of the curve",
										By(isOrigin, originPoint))
								})
							d.Otherwise(
								"an affine point is the closed point lying over its maximal ideal",
								func(e *Argument, affine Fact) {
									parts := e.Conjuncts(
										GroupPremises(elliptic, affine, affinePoint.At(P)),
										"fst(P) is a maximal ideal of chart 0",
										"snd(P) is the contraction of its span")
									Q, over := e.ObtainAs[Prod[Set[A], Set[A]]](
										"some closed point Q of the curve lies over fst(P)",
										"∃Q:prod(set(A), set(A)). «closedPoint»(Q) ∧ fst(Q) = fst(P)",
										By(curve, parts[0], smooth_curve.ChartMaximalClosedPoint.Read(L).At(k, A0, A1, A01, x, first)))
									e.Show(
										"Q is proper in chart 0, so its second component is the contraction too, and Q is P",
										By(
											Normalized,
											over,
											parts[0],
											parts[1],
											proper.At(first),
											curve,
											smooth_curve.ClosedPointSecondComponent.Read(L).At(k, A0, A1, A01, x, Q),
											pairs.PairEta.At(P),
											pairs.PairEta.At(Q)))
								})
						})
					c.Backward(
						"a closed point of the curve is an elliptic closed point",
						func(d *Argument, closed Fact) {
							d.Cases(d.Term("fst(P) = «curveChart0»"))
							d.When(
								"whole in chart 0, P is the origin",
								func(e *Argument, whole Fact) {
									e.Show(
										"which is an elliptic closed point",
										By(whole, closed, atOrigin.At(P), ClosedPointDef.At(fieldOps, k, x, y, P)))
								})
							d.Otherwise(
								"proper in chart 0, fst(P) is maximal and snd(P) the contraction of its span",
								func(e *Argument, properFirst Fact) {
									e.Show(
										"which is an affine elliptic closed point",
										By(
											properFirst,
											closed,
											curve,
											smooth_curve.ClosedPointSecondComponent.Read(L).At(k, A0, A1, A01, x, P),
											smooth_curve.ClosedPointMaximal.At(ring, A0, A1, A01, P),
											biaffine_rational_point.PointChartDef.At(A0, A1, P),
											biaffine_rational_point.PointIdealDef.At(A0, P),
											ClosedPointDef.At(fieldOps, k, x, y, P)))
								})
						})
				}))
			degrees := arg.Have(
				"an elliptic closed point has the same degree on the curve",
				Statement{
					Hypotheses: []string{"elliptic_closed_point(L, k, x, y, P)"},
					Conclusion: "elliptic_point_degree(L, k, x, y, P) = " +
						"curve_closed_degree(field_ring(L), k, «curveChart0», «curveChart1», P)",
				},
				Derive(func(c *Argument) {
					elliptic := c.Assume()
					c.Cases(c.Term("P = «origin»"))
					c.When(
						"at the origin both degrees are one",
						func(d *Argument, isOrigin Fact) {
							d.Show(
								"each definition gives one there",
								By(Normalized, isOrigin, originPoint, PointDegreeDef.At(fieldOps, k, x, y, P)))
						})
					c.Otherwise(
						"off the origin both are the dimension of chart 0 modulo fst(P)",
						func(d *Argument, affine Fact) {
							properFirst := d.Have(
								"fst(P) is a maximal ideal of chart 0, so not the chart",
								"fst(P) ≠ «curveChart0»",
								By(elliptic, affine, affinePoint.At(P), proper.At(first)))
							d.Show(
								"both definitions read the quotient of chart 0 by fst(P)",
								By(
									affine,
									properFirst,
									PointDegreeDef.At(fieldOps, k, x, y, P),
									smooth_curve.ClosedPointDegreeDef.At(ring, k, A0, A1, P),
									biaffine_rational_point.PointChartDef.At(A0, A1, P),
									biaffine_rational_point.PointIdealDef.At(A0, P)))
						})
				}))
			arg.Show(
				"both clauses hold",
				By(closedPoints, degrees))
		}),
})}

// FrobeniusCountIsWeightedMultiples — the Frobenius count is the
// weighted-multiples count of sets/weighted_divisors at the general closed
// points weighted by their degrees: the same sum over the same points, zero
// at m = 0 in both.
var FrobeniusCountIsWeightedMultiples = frobeniusCountIsWeightedMultiplesThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusCountIsWeightedMultiples",
	Key:  "prop_bbf2e6cb9ca89fd",
	Reading: "Both sides are defined as zero at m = 0 and as the sum of the degrees " +
		"of the closed points whose degree divides m otherwise, so no hypothesis on m " +
		"is needed; the datum's hypotheses are those of ClosedPointsAreCurveClosedPoints.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀m:num.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "elliptic_frobenius_count(L, k, x, y, m) = " +
			"weighted_multiples( " +
			"    curve_closed_point(field_ring(L), «curveChart0», «curveChart1», «curveOverlap»), " +
			"    curve_closed_degree(field_ring(L), k, «curveChart0», «curveChart1»), " +
			"    m)",
	}, func(
		arg *Argument,
		L field.FieldFact[on.L],
		k *Expr[Set[A]],
		x, y, a, b *Expr[A],
		m *Expr[Nat],
		given Fact,
	) {
		closed := ClosedPointsAreCurveClosedPoints.Read(L).AsFact().At(k, x, y, a, b)
		samePoints := arg.Have(
			"the closed points of degree dividing m are the curve's closed points of degree dividing m",
			"{P:prod(set(A), set(A)) | "+
				"    elliptic_closed_point(L, k, x, y, P) ∧ elliptic_point_degree(L, k, x, y, P) ∣ m} = "+
				"{P:prod(set(A), set(A)) | "+
				"    P ∈ curve_closed_point(field_ring(L), «curveChart0», «curveChart1», «curveOverlap») ∧ "+
				"    curve_closed_degree(field_ring(L), k, «curveChart0», «curveChart1», P) ∣ m}",
			BySets(given, closed))
		arg.Show(
			"both counts sum the degree over those points, and there the two degrees agree",
			Simp(Fwd(FrobeniusCountDef), Fwd(weighted_divisors.WeightedMultiplesDef)),
			By(given, closed, samePoints, nat_sum.Congruence))
	}),
})}

// FrobeniusCountOne — the Frobenius count at m = 1 is the rational point
// count: a degree dividing one is one, so the count sums one over the closed
// points of degree one; on the curve these are the rational ideal pairs, and
// they are finitely many, being closed points of degree at most one, so the
// sum of ones over them is their number.
var FrobeniusCountOne = frobeniusCountOneThm{family.Add(registry.ProofEntry{
	Name: "FrobeniusCountOne",
	Key:  "prop_5632e4ea4bf518e1",
	Reading: "The left side sums the degree over the closed points of degree dividing 1; " +
		"the right side is the cardinality of the rational ideal pairs of PointCountDef, read " +
		"on the overlap ring with the two charts. Both sides read the one Weierstrass model.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "elliptic_frobenius_count(L, k, x, y, 1) = elliptic_point_count(L, k, x, y)",
		Abbrev: Abbrev{
			{Name: "dividingOne", Text: "{P:prod(set(A), set(A)) | " +
				"    elliptic_closed_point(L, k, x, y, P) ∧ elliptic_point_degree(L, k, x, y, P) ∣ 1}"},
			{Name: "rationalPairs", Text: "{P:prod(set(A), set(A)) | " +
				"    biaffine_rational_point(«curveOverlapRing», k, «curveChart0», «curveChart1», P)}"},
		},
	}, func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], given Fact) {
		A0 := arg.TermAs[Set[A]]("«curveChart0»")
		A1 := arg.TermAs[Set[A]]("«curveChart1»")
		A01 := arg.TermAs[Set[A]]("«curveOverlap»")
		curve := arg.Have(
			"the Weierstrass datum is a smooth finite curve on its two charts",
			"smooth_finite_curve(L, k, x, «curveChart0», «curveChart1», «curveOverlap»)",
			By(given, WeierstrassSmoothFiniteCurve.Read(L).At(k, x, y, a, b)))
		rational := arg.Have(
			"the closed points of degree dividing one are the rational ideal pairs",
			"«dividingOne» = «rationalPairs»",
			Simp(Fwd(set_basic.Extension)),
			Derive(func(c *Argument) {
				P := c.FixAs[Prod[Set[A], Set[A]]]("P")
				c.Show(
					"the closed points and degrees are the curve's, and the "+
						"curve's closed points of degree one are its rational pairs",
					BySets(
						given,
						curve,
						ClosedPointsAreCurveClosedPoints.Read(L).At(k, x, y, a, b, P),
						nat_divides.DividesOne.At(c.TermAs[Nat]("elliptic_point_degree(L, k, x, y, P)")),
						smooth_curve.DegreeOneClosedPointsRational.Read(L).At(k, A0, A1, A01, x, P)))
			}))
		bounded := arg.Have(
			"a rational ideal pair is a closed point of the curve of degree one, so of degree at most one",
			"«rationalPairs» ⊆ "+
				"{P:prod(set(A), set(A)) | "+
				"    curve_closed_point(field_ring(L), «curveChart0», «curveChart1», «curveOverlap», P) ∧ "+
				"    curve_closed_degree(field_ring(L), k, «curveChart0», «curveChart1», P) ≤ 1}",
			BySets(curve, smooth_curve.DegreeOneClosedPointsRational.Read(L), nat_order.LessEqRefl))
		finitely := arg.Have(
			"so they are finitely many: the curve has finitely many closed points of degree at most one",
			"finite(«rationalPairs»)",
			By(
				bounded,
				curve,
				smooth_curve.ClosedPointsFiniteByDegree.Read(L).At(k, A0, A1, A01, x),
				finite_set.FiniteSubset))
		ones := arg.Have(
			"a degree dividing one is one, so summing the degree "+
				"over the closed points of degree dividing one sums ones",
			"Σ_{P∈«dividingOne»} elliptic_point_degree(L, k, x, y, P) = Σ_{P∈«dividingOne»} 1",
			By(nat_sum.Congruence, nat_divides.DividesOne))
		arg.Show(
			"one is not zero, so the count sums ones over the closed points of "+
				"degree dividing one, the rational ideal pairs, and counts that finite set",
			Simp(Fwd(FrobeniusCountDef), Fwd(PointCountDef)),
			By(
				finitely,
				rational,
				ones,
				nat_arith.OneNotZero,
				nat_sum.SumOfOnes.At(arg.TermAs[Set[Prod[Set[A], Set[A]]]]("«rationalPairs»"))))
	}),
})}
