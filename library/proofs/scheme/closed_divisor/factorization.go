// factorization.go — the invertible pairs inside the two charts are the ideal
// pairs of the effective closed divisors, the ideal pair of E being the pair of
// −E. Such a pair other than the structure pair lies under a closed point,
// dividing by the point lowers its colength over the constants, and closed
// points are prime and pairwise incomparable, which forces the exponents.

package closed_divisor

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/invertible_fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// InvertibleChartMember — an invertible fractional ideal of a chart holds a
// nonzero member of the chart: it holds a nonzero multiple c of the whole chart,
// and the chart holds 1, so c is that member.
var InvertibleChartMember = invertibleChartMemberThm{family.Add(registry.ProofEntry{
	Name: "InvertibleChartMember",
	Key:  "prop_f95930e5d453b04b",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀J:set(A).",
		Hypotheses: []string{"«scCurve»", "invertible_fractional(field_ring(L), A₀, J)"},
		Conclusion: "∃c:A. c ∈ J ∧ c ∈ A₀ ∧ c ≠ L.zero",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			J *Expr[Set[A]],
			curve, invertible Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			subring := a.Have(
				"the chart is a subring of L",
				"subring(field_ring(L), A₀)",
				By(curve, smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t)))
			principal := a.Have(
				"a nonzero multiple of the chart lies in J",
				"∃c:A. c ∈ A₀ ∧ c ≠ L.zero ∧ image(L.mul(c), A₀) ⊆ J",
				By(
					subring,
					a.Unfolded(
						a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef), algebraic_curve.CurveOverLineDef),
					invertible,
					invertible_fractional_ideal.InvertibleContainsPrincipal.Read(L).At(A0, J)))
			c, multiple := a.UnpackAs[A](principal)
			chosen := a.Conjuncts(
				multiple,
				"c lies in the chart",
				"c is nonzero",
				"its multiples lie in J")
			inField := a.Have(
				"so c is an element of L",
				"c ∈ L.carrier",
				BySets(chosen[0], subring, comm_ring.SubringSubset.At(ring, A0)))
			one := a.Have(
				"and 1 lies in the chart",
				"L.one ∈ A₀",
				By(subring, comm_ring.SubringOne.At(ring, A0)))
			times := a.Have(
				"c times 1 is c",
				"c * L.one = c",
				ByArith(L, inField))
			held := a.Have(
				"so c, its own multiple of 1, lies in J",
				"c ∈ J",
				BySets(chosen[2], one, times))
			a.Take(c)
			a.Show(
				"c is a nonzero member of J and of the chart",
				By(held, chosen[0], chosen[1]))
		}),
})}

// InvertibleChartIdeal — an invertible fractional ideal inside a chart is a
// nonzero ideal of the chart: it is a module over the chart, and a nonzero
// multiple of the whole chart lies in it.
var InvertibleChartIdeal = invertibleChartIdealThm{family.Add(registry.ProofEntry{
	Name: "InvertibleChartIdeal",
	Key:  "prop_727b9ed85e44d931",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀H:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"invertible_fractional(field_ring(L), A₀, H)",
			"H ⊆ A₀",
		},
		Conclusion: "ring_ideal(restrict_ring(field_ring(L), A₀), H) ∧ H ≠ {L.zero}",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			H *Expr[Set[A]],
			curve, invertible, inChart Fact,
		) {
			a.Have(
				"a module over the chart inside the chart is an ideal",
				"ring_ideal(restrict_ring(field_ring(L), A₀), H)",
				By(
					curve,
					smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t),
					invertible,
					inChart,
					fractional_ideal.IntegralIdealFractional.Read(L).At(A0, H),
					fractional_ideal.InvertibleFractionalDef.At(a.TermAs[RingOps[A]]("field_ring(L)"), A0, H)))
			_, member := a.UnpackAs[A](
				GroupPremises(curve, invertible, InvertibleChartMember.Read(L).At(k, A0, A1, A01, t, H)))
			a.Show(
				"H holds a nonzero member of the chart, so it is not the zero ideal",
				BySets(member))
		}),
})}

// PairBelowClosedPoint — an invertible pair inside the charts that lies under a
// closed point in a chart where the point is proper lies under it in the other
// chart: where the point lies on both charts its other component is the
// contraction of the ideal the first generates, and PairBelowContraction applies.
var PairBelowClosedPoint = pairBelowClosedPointThm{family.Add(registry.ProofEntry{
	Name: "PairBelowClosedPoint",
	Key:  "prop_55807d100af57454",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀I P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(I)",
			"snd(I) ⊆ A₁",
			"«scPoint»(P)",
			"fst(P) ≠ A₀",
			"fst(I) ⊆ fst(P)",
		},
		Conclusion: "snd(I) ⊆ snd(P)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			I, P *Expr[_IdealPair],
			curve, invertible, inChart1, point, proper, below Fact,
		) {
			a.Cases(a.TermAs[Bool]("snd(P) = A₁"))
			a.When(
				"where P is off chart 1 its component is the whole chart",
				func(b *Argument, whole Fact) {
					b.Show(
						"snd(I) lies in chart 1",
						whole.Rw(),
						By(inChart1))
				})
			a.Otherwise(
				"where P lies on both charts snd(P) is cut from the ideal fst(P) generates",
				func(b *Argument, notWhole Fact) {
					fstP := b.TermAs[Set[A]]("fst(P)")
					contracted := b.Have(
						"snd(P) is chart 1 inside the ideal fst(P) generates in the overlap",
						"snd(P) = A₁ ∩ ideal_span(restrict_ring(field_ring(L), A₀₁), fst(P))",
						By(
							curve,
							point,
							proper,
							notWhole,
							smooth_curve.ClosedPointContraction.Read(L).At(k, A0, A1, A01, t, P)))
					pair := b.Conjuncts(
						b.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef),
						"fst(I) is invertible",
						"snd(I) is invertible",
						"I is a lattice pair")[2]
					line := b.Have(
						"the overlap is a subring of L holding chart 0",
						"subring(field_ring(L), A₀₁) ∧ A₀ ⊆ A₀₁",
						By(
							b.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef),
							algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
					inChart0 := b.Have(
						"fst(P) lies in chart 0",
						"fst(P) ⊆ A₀",
						By(
							curve,
							b.Unfolded(point, smooth_curve.CurveClosedPointDef),
							ChartPointInvertible.Read(L).At(k, A0, A1, A01, t, fstP)))
					inOverlap := b.Have(
						"so fst(P) lies in the overlap",
						"fst(P) ⊆ A₀₁",
						BySets(inChart0, line))
					b.Show(
						"so snd(I) lies in the contraction",
						By(
							L,
							line,
							pair,
							inChart1,
							inOverlap,
							contracted,
							below,
							lattice_pair_twist.PairBelowContraction.Read(L).At(A0, A1, A01, I, P)))
				})
		}),
})}

// ProperChartBelowPoint — an invertible pair inside the charts whose first
// component is proper lies under a closed point proper in chart 0: the
// first component lies in a maximal ideal of the chart, and that ideal is the
// first component of a closed point.
var ProperChartBelowPoint = properChartBelowPointThm{family.Add(registry.ProofEntry{
	Name: "ProperChartBelowPoint",
	Key:  "prop_3d65c7f7bed44f13",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀I:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(I)",
			"fst(I) ⊆ A₀",
			"snd(I) ⊆ A₁",
			"fst(I) ≠ A₀",
		},
		Conclusion: "∃P:prod(set(A), set(A)). " +
			"    «scPoint»(P) ∧ fst(P) ≠ A₀ ∧ fst(I) ⊆ fst(P) ∧ snd(I) ⊆ snd(P)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			I *Expr[_IdealPair],
			curve, invertible, inChart0, inChart1, proper Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			fstI := a.TermAs[Set[A]]("fst(I)")
			subring := a.Conjuncts(
				GroupPremises(curve, smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t)),
				"the constants are a subfield of L",
				"the constants lie in the chart",
				"the chart is a subring of L")[2]
			chartRing := a.Have(
				"the chart is a commutative ring",
				"comm_ring_on(«chart»)",
				By(curve, smooth_curve.ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			ideal := a.Have(
				"fst(I) is an ideal of the chart",
				"ring_ideal(«chart», fst(I))",
				By(
					curve,
					a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef),
					inChart0,
					InvertibleChartIdeal.Read(L).At(k, A0, A1, A01, t, fstI)))
			m, maximal := a.ObtainAs[Set[A]](
				"a proper ideal lies in a maximal ideal",
				"∃m:set(A). maximal_ideal(«chart», m) ∧ fst(I) ⊆ m",
				By(
					ideal,
					proper,
					inChart0,
					ring_ideal.IdealOneIff.Read(chartRing).At(fstI),
					ring_ideal.ExistsMaximalAbove.Read(chartRing).At(fstI)))
			above := a.Conjuncts(
				maximal,
				"m is maximal in the chart",
				"m lies above fst(I)")
			unique := a.Have(
				"m is the first component of a closed point",
				"∃!P:prod(set(A), set(A)). «scPoint»(P) ∧ fst(P) = m",
				By(curve, above[0], smooth_curve.ChartMaximalClosedPoint.Read(L).At(k, A0, A1, A01, t, m)))
			P, center := a.UnpackAs[_IdealPair](unique, "P")
			over := a.Conjuncts(
				a.Have(
					"P is that point",
					"«scPoint»(P) ∧ fst(P) = m",
					By(center.At(P))),
				"P is a closed point",
				"its first component is m")
			notWhole := a.Have(
				"m, holding no 1, is not the chart",
				"fst(P) ≠ A₀",
				By(
					Normalized,
					over[1],
					above[0],
					subring,
					comm_ring.SubringOne.At(ring, A0),
					ring_ideal.MaximalIdealProper.At(a.TermAs[RingOps[A]]("«chart»"), m)))
			a.Take(P)
			a.Show(
				"P lies above the pair in chart 1 as well",
				By(
					Normalized,
					over[0],
					over[1],
					above[1],
					notWhole,
					curve,
					invertible,
					inChart1,
					PairBelowClosedPoint.Read(L).At(k, A0, A1, A01, t, I, P)))
		}),
})}

// ProperPairBelowPoint — an invertible pair inside the charts other than the
// structure pair lies under a closed point. One of its components is proper,
// and the second is the first read from the other chart.
var ProperPairBelowPoint = properPairBelowPointThm{family.Add(registry.ProofEntry{
	Name: "ProperPairBelowPoint",
	Key:  "prop_d2f27191cf908d67",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀I:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(I)",
			"fst(I) ⊆ A₀",
			"snd(I) ⊆ A₁",
			"I ≠ (A₀, A₁)",
		},
		Conclusion: "∃P:prod(set(A), set(A)). «scPoint»(P) ∧ fst(I) ⊆ fst(P) ∧ snd(I) ⊆ snd(P)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			I *Expr[_IdealPair],
			curve, invertible, inChart0, inChart1, proper Fact,
		) {
			a.Cases(a.TermAs[Bool]("fst(I) = A₀"))
			a.Otherwise(
				"chart 0 sees a proper first component",
				func(b *Argument, notWhole Fact) {
					b.Show(
						"this is the chart's own point",
						By(
							curve,
							invertible,
							inChart0,
							inChart1,
							notWhole,
							ProperChartBelowPoint.Read(L).At(k, A0, A1, A01, t, I)))
				})
			a.When(
				"with the whole of chart 0 the second component is proper, so read the pair from chart 1",
				func(b *Argument, whole Fact) {
					notWhole := b.Have(
						"the second component is not the whole of chart 1",
						"snd(I) ≠ A₁",
						By(Normalized, proper, whole, pairs.PairEta.At(I)))
					swapped := b.Have(
						"the pair with its components exchanged is invertible",
						"invertible_lattice_pair(field_ring(L), A₁, A₀, A₀₁, (snd(I), fst(I)))",
						By(invertible, invertible_lattice_pair.InvertiblePairSwap.Read(L).At(A0, A1, A01, I)))
					Q, other := b.ObtainAs[_IdealPair](
						"the exchanged pair lies under a point of the exchanged curve",
						"∃Q:prod(set(A), set(A)). "+
							"    curve_closed_point(field_ring(L), A₁, A₀, A₀₁, Q) ∧ snd(I) ⊆ fst(Q) ∧ fst(I) ⊆ snd(Q)",
						By(
							Normalized,
							curve,
							smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t),
							swapped,
							inChart1,
							inChart0,
							notWhole,
							pairs.Fst,
							pairs.Snd,
							ProperChartBelowPoint.Read(L).At(
								k,
								A1,
								A0,
								A01,
								b.TermAs[A]("L.inv(t)"),
								b.TermAs[_IdealPair]("(snd(I), fst(I))"))))
					exchanged := b.Conjuncts(
						other,
						"Q is a closed point of the exchanged curve",
						"above the second component",
						"above the first component")
					b.Take(b.TermAs[_IdealPair]("(snd(Q), fst(Q))"))
					b.Show(
						"exchanged back, Q is a closed point above the pair",
						By(
							exchanged[0],
							exchanged[1],
							exchanged[2],
							smooth_curve.ClosedPointSwap.At(b.TermAs[RingOps[A]]("field_ring(L)"), A1, A0, A01, Q),
							pairs.Fst,
							pairs.Snd))
				})
		}),
})}

// ClosedPointInCharts — the two components of a closed point lie inside the two
// charts: each is the chart or a maximal ideal of it.
var ClosedPointInCharts = closedPointInChartsThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointInCharts",
	Key:  "prop_7c18bf2f977f7069",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"«scCurve»", "«scPoint»(P)"},
		Conclusion: "fst(P) ⊆ A₀ ∧ snd(P) ⊆ A₁",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_IdealPair],
			curve, point Fact,
		) {
			clauses := a.Conjuncts(
				a.Unfolded(point, smooth_curve.CurveClosedPointDef),
				"fst(P) is chart 0 or maximal in it",
				"snd(P) is chart 1 or maximal in it",
				"P is not the structure pair",
				"its two ideals generate one ideal of the overlap",
				"which is proper where P lies on both charts")
			a.Show(
				"each is the statement at its chart, the second read from chart 1",
				By(
					curve,
					clauses[0],
					clauses[1],
					smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t),
					ChartPointInvertible.Read(L).At(k, A0, A1, A01, t, a.TermAs[Set[A]]("fst(P)")),
					ChartPointInvertible.Read(L).At(
						k,
						A1,
						A0,
						A01,
						a.TermAs[A]("L.inv(t)"),
						a.TermAs[Set[A]]("snd(P)"))))
		}),
})}

// ClosedPointProper — the structure pair lies under no closed point: a closed
// point lies inside the two charts and is not the pair of the two charts.
var ClosedPointProper = closedPointProperThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointProper",
	Key:  "prop_834a53899df2b6dc",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"«scCurve»", "«scPoint»(P)"},
		Conclusion: "¬(A₀ ⊆ fst(P) ∧ A₁ ⊆ snd(P))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_IdealPair],
			curve, point Fact,
		) {
			inCharts := a.Conjuncts(
				GroupPremises(curve, point, ClosedPointInCharts.Read(L).At(k, A0, A1, A01, t, P)),
				"fst(P) lies in chart 0",
				"snd(P) lies in chart 1")
			notStructure := a.Conjuncts(
				a.Unfolded(point, smooth_curve.CurveClosedPointDef),
				"fst(P) is chart 0 or maximal in it",
				"snd(P) is chart 1 or maximal in it",
				"P is not the structure pair",
				"its two ideals generate one ideal of the overlap",
				"which is proper where P lies on both charts")[2]
			a.Show(
				"holding both charts, P would be the structure pair",
				By(
					Normalized,
					notStructure,
					inCharts[0],
					inCharts[1],
					a.Hyp("A₀ ⊆ fst(P)"),
					a.Hyp("A₁ ⊆ snd(P)"),
					set_order.SubsetAntisym.At(a.TermAs[Set[A]]("fst(P)"), A0),
					set_order.SubsetAntisym.At(a.TermAs[Set[A]]("snd(P)"), A1)))
		}),
})}

// ClosedPointChartBelow — a closed point under a closed point proper in chart 0
// is that point. Its first component is proper too, hence maximal, so the two
// first components agree, and a maximal ideal has one closed point.
var ClosedPointChartBelow = closedPointChartBelowThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointChartBelow",
	Key:  "prop_c552eeed7bf9a5f9",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀Q P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(Q)",
			"«scPoint»(P)",
			"fst(P) ≠ A₀",
			"fst(Q) ⊆ fst(P)",
		},
		Conclusion: "Q = P",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			Q, P *Expr[_IdealPair],
			curve, pointQ, pointP, proper, below Fact,
		) {
			chart := a.TermAs[RingOps[A]]("«chart»")
			fstQ := a.TermAs[Set[A]]("fst(Q)")
			fstP := a.TermAs[Set[A]]("fst(P)")
			maximalP := a.Have(
				"so fst(P) is maximal in the chart",
				"maximal_ideal(«chart», fst(P))",
				By(Normalized, a.Unfolded(pointP, smooth_curve.CurveClosedPointDef), proper))
			notWhole := a.Have(
				"fst(Q), under fst(P), is not the whole chart",
				"fst(Q) ≠ A₀",
				By(
					Normalized,
					proper,
					below,
					curve,
					pointP,
					ClosedPointInCharts.Read(L).At(k, A0, A1, A01, t, P),
					set_order.SubsetAntisym.At(fstP, A0)))
			maximalQ := a.Have(
				"so fst(Q) is maximal as well",
				"maximal_ideal(«chart», fst(Q))",
				By(Normalized, a.Unfolded(pointQ, smooth_curve.CurveClosedPointDef), notWhole))
			equal := a.Have(
				"a maximal ideal under a proper ideal is that ideal",
				"fst(P) = fst(Q)",
				By(
					Normalized,
					maximalQ,
					below,
					maximalP,
					ring_ideal.MaximalIdealIdeal.At(chart, fstP),
					ring_ideal.MaximalIdealProper.At(chart, fstP),
					ring_ideal.MaximalIdealMaximal.At(chart, fstQ, fstP)))
			unique := a.Have(
				"a maximal ideal is the first component of one closed point",
				"∃!X:prod(set(A), set(A)). «scPoint»(X) ∧ fst(X) = fst(P)",
				By(curve, maximalP, smooth_curve.ChartMaximalClosedPoint.Read(L).At(k, A0, A1, A01, t, fstP)))
			_, center := a.UnpackAs[_IdealPair](unique, "c")
			a.Show(
				"Q and P both are that point",
				By(Normalized, pointQ, pointP, equal, center.At(Q), center.At(P)))
		}),
})}

// ClosedPointBelowPoint — closed points are incomparable: one under another is
// that other. A closed point is proper in one of its charts, and the two charts
// read alike through the swap.
var ClosedPointBelowPoint = closedPointBelowPointThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointBelowPoint",
	Key:  "prop_1f3eb773baaa535c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀Q P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(Q)",
			"«scPoint»(P)",
			"fst(Q) ⊆ fst(P)",
			"snd(Q) ⊆ snd(P)",
		},
		Conclusion: "Q = P",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			Q, P *Expr[_IdealPair],
			curve, pointQ, pointP, below0, below1 Fact,
		) {
			a.Cases(a.TermAs[Bool]("fst(P) = A₀"))
			a.Otherwise(
				"P is proper in chart 0",
				func(b *Argument, proper Fact) {
					b.Show(
						"this is the statement at chart 0",
						By(
							curve,
							pointQ,
							pointP,
							proper,
							below0,
							ClosedPointChartBelow.Read(L).At(k, A0, A1, A01, t, Q, P)))
				})
			a.When(
				"P is off chart 0, hence proper in chart 1",
				func(b *Argument, whole Fact) {
					clauses := b.Conjuncts(
						b.Unfolded(pointP, smooth_curve.CurveClosedPointDef),
						"fst(P) is chart 0 or maximal in it",
						"snd(P) is chart 1 or maximal in it",
						"P is not the structure pair",
						"its two ideals generate one ideal of the overlap",
						"which is proper where P lies on both charts")
					proper := b.Have(
						"snd(P) is not the whole of chart 1",
						"snd(P) ≠ A₁",
						By(Normalized, whole, clauses[2]))
					ring := b.TermAs[RingOps[A]]("field_ring(L)")
					swappedPairs := b.Have(
						"the two points read from chart 1 are closed points of the exchanged curve",
						"curve_closed_point(field_ring(L), A₁, A₀, A₀₁, (snd(Q), fst(Q))) ∧ "+
							"curve_closed_point(field_ring(L), A₁, A₀, A₀₁, (snd(P), fst(P)))",
						By(
							pointQ,
							pointP,
							smooth_curve.ClosedPointSwap.At(ring, A0, A1, A01, Q),
							smooth_curve.ClosedPointSwap.At(ring, A0, A1, A01, P)))
					equal := b.Have(
						"read from chart 1 they are one point",
						"(snd(Q), fst(Q)) = (snd(P), fst(P))",
						By(
							smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t),
							curve,
							swappedPairs,
							proper,
							below1,
							pairs.Fst,
							ClosedPointChartBelow.Read(L).At(
								k,
								A1,
								A0,
								A01,
								b.TermAs[A]("L.inv(t)"),
								b.TermAs[_IdealPair]("(snd(Q), fst(Q))"),
								b.TermAs[_IdealPair]("(snd(P), fst(P))"))))
					b.Show(
						"so Q and P agree in both components",
						By(equal, pairs.PairEq, pairs.PairEta.At(Q), pairs.PairEta.At(P)))
				})
		}),
})}

// ChartIdealProduct — the product of two invertible fractional ideals inside a
// chart lies in the second, and a maximal ideal above it lies above one of them.
var ChartIdealProduct = chartIdealProductThm{family.Add(registry.ProofEntry{
	Name: "ChartIdealProduct",
	Key:  "prop_d0671f07dc4e440c",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀H₁ H₂:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"invertible_fractional(field_ring(L), A₀, H₁)",
			"H₁ ⊆ A₀",
			"invertible_fractional(field_ring(L), A₀, H₂)",
			"H₂ ⊆ A₀",
		},
		Conclusion: "fractional_mul(field_ring(L), A₀, H₁, H₂) ⊆ H₂ ∧ " +
			"(∀m:set(A). " +
			"    maximal_ideal(«chart», m) ∧ fractional_mul(field_ring(L), A₀, H₁, H₂) ⊆ m ⇒ H₁ ⊆ m ∨ H₂ ⊆ m)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			H1, H2 *Expr[Set[A]],
			curve, invertible1, inChart1, invertible2, inChart2 Fact,
		) {
			subring := a.Have(
				"the chart is a subring of L",
				"subring(field_ring(L), A₀)",
				By(curve, smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t)))
			chartRing := a.Have(
				"the chart is a commutative ring",
				"comm_ring_on(«chart»)",
				By(curve, smooth_curve.ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			ideals := a.Conjuncts(
				a.Have(
					"both are ideals of the chart",
					"ring_ideal(«chart», H₁) ∧ ring_ideal(«chart», H₂)",
					By(
						curve,
						invertible1,
						inChart1,
						invertible2,
						inChart2,
						InvertibleChartIdeal.Read(L).At(k, A0, A1, A01, t, H1),
						InvertibleChartIdeal.Read(L).At(k, A0, A1, A01, t, H2))),
				"H₁ is an ideal",
				"H₂ is an ideal")
			prime := a.Have(
				"a maximal ideal above the product lies above a factor",
				Statement{
					Binders:    "∀m:set(A).",
					Hypotheses: []string{"maximal_ideal(«chart», m)", "fractional_mul(field_ring(L), A₀, H₁, H₂) ⊆ m"},
					Conclusion: "H₁ ⊆ m ∨ H₂ ⊆ m",
				},
				Derive(func(b *Argument) {
					m := b.FixAs[Set[A]]("m")
					above := b.Conjuncts(
						b.Assume(),
						"m is maximal",
						"m lies above the product")
					b.Show(
						"maximal ideals are prime, and the product is the product of the two ideals",
						By(
							Normalized,
							above[0],
							above[1],
							subring,
							ideals[0],
							ideals[1],
							ideal_factorization.IntegralMulAsFractional.Read(L).At(A0, H1, H2),
							ring_ideal.MaximalIsPrime.Read(chartRing).At(m),
							ring_ideal.PrimeIdealMulSubset.At(a.TermAs[RingOps[A]]("«chart»"), m, H1, H2)))
				}))
			a.Show(
				"the product lies in H₂, and a maximal ideal above it above a factor",
				By(
					subring,
					ideals[0],
					ideals[1],
					ideal_factorization.IntegralFractionalProduct.Read(L).At(A0, H1, H2),
					prime))
		}),
})}

// ClosedPointPrime — a closed point above a product of two invertible pairs
// inside the charts lies above one of them: maximal ideals are prime in the
// chart where the point is proper, and in the other chart the point follows.
var ClosedPointPrime = closedPointPrimeThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointPrime",
	Key:  "prop_171fac8dd26302ba",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀X Y P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(X)",
			"fst(X) ⊆ A₀",
			"snd(X) ⊆ A₁",
			"«scInvertible»(Y)",
			"fst(Y) ⊆ A₀",
			"snd(Y) ⊆ A₁",
			"«scPoint»(P)",
			"fst(lattice_pair_mul(field_ring(L), A₀, A₁, X, Y)) ⊆ fst(P)",
			"snd(lattice_pair_mul(field_ring(L), A₀, A₁, X, Y)) ⊆ snd(P)",
		},
		Conclusion: "(fst(X) ⊆ fst(P) ∧ snd(X) ⊆ snd(P)) ∨ (fst(Y) ⊆ fst(P) ∧ snd(Y) ⊆ snd(P))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X, Y, P *Expr[_IdealPair],
			curve, invertibleX, x0, x1, invertibleY, y0, y1, point, below0, below1 Fact,
		) {
			fstX := a.TermAs[Set[A]]("fst(X)")
			fstY := a.TermAs[Set[A]]("fst(Y)")
			sndX := a.TermAs[Set[A]]("snd(X)")
			sndY := a.TermAs[Set[A]]("snd(Y)")
			componentsX := a.Conjuncts(
				a.Unfolded(invertibleX, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(X) is invertible",
				"snd(X) is invertible",
				"X is a lattice pair")
			componentsY := a.Conjuncts(
				a.Unfolded(invertibleY, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(Y) is invertible",
				"snd(Y) is invertible",
				"Y is a lattice pair")
			clauses := a.Conjuncts(
				a.Unfolded(point, smooth_curve.CurveClosedPointDef),
				"fst(P) is chart 0 or maximal in it",
				"snd(P) is chart 1 or maximal in it",
				"P is not the structure pair",
				"its two ideals generate one ideal of the overlap",
				"which is proper where P lies on both charts")
			parts := a.Conjuncts(
				a.Have(
					"the product is taken chart by chart",
					"fst(lattice_pair_mul(field_ring(L), A₀, A₁, X, Y)) = "+
						"fractional_mul(field_ring(L), A₀, fst(X), fst(Y)) ∧ "+
						"snd(lattice_pair_mul(field_ring(L), A₀, A₁, X, Y)) = "+
						"fractional_mul(field_ring(L), A₁, snd(X), snd(Y))",
					Simp(Fwd(invertible_lattice_pair.LatticePairMulDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
					Basic()),
				"the first component",
				"the second component")
			inFirst := a.Have(
				"so the product of the first components lies in fst(P)",
				"fractional_mul(field_ring(L), A₀, fst(X), fst(Y)) ⊆ fst(P)",
				parts[0].RwRev(),
				By(below0))
			inSecond := a.Have(
				"and that of the second components in snd(P)",
				"fractional_mul(field_ring(L), A₁, snd(X), snd(Y)) ⊆ snd(P)",
				parts[1].RwRev(),
				By(below1))
			a.Cases(a.TermAs[Bool]("fst(P) = A₀"))
			a.When(
				"off chart 0 only chart 1 counts, where snd(P) is maximal",
				func(b *Argument, whole Fact) {
					maximal := b.Have(
						"snd(P) is maximal in chart 1",
						"maximal_ideal(restrict_ring(field_ring(L), A₁), snd(P))",
						By(Normalized, whole, clauses[1], clauses[2]))
					factor := b.Have(
						"so snd(P) lies above snd(X) or snd(Y)",
						"snd(X) ⊆ snd(P) ∨ snd(Y) ⊆ snd(P)",
						By(
							curve,
							smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t),
							componentsX[1],
							x1,
							componentsY[1],
							y1,
							maximal,
							inSecond,
							ChartIdealProduct.Read(L).At(k, A1, A0, A01, b.TermAs[A]("L.inv(t)"), sndX, sndY)))
					b.Show(
						"the first components lie in chart 0, all of fst(P)",
						Simp(Fwd(whole)),
						By(factor, x0, y0))
				})
			a.Otherwise(
				"P is proper in chart 0, where its first component is maximal",
				func(b *Argument, proper Fact) {
					maximal := b.Have(
						"fst(P) is maximal in chart 0",
						"maximal_ideal(restrict_ring(field_ring(L), A₀), fst(P))",
						By(Normalized, proper, clauses[0]))
					factor := b.Have(
						"so fst(P) lies above fst(X) or fst(Y)",
						"fst(X) ⊆ fst(P) ∨ fst(Y) ⊆ fst(P)",
						By(
							curve,
							componentsX[0],
							x0,
							componentsY[0],
							y0,
							maximal,
							inFirst,
							ChartIdealProduct.Read(L).At(k, A0, A1, A01, t, fstX, fstY)))
					b.Show(
						"and an invertible pair under P in chart 0 lies under it in chart 1",
						By(
							Normalized,
							factor,
							curve,
							invertibleX,
							x1,
							invertibleY,
							y1,
							point,
							proper,
							PairBelowClosedPoint.Read(L).At(k, A0, A1, A01, t, X, P),
							PairBelowClosedPoint.Read(L).At(k, A0, A1, A01, t, Y, P)))
				})
		}),
})}

// ChartDivideByIdeal — dividing an invertible fractional ideal inside a chart by
// an invertible ideal above it stays inside the chart, and the colength over the
// constants does not grow, and strictly drops unless the divisor is the chart.
var ChartDivideByIdeal = chartDivideByIdealThm{family.Add(registry.ProofEntry{
	Name: "ChartDivideByIdeal",
	Key:  "prop_d459f6bcceea75b",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀H Q:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"invertible_fractional(field_ring(L), A₀, H)",
			"H ⊆ A₀",
			"invertible_fractional(field_ring(L), A₀, Q)",
			"Q ⊆ A₀",
			"H ⊆ Q",
		},
		Conclusion: "«J» ⊆ A₀ ∧ «dim»(«J») ≤ «dim»(H) ∧ (Q ≠ A₀ ⇒ «dim»(«J») < «dim»(H))",
		Abbrev: Abbrev{
			{Name: "J", Text: "fractional_mul(field_ring(L), A₀, H, fractional_inverse(field_ring(L), A₀, Q))"},
			{Name: "dim", Text: "λX:set(A). " +
				"    module_dim(restrict_ring(field_ring(L), k), " +
				"        quotient_module(restrict_module(regular_module(field_ring(L)), A₀), X))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			H, Q *Expr[Set[A]],
			curve, invertibleH, inChartH, invertibleQ, inChartQ, below Fact,
		) {
			chart := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀)")
			J := a.TermAs[Set[A]]("«J»")
			constants := a.Conjuncts(
				GroupPremises(curve, smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t)),
				"the constants are a subfield of L",
				"the constants lie in the chart",
				"the chart is a subring of L")
			idealH := a.Conjuncts(
				GroupPremises(curve, invertibleH, inChartH, InvertibleChartIdeal.Read(L).At(k, A0, A1, A01, t, H)),
				"H is an ideal of the chart",
				"H is nonzero")
			idealQ := a.Conjuncts(
				GroupPremises(curve, invertibleQ, inChartQ, InvertibleChartIdeal.Read(L).At(k, A0, A1, A01, t, Q)),
				"Q is an ideal of the chart",
				"Q is nonzero")
			finite := a.Conjuncts(
				GroupPremises(
					curve,
					idealH[0],
					idealH[1],
					smooth_curve.ChartIdealFiniteQuotient.Read(L).At(k, A0, A1, A01, t, H)),
				"the chart modulo H is finite-dimensional",
				"and has finitely many cosets")
			a.Show(
				"the quotient is an ideal of the chart, so it lies in the chart",
				By(
					constants[0],
					constants[1],
					constants[2],
					idealH[0],
					idealH[1],
					invertibleH,
					idealQ[0],
					invertibleQ,
					below,
					finite[0],
					ideal_factorization.DivisionShrinksColength.Read(L).At(k, A0, H, Q),
					ring_ideal.IdealSubset.At(chart, J)))
		}),
})}

// PairQuotient — the quotient of two invertible pairs is invertible, and
// multiplying and dividing by one pair cancel: these are laws of the group the
// invertible pairs form.
var PairQuotient = pairQuotientThm{family.Add(registry.ProofEntry{
	Name: "PairQuotient",
	Key:  "prop_ddc34197168ff749",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀X Y:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(X)",
			"«scInvertible»(Y)",
		},
		Conclusion: "«scInvertible»(«scMul»(X, «scInverse»(Y))) ∧ " +
			"«scMul»(«scMul»(X, «scInverse»(Y)), Y) = X ∧ " +
			"«scMul»(«scMul»(X, Y), «scInverse»(Y)) = X",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X, Y *Expr[_IdealPair],
			curve, invertibleX, invertibleY Fact,
		) {
			datum := a.Have(
				"the charts and their overlap are a biaffine datum inside L",
				"A₀₁ ⊆ L.carrier ∧ biaffine(restrict_ring(field_ring(L), A₀₁), A₀, A₁, t, L.inv(t))",
				By(
					a.Unfolded(curve, smooth_curve.SmoothFiniteFieldCurveDef),
					algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)))
			invertibles := abelian_group.GroupOn.Read(a.Have(
				"the invertible pairs are an abelian group",
				"abelian_group_on(mk_group(«scMul», (A₀, A₁), «scInverse», «scInvertibles»))",
				By(datum, invertible_lattice_pair.InvertiblePairsGroup.Read(L).At(A0, A1, A01, t))))
			a.Show(
				"so X over Y is invertible, times Y it is X, and X times Y over Y is X",
				By(
					invertibleX,
					invertibleY,
					group.MulIn.Read(invertibles),
					group.InvIn.Read(invertibles),
					group.InvMulCancelRightOn.Read(invertibles).AsFact().At(Y, X),
					group.MulInvCancelRightOn.Read(invertibles).AsFact().At(Y, X)))
		}),
})}

// PairDivideByPoint — an invertible pair inside the charts under a closed point
// P is the product of P and an invertible pair inside the charts of strictly
// smaller colength: divide chart by chart, the quotient staying an ideal, and
// the colength drops in a chart where P is proper.
var PairDivideByPoint = pairDivideByPointThm{family.Add(registry.ProofEntry{
	Name: "PairDivideByPoint",
	Key:  "prop_aa71047d8897bc3d",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀I P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(I)",
			"fst(I) ⊆ A₀",
			"snd(I) ⊆ A₁",
			"«scPoint»(P)",
			"fst(I) ⊆ fst(P)",
			"snd(I) ⊆ snd(P)",
		},
		Conclusion: "«scInvertible»(«J») ∧ " +
			"fst(«J») ⊆ A₀ ∧ " +
			"snd(«J») ⊆ A₁ ∧ " +
			"«scMul»(«J», P) = I ∧ " +
			"«colength»(«J») < «colength»(I)",
		Abbrev: Abbrev{
			{Name: "J", Text: "«scMul»(I, «scInverse»(P))"},
			{Name: "dim", Text: "λS:set(A). λX:set(A). " +
				"    module_dim(restrict_ring(field_ring(L), k), " +
				"        quotient_module(restrict_module(regular_module(field_ring(L)), S), X))"},
			{Name: "colength", Text: "λX:prod(set(A), set(A)). «dim»(A₀, fst(X)) + «dim»(A₁, snd(X))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			I, P *Expr[_IdealPair],
			curve, invertible, inChart0, inChart1, point, below0, below1 Fact,
		) {
			fstI := a.TermAs[Set[A]]("fst(I)")
			sndI := a.TermAs[Set[A]]("snd(I)")
			fstP := a.TermAs[Set[A]]("fst(P)")
			sndP := a.TermAs[Set[A]]("snd(P)")
			clauses := a.Conjuncts(
				a.Unfolded(point, smooth_curve.CurveClosedPointDef),
				"fst(P) is chart 0 or maximal in it",
				"snd(P) is chart 1 or maximal in it",
				"P is not the structure pair",
				"its two ideals generate one ideal of the overlap",
				"which is proper where P lies on both charts")
			invertibleI := a.Conjuncts(
				a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(I) is invertible",
				"snd(I) is invertible",
				"I is a lattice pair")
			pInvertible := a.Have(
				"P is an invertible pair",
				"«scInvertible»(P)",
				By(curve, point, ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, P)))
			invertibleP := a.Conjuncts(
				a.Unfolded(pInvertible, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(P) is invertible",
				"snd(P) is invertible",
				"P is a lattice pair")
			pInCharts := a.Conjuncts(
				GroupPremises(curve, point, ClosedPointInCharts.Read(L).At(k, A0, A1, A01, t, P)),
				"fst(P) lies in chart 0",
				"snd(P) lies in chart 1")
			quotient := a.Conjuncts(
				GroupPremises(curve, invertible, pInvertible, PairQuotient.Read(L).At(k, A0, A1, A01, t, I, P)),
				"J is invertible",
				"J times P is I",
				"I times P over P is I")
			first := a.Conjuncts(
				GroupPremises(
					curve,
					inChart0,
					below0,
					invertibleI[0],
					invertibleP[0],
					pInCharts[0],
					ChartDivideByIdeal.Read(L).At(k, A0, A1, A01, t, fstI, fstP)),
				"the quotient lies in chart 0",
				"its colength is no larger",
				"and smaller unless P is off chart 0")
			otherChart := a.Have(
				"the curve reads the same from chart 1",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			second := a.Conjuncts(
				GroupPremises(
					inChart1,
					below1,
					invertibleI[1],
					invertibleP[1],
					pInCharts[1],
					otherChart,
					ChartDivideByIdeal.Read(L).At(k, A1, A0, A01, a.TermAs[A]("L.inv(t)"), sndI, sndP)),
				"the quotient lies in chart 1",
				"its colength is no larger",
				"and smaller unless P is off chart 1")
			parts := a.Conjuncts(
				a.Have(
					"J is the pair of the two chart quotients",
					"fst(«J») = "+
						"fractional_mul(field_ring(L), A₀, fst(I), fractional_inverse(field_ring(L), A₀, fst(P))) ∧ "+
						"snd(«J») = "+
						"fractional_mul(field_ring(L), A₁, snd(I), fractional_inverse(field_ring(L), A₁, snd(P)))",
					Simp(
						Fwd(invertible_lattice_pair.LatticePairMulDef),
						Fwd(invertible_lattice_pair.LatticePairInverseDef),
						Fwd(pairs.Fst),
						Fwd(pairs.Snd)),
					Basic()),
				"the first component",
				"the second component")
			inside0 := a.Have(
				"so fst(J) lies in chart 0",
				"fst(«J») ⊆ A₀",
				parts[0].Rw(),
				By(first[0]))
			inside1 := a.Have(
				"and snd(J) lies in chart 1",
				"snd(«J») ⊆ A₁",
				parts[1].Rw(),
				By(second[0]))
			smaller0 := a.Have(
				"chart 0 does not grow, and shrinks where P is proper",
				"«dim»(A₀, fst(«J»)) ≤ «dim»(A₀, fst(I)) ∧ (fst(P) ≠ A₀ ⇒ «dim»(A₀, fst(«J»)) < «dim»(A₀, fst(I)))",
				parts[0].Rw(),
				By(first[1], first[2]))
			smaller1 := a.Have(
				"so does chart 1",
				"«dim»(A₁, snd(«J»)) ≤ «dim»(A₁, snd(I)) ∧ (snd(P) ≠ A₁ ⇒ «dim»(A₁, snd(«J»)) < «dim»(A₁, snd(I)))",
				parts[1].Rw(),
				By(second[1], second[2]))
			drop := a.Have(
				"P is proper in a chart, so the colength drops",
				"«colength»(«J») < «colength»(I)",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("fst(P) = A₀"))
					b.Otherwise(
						"chart 0 shrinks",
						func(c *Argument, proper Fact) {
							strict := c.Have(
								"strictly in chart 0",
								"«dim»(A₀, fst(«J»)) < «dim»(A₀, fst(I))",
								By(proper, smaller0))
							c.Show(
								"chart 1 does not grow",
								ByArith(smaller1, strict))
						})
					b.When(
						"off chart 0, chart 1 shrinks",
						func(c *Argument, whole Fact) {
							strict := c.Have(
								"strictly in chart 1",
								"«dim»(A₁, snd(«J»)) < «dim»(A₁, snd(I))",
								By(whole, clauses[2], smaller1))
							c.Show(
								"chart 0 does not grow",
								ByArith(smaller0, strict))
						})
				}))
			a.Show(
				"the quotient is invertible inside the charts, times P it is I, and its colength is smaller",
				By(quotient[0], inside0, inside1, quotient[1], drop))
		}),
})}

// EffectivePairIn — the ideal pair of an effective divisor lies in every submonoid
// of the invertible pairs holding the points of its support: it is the product of
// the positive powers of those points.
var EffectivePairIn = effectivePairInThm{family.Add(registry.ProofEntry{
	Name: "EffectivePairIn",
	Key:  "prop_6f4a9a5324b89fe0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀T:set(prod(set(A), set(A))). " +
			"∀E:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"∀X:prod(set(A), set(A)). X ∈ T ⇒ «scInvertible»(X)",
			"(A₀, A₁) ∈ T",
			"∀X Y:prod(set(A), set(A)). X ∈ T ∧ Y ∈ T ⇒ «scMul»(X, Y) ∈ T",
			"«scDivisor»(E)",
			"∀P:prod(set(A), set(A)). 0 ≤ E(P)",
			"∀P:prod(set(A), set(A)). E(P) ≠ 0 ⇒ P ∈ T",
		},
		Conclusion: "«scPair»(λP:prod(set(A), set(A)). -E(P)) ∈ T",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			T *Expr[Set[_IdealPair]],
			E *Arrow[_IdealPair, Int],
			curve, invertible, identity, closed, divisor, nonnegative, points Fact,
		) {
			products := a.Conjuncts(
				GroupPremises(curve, ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")
			ambient := a.Conjuncts(
				a.Unfolded(products[0], comm_monoid.CommMonoidOn),
				"the structure pair is invertible",
				"products of invertible pairs are invertible",
				"the product commutes",
				"and associates",
				"with the structure pair for identity")
			members := a.Have(
				"T lies in the invertible pairs",
				"∀X:prod(set(A), set(A)). X ∈ T ⇒ X ∈ «scInvertibles»",
				BySets(invertible))
			monoid := a.Have(
				"T is a commutative monoid",
				"comm_monoid_on(T, «scMul», (A₀, A₁))",
				Unfold(comm_monoid.CommMonoidOn),
				By(identity, closed, members, ambient[2], ambient[3], ambient[4]))
			negated := a.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). -E(P)")
			negative := a.Conjuncts(
				GroupPremises(curve, divisor, ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, E)),
				"-E is a divisor",
				"the pair of E is invertible",
				"the pair of -E is its inverse",
				"and the degree changes sign")
			support := a.Conjuncts(
				a.Unfolded(negative[0], ClosedDivisorDef),
				"the support of -E is finite",
				"and made of closed points")
			fold := a.Conjuncts(
				GroupPremises(negative[0], products[3].At(negated)),
				"the pair of -E is invertible",
				"and the product of the powers at its support")
			index := a.TermAs[Set[_IdealPair]]("fun_support(int_of_num(0), λP:prod(set(A), set(A)). -E(P))")
			term := a.TermAs[Fun[_IdealPair, _IdealPair]]("λP:prod(set(A), set(A)). «scPower»(P, -E(P))")
			powers := a.Have(
				"each power at the support lies in T",
				Statement{
					Binders: "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{
						"P ∈ fun_support(int_of_num(0), λP:prod(set(A), set(A)). -E(P))",
					},
					Conclusion: "«scPower»(P, -E(P)) ∈ T",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_IdealPair]("P")
					inSupport := b.Assume()
					inverted := b.Have(
						"-E(P) is not zero",
						"-E(P) ≠ 0",
						BySets(inSupport))
					negative := b.Have(
						"so -E(P) is negative",
						"¬(0 ≤ -E(P))",
						ByArith(inverted, nonnegative.At(P)))
					nonzero := b.Have(
						"and E(P) is not zero",
						"E(P) ≠ 0",
						ByArith(inverted))
					power := b.TermAs[Nat]("num_of_int(--E(P))")
					b.Show(
						"a negative exponent is a positive power of P, a member of the monoid T",
						By(negative, nonzero, points.At(P), comm_monoid.PowIn.Read(monoid).AsFact().At(P, power)))
				}))
			product := a.Have(
				"so their product lies in T",
				"module_sum(«scMul», "+
					"    (A₀, A₁), "+
					"    fun_support(int_of_num(0), λP:prod(set(A), set(A)). -E(P)), "+
					"    λP:prod(set(A), set(A)). «scPower»(P, -E(P))) ∈ "+
					"T",
				By(support[0], powers, module.ModuleSumInMonoid.Read(monoid).At(index, term)))
			a.Show(
				"and that product is the pair of -E",
				fold[1].Rw(),
				By(product))
		}),
})}

// PairProductIntegral — the product of two invertible pairs inside the charts
// is an invertible pair lying under the second factor.
var PairProductIntegral = pairProductIntegralThm{family.Add(registry.ProofEntry{
	Name: "PairProductIntegral",
	Key:  "prop_f00452710cdf2b21",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀X Y:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(X)",
			"fst(X) ⊆ A₀",
			"snd(X) ⊆ A₁",
			"«scInvertible»(Y)",
			"fst(Y) ⊆ A₀",
			"snd(Y) ⊆ A₁",
		},
		Conclusion: "«scInvertible»(«scMul»(X, Y)) ∧ " +
			"fst(«scMul»(X, Y)) ⊆ fst(Y) ∧ " +
			"snd(«scMul»(X, Y)) ⊆ snd(Y)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X, Y *Expr[_IdealPair],
			curve, invertibleX, x0, x1, invertibleY, y0, y1 Fact,
		) {
			fstX := a.TermAs[Set[A]]("fst(X)")
			fstY := a.TermAs[Set[A]]("fst(Y)")
			sndX := a.TermAs[Set[A]]("snd(X)")
			sndY := a.TermAs[Set[A]]("snd(Y)")
			xParts := a.Conjuncts(
				a.Unfolded(invertibleX, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(X) is invertible",
				"snd(X) is invertible",
				"X is a lattice pair")
			yParts := a.Conjuncts(
				a.Unfolded(invertibleY, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(Y) is invertible",
				"snd(Y) is invertible",
				"Y is a lattice pair")
			monoid := a.Conjuncts(
				GroupPremises(curve, ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")[0]
			members := a.Have(
				"X and Y are invertible pairs",
				"X ∈ «scInvertibles» ∧ Y ∈ «scInvertibles»",
				BySets(invertibleX, invertibleY))
			product := a.Have(
				"their product is an invertible pair",
				"«scMul»(X, Y) ∈ «scInvertibles»",
				By(members, comm_monoid.OpIn.Read(monoid).AsFact().At(X, Y)))
			invertible := a.Have(
				"that is, invertible",
				"«scInvertible»(«scMul»(X, Y))",
				BySets(product))
			parts := a.Conjuncts(
				a.Have(
					"the product is taken chart by chart",
					"fst(«scMul»(X, Y)) = fractional_mul(field_ring(L), A₀, fst(X), fst(Y)) ∧ "+
						"snd(«scMul»(X, Y)) = fractional_mul(field_ring(L), A₁, snd(X), snd(Y))",
					Simp(Fwd(invertible_lattice_pair.LatticePairMulDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
					Basic()),
				"the first component",
				"the second component")
			otherChart := a.Have(
				"the curve reads the same from chart 1",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			first := a.Conjuncts(
				GroupPremises(
					curve, x0, y0, xParts[0], yParts[0], ChartIdealProduct.Read(L).At(k, A0, A1, A01, t, fstX, fstY)),
				"in chart 0 the product lies in fst(Y)",
				"and a maximal ideal above it lies above a factor")
			second := a.Conjuncts(
				GroupPremises(
					x1,
					y1,
					xParts[1],
					yParts[1],
					otherChart,
					ChartIdealProduct.Read(L).At(k, A1, A0, A01, a.TermAs[A]("L.inv(t)"), sndX, sndY)),
				"in chart 1 the product lies in snd(Y)",
				"and a maximal ideal above it lies above a factor")
			inFirst := a.Have(
				"fst of the product lies in fst(Y)",
				"fst(«scMul»(X, Y)) ⊆ fst(Y)",
				parts[0].Rw(),
				By(first[0]))
			inSecond := a.Have(
				"snd of the product lies in snd(Y)",
				"snd(«scMul»(X, Y)) ⊆ snd(Y)",
				parts[1].Rw(),
				By(second[0]))
			a.Show(
				"the product is invertible, and lies in Y on each chart",
				By(invertible, inFirst, inSecond))
		}),
})}

// EffectivePairIntegral — the ideal pair of an effective divisor is an invertible
// pair inside the charts: such pairs are a submonoid holding the closed points.
var EffectivePairIntegral = effectivePairIntegralThm{family.Add(registry.ProofEntry{
	Name: "EffectivePairIntegral",
	Key:  "prop_7f1d7d98736ecfdb",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀E:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(E)",
			"∀P:prod(set(A), set(A)). 0 ≤ E(P)",
		},
		Conclusion: "«scInvertible»(«pair») ∧ fst(«pair») ⊆ A₀ ∧ snd(«pair») ⊆ A₁",
		Abbrev: Abbrev{
			{Name: "pair", Text: "«scPair»(λP:prod(set(A), set(A)). -E(P))"},
			{Name: "integral", Text: "{X:prod(set(A), set(A)) | " +
				"    «scInvertible»(X) ∧ fst(X) ⊆ A₀ ∧ snd(X) ⊆ A₁}"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			E *Arrow[_IdealPair, Int],
			curve, divisor, nonnegative Fact,
		) {
			integral := a.TermAs[Set[_IdealPair]]("«integral»")
			structurePair := a.TermAs[_IdealPair]("(A₀, A₁)")
			clause := a.Have(
				"an integral pair is an invertible pair inside the charts",
				"∀X:prod(set(A), set(A)). X ∈ «integral» ⇔ «scInvertible»(X) ∧ fst(X) ⊆ A₀ ∧ snd(X) ⊆ A₁",
				BySets())
			invertible := a.Have(
				"so it is invertible",
				"∀X:prod(set(A), set(A)). X ∈ «integral» ⇒ «scInvertible»(X)",
				a.ForEach(func(X *Expr[_IdealPair]) Action { return By(clause.At(X)) }))
			monoid := a.Conjuncts(
				GroupPremises(curve, ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")[0]
			identity := a.Have(
				"the structure pair is integral",
				"(A₀, A₁) ∈ «integral»",
				By(
					clause.At(structurePair),
					comm_monoid.IdentityIn.Read(monoid),
					pairs.Fst,
					pairs.Snd,
					set_order.SubsetRefl))
			closed := a.Have(
				"a product of integral pairs is integral",
				"∀X Y:prod(set(A), set(A)). X ∈ «integral» ∧ Y ∈ «integral» ⇒ «scMul»(X, Y) ∈ «integral»",
				Derive(func(b *Argument) {
					X := b.FixAs[_IdealPair]("X")
					Y := b.FixAs[_IdealPair]("Y")
					members := b.Conjuncts(
						b.Assume(),
						"X is integral",
						"Y is integral")
					factorX := b.Conjuncts(
						b.Have(
							"read out, X is an invertible pair inside the charts",
							"«scInvertible»(X) ∧ fst(X) ⊆ A₀ ∧ snd(X) ⊆ A₁",
							By(members[0], clause.At(X))),
						"X is invertible",
						"fst(X) lies in chart 0",
						"snd(X) lies in chart 1")
					factorY := b.Conjuncts(
						b.Have(
							"as is Y",
							"«scInvertible»(Y) ∧ fst(Y) ⊆ A₀ ∧ snd(Y) ⊆ A₁",
							By(members[1], clause.At(Y))),
						"Y is invertible",
						"fst(Y) lies in chart 0",
						"snd(Y) lies in chart 1")
					product := b.Conjuncts(
						GroupPremises(
							curve,
							factorX[0],
							factorX[1],
							factorX[2],
							factorY[0],
							factorY[1],
							factorY[2],
							PairProductIntegral.Read(L).At(k, A0, A1, A01, t, X, Y)),
						"the product is invertible",
						"it lies under Y in chart 0",
						"and in chart 1")
					b.Show(
						"the product is invertible and lies under Y, inside the charts",
						By(
							clause.At(b.TermAs[_IdealPair]("«scMul»(X, Y)")),
							product[0],
							set_order.SubsetTrans.At(b.TermAs[Set[A]]("fst(«scMul»(X, Y))"), b.TermAs[Set[A]]("fst(Y)"), A0),
							set_order.SubsetTrans.At(b.TermAs[Set[A]]("snd(«scMul»(X, Y))"), b.TermAs[Set[A]]("snd(Y)"), A1),
							product[1],
							product[2],
							factorX[0],
							factorY[1],
							factorY[2]))
				}))
			support := a.Conjuncts(
				a.Unfolded(divisor, ClosedDivisorDef),
				"the support of E is finite",
				"and made of closed points")
			points := a.Have(
				"the closed points of the support are integral",
				"∀P:prod(set(A), set(A)). E(P) ≠ 0 ⇒ P ∈ «integral»",
				Derive(func(b *Argument) {
					P := b.FixAs[_IdealPair]("P")
					point := support[1].At(P)
					nonzero := b.Assume()
					b.Show(
						"a closed point is invertible and inside the charts",
						By(
							nonzero,
							point,
							clause.At(P),
							curve,
							ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, P),
							ClosedPointInCharts.Read(L).At(k, A0, A1, A01, t, P)))
				}))
			inIntegral := a.Have(
				"so the pair of the effective divisor E is integral",
				"«pair» ∈ «integral»",
				By(
					curve,
					invertible,
					identity,
					closed,
					divisor,
					nonnegative,
					points,
					EffectivePairIn.Read(L).At(k, A0, A1, A01, t, integral, E)))
			a.Show(
				"read out, the pair of −E is invertible and lies in the two charts",
				By(inIntegral, clause.At(a.TermAs[_IdealPair]("«pair»"))))
		}),
})}

// EffectivePairAvoidsPoint — the ideal pair of an effective divisor lies under no
// closed point outside its support: the invertible pairs inside the charts not
// under that point are a submonoid, by primality, holding the other closed points.
var EffectivePairAvoidsPoint = effectivePairAvoidsPointThm{family.Add(registry.ProofEntry{
	Name: "EffectivePairAvoidsPoint",
	Key:  "prop_6a1d931619120fc5",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀E:(prod(set(A), set(A)) → int). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(E)",
			"∀Q:prod(set(A), set(A)). 0 ≤ E(Q)",
			"«scPoint»(P)",
			"E(P) = 0",
		},
		Conclusion: "¬(fst(«pair») ⊆ fst(P) ∧ snd(«pair») ⊆ snd(P))",
		Abbrev: Abbrev{
			{Name: "pair", Text: "«scPair»(λQ:prod(set(A), set(A)). -E(Q))"},
			{Name: "away", Text: "{X:prod(set(A), set(A)) | " +
				"    «scInvertible»(X) ∧ fst(X) ⊆ A₀ ∧ snd(X) ⊆ A₁ ∧ ¬(fst(X) ⊆ fst(P) ∧ snd(X) ⊆ snd(P))}"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			E *Arrow[_IdealPair, Int],
			P *Expr[_IdealPair],
			curve, divisor, nonnegative, point, outside Fact,
		) {
			away := a.TermAs[Set[_IdealPair]]("«away»")
			structurePair := a.TermAs[_IdealPair]("(A₀, A₁)")
			clause := a.Have(
				"a pair away from P is an invertible pair inside the charts not under P",
				"∀X:prod(set(A), set(A)). "+
					"    X ∈ «away» ⇔ "+
					"    «scInvertible»(X) ∧ fst(X) ⊆ A₀ ∧ snd(X) ⊆ A₁ ∧ ¬(fst(X) ⊆ fst(P) ∧ snd(X) ⊆ snd(P))",
				BySets())
			invertible := a.Have(
				"so it is invertible",
				"∀X:prod(set(A), set(A)). X ∈ «away» ⇒ «scInvertible»(X)",
				a.ForEach(func(X *Expr[_IdealPair]) Action { return By(clause.At(X)) }))
			monoid := a.Conjuncts(
				GroupPremises(curve, ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")[0]
			identity := a.Have(
				"the structure pair is away from P",
				"(A₀, A₁) ∈ «away»",
				By(
					clause.At(structurePair),
					comm_monoid.IdentityIn.Read(monoid),
					curve,
					point,
					ClosedPointProper.Read(L).At(k, A0, A1, A01, t, P),
					pairs.Fst,
					pairs.Snd,
					set_order.SubsetRefl))
			closed := a.Have(
				"a product of pairs away from P is away from P",
				"∀X Y:prod(set(A), set(A)). X ∈ «away» ∧ Y ∈ «away» ⇒ «scMul»(X, Y) ∈ «away»",
				Derive(func(b *Argument) {
					X := b.FixAs[_IdealPair]("X")
					Y := b.FixAs[_IdealPair]("Y")
					members := b.Conjuncts(
						b.Assume(),
						"X is away from P",
						"Y is away from P")
					factorX := b.Conjuncts(
						b.Have(
							"read out for X",
							"«scInvertible»(X) ∧ fst(X) ⊆ A₀ ∧ snd(X) ⊆ A₁ ∧ ¬(fst(X) ⊆ fst(P) ∧ snd(X) ⊆ snd(P))",
							By(members[0], clause.At(X))),
						"X is invertible",
						"fst(X) lies in chart 0",
						"snd(X) lies in chart 1",
						"X is not under P")
					factorY := b.Conjuncts(
						b.Have(
							"read out for Y",
							"«scInvertible»(Y) ∧ fst(Y) ⊆ A₀ ∧ snd(Y) ⊆ A₁ ∧ ¬(fst(Y) ⊆ fst(P) ∧ snd(Y) ⊆ snd(P))",
							By(members[1], clause.At(Y))),
						"Y is invertible",
						"fst(Y) lies in chart 0",
						"snd(Y) lies in chart 1",
						"Y is not under P")
					product := b.Conjuncts(
						GroupPremises(
							curve,
							factorX[0],
							factorX[1],
							factorX[2],
							factorY[0],
							factorY[1],
							factorY[2],
							PairProductIntegral.Read(L).At(k, A0, A1, A01, t, X, Y)),
						"the product is invertible",
						"it lies under Y in chart 0",
						"and in chart 1")
					prime := b.Have(
						"a closed point above the product lies above a factor, so the product is not under P",
						"¬(fst(«scMul»(X, Y)) ⊆ fst(P) ∧ snd(«scMul»(X, Y)) ⊆ snd(P))",
						By(
							curve,
							factorX[0],
							factorX[1],
							factorX[2],
							factorY[0],
							factorY[1],
							factorY[2],
							point,
							factorX[3],
							factorY[3],
							ClosedPointPrime.Read(L).At(k, A0, A1, A01, t, X, Y, P)))
					b.Show(
						"the product is invertible, inside the charts and not under P",
						By(
							clause.At(b.TermAs[_IdealPair]("«scMul»(X, Y)")),
							product[0],
							prime,
							set_order.SubsetTrans.At(b.TermAs[Set[A]]("fst(«scMul»(X, Y))"), b.TermAs[Set[A]]("fst(Y)"), A0),
							set_order.SubsetTrans.At(b.TermAs[Set[A]]("snd(«scMul»(X, Y))"), b.TermAs[Set[A]]("snd(Y)"), A1),
							product[1],
							product[2],
							factorY[1],
							factorY[2]))
				}))
			support := a.Conjuncts(
				a.Unfolded(divisor, ClosedDivisorDef),
				"the support of E is finite",
				"and made of closed points")
			points := a.Have(
				"the closed points of the support are away from P",
				"∀Q:prod(set(A), set(A)). E(Q) ≠ 0 ⇒ Q ∈ «away»",
				Derive(func(b *Argument) {
					Q := b.FixAs[_IdealPair]("Q")
					nonzero := b.Assume()
					other := b.Have(
						"Q is a closed point",
						"«scPoint»(Q)",
						By(nonzero, support[1].At(Q)))
					notUnder := b.Have(
						"closed points are incomparable and E vanishes at P, so Q is not under P",
						"¬(fst(Q) ⊆ fst(P) ∧ snd(Q) ⊆ snd(P))",
						By(
							Normalized,
							nonzero,
							outside,
							curve,
							other,
							point,
							ClosedPointBelowPoint.Read(L).At(k, A0, A1, A01, t, Q, P)))
					b.Show(
						"a closed point is invertible and inside the charts",
						By(
							clause.At(Q),
							notUnder,
							curve,
							other,
							ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, Q),
							ClosedPointInCharts.Read(L).At(k, A0, A1, A01, t, Q)))
				}))
			inAway := a.Have(
				"so the pair of the effective divisor E is away from P",
				"«pair» ∈ «away»",
				By(
					curve,
					invertible,
					identity,
					closed,
					divisor,
					nonnegative,
					points,
					EffectivePairIn.Read(L).At(k, A0, A1, A01, t, away, E)))
			a.Show(
				"read out, it is not under P",
				By(inAway, clause.At(a.TermAs[_IdealPair]("«pair»"))))
		}),
})}

// ClosedDivisorShift — raising a divisor by one at a closed point multiplies the
// pair of its negative by that point.
var ClosedDivisorShift = closedDivisorShiftThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorShift",
	Key:  "prop_18fc94fb1e740d98",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀D:(prod(set(A), set(A)) → int). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
			"«scPoint»(P)",
		},
		Conclusion: "«scDivisor»(λQ:prod(set(A), set(A)). D(Q) + COND(Q = P, int_of_num(1), 0)) ∧ " +
			"«scPair»(λQ:prod(set(A), set(A)). -(D(Q) + COND(Q = P, int_of_num(1), 0))) = " +
			"lattice_pair_mul(field_ring(L), A₀, A₁, «scPair»(λQ:prod(set(A), set(A)). -D(Q)), P)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_IdealPair, Int],
			P *Expr[_IdealPair],
			curve, divisor, point Fact,
		) {
			one := a.TermAs[Int]("1")
			minusOne := a.TermAs[Int]("-1")
			up := a.TermAs[Fun[_IdealPair, Int]]("λQ:prod(set(A), set(A)). COND(Q = P, int_of_num(1), 0)")
			down := a.TermAs[Fun[_IdealPair, Int]]("λQ:prod(set(A), set(A)). COND(Q = P, -int_of_num(1), 0)")
			negated := a.TermAs[Fun[_IdealPair, Int]]("λQ:prod(set(A), set(A)). -D(Q)")
			pClosed := a.Have(
				"P is a closed divisor",
				"«scDivisor»(λQ:prod(set(A), set(A)). COND(Q = P, int_of_num(1), 0))",
				By(curve, point, ClosedDivisorPoint.Read(L).At(k, A0, A1, A01, t, P, one)))
			lowered := a.Conjuncts(
				GroupPremises(curve, point, ClosedDivisorPoint.Read(L).At(k, A0, A1, A01, t, P, minusOne)),
				"-P is a closed divisor",
				"of minus the degree of P",
				"with pair P")
			sum := a.Conjuncts(
				GroupPremises(curve, divisor, pClosed, ClosedDivisorAdd.Read(L).At(k, A0, A1, A01, t, D, up)),
				"D + P is a closed divisor",
				"its pair is the product",
				"its degree is the sum")
			negatedD := a.Conjuncts(
				GroupPremises(curve, divisor, ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, D)),
				"-D is a closed divisor",
				"the pair of D is invertible",
				"the pair of -D is its inverse",
				"and the degree changes sign")
			difference := a.Conjuncts(
				GroupPremises(
					curve, lowered[0], negatedD[0], ClosedDivisorAdd.Read(L).At(k, A0, A1, A01, t, negated, down)),
				"-D - P is a closed divisor",
				"its pair is the product of the pairs of -D and -P",
				"its degree is the difference")
			pointwise := a.Have(
				"the negative of D + P is -D - P",
				"(λQ:prod(set(A), set(A)). -(D(Q) + COND(Q = P, int_of_num(1), 0))) = "+
					"(λQ:prod(set(A), set(A)). -D(Q) + COND(Q = P, -int_of_num(1), 0))",
				Funext(),
				Derive(func(b *Argument) {
					b.FixAs[_IdealPair]("Q")
					b.Cases(b.TermAs[Bool]("Q = P"))
					b.When(
						"at P both sides are -D(P) - 1",
						func(c *Argument, at Fact) {
							c.Show(
								"at P the conditions hold",
								ByArith(at))
						})
					b.Otherwise(
						"off P both sides are -D(Q)",
						func(c *Argument, off Fact) {
							c.Show(
								"off P the conditions fail",
								ByArith(off))
						})
				}))
			pair := a.Have(
				"so its pair is the product of the pair of -D and P",
				"«scPair»(λQ:prod(set(A), set(A)). -(D(Q) + COND(Q = P, int_of_num(1), 0))) = "+
					"lattice_pair_mul(field_ring(L), A₀, A₁, «scPair»(λQ:prod(set(A), set(A)). -D(Q)), P)",
				pointwise.Rw(),
				By(difference[1], lowered[2]))
			a.Show(
				"D + P is a closed divisor of that pair",
				By(sum[0], pair))
		}),
})}

// EffectiveDivisorLower — an effective divisor nonzero at a point stays effective
// when lowered there by one: its ideal pair is that of the lowered divisor times
// the point, and raising undoes the lowering.
var EffectiveDivisorLower = effectiveDivisorLowerThm{family.Add(registry.ProofEntry{
	Name: "EffectiveDivisorLower",
	Key:  "prop_29ae156a24f2b650",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀E:(prod(set(A), set(A)) → int). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(E)",
			"∀Q:prod(set(A), set(A)). 0 ≤ E(Q)",
			"E(P) ≠ 0",
		},
		Conclusion: "«scDivisor»(«lowered») ∧ " +
			"(∀Q:prod(set(A), set(A)). 0 ≤ «lowered»(Q)) ∧ " +
			"«scPair»(λQ:prod(set(A), set(A)). -E(Q)) = " +
			"lattice_pair_mul(field_ring(L), A₀, A₁, «scPair»(λQ:prod(set(A), set(A)). -«lowered»(Q)), P) ∧ " +
			"(∀Q:prod(set(A), set(A)). «lowered»(Q) + COND(Q = P, int_of_num(1), 0) = E(Q))",
		Abbrev: Abbrev{
			{Name: "lowered", Text: "λQ:prod(set(A), set(A)). E(Q) + COND(Q = P, -int_of_num(1), 0)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			E *Arrow[_IdealPair, Int],
			P *Expr[_IdealPair],
			curve, divisor, nonnegative, nonzero Fact,
		) {
			minusOne := a.TermAs[Int]("-1")
			down := a.TermAs[Fun[_IdealPair, Int]]("λQ:prod(set(A), set(A)). COND(Q = P, -int_of_num(1), 0)")
			lowered := a.TermAs[Fun[_IdealPair, Int]]("«lowered»")
			support := a.Conjuncts(
				a.Unfolded(divisor, ClosedDivisorDef),
				"the support of E is finite",
				"and made of closed points")
			closedPoint := a.Have(
				"P lies in the support, so it is a closed point",
				"«scPoint»(P)",
				By(nonzero, support[1].At(P)))
			minusP := a.Conjuncts(
				GroupPremises(curve, closedPoint, ClosedDivisorPoint.Read(L).At(k, A0, A1, A01, t, P, minusOne)),
				"-P is a closed divisor",
				"of minus the degree of P",
				"with pair P")
			lower := a.Conjuncts(
				GroupPremises(curve, divisor, minusP[0], ClosedDivisorAdd.Read(L).At(k, A0, A1, A01, t, E, down)),
				"E - P is a closed divisor",
				"its pair is the product",
				"its degree is the difference")
			positive := a.Have(
				"E(P), nonzero and not negative, is at least 1",
				"1 ≤ E(P)",
				ByArith(nonzero, nonnegative.At(P)))
			effective := a.Have(
				"E - P is effective",
				"∀Q:prod(set(A), set(A)). 0 ≤ «lowered»(Q)",
				Derive(func(b *Argument) {
					Q := b.FixAs[_IdealPair]("Q")
					b.Cases(b.TermAs[Bool]("Q = P"))
					b.When(
						"at P the value drops by one from at least 1",
						func(c *Argument, at Fact) {
							c.Show(
								"E(P) - 1 is not negative",
								at.Rw(),
								ByArith(positive))
						})
					b.Otherwise(
						"off P the value is that of E",
						func(c *Argument, off Fact) {
							c.Show(
								"E is effective",
								ByArith(off, nonnegative.At(Q)))
						})
				}))
			agrees := a.Have(
				"raising undoes the lowering, point by point",
				"∀Q:prod(set(A), set(A)). «lowered»(Q) + COND(Q = P, int_of_num(1), 0) = E(Q)",
				Derive(func(b *Argument) {
					b.FixAs[_IdealPair]("Q")
					b.Cases(b.TermAs[Bool]("Q = P"))
					b.When(
						"at P the two terms are -1 and 1",
						func(c *Argument, at Fact) {
							c.Show(
								"minus one and plus one cancel",
								ByArith(at))
						})
					b.Otherwise(
						"off P the two terms are 0",
						func(c *Argument, off Fact) {
							c.Show(
								"neither term moves E(Q)",
								ByArith(off))
						})
				}))
			negatives := a.Have(
				"so the negative of the raised lowering is -E",
				"(λQ:prod(set(A), set(A)). -(«lowered»(Q) + COND(Q = P, int_of_num(1), 0))) = "+
					"(λQ:prod(set(A), set(A)). -E(Q))",
				Funext(),
				a.ForEach(func(Q *Expr[_IdealPair]) Action { return ByArith(agrees.At(Q)) }))
			shift := a.Conjuncts(
				GroupPremises(
					curve, lower[0], closedPoint, ClosedDivisorShift.Read(L).At(k, A0, A1, A01, t, lowered, P)),
				"the raised lowering is a closed divisor",
				"whose negative has the shifted pair")
			pair := a.Have(
				"so the pair of -E is that of the lowering, times P",
				"«scPair»(λQ:prod(set(A), set(A)). -E(Q)) = "+
					"lattice_pair_mul(field_ring(L), A₀, A₁, «scPair»(λQ:prod(set(A), set(A)). -«lowered»(Q)), P)",
				negatives.RwRev(),
				By(shift[1]))
			a.Show(
				"the lowering is an effective closed divisor, the "+
					"pair of −E is its pair times P, and raising undoes it",
				By(lower[0], effective, pair, agrees))
		}),
})}

// EffectivePairBelowSupport — the ideal pair of an effective divisor lies under
// each point of its support: it is an integral pair times that point.
var EffectivePairBelowSupport = effectivePairBelowSupportThm{family.Add(registry.ProofEntry{
	Name: "EffectivePairBelowSupport",
	Key:  "prop_287138d7a46c99f4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). " +
			"∀k A₀ A₁ A₀₁:set(A). " +
			"∀t:A. " +
			"∀E:(prod(set(A), set(A)) → int). " +
			"∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(E)",
			"∀Q:prod(set(A), set(A)). 0 ≤ E(Q)",
			"E(P) ≠ 0",
		},
		Conclusion: "fst(«scPair»(λQ:prod(set(A), set(A)). -E(Q))) ⊆ fst(P) ∧ " +
			"snd(«scPair»(λQ:prod(set(A), set(A)). -E(Q))) ⊆ snd(P)",
		Abbrev: Abbrev{
			{Name: "lowered", Text: "λQ:prod(set(A), set(A)). E(Q) + COND(Q = P, -int_of_num(1), 0)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			E *Arrow[_IdealPair, Int],
			P *Expr[_IdealPair],
			curve, divisor, nonnegative, nonzero Fact,
		) {
			lowered := a.TermAs[Fun[_IdealPair, Int]]("«lowered»")
			point := a.Have(
				"P lies in the support, so it is a closed point",
				"«scPoint»(P)",
				By(
					nonzero,
					a.Conjuncts(
						a.Unfolded(divisor, ClosedDivisorDef),
						"the support of E is finite",
						"and made of closed points")[1].At(P)))
			step := a.Conjuncts(
				GroupPremises(
					curve, divisor, nonnegative, nonzero, EffectiveDivisorLower.Read(L).At(k, A0, A1, A01, t, E, P)),
				"the lowering is a closed divisor",
				"it is effective",
				"the pair of -E is that of the lowering, times P",
				"raising undoes the lowering, point by point")
			loweringPair := a.Conjuncts(
				GroupPremises(
					step[1], curve, step[0], EffectivePairIntegral.Read(L).At(k, A0, A1, A01, t, lowered)),
				"the pair of the lowering is invertible",
				"it lies in chart 0",
				"it lies in chart 1")
			invertibleP := a.Have(
				"P is invertible",
				"«scInvertible»(P)",
				By(curve, point, ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, P)))
			pInCharts := a.Conjuncts(
				GroupPremises(curve, point, ClosedPointInCharts.Read(L).At(k, A0, A1, A01, t, P)),
				"fst(P) lies in chart 0",
				"snd(P) lies in chart 1")
			product := a.Conjuncts(
				GroupPremises(curve, loweringPair[0], loweringPair[1], loweringPair[2], invertibleP, pInCharts[0], pInCharts[1], PairProductIntegral.Read(
					L).At(
					k,
					A0,
					A1,
					A01,
					t,
					a.TermAs[_IdealPair]("«scPair»(λQ:prod(set(A), set(A)). -«lowered»(Q))"),
					P)),
				"the product is invertible",
				"it lies under P in chart 0",
				"and in chart 1")
			a.Show(
				"that product is the pair of -E",
				step[2].Rw(),
				By(product[1], product[2]))
		}),
})}

// IntegralPairHasDivisor — an invertible pair inside the charts is the ideal pair
// of exactly one effective closed divisor. By induction on the
// colength: a proper pair lies under a closed point P and divides by it to a pair
// of smaller colength, whose divisor raised at P is a divisor of the pair; and
// any effective divisor of the pair does not vanish at P, so it lowers there to a
// divisor of the quotient.
var IntegralPairHasDivisor = integralPairHasDivisorThm{family.Add(registry.ProofEntry{
	Name: "IntegralPairHasDivisor",
	Key:  "prop_52d139434f0327a0",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀I:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scInvertible»(I)",
			"fst(I) ⊆ A₀",
			"snd(I) ⊆ A₁",
		},
		Conclusion: "∃!D:(prod(set(A), set(A)) → int). «ofPair»(I, D)",
		Abbrev: Abbrev{
			{Name: "ofPair", Text: "λX:prod(set(A), set(A)). λD:(prod(set(A), set(A)) → int). " +
				"    «scDivisor»(D) ∧ " +
				"    (∀P:prod(set(A), set(A)). 0 ≤ D(P)) ∧ " +
				"    X = «scPair»(λP:prod(set(A), set(A)). -D(P))"},
			{Name: "quotient", Text: "λX:prod(set(A), set(A)). λP:prod(set(A), set(A)). " +
				"    lattice_pair_mul(field_ring(L), A₀, A₁, X, lattice_pair_inverse(field_ring(L), A₀, A₁, P))"},
			{Name: "dim", Text: "λS:set(A). λX:set(A). " +
				"    module_dim(restrict_ring(field_ring(L), k), " +
				"        quotient_module(restrict_module(regular_module(field_ring(L)), S), X))"},
			{Name: "colength", Text: "λX:prod(set(A), set(A)). «dim»(A₀, fst(X)) + «dim»(A₁, snd(X))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			I *Expr[_IdealPair],
			curve, invertible, inChart0, inChart1 Fact,
		) {
			indexed := a.Have(
				"every invertible pair inside the charts has its one divisor, at each colength",
				Statement{
					Binders: "∀n:num. ∀X:prod(set(A), set(A)).",
					Hypotheses: []string{
						"«scInvertible»(X)",
						"fst(X) ⊆ A₀",
						"snd(X) ⊆ A₁",
						"«colength»(X) = n",
					},
					Conclusion: "∃!D:(prod(set(A), set(A)) → int). «ofPair»(X, D)",
				},
				ByInduction(nat_order.StrongInduction,
					Case(
						"pairs of smaller colength supply the quotient by a closed point",
						Derive(func(b *Argument) {
							b.FixAs[Nat]("n")
							ih := b.Assume()
							X := b.FixAs[_IdealPair]("X")
							datum := b.Conjuncts(
								b.Assume(),
								"X is invertible",
								"fst(X) lies in chart 0",
								"snd(X) lies in chart 1",
								"X has colength n")
							b.Cases(b.TermAs[Bool]("X = (A₀, A₁)"))
							b.When(
								"the structure pair has the zero divisor alone",
								func(c *Argument, whole Fact) {
									zero := c.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). 0")
									trivial := c.Conjuncts(
										GroupPremises(curve, ClosedDivisorZero.Read(L).At(k, A0, A1, A01, t)),
										"the zero divisor is a closed divisor",
										"its pair is the structure pair",
										"its degree is 0")
									negated := c.Have(
										"the negative of zero is zero",
										"(λP:prod(set(A), set(A)). -0) = (λP:prod(set(A), set(A)). int_of_num(0))",
										Funext(),
										ByArith())
									pair := c.Have(
										"so X is the pair of the negative of the zero divisor",
										"X = «scPair»(λP:prod(set(A), set(A)). -0)",
										negated.Rw(),
										By(whole, trivial[1]))
									c.Take(zero)
									c.Do(SplitConj(
										Case(
											"the zero divisor is a divisor of X",
											By(trivial[0], pair)),
										Case(
											"an effective divisor of the structure pair has empty support",
											Derive(func(d *Argument) {
												E := d.FixAs[Fun[_IdealPair, Int]]("E")
												given := d.Conjuncts(
													d.Assume(),
													"E is a closed divisor",
													"E is effective",
													"X is its pair")
												d.Do(Funext())
												Q := d.FixAs[_IdealPair]("Q")
												nonzero := d.SupposeNot()
												under := d.Conjuncts(
													GroupPremises(
														curve, given[0], given[1], nonzero, EffectivePairBelowSupport.Read(L).At(k, A0, A1, A01, t, E, Q)),
													"the pair lies under Q in chart 0",
													"and in chart 1")
												point := d.Conjuncts(
													d.Unfolded(given[0], ClosedDivisorDef),
													"the support of E is finite",
													"and made of closed points")[1]
												proper := d.Have(
													"Q is a closed point, so the structure pair is not under it",
													"¬(A₀ ⊆ fst(Q) ∧ A₁ ⊆ snd(Q))",
													By(curve, nonzero, point.At(Q), ClosedPointProper.Read(L).At(k, A0, A1, A01, t, Q)))
												d.Show(
													"yet the structure pair is the pair of E",
													By(Normalized, proper, under[0], under[1], given[2], whole, pairs.Fst, pairs.Snd))
											}))))
								})
							b.Otherwise(
								"a proper pair divides by a closed point above it",
								func(c *Argument, proper Fact) {
									P, above := c.ObtainAs[_IdealPair](
										"a closed point lies above X",
										"∃P:prod(set(A), set(A)). «scPoint»(P) ∧ fst(X) ⊆ fst(P) ∧ snd(X) ⊆ snd(P)",
										By(
											curve,
											datum[0],
											datum[1],
											datum[2],
											proper,
											ProperPairBelowPoint.Read(L).At(k, A0, A1, A01, t, X)),
										Named("P"))
									under := c.Conjuncts(
										above,
										"P is a closed point",
										"above X in chart 0",
										"and in chart 1")
									quotient := c.Conjuncts(
										GroupPremises(
											curve,
											datum[0],
											datum[1],
											datum[2],
											under[0],
											under[1],
											under[2],
											PairDivideByPoint.Read(L).At(k, A0, A1, A01, t, X, P)),
										"X over P is invertible",
										"and lies in chart 0",
										"and in chart 1",
										"times P it is X",
										"and its colength is smaller")
									J := c.TermAs[_IdealPair]("«quotient»(X, P)")
									lower := c.Have(
										"the colength of the quotient is below n",
										"«colength»(«quotient»(X, P)) < n",
										ByArith(quotient[4], datum[3]))
									unique := c.Have(
										"so the quotient has its one divisor",
										"∃!D:(prod(set(A), set(A)) → int). «ofPair»(«quotient»(X, P), D)",
										By(
											quotient[0],
											quotient[1],
											quotient[2],
											lower,
											ih.At(c.TermAs[Nat]("«colength»(«quotient»(X, P))"), J)))
									C, center := c.UnpackAs[Fun[_IdealPair, Int]](unique, "C")
									own := c.Conjuncts(
										c.Have(
											"call it C",
											"«ofPair»(«quotient»(X, P), C)",
											By(center.At(C))),
										"C is a closed divisor",
										"C is effective",
										"the quotient is its pair")
									raised := c.TermAs[Fun[_IdealPair, Int]](
										"λQ:prod(set(A), set(A)). C(Q) + COND(Q = P, int_of_num(1), 0)")
									shift := c.Conjuncts(
										GroupPremises(curve, own[0], under[0], ClosedDivisorShift.Read(L).At(k, A0, A1, A01, t, C, P)),
										"C raised at P is a closed divisor",
										"whose negative has the pair of -C times P")
									effective := c.Have(
										"C raised at P is effective",
										"∀Q:prod(set(A), set(A)). 0 ≤ C(Q) + COND(Q = P, int_of_num(1), 0)",
										Derive(func(d *Argument) {
											Q := d.FixAs[_IdealPair]("Q")
											d.Cases(d.TermAs[Bool]("Q = P"))
											d.When(
												"at P the value rises",
												func(e *Argument, at Fact) {
													e.Show(
														"C is effective",
														ByArith(at, own[1].At(Q)))
												})
											d.Otherwise(
												"off P the value is that of C",
												func(e *Argument, off Fact) {
													e.Show(
														"C is effective",
														ByArith(off, own[1].At(Q)))
												})
										}))
									pair := c.Have(
										"its negative has pair X",
										"X = «scPair»(λQ:prod(set(A), set(A)). -(C(Q) + COND(Q = P, int_of_num(1), 0)))",
										By(shift[1], own[2], quotient[3]))
									c.Take(raised)
									c.Do(SplitConj(
										Case(
											"C raised at P is a divisor of X",
											By(shift[0], effective, pair)),
										Case(
											"every effective divisor of X is C raised at P",
											Derive(func(d *Argument) {
												E := d.FixAs[Fun[_IdealPair, Int]]("E")
												given := d.Conjuncts(
													d.Assume(),
													"E is a closed divisor",
													"E is effective",
													"X is its pair")
												nonzeroAtP := d.Have(
													"E does not vanish at P, the pair of E lying under P",
													"E(P) ≠ 0",
													By(
														Normalized,
														curve,
														given[0],
														given[1],
														under[0],
														under[1],
														under[2],
														given[2],
														EffectivePairAvoidsPoint.Read(L).At(k, A0, A1, A01, t, E, P)))
												lowered := d.TermAs[Fun[_IdealPair, Int]](
													"λQ:prod(set(A), set(A)). E(Q) + COND(Q = P, -int_of_num(1), 0)")
												step := d.Conjuncts(
													GroupPremises(
														curve, given[0], given[1], nonzeroAtP, EffectiveDivisorLower.Read(L).At(k, A0, A1, A01, t, E, P)),
													"E lowered at P is a closed divisor",
													"it is effective",
													"the pair of -E is its pair times P",
													"raising undoes the lowering, point by point")
												factor := d.TermAs[_IdealPair](
													"«scPair»(λQ:prod(set(A), set(A)). -(E(Q) + COND(Q = P, -int_of_num(1), 0)))")
												integral := d.Conjuncts(
													GroupPremises(
														step[1], curve, step[0], EffectivePairIntegral.Read(L).At(k, A0, A1, A01, t, lowered)),
													"the pair of the lowering is invertible",
													"it lies in chart 0",
													"it lies in chart 1")
												invertibleP := d.Have(
													"P is invertible",
													"«scInvertible»(P)",
													By(curve, under[0], ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, P)))
												cancels := d.Conjuncts(
													GroupPremises(
														curve, integral[0], invertibleP, PairQuotient.Read(L).At(k, A0, A1, A01, t, factor, P)),
													"the quotient by P is invertible",
													"multiplying back recovers it",
													"and dividing a product by P recovers the factor")
												ofQuotient := d.Have(
													"so E lowered at P is a divisor of the quotient",
													"«ofPair»(«quotient»(X, P), λQ:prod(set(A), set(A)). E(Q) + COND(Q = P, -int_of_num(1), 0))",
													By(step[0], step[1], step[2], given[2], cancels[2], integral[0]))
												same := d.Have(
													"so it is C, point by point",
													"∀Q:prod(set(A), set(A)). E(Q) + COND(Q = P, -int_of_num(1), 0) = C(Q)",
													By(ofQuotient, center.At(lowered)))
												d.Show(
													"and E is C raised at P",
													Funext(),
													d.ForEach(func(Q *Expr[_IdealPair]) Action {
														return ByArith(same.At(Q), step[3].At(Q))
													}))
											}))))
								})
						}))))
			colength := a.TermAs[Nat]("«colength»(I)")
			a.Show(
				"I has its colength",
				By(invertible, inChart0, inChart1, indexed.At(colength, I)))
		}),
})}

// ClosedDivisorFactorization — closed points are invertible pairs, and an
// invertible pair inside the charts is the ideal pair of exactly one effective
// closed divisor: the ideals of a smooth curve factor uniquely into closed points.
var ClosedDivisorFactorization = closedDivisorFactorizationThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorFactorization",
	Key:  "prop_e4661d40ddaed33f",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "(∀P:prod(set(A), set(A)). «scPoint»(P) ⇒ «scInvertible»(P)) ∧ " +
			"(∀I:prod(set(A), set(A)). " +
			"    «scInvertible»(I) ∧ fst(I) ⊆ A₀ ∧ snd(I) ⊆ A₁ ⇒ " +
			"    ∃!D:(prod(set(A), set(A)) → int). " +
			"        «scDivisor»(D) ∧ " +
			"        (∀P:prod(set(A), set(A)). 0 ≤ D(P)) ∧ " +
			"        I = «scPair»(λP:prod(set(A), set(A)). -D(P)))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			a.Show(
				"closed points are invertible, and an invertible pair "+
					"inside the charts has exactly one effective divisor",
				By(
					curve,
					At(Read(ClosedPointInvertible, L), k, A0, A1, A01, t),
					At(Read(IntegralPairHasDivisor, L), k, A0, A1, A01, t)))
		}),
})}
