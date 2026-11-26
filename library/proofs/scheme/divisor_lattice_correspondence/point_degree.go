// point_degree.go — the lattice degree of a closed point. Measured against the
// structure pair, the ideals of a point cut its residue field out of a chart
// that holds it, and on the overlap they cut nothing that the second chart
// does not cut as well, so the point's pair has minus its residue degree. The
// degree reads the powers of a point additively, so the lattice degree of a
// closed divisor's pair is the divisor's degree.

package divisor_lattice_correspondence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_sequence"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ChartPointFiniteQuotient — the ideal a closed point has in a chart, the whole
// chart off the point and a maximal ideal on it, has finite colength over the
// constants: either way it is a nonzero ideal of the chart.
var ChartPointFiniteQuotient = chartPointFiniteQuotientThm{family.Add(registry.ProofEntry{
	Name: "ChartPointFiniteQuotient",
	Key:  "prop_7dce4149d0439212",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀H:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"H = A₀ ∨ maximal_ideal(restrict_ring(field_ring(L), A₀), H)",
		},
		Conclusion: "finite_dimensional(restrict_ring(field_ring(L), k), " +
			"    quotient_module(restrict_module(regular_module(field_ring(L)), A₀), H))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			H *Expr[Set[A]],
			curve, chartPoint Fact,
		) {
			nonzeroIdeal := a.Have(
				"H is a nonzero ideal of the chart",
				"ring_ideal(«chart», H) ∧ H ≠ {L.zero}",
				Derive(func(b *Argument) {
					b.Cases(b.TermAs[Bool]("H = A₀"))
					b.When(
						"the chart, an ideal of itself, holds the nonzero coordinate",
						func(c *Argument, whole Fact) {
							chartRing := c.Have(
								"the chart is a ring",
								"comm_ring_on(«chart»)",
								By(
									curve,
									smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t),
									comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A0)))
							coordinate := c.Have(
								"t is a nonzero element of the chart",
								"t ∈ A₀ ∧ t ≠ L.zero",
								By(curve, smooth_curve.ChartOverlap.Read(L).At(k, A0, A1, A01, t)))
							nonzero := c.Have(
								"so the chart is not {0}",
								"H ≠ {L.zero}",
								BySets(whole, coordinate))
							c.Show(
								"H is the chart",
								By(Normalized, whole, nonzero, ring_ideal.CarrierIdeal.Read(chartRing)))
						})
					b.Otherwise(
						"a maximal ideal of the chart is a nonzero ideal",
						func(c *Argument, notWhole Fact) {
							maximal := c.Have(
								"H, not the whole chart, is maximal in it",
								"maximal_ideal(«chart», H)",
								By(Normalized, notWhole, chartPoint))
							c.Show(
								"it is an ideal, and the zero ideal is not maximal in a chart",
								By(
									curve,
									maximal,
									ring_ideal.MaximalIdealDef.At(c.TermAs[RingOps[A]]("«chart»"), H),
									smooth_curve.ChartMaximalNonzero.Read(L).At(k, A0, A1, A01, t, H)))
						})
				}))
			a.Show(
				"a nonzero ideal of a chart has finite colength",
				By(curve, nonzeroIdeal, smooth_curve.ChartIdealFiniteQuotient.Read(L).At(k, A0, A1, A01, t, H)))
		}),
})}

// ClosedPointLatticeDegree — the pair of a closed point has lattice degree minus
// its residue degree. χ(A₀, A₁) − χ(P) is d₀ + d₁ − d₀₁ for the quotients of the
// structure pair by P on the two charts and the overlap (EulerAdditive). A point
// of one chart alone is the whole of the other, so that chart's quotient and the
// overlap's vanish; on a point of both charts the second component is contracted
// from its span, so d₁ = d₀₁ and d₀ remains. What remains is the residue degree.
var ClosedPointLatticeDegree = closedPointLatticeDegreeThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointLatticeDegree",
	Key:  "prop_d2b507334486bc41",
	Reading: "P is the pair of ideals vanishing at the point, the pair of the divisor " +
		"−P, which is why the sign is minus. curve_closed_degree reads the residue " +
		"dimension on the first chart holding the point; the lattice degree names no chart.",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"«scCurve»", "«scPoint»(P)"},
		Conclusion: "curve_degree(field_ring(L), k, A₀, A₁, A₀₁, P) = -«scPointDegree»(P)",
		Abbrev: Abbrev{
			{Name: "constants", Text: "restrict_ring(field_ring(L), k)"},
			{Name: "chartZero", Text: "restrict_ring(field_ring(L), A₀)"},
			{Name: "chartOne", Text: "restrict_ring(field_ring(L), A₁)"},
			{Name: "vectors", Text: "restrict_module(regular_module(field_ring(L)))"},
			{Name: "functionField", Text: "regular_module(field_ring(L))"},
			{Name: "euler", Text: "lattice_pair_euler(«overlap», k, «functionField»)"},
			{Name: "span", Text: "module_span(«overlap», «functionField»)"},
			{Name: "quotientZero", Text: "quotient_module(«vectors»(A₀), fst(P))"},
			{Name: "quotientOne", Text: "quotient_module(«vectors»(A₁), snd(P))"},
			{Name: "quotientOverlap", Text: "quotient_module(«vectors»(«span»(A₀)), «span»(fst(P)))"},
			{Name: "dimZero", Text: "module_dim(«constants», «quotientZero»)"},
			{Name: "dimOne", Text: "module_dim(«constants», «quotientOne»)"},
			{Name: "dimOverlap", Text: "module_dim(«constants», «quotientOverlap»)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_IdealPair],
			curve, point Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			overlap := a.TermAs[RingOps[A]]("«overlap»")
			constantsRing := a.TermAs[RingOps[A]]("«constants»")
			chartZero := a.TermAs[RingOps[A]]("«chartZero»")
			chartOne := a.TermAs[RingOps[A]]("«chartOne»")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("«functionField»")
			inverse := a.TermAs[A]("L.inv(t)")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			structure := a.TermAs[_IdealPair]("(A₀, A₁)")
			first, second := a.TermAs[Set[A]]("fst(P)"), a.TermAs[Set[A]]("snd(P)")
			spanned := a.TermAs[Set[A]]("«span»(A₀)")

			overLine := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			data := a.Conjuncts(
				GroupPremises(overLine, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)),
				"the overlap lies in L",
				"the charts and their overlap are a biaffine datum",
				"k is a subfield of L",
				"the structure pair is a lattice pair",
				"its ambient is the overlap",
				"the structure pair is invertible",
				"the constants form a field",
				"the constants lie in both charts")
			biaffine, structurePair := data[1], data[3]
			clauses := a.Conjuncts(
				a.Unfolded(point, smooth_curve.CurveClosedPointDef),
				"fst(P) is chart 0 or maximal in it",
				"snd(P) is chart 1 or maximal in it",
				"P is not the structure pair",
				"its two ideals generate one ideal of the overlap",
				"which is proper where P lies on both charts")
			invertible := a.Have(
				"the point is an invertible pair",
				"«scInvertible»(P)",
				By(curve, point, closed_divisor.ClosedPointInvertible.Read(L).At(k, A0, A1, A01, t, P)))
			pair := a.Conjuncts(
				a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(P) is invertible",
				"snd(P) is invertible",
				"P is a lattice pair")[2]
			otherCurve := a.Have(
				"the curve reads the same from its other chart",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			inside := a.Have(
				"the ideals of the point lie in their charts",
				"fst(P) ⊆ A₀ ∧ snd(P) ⊆ A₁",
				By(curve, point, closed_divisor.ClosedPointInCharts.Read(L).At(k, A0, A1, A01, t, P)))
			finiteQuotients := a.Have(
				"and have finite colength there",
				"finite_dimensional(«constants», «quotientZero») ∧ finite_dimensional(«constants», «quotientOne»)",
				By(
					curve,
					otherCurve,
					clauses[0],
					clauses[1],
					ChartPointFiniteQuotient.Read(L).At(k, A0, A1, A01, t, first),
					ChartPointFiniteQuotient.Read(L).At(k, A1, A0, A01, inverse, second)))
			overlapSubfield := a.Have(
				"k is a field under the overlap's operations",
				"ring_subfield(«overlap», L.inv, k)",
				By(
					curve,
					smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t),
					field.SubfieldRingSubfield.Read(L).At(k, A01)))
			kInCharts := a.Have(
				"k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(data[7]))
			euler := a.Simplified(
				lattice_pair_sequence.EulerAdditive.At(overlap, A0, A1, t, inverse, k, inv, vectors, structure, P),
				Fwd(module_record.RestrictRingTwice),
				Fwd(module_record.RestrictModuleTwice),
				Fwd(pairs.Fst),
				Fwd(pairs.Snd),
				Fwd(lattice_pair.LatticePairAmbientDef))
			difference := a.Have(
				"χ(A₀, A₁) − χ(P) is the alternating sum of the three quotient dimensions",
				"«euler»((A₀, A₁)) - «euler»(P) = "+
					"int_of_num(«dimZero») + int_of_num(«dimOne») - int_of_num(«dimOverlap»)",
				By(
					euler,
					biaffine,
					overlapSubfield,
					kInCharts,
					structurePair,
					pair,
					inside,
					finiteQuotients,
					overLine,
					invertible,
					algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, P)))
			degree := a.Have(
				"the degree of P is χ(P) − χ(A₀, A₁)",
				"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, P) = «euler»(P) - «euler»((A₀, A₁))",
				Simp(Fwd(curve_degree.CurveDegreeDef)),
				Refl())

			structureData := a.Conjuncts(
				a.Simplified(
					a.Unfolded(structurePair, lattice_pair.LatticePairDef),
					Fwd(module_record.RestrictRingTwice),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				"L is a module over the overlap",
				"chart 0 is a module over itself",
				"chart 1 is a module over itself",
				"the two span one module")
			pointData := a.Conjuncts(
				a.Have(
					"the ideals of the point are modules over their charts, and they span one module",
					"submodule(«chartZero», «functionField», fst(P)) ∧ "+
						"submodule(«chartOne», «functionField», snd(P)) ∧ "+
						"«span»(fst(P)) = «span»(snd(P))",
					By(a.Simplified(
						a.Unfolded(pair, lattice_pair.LatticePairDef),
						Fwd(module_record.RestrictRingTwice)))),
				"fst(P) is a module over chart 0",
				"snd(P) is a module over chart 1",
				"the two span one module")
			moduleOverlap, chartsSpan, pointSpan := structureData[0], structureData[3], pointData[2]

			// Quotients of a space by itself, over k.
			moduleK := a.Have(
				"k is a subring of the overlap, so L is a space over k",
				"module_on(«constants», «functionField»)",
				By(
					Normalized,
					moduleOverlap,
					biaffine,
					overlapSubfield,
					kInCharts,
					lattice_pair.ChartFieldSubring.At(overlap, A0, A1, t, inverse, k, inv),
					module.ModuleRestrictScalars.At(overlap, vectors, k),
					module_record.RestrictRingTwice.At(ring, A01, k)))
			constants := a.Have(
				"k is a field of scalars",
				"ring_subfield(«constants», L.inv, k)",
				By(
					curve,
					smooth_curve.ChartSubring.Read(L).At(k, A0, A1, A01, t),
					field.SubfieldRingSubfield.Read(L).At(k, k)))
			vanishes := a.Have(
				"a subspace of L modulo itself has dimension zero",
				Statement{
					Binders:    "∀X:set(A).",
					Hypotheses: []string{"submodule(«constants», «functionField», X)"},
					Conclusion: "module_dim(«constants», quotient_module(«vectors»(X), X)) = 0",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[Set[A]]("X")
					subspace := b.Assume()
					b.Show(
						"X lies in itself, and the quotient of X by X is zero",
						By(
							moduleK,
							constants,
							subspace,
							set_order.SubsetRefl,
							module_dimension.QuotientDimZeroIff.At(constantsRing, vectors, inv, X, X)))
				}))
			spanModule := a.Have(
				"the span of chart 0 is a module over the overlap",
				"submodule(«overlap», «functionField», «span»(A₀))",
				By(moduleOverlap, submodule.SubmoduleSubset.Read(structureData[1]), submodule.SpanSubmodule))
			inOverlap := a.Have(
				"k lies in the overlap",
				"k ⊆ A₀₁",
				By(biaffine, kInCharts, lattice_pair.ChartSubsetInOverlap.At(overlap, A0, A1, t, inverse, k)))
			subspaces := a.Have(
				"over k, the charts and the span of chart 0 are subspaces of L",
				"submodule(«constants», «functionField», A₀) ∧ "+
					"submodule(«constants», «functionField», A₁) ∧ "+
					"submodule(«constants», «functionField», «span»(A₀))",
				By(
					kInCharts,
					structureData[1],
					structureData[2],
					spanModule,
					inOverlap,
					submodule.SubmoduleRestrictScalars.At(chartZero, vectors, A0, constantsRing),
					submodule.SubmoduleRestrictScalars.At(chartOne, vectors, A1, constantsRing),
					submodule.SubmoduleRestrictScalars.At(overlap, vectors, spanned, constantsRing)))
			parts := a.Conjuncts(
				subspaces,
				"chart 0 is a subspace of L",
				"chart 1 is a subspace of L",
				"so is the span of chart 0")
			degreeProper := a.Have(
				"where fst(P) is proper the residue degree is the colength in chart 0",
				"fst(P) ≠ A₀ ⇒ «scPointDegree»(P) = «dimZero»",
				Derive(func(b *Argument) {
					proper := b.Assume()
					b.Do(Simp(
						Fwd(smooth_curve.ClosedPointDegreeDef),
						Fwd(biaffine_rational_point.PointChartDef),
						Fwd(biaffine_rational_point.PointIdealDef)))
					b.Show(
						"the conditions read the proper ideal",
						By(proper))
				}))
			degreeWhole := a.Have(
				"where fst(P) is whole it is the colength in chart 1",
				"fst(P) = A₀ ⇒ «scPointDegree»(P) = «dimOne»",
				Derive(func(b *Argument) {
					whole := b.Assume()
					b.Do(Simp(
						Fwd(smooth_curve.ClosedPointDegreeDef),
						Fwd(biaffine_rational_point.PointChartDef),
						Fwd(biaffine_rational_point.PointIdealDef)))
					b.Show(
						"the conditions read the whole chart",
						By(whole))
				}))

			a.Cases(a.TermAs[Bool]("snd(P) = A₁"))
			a.When(
				"a point of chart 0 alone: chart 1 and the overlap lose nothing, and d₀ is the residue degree",
				func(b *Argument, secondWhole Fact) {
					firstProper := b.Have(
						"fst(P) is proper, P not being the structure pair",
						"fst(P) ≠ A₀",
						By(Normalized, clauses[2], secondWhole))
					zeroOne := b.Have(
						"chart 1 modulo itself vanishes",
						"«dimOne» = 0",
						By(secondWhole, parts[1], vanishes.At(A1)))
					sameSpan := b.Have(
						"the point and the structure pair span one module",
						"«span»(fst(P)) = «span»(A₀)",
						By(secondWhole, pointSpan, chartsSpan))
					zeroOverlap := b.Have(
						"so the overlap quotient vanishes",
						"«dimOverlap» = 0",
						By(sameSpan, parts[2], vanishes.At(spanned)))
					b.Show(
						"the degree is minus d₀",
						ByArith(degree, difference, zeroOne, zeroOverlap, degreeProper, firstProper))
				})
			a.Otherwise(
				"a point of chart 1",
				func(b *Argument, secondProper Fact) {
					b.Cases(b.TermAs[Bool]("fst(P) = A₀"))
					b.When(
						"a point of chart 1 alone: chart 0 and the overlap lose nothing, and d₁ is the residue degree",
						func(c *Argument, firstWhole Fact) {
							zeroZero := c.Have(
								"chart 0 modulo itself vanishes",
								"«dimZero» = 0",
								By(firstWhole, parts[0], vanishes.At(A0)))
							zeroOverlap := c.Have(
								"the overlap quotient vanishes, fst(P) spanning what chart 0 spans",
								"«dimOverlap» = 0",
								By(firstWhole, parts[2], vanishes.At(spanned)))
							c.Show(
								"the degree is minus d₁",
								ByArith(degree, difference, zeroZero, zeroOverlap, degreeWhole, firstWhole))
						})
					b.Otherwise(
						"a point of both charts: snd(P) is contracted from "+
							"its span, so d₁ = d₀₁ and d₀ is the residue degree",
						func(c *Argument, firstProper Fact) {
							rings := c.Have(
								"L holds the overlap as a subring, above both charts",
								"subring(field_ring(L), A₀₁) ∧ A₀ ⊆ A₀₁ ∧ A₁ ⊆ A₀₁",
								By(overLine, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
							firstInOverlap := c.Have(
								"fst(P) lies in the overlap",
								"fst(P) ⊆ A₀₁",
								BySets(inside, rings))
							idealSpan := c.Simplified(GroupPremises(
								rings, firstInOverlap, fractional_ideal.SpanInSubringIsIdealSpan.Read(L).At(A01, first)))
							contraction := c.Have(
								"snd(P) is what chart 1 keeps of the ideal fst(P) generates",
								"snd(P) = A₁ ∩ ideal_span(«overlap», fst(P))",
								By(
									curve,
									point,
									firstProper,
									secondProper,
									smooth_curve.ClosedPointContraction.Read(L).At(k, A0, A1, A01, t, P)))
							contracted := c.Have(
								"so snd(P) is contracted from its span",
								"A₁ ∩ «span»(snd(P)) ⊆ snd(P)",
								BySets(pointSpan, idealSpan, contraction))
							keeps := c.Simplified(
								lattice_pair.ContractedQuotientDimLocalizes.At(
									overlap, A1, A0, inverse, t, k, inv, vectors, A1, second),
								Fwd(module_record.RestrictRingTwice),
								Fwd(module_record.RestrictModuleTwice))
							sameDimension := c.Have(
								"so the overlap quotient has the dimension of the chart 1 quotient",
								"«dimOverlap» = «dimOne»",
								By(
									keeps,
									lattice_pair.BiaffineSwap.Read(biaffine),
									overlapSubfield,
									kInCharts,
									moduleOverlap,
									structureData[2],
									pointData[1],
									inside,
									finiteQuotients,
									contracted,
									chartsSpan,
									pointSpan))
							c.Show(
								"the degree is minus d₀",
								ByArith(degree, difference, sameDimension, degreeProper, firstProper))
						})
				})
		}),
})}

// CurveDegreeOnInvertiblePairs — on a smooth curve the structure pair has degree
// zero and the degree adds over products of invertible pairs: the curve lies
// over its line, where both hold.
var CurveDegreeOnInvertiblePairs = curveDegreeOnInvertiblePairsThm{family.Add(registry.ProofEntry{
	Name: "CurveDegreeOnInvertiblePairs",
	Key:  "prop_4cb8a54f0c401d54",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "curve_degree(field_ring(L), k, A₀, A₁, A₀₁, (A₀, A₁)) = 0 ∧ " +
			"(∀X Y:prod(set(A), set(A)). " +
			"    X ∈ «scInvertibles» ∧ Y ∈ «scInvertibles» ⇒ " +
			"    curve_degree(field_ring(L), " +
			"        k, " +
			"        A₀, " +
			"        A₁, " +
			"        A₀₁, " +
			"        lattice_pair_mul(field_ring(L), A₀, A₁, X, Y)) = " +
			"    curve_degree(field_ring(L), k, A₀, A₁, A₀₁, X) + " +
			"    curve_degree(field_ring(L), k, A₀, A₁, A₀₁, Y))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			sums := a.Have(
				"the degree adds over products of invertible pairs",
				Statement{
					Binders: "∀X Y:prod(set(A), set(A)).",
					Hypotheses: []string{
						"X ∈ «scInvertibles»",
						"Y ∈ «scInvertibles»",
					},
					Conclusion: "curve_degree(field_ring(L), " +
						"    k, " +
						"    A₀, " +
						"    A₁, " +
						"    A₀₁, " +
						"    lattice_pair_mul(field_ring(L), A₀, A₁, X, Y)) = " +
						"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, X) + curve_degree(field_ring(L), k, A₀, A₁, A₀₁, Y)",
				},
				Derive(func(b *Argument) {
					X, Y := b.FixAs[_IdealPair]("X"), b.FixAs[_IdealPair]("Y")
					b.Show(
						"the curve datum holds, and X and Y are invertible",
						By(
							b.Assume(),
							curve,
							smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
							curve_degree.DegreeAdditive.Read(L).At(k, A0, A1, A01, t, X, Y)))
				}))
			a.Show(
				"the structure pair has degree zero, and the degree adds over products",
				By(curve_degree.DegreeStructure.Read(L).At(k, A0, A1, A01), sums))
		}),
})}

// ClosedPointPowerDegree — the integer power of a closed point at n has lattice
// degree n times the residue degree. The degree reads the powers additively, the
// power at −1 is the point, of degree minus its residue degree, and every
// integer is a natural number or the negative of one.
var ClosedPointPowerDegree = closedPointPowerDegreeThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointPowerDegree",
	Key:  "prop_e69d5337e8b1979a",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:int.",
		Hypotheses: []string{"«scCurve»", "«scPoint»(P)"},
		Conclusion: "curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, n)) = n * «scPointDegree»(P)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_IdealPair],
			n *Expr[Int],
			curve, point Fact,
		) {
			degree := a.Conjuncts(
				GroupPremises(curve, CurveDegreeOnInvertiblePairs.Read(L).At(k, A0, A1, A01, t)),
				"the structure pair has degree zero",
				"the degree adds over products")
			laws := a.Conjuncts(
				GroupPremises(point, a.Conjuncts(
					GroupPremises(curve, closed_divisor.ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
					"the invertible pairs are a commutative monoid",
					"inverses are unique",
					"the integer powers at a closed point",
					"a closed divisor's pair is the product of its powers")[2].At(P)),
				"the power at 0 is the structure pair",
				"the power at −1 is P",
				"every power is invertible",
				"the exponents add")
			one := a.TermAs[Int]("1")
			minusOne := a.TermAs[Int]("-1")
			zero := a.TermAs[Int]("0")
			adds := a.Have(
				"along exponents that add, the degrees add",
				Statement{
					Binders:    "∀i j l:int.",
					Hypotheses: []string{"i + j = l"},
					Conclusion: "curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, l)) = " +
						"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, i)) + " +
						"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, j))",
				},
				Derive(func(b *Argument) {
					i, j := b.FixAs[Int]("i"), b.FixAs[Int]("j")
					b.FixAs[Int]("l")
					sum := b.Assume()
					b.Show(
						"the power at i + j is the product of the two powers, both invertible",
						sum.RwRev(),
						By(
							laws[3].At(i, j),
							laws[2].At(i),
							laws[2].At(j),
							degree[1].At(b.TermAs[_IdealPair]("«scPower»(P, i)"), b.TermAs[_IdealPair]("«scPower»(P, j)"))))
				}))
			atZero := a.Have(
				"at 0 the degree is that of the structure pair",
				"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, int_of_num(0))) = int_of_num(0)",
				laws[0].Rw(),
				By(degree[0]))
			atMinusOne := a.Have(
				"at −1 it is that of P",
				"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, -int_of_num(1))) = -«scPointDegree»(P)",
				laws[1].Rw(),
				By(curve, point, ClosedPointLatticeDegree.Read(L).At(k, A0, A1, A01, t, P)))
			atOne := a.Have(
				"so at 1 it is the residue degree",
				"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, int_of_num(1))) = «scPointDegree»(P)",
				ByArith(adds.At(one, minusOne, zero), atZero, atMinusOne))
			natural := a.Have(
				"at a natural number d it is d times the residue degree",
				"∀d:num. "+
					"    curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, int_of_num(d))) = "+
					"    int_of_num(d) * «scPointDegree»(P)",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]("d")
					b.Induct(d)
					b.Base(
						"at 0 both sides vanish",
						ByArith(atZero))
					b.Step(
						"one more factor adds the residue degree once",
						func(c *Argument, ih Fact) {
							natural := c.TermAs[Int]("d")
							next := c.Have(
								"d + 1 is the successor of d",
								"d + &1 = int_of_num(suc(d))",
								ByArith(int_embed.OfNumSuc.At(d)))
							c.Show(
								"the degree at suc(d) is the degree at d and the degree at 1",
								ByArith(
									next,
									adds.At(natural, one, c.TermAs[Int]("suc(d)")),
									atOne,
									ih,
									int_real_lift.RightDistrib.At(natural, one, c.TermAs[Int]("«scPointDegree»(P)"))))
						})
				}))
			a.Cases(a.TermAs[Bool]("&0 ≤ n"))
			a.When(
				"a nonnegative n is natural",
				func(b *Argument, nonnegative Fact) {
					b.Show(
						"n is the natural number num_of_int(n)",
						By(nonnegative, int_embed.NumOfIntSection.At(n), natural.At(b.TermAs[Nat]("num_of_int(n)"))))
				})
			a.Otherwise(
				"a negative n is the negative of a natural number",
				func(b *Argument, negative Fact) {
					opposite := b.TermAs[Int]("-n")
					section := b.Have(
						"−n is a natural number",
						"&num_of_int(-n) = -n",
						ByArith(negative, int_embed.NumOfIntSection.At(opposite)))
					atOpposite := b.Have(
						"so the degree at −n is −n times the residue degree",
						"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, -n)) = -n * «scPointDegree»(P)",
						By(section, natural.At(b.TermAs[Nat]("num_of_int(-n)"))))
					balance := b.Have(
						"−n and n add to 0",
						"-n + n = int_of_num(0)",
						ByArith())
					b.Show(
						"the degrees at −n and n add to the degree at 0",
						ByArith(balance, adds.At(opposite, n, zero), atZero, atOpposite))
				})
		}),
})}

// ClosedDivisorLatticeDegree — the lattice degree of a closed divisor's pair is
// the divisor's degree: the pair is the product of the powers of its points,
// the degree a homomorphism on the invertible pairs, and each power has the
// degree of its term.
var ClosedDivisorLatticeDegree = closedDivisorLatticeDegreeThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorLatticeDegree",
	Key:  "prop_6a9ad870d43d823a",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{"«scCurve»", "«scDivisor»(D)"},
		Conclusion: "curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPair»(D)) = «scDegree»(D)",
		Abbrev: Abbrev{
			{Name: "support", Text: "fun_support(int_of_num(0), D)"},
			{Name: "intSum", Text: "module_sum(λa:int. λb:int. a + b, int_of_num(0), «support»)"},
			{Name: "powerTerm", Text: "λP:prod(set(A), set(A)). «scPower»(P, D(P))"},
			{Name: "degreeTerm", Text: "λP:prod(set(A), set(A)). " +
				"    curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, D(P)))"},
			{Name: "weightTerm", Text: "λP:prod(set(A), set(A)). D(P) * «scPointDegree»(P)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_IdealPair, Int],
			curve, divisor Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			products := a.Conjuncts(
				GroupPremises(curve, closed_divisor.ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")
			monoid, powers, pairOf := products[0], products[2], products[3]
			degree := a.Conjuncts(
				GroupPremises(curve, CurveDegreeOnInvertiblePairs.Read(L).At(k, A0, A1, A01, t)),
				"the structure pair has degree zero",
				"the degree adds over products")
			supported := a.Conjuncts(
				a.Unfolded(divisor, closed_divisor.ClosedDivisorDef),
				"the support is finite",
				"its pairs are closed points")
			points := a.Have(
				"the pairs of the support are closed points",
				"∀P:prod(set(A), set(A)). P ∈ «support» ⇒ «scPoint»(P)",
				a.ForEach(func(P *Expr[_IdealPair]) Action { return BySets(supported[1].At(P)) }))
			invertible := a.Have(
				"so their powers are invertible",
				"∀P:prod(set(A), set(A)). P ∈ «support» ⇒ «scPower»(P, D(P)) ∈ «scInvertibles»",
				Derive(func(b *Argument) {
					P := b.FixAs[_IdealPair]("P")
					inSupport := b.Assume()
					b.Show(
						"the integer powers of a closed point are invertible",
						By(inSupport, points.At(P), powers.At(P)))
				}))
			terms := a.Have(
				"each power has the degree of its term",
				Statement{
					Binders: "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{
						"P ∈ «support»",
					},
					Conclusion: "curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPower»(P, D(P))) = " +
						"D(P) * «scPointDegree»(P)",
				},
				Derive(func(b *Argument) {
					P := b.FixAs[_IdealPair]("P")
					inSupport := b.Assume()
					b.Show(
						"P is a closed point",
						By(
							inSupport,
							points.At(P),
							curve,
							ClosedPointPowerDegree.Read(L).At(k, A0, A1, A01, t, P, b.TermAs[Int]("D(P)"))))
				}))
			sum := a.TermAs[Op[Int]]("λa:int. λb:int. a + b")
			unit := a.TermAs[Int]("0")
			support := a.TermAs[Set[_IdealPair]]("«support»")
			degreeTerm := a.TermAs[Fun[_IdealPair, Int]]("«degreeTerm»")
			weightTerm := a.TermAs[Fun[_IdealPair, Int]]("«weightTerm»")
			a.Show(
				"the degree of the product is the sum of the degrees of its factors",
				CalcEq(
					Leg(
						a.TermAs[Int](
							"curve_degree(field_ring(L), "+
								"    k, "+
								"    A₀, "+
								"    A₁, "+
								"    A₀₁, "+
								"    module_sum(«scMul», (A₀, A₁), «support», «powerTerm»))"),
						"the pair of D is the product of its powers",
						By(divisor, pairOf.At(D))),
					Leg(
						a.TermAs[Int]("«intSum»(«degreeTerm»)"),
						"the degree is a homomorphism on the invertible pairs",
						By(
							monoid,
							degree[0],
							degree[1],
							supported[0],
							invertible,
							Read(module.ModuleSumMonoidHomomorphism, monoid).At(
								sum,
								unit,
								a.TermAs[Fun[_IdealPair, Int]]("curve_degree(field_ring(L), k, A₀, A₁, A₀₁)"),
								support,
								a.TermAs[Fun[_IdealPair, _IdealPair]]("«powerTerm»")))),
					Leg(
						a.TermAs[Int]("«intSum»(«weightTerm»)"),
						"term by term",
						By(terms, module.ModuleSumCongruence.At(sum, unit, support, degreeTerm, weightTerm))),
					FinalLeg(
						"and that is the degree of D",
						By(closed_divisor.ClosedDivisorDegreeDef.At(ring, k, A0, A1, D)))))
		}),
})}
