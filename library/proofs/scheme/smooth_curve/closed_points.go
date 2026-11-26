package smooth_curve

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ClosedPointSwap — a closed point read from the other chart: exchanging the
// charts and the two components of a point permutes the clauses of its
// definition, and the last clause survives since the two spans agree.
var ClosedPointSwap = closedPointSwapThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointSwap",
	Key:  "prop_5173551ca5bb78eb",
	Build: family.Theorem("∀R:ring_ops(A). ∀A₀ A₁ A₀₁:set(A). ∀P:prod(set(A), set(A)). "+
		"    curve_closed_point(R, A₀, A₁, A₀₁, P) ⇔ curve_closed_point(R, A₁, A₀, A₀₁, (snd(P), fst(P)))",
		func(a *Argument, R *Expr[RingOps[A]], A0, A1, A01 *Expr[Set[A]], P *Expr[Prod[Set[A], Set[A]]]) {
			a.Do(
				Simp(Fwd(CurveClosedPointDef)),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)))
			a.Iff()
			a.Forward(
				"the clauses of the point, permuted, are those of the swapped point",
				func(b *Argument, point Fact) {
					b.Show(
						"the two spans being equal, the last clause moves across them",
						By(Normalized, point))
				})
			a.Backward(
				"and the clauses of the swapped point are those of the point",
				func(b *Argument, swapped Fact) {
					b.Show(
						"the two spans being equal, the last clause moves back",
						By(Normalized, swapped))
				})
		}),
})}

// ClosedPointMaximal — a closed point is a maximal ideal of a chart: when the
// first component is not all of A₀ it is maximal there, and otherwise the
// second, which is then not all of A₁, is maximal in A₁.
var ClosedPointMaximal = closedPointMaximalThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointMaximal",
	Key:  "prop_e2a7c4bf051953a7",
	Build: family.Theorem(Statement{
		Binders:    "∀R:ring_ops(A). ∀A₀ A₁ A₀₁:set(A). ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"curve_closed_point(R, A₀, A₁, A₀₁, P)"},
		Conclusion: "maximal_ideal(restrict_ring(R, point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
	},
		func(
			a *Argument,
			R *Expr[RingOps[A]],
			A0, A1, A01 *Expr[Set[A]],
			P *Expr[Prod[Set[A], Set[A]]],
			point Fact,
		) {
			clauses := a.Unfolded(point, CurveClosedPointDef)
			a.Do(Simp(Fwd(biaffine_rational_point.PointChartDef), Fwd(biaffine_rational_point.PointIdealDef)))
			a.Cases(a.Term("fst(P) = A₀"))
			a.When(
				"the first component is all of A₀, so the second is proper",
				func(b *Argument, whole Fact) {
					b.Show(
						"and a proper component of a point is maximal in its chart",
						By(Normalized, whole, clauses))
				})
			a.Otherwise(
				"the first component is proper",
				func(b *Argument, proper Fact) {
					b.Show(
						"so it is maximal in A₀",
						By(Normalized, proper, clauses))
				})
		}),
})}

// ChartOverlap — the overlap of a smooth curve: it is a subring of L above the
// chart A₀ which holds the inverse of t and is A₀ with t inverted, inside
// itself and inside L; the powers of t lie in A₀ and invert the powers of its
// inverse in the overlap.
var ChartOverlap = chartOverlapThm{family.Add(registry.ProofEntry{
	Name: "ChartOverlap",
	Key:  "prop_b81333c4748a6304",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "subring(field_ring(L), A₀₁) ∧ " +
			"A₀ ⊆ A₀₁ ∧ " +
			"t ∈ A₀ ∧ " +
			"t ≠ L.zero ∧ " +
			"L.inv(t) ∈ A₀₁ ∧ " +
			"t * L.inv(t) = L.one ∧ " +
			"A₀₁ = ring_away(«overlap», A₀, t) ∧ " +
			"A₀₁ = ring_away(field_ring(L), A₀, t) ∧ " +
			"(∀j:num. «tPow»(j) ∈ A₀ ∧ «sPow»(j) ∈ A₀₁ ∧ «tPow»(j) * «sPow»(j) = L.one)",
		Abbrev: Abbrev{
			{Name: "tPow", Text: "λj:num. monoid_pow(L.mul, L.one, t, j)"},
			{Name: "sPow", Text: "λj:num. monoid_pow(L.mul, L.one, L.inv(t), j)"},
		},
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			inverse := a.TermAs[A]("L.inv(t)")
			line := a.Have(
				"the overlap is a subring above both charts, and A₀ with t inverted inside it",
				"subring(field_ring(L), A₀₁) ∧ "+
					"A₀ ⊆ A₀₁ ∧ "+
					"t ∈ A₀ ∧ "+
					"t ≠ L.zero ∧ "+
					"L.inv(t) ∈ A₁ ∧ "+
					"A₁ ⊆ A₀₁ ∧ "+
					"t * L.inv(t) = L.one ∧ "+
					"A₀₁ = ring_away(«overlap», A₀, t)",
				By(
					a.Unfolded(curve, SmoothFiniteFieldCurveDef),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			overlapRing := a.Have(
				"the overlap is a ring under L's operations",
				"comm_ring_on(«overlap»)",
				By(curve, OverlapCommRing.Read(L).At(k, A0, A1, A01, t)))
			chartRing := a.Have(
				"the chart is a ring under L's operations",
				"comm_ring_on(«chart»)",
				By(curve, ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			coordinateIn := a.Have(
				"t lies in the overlap",
				"t ∈ A₀₁",
				BySets(line))
			inverseIn := a.Have(
				"and so does its inverse",
				"L.inv(t) ∈ A₀₁",
				BySets(line))
			powers := a.Have(
				"the powers of t lie in A₀, those of its inverse in the overlap, and the two invert each other",
				"∀j:num. «tPow»(j) ∈ A₀ ∧ «sPow»(j) ∈ A₀₁ ∧ «tPow»(j) * «sPow»(j) = L.one",
				a.ForEach(func(j *Expr[Nat]) Action {
					return By(
						overlapRing,
						line,
						coordinateIn,
						inverseIn,
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(chartRing)).AsFact().At(t, j),
						comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(overlapRing)).AsFact().At(inverse, j),
						comm_monoid.PowInverseOn.Read(comm_ring.MulMonoidOn.Read(overlapRing)).AsFact().At(t, inverse, j))
				}))
			a.Show(
				"inverting t inside the overlap and inside L give one ring, the overlap holding t and its inverse",
				By(
					coordinateIn,
					inverseIn,
					line,
					powers,
					field.RingOn.Read(L),
					ring_away.RingAwayInSubring.At(ring, A01, A0, t, inverse)))
		}),
})}

// OverlapPowerUnit — a power of t is a unit of the overlap: it lies there with
// the same power of the inverse of t, and that power takes its multiple of an
// element of the overlap back to the element.
var OverlapPowerUnit = overlapPowerUnitThm{family.Add(registry.ProofEntry{
	Name: "OverlapPowerUnit",
	Key:  "prop_425a7264abdea2e",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀j:num. ∀z:A.",
		Hypotheses: []string{"«scCurve»", "z ∈ A₀₁"},
		Conclusion: "«tPow»(j) ∈ A₀₁ ∧ «sPow»(j) ∈ A₀₁ ∧ z = «sPow»(j) * («tPow»(j) * z)",
		Abbrev: Abbrev{
			{Name: "tPow", Text: "λj:num. monoid_pow(L.mul, L.one, t, j)"},
			{Name: "sPow", Text: "λj:num. monoid_pow(L.mul, L.one, L.inv(t), j)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			j *Expr[Nat],
			z *Expr[A],
			curve, inOverlap Fact,
		) {
			datum := a.Conjuncts(
				GroupPremises(curve, ChartOverlap.Read(L).At(k, A0, A1, A01, t)),
				"the overlap is a subring of L",
				"it contains the chart",
				"the chart holds t",
				"t is nonzero",
				"the overlap holds the inverse of t",
				"they multiply to one",
				"the overlap is the chart with t inverted, inside itself",
				"and inside L",
				"the powers of t and of its inverse")
			overlapRing := a.Have(
				"the overlap is a ring",
				"comm_ring_on(restrict_ring(field_ring(L), A₀₁))",
				By(curve, OverlapCommRing.Read(L).At(k, A0, A1, A01, t)))
			unit := a.Conjuncts(
				datum[8].At(j),
				"the power of t lies in the chart",
				"the power of the inverse lies in the overlap",
				"the two invert each other")
			powerIn := a.Have(
				"so the power of t lies in the overlap",
				"«tPow»(j) ∈ A₀₁",
				BySets(unit[0], datum[1]))
			restored := a.Have(
				"multiplying by the inverse power restores z",
				"z = «sPow»(j) * («tPow»(j) * z)",
				ByArith(overlapRing, Scaled(z, unit[2]), inOverlap, powerIn, unit[1]))
			a.Show(
				"so the power lies in the overlap, with the inverse power undoing it",
				By(powerIn, unit[1], restored))
		}),
})}

// ChartMaximalLocalizes — a maximal ideal m of a chart which avoids t extends
// to a prime of the overlap, and that prime contracts back to m. The extension
// lies in the saturation of m at t, so clearing denominators reads a product in
// it as a product in the prime m, and a denominator cancels in it since t is a
// unit of the overlap; the contraction is MaximalPowerLocalization at the first
// power of m.
var ChartMaximalLocalizes = chartMaximalLocalizesThm{family.Add(registry.ProofEntry{
	Name: "ChartMaximalLocalizes",
	Key:  "prop_e8202b315edf3e25",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"maximal_ideal(«chart», m)",
			"t ∉ m",
		},
		Conclusion: "prime_ideal(«overlap», ideal_span(«overlap», m)) ∧ A₀ ∩ ideal_span(«overlap», m) = m",
		Abbrev: Abbrev{
			{Name: "saturated", Text: "ring_away(field_ring(L), m, t)"},
			{Name: "tPow", Text: "λj:num. monoid_pow(L.mul, L.one, t, j)"},
			{Name: "sPow", Text: "λj:num. monoid_pow(L.mul, L.one, L.inv(t), j)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			m *Expr[Set[A]],
			curve, maximal, outside Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			chart := a.TermAs[RingOps[A]]("«chart»")
			overlap := a.TermAs[RingOps[A]]("«overlap»")
			subring := a.Have(
				"the chart is a subring of L",
				"subring(field_ring(L), A₀)",
				By(curve, ChartSubring.Read(L).At(k, A0, A1, A01, t)))
			datum := a.Conjuncts(
				GroupPremises(curve, ChartOverlap.Read(L).At(k, A0, A1, A01, t)),
				"the overlap is a subring of L",
				"it contains the chart",
				"the chart holds t",
				"t is nonzero",
				"the overlap holds the inverse of t",
				"they multiply to one",
				"the overlap is the chart with t inverted, inside itself",
				"and inside L",
				"the powers of t and of its inverse")
			above, tIn, away, powers := datum[1], datum[2], datum[7], datum[8]
			chartRing := a.Have(
				"the chart is a ring",
				"comm_ring_on(«chart»)",
				By(curve, ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			overlapRing := a.Have(
				"the overlap is a ring",
				"comm_ring_on(«overlap»)",
				By(curve, OverlapCommRing.Read(L).At(k, A0, A1, A01, t)))
			ideal := a.Have(
				"m is an ideal of the chart",
				"ring_ideal(«chart», m)",
				By(maximal, ring_ideal.MaximalIdealIdeal.At(chart, m)))
			prime := a.Have(
				"m is prime",
				"prime_ideal(«chart», m)",
				By(maximal, ring_ideal.MaximalIsPrime.Read(chartRing).At(m)))
			inOverlap := a.Have(
				"m lies in the overlap",
				"m ⊆ A₀₁",
				BySets(ideal, above, ring_ideal.IdealSubset.At(chart, m)))
			firstPower := a.Have(
				"m is its own first power among the ideals of the chart",
				"ideal_pow(«chart», m, 1) = m",
				By(
					Normalized,
					ideal,
					ring_ideal.IdealPowDef.At(chart, m, a.TermAs[Nat]("1")),
					comm_monoid.PowOneOn.Read(ring_ideal.IdealsCommMonoid.Read(chartRing)).AsFact().At(m)))
			contraction := a.Have(
				"extending m to the chart with t inverted and contracting gives m back",
				"A₀ ∩ ideal_span(«overlap», m) = m",
				By(
					Normalized,
					away,
					firstPower,
					maximal,
					outside,
					tIn,
					subring,
					ideal_factorization.MaximalPowerLocalization.Read(L).At(A0, m, t, a.TermAs[Nat]("1"))))
			J, spanDef := a.LetAs[Set[A]]("J", "ideal_span(«overlap», m)")
			spanFacts := a.Have(
				"J is an ideal of the overlap containing m",
				"ring_ideal(«overlap», J) ∧ m ⊆ J",
				By(
					Normalized,
					overlapRing,
					spanDef,
					inOverlap,
					ring_ideal.SpanIdeal.Read(overlapRing).At(m),
					ring_ideal.SpanContains.At(overlap, m)))
			parts := a.Conjuncts(
				spanFacts,
				"J is an ideal",
				"J contains m")
			idealJ, containing := parts[0], parts[1]
			saturation := a.Have(
				"the saturation of m is an ideal of the overlap above m",
				"ring_ideal(«overlap», «saturated») ∧ m ⊆ «saturated»",
				By(Normalized, away, ideal, tIn, subring, ring_away.RingAwayIdeal.Read(L).At(A0, m, t)))
			inside := a.Have(
				"so J lies in the saturation of m",
				"J ⊆ «saturated»",
				By(
					Normalized,
					spanDef,
					saturation,
					ring_ideal.SpanLeast.At(overlap, m, a.TermAs[Set[A]]("«saturated»"))))
			cancelled := a.Have(
				"a denominator of t cancels in J, since t is a unit of the overlap",
				"∀z:A. ∀j:num. z ∈ A₀₁ ∧ «tPow»(j) * z ∈ J ⇒ z ∈ J",
				Derive(func(b *Argument) {
					z := b.FixAs[A]("z")
					j := b.FixAs[Nat]("j")
					given := b.Conjuncts(
						b.Assume(),
						"z lies in the overlap",
						"the cleared element lies in J")
					unit := b.Conjuncts(
						GroupPremises(curve, given[0], OverlapPowerUnit.Read(L).At(k, A0, A1, A01, t, j, z)),
						"the power of t lies in the overlap",
						"so does the power of the inverse",
						"which restores z")
					back := b.TermAs[A]("«sPow»(j)")
					b.Show(
						"and J absorbs the inverse power",
						By(
							Normalized,
							unit[2],
							given[1],
							unit[1],
							idealJ,
							ring_ideal.IdealMul.At(overlap, J, back, b.TermAs[A]("«tPow»(j) * z"))))
				}))
			proper := a.Have(
				"J misses one, since it contracts to the proper ideal m",
				"L.one ∉ J",
				BySets(
					contraction,
					maximal,
					ring_ideal.MaximalIdealProper.At(chart, m),
					comm_ring.OneIn.Read(chartRing)))
			avoided := a.Have(
				"the powers of t stay outside the prime m",
				"∀j:num. «tPow»(j) ∉ m",
				a.ForEach(func(j *Expr[Nat]) Action {
					return By(
						outside,
						tIn,
						prime,
						ring_ideal.PrimeIdealPow.Read(chartRing).At(m, a.MemberOf[on.Any](t, tIn), j))
				}))
			primality := a.Have(
				"J is prime: clearing denominators reads a product in J as a product in m",
				"∀x y:A. x ∈ A₀₁ ∧ y ∈ A₀₁ ∧ x * y ∈ J ⇒ x ∈ J ∨ y ∈ J",
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					y := b.FixAs[A]("y")
					given := b.Conjuncts(
						b.Assume(),
						"x lies in the overlap",
						"y lies in the overlap",
						"their product lies in J")
					i, j, l, clearedFacts := b.Obtain3As[Nat, Nat, Nat](
						"denominators of t clear x and y into the chart and their product into m",
						"∃i j l:num. «tPow»(i) * x ∈ A₀ ∧ «tPow»(j) * y ∈ A₀ ∧ «tPow»(l) * (x * y) ∈ m",
						BySets(
							given[0],
							given[1],
							given[2],
							inside,
							away,
							ring_away.RingAwayDef.At(ring, A0, t),
							ring_away.RingAwayDef.At(ring, m, t)))
					cleared := b.Conjuncts(
						clearedFacts,
						"x cleared lies in the chart",
						"y cleared lies in the chart",
						"the product cleared lies in m")
					first := b.Conjuncts(
						powers.At(i),
						"the first power lies in the chart",
						"its inverse",
						"their product")
					second := b.Conjuncts(
						powers.At(j),
						"the second power lies in the chart",
						"its inverse",
						"their product")
					third := b.Conjuncts(
						powers.At(l),
						"the third power lies in the chart",
						"its inverse",
						"their product")
					members := b.Have(
						"the three powers lie in the overlap",
						"«tPow»(i) ∈ A₀₁ ∧ «tPow»(j) ∈ A₀₁ ∧ «tPow»(l) ∈ A₀₁",
						BySets(first[0], second[0], third[0], above))
					regrouped := b.Have(
						"the third power times the cleared factors is a chart multiple of the cleared product",
						"«tPow»(l) * ((«tPow»(i) * x) * («tPow»(j) * y)) = («tPow»(i) * «tPow»(j)) * («tPow»(l) * (x * y))",
						ByArith(overlapRing, members, given[0], given[1]))
					multiple := b.Have(
						"the product of the two powers lies in the chart, and so does that of the cleared factors",
						"«tPow»(i) * «tPow»(j) ∈ A₀ ∧ («tPow»(i) * x) * («tPow»(j) * y) ∈ A₀",
						By(cleared[0], cleared[1], first[0], second[0], comm_ring.MulIn.Read(chartRing)))
					product := b.Have(
						"so the product of the cleared factors lies in the prime m, which the third power avoids",
						"(«tPow»(i) * x) * («tPow»(j) * y) ∈ m",
						By(
							regrouped,
							cleared[2],
							prime,
							ideal,
							multiple,
							third[0],
							avoided.At(l),
							ring_ideal.IdealMul.At(
								chart,
								m,
								b.TermAs[A]("«tPow»(i) * «tPow»(j)"),
								b.TermAs[A]("«tPow»(l) * (x * y)")),
							ring_ideal.PrimeIdealPrime.At(
								chart,
								m,
								b.TermAs[A]("«tPow»(l)"),
								b.TermAs[A]("(«tPow»(i) * x) * («tPow»(j) * y)"))))
					factor := b.Have(
						"so one cleared factor lies in m, hence in J",
						"«tPow»(i) * x ∈ J ∨ «tPow»(j) * y ∈ J",
						BySets(
							product,
							cleared[0],
							cleared[1],
							prime,
							containing,
							ring_ideal.PrimeIdealPrime.At(
								chart,
								m,
								b.TermAs[A]("«tPow»(i) * x"),
								b.TermAs[A]("«tPow»(j) * y"))))
					b.Show(
						"and the denominator cancels in J",
						By(factor, given[0], given[1], cancelled.At(x, i), cancelled.At(y, j)))
				}))
			a.Show(
				"J is a proper ideal with the prime property, and it contracts to m",
				By(proper, primality, contraction, idealJ, ring_ideal.PrimeIdealDef.At(overlap, J)))
		}),
})}

// ClosedPointChart — a closed point seen from a chart where it is proper. When
// its other component is whole, t lies in it, as otherwise its span would be a
// prime of the overlap holding one. When the other component is proper, t lies
// outside it, as otherwise its span would be the whole overlap, and it is the
// contraction of the other component's span.
var ClosedPointChart = closedPointChartThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointChart",
	Key:  "prop_d662b01e7726354",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(P)",
			"fst(P) ≠ A₀",
		},
		Conclusion: "(snd(P) = A₁ ⇒ t ∈ fst(P)) ∧ " +
			"(snd(P) ≠ A₁ ⇒ t ∉ fst(P) ∧ fst(P) = A₀ ∩ ideal_span(«overlap», snd(P)))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve, point, nonWhole Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			chart := a.TermAs[RingOps[A]]("«chart»")
			overlap := a.TermAs[RingOps[A]]("«overlap»")
			first := a.TermAs[Set[A]]("fst(P)")
			inverse := a.TermAs[A]("L.inv(t)")
			clauses := a.Conjuncts(
				a.Unfolded(point, CurveClosedPointDef),
				"the first component is whole or maximal",
				"the second component is whole or maximal",
				"the two are not both whole",
				"the two spans agree",
				"a point in both charts has a proper span")
			spans, properSpan := clauses[3], clauses[4]
			maximal := a.Have(
				"the first component, not being whole, is maximal in A₀",
				"maximal_ideal(«chart», fst(P))",
				By(Normalized, nonWhole, clauses[0]))
			otherCurve := a.Have(
				"the curve read from its other chart",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			oneIn := a.Have(
				"the other chart is a subring of L, so it holds one",
				"L.one ∈ A₁",
				By(otherCurve, ChartSubring.Read(L).At(k, A1, A0, A01, inverse), comm_ring.SubringOne.At(ring, A1)))
			overlapRing := a.Have(
				"the overlap is a ring",
				"comm_ring_on(«overlap»)",
				By(curve, OverlapCommRing.Read(L).At(k, A0, A1, A01, t)))
			whole := a.Have(
				"when the second component is whole, t lies in the first",
				"snd(P) = A₁ ⇒ t ∈ fst(P)",
				Derive(func(b *Argument) {
					second := b.Assume()
					notIn := b.SupposeNot()
					prime := b.Have(
						"otherwise the span of the first component is prime",
						"prime_ideal(«overlap», ideal_span(«overlap», fst(P)))",
						By(curve, maximal, notIn, ChartMaximalLocalizes.Read(L).At(k, A0, A1, A01, t, first)))
					b.Show(
						"but it is the span of A₁, which holds one",
						By(
							second,
							oneIn,
							spans,
							prime,
							ring_ideal.SpanContains.At(overlap, A1),
							ring_ideal.PrimeIdealProper.At(
								overlap,
								b.TermAs[Set[A]]("ideal_span(«overlap», fst(P))")),
							set_basic.SubsetDef))
				}))
			proper := a.Have(
				"when the second component is proper, t lies outside the first, which it contracts to",
				"snd(P) ≠ A₁ ⇒ t ∉ fst(P) ∧ fst(P) = A₀ ∩ ideal_span(«overlap», snd(P))",
				Derive(func(b *Argument) {
					second := b.Assume()
					outside := b.Have(
						"t lies outside the first component, whose span would otherwise be the whole overlap, holding one",
						"t ∉ fst(P)",
						By(
							Normalized,
							nonWhole,
							second,
							properSpan,
							maximal,
							ring_ideal.MaximalIdealIdeal.At(chart, first),
							ring_ideal.IdealSubset.At(chart, first),
							curve,
							SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
							algebraic_curve.CoordinateSpansOverlap.Read(L).At(k, A0, A1, A01, t, first),
							comm_ring.OneIn.Read(overlapRing)))
					b.Show(
						"so the first component contracts from its span, which is the span of the second",
						By(
							Normalized,
							outside,
							spans,
							curve,
							maximal,
							ChartMaximalLocalizes.Read(L).At(k, A0, A1, A01, t, first)))
				}))
			a.Show(
				"a whole second component puts t in the first, and a proper one puts t outside it",
				By(whole, proper))
		}),
})}

// ClosedPointContraction — how the two components of a closed point meet t and
// each other: a point in both charts avoids the coordinate on either side, its
// components contracting from each other's span, and a point in one chart
// alone holds that chart's coordinate. It is ClosedPointChart at the point and
// at the swapped point.
var ClosedPointContraction = closedPointContractionThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointContraction",
	Key:  "prop_dbead4b6be87fb5b",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"«scCurve»", "«scPoint»(P)"},
		Conclusion: "(fst(P) ≠ A₀ ∧ snd(P) ≠ A₁ ⇒ " +
			"    t ∉ fst(P) ∧ " +
			"    L.inv(t) ∉ snd(P) ∧ " +
			"    snd(P) = A₁ ∩ ideal_span(«overlap», fst(P)) ∧ " +
			"    fst(P) = A₀ ∩ ideal_span(«overlap», snd(P))) ∧ " +
			"(snd(P) = A₁ ⇒ t ∈ fst(P)) ∧ " +
			"(fst(P) = A₀ ⇒ L.inv(t) ∈ snd(P))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve, point Fact,
		) {
			inverse := a.TermAs[A]("L.inv(t)")
			swapped := a.TermAs[Prod[Set[A], Set[A]]]("(snd(P), fst(P))")
			otherCurve := a.Have(
				"the curve read from its other chart",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			otherPoint := a.Have(
				"the point read from its other chart",
				"curve_closed_point(field_ring(L), A₁, A₀, A₀₁, (snd(P), fst(P)))",
				By(point, ClosedPointSwap))
			direct := a.Have(
				"the point seen from A₀",
				Statement{
					Hypotheses: []string{
						"fst(P) ≠ A₀",
					},
					Conclusion: "(snd(P) = A₁ ⇒ t ∈ fst(P)) ∧ " +
						"(snd(P) ≠ A₁ ⇒ t ∉ fst(P) ∧ fst(P) = A₀ ∩ ideal_span(«overlap», snd(P)))",
				},
				By(Normalized, curve, point, ClosedPointChart.Read(L).At(k, A0, A1, A01, t, P)))
			other := a.Have(
				"the point seen from A₁",
				Statement{
					Hypotheses: []string{
						"snd(P) ≠ A₁",
					},
					Conclusion: "(fst(P) = A₀ ⇒ L.inv(t) ∈ snd(P)) ∧ " +
						"(fst(P) ≠ A₀ ⇒ L.inv(t) ∉ snd(P) ∧ snd(P) = A₁ ∩ ideal_span(«overlap», fst(P)))",
				},
				By(
					otherCurve,
					otherPoint,
					ClosedPointChart.Read(L).At(k, A1, A0, A01, inverse, swapped),
					pairs.Fst,
					pairs.Snd))
			notBoth := a.Have(
				"the two components are not both whole",
				"¬(fst(P) = A₀ ∧ snd(P) = A₁)",
				By(a.Unfolded(point, CurveClosedPointDef)))
			a.Show(
				"each case is one of the two readings",
				By(Normalized, notBoth, direct, other))
		}),
})}

// ClosedPointSecondComponent — a closed point proper in chart 0 has for its
// second component the meet of A₁ with the span of its first. All of A₁ lies
// in its own span, which is the first component's; a proper second component
// is that meet by ClosedPointContraction.
var ClosedPointSecondComponent = closedPointSecondComponentThm{family.Add(registry.ProofEntry{
	Name: "ClosedPointSecondComponent",
	Key:  "prop_e687e9d561520885",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«scCurve»",
			"«scPoint»(P)",
			"fst(P) ≠ A₀",
		},
		Conclusion: "snd(P) = A₁ ∩ ideal_span(«overlap», fst(P))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve, point, nonWhole Fact,
		) {
			overlap := a.TermAs[RingOps[A]]("«overlap»")
			a.Cases(a.Term("snd(P) = A₁"))
			a.When(
				"the second component is all of A₁",
				func(b *Argument, whole Fact) {
					b.Show(
						"A₁ lies in its own span, which is the span of the first component",
						BySets(whole, b.Unfolded(point, CurveClosedPointDef), ring_ideal.SpanContains.At(overlap, A1)))
				})
			a.Otherwise(
				"the second component is proper too",
				func(b *Argument, proper Fact) {
					b.Show(
						"so the point lies in both charts, where each component "+
							"is the meet of its chart with the other's span",
						By(proper, nonWhole, curve, point, ClosedPointContraction.Read(L).At(k, A0, A1, A01, t, P)))
				})
		}),
})}

// OverlapPrimeMaximal — a nonzero prime of the overlap contracts to a maximal
// ideal of a chart: its contraction is prime, a nonzero element cleared of its
// denominator lies in it, so it has finite colength, and a prime of finite
// index is maximal.
var OverlapPrimeMaximal = overlapPrimeMaximalThm{family.Add(registry.ProofEntry{
	Name: "OverlapPrimeMaximal",
	Key:  "prop_1fa589688043ebf4",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀J:set(A).",
		Hypotheses: []string{
			"«scCurve»",
			"prime_ideal(«overlap», J)",
			"J ≠ {L.zero}",
		},
		Conclusion: "maximal_ideal(«chart», A₀ ∩ J)",
		Abbrev: Abbrev{
			{Name: "tPow", Text: "λj:num. monoid_pow(L.mul, L.one, t, j)"},
			{Name: "sPow", Text: "λj:num. monoid_pow(L.mul, L.one, L.inv(t), j)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			J *Expr[Set[A]],
			curve, prime, nonzero Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			chart := a.TermAs[RingOps[A]]("«chart»")
			overlap := a.TermAs[RingOps[A]]("«overlap»")
			contraction := a.TermAs[Set[A]]("A₀ ∩ J")
			subring := a.Have(
				"the chart is a subring of L",
				"subring(field_ring(L), A₀)",
				By(curve, ChartSubring.Read(L).At(k, A0, A1, A01, t)))
			datum := a.Conjuncts(
				GroupPremises(curve, ChartOverlap.Read(L).At(k, A0, A1, A01, t)),
				"the overlap is a subring of L",
				"it contains the chart",
				"the chart holds t",
				"t is nonzero",
				"the overlap holds the inverse of t",
				"they multiply to one",
				"the overlap is the chart with t inverted, inside itself",
				"and inside L",
				"the powers of t and of its inverse")
			above, away := datum[1], datum[7]
			chartRing := a.Have(
				"the chart is a ring",
				"comm_ring_on(«chart»)",
				By(curve, ChartCommRing.Read(L).At(k, A0, A1, A01, t)))
			overlapRing := a.Have(
				"the overlap is a ring",
				"comm_ring_on(«overlap»)",
				By(curve, OverlapCommRing.Read(L).At(k, A0, A1, A01, t)))
			idealJ := a.Have(
				"J is an ideal of the overlap, missing one",
				"ring_ideal(«overlap», J) ∧ L.one ∉ J",
				By(prime, ring_ideal.PrimeIdealIdeal.At(overlap, J), ring_ideal.PrimeIdealProper.At(overlap, J)))
			parts := a.Conjuncts(
				idealJ,
				"J is an ideal",
				"J misses one")
			contracted := a.Have(
				"its contraction to the chart is prime",
				"prime_ideal(«chart», A₀ ∩ J)",
				Simp(Fwd(ring_ideal.PrimeIdealDef), Fwd(ring_ideal.RingIdealDef)),
				BySets(
					parts[1],
					prime,
					parts[0],
					subring,
					above,
					comm_ring.SubringZero.At(ring, A0),
					ring_ideal.IdealZero.At(overlap, J),
					At(comm_ring.SubringAdd, ring, A0),
					At(comm_ring.SubringMul, ring, A0),
					At(ring_ideal.IdealAdd, overlap, J),
					At(ring_ideal.IdealMul, overlap, J),
					At(ring_ideal.PrimeIdealPrime, overlap, J)))
			w, witness := a.ObtainAs[A](
				"a nonzero ideal holds a nonzero element",
				"∃w:A. w ∈ J ∧ w ≠ L.zero",
				BySets(nonzero, parts[0], ring_ideal.IdealZero.At(overlap, J)))
			chosen := a.Conjuncts(
				witness,
				"w lies in J",
				"w is nonzero")
			inJ, notZero := chosen[0], chosen[1]
			inOverlap := a.Have(
				"so w lies in the overlap",
				"w ∈ A₀₁",
				By(inJ, parts[0], ring_ideal.IdealSubset.At(overlap, J), set_basic.SubsetDef))
			j, clearedIn := a.ObtainAs[Nat](
				"a power of t clears w into the chart",
				"∃j:num. «tPow»(j) * w ∈ A₀",
				BySets(inOverlap, away, ring_away.RingAwayDef.At(ring, A0, t)))
			unit := a.Conjuncts(
				GroupPremises(curve, inOverlap, OverlapPowerUnit.Read(L).At(k, A0, A1, A01, t, j, w)),
				"the power of t lies in the overlap",
				"so does the power of the inverse",
				"which restores w")
			powerIn, restored := unit[0], unit[2]
			power := a.TermAs[A]("«tPow»(j)")
			clearedJ := a.Have(
				"the cleared element lies in J",
				"«tPow»(j) * w ∈ J",
				By(parts[0], powerIn, inJ, ring_ideal.IdealMul.At(overlap, J, power, w)))
			clearedNonzero := a.Have(
				"and it is nonzero, since it restores w",
				"«tPow»(j) * w ≠ L.zero",
				Derive(func(b *Argument) {
					vanishing := b.SupposeNot()
					zero := b.Have(
						"suppose the cleared element vanishes",
						"«tPow»(j) * w = L.zero",
						By(vanishing))
					back := b.TermAs[A]("«sPow»(j)")
					b.Show(
						"then w would vanish",
						ByArith(overlapRing, notZero, restored, Scaled(back, zero), inOverlap, powerIn, unit[1]))
				}))
			nonzeroContraction := a.Have(
				"so the contraction is nonzero",
				"A₀ ∩ J ≠ {L.zero}",
				BySets(clearedIn, clearedJ, clearedNonzero))
			idealContraction := a.Have(
				"the contraction is an ideal of the chart",
				"ring_ideal(«chart», A₀ ∩ J)",
				By(contracted, ring_ideal.PrimeIdealIdeal.At(chart, contraction)))
			a.Show(
				"a nonzero ideal of a chart has finite index, and a prime of finite index is maximal",
				By(
					curve,
					nonzeroContraction,
					idealContraction,
					contracted,
					ChartIdealFiniteQuotient.Read(L).At(k, A0, A1, A01, t, contraction),
					quotient_ring.FiniteIndexPrimeMaximal.Read(chartRing).At(contraction)))
		}),
})}

// ChartMaximalClosedPoint — every maximal ideal m of a chart is the first
// component of exactly one closed point. If t lies in m the point is (m, A₁),
// both spans being the unit ideal. If not, m extends to a nonzero prime of the
// overlap, which contracts to a maximal ideal of A₁ with the same span, and
// that is the second component. ClosedPointContraction leaves no other choice.
var ChartMaximalClosedPoint = chartMaximalClosedPointThm{family.Add(registry.ProofEntry{
	Name: "ChartMaximalClosedPoint",
	Key:  "prop_d73b26fc11d8eb46",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀m:set(A).",
		Hypotheses: []string{"«scCurve»", "maximal_ideal(«chart», m)"},
		Conclusion: "∃!P:prod(set(A), set(A)). «scPoint»(P) ∧ fst(P) = m",
		Abbrev: Abbrev{
			{Name: "otherChart", Text: "restrict_ring(field_ring(L), A₁)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			m *Expr[Set[A]],
			curve, maximal Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			chart := a.TermAs[RingOps[A]]("«chart»")
			overlap := a.TermAs[RingOps[A]]("«overlap»")
			inverse := a.TermAs[A]("L.inv(t)")
			otherCurve := a.Have(
				"the curve read from its other chart",
				"smooth_finite_curve(L, k, L.inv(t), A₁, A₀, A₀₁)",
				By(curve, SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t)))
			subring := a.Have(
				"the chart is a subring of L",
				"subring(field_ring(L), A₀)",
				By(curve, ChartSubring.Read(L).At(k, A0, A1, A01, t)))
			otherSubring := a.Have(
				"so is the other chart",
				"subring(field_ring(L), A₁)",
				By(otherCurve, ChartSubring.Read(L).At(k, A1, A0, A01, inverse)))
			otherDatum := a.Conjuncts(
				a.Have(
					"the overlap read from the other chart",
					"A₁ ⊆ A₀₁ ∧ "+
						"L.inv(t) ∈ A₁ ∧ "+
						"L.inv(L.inv(t)) ∈ A₀₁ ∧ "+
						"L.inv(t) * L.inv(L.inv(t)) = L.one ∧ "+
						"A₀₁ = ring_away(«overlap», A₁, L.inv(t))",
					By(otherCurve, ChartOverlap.Read(L).At(k, A1, A0, A01, inverse))),
				"the overlap contains the other chart",
				"the other chart holds the inverse of t",
				"the overlap holds the inverse of the inverse",
				"those two multiply to one",
				"the overlap is the other chart with the inverse inverted")
			otherAbove := otherDatum[0]
			overlapRing := a.Have(
				"the overlap is a ring",
				"comm_ring_on(«overlap»)",
				By(curve, OverlapCommRing.Read(L).At(k, A0, A1, A01, t)))
			ideal := a.Have(
				"m is an ideal of the chart",
				"ring_ideal(«chart», m)",
				By(maximal, ring_ideal.MaximalIdealIdeal.At(chart, m)))
			notOne := a.Have(
				"m is proper",
				"L.one ∉ m",
				By(maximal, ring_ideal.MaximalIdealProper.At(chart, m)))
			inChart := a.Have(
				"m lies in the chart, as one does",
				"m ⊆ A₀ ∧ L.one ∈ A₀",
				By(ideal, subring, ring_ideal.IdealSubset.At(chart, m), comm_ring.SubringOne.At(ring, A0)))
			notWhole := a.Have(
				"so m is not the chart",
				"m ≠ A₀",
				BySets(notOne, inChart))
			inOverlap := a.Have(
				"m lies in the overlap, which contains the chart",
				"m ⊆ A₀₁",
				By(
					inChart,
					curve,
					ChartOverlap.Read(L).At(k, A0, A1, A01, t),
					set_order.SubsetTrans.At(m, A0, A01)))
			oneIn := a.Have(
				"the other chart holds one",
				"L.one ∈ A₁",
				By(otherSubring, comm_ring.SubringOne.At(ring, A1)))
			J, spanDef := a.LetAs[Set[A]]("J", "ideal_span(«overlap», m)")
			spans := a.Have(
				"J and the span of A₁ are ideals of the overlap, the first containing m and the second one",
				"ring_ideal(«overlap», J) ∧ "+
					"m ⊆ J ∧ "+
					"ring_ideal(«overlap», ideal_span(«overlap», A₁)) ∧ "+
					"L.one ∈ ideal_span(«overlap», A₁)",
				By(
					Normalized,
					overlapRing,
					spanDef,
					oneIn,
					otherAbove,
					inOverlap,
					ring_ideal.SpanIdeal.Read(overlapRing).At(m),
					ring_ideal.SpanContains.At(overlap, m),
					ring_ideal.SpanIdeal.Read(overlapRing).At(A1),
					ring_ideal.SpanContains.At(overlap, A1),
					set_basic.SubsetDef))
			spanParts := a.Conjuncts(
				spans,
				"J is an ideal",
				"J contains m",
				"the span of A₁ is an ideal",
				"the span of A₁ holds one")
			idealJ, containing := spanParts[0], spanParts[1]
			build := a.Have(
				"a whole or maximal n with the span of m, proper unless n is whole, makes a closed point (m, n)",
				Statement{
					Binders: "∀n:set(A).",
					Hypotheses: []string{
						"n = A₁ ∨ maximal_ideal(«otherChart», n)",
						"J = ideal_span(«overlap», n)",
						"n ≠ A₁ ⇒ L.one ∉ J",
					},
					Conclusion: "«scPoint»((m, n))",
				},
				Derive(func(b *Argument) {
					b.FixAs[Set[A]]("n")
					given := b.Assume()
					b.Do(
						Simp(Fwd(CurveClosedPointDef)),
						Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)))
					b.Show(
						"each clause of the definition is one of these facts",
						By(Normalized, maximal, notWhole, spanDef, given))
				}))
			assemble := a.Have(
				"a closed point (m, n) with n forced is the only point over m",
				Statement{
					Binders: "∀n:set(A).",
					Hypotheses: []string{
						"«scPoint»((m, n))",
						"∀Q:prod(set(A), set(A)). «scPoint»(Q) ∧ fst(Q) = m ⇒ snd(Q) = n",
					},
					Conclusion: "∃!P:prod(set(A), set(A)). «scPoint»(P) ∧ fst(P) = m",
				},
				Derive(func(b *Argument) {
					n := b.FixAs[Set[A]]("n")
					given := b.Conjuncts(
						b.Assume(),
						"(m, n) is a closed point",
						"a point over m has second component n")
					b.Take(b.TermAs[Prod[Set[A], Set[A]]]("(m, n)"))
					b.Do(SplitConj(
						Case(
							"the pair is a point over m",
							By(given[0], pairs.Fst.At(m, n))),
						Case(
							"a point over m is the pair, its components being m and n",
							b.ForEach(func(y *Expr[Prod[Set[A], Set[A]]]) Action {
								return By(Normalized, given[1].At(y), pairs.PairEta.At(y))
							}))))
				}))
			forced := a.Have(
				"ClosedPointContraction forces the second component of a point over m",
				Statement{
					Binders: "∀Q:prod(set(A), set(A)).",
					Hypotheses: []string{
						"«scPoint»(Q)",
						"fst(Q) = m",
					},
					Conclusion: "(snd(Q) ≠ A₁ ⇒ t ∉ m ∧ snd(Q) = A₁ ∩ J) ∧ (snd(Q) = A₁ ⇒ t ∈ m)",
				},
				Derive(func(b *Argument) {
					Q := b.FixAs[Prod[Set[A], Set[A]]]("Q")
					given := b.Conjuncts(
						b.Assume(),
						"Q is a closed point",
						"its first component is m")
					b.Show(
						"its first component is the proper ideal m",
						By(
							Normalized,
							given[1],
							notWhole,
							spanDef,
							curve,
							given[0],
							ClosedPointContraction.Read(L).At(k, A0, A1, A01, t, Q)))
				}))
			a.Cases(a.Term("t ∈ m"))
			a.When(
				"t lies in m, so the second component is all of A₁",
				func(b *Argument, inM Fact) {
					equal := b.Have(
						"a part of the chart holding t spans the whole overlap, as A₁ does, so J is the span of A₁",
						"J = ideal_span(«overlap», A₁)",
						By(
							spanDef,
							inChart,
							inM,
							curve,
							spanParts[2],
							spanParts[3],
							SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
							algebraic_curve.CoordinateSpansOverlap.Read(L).At(k, A0, A1, A01, t, m),
							ring_ideal.IdealOneIff.Read(overlapRing).At(b.TermAs[Set[A]]("ideal_span(«overlap», A₁)"))))
					point := b.Have(
						"so (m, A₁) is a closed point",
						"«scPoint»((m, A₁))",
						By(build.At(A1), equal))
					only := b.Have(
						"and a point over m has second component A₁",
						"∀Q:prod(set(A), set(A)). «scPoint»(Q) ∧ fst(Q) = m ⇒ snd(Q) = A₁",
						Derive(func(c *Argument) {
							Q := c.FixAs[Prod[Set[A], Set[A]]]("Q")
							over := c.Assume()
							c.Show(
								"the other case would put t outside m",
								By(Normalized, over, forced.At(Q), inM))
						}))
					b.Show(
						"so it is the unique point",
						By(assemble.At(A1), only, point))
				})
			a.Otherwise(
				"t lies outside m, so the second component is the contraction of J to A₁",
				func(b *Argument, outside Fact) {
					contraction := b.TermAs[Set[A]]("A₁ ∩ J")
					localized := b.Have(
						"J is prime",
						"prime_ideal(«overlap», J)",
						By(
							Normalized,
							spanDef,
							outside,
							curve,
							maximal,
							ChartMaximalLocalizes.Read(L).At(k, A0, A1, A01, t, m)))
					nonzero := b.Have(
						"J is nonzero, since it contains the nonzero ideal m",
						"J ≠ {L.zero}",
						BySets(
							containing,
							ideal,
							maximal,
							curve,
							ring_ideal.IdealZero.At(chart, m),
							ChartMaximalNonzero.Read(L).At(k, A0, A1, A01, t, m)))
					otherMaximal := b.Have(
						"so its contraction to the other chart is maximal",
						"maximal_ideal(«otherChart», A₁ ∩ J)",
						By(nonzero, localized, otherCurve, OverlapPrimeMaximal.Read(L).At(k, A1, A0, A01, inverse, J)))
					otherInOverlap := b.Have(
						"the other chart is a subring of the overlap",
						"subring(«overlap», A₁)",
						By(
							otherAbove,
							otherSubring,
							comm_ring.SubringRingOn.Read(overlapRing).At(A1),
							comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A1),
							module_record.RestrictRingTwice))
					span := b.Have(
						"extending that contraction back gives J",
						"ideal_span(«overlap», A₁ ∩ J) = J",
						By(
							overlapRing,
							otherInOverlap,
							otherDatum[1],
							otherDatum[2],
							otherDatum[3],
							otherDatum[4],
							idealJ,
							ring_away.RingAwaySpanOfContraction.At(
								overlap,
								A1,
								inverse,
								b.TermAs[A]("L.inv(L.inv(t))"),
								J)))
					point := b.Have(
						"so (m, A₁ ∩ J) is a closed point",
						"«scPoint»((m, A₁ ∩ J))",
						By(
							build.At(contraction),
							span,
							otherMaximal,
							localized,
							ring_ideal.PrimeIdealProper.At(overlap, J)))
					only := b.Have(
						"and a point over m has second component A₁ ∩ J",
						"∀Q:prod(set(A), set(A)). «scPoint»(Q) ∧ fst(Q) = m ⇒ snd(Q) = A₁ ∩ J",
						Derive(func(c *Argument) {
							Q := c.FixAs[Prod[Set[A], Set[A]]]("Q")
							over := c.Assume()
							c.Show(
								"the other case would put t in m",
								By(Normalized, over, forced.At(Q), outside))
						}))
					b.Show(
						"so it is the unique point",
						By(assemble.At(contraction), only, point))
				})
		}),
})}

// DegreeOneClosedPointsRational — on a smooth finite curve, a pair of chart
// ideals is a closed point of degree one exactly when it is a rational point
// of the biaffine datum: each proper component is a rational ideal of its
// chart, the two agreeing on the overlap. An ideal of a chart is rational
// exactly when the chart modulo it is a line over k, and the degree of a point
// is that dimension at its ideal in its chart. So the ideal of a closed point
// of degree one, maximal in its chart, is rational; off chart 0 the first
// component is A₀ and the point is rational, and on chart 0 the point is the
// kernel of the residue map of its first component together with the meet of
// A₁ and the span of that kernel, a rational point. Conversely the proper
// components of a rational point are maximal, making it a closed point, and
// its ideal is rational in its chart, of colength one.
var DegreeOneClosedPointsRational = degreeOneClosedPointsRationalThm{family.Add(registry.ProofEntry{
	Name: "DegreeOneClosedPointsRational",
	Key:  "prop_e13bd3064fe1b715",
	Reading: "The rational point is read on the overlap ring with the two charts, as " +
		"curve_rational_point_count and closed_point's elliptic_point_count read it. The last " +
		"three clauses of biaffine_rational_point are those of curve_closed_point; the first two " +
		"replace 'maximal' by 'rational', and the degree is what tells the two apart: a rational " +
		"ideal is a maximal ideal of residue field k, and a maximal ideal of degree one is rational.",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "«scPoint»(P) ∧ «scPointDegree»(P) = 1 ⇔ " +
			"biaffine_rational_point(restrict_ring(field_ring(L), A₀₁), k, A₀, A₁, P)",
		Abbrev: Abbrev{
			{Name: "residues", Text: "λS:set(A). λI:set(A). " +
				"    quotient_module(restrict_module(regular_module(field_ring(L)), S), I)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve Fact,
		) {
			ringOn := field.RingOn.Read(L)
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			overlap := a.TermAs[RingOps[A]]("«overlap»")
			inverse := a.TermAs[A]("L.inv(t)")
			inv := a.TermAs[Fun[A, A]]("L.inv")
			first := a.TermAs[Set[A]]("fst(P)")
			chart, ideal := a.TermAs[Set[A]]("point_chart(A₀, A₁, P)"), a.TermAs[Set[A]]("point_ideal(A₀, P)")
			chartRing := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), point_chart(A₀, A₁, P))")
			datum := a.Conjuncts(
				a.Have(
					"the overlap is a ring with the field k, and with "+
						"the charts a biaffine datum, k lying in both charts",
					"comm_ring_on(«overlap») ∧ "+
						"ring_subfield(«overlap», L.inv, k) ∧ "+
						"biaffine(«overlap», A₀, A₁, t, L.inv(t)) ∧ "+
						"k ⊆ A₀ ∩ A₁",
					By(
						curve,
						OverlapCommRing.Read(L).At(k, A0, A1, A01, t),
						SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
						algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
						field.SubfieldRingSubfield.Read(L).At(k, A01))),
				"the overlap is a ring",
				"k is a field under its operations",
				"the charts and the overlap are a biaffine datum",
				"k lies in both charts")
			constants, biaffine := datum[1], datum[2]
			kIn := a.Have(
				"so k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(datum[3]))
			charts := a.Have(
				"both charts are subrings of L",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁)",
				By(
					curve,
					SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			subrings := a.Have(
				"and subrings of the overlap",
				"subring(«overlap», A₀) ∧ subring(«overlap», A₁)",
				By(biaffine, lattice_pair.BiaffineDef.At(overlap, A0, A1, t, inverse)))
			ringSubfield := a.Have(
				"k is a field under L's operations",
				"ring_subfield(field_ring(L), L.inv, k)",
				By(constants, field.RingSubfieldRestrict.At(ring, A01, inv, k)))
			pointChart := a.Have(
				"P's chart, one of the two, is a subring of L holding k",
				"subring(field_ring(L), point_chart(A₀, A₁, P)) ∧ k ⊆ point_chart(A₀, A₁, P)",
				Simp(Fwd(biaffine_rational_point.PointChartDef)),
				By(charts, kIn))
			a.Iff()
			a.Forward(
				"a closed point of degree one has a rational ideal in its chart, and is a rational point",
				func(b *Argument, given Fact) {
					parts := b.Conjuncts(
						given,
						"P is a closed point",
						"of degree one")
					point, degreeOne := parts[0], parts[1]
					clauses := b.Unfolded(point, CurveClosedPointDef)
					maximal := b.Have(
						"P's ideal is maximal in P's chart",
						"maximal_ideal(restrict_ring(field_ring(L), point_chart(A₀, A₁, P)), point_ideal(A₀, P))",
						By(point, ClosedPointMaximal.At(ring, A0, A1, A01, P)))
					finite := b.Have(
						"P's chart modulo P's ideal there is finite-dimensional over k",
						"finite_dimensional(restrict_ring(field_ring(L), k), "+
							"    «residues»(point_chart(A₀, A₁, P), point_ideal(A₀, P)))",
						By(curve, point, ClosedPointResidue.Read(L).At(k, A0, A1, A01, t, P)))
					rational := b.Have(
						"so P's chart modulo P's ideal is a line, and P's ideal is a rational ideal of P's chart",
						"rational_ideal(field_ring(L), k, point_chart(A₀, A₁, P), point_ideal(A₀, P))",
						By(
							ringOn,
							ringSubfield,
							pointChart,
							maximal,
							finite,
							degreeOne,
							ring_ideal.MaximalIdealIdeal.At(chartRing, ideal),
							module_dimension.RationalIffColengthOne.At(ring, k, inv, chart, ideal),
							ClosedPointDegreeDef.At(ring, k, A0, A1, P)))
					sameReading := b.Have(
						"the overlap's operations being L's, P's ideal is rational on the overlap exactly when on L",
						"rational_ideal(«overlap», k, point_chart(A₀, A₁, P), point_ideal(A₀, P)) ⇔ "+
							"rational_ideal(field_ring(L), k, point_chart(A₀, A₁, P), point_ideal(A₀, P))",
						Simp(
							Fwd(quotient_ring.RationalIdealDef),
							Fwd(module_record.RestrictRingTwice),
							Fwd(module_record.RestrictRingDef)),
						Basic())
					onOverlap := b.Have(
						"so it is a rational ideal of P's chart on the overlap",
						"rational_ideal(«overlap», k, point_chart(A₀, A₁, P), point_ideal(A₀, P))",
						By(rational, sameReading))
					b.Cases(b.Term("fst(P) = A₀"))
					b.When(
						"P lies off chart 0, so its ideal is the second component, and fst(P) is A₀",
						func(c *Argument, whole Fact) {
							onChartOne := c.Conjuncts(
								GroupPremises(whole, biaffine_rational_point.PointOffChartZero.At(A0, A1, P)),
								"its chart is A₁",
								"its ideal is the second component")
							c.Show(
								"the other clauses of a rational point are those of the closed point",
								Simp(Fwd(biaffine_rational_point.BiaffineRationalPointDef)),
								By(Normalized, whole, onOverlap, onChartOne[0], onChartOne[1], clauses))
						})
					b.Otherwise(
						"P lies on chart 0, so its ideal is the first component",
						func(c *Argument, proper Fact) {
							onChartZero := c.Conjuncts(
								GroupPremises(proper, biaffine_rational_point.PointOnChartZero.At(A0, A1, P)),
								"its chart is A₀",
								"its ideal is the first component")
							_, residueMap := c.ObtainAs[Fun[A, A]](
								"fst(P) is the kernel of a ring map φ from A₀ to k fixing k",
								"∃φ:(A → A). "+
									"    ring_homomorphism(restrict_ring(«overlap», A₀), restrict_ring(«overlap», k), φ) ∧ "+
									"    (∀c:A. c ∈ k ⇒ φ(c) = c) ∧ "+
									"    fst(P) = ring_kernel(L.zero, A₀, φ)",
								By(
									datum[0],
									constants,
									subrings,
									kIn,
									onOverlap,
									onChartZero[0],
									onChartZero[1],
									quotient_ring.FieldResiduesHomomorphism.At(overlap, k, inv, A0, first)))
							contraction := c.Have(
								"snd(P) is the meet of A₁ with the ideal fst(P) spans in the overlap",
								"snd(P) = A₁ ∩ ideal_span(«overlap», fst(P))",
								By(proper, curve, point, ClosedPointSecondComponent.Read(L).At(k, A0, A1, A01, t, P)))
							c.Show(
								"so P is the point of φ, a rational point on chart 0",
								By(
									biaffine,
									constants,
									kIn,
									residueMap,
									contraction,
									pairs.PairEta.At(P),
									biaffine_rational_point.RationalPointHomomorphism.At(overlap, A0, A1, t, inverse, k, inv, P)))
						})
				})
			a.Backward(
				"a rational point is a closed point with a rational ideal in its chart, so of degree one",
				func(b *Argument, rational Fact) {
					clauses := b.Unfolded(rational, biaffine_rational_point.BiaffineRationalPointDef)
					maximal := b.Have(
						"the proper components of a rational point are maximal in their charts",
						"(fst(P) ≠ A₀ ⇒ maximal_ideal(restrict_ring(«overlap», A₀), fst(P))) ∧ "+
							"(snd(P) ≠ A₁ ⇒ maximal_ideal(restrict_ring(«overlap», A₁), snd(P)))",
						By(
							biaffine,
							constants,
							kIn,
							rational,
							biaffine_rational_point.RationalPointMaximal.At(overlap, A0, A1, t, inverse, k, inv, P)))
					point := b.Have(
						"so P is a closed point, the clauses after the first two being those of the rational point",
						"«scPoint»(P)",
						Simp(Fwd(CurveClosedPointDef)),
						By(
							Normalized,
							maximal,
							clauses,
							module_record.RestrictRingTwice.At(ring, A01, A0),
							module_record.RestrictRingTwice.At(ring, A01, A1)))
					chartRational := b.Have(
						"P's ideal is a rational ideal of P's chart",
						"rational_ideal(field_ring(L), k, point_chart(A₀, A₁, P), point_ideal(A₀, P))",
						By(charts, kIn, rational, biaffine_rational_point.RationalPointChart.Read(L).At(k, A0, A1, A01, P)))
					b.Show(
						"so P's chart modulo P's ideal is a line: P has degree one",
						By(
							point,
							ringOn,
							ringSubfield,
							pointChart,
							chartRational,
							quotient_ring.RationalIdealDef.At(ring, k, chart, ideal),
							module_dimension.RationalIffColengthOne.At(ring, k, inv, chart, ideal),
							ClosedPointDegreeDef.At(ring, k, A0, A1, P)))
				})
		}),
})}
