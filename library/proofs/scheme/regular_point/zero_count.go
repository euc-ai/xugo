// zero_count.go — the zeros of a section with poles at one point.
// Multiplication by a nonzero f with poles of order at most n at P maps N⁻¹
// into the structure pair O, where N is the pole pair, and its image f · N⁻¹ is
// the ideal pair of the zero divisor of f: invertible of degree -n, and inside
// the ideal pair of each zero of f off P. The pair stands in for that divisor,
// which f itself does not have: the model may be singular at other points. A
// pair inside the structure pair and inside the ideals of a finite set of
// regular points has degree at most minus their number
// (curve_degree.InvertibleInsidePointsDegree): so a finite set of zeros has at
// most n points, and hence so has the set of all zeros.

package regular_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// EvaluationZeroInIdeal — at a regular point Q, a member x of Q's chart killed
// by evaluation at Q lies in Q's ideal on the chart: x is a constant y modulo
// the ideal (biaffine_rational_point.RationalPointChart), and evaluation kills
// the ideal and fixes y, so y = v(x) = 0.
var EvaluationZeroInIdeal = evaluationZeroInIdealThm{family.Add(registry.ProofEntry{
	Name: "EvaluationZeroInIdeal",
	Key:  "prop_bb1adecc463a2b07",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀Q:prod(set(A), set(A)). ∀x:A.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(Q)",
			"x ∈ point_chart(A₀, A₁, Q)",
			"«rpEvaluation»(Q, x) = L.zero",
		},
		Conclusion: "x ∈ point_ideal(A₀, Q)",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, Q)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, Q))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			Q *Expr[_LatticePair],
			curve, point Fact,
			x *Expr[A],
			member, vanishes Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			source := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), «local»)")
			target := a.TermAs[RingOps[A]]("«rpScalars»")
			chart := a.TermAs[Set[A]]("point_chart(A₀, A₁, Q)")
			evaluation := a.TermAs[Fun[A, A]]("«rpEvaluation»(Q)")
			rational := a.Have(
				"Q is a rational point",
				"biaffine_rational_point(restrict_ring(field_ring(L), A₀₁), k, A₀, A₁, Q)",
				By(point, lattice_pair_twist.BiaffineRegularPointDef.At(ring, k, A0, A1, A01, Q)))
			charts := a.Have(
				"the charts are subrings of L holding the constants",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁) ∧ k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			onChart := a.Conjuncts(
				GroupPremises(
					charts, rational, biaffine_rational_point.RationalPointChart.Read(L).At(k, A0, A1, A01, Q)),
				"Q's chart is a subring of L",
				"holding the constants",
				"and Q's ideal is the ideal of a rational point of it")
			parts := a.Conjuncts(
				a.Unfolded(onChart[2], quotient_ring.RationalIdealDef),
				"it is an ideal of the chart",
				"missing one",
				"and each member of the chart is a constant modulo it")
			placed := a.Have(
				"so the chart holds the ideal, and lies in L",
				"point_ideal(A₀, Q) ⊆ point_chart(A₀, A₁, Q) ∧ point_chart(A₀, A₁, Q) ⊆ L.carrier",
				BySets(
					onChart[0],
					parts[0],
					comm_ring.SubringSubset.At(ring, chart),
					ring_ideal.IdealSubset.At(
						a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), point_chart(A₀, A₁, Q))"),
						a.TermAs[Set[A]]("point_ideal(A₀, Q)"))))
			inLocal := a.Have(
				"the chart lies in the local ring at the regular point Q",
				"point_chart(A₀, A₁, Q) ⊆ «local»",
				By(curve, point, RegularPointLocalRing.Read(L).At(k, A0, A1, A01, t, Q)))
			// The order at Q is the point's law read at L.
			pointOrder := RegularPointOrderAndFiltration.Read(L).AsFact().At(k, A0, A1, A01, t)
			evaluates := a.Have(
				"evaluation is a ring map onto the constants, fixing them, whose kernel the ideal generates",
				"ring_homomorphism(restrict_ring(field_ring(L), «local»), «rpScalars», «rpEvaluation»(Q)) ∧ "+
					"(∀c:A. c ∈ k ⇒ «rpEvaluation»(Q, c) = c) ∧ "+
					"{c:A | c ∈ «local» ∧ «rpEvaluation»(Q, c) = L.zero} = «maximal»",
				By(a.Simplified(GroupPremises(curve, point, pointOrder.At(Q)))))
			inIdeal := a.Have(
				"the ideal lies in what it generates on the local ring",
				"point_ideal(A₀, Q) ⊆ «maximal»",
				Cite(ring_ideal.SpanContains))
			killed := a.Have(
				"so evaluation kills the ideal",
				"∀c:A. c ∈ point_ideal(A₀, Q) ⇒ «rpEvaluation»(Q, c) = L.zero",
				BySets(evaluates, inIdeal))
			y, near := a.ObtainAs[A](
				"x is a constant y modulo the ideal",
				"∃y:A. y ∈ k ∧ x + -y ∈ point_ideal(A₀, Q)",
				By(parts[2].At(x), member))
			difference := a.TermAs[A]("x + -y")
			held := a.Have(
				"y and x - y lie in the local ring, and x and y in L",
				"y ∈ «local» ∧ x + -y ∈ «local» ∧ x ∈ L.carrier ∧ y ∈ L.carrier",
				BySets(member, near, onChart[1], placed, inLocal))
			regroup := a.Have(
				"x is x - y plus y",
				"(x + -y) + y = x",
				ByArith(L, held))
			adds := a.Have(
				"evaluation adds",
				"«rpEvaluation»(Q, (x + -y) + y) = «rpEvaluation»(Q, x + -y) + «rpEvaluation»(Q, y)",
				By(evaluates, held, ring_homomorphism.MapAdd.At(source, target, evaluation, difference, y)))
			values := a.Have(
				"it kills x - y and fixes y",
				"«rpEvaluation»(Q, x + -y) = L.zero ∧ «rpEvaluation»(Q, y) = y",
				By(near, evaluates, killed.At(difference)))
			constant := a.Have(
				"so the constant is zero",
				"y = L.zero",
				Derive(func(c *Argument) {
					absorbed := c.Have(
						"zero is absorbed",
						"L.zero + y = y",
						ByArith(L, held))
					c.Show(
						"0 = v(x) = 0 + y",
						By(absorbed, regroup, adds, values, vanishes))
				}))
			unchanged := a.Have(
				"x minus zero is x",
				"x + -L.zero = x",
				ByArith(L, held))
			a.Show(
				"so x - y is x, and x lies in the ideal",
				By(Normalized, near, constant, unchanged))
		}),
})}

// SectionZerosInside — for a nonzero f with poles of order at most n at P, the pair
// f · N⁻¹, N the pole pair, lies in the structure pair and in the ideal pair of every
// zero of f off P. N holds one and f, so a member g of a chart of N⁻¹ lies in the chart
// with f · g. At a zero Q, evaluation kills f · g, which EvaluationZeroInIdeal puts in
// Q's ideal on the chart of its local ring; on the other chart, if Q is proper there,
// the invertible pair f · N⁻¹ lies in Q by PairBelowContraction.
var SectionZerosInside = sectionZerosInsideThm{family.Add(registry.ProofEntry{
	Name: "SectionZerosInside",
	Key:  "prop_569a5a21a6fd0d8a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:num. ∀f:A.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
			"f ∈ «rpPoles»(n).carrier",
			"f ≠ L.zero",
		},
		Conclusion: "fst(«zeros») ⊆ A₀ ∧ " +
			"snd(«zeros») ⊆ A₁ ∧ " +
			"(∀Q:prod(set(A), set(A)). " +
			"    «rpPoint»(Q) ∧ Q ≠ P ∧ «rpEvaluation»(Q, f) = L.zero ⇒ " +
			"    fst(«zeros») ⊆ fst(Q) ∧ snd(«zeros») ⊆ snd(Q))",
		Abbrev: Abbrev{
			{Name: "poleInverse", Text: "lattice_pair_inverse(field_ring(L), A₀, A₁, «rpPolePair»(n))"},
			{Name: "zeros", Text: "lattice_pair_scale(f, «poleInverse»)"},
			{Name: "overlap", Text: "restrict_ring(field_ring(L), A₀₁)"},
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			n *Expr[Nat],
			f *Expr[A],
			curve, point, section, nonzero Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			overlap := a.TermAs[RingOps[A]]("«overlap»")
			pole := a.TermAs[_LatticePair]("«rpPolePair»(n)")
			poleInverse := a.TermAs[_LatticePair]("«poleInverse»")
			datum := GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t))
			subrings := a.Have(
				"the overlap lies in L, the charts are a biaffine datum, and they are subrings of L",
				"A₀₁ ⊆ L.carrier ∧ "+
					"biaffine(«overlap», A₀, A₁, t, L.inv(t)) ∧ "+
					"subring(field_ring(L), A₀) ∧ "+
					"subring(field_ring(L), A₁) ∧ "+
					"subring(field_ring(L), A₀₁) ∧ "+
					"A₀ ⊆ A₀₁ ∧ "+
					"A₁ ⊆ A₀₁",
				By(datum, invertible_lattice_pair.ChartRingsInField.Read(L).At(A0, A1, A01, t)))
			poleIn := a.Have(
				"the pole pair is invertible, with charts inside L",
				"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «rpPolePair»(n)) ∧ "+
					"fst(«rpPolePair»(n)) ⊆ L.carrier ∧ "+
					"snd(«rpPolePair»(n)) ⊆ L.carrier",
				By(
					curve,
					point,
					PolePairDegree.Read(L).At(k, A0, A1, A01, t, P, n),
					invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, pole)))
			sectionIn := a.Have(
				"f lies in both charts of the pole pair",
				"f ∈ fst(«rpPolePair»(n)) ∩ snd(«rpPolePair»(n))",
				By(
					section,
					SinglePointPoleSpaceDef.At(ring, A0, A1, P, n),
					lattice_pair.LatticePairH0Def.At(
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"), pole)))
			oneIn := a.Have(
				"so does one",
				"L.one ∈ fst(«rpPolePair»(n)) ∩ snd(«rpPolePair»(n))",
				By(
					curve,
					point,
					PolesHoldOne.Read(L).At(k, A0, A1, A01, t, P, n),
					SinglePointPoleSpaceDef.At(ring, A0, A1, P, n),
					lattice_pair.LatticePairH0Def.At(
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"), pole)))
			fIn := a.Have(
				"f lies in L",
				"f ∈ L.carrier",
				BySets(sectionIn, poleIn))
			inverted := a.Have(
				"the inverse of the pole pair is invertible",
				"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «poleInverse»)",
				By(
					datum,
					poleIn,
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, pole)))
			invertible := a.Have(
				"so f · N⁻¹ is invertible, f being nonzero",
				"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «zeros»)",
				By(
					datum,
					fIn,
					nonzero,
					inverted,
					invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, poleInverse),
					invertible_lattice_pair.InvertibleLatticeScale.Read(L).At(
						A0, A1, A01, t, a.MemberOf[on.L](f, fIn), poleInverse)))
			latticePair := a.Conjuncts(
				a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef),
				"its first chart is invertible",
				"its second chart is invertible",
				"it is a lattice pair")[2]
			clearing := a.Have(
				"a member of the inverse of a set holding one and f lies in the chart, with its multiple by f",
				Statement{
					Binders:    "∀S T:set(A). ∀g:A.",
					Hypotheses: []string{"L.one ∈ T", "f ∈ T", "g ∈ fractional_inverse(field_ring(L), S, T)"},
					Conclusion: "g ∈ S ∧ f * g ∈ S",
				},
				Derive(func(b *Argument) {
					S := b.FixAs[Set[A]]("S")
					T := b.FixAs[Set[A]]("T")
					b.FixAs[A]("g")
					assumed := b.Conjuncts(
						b.Assume(),
						"T holds one",
						"T holds f",
						"g lies in the inverse of T")
					holdsF, member := assumed[1], assumed[2]
					inChart := b.Have(
						"one carries g into S",
						"g ∈ S",
						BySets(
							member,
							GroupPremises(assumed[0], fractional_ideal.FractionalInverseOfUnit.Read(L).At(S, T))))
					carried := b.Have(
						"f carries g into S",
						"g ∈ L.carrier ∧ g * f ∈ S",
						BySets(holdsF, member, fractional_ideal.FractionalInverseDef.At(ring, S, T)))
					swapped := b.Have(
						"f · g is g · f",
						"f * g = g * f",
						ByArith(L, fIn, carried))
					b.Show(
						"g and f · g lie in S",
						By(Normalized, inChart, carried, swapped))
				}))
			scaled := a.Have(
				"the charts of f · N⁻¹ are f times those of N⁻¹",
				"fst(«zeros») = image(L.mul(f), fst(«poleInverse»)) ∧ "+
					"snd(«zeros») = image(L.mul(f), snd(«poleInverse»))",
				Simp(Fwd(invertible_lattice_pair.LatticePairScaleDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				Basic())
			inverseCharts := a.Have(
				"the charts of N⁻¹ are the inverses of those of N",
				"fst(«poleInverse») = fractional_inverse(field_ring(L), A₀, fst(«rpPolePair»(n))) ∧ "+
					"snd(«poleInverse») = fractional_inverse(field_ring(L), A₁, snd(«rpPolePair»(n)))",
				Simp(Fwd(invertible_lattice_pair.LatticePairInverseDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				Basic())
			sections := a.Have(
				"so a member g of a chart of N⁻¹ lies in the chart, with f · g",
				"(∀g:A. g ∈ fst(«poleInverse») ⇒ g ∈ A₀ ∧ f * g ∈ A₀) ∧ "+
					"(∀g:A. g ∈ snd(«poleInverse») ⇒ g ∈ A₁ ∧ f * g ∈ A₁)",
				BySets(inverseCharts, sectionIn, oneIn, clearing))
			structure := a.Have(
				"f · N⁻¹ lies in the structure pair",
				"fst(«zeros») ⊆ A₀ ∧ snd(«zeros») ⊆ A₁",
				BySets(scaled, sections))
			constants := a.Have(
				"the constants are a field under the overlap's operations, inside both charts",
				"ring_subfield(«overlap», L.inv, k) ∧ k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(GroupPremises(datum, field.SubfieldRingSubfield.Read(L).At(k, A01))))
			// The order at a point is the point's law read at L.
			pointOrder := RegularPointOrderAndFiltration.Read(L).AsFact().At(k, A0, A1, A01, t)
			atZeros := a.Have(
				"f · N⁻¹ lies in the ideal pair of a zero of f off P",
				Statement{
					Binders: "∀Q:prod(set(A), set(A)).",
					Hypotheses: []string{
						"«rpPoint»(Q)",
						"Q ≠ P",
						"«rpEvaluation»(Q, f) = L.zero",
					},
					Conclusion: "fst(«zeros») ⊆ fst(Q) ∧ snd(«zeros») ⊆ snd(Q)",
				},
				Derive(func(b *Argument) {
					Q := b.FixAs[_LatticePair]("Q")
					assumed := b.Conjuncts(
						b.Assume(),
						"Q is a regular point",
						"other than P",
						"where f vanishes")
					pointQ, distinct, vanishes := assumed[0], assumed[1], assumed[2]
					evaluation := b.TermAs[Fun[A, A]]("«rpEvaluation»(Q)")
					source := b.TermAs[RingOps[A]]("restrict_ring(field_ring(L), «local»(Q))")
					target := b.TermAs[RingOps[A]]("«rpScalars»")
					inLocal := b.Have(
						"f lies in the local ring at Q",
						"f ∈ «local»(Q)",
						By(pointQ, distinct, section, b.Simplified(GroupPremises(curve, point, pointOrder.At(P)))))
					homomorphism := b.Have(
						"evaluation at Q is a ring map to the constants",
						"ring_homomorphism(restrict_ring(field_ring(L), «local»(Q)), «rpScalars», «rpEvaluation»(Q))",
						By(b.Simplified(GroupPremises(curve, pointQ, pointOrder.At(Q)))))
					multiples := b.Have(
						"every multiple of f on the chart by a member of the chart lies in the ideal",
						"∀g:A. g ∈ point_chart(A₀, A₁, Q) ∧ f * g ∈ point_chart(A₀, A₁, Q) ⇒ f * g ∈ point_ideal(A₀, Q)",
						Derive(func(c *Argument) {
							g := c.FixAs[A]("g")
							both := c.Assume()
							gLocal := c.Have(
								"g lies in the local ring",
								"g ∈ «local»(Q)",
								BySets(GroupPremises(curve, pointQ, RegularPointLocalRing.Read(L).At(k, A0, A1, A01, t, Q)), both))
							value := c.Have(
								"so v(g) is a constant",
								"«rpEvaluation»(Q, g) ∈ k",
								By(homomorphism, gLocal, ring_homomorphism.MapIn.At(source, target, evaluation, g)))
							inL := c.Have(
								"inside L",
								"«rpEvaluation»(Q, g) ∈ L.carrier",
								BySets(value, constants, subrings))
							absorbed := c.Have(
								"zero annihilates it",
								"L.zero * «rpEvaluation»(Q, g) = L.zero",
								ByArith(L, inL))
							multiplies := c.Have(
								"v multiplies",
								"«rpEvaluation»(Q, f * g) = «rpEvaluation»(Q, f) * «rpEvaluation»(Q, g)",
								By(homomorphism, inLocal, gLocal, ring_homomorphism.MapMul.At(source, target, evaluation, f, g)))
							c.Show(
								"v(f · g) = v(f) · v(g) = 0, and f · g lies in the chart",
								By(
									both,
									vanishes,
									absorbed,
									multiplies,
									curve,
									pointQ,
									EvaluationZeroInIdeal.Read(L).At(k, A0, A1, A01, t, Q, c.TermAs[A]("f * g"))))
						}))
					b.Cases(b.Term("fst(Q) = A₀"))
					b.When(
						"off chart 0 Q is proper on chart 1, the chart of its local ring",
						func(c *Argument, whole Fact) {
							onChart := c.Have(
								"multiples on chart 1 lie in Q's ideal",
								"∀g:A. g ∈ A₁ ∧ f * g ∈ A₁ ⇒ f * g ∈ snd(Q)",
								By(Normalized, whole, multiples, biaffine_rational_point.PointOffChartZero.At(A0, A1, Q)))
							c.Show(
								"chart 0 is all of fst(Q), and snd(Q) holds the multiples on chart 1",
								BySets(whole, scaled, sections, onChart))
						})
					b.Otherwise(
						"on chart 0 Q's ideal holds the multiples there",
						func(c *Argument, properFirst Fact) {
							onChart := c.Have(
								"multiples on chart 0 lie in Q's ideal",
								"∀g:A. g ∈ A₀ ∧ f * g ∈ A₀ ⇒ f * g ∈ fst(Q)",
								By(Normalized, properFirst, multiples, biaffine_rational_point.PointOnChartZero.At(A0, A1, Q)))
							firstInside := c.Have(
								"so the first chart of f · N⁻¹ lies in Q",
								"fst(«zeros») ⊆ fst(Q)",
								BySets(scaled, sections, onChart))
							c.Cases(c.Term("snd(Q) = A₁"))
							c.When(
								"off chart 1 there is nothing more to show",
								func(e *Argument, whole Fact) {
									e.Show(
										"the second chart lies in A₁",
										BySets(whole, firstInside, scaled, sections))
								})
							c.Otherwise(
								"on both charts the ideal of chart 1 is the contraction of what fst(Q) spans",
								func(e *Argument, properSecond Fact) {
									rational := e.Have(
										"Q is a rational point",
										"biaffine_rational_point(«overlap», k, A₀, A₁, Q)",
										By(pointQ, lattice_pair_twist.BiaffineRegularPointDef.At(ring, k, A0, A1, A01, Q)))
									contraction := e.Have(
										"snd(Q) is chart 1 meeting what fst(Q) spans on the overlap",
										"snd(Q) = A₁ ∩ ideal_span(«overlap», fst(Q))",
										By(
											properFirst,
											properSecond,
											subrings,
											constants,
											rational,
											biaffine_rational_point.RationalPointOverlap.At(
												overlap, A0, A1, t, e.TermAs[A]("L.inv(t)"), k, e.TermAs[Fun[A, A]]("L.inv"), Q)))
									inChart := e.Have(
										"fst(Q) lies in chart 0",
										"fst(Q) ⊆ A₀",
										By(
											subrings,
											rational,
											biaffine_rational_point.PointIdealLattice.At(overlap, A0, A1, t, e.TermAs[A]("L.inv(t)"), k, Q)))
									inOverlap := e.Have(
										"so in the overlap",
										"fst(Q) ⊆ A₀₁",
										BySets(subrings, inChart))
									e.Show(
										"so the second chart of f · N⁻¹ lies in the contraction",
										By(
											subrings,
											latticePair,
											structure,
											inOverlap,
											contraction,
											firstInside,
											lattice_pair_twist.PairBelowContraction.Read(L).At(
												A0, A1, A01, e.TermAs[_LatticePair]("«zeros»"), Q)))
								})
						})
				}))
			a.Show(
				"f · N⁻¹ lies in the structure pair and inside every zero of f off P",
				By(structure, atZeros))
		}),
})}

// NonzeroSectionZeroCount — a nonzero f with poles of order at most n at P has at
// most n zeros off P: a finite set of them has at most n points by
// curve_degree.InvertibleInsidePointsDegree at f · N⁻¹, and
// cardinality.BoundedFiniteSubsets passes to them all.
var NonzeroSectionZeroCount = nonzeroSectionZeroCountThm{family.Add(registry.ProofEntry{
	Name: "NonzeroSectionZeroCount",
	Key:  "prop_d457e50fdd8de1f1",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)). ∀n:num. ∀f:A.",
		Hypotheses: []string{
			"«rpCurve»",
			"«rpPoint»(P)",
			"f ∈ «rpPoles»(n).carrier",
			"f ≠ L.zero",
		},
		Conclusion: "finite(«zeroSet») ∧ card(«zeroSet») ≤ n",
		Abbrev: Abbrev{
			{Name: "poleInverse", Text: "lattice_pair_inverse(field_ring(L), A₀, A₁, «rpPolePair»(n))"},
			{Name: "zeros", Text: "lattice_pair_scale(f, «poleInverse»)"},
			{Name: "zeroSet", Text: "{Q:prod(set(A), set(A)) | " +
				"    «rpPoint»(Q) ∧ Q ≠ P ∧ «rpEvaluation»(Q, f) = L.zero}"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[_LatticePair],
			n *Expr[Nat],
			f *Expr[A],
			curve, point, section, nonzero Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			pole := a.TermAs[_LatticePair]("«rpPolePair»(n)")
			poleInverse := a.TermAs[_LatticePair]("«poleInverse»")
			datum := GroupPremises(curve, algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t))
			polePair := a.Have(
				"the pole pair is invertible of degree n",
				"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «rpPolePair»(n)) ∧ "+
					"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «rpPolePair»(n)) = n",
				By(curve, point, PolePairDegree.Read(L).At(k, A0, A1, A01, t, P, n)))
			inverted := a.Have(
				"so its inverse is invertible",
				"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «poleInverse»)",
				By(
					datum,
					polePair,
					invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, pole)))
			poleInL := a.Have(
				"the pole pair lies in L",
				"fst(«rpPolePair»(n)) ⊆ L.carrier ∧ snd(«rpPolePair»(n)) ⊆ L.carrier",
				By(polePair, invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, pole)))
			sectionIn := a.Have(
				"f lies in the pole pair",
				"f ∈ fst(«rpPolePair»(n)) ∩ snd(«rpPolePair»(n))",
				By(
					section,
					SinglePointPoleSpaceDef.At(ring, A0, A1, P, n),
					lattice_pair.LatticePairH0Def.At(
						a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))"), pole)))
			fIn := a.Have(
				"so f lies in L",
				"f ∈ L.carrier",
				BySets(sectionIn, poleInL))
			fMember := a.MemberOf[on.L](f, fIn)
			inverseInL := a.Have(
				"the inverse of the pole pair lies in L",
				"fst(«poleInverse») ⊆ L.carrier ∧ snd(«poleInverse») ⊆ L.carrier",
				By(inverted, invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, poleInverse)))
			invertible := a.Have(
				"f · N⁻¹ is invertible, f being nonzero",
				"invertible_lattice_pair(field_ring(L), A₀, A₁, A₀₁, «zeros»)",
				By(
					datum,
					fIn,
					nonzero,
					inverseInL,
					inverted,
					invertible_lattice_pair.InvertibleLatticeScale.Read(L).At(A0, A1, A01, t, fMember, poleInverse)))
			degree := a.Have(
				"of degree -n",
				"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «zeros») = -n",
				By(
					curve,
					inverted,
					fIn,
					nonzero,
					polePair,
					curve_degree.DegreeScale.Read(L).At(k, A0, A1, A01, t, fMember, poleInverse),
					curve_degree.DegreeInverse.Read(L).At(k, A0, A1, A01, t, pole)))
			inside := a.Have(
				"it lies in the structure pair and in the ideal of each zero off P",
				"fst(«zeros») ⊆ A₀ ∧ "+
					"snd(«zeros») ⊆ A₁ ∧ "+
					"(∀Q:prod(set(A), set(A)). "+
					"    «rpPoint»(Q) ∧ Q ≠ P ∧ «rpEvaluation»(Q, f) = L.zero ⇒ "+
					"    fst(«zeros») ⊆ fst(Q) ∧ snd(«zeros») ⊆ snd(Q))",
				By(curve, point, section, nonzero, SectionZerosInside.Read(L).At(k, A0, A1, A01, t, P, n, f)))
			pair := a.TermAs[_LatticePair]("«zeros»")
			bounded := a.Have(
				"a finite set of such zeros has at most n points",
				"∀S:set(prod(set(A), set(A))). finite(S) ∧ S ⊆ «zeroSet» ⇒ card(S) ≤ n",
				Derive(func(b *Argument) {
					S := b.FixAs[Set[_LatticePair]]("S")
					assumed := b.Conjuncts(
						b.Assume(),
						"S is finite",
						"and a set of zeros")
					finiteS, inZeroSet := assumed[0], assumed[1]
					pointwise := b.Have(
						"each point of S is a regular zero off P",
						"∀Q:prod(set(A), set(A)). Q ∈ S ⇒ «rpPoint»(Q) ∧ Q ≠ P ∧ «rpEvaluation»(Q, f) = L.zero",
						BySets(inZeroSet))
					regular := b.Have(
						"so it is a regular point",
						"∀Q:prod(set(A), set(A)). Q ∈ S ⇒ «rpPoint»(Q)",
						Derive(func(c *Argument) {
							Q := c.FixAs[_LatticePair]("Q")
							member := c.Assume()
							c.Show(
								"Q is a regular zero off P",
								By(pointwise.At(Q), member))
						}))
					each := b.Have(
						"and f · N⁻¹ lies inside it",
						"∀Q:prod(set(A), set(A)). Q ∈ S ⇒ fst(«zeros») ⊆ fst(Q) ∧ snd(«zeros») ⊆ snd(Q)",
						Derive(func(c *Argument) {
							Q := c.FixAs[_LatticePair]("Q")
							member := c.Assume()
							c.Show(
								"it is a zero off P",
								By(pointwise.At(Q), member, inside))
						}))
					total := b.Have(
						"so the degree bound reads at f · N⁻¹",
						"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «zeros») + int_of_num(card(S)) ≤ &0",
						By(
							curve,
							finiteS,
							regular,
							invertible,
							inside,
							each,
							curve_degree.InvertibleInsidePointsDegree.Read(L).At(k, A0, A1, A01, t, S, pair)))
					asIntegers := b.Have(
						"as integers, the count is at most n",
						"int_of_num(card(S)) ≤ n",
						ByArith(total, degree))
					b.Show(
						"and so as numbers",
						By(asIntegers, int_embed.OfNumLe.At(b.TermAs[Nat]("card(S)"), n)))
				}))
			zeroSet := a.TermAs[Set[_LatticePair]]("«zeroSet»")
			a.Show(
				"a set whose finite subsets have at most n points is finite with at most n points",
				By(bounded, cardinality.BoundedFiniteSubsets.At(n, zeroSet)))
		}),
})}
