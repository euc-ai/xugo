package plane_model

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_composite"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/constant_field_extension"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/rational_point_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_away"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/divisor_lattice_correspondence"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/registry"
)

// SecondChartRegular — a point of the first chart A₀ whose ideal m holds t − t₀
// and z − z₀, with a relation (z − z₀)·g = (t − t₀)·h and g off the point, is
// regular on the second chart A₁ = k[u][w], u = t⁻¹ and w = uᵇ·z, when it lies on
// that chart too: the span of m in the overlap meets A₁ in a rational ideal. That
// last hypothesis is what keeps the point off t = 0: the ideal is the kernel of a
// point ψ of A₁, and ψ(u)·t₀ = 1. Then uᵇ − ψ(uᵇ) is a multiple of u − ψ(u), so
// w − ψ(w) = uᵇ(z − z₀) + z₀·(uᵇ − ψ(uᵇ)), and t − t₀ = −t·t₀·(u − ψ(u)); a power
// of u clears g and h into A₁ and turns the relation into one between u − ψ(u)
// and w − ψ(w), with a multiple of g off the point, so the Jacobian criterion
// makes the ideal invertible.
var SecondChartRegular = secondChartRegularThm{family.Add(registry.ProofEntry{
	Name: "SecondChartRegular",
	Key:  "prop_1b7b0ffcb3f88dde",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "overlapRing", Text: "restrict_ring(field_ring(L), A₀₁)"},
			{Name: "spanned", Text: "ideal_span(«overlapRing», m)"},
			{Name: "secondPoint", Text: "A₁ ∩ «spanned»"},
			{Name: "uPow", Text: "λn:num. monoid_pow(L.mul, L.one, L.inv(t), n)"},
			{Name: "tPow", Text: "λn:num. monoid_pow(L.mul, L.one, t, n)"},
			{Name: "power", Text: "«uPow»(b)"},
			{Name: "scaled", Text: "«power» * z"},
			{Name: "secondChart", Text: "polynomial_image(field_ring(L), " +
				"    polynomial_image(field_ring(L), k, L.inv(t)), " +
				"    «scaled»)"},
			{Name: "cleared", Text: "λi:num. λj:num. «uPow»(j) * («uPow»(i) * g)"},
			{Name: "multiplier", Text: "λx:A. λi:num. λj:num. " +
				"    -t₀ * «uPow»(b - 1) * («uPow»(i) * («uPow»(j) * h)) + z₀ * x * «cleared»(i, j)"},
		},
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁ m:set(A). ∀t z t₀ z₀ g h:A. ∀b:num.",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"A₁ = «secondChart»",
			"0 < b",
			"t₀ ∈ k",
			"z₀ ∈ k",
			"z ∈ A₀",
			"g ∈ A₀",
			"h ∈ A₀",
			"ring_ideal(restrict_ring(field_ring(L), A₀), m)",
			"t - t₀ ∈ m",
			"z - z₀ ∈ m",
			"g ∉ m",
			"m = A₀ ∩ «spanned»",
			"(z - z₀) * g = (t - t₀) * h",
			"rational_ideal(«overlapRing», k, A₁, «secondPoint»)",
		},
		Conclusion: "invertible_fractional(field_ring(L), A₁, «secondPoint»)",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01, m *Expr[Set[A]],
			t, z, t0, z0, g, h *Expr[A],
			b *Expr[Nat],
			curve, secondReading, bPositive, t0In, z0In, zIn, gIn, hIn, ideal, tOnPoint, zOnPoint, gOff, contracted, related, rational Fact,
		) {
			ops := a.TermAs[FieldOps[A]]("L")
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			overlapRing := a.TermAs[RingOps[A]]("«overlapRing»")
			spanned := a.TermAs[Set[A]]("«spanned»")
			second := a.TermAs[Set[A]]("«secondPoint»")
			inverse := a.TermAs[Fun[A, A]]("L.inv")

			// The curve over the line: the charts inside the overlap, and k[1/t] inside the second chart.
			datum := a.Conjuncts(
				a.Have(
					"what the curve over the line gives",
					"subfield(L, k) ∧ "+
						"t ∈ L.carrier ∧ "+
						"¬algebraic_over(L, k, L.inv(t)) ∧ "+
						"biaffine(«overlapRing», A₀, A₁, t, L.inv(t)) ∧ "+
						"subring(field_ring(L), A₀₁) ∧ "+
						"subring(field_ring(L), A₁) ∧ "+
						"A₀ ⊆ A₀₁ ∧ "+
						"A₁ ⊆ A₀₁ ∧ "+
						"t ∈ A₀ ∧ "+
						"L.inv(t) ∈ A₁ ∧ "+
						"t * L.inv(t) = L.one ∧ "+
						"A₀₁ = ring_away(«overlapRing», A₁, L.inv(t)) ∧ "+
						"polynomial_image(field_ring(L), k, L.inv(t)) ⊆ A₁",
					By(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t))),
				"k is a subfield of L",
				"t lies in L",
				"the inverse of t is transcendental over k",
				"the charts are biaffine in the overlap",
				"the overlap is a subring",
				"the second chart is a subring",
				"the first chart lies in the overlap",
				"the second chart lies in the overlap",
				"t lies in the first chart",
				"its inverse lies in the second",
				"t times its inverse is one",
				"the overlap is the second chart with the inverse of t inverted",
				"k[1/t] lies in the second chart")
			kSubfield, tIn, inverseTranscendental, biaffine := datum[0], datum[1], datum[2], datum[3]
			overlapSubring, secondSubring := datum[4], datum[5]
			firstInOverlap, secondInOverlap, tInFirst, uInSecond, unit :=
				datum[6], datum[7], datum[8], datum[9], datum[10]
			awayFromU, polesInSecond := datum[11], datum[12]
			overlap := a.Conjuncts(
				a.Have(
					"the overlap is a ring holding the second chart as a subring",
					"comm_ring_on(«overlapRing») ∧ subring(«overlapRing», A₁)",
					By(biaffine, lattice_pair.BiaffineDef.At(overlapRing, A0, A1, t, a.TermAs[A]("L.inv(t)")))),
				"the overlap is a ring",
				"the second chart is a subring of it")
			overlapOn, secondSubOverlap := overlap[0], overlap[1]
			u := a.TermAs[A]("L.inv(t)")
			line := a.TermAs[Set[A]]("polynomial_image(field_ring(L), k, L.inv(t))")
			power := a.TermAs[A]("«power»")
			scaled := a.TermAs[A]("«scaled»")
			tm := a.MemberOf[on.L](t, tIn)
			um := field.InvIn.Read(L).At(tm)
			lineData := a.Have(
				"k[1/t] is a subring holding k and the inverse of t",
				"subring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(t))) ∧ "+
					"k ⊆ polynomial_image(field_ring(L), k, L.inv(t)) ∧ "+
					"L.inv(t) ∈ polynomial_image(field_ring(L), k, L.inv(t))",
				By(kSubfield, algebraic_element.PolynomialImageRing.Read(L).At(k, um)))
			kInSecond := a.Have(
				"k lies in the second chart",
				"k ⊆ A₁",
				BySets(lineData, polesInSecond))
			members := a.Have(
				"the data lie in the charts and in L",
				"t₀ ∈ A₁ ∧ "+
					"z₀ ∈ A₁ ∧ "+
					"t₀ ∈ A₀₁ ∧ "+
					"z₀ ∈ A₀₁ ∧ "+
					"L.inv(t) ∈ A₀₁ ∧ "+
					"t ∈ A₀₁ ∧ "+
					"z ∈ A₀₁ ∧ "+
					"g ∈ A₀₁ ∧ "+
					"h ∈ A₀₁ ∧ "+
					"m ⊆ A₀₁ ∧ "+
					"A₀₁ ⊆ L.carrier ∧ "+
					"t₀ ∈ L.carrier ∧ "+
					"z₀ ∈ L.carrier ∧ "+
					"L.inv(t) ∈ L.carrier ∧ "+
					"z ∈ L.carrier ∧ "+
					"g ∈ L.carrier ∧ "+
					"h ∈ L.carrier",
				BySets(
					t0In,
					z0In,
					kInSecond,
					uInSecond,
					tInFirst,
					zIn,
					gIn,
					hIn,
					firstInOverlap,
					secondInOverlap,
					ideal,
					ring_ideal.IdealSubset.At(a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀)"), m),
					overlapSubring,
					comm_ring.SubringSubset.At(ring, A01)))
			subfieldRing := a.Have(
				"k is a subfield of the overlap ring",
				"ring_subfield(«overlapRing», L.inv, k)",
				By(kSubfield, field.SubfieldRingSubfield.Read(L).At(k, A01)))

			// The second component is the kernel of a point ψ of the second chart onto k, fixing k.
			psi, psiData := a.ObtainAs[Fun[A, A]](
				"the second component, a rational ideal, is the kernel of a point ψ of the second chart",
				"∃ψ:(A → A). "+
					"    ring_homomorphism(restrict_ring(«overlapRing», A₁), restrict_ring(«overlapRing», k), ψ) ∧ "+
					"    (∀c:A. c ∈ k ⇒ ψ(c) = c) ∧ "+
					"    «secondPoint» = ring_kernel(L.zero, A₁, ψ)",
				By(
					overlapOn,
					subfieldRing,
					secondSubOverlap,
					kInSecond,
					rational,
					quotient_ring.FieldResiduesHomomorphism.At(overlapRing, k, inverse, A1, second)),
				Named("ψ"))
			psiParts := a.Conjuncts(
				psiData,
				"ψ is a ring map from the second chart onto k",
				"fixing k",
				"whose kernel is the second component")
			fixes := psiParts[1]
			homSecond := a.Have(
				"ψ is a ring map of the second chart read in L",
				"ring_homomorphism(restrict_ring(field_ring(L), A₁), restrict_ring(field_ring(L), k), ψ)",
				By(
					Normalized,
					psiParts[0],
					module_record.RestrictRingTwice.At(ring, A01, A1),
					module_record.RestrictRingTwice.At(ring, A01, k)))
			kernel := a.Have(
				"the second component is the kernel of ψ",
				"«secondPoint» = {x:A | x ∈ A₁ ∧ ψ(x) = L.zero}",
				By(psiParts[2], ring_homomorphism.RingKernelDef.At(a.TermAs[A]("L.zero"), A1, psi)))
			spanIdeal := a.Have(
				"the point spans an ideal of the overlap",
				"ring_ideal(«overlapRing», «spanned»)",
				By(members, ring_ideal.SpanIdeal.Read(overlapOn).At(m)))
			pointInSpan := a.Have(
				"which holds t − t₀ and z − z₀",
				"t - t₀ ∈ «spanned» ∧ z - z₀ ∈ «spanned»",
				BySets(tOnPoint, zOnPoint, ring_ideal.SpanContains.At(overlapRing, m)))

			// u, uᵇ and w lie in the second chart, and ψ takes them into k.
			secondRing := a.Have(
				"the second chart is a ring under the operations of L",
				"comm_ring_on(restrict_ring(field_ring(L), A₁))",
				By(secondSubring, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(A1)))
			lineRing := a.Have(
				"so is k[1/t]",
				"comm_ring_on(restrict_ring(field_ring(L), polynomial_image(field_ring(L), k, L.inv(t))))",
				By(lineData, comm_ring.SubringRingOn.Read(field.RingOn.Read(L)).At(line)))
			powerInLine := a.Have(
				"the b-th power of the inverse of t lies in k[1/t]",
				"«power» ∈ polynomial_image(field_ring(L), k, L.inv(t))",
				By(lineData, comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(lineRing)).AsFact().At(u, b)))
			powerIn := a.Have(
				"it lies in L",
				"«power» ∈ L.carrier",
				BySets(powerInLine, lineData, comm_ring.SubringSubset.At(ring, line)))
			scaledIn := a.Have(
				"and so does w",
				"«scaled» ∈ L.carrier",
				By(powerIn, members, comm_ring.MulIn.Read(field.RingOn.Read(L)).AsFact().At(power, z)))
			powerInField := a.Have(
				"the power and w lie in L",
				"«power» ∈ L.carrier ∧ «scaled» ∈ L.carrier",
				By(powerIn, scaledIn))
			wm := a.MemberOf[on.L](scaled, scaledIn)
			chartData := a.Have(
				"k[1/t][w] is a subring holding k[1/t] and w",
				"subring(field_ring(L), «secondChart») ∧ "+
					"polynomial_image(field_ring(L), k, L.inv(t)) ⊆ «secondChart» ∧ "+
					"«scaled» ∈ «secondChart»",
				By(lineData, algebraic_element.PolynomialImageSubring.Read(L).At(line, wm)))
			secondHolds := a.Have(
				"so the second chart holds the power and w",
				"«power» ∈ A₁ ∧ «scaled» ∈ A₁",
				BySets(secondReading, chartData, powerInLine))
			values := a.Have(
				"ψ takes the inverse of t, its power and w into k",
				"ψ(L.inv(t)) ∈ k ∧ ψ(«power») ∈ k ∧ ψ(«scaled») ∈ k",
				By(uInSecond, secondHolds, ring_homomorphism.MapIn.Read(homSecond)))
			valuesIn := a.Have(
				"so into the charts and L",
				"ψ(L.inv(t)) ∈ A₁ ∧ "+
					"ψ(«power») ∈ A₁ ∧ "+
					"ψ(L.inv(t)) ∈ L.carrier ∧ "+
					"ψ(«power») ∈ L.carrier ∧ "+
					"ψ(«scaled») ∈ L.carrier",
				BySets(values, kInSecond, secondInOverlap, members))

			// ψ(u) is the inverse of t₀: u·t₀ − 1 = −u·(t − t₀) lies in the span of the point.
			inverseValue := a.Have(
				"ψ(u) is the inverse of t₀",
				"ψ(L.inv(t)) * t₀ = L.one",
				Derive(func(c *Argument) {
					unitIn := c.Have(
						"u·t₀ and one lie in the second chart",
						"L.inv(t) * t₀ ∈ A₁ ∧ L.one ∈ A₁",
						By(
							secondSubring,
							uInSecond,
							members,
							comm_ring.SubringMul.At(ring, A1, u, t0),
							comm_ring.SubringOne.At(ring, A1)))
					unitDifferenceIn := c.Have(
						"so does u·t₀ − 1",
						"L.inv(t) * t₀ - L.one ∈ A₁",
						By(unitIn, comm_ring.SubIn.Read(secondRing)))
					minusU := c.Have(
						"minus the inverse of t lies in the overlap",
						"-L.inv(t) ∈ A₀₁",
						By(members, overlapSubring, comm_ring.SubringNeg.At(ring, A01, u)))
					unitDifference := c.Have(
						"u·t₀ − 1 is −u times t − t₀",
						"L.inv(t) * t₀ - L.one = -L.inv(t) * (t - t₀)",
						ByArith(L, unit, members, tIn))
					unitDifferenceInSpan := c.Have(
						"so it lies in the span of the point",
						"L.inv(t) * t₀ - L.one ∈ «spanned»",
						By(
							unitDifference,
							minusU,
							pointInSpan,
							spanIdeal,
							ring_ideal.IdealMul.At(overlapRing, spanned, c.TermAs[A]("-L.inv(t)"), c.TermAs[A]("t - t₀"))))
					unitKilled := c.Have(
						"and ψ kills it",
						"ψ(L.inv(t) * t₀ - L.one) = L.zero",
						BySets(kernel, unitDifferenceIn, unitDifferenceInSpan))
					unitMapped := c.Have(
						"ψ of it is ψ(u)·t₀ − 1",
						"ψ(L.inv(t) * t₀ - L.one) = ψ(L.inv(t)) * t₀ - L.one",
						By(
							unitIn,
							uInSecond,
							members,
							t0In,
							fixes.At(t0),
							ring_homomorphism.MapSub.Read(homSecond).AsFact().At(
								c.TermAs[A]("L.inv(t) * t₀"), c.TermAs[A]("L.one")),
							ring_homomorphism.MapMul.Read(homSecond).AsFact().At(u, t0),
							ring_homomorphism.MapOne.Read(homSecond)))
					c.Show(
						"so ψ(u)·t₀ − 1 is zero",
						ByArith(L, unitKilled, unitMapped, valuesIn, members))
				}))

			// uᵇ − ψ(uᵇ) is a multiple e of u − ψ(u), uᵇ lying in k[1/t].
			homChart := a.Have(
				"ψ is a ring map of k[1/t][w]",
				"ring_homomorphism(restrict_ring(field_ring(L), «secondChart»), "+
					"    restrict_ring(field_ring(L), k), "+
					"    ψ)",
				By(Normalized, homSecond, secondReading))
			principal := a.Have(
				"an element of k[1/t] less its value is a multiple of u − ψ(u)",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ polynomial_image(field_ring(L), k, L.inv(t))",
					},
					Conclusion: "∃e:A. e ∈ «secondChart» ∧ x - ψ(x) = (L.inv(t) - ψ(L.inv(t))) * e",
				},
				By(kSubfield, homChart, fixes, rational_point_ideal.MonogenicPointIdeal.Read(L).At(k, um, wm, psi)))
			e, eData := a.ObtainAs[A](
				"so is the power less its value",
				"∃e:A. e ∈ «secondChart» ∧ «power» - ψ(«power») = (L.inv(t) - ψ(L.inv(t))) * e",
				By(powerInLine, principal.At(power)),
				Named("e"))
			eParts := a.Conjuncts(
				eData,
				"e lies in the chart",
				"the power less its value is (u − ψ(u)) e")
			eIn := a.Have(
				"e lies in the second chart, the overlap and L",
				"e ∈ A₁ ∧ e ∈ A₀₁ ∧ e ∈ L.carrier",
				BySets(eParts[0], secondReading, secondInOverlap, members))

			// w − ψ(w) splits along z − z₀ and u − ψ(u): w less ψ(uᵇ)·z₀ lies in the span of the point.
			wSplit := a.Have(
				"w less its value splits along z − z₀ and u − ψ(u)",
				"«scaled» - ψ(«scaled») = «power» * (z - z₀) + z₀ * e * (L.inv(t) - ψ(L.inv(t)))",
				Derive(func(c *Argument) {
					wDifference := c.Have(
						"w less ψ(power)·z₀ splits along z − z₀ and u − ψ(u)",
						"«scaled» - ψ(«power») * z₀ = «power» * (z - z₀) + z₀ * e * (L.inv(t) - ψ(L.inv(t)))",
						ByArith(L, Scaled(z0, eParts[1]), members, valuesIn, eIn, powerInField))
					uDifferenceIn := c.Have(
						"u − ψ(u) lies in the second chart",
						"L.inv(t) - ψ(L.inv(t)) ∈ A₁",
						By(uInSecond, valuesIn, comm_ring.SubIn.Read(secondRing)))
					uDifferenceKilled := c.Have(
						"and ψ kills it, being a ring map onto k fixing k",
						"ψ(L.inv(t) - ψ(L.inv(t))) = L.zero",
						By(
							L,
							secondSubring,
							kInSecond,
							homSecond,
							fixes,
							uInSecond,
							rational_point_ideal.PointKillsDifference.At(ops, k, A1, psi, u)))
					uDifferenceInSpan := c.Have(
						"so it lies in the second component, inside the span of the point",
						"L.inv(t) - ψ(L.inv(t)) ∈ «spanned»",
						BySets(kernel, uDifferenceIn, uDifferenceKilled))
					powerOverlap := c.Have(
						"the power lies in the overlap",
						"«power» ∈ A₀₁",
						BySets(secondHolds, secondInOverlap))
					zDifferenceIn := c.Have(
						"z less z₀ lies in the overlap",
						"z - z₀ ∈ A₀₁ ∧ z₀ * e ∈ A₀₁",
						By(
							members,
							eIn,
							overlapOn,
							comm_ring.SubIn.Read(overlapOn).AsFact().At(z, z0),
							comm_ring.MulIn.Read(overlapOn).AsFact().At(z0, e)))
					wDifferenceInSpan := c.Have(
						"so w less ψ(power)·z₀ lies in the span of the point",
						"«scaled» - ψ(«power») * z₀ ∈ «spanned»",
						By(
							wDifference,
							powerOverlap,
							zDifferenceIn,
							pointInSpan,
							uDifferenceInSpan,
							spanIdeal,
							ring_ideal.IdealMul.At(overlapRing, spanned, power, c.TermAs[A]("z - z₀")),
							ring_ideal.IdealMul.At(
								overlapRing, spanned, c.TermAs[A]("z₀ * e"), c.TermAs[A]("L.inv(t) - ψ(L.inv(t))")),
							ring_ideal.IdealAdd.At(
								overlapRing,
								spanned,
								c.TermAs[A]("«power» * (z - z₀)"),
								c.TermAs[A]("z₀ * e * (L.inv(t) - ψ(L.inv(t)))"))))
					valueProduct := c.Have(
						"ψ(power)·z₀ lies in k",
						"ψ(«power») * z₀ ∈ k ∧ ψ(«power») * z₀ ∈ A₁",
						By(
							kSubfield,
							values,
							z0In,
							kInSecond,
							field.SubfieldMul.At(ops, k, c.TermAs[A]("ψ(«power»)"), z0),
							comm_ring.SubringMul.At(ring, A1, c.TermAs[A]("ψ(«power»)"), z0),
							valuesIn,
							members,
							secondSubring))
					wDifferenceIn := c.Have(
						"and in the second chart",
						"«scaled» - ψ(«power») * z₀ ∈ A₁",
						By(secondHolds, valueProduct, comm_ring.SubIn.Read(secondRing)))
					wKilled := c.Have(
						"so ψ kills it",
						"ψ(«scaled» - ψ(«power») * z₀) = L.zero",
						BySets(kernel, wDifferenceIn, wDifferenceInSpan))
					wValue := c.Have(
						"so ψ(w) is ψ(power)·z₀",
						"ψ(«scaled») = ψ(«power») * z₀",
						ByArith(
							L,
							wKilled,
							valuesIn,
							members,
							valueProduct,
							fixes.At(c.TermAs[A]("ψ(«power») * z₀")),
							ring_homomorphism.MapSub.Read(homSecond).AsFact().At(scaled, c.TermAs[A]("ψ(«power») * z₀")),
							secondHolds))
					c.Show(
						"so w less ψ(w) is the split of w less ψ(power)·z₀",
						ByArith(L, wDifference, wValue, valuesIn, members, eIn, powerInField))
				}))

			// A power of u clears g and h into the second chart, and the relation becomes one
			// between w − ψ(w) and u − ψ(u).
			n1, gCleared := a.UnpackAs[Nat](
				a.Have(
					"a power of u clears g into the second chart",
					"∃n:num. «uPow»(n) * g ∈ A₁",
					BySets(awayFromU, members, ring_away.RingAwayDef.At(overlapRing, A1, u))),
				"n₁")
			n2, hCleared := a.UnpackAs[Nat](
				a.Have(
					"and one clears h",
					"∃n:num. «uPow»(n) * h ∈ A₁",
					BySets(awayFromU, members, ring_away.RingAwayDef.At(overlapRing, A1, u))),
				"n₂")
			powersL := comm_ring.MulMonoidOn.Read(field.RingOn.Read(L))
			powers := a.Have(
				"the powers of t and of its inverse are inverse to each other and lie in L",
				"«tPow»(n₁) * «uPow»(n₁) = L.one ∧ "+
					"«tPow»(n₂) * «uPow»(n₂) = L.one ∧ "+
					"«tPow»(n₁) ∈ L.carrier ∧ "+
					"«tPow»(n₂) ∈ L.carrier ∧ "+
					"«uPow»(n₁) ∈ L.carrier ∧ "+
					"«uPow»(n₂) ∈ L.carrier ∧ "+
					"«uPow»(b - 1) ∈ L.carrier",
				By(
					unit,
					comm_monoid.PowInverseOn.Read(powersL).At(tm, um, n1),
					comm_monoid.PowInverseOn.Read(powersL).At(tm, um, n2),
					comm_monoid.PowIn.Read(powersL).At(tm, n1),
					comm_monoid.PowIn.Read(powersL).At(tm, n2),
					comm_monoid.PowIn.Read(powersL).At(um, n1),
					comm_monoid.PowIn.Read(powersL).At(um, n2),
					comm_monoid.PowIn.Read(powersL).At(um, a.TermAs[Nat]("b - 1"))))
			powerParts := a.Conjuncts(
				powers,
				"tⁿ¹ uⁿ¹ is one",
				"tⁿ² uⁿ² is one",
				"tⁿ¹ lies in L",
				"tⁿ² lies in L",
				"uⁿ¹ lies in L",
				"uⁿ² lies in L",
				"the lower power lies in L")
			secondPowers := comm_ring.MulMonoidOn.Read(secondRing)
			lowerIn := a.Have(
				"the powers of u lie in the second chart",
				"«uPow»(n₁) ∈ A₁ ∧ «uPow»(n₂) ∈ A₁ ∧ «uPow»(b - 1) ∈ A₁",
				By(
					uInSecond,
					comm_monoid.PowIn.Read(secondPowers).AsFact().At(u, n1),
					comm_monoid.PowIn.Read(secondPowers).AsFact().At(u, n2),
					comm_monoid.PowIn.Read(secondPowers).AsFact().At(u, a.TermAs[Nat]("b - 1"))))
			g1 := a.TermAs[A]("«cleared»(n₁, n₂)")
			clearedIn := a.Have(
				"so uⁿ¹⁺ⁿ²·g and uⁿ¹⁺ⁿ²·h lie in the second chart",
				"«cleared»(n₁, n₂) ∈ A₁ ∧ «uPow»(n₁) * («uPow»(n₂) * h) ∈ A₁",
				By(
					gCleared,
					hCleared,
					lowerIn,
					secondSubring,
					comm_ring.SubringMul.At(ring, A1, a.TermAs[A]("«uPow»(n₂)"), a.TermAs[A]("«uPow»(n₁) * g")),
					comm_ring.SubringMul.At(ring, A1, a.TermAs[A]("«uPow»(n₁)"), a.TermAs[A]("«uPow»(n₂) * h"))))
			h1 := a.TermAs[A]("«multiplier»(e, n₁, n₂)")
			h1In := a.Have(
				"the multiplier of u − ψ(u) lies in the second chart",
				"«multiplier»(e, n₁, n₂) ∈ A₁",
				By(
					members,
					lowerIn,
					clearedIn,
					eIn,
					secondRing,
					comm_ring.MulIn.Read(secondRing),
					comm_ring.AddIn.Read(secondRing),
					comm_ring.NegIn.Read(secondRing)))
			relation := a.Have(
				"so w − ψ(w) times the cleared g is u − ψ(u) times the multiplier",
				"(«scaled» - ψ(«scaled»)) * «cleared»(n₁, n₂) = (L.inv(t) - ψ(L.inv(t))) * «multiplier»(e, n₁, n₂)",
				Derive(func(c *Argument) {
					successor := c.Have(
						"b is a successor, being positive",
						"b = suc(b - 1)",
						ByArith(bPositive))
					powerSplit := c.Have(
						"the b-th power is u times the power below it",
						"«power» = L.inv(t) * «uPow»(b - 1)",
						By(successor, comm_monoid.MonoidPowDef))
					lower := c.TermAs[A]("«uPow»(b - 1)")
					tDifference := c.Have(
						"(t − t₀) times the power is −t₀ times the lower power times (u − ψ(u))",
						"(t - t₀) * «power» = -(L.inv(t) - ψ(L.inv(t))) * t₀ * «uPow»(b - 1)",
						ByArith(
							L,
							Scaled(t, powerSplit),
							Scaled(t0, powerSplit),
							Scaled(lower, unit),
							Scaled(lower, inverseValue),
							members,
							valuesIn,
							powers,
							tIn,
							powerInField))
					c.Show(
						"the relation times uᵇ·uⁿ¹⁺ⁿ², with w − ψ(w) split and t − t₀ read in u − ψ(u)",
						ByArith(
							L,
							Scaled(g1, wSplit),
							Scaled(c.TermAs[A]("«power» * «uPow»(n₂) * «uPow»(n₁)"), related),
							Scaled(c.TermAs[A]("«uPow»(n₂) * «uPow»(n₁) * h"), tDifference),
							members,
							valuesIn,
							powers,
							eIn,
							powerInField,
							tIn))
				}))

			// The cleared multiple of g lies off the point, so ψ does not kill it.
			clearedOff := a.Have(
				"the cleared multiple of g lies off the second component",
				"«cleared»(n₁, n₂) ∉ «secondPoint»",
				Derive(func(c *Argument) {
					inSecond := c.SupposeNot()
					tPowers := c.TermAs[A]("«tPow»(n₁) * «tPow»(n₂)")
					tPowersIn := c.Have(
						"the powers of t lie in the overlap",
						"«tPow»(n₁) * «tPow»(n₂) ∈ A₀₁",
						By(
							members,
							overlapOn,
							comm_ring.MulIn.Read(overlapOn).AsFact().At(c.TermAs[A]("«tPow»(n₁)"), c.TermAs[A]("«tPow»(n₂)")),
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(overlapOn)).AsFact().At(t, n1),
							comm_monoid.PowIn.Read(comm_ring.MulMonoidOn.Read(overlapOn)).AsFact().At(t, n2)))
					inSpan := c.Have(
						"it would lie in the span of the point",
						"«cleared»(n₁, n₂) ∈ «spanned»",
						BySets(inSecond))
					recovered := c.Have(
						"the powers of t carry it back to g",
						"«tPow»(n₁) * «tPow»(n₂) * «cleared»(n₁, n₂) = g",
						ByArith(
							L,
							Scaled(c.TermAs[A]("«tPow»(n₂) * «uPow»(n₂) * g"), powerParts[0]),
							Scaled(g, powerParts[1]),
							powers,
							members))
					gInSpan := c.Have(
						"so g would lie in the span of the point",
						"g ∈ «spanned»",
						By(
							Normalized,
							recovered,
							inSpan,
							tPowersIn,
							spanIdeal,
							ring_ideal.IdealMul.At(overlapRing, spanned, tPowers, g1)))
					c.Show(
						"and so on the point, which it is off",
						BySets(gIn, gInSpan, contracted, gOff))
				}))
			clearedValue := a.Have(
				"so ψ does not kill it",
				"ψ(«cleared»(n₁, n₂)) ≠ L.zero",
				BySets(kernel, clearedIn, clearedOff))

			// The Jacobian criterion on k[1/t][w], u lying off k.
			uOff := a.Have(
				"the inverse of t lies off k, being transcendental",
				"L.inv(t) ∉ k",
				Derive(func(c *Argument) {
					inK := c.SupposeNot()
					c.Show(
						"a member of k is algebraic over k",
						By(
							inverseTranscendental,
							kSubfield,
							inK,
							algebraic_element.MemberAlgebraic.Read(L).AsFact().At(k, u)))
				}))
			inChart := a.Have(
				"the cleared multiples lie in k[1/t][w]",
				"«cleared»(n₁, n₂) ∈ «secondChart» ∧ «multiplier»(e, n₁, n₂) ∈ «secondChart»",
				By(secondReading, clearedIn, h1In))
			invertible := a.Have(
				"the Jacobian criterion on k[1/t][w]",
				"invertible_fractional(field_ring(L), «secondChart», {x:A | x ∈ «secondChart» ∧ ψ(x) = L.zero})",
				By(
					kSubfield,
					uOff,
					homChart,
					fixes,
					inChart,
					clearedValue,
					relation,
					rational_point_ideal.MonogenicRelationInvertible.Read(L).At(k, um, wm, g1, h1, psi)))
			a.Show(
				"which is the second component on the second chart",
				By(invertible, secondReading, kernel))
		}),
})}

// PlaneRegularPointsFromBezout — an l-point φ of the extended first chart l[t][z]
// at which a(t) survives is a regular point of the extended plane model, and t
// less its value has order one there. The certificate U·F + V·F′ = a(t), read at
// z, makes F′(z) survive at φ, so dividing F by z − φ(z) relates the generators
// z − φ(z) and t − φ(t) of the point through a unit (SimpleRootRelation); the
// first chart's ideal is then invertible, the second's is the whole chart or,
// off t = 0, invertible by the same relation moved there (SecondChartRegular),
// and t − φ(t) generates the ideal of the local ring.
var PlaneRegularPointsFromBezout = planeRegularPointsFromBezoutThm{family.Add(registry.ProofEntry{
	Name: "PlaneRegularPointsFromBezout",
	Key:  "prop_889afaac0810388b",
	Build: family.Theorem(Statement{
		Abbrev: Abbrev{
			{Name: "point", Text: "{x:A | x ∈ «pmExtendedChart0» ∧ phi(x) = M.zero}"},
			{Name: "spanned", Text: "ideal_span(restrict_ring(field_ring(M), «pmExtendedOverlap»), «point»)"},
			{Name: "pair", Text: "(«point», «pmExtendedChart1» ∩ «spanned»)"},
			{Name: "planeChart", Text: "polynomial_image(field_ring(M), " +
				"    polynomial_image(field_ring(M), l, t), " +
				"    z)"},
			{Name: "overlapRing", Text: "restrict_ring(field_ring(«pmExtendedField»), «pmExtendedOverlap»)"},
			{Name: "kernel", Text: "λφ:(A → A). ring_kernel(«overlapRing».zero, «pmExtendedChart0», φ)"},
			{Name: "regularPoint", Text: "λφ:(A → A). " +
				"    («kernel»(φ), «pmExtendedChart1» ∩ ideal_span(«overlapRing», «kernel»(φ)))"},
		},
		Binders: "∀M:field_on(A). " +
			"∀K k:set(A). " +
			"∀t z:A. " +
			"∀F:(num → A). " +
			"∀b:num. " +
			"∀l:set(A). " +
			"∀a U V:(num → A). " +
			"∀phi:(A → A).",
		Hypotheses: []string{
			"subfield(M, K)",
			"integral_plane_model(restrict_field(M, K), k, t, z, F, b)",
			"subfield(M, l)",
			"k ⊆ l",
			"finite_extension(M, k, l)",
			"plane_good_certificate(«pmRing», k, t, F, a, U, V)",
			"phi ∈ " +
				"algebra_points(restrict_ring(field_ring(M), «pmExtendedChart0»), " +
				"    restrict_ring(field_ring(M), l), " +
				"    l, " +
				"    λx:A. x)",
			"phi(polynomial_eval(a, t)) ≠ M.zero",
		},
		Conclusion: "biaffine_regular_point(restrict_ring(field_ring(M), constant_composite(M, K, l)), " +
			"    l, " +
			"    «pmExtendedChart0», " +
			"    «pmExtendedChart1», " +
			"    «pmExtendedOverlap», " +
			"    «pair») ∧ " +
			"regular_point_order(restrict_ring(field_ring(M), constant_composite(M, K, l)), " +
			"    «pmExtendedChart0», " +
			"    «pmExtendedChart1», " +
			"    «pair», " +
			"    t - phi(t)) = " +
			"1",
	},
		func(
			arg *Argument,
			M field.FieldFact[on.M],
			K, k *Expr[Set[A]],
			t, z *Expr[A],
			F *Arrow[Nat, A],
			b *Expr[Nat],
			l *Expr[Set[A]],
			a, U, V *Arrow[Nat, A],
			phi *Arrow[A, A],
			subfieldK, model, lSubfield, kInL, finiteExtension, certificate, isPoint, valueSurvives Fact,
		) {
			m := arg.TermAs[FieldOps[A]]("M")
			fieldRing := arg.TermAs[RingOps[A]]("field_ring(M)")
			zero := arg.TermAs[A]("M.zero")
			extendedField := arg.TermAs[FieldOps[A]]("«pmExtendedField»")
			compositeRing := arg.TermAs[RingOps[A]]("field_ring(«pmExtendedField»)")
			composite := arg.TermAs[Set[A]]("constant_composite(M, K, l)")
			firstChart := arg.TermAs[Set[A]]("«pmExtendedChart0»")
			secondChart := arg.TermAs[Set[A]]("«pmExtendedChart1»")
			overlap := arg.TermAs[Set[A]]("«pmExtendedOverlap»")
			overlapRing := arg.TermAs[RingOps[A]]("«overlapRing»")
			point := arg.TermAs[Set[A]]("«point»")
			planeChart := arg.TermAs[Set[A]]("«planeChart»")
			kLine := arg.TermAs[Set[A]]("«pmPolynomials»")
			lLine := arg.TermAs[Set[A]]("polynomial_image(field_ring(M), l, t)")
			pair := arg.TermAs[Prod[Set[A], Set[A]]]("«pair»")

			// The model read in M: K regular over k, t and z in K, w = t^(-b)·z, and k[1/t].
			ambient := arg.Conjuncts(
				GroupPremises(subfieldK, model, PlaneModelInAmbient.Read(M).At(K, k, t, z, F, b)),
				"K is regular over k read in M",
				"k is a subfield of M",
				"k lies in K",
				"K lies in M",
				"t lies in K",
				"z lies in K",
				"t lies in M",
				"z lies in M",
				"t is transcendental over k",
				"z is algebraic over k(t)",
				"F is the minimal polynomial of z over k(t)",
				"t is not zero",
				"w lies in M",
				"k[1/t] is a subring of M",
				"inside k(t)",
				"z = t^b w")
			regular, kSubfield, tInK := ambient[0], ambient[1], ambient[4]
			tInM, zInM, kInverseLine := ambient[6], ambient[7], ambient[13]
			tm, zm := arg.MemberOf[on.M](t, tInM), arg.MemberOf[on.M](z, zInM)
			wm := arg.MemberOf[on.M](arg.TermAs[A]("«pmGenerator»"), ambient[12])
			weightPositive := arg.Have(
				"the weight b is positive",
				"0 < b",
				By(arg.Unfolded(model, IntegralPlaneModelDef)))

			// The extended first chart is l[t][z], and φ is a point of it fixing l.
			kLineData := arg.Have(
				"k[t] is a subring of M",
				"subring(field_ring(M), «pmPolynomials»)",
				By(kSubfield, algebraic_element.PolynomialImageRing.Read(M).At(k, tm)))
			lLineEq := arg.Have(
				"l[t] is the chart of k[t] over l",
				"polynomial_image(field_ring(M), l, t) = constant_chart(field_ring(M), l, «pmPolynomials»)",
				By(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					tInK,
					constant_field_extension.ConstantPolynomialChart.Read(M).At(K, k, l, t)))
			firstReading := arg.Have(
				"the extended first chart is l[t][z]",
				"«pmExtendedChart0» = «planeChart»",
				By(
					lSubfield,
					kLineData,
					lLineEq,
					PlaneChartsInAmbient.At(m, K, k, t, z, b),
					constant_field_extension.ConstantChartPolynomialImage.Read(M).At(l, kLine, zm)))
			pointParts := arg.Conjuncts(
				arg.Have(
					"φ is a ring map from the first chart onto l fixing l",
					"ring_homomorphism(restrict_ring(field_ring(M), «planeChart»), "+
						"    restrict_ring(field_ring(M), l), "+
						"    phi) ∧ "+
						"(∀c:A. c ∈ l ⇒ phi(c) = c)",
					By(
						isPoint,
						firstReading,
						algebra_points.AlgebraPointsMember.At(
							arg.TermAs[RingOps[A]]("restrict_ring(field_ring(M), «pmExtendedChart0»)"),
							arg.TermAs[RingOps[A]]("restrict_ring(field_ring(M), l)"),
							l,
							arg.TermAs[Fun[A, A]]("λx:A. x"),
							phi))),
				"φ is a ring map of l[t][z]",
				"fixing l")
			hom, fixes := pointParts[0], pointParts[1]
			equation := arg.Conjuncts(
				arg.Have(
					"F is monic over k[t] and vanishes at z",
					"polynomial_over(«pmPolynomials», F) ∧ polynomial_monic(F) ∧ polynomial_eval(F, z) = M.zero",
					By(subfieldK, model, PlaneModelRelation.Read(M).At(K, k, t, z, F, b))),
				"F is a polynomial over k[t]",
				"F is monic",
				"F vanishes at z")
			lLineData := arg.Have(
				"l[t] is a subring of M holding l and t, and k[t] lies in it",
				"subring(field_ring(M), polynomial_image(field_ring(M), l, t)) ∧ "+
					"l ⊆ polynomial_image(field_ring(M), l, t) ∧ "+
					"t ∈ polynomial_image(field_ring(M), l, t) ∧ "+
					"«pmPolynomials» ⊆ polynomial_image(field_ring(M), l, t)",
				By(
					lSubfield,
					kLineData,
					lLineEq,
					algebraic_element.PolynomialImageRing.Read(M).At(l, tm),
					constant_field_extension.ConstantChartSubring.Read(M).At(l, kLine)))
			chartData := arg.Have(
				"l[t][z] is a subring of M holding l[t] and z",
				"subring(field_ring(M), «planeChart») ∧ "+
					"polynomial_image(field_ring(M), l, t) ⊆ «planeChart» ∧ "+
					"z ∈ «planeChart»",
				By(lLineData, algebraic_element.PolynomialImageSubring.Read(M).At(lLine, zm)))
			chartRing := arg.Have(
				"l[t][z] is a ring under the operations of M",
				"comm_ring_on(restrict_ring(field_ring(M), «planeChart»))",
				By(chartData, comm_ring.SubringRingOn.Read(field.RingOn.Read(M)).At(planeChart)))
			FOverLine := arg.Have(
				"F is a polynomial over l[t]",
				"polynomial_over(polynomial_image(field_ring(M), l, t), F)",
				By(equation[0], lLineData, polynomial.PolynomialOverMono.At(zero, kLine, lLine, F)))

			// The certificate U·F + V·F′ = a(t), read at z where F vanishes, leaves
			// V(z)·F′(z) = a(t), so F′(z) survives at φ.
			certificateParts := arg.Conjuncts(
				arg.Unfolded(certificate, PlaneGoodCertificateDef),
				"a is a polynomial over k",
				"a is not zero",
				"U is a polynomial over k[t]",
				"V is a polynomial over k[t]",
				"U·F + V·F′ is the constant a(t)")
			kLineInChart := arg.Have(
				"k[t] lies in the chart",
				"polynomial_image(«pmRing», k, t) ⊆ «planeChart» ∧ "+
					"«pmPolynomials» ⊆ «planeChart» ∧ "+
					"«planeChart» ⊆ M.carrier",
				BySets(
					lLineData,
					chartData,
					field.RestrictFieldRing.At(m, K),
					algebraic_element.PolynomialsOverRestriction.At(m, K, k, t),
					comm_ring.SubringSubset.At(fieldRing, planeChart)))
			polynomials := arg.Have(
				"U, V, F and F′ are polynomials over the chart",
				"polynomial_over(«planeChart», U) ∧ "+
					"polynomial_over(«planeChart», V) ∧ "+
					"polynomial_over(«planeChart», F) ∧ "+
					"polynomial_over(«planeChart», polynomial_derivative(F))",
				By(
					certificateParts[2],
					certificateParts[3],
					equation[0],
					kLineInChart,
					chartRing,
					polynomial.PolynomialOverMono.At(
						zero, arg.TermAs[Set[A]]("polynomial_image(«pmRing», k, t)"), planeChart, U),
					polynomial.PolynomialOverMono.At(
						zero, arg.TermAs[Set[A]]("polynomial_image(«pmRing», k, t)"), planeChart, V),
					polynomial.PolynomialOverMono.At(zero, kLine, planeChart, F),
					polynomial.DerivativeOverCarrier.Read(chartRing).AsFact().At(F)))
			valueIn := arg.Have(
				"a(t) lies in k[t], so in the chart",
				"polynomial_eval(a, t) ∈ «planeChart» ∧ polynomial_eval(a, t) ∈ M.carrier",
				BySets(certificateParts[0], kLineInChart, algebraic_element.PolynomialImageDef.At(fieldRing, k, t)))
			productU := arg.TermAs[Fun[Nat, A]]("polynomial_mul(U, F)")
			productV := arg.TermAs[Fun[Nat, A]]("polynomial_mul(V, polynomial_derivative(F))")
			derivative := arg.TermAs[Fun[Nat, A]]("polynomial_derivative(F)")
			value := arg.TermAs[A]("polynomial_eval(a, t)")
			productsOver := arg.Have(
				"the two products are polynomials over the chart",
				"polynomial_over(«planeChart», polynomial_mul(U, F)) ∧ "+
					"polynomial_over(«planeChart», polynomial_mul(V, polynomial_derivative(F)))",
				By(
					polynomials,
					polynomial.PolynomialMulOver.Read(chartRing).AsFact().At(U, F),
					polynomial.PolynomialMulOver.Read(chartRing).AsFact().At(V, derivative)))
			atZ := arg.Have(
				"read at z, the left side is U(z)F(z) + V(z)F′(z)",
				"polynomial_eval(vec_add(polynomial_mul(U, F), polynomial_mul(V, polynomial_derivative(F))), "+
					"    z) = "+
					"polynomial_eval(U, z) * polynomial_eval(F, z) + "+
					"polynomial_eval(V, z) * polynomial_eval(polynomial_derivative(F), z)",
				By(
					polynomials,
					productsOver,
					chartData,
					polynomial_evaluation.EvalAdd.Read(chartRing).AsFact().At(productU, productV, z),
					polynomial_evaluation.EvalMul.Read(chartRing).AsFact().At(U, F, z),
					polynomial_evaluation.EvalMul.Read(chartRing).AsFact().At(V, derivative, z)))
			constantAtZ := arg.Have(
				"and the right side is a(t)",
				"polynomial_eval(vec_scalar_mul(polynomial_eval(a, t), basis_vector(0)), z) = "+
					"polynomial_eval(a, t)",
				By(valueIn, chartData, polynomial_evaluation.EvalConstant.Read(chartRing).AsFact().At(value, z)))
			evaluations := arg.Have(
				"U(z), V(z), F(z) and F′(z) lie in the chart",
				"polynomial_eval(U, z) ∈ «planeChart» ∧ "+
					"polynomial_eval(V, z) ∈ «planeChart» ∧ "+
					"polynomial_eval(F, z) ∈ «planeChart» ∧ "+
					"polynomial_eval(polynomial_derivative(F), z) ∈ «planeChart»",
				By(polynomials, chartData, polynomial_evaluation.EvalIn.Read(chartRing)))
			evaluationsInField := arg.Have(
				"so they lie in M",
				"polynomial_eval(U, z) ∈ M.carrier ∧ "+
					"polynomial_eval(V, z) ∈ M.carrier ∧ "+
					"polynomial_eval(F, z) ∈ M.carrier ∧ "+
					"polynomial_eval(polynomial_derivative(F), z) ∈ M.carrier",
				BySets(evaluations, kLineInChart))
			bezoutAtZ := arg.Have(
				"so U(z)F(z) + V(z)F′(z) = a(t)",
				"polynomial_eval(U, z) * polynomial_eval(F, z) + "+
					"polynomial_eval(V, z) * polynomial_eval(polynomial_derivative(F), z) = "+
					"polynomial_eval(a, t)",
				By(certificateParts[4], atZ, constantAtZ))
			bezout := arg.Have(
				"and F(z) = 0 leaves V(z)F′(z) = a(t)",
				"polynomial_eval(V, z) * polynomial_eval(polynomial_derivative(F), z) = polynomial_eval(a, t)",
				ByArith(M, bezoutAtZ, equation[2], evaluationsInField, valueIn))
			vz := arg.TermAs[A]("polynomial_eval(V, z)")
			derivativeZ := arg.TermAs[A]("polynomial_eval(polynomial_derivative(F), z)")
			images := arg.Have(
				"φ takes V(z) and F′(z) into l, so into M",
				"phi(polynomial_eval(V, z)) ∈ M.carrier ∧ "+
					"phi(polynomial_eval(polynomial_derivative(F), z)) ∈ M.carrier ∧ "+
					"phi(polynomial_eval(a, t)) ∈ M.carrier",
				BySets(
					ring_homomorphism.MapIn.Read(hom).AsFact().At(vz),
					ring_homomorphism.MapIn.Read(hom).AsFact().At(derivativeZ),
					ring_homomorphism.MapIn.Read(hom).AsFact().At(value),
					valueIn,
					evaluations,
					lSubfield,
					field.SubfieldSubset.At(m, l)))
			mappedBezout := arg.Have(
				"φ(a(t)) = φ(V(z))·φ(F′(z))",
				"phi(polynomial_eval(a, t)) = "+
					"phi(polynomial_eval(V, z)) * phi(polynomial_eval(polynomial_derivative(F), z))",
				By(bezout, evaluations, ring_homomorphism.MapMul.Read(hom).AsFact().At(vz, derivativeZ)))
			derivativeSurvives := arg.Have(
				"so F′(z) survives at φ, a(t) surviving",
				"phi(polynomial_eval(polynomial_derivative(F), z)) ≠ M.zero",
				Derive(func(c *Argument) {
					killed := c.SupposeNot()
					c.Show(
						"else φ(a(t)) would vanish",
						ByArith(M, mappedBezout, killed, images, valueSurvives))
				}))

			// Dividing F by z − φ(z) relates the generators z − φ(z) and t − φ(t) of the
			// point through g, with φ(g) ≠ 0; the two generate the point.
			g, h, related := arg.Obtain2As[A, A](
				"dividing F by z − φ(z) relates the two generators through g, with φ(g) = φ(F′(z))",
				"∃g h:A. "+
					"    g ∈ «planeChart» ∧ "+
					"    h ∈ «planeChart» ∧ "+
					"    phi(g) = phi(polynomial_eval(polynomial_derivative(F), z)) ∧ "+
					"    (z - phi(z)) * g = (t - phi(t)) * h",
				By(
					lSubfield,
					FOverLine,
					equation[2],
					hom,
					fixes,
					rational_point_ideal.SimpleRootRelation.Read(M).At(l, tm, zm, F, phi)),
				Named("g", "h"))
			relatedParts := arg.Conjuncts(
				related,
				"g lies in the chart",
				"h lies in the chart",
				"φ(g) is φ(F′(z))",
				"(z − φ(z))·g = (t − φ(t))·h")
			gSurvives := arg.Have(
				"so φ(g) is not zero",
				"phi(g) ≠ M.zero",
				By(relatedParts[2], derivativeSurvives))
			generated := arg.Have(
				"the point's ideal is generated by t − φ(t) and z − φ(z)",
				"«point» = ideal_span(restrict_ring(field_ring(M), «planeChart»), {t - phi(t), z - phi(z)})",
				By(
					lSubfield,
					hom,
					fixes,
					firstReading,
					rational_point_ideal.MonogenicPointIdeal.Read(M).At(l, tm, zm, phi)))

			// The extended charts are a curve over the line over l, and the Jacobian
			// criterion makes the point's ideal invertible in the first chart.
			compositeData := arg.Have(
				"the composite K(l) is a subfield of M holding K and l",
				"subfield(M, constant_composite(M, K, l)) ∧ "+
					"K ⊆ constant_composite(M, K, l) ∧ "+
					"l ⊆ constant_composite(M, K, l)",
				By(subfieldK, lSubfield, constant_composite.ConstantCompositeSubfield.Read(M).AsFact().At(K, l)))
			compositeFieldOn := arg.Have(
				"so a field under the operations of M",
				"field_on(«pmExtendedField»)",
				By(compositeData, field.SubfieldFieldOn.Read(M).At(composite)))
			curve := arg.Have(
				"the extended charts are a curve over the line over l",
				"curve_over_line(«pmExtendedField», "+
					"    l, "+
					"    t, "+
					"    «pmExtendedChart0», "+
					"    «pmExtendedChart1», "+
					"    «pmExtendedOverlap»)",
				By(
					subfieldK,
					model,
					lSubfield,
					kInL,
					finiteExtension,
					PlaneModelBaseChange.Read(M).At(K, k, t, z, F, b, l)))
			curveData := arg.Conjuncts(
				arg.Have(
					"what the extended curve gives",
					"subfield(«pmExtendedField», l) ∧ "+
						"¬algebraic_over(«pmExtendedField», l, t) ∧ "+
						"biaffine(«overlapRing», «pmExtendedChart0», «pmExtendedChart1», t, «pmExtendedField».inv(t)) ∧ "+
						"subring(field_ring(«pmExtendedField»), «pmExtendedChart0») ∧ "+
						"subring(field_ring(«pmExtendedField»), «pmExtendedChart1»)",
					By(
						curve,
						algebraic_curve.CurveOverItsLine.Read(compositeFieldOn).AsFact().At(
							l, firstChart, secondChart, overlap, t))),
				"l is a subfield of the composite",
				"t is transcendental over l",
				"the extended charts are biaffine in the overlap",
				"the first chart is a subring",
				"the second chart is a subring")
			lSubfieldInComposite, tTranscendental, biaffine, firstSubring, secondSubring :=
				curveData[0], curveData[1], curveData[2], curveData[3], curveData[4]
			inComposite := arg.Have(
				"t, z, g and h lie in the composite, and l in the first chart",
				"t ∈ constant_composite(M, K, l) ∧ "+
					"z ∈ constant_composite(M, K, l) ∧ "+
					"g ∈ constant_composite(M, K, l) ∧ "+
					"h ∈ constant_composite(M, K, l) ∧ "+
					"l ⊆ «pmExtendedChart0» ∧ "+
					"g ∈ «pmExtendedChart0» ∧ "+
					"h ∈ «pmExtendedChart0» ∧ "+
					"z ∈ «pmExtendedChart0»",
				BySets(
					relatedParts[0],
					relatedParts[1],
					firstReading,
					chartData,
					lLineData,
					firstSubring,
					comm_ring.SubringSubset.At(compositeRing, firstChart)))
			tOff := arg.Have(
				"t lies off l, being transcendental over it",
				"t ∉ l",
				Derive(func(c *Argument) {
					inL := c.SupposeNot()
					c.Show(
						"a member of l is algebraic over l",
						By(
							tTranscendental,
							lSubfieldInComposite,
							inL,
							algebraic_element.MemberAlgebraic.Read(compositeFieldOn).AsFact().At(l, t)))
				}))
			homInComposite := arg.Have(
				"φ read in the composite",
				"ring_homomorphism(restrict_ring(field_ring(«pmExtendedField»), "+
					"        polynomial_image(field_ring(«pmExtendedField»), "+
					"            polynomial_image(field_ring(«pmExtendedField»), l, t), "+
					"            z)), "+
					"    restrict_ring(field_ring(«pmExtendedField»), l), "+
					"    phi)",
				Simp(Fwd(field.RestrictFieldRecords), Fwd(algebraic_element.RestrictFieldReadings)),
				By(hom))
			chartInComposite := arg.Have(
				"g and h lie in l[t][z] read in the composite",
				"g ∈ "+
					"polynomial_image(field_ring(«pmExtendedField»), "+
					"    polynomial_image(field_ring(«pmExtendedField»), l, t), "+
					"    z) ∧ "+
					"h ∈ "+
					"polynomial_image(field_ring(«pmExtendedField»), "+
					"    polynomial_image(field_ring(«pmExtendedField»), l, t), "+
					"    z)",
				Simp(Fwd(algebraic_element.RestrictFieldReadings)),
				By(relatedParts[0], relatedParts[1]))
			firstInvertibleInComposite := arg.Have(
				"the Jacobian criterion on the first chart",
				"invertible_fractional(field_ring(«pmExtendedField»), "+
					"    polynomial_image(field_ring(«pmExtendedField»), "+
					"        polynomial_image(field_ring(«pmExtendedField»), l, t), "+
					"        z), "+
					"    {x:A | "+
					"        x ∈ "+
					"        polynomial_image(field_ring(«pmExtendedField»), "+
					"            polynomial_image(field_ring(«pmExtendedField»), l, t), "+
					"            z) ∧ "+
					"        phi(x) = «pmExtendedField».zero})",
				By(
					compositeFieldOn,
					lSubfieldInComposite,
					inComposite,
					tOff,
					homInComposite,
					fixes,
					chartInComposite,
					gSurvives,
					relatedParts[3],
					rational_point_ideal.MonogenicRelationInvertible.At(extendedField, l, t, z, g, h, phi)))
			firstInvertibleRead := arg.Simplified(
				firstInvertibleInComposite,
				Fwd(algebraic_element.RestrictFieldReadings))
			firstInvertible := arg.Have(
				"so the point's ideal is invertible in the first chart",
				"invertible_fractional(field_ring(«pmExtendedField»), «pmExtendedChart0», «point»)",
				By(firstInvertibleRead, firstReading))

			// The pair is a rational point on the first chart, the kernel of φ with its
			// contraction to the second chart.
			subfieldOverlap := arg.Have(
				"l is a subfield of the overlap ring",
				"ring_subfield(«overlapRing», «pmExtendedField».inv, l)",
				By(lSubfieldInComposite, field.SubfieldRingSubfield.Read(compositeFieldOn).AsFact().At(l, overlap)))
			homOverlap := arg.Have(
				"φ read in the overlap ring",
				"ring_homomorphism(restrict_ring(«overlapRing», «pmExtendedChart0»), "+
					"    restrict_ring(«overlapRing», l), "+
					"    phi)",
				Simp(Fwd(module_record.RestrictRingTwice), Fwd(field.RestrictFieldRecords)),
				By(hom, firstReading))
			lInSecond := arg.Have(
				"l lies in the second chart",
				"l ⊆ «pmExtendedChart1»",
				BySets(
					curve,
					algebraic_curve.CurveOverItsLine.Read(compositeFieldOn).AsFact().At(
						l, firstChart, secondChart, overlap, t)))
			pairForm := arg.Have(
				"the pair is the kernel of φ and its contraction to the second chart",
				"«pair» = «regularPoint»(phi)",
				Simp(Fwd(field.RestrictFieldRecords), Fwd(ring_homomorphism.RingKernelDef)),
				Basic())
			pointMap := arg.Have(
				"φ is a point of the first chart over l whose kernel and its contraction are the pair",
				"∃ψ:(A → A). "+
					"    ring_homomorphism(restrict_ring(«overlapRing», «pmExtendedChart0»), "+
					"        restrict_ring(«overlapRing», l), "+
					"        ψ) ∧ "+
					"    (∀c:A. c ∈ l ⇒ ψ(c) = c) ∧ "+
					"    «pair» = «regularPoint»(ψ)",
				Derive(func(c *Argument) {
					c.Take(phi)
					c.Show(
						"φ itself",
						By(homOverlap, fixes, pairForm))
				}))
			pointCriterion := arg.Have(
				"a pair is a rational point on the first chart exactly when "+
					"it is the kernel of a point over l with its contraction",
				"biaffine_rational_point(«overlapRing», l, «pmExtendedChart0», «pmExtendedChart1», «pair») ∧ "+
					"fst(«pair») ≠ «pmExtendedChart0» ⇔ "+
					"(∃ψ:(A → A). "+
					"    ring_homomorphism(restrict_ring(«overlapRing», «pmExtendedChart0»), "+
					"        restrict_ring(«overlapRing», l), "+
					"        ψ) ∧ "+
					"    (∀c:A. c ∈ l ⇒ ψ(c) = c) ∧ "+
					"    «pair» = «regularPoint»(ψ))",
				By(
					biaffine,
					subfieldOverlap,
					inComposite,
					lInSecond,
					biaffine_rational_point.RationalPointHomomorphism.At(
						overlapRing,
						firstChart,
						secondChart,
						t,
						arg.TermAs[A]("«pmExtendedField».inv(t)"),
						l,
						arg.TermAs[Fun[A, A]]("«pmExtendedField».inv"),
						pair)))
			rationalPoint := arg.Have(
				"so the pair is a rational point of the extended charts on the first chart",
				"biaffine_rational_point(«overlapRing», l, «pmExtendedChart0», «pmExtendedChart1», «pair») ∧ "+
					"fst(«pair») ≠ «pmExtendedChart0»",
				By(pointCriterion, pointMap))
			rationalClauses := arg.Conjuncts(
				arg.Unfolded(rationalPoint, biaffine_rational_point.BiaffineRationalPointDef),
				"the first component is the chart or a rational ideal of it",
				"the second component is the chart or a rational ideal of it",
				"the point lies on some chart",
				"the components span one ideal of the overlap",
				"a point on both charts is proper in the overlap",
				"the point lies on the first chart")
			projections := arg.Have(
				"the components of the pair",
				"fst(«pair») = «point» ∧ snd(«pair») = «pmExtendedChart1» ∩ «spanned»",
				By(
					pairs.Fst.At(point, arg.TermAs[Set[A]]("«pmExtendedChart1» ∩ «spanned»")),
					pairs.Snd.At(point, arg.TermAs[Set[A]]("«pmExtendedChart1» ∩ «spanned»"))))
			overlapClauses := arg.Have(
				"how the point meets t",
				"(fst(«pair») ≠ «pmExtendedChart0» ∧ snd(«pair») ≠ «pmExtendedChart1» ⇔ t ∉ fst(«pair»)) ∧ "+
					"(t ∉ fst(«pair») ⇒ fst(«pair») = «pmExtendedChart0» ∩ ideal_span(«overlapRing», fst(«pair»)))",
				By(
					biaffine,
					subfieldOverlap,
					inComposite,
					lInSecond,
					rationalPoint,
					biaffine_rational_point.RationalPointOverlap.At(
						overlapRing,
						firstChart,
						secondChart,
						t,
						arg.TermAs[A]("«pmExtendedField».inv(t)"),
						l,
						arg.TermAs[Fun[A, A]]("«pmExtendedField».inv"),
						pair)))
			overlapRead := arg.Simplified(overlapClauses, Fwd(pairs.Fst), Fwd(pairs.Snd))
			onFirst := arg.Have(
				"the point lies on the first chart",
				"«point» ≠ «pmExtendedChart0»",
				By(rationalPoint, projections))

			// Over t = 0 the second component is the whole second chart; elsewhere the
			// relation moves to the second chart l[1/t][t^(-b) z] (SecondChartRegular).
			pointIdeal := arg.Have(
				"the point is an ideal of the first chart",
				"ring_ideal(restrict_ring(field_ring(«pmExtendedField»), «pmExtendedChart0»), «point»)",
				Simp(Fwd(field.RestrictFieldRecords)),
				By(
					hom,
					firstReading,
					ring_homomorphism.RingKernelDef.At(zero, planeChart, phi),
					ring_homomorphism.KernelIdeal.Read(hom)))
			onPoint := arg.Have(
				"t − φ(t) and z − φ(z) lie on the point",
				"t - phi(t) ∈ «point» ∧ z - phi(z) ∈ «point»",
				BySets(
					generated,
					ring_ideal.SpanContains.At(
						arg.TermAs[RingOps[A]]("restrict_ring(field_ring(M), «planeChart»)"),
						arg.TermAs[Set[A]]("{t - phi(t), z - phi(z)}"))))
			gOff := arg.Have(
				"g lies off the point",
				"g ∉ «point»",
				By(gSurvives))
			coordinatesIn := arg.Have(
				"t and z lie in l[t][z]",
				"t ∈ «planeChart» ∧ z ∈ «planeChart»",
				BySets(lLineData, chartData))
			pointValues := arg.Have(
				"φ(t) and φ(z) lie in l",
				"phi(t) ∈ l ∧ phi(z) ∈ l",
				By(coordinatesIn, ring_homomorphism.MapIn.Read(hom)))
			recordsEq := arg.Have(
				"the overlap ring read in the composite is the overlap ring of M",
				"«overlapRing» = restrict_ring(field_ring(M), «pmExtendedOverlap»)",
				By(field.RestrictFieldRecords.At(m, composite, overlap)))
			inverseInK := arg.Have(
				"the inverse of t lies in K",
				"M.inv(t) ∈ K",
				By(subfieldK, tInK, field.SubfieldInv.At(m, K, t)))
			lInverseEq := arg.Have(
				"l[1/t] is the chart of k[1/t] over l",
				"polynomial_image(field_ring(M), l, M.inv(t)) = "+
					"constant_chart(field_ring(M), l, «pmInversePolynomials»)",
				By(
					regular,
					lSubfield,
					kInL,
					finiteExtension,
					inverseInK,
					constant_field_extension.ConstantPolynomialChart.Read(M).At(K, k, l, arg.TermAs[A]("M.inv(t)"))))
			secondReading := arg.Have(
				"the extended second chart is l[1/t][t^(-b) z]",
				"«pmExtendedChart1» = "+
					"polynomial_image(field_ring(M), polynomial_image(field_ring(M), l, M.inv(t)), «pmGenerator»)",
				By(
					lSubfield,
					kInverseLine,
					lInverseEq,
					PlaneChartsInAmbient.At(m, K, k, t, z, b),
					constant_field_extension.ConstantChartPolynomialImage.Read(M).At(
						l, arg.TermAs[Set[A]]("«pmInversePolynomials»"), wm)))
			secondInvertible := arg.Have(
				"the second component is invertible in the second chart",
				"invertible_fractional(field_ring(«pmExtendedField»), "+
					"    «pmExtendedChart1», "+
					"    «pmExtendedChart1» ∩ «spanned»)",
				Derive(func(c *Argument) {
					c.Cases(c.Term("phi(t) = M.zero"))
					c.When(
						"over t = 0 the point is off the second chart, whose component is the whole chart",
						func(d *Argument, atZero Fact) {
							tOnPoint := d.Have(
								"t lies on the point",
								"t ∈ «point»",
								BySets(atZero, coordinatesIn, firstReading))
							whole := d.Have(
								"so the second component is the second chart",
								"«pmExtendedChart1» ∩ «spanned» = «pmExtendedChart1»",
								By(tOnPoint, onFirst, overlapRead))
							d.Show(
								"which is invertible",
								By(
									whole,
									secondSubring,
									compositeFieldOn,
									fractional_ideal.SubringInvertible.Read(compositeFieldOn).AsFact().At(secondChart)))
						})
					c.Otherwise(
						"off t = 0 the relation moves to the second chart",
						func(d *Argument, offZero Fact) {
							tOffPoint := d.Have(
								"t lies off the point",
								"t ∉ «point»",
								BySets(offZero))
							contracted := d.Have(
								"the point is the contraction of its span in the overlap",
								"«point» = «pmExtendedChart0» ∩ ideal_span(«overlapRing», «point»)",
								By(tOffPoint, overlapRead))
							rationalSecond := d.Have(
								"so the second component is a rational ideal of the second chart",
								"rational_ideal(«overlapRing», "+
									"    l, "+
									"    «pmExtendedChart1», "+
									"    «pmExtendedChart1» ∩ ideal_span(«overlapRing», «point»))",
								By(tOffPoint, onFirst, overlapRead, rationalClauses[1], projections, recordsEq))
							secondReadingInComposite := d.Have(
								"the second chart is l[1/t][t^(-b) z]",
								"«pmExtendedChart1» = "+
									"polynomial_image(field_ring(«pmExtendedField»), "+
									"    polynomial_image(field_ring(«pmExtendedField»), l, «pmExtendedField».inv(t)), "+
									"    monoid_pow(«pmExtendedField».mul, «pmExtendedField».one, «pmExtendedField».inv(t), b) * z)",
								Simp(Fwd(algebraic_element.RestrictFieldReadings)),
								By(secondReading))
							secondInComposite := d.Have(
								"by the relation cleared into the second chart",
								"invertible_fractional(field_ring(«pmExtendedField»), "+
									"    «pmExtendedChart1», "+
									"    «pmExtendedChart1» ∩ ideal_span(«overlapRing», «point»))",
								By(
									compositeFieldOn,
									curve,
									secondReadingInComposite,
									weightPositive,
									pointValues,
									inComposite,
									pointIdeal,
									onPoint,
									gOff,
									contracted,
									relatedParts[3],
									rationalSecond,
									SecondChartRegular.At(
										extendedField,
										l,
										firstChart,
										secondChart,
										overlap,
										point,
										t,
										z,
										d.TermAs[A]("phi(t)"),
										d.TermAs[A]("phi(z)"),
										g,
										h,
										b)))
							d.Show(
								"read with the operations of M",
								By(secondInComposite, recordsEq))
						})
				}))

			// So the pair is an invertible lattice pair, and a regular point.
			componentsIn := arg.Have(
				"each component lies in its chart",
				"«point» ⊆ «pmExtendedChart0» ∧ «pmExtendedChart1» ∩ «spanned» ⊆ «pmExtendedChart1»",
				BySets())
			latticePair := arg.Have(
				"so the pair is an invertible lattice pair",
				"invertible_lattice_pair(field_ring(«pmExtendedField»), "+
					"    «pmExtendedChart0», "+
					"    «pmExtendedChart1», "+
					"    «pmExtendedOverlap», "+
					"    «pair»)",
				By(
					compositeFieldOn,
					curve,
					firstInvertible,
					secondInvertible,
					componentsIn,
					rationalClauses[3],
					projections,
					closed_divisor.ChartIdealsInvertiblePair.Read(compositeFieldOn).AsFact().At(
						l, firstChart, secondChart, overlap, t, pair)))
			regularPoint := arg.Have(
				"a rational point with an invertible pair is a regular point",
				"biaffine_regular_point(restrict_ring(field_ring(M), constant_composite(M, K, l)), "+
					"    l, "+
					"    «pmExtendedChart0», "+
					"    «pmExtendedChart1», "+
					"    «pmExtendedOverlap», "+
					"    «pair»)",
				By(
					rationalPoint,
					latticePair,
					field.RestrictFieldRing.At(m, composite),
					module_record.RestrictRingTwice.At(fieldRing, composite, overlap),
					field.RestrictFieldRecords,
					lattice_pair_twist.BiaffineRegularPointDef.At(
						arg.TermAs[RingOps[A]]("restrict_ring(field_ring(M), constant_composite(M, K, l))"),
						l,
						firstChart,
						secondChart,
						overlap,
						pair)))

			// t − φ(t) has order one: the point is a prime generated by t − φ(t) and
			// z − φ(z), the two related through g off the point.
			overlapData := arg.Have(
				"the overlap is a ring holding the first chart as a subring",
				"comm_ring_on(«overlapRing») ∧ subring(«overlapRing», «pmExtendedChart0»)",
				By(
					biaffine,
					lattice_pair.BiaffineDef.At(
						overlapRing, firstChart, secondChart, t, arg.TermAs[A]("«pmExtendedField».inv(t)"))))
			rationalFirst := arg.Have(
				"the point is a rational ideal of the first chart",
				"rational_ideal(«overlapRing», l, «pmExtendedChart0», «point»)",
				By(rationalClauses[0], onFirst, projections))
			maximal := arg.Have(
				"so a maximal ideal of it",
				"maximal_ideal(restrict_ring(field_ring(«pmExtendedField»), «pmExtendedChart0»), «point»)",
				By(
					overlapData,
					subfieldOverlap,
					inComposite,
					rationalFirst,
					module_record.RestrictRingTwice.At(compositeRing, overlap, firstChart),
					quotient_ring.FieldResiduesMaximal.At(
						overlapRing, l, arg.TermAs[Fun[A, A]]("«pmExtendedField».inv"), firstChart, point)))
			firstRingInComposite := arg.Have(
				"the first chart is a ring under the operations of the composite",
				"comm_ring_on(restrict_ring(field_ring(«pmExtendedField»), «pmExtendedChart0»))",
				By(
					firstSubring,
					comm_ring.SubringRingOn.Read(field.RingOn.Read(compositeFieldOn)).AsFact().At(firstChart)))
			prime := arg.Have(
				"so a prime",
				"prime_ideal(restrict_ring(field_ring(«pmExtendedField»), «pmExtendedChart0»), «point»)",
				By(maximal, ring_ideal.MaximalIsPrime.Read(firstRingInComposite).AsFact().At(point)))
			generatedInComposite := arg.Have(
				"generated by t − φ(t) and z − φ(z) in the first chart read in the composite",
				"«point» = "+
					"ideal_span(restrict_ring(field_ring(«pmExtendedField»), «pmExtendedChart0»), "+
					"    {t - phi(t), z - phi(z)})",
				Simp(Fwd(field.RestrictFieldRecords)),
				By(generated, firstReading))
			generatorsIn := arg.Have(
				"the generators lie in the first chart",
				"t - phi(t) ∈ «pmExtendedChart0» ∧ z - phi(z) ∈ «pmExtendedChart0»",
				BySets(onPoint))
			valuesInField := arg.Have(
				"φ(t) lies in M",
				"phi(t) ∈ M.carrier",
				BySets(pointValues, lSubfield, field.SubfieldSubset.At(m, l)))
			uNonzero := arg.Have(
				"t − φ(t) is not zero, t lying off l",
				"t - phi(t) ≠ M.zero",
				Derive(func(c *Argument) {
					same := c.SupposeNot()
					equal := c.Have(
						"t would be φ(t)",
						"t = phi(t)",
						ByArith(M, same, tInM, valuesInField))
					c.Show(
						"which lies in l",
						By(Normalized, equal, pointValues, tOff))
				}))
			orderFacts := arg.Have(
				"the first component is a prime generated by t − φ(t) and z − φ(z), off g",
				"prime_ideal(restrict_ring(field_ring(«pmExtendedField»), «pmExtendedChart0»), fst(«pair»)) ∧ "+
					"fst(«pair») = "+
					"ideal_span(restrict_ring(field_ring(«pmExtendedField»), «pmExtendedChart0»), "+
					"    {t - phi(t), z - phi(z)}) ∧ "+
					"g ∉ fst(«pair»)",
				Simp(Fwd(pairs.Fst)),
				By(prime, generatedInComposite, gOff))
			order := arg.Have(
				"t − φ(t) has order one, the other generator being a multiple of it by a unit",
				"regular_point_order(field_ring(«pmExtendedField»), "+
					"    «pmExtendedChart0», "+
					"    «pmExtendedChart1», "+
					"    «pair», "+
					"    t - phi(t)) = "+
					"1",
				By(
					compositeFieldOn,
					firstSubring,
					orderFacts,
					generatorsIn,
					uNonzero,
					inComposite,
					relatedParts[3],
					divisor_lattice_correspondence.GeneratorOrderOne.At(
						extendedField,
						firstChart,
						secondChart,
						pair,
						arg.TermAs[A]("t - phi(t)"),
						arg.TermAs[A]("z - phi(z)"),
						g,
						h)))
			arg.Show(
				"a regular point at which t − φ(t) has order one",
				By(regularPoint, order, field.RestrictFieldRing.At(m, composite)))
		}),
})}
