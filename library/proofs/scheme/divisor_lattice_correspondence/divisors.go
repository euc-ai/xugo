// divisors.go — the correspondence between closed divisors and invertible pairs.
// Every invertible pair is the pair of exactly one closed divisor, principal
// divisors are the scalings of the structure pair, of degree zero, and the
// coefficient of div f at a closed point is the order of f there.

package divisor_lattice_correspondence

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/regular_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// InvertiblePairLaws — the laws of the invertible pairs of L: the structure pair
// is invertible; an invertible pair lies in L and has an inverse, which is
// invertible and whose inverse is the pair; and a nonzero member of L scales an
// invertible pair to an invertible pair, its inverse undoing the scaling, and
// comes out of a product.
var InvertiblePairLaws = invertiblePairLawsThm{family.Add(registry.ProofEntry{
	Name: "InvertiblePairLaws",
	Key:  "prop_3a2fd9bc5344b91b",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{"«scCurve»"},
		Conclusion: "«scInvertible»((A₀, A₁)) ∧ " +
			"(∀X:prod(set(A), set(A)). " +
			"    «scInvertible»(X) ⇒ " +
			"    fst(X) ⊆ L.carrier ∧ " +
			"    snd(X) ⊆ L.carrier ∧ " +
			"    «scInvertible»(«scInverse»(X)) ∧ " +
			"    «scMul»(X, «scInverse»(X)) = (A₀, A₁) ∧ " +
			"    «scInverse»(«scInverse»(X)) = X) ∧ " +
			"(∀a:A. ∀X:prod(set(A), set(A)). " +
			"    a ∈ L.carrier ∧ a ≠ L.zero ∧ «scInvertible»(X) ⇒ " +
			"    «scInvertible»(lattice_pair_scale(a, X)) ∧ " +
			"    lattice_pair_scale(L.inv(a), lattice_pair_scale(a, X)) = X ∧ " +
			"    (∀Y:prod(set(A), set(A)). " +
			"        «scInvertible»(Y) ⇒ " +
			"        «scMul»(lattice_pair_scale(a, X), Y) = lattice_pair_scale(a, «scMul»(X, Y))))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
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
			overlapInL, biaffine := data[0], data[1]
			inverse := a.Have(
				"an invertible pair lies in L and has its inverse",
				Statement{
					Binders:    "∀X:prod(set(A), set(A)).",
					Hypotheses: []string{"«scInvertible»(X)"},
					Conclusion: "fst(X) ⊆ L.carrier ∧ " +
						"snd(X) ⊆ L.carrier ∧ " +
						"«scInvertible»(«scInverse»(X)) ∧ " +
						"«scMul»(X, «scInverse»(X)) = (A₀, A₁) ∧ " +
						"«scInverse»(«scInverse»(X)) = X",
				},
				Derive(func(b *Argument) {
					X := b.FixAs[_IdealPair]("X")
					invertible := b.Assume()
					b.Show(
						"the laws of the invertible pairs of L",
						By(
							invertible,
							overlapInL,
							biaffine,
							invertible_lattice_pair.InvertibleChartsInField.Read(L).At(A0, A1, A01, X),
							invertible_lattice_pair.InvertibleLatticeInverse.Read(L).At(A0, A1, A01, t, X)))
				}))
			scaled := a.Have(
				"a nonzero member of L scales an invertible pair",
				Statement{
					Binders:    "∀a:A. ∀X:prod(set(A), set(A)).",
					Hypotheses: []string{"a ∈ L.carrier ∧ a ≠ L.zero ∧ «scInvertible»(X)"},
					Conclusion: "«scInvertible»(lattice_pair_scale(a, X)) ∧ " +
						"lattice_pair_scale(L.inv(a), lattice_pair_scale(a, X)) = X ∧ " +
						"(∀Y:prod(set(A), set(A)). " +
						"    «scInvertible»(Y) ⇒ " +
						"    «scMul»(lattice_pair_scale(a, X), Y) = lattice_pair_scale(a, «scMul»(X, Y)))",
				},
				Derive(func(b *Argument) {
					s := b.FixAs[A]("a")
					X := b.FixAs[_IdealPair]("X")
					given := b.Conjuncts(
						b.Assume(),
						"a lies in L",
						"a is not zero",
						"X is invertible")
					member := b.MemberOf[on.L](s, given[0])
					inL := b.Conjuncts(
						GroupPremises(given[2], inverse.At(X)),
						"fst(X) lies in L",
						"snd(X) lies in L",
						"the inverse of X is invertible",
						"X times its inverse is the structure pair",
						"and its inverse is X")
					invertible := b.Have(
						"a · X is invertible",
						"«scInvertible»(lattice_pair_scale(a, X))",
						By(
							overlapInL,
							biaffine,
							given[1],
							given[2],
							inL[0],
							inL[1],
							invertible_lattice_pair.InvertibleLatticeScale.Read(L).At(A0, A1, A01, t, member, X)))
					undone := b.Have(
						"dividing a · X by a gives X, its charts lying in L",
						"lattice_pair_scale(L.inv(a), lattice_pair_scale(a, X)) = X",
						By(given[1], inL[0], inL[1], invertible_lattice_pair.ScaleCancel.Read(L).At(member, X)))
					outOfProducts := b.Have(
						"a comes out of a product with an invertible pair",
						Statement{
							Binders:    "∀Y:prod(set(A), set(A)).",
							Hypotheses: []string{"«scInvertible»(Y)"},
							Conclusion: "«scMul»(lattice_pair_scale(a, X), Y) = lattice_pair_scale(a, «scMul»(X, Y))",
						},
						Derive(func(c *Argument) {
							Y := c.FixAs[_IdealPair]("Y")
							invertibleY := c.Assume()
							inLY := c.Conjuncts(
								GroupPremises(invertibleY, inverse.At(Y)),
								"fst(Y) lies in L",
								"snd(Y) lies in L",
								"the inverse of Y is invertible",
								"Y times its inverse is the structure pair",
								"and its inverse is Y")
							c.Show(
								"the law on the two charts",
								By(
									invertibleY,
									overlapInL,
									biaffine,
									inL[0],
									inL[1],
									inLY[0],
									inLY[1],
									invertible_lattice_pair.ScaleMulAssoc.Read(L).At(A0, A1, A01, t, member, X, Y)))
						}))
					b.Show(
						"a · X is invertible, a⁻¹ undoes the scaling, and a comes out of products",
						By(invertible, undone, outOfProducts))
				}))
			a.Show(
				"the structure pair, the inverses and the scaling",
				By(data[5], inverse, scaled))
		}),
})}

// ChartMeetInvertible — the part of an invertible fractional ideal inside its
// chart is invertible: it is an ideal of the chart, and a nonzero one, the
// fractional ideal holding a nonzero multiple of the whole chart.
var ChartMeetInvertible = chartMeetInvertibleThm{family.Add(registry.ProofEntry{
	Name: "ChartMeetInvertible",
	Key:  "prop_79fed01af2b684b4",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀J:set(A).",
		Hypotheses: []string{"«scCurve»", "invertible_fractional(field_ring(L), A₀, J)"},
		Conclusion: "invertible_fractional(field_ring(L), A₀, J ∩ A₀)",
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
			chart := a.TermAs[RingOps[A]]("restrict_ring(field_ring(L), A₀)")
			vectors := a.TermAs[module_record.ModuleOps[A, A]]("regular_module(field_ring(L))")
			meet := a.TermAs[Set[A]]("J ∩ A₀")
			subring := a.Have(
				"the chart is a subring of L",
				"subring(field_ring(L), A₀)",
				By(
					curve,
					smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			inChart := a.Have(
				"J ∩ A₀ lies in the chart",
				"J ∩ A₀ ⊆ A₀",
				BySets())
			ideal := a.Have(
				"J ∩ A₀ is an ideal of the chart: the meet of two modules over it, inside it",
				"ring_ideal(restrict_ring(field_ring(L), A₀), J ∩ A₀)",
				By(
					subring,
					invertible,
					inChart,
					fractional_ideal.InvertibleFractionalDef.At(ring, A0, J),
					fractional_ideal.SubringSubmodule.Read(L).At(A0),
					submodule.SubmoduleInter.At(chart, vectors, J, A0),
					fractional_ideal.IntegralIdealFractional.Read(L).At(A0, meet)))
			_, member := a.UnpackAs[A](GroupPremises(
				curve, invertible, closed_divisor.InvertibleChartMember.Read(L).At(k, A0, A1, A01, t, J)))
			nonzero := a.Have(
				"J holds a nonzero member of the chart, so J ∩ A₀ is not the zero ideal",
				"J ∩ A₀ ≠ {L.zero}",
				BySets(member))
			a.Show(
				"a nonzero ideal of a chart is invertible",
				By(ideal, nonzero, curve, smooth_curve.ChartIdealInvertible.Read(L).At(k, A0, A1, A01, t, meet)))
		}),
})}

// InvertibleMeetInvertible — the meet of an invertible pair with the structure
// pair is invertible: each component is the part of an invertible fractional
// ideal inside its chart, the second read through the swap, and the meet of two
// lattice pairs is a lattice pair.
var InvertibleMeetInvertible = invertibleMeetInvertibleThm{family.Add(registry.ProofEntry{
	Name: "InvertibleMeetInvertible",
	Key:  "prop_8fd59dc0a56ac061",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀W:prod(set(A), set(A)).",
		Hypotheses: []string{"«scCurve»", "«scInvertible»(W)"},
		Conclusion: "«scInvertible»((fst(W) ∩ A₀, snd(W) ∩ A₁))",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			W *Expr[_IdealPair],
			curve, invertible Fact,
		) {
			overLine := a.Have(
				"the curve lies over the line of t",
				"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
				By(curve, smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t)))
			lattice := a.Conjuncts(
				GroupPremises(
					invertible, overLine, algebraic_curve.InvertibleMeetStructure.Read(L).At(k, A0, A1, A01, t, W)),
				"the meet is a lattice pair",
				"chart 0 modulo the meet is finite",
				"chart 1 modulo the meet is finite",
				"fst(W) modulo the meet is finite",
				"snd(W) modulo the meet is finite")[0]
			components := a.Conjuncts(
				a.Unfolded(invertible, invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(W) is invertible",
				"snd(W) is invertible",
				"W is a lattice pair")
			first := a.Have(
				"the part of fst(W) in chart 0 is invertible",
				"invertible_fractional(field_ring(L), A₀, fst(W) ∩ A₀)",
				By(
					curve,
					components[0],
					ChartMeetInvertible.Read(L).At(k, A0, A1, A01, t, a.TermAs[Set[A]]("fst(W)"))))
			second := a.Have(
				"and the part of snd(W) in chart 1, read from the other chart",
				"invertible_fractional(field_ring(L), A₁, snd(W) ∩ A₁)",
				By(
					curve,
					components[1],
					smooth_curve.SmoothCurveSwap.Read(L).At(k, A0, A1, A01, t),
					ChartMeetInvertible.Read(L).At(
						k, A1, A0, A01, a.TermAs[A]("L.inv(t)"), a.TermAs[Set[A]]("snd(W)"))))
			a.Show(
				"the two invertible components of a lattice pair",
				Unfold(invertible_lattice_pair.InvertibleLatticePairDef),
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(first, second, lattice))
		}),
})}

// ClosedDivisorPairInjective — a closed divisor is determined by its pair: adding
// |D| + |E| to D and to E gives two effective divisors whose ideal pairs agree,
// and the factorization of an integral pair is unique.
var ClosedDivisorPairInjective = closedDivisorPairInjectiveThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorPairInjective",
	Key:  "prop_935721502d63501a",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D E:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«scCurve»",
			"«scDivisor»(D)",
			"«scDivisor»(E)",
			"«scPair»(D) = «scPair»(E)",
		},
		Conclusion: "D = E",
		Abbrev: Abbrev{
			{Name: "shift", Text: "λP:prod(set(A), set(A)). |D(P)| + |E(P)|"},
			{Name: "raisedD", Text: "λP:prod(set(A), set(A)). D(P) + «shift»(P)"},
			{Name: "raisedE", Text: "λP:prod(set(A), set(A)). E(P) + «shift»(P)"},
			{Name: "idealD", Text: "«scPair»(λP:prod(set(A), set(A)). -«raisedD»(P))"},
			{Name: "idealE", Text: "«scPair»(λP:prod(set(A), set(A)). -«raisedE»(P))"},
			{Name: "supports", Text: "fun_support(int_of_num(0), D) ∪ fun_support(int_of_num(0), E)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D, E *Arrow[_IdealPair, Int],
			curve, divisorD, divisorE, same Fact,
		) {
			supportedD := a.Conjuncts(
				a.Unfolded(divisorD, closed_divisor.ClosedDivisorDef),
				"the support of D is finite",
				"its pairs are closed points")
			supportedE := a.Conjuncts(
				a.Unfolded(divisorE, closed_divisor.ClosedDivisorDef),
				"the support of E is finite",
				"its pairs are closed points")
			shift := a.TermAs[Fun[_IdealPair, Int]]("«shift»")
			raisedD := a.TermAs[Fun[_IdealPair, Int]]("«raisedD»")
			raisedE := a.TermAs[Fun[_IdealPair, Int]]("«raisedE»")
			vanishing := a.Have(
				"where |D| + |E| is not zero, D or E is not zero",
				Statement{
					Binders: "∀P:prod(set(A), set(A)).",
					Hypotheses: []string{
						"|D(P)| + |E(P)| ≠ int_of_num(0)",
					},
					Conclusion: "D(P) ≠ int_of_num(0) ∨ E(P) ≠ int_of_num(0)",
				},
				a.ForEach(func(P *Expr[_IdealPair]) Action { return ByArith() }))
			inSupports := a.Have(
				"so its support lies in the two supports",
				"∀P:prod(set(A), set(A)). |D(P)| + |E(P)| ≠ int_of_num(0) ⇒ P ∈ «supports»",
				a.ForEach(func(P *Expr[_IdealPair]) Action { return BySets(vanishing.At(P)) }))
			closedPoints := a.Have(
				"and the pairs of the two supports are closed points",
				"∀P:prod(set(A), set(A)). P ∈ «supports» ⇒ «scPoint»(P)",
				a.ForEach(func(P *Expr[_IdealPair]) Action {
					return BySets(supportedD[1].At(P), supportedE[1].At(P))
				}))
			absoluteSum := a.Have(
				"so |D| + |E|, supported in the two supports, is a closed divisor",
				"«scDivisor»(«shift»)",
				By(
					supportedD[0],
					supportedE[0],
					closedPoints,
					inSupports,
					finite_set.FiniteUnion.At(
						a.TermAs[Set[_IdealPair]]("fun_support(int_of_num(0), D)"),
						a.TermAs[Set[_IdealPair]]("fun_support(int_of_num(0), E)")),
					closed_divisor.ClosedDivisorOfSupport.At(
						a.TermAs[RingOps[A]]("field_ring(L)"),
						A0,
						A1,
						A01,
						a.TermAs[Set[_IdealPair]]("«supports»"),
						shift)))
			addD := a.Conjuncts(
				GroupPremises(
					curve,
					divisorD,
					absoluteSum,
					closed_divisor.ClosedDivisorAdd.Read(L).At(k, A0, A1, A01, t, D, shift)),
				"D raised is a closed divisor",
				"its pair is the product of the pairs",
				"its degree is the sum of the degrees")
			addE := a.Conjuncts(
				GroupPremises(
					curve,
					divisorE,
					absoluteSum,
					closed_divisor.ClosedDivisorAdd.Read(L).At(k, A0, A1, A01, t, E, shift)),
				"E raised is a closed divisor",
				"its pair is the product of the pairs",
				"its degree is the sum of the degrees")
			negatedD := a.Conjuncts(
				GroupPremises(
					curve, addD[0], closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, raisedD)),
				"its negative is a closed divisor",
				"its pair is invertible",
				"the pair of the negative is the inverse",
				"its degree is the negative degree")
			negatedE := a.Conjuncts(
				GroupPremises(
					addE[0], curve, closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, raisedE)),
				"its negative is a closed divisor",
				"its pair is invertible",
				"the pair of the negative is the inverse",
				"its degree is the negative degree")
			ideals := a.Have(
				"the ideal pairs of the two agree",
				"«idealD» = «idealE»",
				By(same, addD[1], addE[1], negatedD[2], negatedE[2]))
			effectiveD := a.Have(
				"D raised is effective",
				"∀P:prod(set(A), set(A)). int_of_num(0) ≤ «raisedD»(P)",
				a.ForEach(func(P *Expr[_IdealPair]) Action { return ByArith() }))
			effectiveE := a.Have(
				"and so is E raised",
				"∀P:prod(set(A), set(A)). int_of_num(0) ≤ «raisedE»(P)",
				a.ForEach(func(P *Expr[_IdealPair]) Action { return ByArith() }))
			integral := a.Conjuncts(
				GroupPremises(
					curve,
					addE[0],
					effectiveE,
					closed_divisor.EffectivePairIntegral.Read(L).At(k, A0, A1, A01, t, raisedE)),
				"the ideal pair of E raised is invertible",
				"inside chart 0",
				"and chart 1")
			unique := a.Have(
				"so it is the ideal pair of one effective divisor",
				"∃!C:(prod(set(A), set(A)) → int). "+
					"    «scDivisor»(C) ∧ "+
					"    (∀P:prod(set(A), set(A)). int_of_num(0) ≤ C(P)) ∧ "+
					"    «idealE» = «scPair»(λP:prod(set(A), set(A)). -C(P))",
				By(
					curve,
					integral[0],
					integral[1],
					integral[2],
					closed_divisor.IntegralPairHasDivisor.Read(L).At(
						k, A0, A1, A01, t, a.TermAs[_IdealPair]("«idealE»"))))
			_, center := a.UnpackAs[Fun[_IdealPair, Int]](unique, "C")
			raised := a.Have(
				"so D raised and E raised are one divisor",
				"«raisedD» = «raisedE»",
				By(addD[0], addE[0], effectiveD, effectiveE, ideals, center.At(raisedD), center.At(raisedE)))
			a.Do(Funext())
			a.FixAs[_IdealPair]("P")
			atPoint := a.Have(
				"at P the two raised divisors agree",
				"«raisedD»(P) = «raisedE»(P)",
				By(raised))
			a.Show(
				"the common shift cancels",
				ByArith(atPoint))
		}),
})}

// InvertiblePairHasDivisor — every invertible pair is the pair of exactly one
// closed divisor. Meeting X⁻¹ with the structure pair gives an invertible pair Z
// inside the charts and X · Z lies inside them too, so both are ideal pairs; X is
// their quotient.
var InvertiblePairHasDivisor = invertiblePairHasDivisorThm{family.Add(registry.ProofEntry{
	Name: "InvertiblePairHasDivisor",
	Key:  "prop_1dd47819b4603a1c",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀X:prod(set(A), set(A)).",
		Hypotheses: []string{"«scCurve»", "«scInvertible»(X)"},
		Conclusion: "∃!D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scPair»(D) = X",
		Abbrev: Abbrev{
			{Name: "meet", Text: "(fst(«scInverse»(X)) ∩ A₀, snd(«scInverse»(X)) ∩ A₁)"},
			{Name: "product", Text: "«scMul»(X, «meet»)"},
			{Name: "quotient", Text: "λP:prod(set(A), set(A)). -D₁(P) + D₂(P)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X *Expr[_IdealPair],
			curve, invertible Fact,
		) {
			meet := a.TermAs[_IdealPair]("«meet»")
			product := a.TermAs[_IdealPair]("«product»")
			first, second := a.TermAs[Set[A]]("fst(X)"), a.TermAs[Set[A]]("snd(X)")
			laws := a.Conjuncts(
				GroupPremises(curve, InvertiblePairLaws.Read(L).At(k, A0, A1, A01, t)),
				"the structure pair is invertible",
				"the inverse of an invertible pair",
				"scaling an invertible pair")
			inverse := a.Conjuncts(
				GroupPremises(invertible, laws[1].At(X)),
				"fst(X) lies in L",
				"snd(X) lies in L",
				"the inverse of X is invertible",
				"X times its inverse is the structure pair",
				"and its inverse is X")
			invertibleMeet := a.Have(
				"the meet of X⁻¹ with the structure pair is invertible",
				"«scInvertible»(«meet»)",
				By(
					curve,
					inverse[2],
					InvertibleMeetInvertible.Read(L).At(k, A0, A1, A01, t, a.TermAs[_IdealPair]("«scInverse»(X)"))))
			meetInCharts := a.Have(
				"and lies inside the charts",
				"fst(«meet») ⊆ A₀ ∧ snd(«meet») ⊆ A₁",
				Simp(Fwd(pairs.Fst), Fwd(pairs.Snd)),
				BySets())
			quotient := a.Conjuncts(
				GroupPremises(
					curve,
					invertible,
					invertibleMeet,
					closed_divisor.PairQuotient.Read(L).At(k, A0, A1, A01, t, X, meet)),
				"the product of X and the inverse of the meet is invertible",
				"and multiplies back to X",
				"X times the meet, over the meet, is X")
			products := a.Conjuncts(
				GroupPremises(curve, closed_divisor.ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")
			invertibleProduct := a.Have(
				"so X times the meet is invertible",
				"«scInvertible»(«product»)",
				BySets(invertible, invertibleMeet, comm_monoid.OpIn.Read(products[0]).AsFact().At(X, meet)))
			unit := a.Conjuncts(
				a.Simplified(
					inverse[3],
					Fwd(invertible_lattice_pair.LatticePairMulDef),
					Fwd(invertible_lattice_pair.LatticePairInverseDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd),
					Fwd(pairs.PairEq)),
				"on chart 0 X and its inverse multiply to the chart",
				"on chart 1 likewise")
			below := a.Have(
				"the two components of the meet lie in those of X⁻¹",
				"fractional_inverse(field_ring(L), A₀, fst(X)) ∩ A₀ ⊆ "+
					"fractional_inverse(field_ring(L), A₀, fst(X)) ∧ "+
					"fractional_inverse(field_ring(L), A₁, snd(X)) ∩ A₁ ⊆ "+
					"fractional_inverse(field_ring(L), A₁, snd(X))",
				BySets())
			productInCharts := a.Have(
				"and lies inside the charts, under X · X⁻¹",
				"fst(«product») ⊆ A₀ ∧ snd(«product») ⊆ A₁",
				Simp(
					Fwd(invertible_lattice_pair.LatticePairMulDef),
					Fwd(invertible_lattice_pair.LatticePairInverseDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				By(
					unit[0],
					unit[1],
					set_order.SubsetRefl,
					below,
					fractional_ideal.FractionalMulMono.Read(L).At(
						A0,
						first,
						first,
						a.TermAs[Set[A]]("fractional_inverse(field_ring(L), A₀, fst(X)) ∩ A₀"),
						a.TermAs[Set[A]]("fractional_inverse(field_ring(L), A₀, fst(X))")),
					fractional_ideal.FractionalMulMono.Read(L).At(
						A1,
						second,
						second,
						a.TermAs[Set[A]]("fractional_inverse(field_ring(L), A₁, snd(X)) ∩ A₁"),
						a.TermAs[Set[A]]("fractional_inverse(field_ring(L), A₁, snd(X))"))))
			factorProduct := a.Have(
				"X times the meet is an ideal pair",
				"∃!D₁:(prod(set(A), set(A)) → int). "+
					"    «scDivisor»(D₁) ∧ "+
					"    (∀P:prod(set(A), set(A)). 0 ≤ D₁(P)) ∧ "+
					"    «product» = «scPair»(λP:prod(set(A), set(A)). -D₁(P))",
				By(
					curve,
					invertibleProduct,
					productInCharts,
					closed_divisor.IntegralPairHasDivisor.Read(L).At(k, A0, A1, A01, t, product)))
			factorMeet := a.Have(
				"and so is the meet",
				"∃!D₂:(prod(set(A), set(A)) → int). "+
					"    «scDivisor»(D₂) ∧ "+
					"    (∀P:prod(set(A), set(A)). 0 ≤ D₂(P)) ∧ "+
					"    «meet» = «scPair»(λP:prod(set(A), set(A)). -D₂(P))",
				By(
					curve,
					invertibleMeet,
					meetInCharts,
					closed_divisor.IntegralPairHasDivisor.Read(L).At(k, A0, A1, A01, t, meet)))
			D1, centerProduct := a.UnpackAs[Fun[_IdealPair, Int]](factorProduct, "D₁")
			D2, centerMeet := a.UnpackAs[Fun[_IdealPair, Int]](factorMeet, "D₂")
			ofProduct := a.Conjuncts(
				a.Have(
					"D₁ is that divisor",
					"«scDivisor»(D₁) ∧ "+
						"(∀P:prod(set(A), set(A)). 0 ≤ D₁(P)) ∧ "+
						"«product» = «scPair»(λP:prod(set(A), set(A)). -D₁(P))",
					By(centerProduct.At(D1))),
				"D₁ is a closed divisor",
				"D₁ is effective",
				"X times the meet is its ideal pair")
			ofMeet := a.Conjuncts(
				a.Have(
					"D₂ is that divisor",
					"«scDivisor»(D₂) ∧ "+
						"(∀P:prod(set(A), set(A)). 0 ≤ D₂(P)) ∧ "+
						"«meet» = «scPair»(λP:prod(set(A), set(A)). -D₂(P))",
					By(centerMeet.At(D2))),
				"D₂ is a closed divisor",
				"D₂ is effective",
				"the meet is its ideal pair")
			negatedFirst := a.Conjuncts(
				GroupPremises(
					curve, ofProduct[0], closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, D1)),
				"−D₁ is a closed divisor",
				"the pair of D₁ is invertible",
				"the pair of −D₁ is its inverse",
				"its degree is the negative degree")
			negatedMeet := a.Conjuncts(
				GroupPremises(
					curve, ofMeet[0], closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, D2)),
				"−D₂ is a closed divisor",
				"the pair of D₂ is invertible",
				"the pair of −D₂ is its inverse",
				"its degree is the negative degree")
			inverseOfMeet := a.Have(
				"the inverse of the meet is the pair of D₂",
				"«scInverse»(«meet») = «scPair»(D₂)",
				By(ofMeet[2], negatedMeet[1], negatedMeet[2], laws[1].At(a.TermAs[_IdealPair]("«scPair»(D₂)"))))
			added := a.Conjuncts(
				GroupPremises(
					curve,
					ofMeet[0],
					negatedFirst[0],
					closed_divisor.ClosedDivisorAdd.Read(L).At(
						k, A0, A1, A01, t, a.TermAs[Fun[_IdealPair, Int]]("λP:prod(set(A), set(A)). -D₁(P)"), D2)),
				"D₂ − D₁ is a closed divisor",
				"its pair is the product of the pairs",
				"its degree is the sum of the degrees")
			pair := a.Have(
				"so X is the pair of D₂ − D₁",
				"«scPair»(«quotient») = X",
				By(ofProduct[2], inverseOfMeet, quotient[2], added[1]))
			exhibit := a.TermAs[Fun[_IdealPair, Int]]("«quotient»")
			a.Take(exhibit)
			a.Do(SplitConj(
				Case(
					"D₂ − D₁ is a closed divisor with pair X",
					By(added[0], pair)),
				Case(
					"a divisor with pair X is that one, by the injectivity of the pair",
					Derive(func(b *Argument) {
						E := b.FixAs[Fun[_IdealPair, Int]]("E")
						given := b.Conjuncts(
							b.Assume(),
							"E is a closed divisor",
							"its pair is X")
						b.Show(
							"E and D₂ − D₁ have one pair",
							By(
								curve,
								given[0],
								added[0],
								given[1],
								pair,
								ClosedDivisorPairInjective.Read(L).At(k, A0, A1, A01, t, E, exhibit)))
					}))))
		}),
})}

// ClosedPrincipalDivisorPair — the divisor of a nonzero function f is a closed
// divisor, and its pair is the structure pair scaled by f⁻¹: the inverse of f
// times a chart is f⁻¹ times the chart, that pair is invertible, so it has a
// divisor, and the definition chooses one.
var ClosedPrincipalDivisorPair = closedPrincipalDivisorPairThm{family.Add(registry.ProofEntry{
	Name: "ClosedPrincipalDivisorPair",
	Key:  "prop_8776b820ac7ac04e",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t f:A.",
		Hypotheses: []string{"«scCurve»", "f ∈ L.carrier", "f ≠ L.zero"},
		Conclusion: "«scDivisor»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) ∧ " +
			"«scPair»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) = " +
			"lattice_pair_scale(L.inv(f), (A₀, A₁))",
		Abbrev: Abbrev{
			{Name: "inverses", Text: "(fractional_inverse(field_ring(L), A₀, image(L.mul(f), A₀)), " +
				"    fractional_inverse(field_ring(L), A₁, image(L.mul(f), A₁)))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t, f *Expr[A],
			curve, inL, nonzero Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			member := a.MemberOf[on.L](f, inL)
			structure := a.TermAs[_IdealPair]("(A₀, A₁)")
			inverseOfF := a.TermAs[A]("L.inv(f)")
			scaled := a.TermAs[_IdealPair]("lattice_pair_scale(L.inv(f), (A₀, A₁))")
			laws := a.Conjuncts(
				GroupPremises(curve, InvertiblePairLaws.Read(L).At(k, A0, A1, A01, t)),
				"the structure pair is invertible",
				"the inverse of an invertible pair",
				"scaling an invertible pair")
			chartsInL := a.Have(
				"the charts lie in L",
				"A₀ ⊆ L.carrier ∧ A₁ ⊆ L.carrier",
				By(laws[0], laws[1].At(structure), pairs.Fst, pairs.Snd))
			subrings := a.Have(
				"and are subrings of it",
				"subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁)",
				By(
					curve,
					smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t)))
			values := a.Have(
				"the inverse of f times a chart is f⁻¹ times the chart",
				"fractional_inverse(field_ring(L), A₀, image(L.mul(f), A₀)) = image(L.mul(L.inv(f)), A₀) ∧ "+
					"fractional_inverse(field_ring(L), A₁, image(L.mul(f), A₁)) = image(L.mul(L.inv(f)), A₁)",
				By(
					nonzero,
					chartsInL,
					subrings,
					fractional_ideal.FractionalInverseScale.Read(L).At(A0, A0, member),
					fractional_ideal.FractionalInverseScale.Read(L).At(A1, A1, member),
					fractional_ideal.SubringInvertible.Read(L).At(A0),
					fractional_ideal.SubringInvertible.Read(L).At(A1)))
			inverseInL := a.Have(
				"the inverse of f lies in L and is not zero",
				"L.inv(f) ∈ L.carrier ∧ L.inv(f) ≠ L.zero",
				By(nonzero, field.InvIn.Read(L).At(member), field.InvEqZeroOn.Read(L).At(member)))
			invertible := a.Have(
				"so the structure pair scaled by it is invertible",
				"«scInvertible»(lattice_pair_scale(L.inv(f), (A₀, A₁)))",
				By(inverseInL, laws[0], laws[2].At(inverseOfF, structure)))
			unique := a.Have(
				"and has its one closed divisor",
				"∃!D:(prod(set(A), set(A)) → int). "+
					"    «scDivisor»(D) ∧ «scPair»(D) = lattice_pair_scale(L.inv(f), (A₀, A₁))",
				By(curve, invertible, InvertiblePairHasDivisor.Read(L).At(k, A0, A1, A01, t, scaled)))
			same := a.Have(
				"that pair is the pair of the two inverses",
				"«inverses» = lattice_pair_scale(L.inv(f), (A₀, A₁))",
				Simp(Fwd(invertible_lattice_pair.LatticePairScaleDef), Fwd(pairs.Fst), Fwd(pairs.Snd)),
				By(values))
			possible := a.Have(
				"so a closed divisor has the pair of the two inverses",
				"∃D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scPair»(D) = «inverses»",
				same.Rw(),
				By(unique))
			chosen := a.Have(
				"the definition chooses such a divisor",
				"«scDivisor»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) ∧ "+
					"«scPair»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) = «inverses»",
				By(possible, ClosedPrincipalDivisorDef.At(ring, A0, A1, A01, f)))
			a.Show(
				"and its pair is f⁻¹ times the structure pair",
				By(chosen, same))
		}),
})}

// EffectiveDivisorOfSection — a nonzero section s of an invertible pair X is X
// written as s times the pair of an effective divisor: s⁻¹ · X holds 1, so its
// inverse lies inside the charts and is an ideal pair.
var EffectiveDivisorOfSection = effectiveDivisorOfSectionThm{family.Add(registry.ProofEntry{
	Name: "EffectiveDivisorOfSection",
	Key:  "prop_71c27debed100961",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀X:prod(set(A), set(A)). ∀s:A.",
		Hypotheses: []string{"«scCurve»", "«scInvertible»(X)", "s ∈ fst(X) ∩ snd(X)", "s ≠ L.zero"},
		Conclusion: "∃D:(prod(set(A), set(A)) → int). " +
			"    «scDivisor»(D) ∧ (∀P:prod(set(A), set(A)). 0 ≤ D(P)) ∧ X = lattice_pair_scale(s, «scPair»(D))",
		Abbrev: Abbrev{
			{Name: "divided", Text: "lattice_pair_scale(L.inv(s), X)"},
			{Name: "ideal", Text: "«scInverse»(«divided»)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			X *Expr[_IdealPair],
			s *Expr[A],
			curve, invertible, section, nonzero Fact,
		) {
			inverseOfS := a.TermAs[A]("L.inv(s)")
			divided := a.TermAs[_IdealPair]("«divided»")
			ideal := a.TermAs[_IdealPair]("«ideal»")
			laws := a.Conjuncts(
				GroupPremises(curve, InvertiblePairLaws.Read(L).At(k, A0, A1, A01, t)),
				"the structure pair is invertible",
				"the inverse of an invertible pair",
				"scaling an invertible pair")
			inL := a.Conjuncts(
				GroupPremises(invertible, laws[1].At(X)),
				"fst(X) lies in L",
				"snd(X) lies in L",
				"the inverse of X is invertible",
				"X times its inverse is the structure pair",
				"and its inverse is X")
			components := a.Have(
				"s lies in each component of X",
				"s ∈ fst(X) ∧ s ∈ snd(X)",
				BySets(section))
			sInL := a.Have(
				"so s lies in L",
				"s ∈ L.carrier",
				BySets(components, inL[0]))
			member := a.MemberOf[on.L](s, sInL)
			inverseData := a.Have(
				"the inverse of s lies in L and is not zero",
				"L.inv(s) ∈ L.carrier ∧ L.inv(s) ≠ L.zero",
				By(nonzero, field.InvIn.Read(L).At(member), field.InvEqZeroOn.Read(L).At(member)))
			twice := a.Have(
				"and its inverse is s",
				"L.inv(L.inv(s)) = s",
				By(field.InvInvOn.Read(L).At(member)))
			scaled := a.Conjuncts(
				GroupPremises(invertible, inverseData, laws[2].At(inverseOfS, X)),
				"s⁻¹ · X is invertible",
				"its inverse's scaling undoes it",
				"the scalar comes out of products")
			inverse := a.Conjuncts(
				GroupPremises(scaled[0], laws[1].At(divided)),
				"fst(s⁻¹ · X) lies in L",
				"snd(s⁻¹ · X) lies in L",
				"its inverse is invertible",
				"it times its inverse is the structure pair",
				"and the inverse of that inverse is it")
			back := a.Have(
				"s times s⁻¹ · X is X",
				"lattice_pair_scale(s, «divided») = X",
				By(Normalized, twice, scaled[1]))
			unit := a.Have(
				"s⁻¹ · s is 1",
				"L.inv(s) * s = L.one",
				By(nonzero, field.MulLeftInverseOn.Read(L).At(member)))
			ones := a.Have(
				"so s⁻¹ · X holds 1 on each chart",
				"L.one ∈ image(L.mul(L.inv(s)), fst(X)) ∧ L.one ∈ image(L.mul(L.inv(s)), snd(X))",
				BySets(unit, components))
			within := a.Have(
				"so the inverse of s⁻¹ · X lies inside the charts",
				"fst(«ideal») ⊆ A₀ ∧ snd(«ideal») ⊆ A₁",
				Simp(
					Fwd(invertible_lattice_pair.LatticePairInverseDef),
					Fwd(invertible_lattice_pair.LatticePairScaleDef),
					Fwd(pairs.Fst),
					Fwd(pairs.Snd)),
				By(
					ones,
					fractional_ideal.FractionalInverseOfUnit.Read(L).At(
						A0, a.TermAs[Set[A]]("image(L.mul(L.inv(s)), fst(X))")),
					fractional_ideal.FractionalInverseOfUnit.Read(L).At(
						A1, a.TermAs[Set[A]]("image(L.mul(L.inv(s)), snd(X))"))))
			unique := a.Have(
				"so it is the ideal pair of an effective divisor",
				"∃!E:(prod(set(A), set(A)) → int). "+
					"    «scDivisor»(E) ∧ "+
					"    (∀P:prod(set(A), set(A)). 0 ≤ E(P)) ∧ "+
					"    «ideal» = «scPair»(λP:prod(set(A), set(A)). -E(P))",
				By(
					curve,
					inverse[2],
					within,
					closed_divisor.IntegralPairHasDivisor.Read(L).At(k, A0, A1, A01, t, ideal)))
			E, center := a.UnpackAs[Fun[_IdealPair, Int]](unique, "E")
			effective := a.Conjuncts(
				a.Have(
					"E is that divisor",
					"«scDivisor»(E) ∧ "+
						"(∀P:prod(set(A), set(A)). 0 ≤ E(P)) ∧ "+
						"«ideal» = «scPair»(λP:prod(set(A), set(A)). -E(P))",
					By(center.At(E))),
				"E is a closed divisor",
				"E is effective",
				"the inverse of s⁻¹ · X is the pair of −E")
			negated := a.Conjuncts(
				GroupPremises(
					curve, effective[0], closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, E)),
				"−E is a closed divisor",
				"the pair of E is invertible",
				"the pair of −E is its inverse",
				"its degree is the negative degree")
			pair := a.Have(
				"so s⁻¹ · X is the pair of E",
				"«divided» = «scPair»(E)",
				By(
					inverse[4],
					effective[2],
					negated[1],
					negated[2],
					laws[1].At(a.TermAs[_IdealPair]("«scPair»(E)"))))
			a.Take(E)
			a.Show(
				"X is s times the pair of the effective divisor E",
				By(Normalized, effective[0], effective[1], pair, back))
		}),
})}

// ClosedDivisorEquivalentIff — two closed divisors are equivalent exactly when
// E − D is a principal divisor: their pairs lie in one class when a nonzero a
// scales one to the other, and that says the pair of E − D is a times the
// structure pair, the pair of div(a⁻¹).
var ClosedDivisorEquivalentIff = closedDivisorEquivalentIffThm{family.Add(registry.ProofEntry{
	Name: "ClosedDivisorEquivalentIff",
	Key:  "prop_682857d55d8c75cf",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D E:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{"«scCurve»", "«scDivisor»(D)", "«scDivisor»(E)"},
		Conclusion: "closed_divisor_equivalent(field_ring(L), A₀, A₁, A₀₁, D, E) ⇔ " +
			"∃f:A. " +
			"    f ∈ L.carrier ∧ " +
			"    f ≠ L.zero ∧ " +
			"    «difference» = closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)",
		Abbrev: Abbrev{
			{Name: "difference", Text: "λP:prod(set(A), set(A)). E(P) - D(P)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D, E *Arrow[_IdealPair, Int],
			curve, divisorD, divisorE Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			pairD := a.TermAs[_IdealPair]("«scPair»(D)")
			pairE := a.TermAs[_IdealPair]("«scPair»(E)")
			structure := a.TermAs[_IdealPair]("(A₀, A₁)")
			difference := a.TermAs[Fun[_IdealPair, Int]]("«difference»")
			laws := a.Conjuncts(
				GroupPremises(curve, InvertiblePairLaws.Read(L).At(k, A0, A1, A01, t)),
				"the structure pair is invertible",
				"the inverse of an invertible pair",
				"scaling an invertible pair")
			monoid := a.Conjuncts(
				GroupPremises(curve, closed_divisor.ClosedDivisorPairProduct.Read(L).At(k, A0, A1, A01, t)),
				"the invertible pairs are a commutative monoid",
				"inverses are unique",
				"the integer powers at a closed point",
				"a closed divisor's pair is the product of its powers")[0]
			negatedD := a.Conjuncts(
				GroupPremises(curve, divisorD, closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, D)),
				"−D is a closed divisor",
				"the pair of D is invertible",
				"the pair of −D is its inverse",
				"its degree is the negative degree")
			negatedE := a.Conjuncts(
				GroupPremises(curve, divisorE, closed_divisor.ClosedDivisorNegate.Read(L).At(k, A0, A1, A01, t, E)),
				"−E is a closed divisor",
				"the pair of E is invertible",
				"the pair of −E is its inverse",
				"its degree is the negative degree")
			invertibleD, invertibleE := negatedD[1], negatedE[1]
			inverseD := a.Conjuncts(
				GroupPremises(negatedD[1], laws[1].At(pairD)),
				"the first component lies in L",
				"the second component lies in L",
				"the inverse of the pair of D is invertible",
				"the pair of D times its inverse is the structure pair",
				"and the inverse of that inverse is the pair")
			subtracted := a.Conjuncts(
				GroupPremises(
					curve, divisorE, divisorD, closed_divisor.ClosedDivisorSub.Read(L).At(k, A0, A1, A01, t, E, D)),
				"E − D is a closed divisor",
				"its pair is the quotient of the two pairs",
				"its degree is the difference of the degrees")
			divisor, pair := subtracted[0], subtracted[1]
			equivalent := a.Have(
				"equivalence says a nonzero member of L scales one pair to the other",
				"closed_divisor_equivalent(field_ring(L), A₀, A₁, A₀₁, D, E) ⇔ "+
					"∃c:A. c ∈ L.carrier ∧ c ≠ L.zero ∧ «scPair»(E) = lattice_pair_scale(c, «scPair»(D))",
				By(
					curve,
					smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					invertibleD,
					invertibleE,
					ClosedDivisorEquivalentDef.At(ring, A0, A1, A01, D, E),
					algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
					curve_degree.PairClassEqIff.Read(L).At(A0, A1, A01, t, pairD, pairE)))
			inverseIn := a.Have(
				"a nonzero member of L has a nonzero inverse in L, and its inverse is that member",
				"∀c:A. c ∈ L.carrier ∧ c ≠ L.zero ⇒ L.inv(c) ∈ L.carrier ∧ L.inv(c) ≠ L.zero ∧ L.inv(L.inv(c)) = c",
				Derive(func(b *Argument) {
					c := b.FixAs[A]("c")
					given := b.Conjuncts(
						b.Assume(),
						"c lies in L",
						"c is not zero")
					member := b.MemberOf[on.L](c, given[0])
					b.Show(
						"the inverse laws of the field L",
						By(
							given[1],
							field.InvIn.Read(L).At(member),
							field.InvEqZeroOn.Read(L).At(member),
							field.InvInvOn.Read(L).At(member)))
				}))
			a.Iff()
			a.Forward(
				"a scalar c between the pairs makes E − D the divisor of its inverse",
				func(b *Argument, classed Fact) {
					c, scalar := b.ObtainAs[A](
						"c scales the pair of D to the pair of E",
						"∃c:A. c ∈ L.carrier ∧ c ≠ L.zero ∧ «scPair»(E) = lattice_pair_scale(c, «scPair»(D))",
						By(classed, equivalent))
					given := b.Conjuncts(
						scalar,
						"c lies in L",
						"c is not zero",
						"it scales the pair of D to the pair of E")
					f := b.TermAs[A]("L.inv(c)")
					inverted := b.Conjuncts(
						GroupPremises(given[0], given[1], inverseIn.At(c)),
						"its inverse lies in L",
						"its inverse is not zero",
						"and the inverse of that is c")
					principal := b.Conjuncts(
						GroupPremises(
							curve,
							inverted[1],
							ClosedPrincipalDivisorPair.Read(L).At(k, A0, A1, A01, t, b.MemberOf[on.L](f, inverted[0]))),
						"the divisor of c⁻¹ is a closed divisor",
						"its pair is c times the structure pair")
					scaling := b.Conjuncts(
						GroupPremises(given[0], given[1], negatedD[1], laws[2].At(c, pairD)),
						"c times the pair of D is invertible",
						"which its inverse undoes",
						"and c comes out of products")
					quotient := b.Have(
						"the pair of E − D is c times the structure pair",
						"«scPair»(«difference») = lattice_pair_scale(c, (A₀, A₁))",
						By(
							pair,
							given[2],
							inverseD[2],
							inverseD[3],
							scaling[2].At(b.TermAs[_IdealPair]("«scInverse»(«scPair»(D))"))))
					same := b.Have(
						"which is the pair of the divisor of c⁻¹",
						"«scPair»(«difference») = «scPair»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, L.inv(c)))",
						By(quotient, principal[1], inverted[2]))
					b.Take(f)
					b.Show(
						"so E − D and the divisor of c⁻¹ are one divisor",
						By(
							inverted[0],
							inverted[1],
							curve,
							divisor,
							principal[0],
							same,
							ClosedDivisorPairInjective.Read(L).At(
								k,
								A0,
								A1,
								A01,
								t,
								difference,
								b.TermAs[Fun[_IdealPair, Int]]("closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, L.inv(c))"))))
				})
			a.Backward(
				"where E − D is the divisor of f, the inverse of f scales the pair of D to the pair of E",
				func(b *Argument, principal Fact) {
					f, chosen := b.UnpackAs[A](principal, "f")
					given := b.Conjuncts(
						chosen,
						"f lies in L",
						"f is not zero",
						"E − D is the divisor of f")
					inverted := b.Conjuncts(
						GroupPremises(given[0], given[1], inverseIn.At(f)),
						"its inverse lies in L",
						"its inverse is not zero",
						"and the inverse of that is f")
					divisorOfF := b.Conjuncts(
						GroupPremises(
							curve,
							given[1],
							ClosedPrincipalDivisorPair.Read(L).At(k, A0, A1, A01, t, b.MemberOf[on.L](f, given[0]))),
						"the divisor of f is a closed divisor",
						"its pair is f⁻¹ times the structure pair")
					c := b.TermAs[A]("L.inv(f)")
					quotient := b.Have(
						"the pair of E − D is f⁻¹ times the structure pair",
						"«scPair»(«difference») = lattice_pair_scale(L.inv(f), (A₀, A₁))",
						given[2].Rw(),
						By(divisorOfF[1]))
					scaling := b.Conjuncts(
						GroupPremises(inverted[0], inverted[1], laws[0], laws[2].At(c, structure)),
						"f⁻¹ times the structure pair is invertible",
						"which its inverse undoes",
						"and f⁻¹ comes out of products")
					division := b.Conjuncts(
						GroupPremises(
							curve,
							negatedE[1],
							negatedD[1],
							closed_divisor.PairQuotient.Read(L).At(k, A0, A1, A01, t, pairE, pairD)),
						"the quotient of the two pairs is invertible",
						"and multiplies back to the pair of E",
						"the pair of E times the pair of D, over that, is the pair of E")
					product := b.Have(
						"so the pair of E is f⁻¹ times the pair of D",
						"«scPair»(E) = lattice_pair_scale(L.inv(f), «scPair»(D))",
						By(
							pair,
							quotient,
							division[1],
							scaling[2].At(pairD),
							invertibleD,
							comm_monoid.LeftIdentityOn.Read(monoid).AsFact().At(pairD)))
					scalar := b.Have(
						"so a nonzero member of L scales one pair to the other",
						"∃c:A. c ∈ L.carrier ∧ c ≠ L.zero ∧ «scPair»(E) = lattice_pair_scale(c, «scPair»(D))",
						Witness(c),
						By(inverted[0], inverted[1], product))
					b.Show(
						"so the two classes agree",
						By(scalar, equivalent))
				})
		}),
})}

// ClosedPrincipalDivisorOrder — the coefficient of div f at a closed point is the
// order of f there: both are the integer exponent of f times the local ring as a
// power of the maximal ideal, and that exponent is unique.
var ClosedPrincipalDivisorOrder = closedPrincipalDivisorOrderThm{family.Add(registry.ProofEntry{
	Name: "ClosedPrincipalDivisorOrder",
	Key:  "prop_49ce038d820d578e",
	Build: family.Theorem(Statement{
		Binders:    "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t f:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{"«scCurve»", "f ∈ L.carrier", "f ≠ L.zero", "«scPoint»(P)"},
		Conclusion: "closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f, P) = " +
			"regular_point_order(field_ring(L), A₀, A₁, P, f)",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t, f *Expr[A],
			P *Expr[_IdealPair],
			curve, inL, nonzero, point Fact,
		) {
			ring := a.TermAs[RingOps[A]]("field_ring(L)")
			divisor := a.TermAs[Fun[_IdealPair, Int]]("closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)")
			coefficient := a.TermAs[Int]("closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f, P)")
			fm := a.MemberOf[on.L](f, inL)
			principal := a.Conjuncts(
				GroupPremises(curve, nonzero, ClosedPrincipalDivisorPair.Read(L).At(k, A0, A1, A01, t, fm)),
				"the divisor of f is a closed divisor",
				"its pair is f⁻¹ times the structure pair")
			power := a.Have(
				"f times the local ring is the power of the maximal ideal at the coefficient",
				"image(L.mul(f), «local») = "+
					"signed_ideal_power(field_ring(L), "+
					"    «local», "+
					"    «maximal», "+
					"    closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f, P))",
				By(
					curve,
					principal[0],
					point,
					nonzero,
					principal[1],
					ClosedDivisorLocalPower.Read(L).At(k, A0, A1, A01, t, fm, divisor, P)))
			possible := a.Have(
				"so some exponent has that power",
				"∃n:int. image(L.mul(f), «local») = signed_ideal_power(field_ring(L), «local», «maximal», n)",
				Witness(coefficient),
				By(power))
			order := a.Have(
				"and the definition of the order chooses one",
				"image(L.mul(f), «local») = "+
					"signed_ideal_power(field_ring(L), "+
					"    «local», "+
					"    «maximal», "+
					"    regular_point_order(field_ring(L), A₀, A₁, P, f))",
				By(possible, regular_point.RegularPointOrderDef.At(ring, A0, A1, P, f)))
			a.Show(
				"distinct exponents give distinct powers",
				By(
					curve,
					point,
					power,
					order,
					LocalPowerInjective.Read(L).At(
						k,
						A0,
						A1,
						A01,
						t,
						P,
						coefficient,
						a.TermAs[Int]("regular_point_order(field_ring(L), A₀, A₁, P, f)"))))
		}),
})}

// WeightedDivisorLatticeCorrespondence — closed divisors and invertible pairs
// correspond, degrees agreeing: each clause is a member of the chapter, the first
// read with the invertibility of a divisor's pair.
var WeightedDivisorLatticeCorrespondence = weightedDivisorLatticeCorrespondenceThm{family.Add(registry.ProofEntry{
	Name: "WeightedDivisorLatticeCorrespondence",
	Key:  "prop_9e1637e013649c03",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A.",
		Hypotheses: []string{
			"«scCurve»",
		},
		Conclusion: "(∀D:(prod(set(A), set(A)) → int). " +
			"    «scDivisor»(D) ⇒ " +
			"    «scInvertible»(«scPair»(D)) ∧ " +
			"    curve_degree(field_ring(L), k, A₀, A₁, A₀₁, «scPair»(D)) = «scDegree»(D)) ∧ " +
			"(∀X:prod(set(A), set(A)). " +
			"    «scInvertible»(X) ⇒ ∃!D:(prod(set(A), set(A)) → int). «scDivisor»(D) ∧ «scPair»(D) = X) ∧ " +
			"(∀f:A. " +
			"    f ∈ L.carrier ∧ f ≠ L.zero ⇒ " +
			"    «scDivisor»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) ∧ " +
			"    «scPair»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) = " +
			"    lattice_pair_scale(L.inv(f), (A₀, A₁))) ∧ " +
			"(∀X:prod(set(A), set(A)). ∀s:A. " +
			"    «scInvertible»(X) ∧ s ∈ fst(X) ∩ snd(X) ∧ s ≠ L.zero ⇒ " +
			"    ∃D:(prod(set(A), set(A)) → int). " +
			"        «scDivisor»(D) ∧ " +
			"        (∀P:prod(set(A), set(A)). 0 ≤ D(P)) ∧ " +
			"        X = lattice_pair_scale(s, «scPair»(D))) ∧ " +
			"(∀D E:(prod(set(A), set(A)) → int). " +
			"    «scDivisor»(D) ∧ «scDivisor»(E) ⇒ " +
			"    (closed_divisor_equivalent(field_ring(L), A₀, A₁, A₀₁, D, E) ⇔ " +
			"        ∃f:A. " +
			"            f ∈ L.carrier ∧ " +
			"            f ≠ L.zero ∧ " +
			"            (λP:prod(set(A), set(A)). E(P) - D(P)) = " +
			"            closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f))) ∧ " +
			"(∀f:A. ∀P:prod(set(A), set(A)). " +
			"    f ∈ L.carrier ∧ f ≠ L.zero ∧ «scPoint»(P) ⇒ " +
			"    closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f, P) = " +
			"    regular_point_order(field_ring(L), A₀, A₁, P, f))",
	},
		func(a *Argument, L field.FieldFact[on.L], k, A0, A1, A01 *Expr[Set[A]], t *Expr[A], curve Fact) {
			a.Show(
				"the clauses are the members",
				By(
					curve,
					At(Read(closed_divisor.ClosedDivisorNegate, L), k, A0, A1, A01, t),
					At(Read(ClosedDivisorLatticeDegree, L), k, A0, A1, A01, t),
					At(Read(InvertiblePairHasDivisor, L), k, A0, A1, A01, t),
					At(Read(ClosedPrincipalDivisorPair, L), k, A0, A1, A01, t),
					At(Read(EffectiveDivisorOfSection, L), k, A0, A1, A01, t),
					At(Read(ClosedDivisorEquivalentIff, L), k, A0, A1, A01, t),
					At(Read(ClosedPrincipalDivisorOrder, L), k, A0, A1, A01, t)))
		}),
})}

// PrincipalDivisorDegreeZero — a nonzero function has a closed divisor, and
// its degree is zero: the pair of div f is the structure pair scaled by f⁻¹,
// scaling keeps the degree of an invertible pair, and the structure pair has
// degree zero.
var PrincipalDivisorDegreeZero = principalDivisorDegreeZeroThm{family.Add(registry.ProofEntry{
	Name: "PrincipalDivisorDegreeZero",
	Key:  "prop_3c99119956355aca",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t f:A.",
		Hypotheses: []string{
			"«scCurve»",
			"f ∈ L.carrier",
			"f ≠ L.zero",
		},
		Conclusion: "«scDivisor»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) ∧ " +
			"«scDegree»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) = 0",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t, f *Expr[A],
			curve, inL, nonzero Fact,
		) {
			member := a.MemberOf[on.L](f, inL)
			principal := a.Have(
				"the divisor of f is a closed divisor, and its pair "+
					"is the structure pair scaled by the inverse of f",
				"«scDivisor»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) ∧ "+
					"«scPair»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f)) = "+
					"lattice_pair_scale(L.inv(f), (A₀, A₁))",
				By(WeightedDivisorLatticeCorrespondence.Read(L).At(k, A0, A1, A01, t), curve, inL, nonzero))
			degree := a.Have(
				"the degree of that pair is the degree of the divisor",
				"curve_degree(field_ring(L), "+
					"    k, "+
					"    A₀, "+
					"    A₁, "+
					"    A₀₁, "+
					"    «scPair»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f))) = "+
					"«scDegree»(closed_principal_divisor(field_ring(L), A₀, A₁, A₀₁, f))",
				By(WeightedDivisorLatticeCorrespondence.Read(L).At(k, A0, A1, A01, t), curve, principal))
			inverse := a.Have(
				"the inverse of f lies in L and is not zero",
				"L.inv(f) ∈ L.carrier ∧ L.inv(f) ≠ L.zero",
				By(nonzero, field.InvIn.Read(L).At(member), field.InvEqZeroOn.Read(L).At(member)))
			scaled := a.Have(
				"scaling the structure pair by the inverse of f keeps its degree, which is zero",
				"curve_degree(field_ring(L), k, A₀, A₁, A₀₁, lattice_pair_scale(L.inv(f), (A₀, A₁))) = &0",
				By(
					curve,
					smooth_curve.SmoothCurveOverLine.Read(L).At(k, A0, A1, A01, t),
					inverse,
					algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t),
					curve_degree.DegreeScale.Read(L).At(
						k, A0, A1, A01, t, field.InvIn.Read(L).At(member), a.TermAs[_IdealPair]("(A₀, A₁)")),
					curve_degree.DegreeStructure.Read(L).At(k, A0, A1, A01)))
			a.Show(
				"the divisor of f is a closed divisor of degree zero",
				By(principal, degree, scaled))
		}),
})}
