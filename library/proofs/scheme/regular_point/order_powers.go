// order_powers.go — the order at a regular rational point. The point lies in a
// chart whose ideal is rational and invertible, and the localization of the
// chart at that ideal is the local ring at the point, where every nonzero
// function generates exactly one integer power of the maximal ideal
// (subring_localization.OrderAtChartPoint).

package regular_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/subring_localization"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/biaffine_rational_point"
	"github.com/euc-ai/xugo/library/proofs/scheme/invertible_lattice_pair"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair_twist"
	"github.com/euc-ai/xugo/library/registry"
)

// OrderAtRegularPoint — at a regular rational point every nonzero function
// generates exactly one integer power of the maximal ideal of the local ring,
// the powers decrease strictly, and the exponent is a valuation of the
// function field: P's chart and ideal meet the hypotheses of subring_localization.OrderAtChartPoint
// (RegularPointChart), whose localization is the local ring at P, so its three
// conclusions are the statement, regular_point_order being the exponent its ε
// chooses.
var OrderAtRegularPoint = orderAtRegularPointThm{family.Add(registry.ProofEntry{
	Name: "OrderAtRegularPoint",
	Reading: "Invertibility of P's ideal makes the maximal ideal principal: at " +
		"a rational point that is not invertible, the cusp y² = x³ at the origin, " +
		"xO is no power of the maximal ideal and the ε has nothing to pick. The " +
		"finite rank of the chart over k[t] bounds the order of a nonzero function.",
	Key: "prop_c7b3b1750a389136",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
		},
		Conclusion: "valuation_order(field_ring(L), regular_point_order(field_ring(L), A₀, A₁, P)) ∧ " +
			"(∀f:A. f ∈ L.carrier ∧ f ≠ L.zero ⇒ ∃!n:int. image(L.mul(f), «local») = «power»(n)) ∧ " +
			"(∀i j:int. «power»(i) ⊆ «power»(j) ⇔ j ≤ i)",
		Abbrev: Abbrev{
			{Name: "local", Text: "point_local_ring(field_ring(L), A₀, A₁, P)"},
			{Name: "maximal", Text: "ideal_span(restrict_ring(field_ring(L), «local»), point_ideal(A₀, P))"},
			{Name: "power", Text: "λn:int. signed_ideal_power(field_ring(L), «local», «maximal», n)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			curve, regular Fact,
		) {
			chart := a.Simplified(
				GroupPremises(curve, regular, RegularPointChart.Read(L).At(k, A0, A1, A01, t, P)))
			localRing := a.Have(
				"the local ring at P is the localization of P's chart at P's ideal",
				"«local» = subring_localization(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P))",
				Simp(Fwd(PointLocalRingDef)),
				Refl())
			order := a.Conjuncts(
				a.Simplified(
					GroupPremises(
						chart,
						subring_localization.OrderAtChartPoint.Read(L).At(
							k, a.TermAs[Set[A]]("point_chart(A₀, A₁, P)"), a.TermAs[Set[A]]("point_ideal(A₀, P)"))),
					Rev(localRing)),
				"every nonzero function generates exactly one power of the maximal ideal",
				"the powers decrease strictly",
				"an exponent of the principal ideals is a valuation")
			unique, decreasing, valuation := order[0], order[1], order[2]
			picks := a.Have(
				"regular_point_order picks that exponent",
				Statement{
					Binders: "∀f:A.",
					Hypotheses: []string{
						"f ∈ L.carrier",
						"f ≠ L.zero",
					},
					Conclusion: "image(L.mul(f), «local») = «power»(regular_point_order(field_ring(L), A₀, A₁, P, f))",
				},
				Derive(func(b *Argument) {
					f := b.FixAs[A]("f")
					nonzero := b.Assume()
					b.Show(
						"the ε picks the exponent there is",
						By(nonzero, unique, RegularPointOrderDef.At(b.TermAs[RingOps[A]]("field_ring(L)"), A0, A1, P, f)))
				}))
			a.Show(
				"so regular_point_order is a valuation, beside the unique exponent and the decreasing powers",
				By(
					unique,
					decreasing,
					picks,
					valuation.At(a.TermAs[Fun[A, Int]]("regular_point_order(field_ring(L), A₀, A₁, P)"))))
		}),
})}

// RegularPointChart — a regular rational point P of a curve over the line of t
// lies in its chart S = point_chart(A₀, A₁, P) at its ideal point_ideal(A₀, P):
// A₁ with ideal snd(P) when fst(P) is all of A₀, and A₀ with ideal fst(P)
// otherwise. There S is a subring holding the subfield k, L is its field of
// fractions, each nonzero principal ideal of S has finite colength
// (algebraic_curve.PrincipalColengthFinite), and the ideal of P is the ideal of
// a k-rational point of S (biaffine_rational_point.RationalPointChart),
// invertible in S.
var RegularPointChart = regularPointChartThm{family.Add(registry.ProofEntry{
	Name: "RegularPointChart",
	Key:  "prop_1a227d5ac0137ff7",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀P:prod(set(A), set(A)).",
		Hypotheses: []string{
			"curve_over_line(L, k, t, A₀, A₁, A₀₁)",
			"biaffine_regular_point(field_ring(L), k, A₀, A₁, A₀₁, P)",
		},
		Conclusion: "subring(field_ring(L), point_chart(A₀, A₁, P)) ∧ " +
			"subfield(L, k) ∧ " +
			"k ⊆ point_chart(A₀, A₁, P) ∧ " +
			"fraction_field_carrier(field_ring(L), point_chart(A₀, A₁, P)) ∧ " +
			"rational_ideal(field_ring(L), k, point_chart(A₀, A₁, P), point_ideal(A₀, P)) ∧ " +
			"invertible_fractional(field_ring(L), point_chart(A₀, A₁, P), point_ideal(A₀, P)) ∧ " +
			"(∀a:A. a ∈ point_chart(A₀, A₁, P) ∧ a ≠ L.zero ⇒ «principalFinite»(point_chart(A₀, A₁, P), a))",
		Abbrev: Abbrev{
			{Name: "principalFinite", Text: "λU:set(A). λx:A. " +
				"    finite_dimensional(restrict_ring(field_ring(L), k), " +
				"        quotient_module(restrict_module(regular_module(field_ring(L)), U), image(L.mul(x), U)))"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			P *Expr[Prod[Set[A], Set[A]]],
			h Fact,
		) {
			given := a.Conjuncts(
				h,
				"the curve over the line of t",
				"P is a regular rational point")
			curve, regular := given[0], given[1]
			charts := a.Have(
				"k is a subfield, and the charts are subrings of L holding it",
				"subfield(L, k) ∧ subring(field_ring(L), A₀) ∧ subring(field_ring(L), A₁) ∧ k ⊆ A₀ ∩ A₁",
				By(
					curve,
					algebraic_curve.CurveOverItsLine.Read(L).At(k, A0, A1, A01, t),
					algebraic_curve.CurveLatticeData.Read(L).At(k, A0, A1, A01, t)))
			kInCharts := a.Have(
				"so k lies in each chart",
				"k ⊆ A₀ ∧ k ⊆ A₁",
				BySets(charts))
			fractions := a.Have(
				"L is the field of fractions of both charts",
				"fraction_field_carrier(field_ring(L), A₀) ∧ fraction_field_carrier(field_ring(L), A₁)",
				By(curve, algebraic_curve.FractionFieldBothCharts.Read(L).At(k, A0, A1, A01, t)))
			finite := a.Conjuncts(
				GroupPremises(curve, algebraic_curve.PrincipalColengthFinite.Read(L).At(k, A0, A1, A01, t)),
				"each nonzero principal ideal of chart zero has finite colength",
				"and so does each of chart one")
			point := a.Conjuncts(
				a.Unfolded(regular, lattice_pair_twist.BiaffineRegularPointDef),
				"P is a rational point of the overlap",
				"P is an invertible pair")
			invertible := a.Conjuncts(
				a.Unfolded(point[1], invertible_lattice_pair.InvertibleLatticePairDef),
				"fst(P) is invertible in A₀",
				"snd(P) is invertible in A₁",
				"P is a lattice pair")
			// P's chart is a subring of L holding k, where P's ideal is the ideal of a
			// k-rational point.
			located := GroupPremises(
				charts,
				kInCharts,
				point[0],
				biaffine_rational_point.RationalPointChart.Read(L).At(k, A0, A1, A01, P))
			a.Cases(a.TermAs[Bool]("fst(P) = A₀"))
			a.When(
				"P lies off A₀, its first ideal the whole chart, so its chart is A₁ with ideal snd(P)",
				func(b *Argument, offFirst Fact) {
					b.Show(
						"the chart A₁ and its ideal snd(P)",
						By(
							Normalized,
							offFirst,
							biaffine_rational_point.PointOffChartZero.At(A0, A1, P),
							charts,
							located,
							fractions,
							finite[1],
							invertible[1]))
				})
			a.Otherwise(
				"P lies in A₀, with ideal fst(P)",
				func(b *Argument, inFirst Fact) {
					b.Show(
						"the chart A₀ and its ideal fst(P)",
						By(
							Normalized,
							inFirst,
							biaffine_rational_point.PointOnChartZero.At(A0, A1, P),
							charts,
							located,
							fractions,
							finite[0],
							invertible[0]))
				})
		}),
})}
