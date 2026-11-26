// smooth_curve.go — the Weierstrass datum as a smooth finite curve in the
// sense of scheme/smooth_curve: every nonzero ideal of either chart is
// invertible, so each chart is integrally closed in L, and smooth_finite_curve
// holds of the datum.

package closed_point

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ideal_factorization"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/elliptic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	"github.com/euc-ai/xugo/library/registry"
)

// ChartIdealsInvertible — in either chart of a smooth Weierstrass datum every
// nonzero ideal is invertible: the datum is a curve over the x-line, so a
// nonzero ideal of either chart has finite k-colength and hence finite height,
// every maximal ideal of either chart is invertible, and a subring of L with
// both properties has every nonzero ideal invertible.
var ChartIdealsInvertible = chartIdealsInvertibleThm{family.Add(registry.ProofEntry{
	Name: "ChartIdealsInvertible",
	Key:  "prop_6271646a403acbcc",
	Reading: "k need not be finite. Smoothness, 2 ≠ 0 and 4a³ + 27b² ≠ 0, enters only through the " +
		"maximal ideals: on a singular cubic the maximal ideal of the singular point is not invertible.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A. ∀I:set(A).",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "(ring_ideal(restrict_ring(field_ring(L), «curveChart0»), I) ∧ I ≠ {L.zero} ⇒ " +
			"    invertible_fractional(field_ring(L), «curveChart0», I)) ∧ " +
			"(ring_ideal(restrict_ring(field_ring(L), «curveChart1»), I) ∧ I ≠ {L.zero} ⇒ " +
			"    invertible_fractional(field_ring(L), «curveChart1», I))",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			I *Expr[Set[A]],
			smooth Fact,
		) {
			chartZero := arg.TermAs[Set[A]]("«curveChart0»")
			chartOne := arg.TermAs[Set[A]]("«curveChart1»")
			overlap := arg.TermAs[Set[A]]("«curveOverlap»")
			curve := arg.Have(
				"the datum is a curve over the x-line whose charts are the two Weierstrass charts",
				"curve_over_line(L, k, x, «curveChart0», «curveChart1», «curveOverlap»)",
				By(
					elliptic_curve.SmoothWeierstrassDatum.Read(smooth),
					elliptic_curve.WeierstrassIsCurve.Read(L).At(k, x, y, a, b)))
			charts := arg.Have(
				"both charts are subrings of L containing the subfield k",
				"subfield(L, k) ∧ "+
					"subring(field_ring(L), «curveChart0») ∧ "+
					"subring(field_ring(L), «curveChart1») ∧ "+
					"k ⊆ «curveChart0» ∧ "+
					"k ⊆ «curveChart1»",
				BySets(curve, algebraic_curve.CurveOverItsLine.Read(L).At(k, chartZero, chartOne, overlap, x)))
			heights := arg.Have(
				"a nonzero ideal of either chart has finite k-colength, so finite height",
				"∀H:set(A). "+
					"    (ring_ideal(restrict_ring(field_ring(L), «curveChart0»), H) ∧ H ≠ {L.zero} ⇒ "+
					"        finite_ideal_height(restrict_ring(field_ring(L), «curveChart0»), H)) ∧ "+
					"    (ring_ideal(restrict_ring(field_ring(L), «curveChart1»), H) ∧ H ≠ {L.zero} ⇒ "+
					"        finite_ideal_height(restrict_ring(field_ring(L), «curveChart1»), H))",
				arg.ForEach(func(H *Expr[Set[A]]) Action {
					return By(
						curve,
						charts,
						algebraic_curve.NonzeroIdealFiniteColength.Read(L).At(k, chartZero, chartOne, overlap, x, H),
						ideal_factorization.FiniteColengthIdealHeight.Read(L).At(chartZero, k, H),
						ideal_factorization.FiniteColengthIdealHeight.Read(L).At(chartOne, k, H))
				}))
			arg.Show(
				"a subring of L with nonzero ideals of finite height and invertible "+
					"maximal ideals has every nonzero ideal invertible; both charts are such",
				SplitConj(
					Case(
						"chart zero, every maximal ideal of which is invertible",
						By(
							ideal_factorization.NonzeroIdealInvertible.Read(L).At(chartZero, I),
							charts,
							heights,
							smooth,
							ChartZeroMaximalInvertible.Read(L))),
					Case(
						"chart one, every maximal ideal of which is invertible",
						By(
							ideal_factorization.NonzeroIdealInvertible.Read(L).At(chartOne, I),
							charts,
							heights,
							smooth,
							ChartOneMaximalInvertible.Read(L)))))
		}),
})}

// WeierstrassChartsNormal — both charts of a smooth Weierstrass datum are
// integrally closed in L: every nonzero ideal of either chart is invertible,
// L is the field of fractions of either, and a subring of L with these two
// properties is integrally closed in its field of fractions.
var WeierstrassChartsNormal = weierstrassChartsNormalThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassChartsNormal",
	Key:  "prop_ed504e3f6495d03d",
	Reading: "k need not be finite. Smoothness is load-bearing: with 4a³ + 27b² = 0 the " +
		"affine chart is not integrally closed (y/x is integral over k[x, y]/(y² − x³)). The " +
		"statement is about the charts as subrings of L, L the field of fractions of either.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
		},
		Conclusion: "integrally_closed_in(restrict_ring(field_ring(L), «curveChart0»), L.carrier) ∧ " +
			"integrally_closed_in(restrict_ring(field_ring(L), «curveChart1»), L.carrier)",
	}, func(arg *Argument, L field.FieldFact[on.L], k *Expr[Set[A]], x, y, a, b *Expr[A], smooth Fact) {
		chartZero := arg.TermAs[Set[A]]("«curveChart0»")
		chartOne := arg.TermAs[Set[A]]("«curveChart1»")
		overlap := arg.TermAs[Set[A]]("«curveOverlap»")
		invertible := arg.Have(
			"every nonzero ideal of either chart is invertible",
			"∀I:set(A). "+
				"    (ring_ideal(restrict_ring(field_ring(L), «curveChart0»), I) ∧ I ≠ {L.zero} ⇒ "+
				"        invertible_fractional(field_ring(L), «curveChart0», I)) ∧ "+
				"    (ring_ideal(restrict_ring(field_ring(L), «curveChart1»), I) ∧ I ≠ {L.zero} ⇒ "+
				"        invertible_fractional(field_ring(L), «curveChart1», I))",
			arg.ForEach(func(I *Expr[Set[A]]) Action {
				return By(smooth, ChartIdealsInvertible.Read(L).At(k, x, y, a, b, I))
			}))
		charts := arg.Have(
			"the datum is a curve over the x-line, so either chart "+
				"is a subring of L with L for its field of fractions",
			"subring(field_ring(L), «curveChart0») ∧ "+
				"subring(field_ring(L), «curveChart1») ∧ "+
				"fraction_field_carrier(field_ring(L), «curveChart0») ∧ "+
				"fraction_field_carrier(field_ring(L), «curveChart1»)",
			By(
				elliptic_curve.SmoothWeierstrassDatum.Read(smooth),
				elliptic_curve.WeierstrassIsCurve.Read(L).At(k, x, y, a, b),
				algebraic_curve.CurveOverItsLine.Read(L).At(k, chartZero, chartOne, overlap, x),
				algebraic_curve.FractionFieldBothCharts.Read(L).At(k, chartZero, chartOne, overlap, x)))
		arg.Show(
			"a subring of L with every nonzero ideal invertible and L for its "+
				"field of fractions is integrally closed in L; both charts are such",
			SplitConj(
				Case(
					"chart zero is integrally closed in L",
					By(invertible, charts, ideal_factorization.InvertibleIdealsIntegrallyClosed.Read(L).At(chartZero))),
				Case(
					"chart one is integrally closed in L",
					By(invertible, charts, ideal_factorization.InvertibleIdealsIntegrallyClosed.Read(L).At(chartOne)))))
	}),
})}

// WeierstrassSmoothFiniteCurve — a smooth Weierstrass datum, 2 ≠ 0 and
// 4a³ + 27b² ≠ 0, over a finite field is a smooth finite curve over k with
// coordinate x: a curve over the line, finite k, and two normal charts.
var WeierstrassSmoothFiniteCurve = weierstrassSmoothFiniteCurveThm{family.Add(registry.ProofEntry{
	Name: "WeierstrassSmoothFiniteCurve",
	Key:  "prop_a26990f969b42442",
	Reading: "The field argument is L itself: smooth_finite_curve reads the normality of the charts " +
		"in L's carrier, which is the function field of the datum. The charts are the datum's chart 0 " +
		"and chart 1 and the overlap is chart 0 with x inverted, as WeierstrassIsCurve presents them.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k:set(A). ∀x y a b:A.",
		Hypotheses: []string{
			"smooth_weierstrass(L, k, x, y, a, b)",
			"finite(k)",
		},
		Conclusion: "smooth_finite_curve(L, k, x, «curveChart0», «curveChart1», «curveOverlap»)",
	},
		func(
			arg *Argument,
			L field.FieldFact[on.L],
			k *Expr[Set[A]],
			x, y, a, b *Expr[A],
			smooth, finite Fact,
		) {
			arg.Show(
				"the datum is a curve over the x-line, k is finite and both charts are integrally closed in L",
				By(
					elliptic_curve.SmoothWeierstrassDatum.Read(smooth),
					smooth,
					finite,
					smooth_curve.SmoothFiniteFieldCurveDef,
					elliptic_curve.WeierstrassIsCurve.Read(L).At(k, x, y, a, b),
					WeierstrassChartsNormal.Read(L).At(k, x, y, a, b)))
		}),
})}
