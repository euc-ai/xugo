// arcsine.go — the arcsine: the sine takes every value of ⟦−1, 1⟧ on
// ⟦−π/2, π/2⟧, so arcsin y is a point there where the sine is y; the sine
// rises strictly there, so it is the only one, arcsin undoes the sine on
// the interval, and inside ⟬−1, 1⟭ its derivative is the reciprocal of
// the sine's, cos(arcsin y) = √(1 − y²).

package real_inverse_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

// ArcsinSpec — for y in ⟦−1, 1⟧, arcsin y is a point of ⟦−π/2, π/2⟧
// where the sine is y: it is chosen among those points, and the sine
// takes every value of ⟦−1, 1⟧ there, so there is one.
var ArcsinSpec = arcsinSpecThm{family.Add(registry.ProofEntry{
	Name: "ArcsinSpec",
	Key:  "prop_617958592d4d47c2",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"|y| ≤ &1",
		},
		Conclusion: "-(pi / &2) ≤ arcsin(y) ∧ arcsin(y) ≤ pi / &2 ∧ sin(arcsin(y)) = y",
	},
		func(arg *Argument, y *Expr[Real], bounded Fact) {
			arg.Have(
				"y lies in ⟦−1, 1⟧, so the sine is y somewhere in ⟦−π/2, π/2⟧",
				"∃x:real. -(pi / &2) ≤ x ∧ x ≤ pi / &2 ∧ sin(x) = y",
				By(bounded, real_trigonometry.SinSurjectiveHalfPi.At(y)))
			arg.Show(
				"and arcsin y is chosen among those points",
				Unfold(RealArcsinDef))
		}),
})}

// ArcsinBounds — for y in ⟦−1, 1⟧ the arcsine lies in ⟦−π/2, π/2⟧, by
// its specification.
var ArcsinBounds = arcsinBoundsThm{family.Add(registry.ProofEntry{
	Name: "ArcsinBounds",
	Key:  "prop_aadfe87441933a9",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"|y| ≤ &1",
		},
		Conclusion: "-(pi / &2) ≤ arcsin(y) ∧ arcsin(y) ≤ pi / &2",
	},
		func(arg *Argument, y *Expr[Real], bounded Fact) {
			arg.Show(
				"arcsin y is a point of ⟦−π/2, π/2⟧",
				By(bounded, ArcsinSpec.At(y)))
		}),
})}

// SinArcsin — on ⟦−1, 1⟧ the arcsine is a right inverse of the sine, by
// its specification.
var SinArcsin = sinArcsinThm{family.Add(registry.ProofEntry{
	Name: "SinArcsin",
	Key:  "prop_119aded658fb12c6",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"|y| ≤ &1",
		},
		Conclusion: "sin(arcsin(y)) = y",
	},
		func(arg *Argument, y *Expr[Real], bounded Fact) {
			arg.Show(
				"arcsin y is a point where the sine is y",
				By(bounded, ArcsinSpec.At(y)))
		}),
})}

// ArcsinSin — the arcsine undoes the sine on ⟦−π/2, π/2⟧: arcsin(sin x)
// lies in the interval and has the sine of x, and the sine rises strictly
// there, so it is neither below x nor above it.
var ArcsinSin = arcsinSinThm{family.Add(registry.ProofEntry{
	Name: "ArcsinSin",
	Key:  "prop_980d9bb27eb29a05",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"-(pi / &2) ≤ x",
			"x ≤ pi / &2",
		},
		Conclusion: "arcsin(sin(x)) = x",
	},
		func(arg *Argument, x *Expr[Real], within Fact) {
			s, back := arg.TermAs[Real]("sin(x)"), arg.TermAs[Real]("arcsin(sin(x))")
			arg.Show(
				"sin(arcsin(sin x)) = sin x, and a strictly increasing sine takes that value at x alone",
				ByArith(
					within,
					real_trigonometry.SinAbsLessEqOne.At(x),
					ArcsinSpec.At(s),
					real_trigonometry.SinStrictlyIncreasingHalfPi.At(back, x),
					real_trigonometry.SinStrictlyIncreasingHalfPi.At(x, back)))
		}),
})}

// ArcsinDerivative — inside ⟬−1, 1⟭ the arcsine has derivative
// 1/√(1 − y²). There arcsin y is no end of ⟦−π/2, π/2⟧, where the sine is
// ±1 ≠ y, so the cosine is positive at it, and its square is
// 1 − sin² = 1 − y²: the sine has derivative cos(arcsin y) = √(1 − y²),
// not 0, at arcsin y. The arcsine undoes the sine on the ball of radius
// 1 − |y| about y, inside ⟬−1, 1⟭, and it is continuous at y, as the
// inverse of a function strictly increasing on ⟦−π/2, π/2⟧, the ball of
// radius π/2 − |arcsin y| about arcsin y lying inside that interval.
var ArcsinDerivative = arcsinDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ArcsinDerivative",
	Key:  "prop_33122073ce32c1b7",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"|y| < &1",
		},
		Conclusion: "real_derivative_at(real_arcsin, y, real_inv(real_sqrt(&1 - real_pow(y, 2))))",
	},
		func(arg *Argument, y *Expr[Real], inside Fact) {
			sin, arcsin := arg.TermAs[Fun[Real, Real]]("real_sin"), arg.TermAs[Fun[Real, Real]]("real_arcsin")
			a := arg.TermAs[Real]("arcsin(y)")
			spec := arg.Have(
				"arcsin y lies in ⟦−π/2, π/2⟧, and the sine is y there",
				"-(pi / &2) ≤ arcsin(y) ∧ arcsin(y) ≤ pi / &2 ∧ sin(arcsin(y)) = y",
				ByArith(inside, ArcsinSpec.At(y)))
			ends := arg.Have(
				"the sine is 1 at π/2 and −1 at −π/2, neither of them y",
				"sin(pi / &2) ≠ y ∧ sin(-(pi / &2)) ≠ y",
				Simp(Fwd(real_trigonometry.SinNeg), Fwd(real_trigonometry.SinPiHalf)),
				ByArith(inside))
			notTop := arg.Unless(
				arg.Term("arcsin(y) = pi / &2"),
				"at π/2 the sine is 1, not y",
				Given(func(b *Argument, top Fact) {
					b.Show(
						"sin(arcsin y) would be sin(π/2)",
						By(Normalized, top, spec, ends))
				}))
			notBottom := arg.Unless(
				arg.Term("arcsin(y) = -(pi / &2)"),
				"at −π/2 the sine is −1, not y",
				Given(func(b *Argument, bottom Fact) {
					b.Show(
						"sin(arcsin y) would be sin(−π/2)",
						By(Normalized, bottom, spec, ends))
				}))
			strict := arg.Have(
				"so arcsin y lies strictly inside, in ⟬−π/2, π/2⟭",
				"-(pi / &2) < arcsin(y) ∧ arcsin(y) < pi / &2",
				ByArith(notTop, notBottom, spec))
			root := arg.Have(
				"there the cosine is positive and its square is 1 − sin² = 1 − y², so it is √(1 − y²)",
				"&0 < cos(arcsin(y)) ∧ cos(arcsin(y)) = real_sqrt(&1 - real_pow(y, 2))",
				ByArith(
					strict,
					spec,
					real_trigonometry.CosPositiveHalfPi.At(a),
					real_trigonometry.SinSquareAddCosSquare.At(a),
					real_sqrt.SqrtUnique.At(
						arg.TermAs[Real]("&1 - real_pow(y, 2)"), arg.TermAs[Real]("cos(arcsin(y))"))))
			within := arg.Have(
				"the ball of radius 1 − |y| about y lies inside ⟦−1, 1⟧",
				"∀z:real. |z - y| < &1 - |y| ⇒ |z| ≤ &1",
				arg.ForEach(func(z *Expr[Real]) Action { return ByArith() }))
			ball := arg.Have(
				"the ball of radius π/2 − |arcsin y| about arcsin y lies inside ⟦−π/2, π/2⟧",
				"∀x:real. |x - arcsin(y)| < pi / &2 - |arcsin(y)| ⇒ -(pi / &2) ≤ x ∧ x ≤ pi / &2",
				arg.ForEach(func(x *Expr[Real]) Action { return ByArith(spec) }))
			rising := arg.Have(
				"the sine is strictly increasing on ⟦−π/2, π/2⟧",
				"real_strictly_increasing_on(⟦-(pi / &2), pi / &2⟧, real_sin)",
				Unfold(real_continuous.RealStrictlyIncreasingOnDef),
				By(real_trigonometry.SinStrictlyIncreasingHalfPi))
			continuous := arg.Have(
				"so the arcsine, inverse to the strictly increasing sine, is continuous at y",
				"real_continuous_at(real_arcsin, y)",
				ByArith(
					within,
					ArcsinSpec,
					ball,
					inside,
					strict,
					rising,
					real_continuous.MonotoneInverseContinuous.At(sin, arcsin,
						arg.TermAs[Set[Real]]("⟦-(pi / &2), pi / &2⟧"), y,
						arg.TermAs[Real]("&1 - |y|"), arg.TermAs[Real]("pi / &2 - |arcsin(y)|"))))
			arg.Show(
				"the derivative of the inverse is the reciprocal of cos(arcsin y) = √(1 − y²), which is not 0",
				ByArith(
					within,
					ArcsinSpec,
					continuous,
					inside,
					root,
					real_trigonometry.SinDerivative.At(a),
					real_derivative.DerivativeInverse.At(sin, arcsin, y,
						arg.TermAs[Real]("real_sqrt(&1 - real_pow(y, 2))"), arg.TermAs[Real]("&1 - |y|"))))
		}),
})}
