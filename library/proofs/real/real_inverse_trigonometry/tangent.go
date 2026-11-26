// tangent.go — the tangent on ⟬−π/2, π/2⟭: it is odd, its derivative is
// 1 + tan², so it is continuous and strictly increasing there, and it
// takes every real value, since near π/2 it is cos h / sin h ≥ 1/(2h).

package real_inverse_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

// TanNeg — the tangent is odd: the sine is odd and the cosine even, so
// tan(−x) = −sin x / cos x.
var TanNeg = tanNegThm{family.Add(registry.ProofEntry{
	Name: "TanNeg",
	Key:  "prop_28a5e9d216e19dee",
	Build: family.Theorem("∀x:real. tan(-x) = -tan(x)",
		func(arg *Argument, x *Expr[Real]) {
			arg.Show(
				"tan(−x) = sin(−x)/cos(−x) = −sin x / cos x",
				Unfold(RealTanDef),
				Simp(Fwd(real_trigonometry.SinNeg), Fwd(real_trigonometry.CosNeg)),
				ByArith())
		}),
})}

// TanDerivative — where the cosine is not 0, the tangent has derivative
// 1 + tan²: by the quotient rule its derivative is
// (cos·cos − sin·(−sin))/cos², which is 1 + (sin/cos)².
var TanDerivative = tanDerivativeThm{family.Add(registry.ProofEntry{
	Name: "TanDerivative",
	Key:  "prop_fc43ca13e5b0e4cd",
	Build: family.Theorem(Statement{
		Binders: "∀c:real.",
		Hypotheses: []string{
			"cos(c) ≠ &0",
		},
		Conclusion: "real_derivative_at(real_tan, c, &1 + real_pow(tan(c), 2))",
	},
		func(arg *Argument, c *Expr[Real], nonzero Fact) {
			sin, cos := arg.TermAs[Fun[Real, Real]]("real_sin"), arg.TermAs[Fun[Real, Real]]("real_cos")
			quotient := arg.Have(
				"by the quotient rule, sin/cos has derivative (cos c·cos c − sin c·(−sin c))/cos² c at c",
				"real_derivative_at(λx:real. sin(x) / cos(x), "+
					"    c, "+
					"    (cos(c) * cos(c) - sin(c) * -sin(c)) / real_pow(cos(c), 2))",
				By(
					nonzero,
					real_trigonometry.SinDerivative.At(c),
					real_trigonometry.CosDerivative.At(c),
					real_derivative.DerivativeDiv.At(sin, cos, c,
						arg.TermAs[Real]("cos(c)"), arg.TermAs[Real]("-sin(c)"))))
			value := arg.Have(
				"which is (cos² c + sin² c)/cos² c = 1 + (sin c / cos c)²",
				"(cos(c) * cos(c) - sin(c) * -sin(c)) / real_pow(cos(c), 2) = &1 + real_pow(sin(c) / cos(c), 2)",
				ByArith(nonzero))
			arg.Show(
				"the tangent is sin/cos",
				Unfold(RealTanDef),
				By(value, quotient))
		}),
})}

// TanDerivativeHalfPi — inside ⟬−π/2, π/2⟭ the tangent has derivative
// 1 + tan²: the cosine is positive there, so not 0.
var TanDerivativeHalfPi = tanDerivativeHalfPiThm{family.Add(registry.ProofEntry{
	Name: "TanDerivativeHalfPi",
	Key:  "prop_f62df70b1e8de6fa",
	Build: family.Theorem(Statement{
		Binders: "∀t:real.",
		Hypotheses: []string{
			"-(pi / &2) < t",
			"t < pi / &2",
		},
		Conclusion: "real_derivative_at(real_tan, t, &1 + real_pow(tan(t), 2))",
	},
		func(arg *Argument, t *Expr[Real], inside Fact) {
			arg.Show(
				"the cosine is positive inside ⟬−π/2, π/2⟭, so not 0",
				ByArith(inside, TanDerivative.At(t), real_trigonometry.CosPositiveHalfPi.At(t)))
		}),
})}

// TanContinuousOn — the tangent is continuous on every closed interval
// inside ⟬−π/2, π/2⟭: it has a derivative at every point of it.
var TanContinuousOn = tanContinuousOnThm{family.Add(registry.ProofEntry{
	Name: "TanContinuousOn",
	Key:  "prop_38ad5ae2ccb72328",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real.",
		Hypotheses: []string{
			"-(pi / &2) < a",
			"b < pi / &2",
		},
		Conclusion: "real_continuous_on(⟦a, b⟧, real_tan)",
	},
		func(arg *Argument, a, b *Expr[Real], inside Fact) {
			arg.Show(
				"⟦a, b⟧ lies inside ⟬−π/2, π/2⟭, where the tangent has a "+
					"derivative at every point, so it is continuous on ⟦a, b⟧",
				ByArith(
					inside,
					TanDerivativeHalfPi,
					real_derivative.DerivativeContinuousOn.At(
						arg.TermAs[Fun[Real, Real]]("real_tan"),
						arg.TermAs[Fun[Real, Real]]("λt:real. &1 + real_pow(tan(t), 2)"),
						arg.TermAs[Set[Real]]("⟦a, b⟧"))))
		}),
})}

// TanStrictlyIncreasing — the tangent rises strictly on ⟬−π/2, π/2⟭:
// between two points x < y of the interval it is continuous, and its
// derivative 1 + tan² is positive.
var TanStrictlyIncreasing = tanStrictlyIncreasingThm{family.Add(registry.ProofEntry{
	Name: "TanStrictlyIncreasing",
	Key:  "prop_3af1aa25bae0843a",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"-(pi / &2) < x",
			"x < y",
			"y < pi / &2",
		},
		Conclusion: "tan(x) < tan(y)",
	},
		func(arg *Argument, x, y *Expr[Real], order Fact) {
			arg.Show(
				"the tangent is continuous on ⟦x, y⟧, its derivative 1 + "+
					"tan² there is positive, and such a function rises strictly",
				ByArith(
					order,
					TanDerivativeHalfPi,
					TanContinuousOn.At(x, y),
					real_derivative.DerivativePositiveStrictlyIncreasing.At(
						arg.TermAs[Fun[Real, Real]]("real_tan"),
						arg.TermAs[Fun[Real, Real]]("λt:real. &1 + real_pow(tan(t), 2)"),
						x, y, x, y)))
		}),
})}

// TanSurjective — the tangent takes every value y on ⟬−π/2, π/2⟭. Take
// h = π/(8(|y| + 1)), so 0 < h < 1/2 and h·|y| < 1/2. Near π/2 the
// tangent is tan(π/2 − h) = cos h / sin h, and sin h ≤ h while
// cos h ≥ 1 − h²/2 > 1/2, so |y|·sin h < 1/2 < cos h: the tangent exceeds
// |y| at π/2 − h, and by oddness it is below −|y| at −(π/2 − h). It is
// continuous between the two, so the intermediate value theorem finds y
// as a value there.
var TanSurjective = tanSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "TanSurjective",
	Key:  "prop_35daa0f2faefed80",
	Build: family.Theorem("∀y:real. ∃x:real. -(pi / &2) < x ∧ x < pi / &2 ∧ tan(x) = y",
		func(arg *Argument, y *Expr[Real]) {
			h, hDef := arg.LetAs[Real]("h", "pi / (&8 * (|y| + &1))")
			divisor := arg.Have(
				"8(|y| + 1) is positive",
				"&0 < &8 * (|y| + &1)",
				ByArith())
			positive := arg.Have(
				"h is positive",
				"&0 < h",
				ByArith(hDef, divisor, real_trigonometry.PiBounds))
			small := arg.Have(
				"8h(|y| + 1) = π < 4, so h < 1/2, h·|y| < 1/2 and h ≤ π/8 < π/2",
				"h < &1 / &2 ∧ h * |y| < &1 / &2 ∧ h < pi / &2",
				ByArith(hDef, divisor, positive, real_trigonometry.PiBounds, real_sgn_abs.AbsNonneg.At(y)))
			end := arg.Have(
				"tan(π/2 − h) = sin(π/2 − h)/cos(π/2 − h) = cos h / sin h",
				"tan(pi / &2 - h) = cos(h) / sin(h)",
				Unfold(RealTanDef),
				Simp(Fwd(real_trigonometry.SinSubHalfPi), Fwd(real_trigonometry.CosSubHalfPi)),
				Refl())
			sine := arg.Have(
				"0 < sin h ≤ h, h lying in ⟬0, 2⟭",
				"&0 < sin(h) ∧ sin(h) ≤ h",
				ByArith(
					positive,
					small,
					real_trigonometry.SinPositive.At(h),
					real_trigonometry.SinTaylorBounds.At(h)))
			cosine := arg.Have(
				"cos h ≥ 1 − h²/2 > 1/2, as h < 1/2",
				"&1 / &2 < cos(h)",
				ByArith(positive, small, real_trigonometry.CosTaylorBounds.At(h)))
			steep := arg.Have(
				"|y|·sin h ≤ |y|·h < 1/2 < cos h, so the tangent exceeds |y| at π/2 − h",
				"|y| < tan(pi / &2 - h)",
				ByArith(end, small, sine, cosine, real_sgn_abs.AbsNonneg.At(y)))
			a, b := arg.TermAs[Real]("-(pi / &2 - h)"), arg.TermAs[Real]("pi / &2 - h")
			ends := arg.Have(
				"by oddness tan(−(π/2 − h)) = −tan(π/2 − h) < −|y| ≤ y ≤ |y| < tan(π/2 − h)",
				"-(pi / &2 - h) ≤ pi / &2 - h ∧ tan(-(pi / &2 - h)) ≤ y ∧ y ≤ tan(pi / &2 - h)",
				ByArith(small, steep, TanNeg.At(b)))
			onInterval := arg.Have(
				"the tangent is continuous on ⟦−(π/2 − h), π/2 − h⟧, which lies inside ⟬−π/2, π/2⟭",
				"real_continuous_on(⟦-(pi / &2 - h), pi / &2 - h⟧, real_tan)",
				ByArith(positive, TanContinuousOn.At(a, b)))
			x, found := arg.ObtainAs[Real](
				"so it takes the value y there, by the intermediate value theorem",
				"∃x:real. -(pi / &2 - h) ≤ x ∧ x ≤ pi / &2 - h ∧ tan(x) = y",
				By(
					ends,
					onInterval,
					real_continuous.IntermediateValue.At(arg.TermAs[Fun[Real, Real]]("real_tan"), a, b, y)))
			arg.Take(x)
			arg.Show(
				"and that interval lies inside ⟬−π/2, π/2⟭, h being positive",
				ByArith(positive, found))
		}),
})}

// TanPiQuarter — the tangent is 1 at π/4, where the sine and the cosine
// agree and the cosine is positive.
var TanPiQuarter = tanPiQuarterThm{family.Add(registry.ProofEntry{
	Name: "TanPiQuarter",
	Key:  "prop_87e7634e4c261d16",
	Build: family.Theorem("tan(pi / &4) = &1",
		func(arg *Argument) {
			arg.Show(
				"tan(π/4) = sin(π/4)/cos(π/4) = 1, as sin(π/4) = cos(π/4) > 0",
				Unfold(RealTanDef),
				ByArith(
					real_trigonometry.PiBounds,
					real_trigonometry.SinEqCosPiQuarter,
					real_trigonometry.CosPositiveHalfPi.At(arg.TermAs[Real]("pi / &4"))))
		}),
})}
