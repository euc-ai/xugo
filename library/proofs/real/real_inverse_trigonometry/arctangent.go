// arctangent.go — the arctangent: the tangent takes every value on
// ⟬−π/2, π/2⟭, so arctan y is a point there where the tangent is y; the
// tangent rises strictly there, so it is the only one, arctan undoes the
// tangent on the interval, and its derivative is the reciprocal of the
// tangent's, 1/(1 + y²).

package real_inverse_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

// ArctanSpec — arctan y is a point of ⟬−π/2, π/2⟭ where the tangent is y:
// it is chosen among those points, and the tangent takes every value
// there, so there is one.
var ArctanSpec = arctanSpecThm{family.Add(registry.ProofEntry{
	Name: "ArctanSpec",
	Key:  "prop_f7795404e88a3668",
	Build: family.Theorem("∀y:real. -(pi / &2) < arctan(y) ∧ arctan(y) < pi / &2 ∧ tan(arctan(y)) = y",
		func(arg *Argument, y *Expr[Real]) {
			arg.Show(
				"the tangent is y somewhere in ⟬−π/2, π/2⟭, and arctan y is chosen among those points",
				Cite(TanSurjective, y),
				Unfold(RealArctanDef))
		}),
})}

// ArctanBounds — the arctangent lies in ⟬−π/2, π/2⟭, by its
// specification.
var ArctanBounds = arctanBoundsThm{family.Add(registry.ProofEntry{
	Name: "ArctanBounds",
	Key:  "prop_a5d8497bb9b9c665",
	Build: family.Theorem("∀y:real. -(pi / &2) < arctan(y) ∧ arctan(y) < pi / &2",
		func(arg *Argument, y *Expr[Real]) {
			arg.Show(
				"arctan y is a point of ⟬−π/2, π/2⟭",
				By(ArctanSpec.At(y)))
		}),
})}

// TanArctan — the arctangent is a right inverse of the tangent, by its
// specification.
var TanArctan = tanArctanThm{family.Add(registry.ProofEntry{
	Name: "TanArctan",
	Key:  "prop_138499a0dea2b544",
	Build: family.Theorem("∀y:real. tan(arctan(y)) = y",
		func(arg *Argument, y *Expr[Real]) {
			arg.Show(
				"arctan y is a point where the tangent is y",
				By(ArctanSpec.At(y)))
		}),
})}

// ArctanTan — the arctangent undoes the tangent on ⟬−π/2, π/2⟭: arctan(tan x)
// lies in the interval and has the tangent of x, and the tangent rises
// strictly there, so it is neither below x nor above it.
var ArctanTan = arctanTanThm{family.Add(registry.ProofEntry{
	Name: "ArctanTan",
	Key:  "prop_612bf5182b6c2014",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"-(pi / &2) < x",
			"x < pi / &2",
		},
		Conclusion: "arctan(tan(x)) = x",
	},
		func(arg *Argument, x *Expr[Real], within Fact) {
			t, back := arg.TermAs[Real]("tan(x)"), arg.TermAs[Real]("arctan(tan(x))")
			arg.Show(
				"tan(arctan(tan x)) = tan x, and a strictly increasing tangent takes that value at x alone",
				ByArith(
					within,
					ArctanSpec.At(t),
					TanStrictlyIncreasing.At(back, x),
					TanStrictlyIncreasing.At(x, back)))
		}),
})}

// ArctanOne — the arctangent of 1 is π/4, where the tangent is 1.
var ArctanOne = arctanOneThm{family.Add(registry.ProofEntry{
	Name: "ArctanOne",
	Key:  "prop_738b4f62bd16d5eb",
	Build: family.Theorem("arctan(&1) = pi / &4",
		func(arg *Argument) {
			arg.Show(
				"π/4 lies in ⟬−π/2, π/2⟭ and tan(π/4) = 1, so arctan 1 = arctan(tan(π/4)) = π/4",
				ByArith(real_trigonometry.PiBounds, TanPiQuarter, ArctanTan.At(arg.TermAs[Real]("pi / &4"))))
		}),
})}

// ArctanZero — the arctangent of 0 is 0: 0 lies in ⟬−π/2, π/2⟭, where the
// arctangent undoes the tangent, and the tangent of 0 is 0.
var ArctanZero = arctanZeroThm{family.Add(registry.ProofEntry{
	Name: "ArctanZero",
	Key:  "prop_64696a7d8021b92e",
	Build: family.Theorem("arctan(&0) = &0",
		func(arg *Argument) {
			zero := arg.TermAs[Real]("&0")
			arg.Show(
				"tan 0 = sin 0 / cos 0 = 0/1 = 0, and 0 lies in ⟬−π/2, π/2⟭, so arctan 0 = arctan(tan 0) = 0",
				ByArith(
					real_trigonometry.PiBounds,
					RealTanDef.At(zero),
					real_trigonometry.SinZero,
					real_trigonometry.CosZero,
					ArctanTan.At(zero)))
		}),
})}

// ArctanDerivative — the arctangent has derivative 1/(1 + y²) at every y.
// It is the inverse of the tangent, which has derivative
// 1 + tan²(arctan y) = 1 + y², never 0, at arctan y; and it is continuous
// at y, as the inverse of a function strictly increasing on
// ⟬−π/2, π/2⟭, the ball of radius π/2 − |arctan y| about arctan y lying
// inside that interval. Both laws ask that the tangent undo the
// arctangent on some ball about y; it does so at every point, so any
// radius serves, and the proof takes 1.
var ArctanDerivative = arctanDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ArctanDerivative",
	Key:  "prop_335f95de3a900d18",
	Build: family.Theorem("∀y:real. real_derivative_at(real_arctan, y, real_inv(&1 + real_pow(y, 2)))",
		func(arg *Argument, y *Expr[Real]) {
			tan, arctan := arg.TermAs[Fun[Real, Real]]("real_tan"), arg.TermAs[Fun[Real, Real]]("real_arctan")
			a := arg.TermAs[Real]("arctan(y)")
			spec := ArctanSpec.At(y)
			slope := arg.Have(
				"arctan y lies in ⟬−π/2, π/2⟭, so the tangent has derivative 1 + tan²(arctan y) = 1 + y² there",
				"real_derivative_at(real_tan, arctan(y), &1 + real_pow(y, 2))",
				ByArith(spec, TanDerivativeHalfPi.At(a)))
			ball := arg.Have(
				"the ball of radius π/2 − |arctan y| about arctan y lies inside ⟬−π/2, π/2⟭",
				"∀x:real. |x - arctan(y)| < pi / &2 - |arctan(y)| ⇒ -(pi / &2) < x ∧ x < pi / &2",
				arg.ForEach(func(x *Expr[Real]) Action { return ByArith(spec) }))
			rising := arg.Have(
				"the tangent is strictly increasing on ⟬−π/2, π/2⟭",
				"real_strictly_increasing_on(⟬-(pi / &2), pi / &2⟭, real_tan)",
				Unfold(real_continuous.RealStrictlyIncreasingOnDef),
				By(TanStrictlyIncreasing))
			continuous := arg.Have(
				"so the arctangent, inverse to the strictly increasing tangent, is continuous at y",
				"real_continuous_at(real_arctan, y)",
				ByArith(
					ball,
					ArctanSpec,
					spec,
					rising,
					real_continuous.MonotoneInverseContinuous.At(tan, arctan,
						arg.TermAs[Set[Real]]("⟬-(pi / &2), pi / &2⟭"), y,
						arg.TermAs[Real]("&1"), arg.TermAs[Real]("pi / &2 - |arctan(y)|"))))
			arg.Show(
				"the derivative of the inverse is the reciprocal of 1 + y², which is not 0",
				ByArith(
					slope,
					continuous,
					TanArctan,
					real_derivative.DerivativeInverse.At(tan, arctan, y,
						arg.TermAs[Real]("&1 + real_pow(y, 2)"), arg.TermAs[Real]("&1"))))
		}),
})}
