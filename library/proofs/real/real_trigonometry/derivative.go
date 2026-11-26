// derivative.go — the derivatives of the sine and the cosine, from the
// addition formulas and the bounds near 0.

package real_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// SinDerivative — the derivative of the sine at c is cos c, by the
// quadratic-remainder criterion. The addition formula writes the excess
// of the increment sin(c + h) − sin c over its linear part cos c·h as
// sin c·(cos h − 1) + cos c·(sin h − h); for |h| < 1 the bounds near 0
// make each remainder at most h² in size, and the sine and the cosine
// are at most 1 in size, so the excess is at most 2h² in size.
var SinDerivative = sinDerivativeThm{family.Add(registry.ProofEntry{
	Name: "SinDerivative",
	Key:  "prop_347943bd84fad93d",
	Build: family.Theorem("∀c:real. real_derivative_at(real_sin, c, cos(c))",
		func(arg *Argument, c *Expr[Real]) {
			one := arg.TermAs[Real]("&1")
			bound := arg.Have(
				"on |h| < 1 the increment sin(c + h) − sin c is its linear part cos c·h to within 2h²",
				"∀h:real. |h| < &1 ⇒ |sin(c + h) - sin(c) - cos(c) * h| ≤ &2 * real_pow(h, 2)",
				Derive(func(d *Argument) {
					h := d.FixAs[Real]()
					near := d.Assume()
					square := d.TermAs[Real]("real_pow(h, 2)")
					split := d.Have(
						"by the addition formula the excess over the linear part is sin c·(cos h − 1) + cos c·(sin h − h)",
						"sin(c + h) - sin(c) - cos(c) * h = sin(c) * (cos(h) - &1) + cos(c) * (sin(h) - h)",
						ByArith(SinAdd.At(c, h)))
					sinTerm := d.Have(
						"|sin c| ≤ 1 and, as |h| ≤ 1, |cos h − 1| ≤ h²: the sine's term is at most h² in size",
						"|sin(c) * (cos(h) - &1)| ≤ real_pow(h, 2)",
						ByArith(
							near,
							CosQuadraticBound.At(h),
							SinAbsLessEqOne.At(c),
							real_order_ring.LessEqMul2.At(d.TermAs[Real]("|sin(c)|"), one,
								d.TermAs[Real]("|cos(h) - &1|"), square),
							real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("sin(c)")),
							real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("cos(h) - &1"))))
					cosTerm := d.Have(
						"|cos c| ≤ 1 and |sin h − h| ≤ h² likewise: the cosine's term is at most h² in size",
						"|cos(c) * (sin(h) - h)| ≤ real_pow(h, 2)",
						ByArith(
							near,
							SinQuadraticBound.At(h),
							CosAbsLessEqOne.At(c),
							real_order_ring.LessEqMul2.At(d.TermAs[Real]("|cos(c)|"), one,
								d.TermAs[Real]("|sin(h) - h|"), square),
							real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("cos(c)")),
							real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("sin(h) - h"))))
					d.Show(
						"the sum of the two terms is at most the sum of their sizes, 2h², in size",
						split.Rw(),
						ByArith(
							sinTerm,
							cosTerm,
							real_sgn_abs.AbsTriangle.At(d.TermAs[Real]("sin(c) * (cos(h) - &1)"),
								d.TermAs[Real]("cos(c) * (sin(h) - h)"))))
				}))
			arg.Show(
				"a first-order approximation with a quadratic remainder on a ball is a derivative",
				By(
					bound,
					real_derivative.DerivativeFromQuadraticRemainder.At(
						arg.TermAs[Fun[Real, Real]]("real_sin"),
						c,
						arg.TermAs[Real]("cos(c)"),
						arg.TermAs[Real]("&2"),
						one)))
		}),
})}

// CosDerivative — the derivative of the cosine at c is −sin c, by the
// quadratic-remainder criterion. The addition formula writes the excess
// of the increment cos(c + h) − cos c over its linear part −sin c·h as
// cos c·(cos h − 1) − sin c·(sin h − h); for |h| < 1 the bounds near 0
// make each remainder at most h² in size, and the sine and the cosine
// are at most 1 in size, so the excess is at most 2h² in size.
var CosDerivative = cosDerivativeThm{family.Add(registry.ProofEntry{
	Name: "CosDerivative",
	Key:  "prop_6db98824740aad2e",
	Build: family.Theorem("∀c:real. real_derivative_at(real_cos, c, -sin(c))",
		func(arg *Argument, c *Expr[Real]) {
			one := arg.TermAs[Real]("&1")
			bound := arg.Have(
				"on |h| < 1 the increment cos(c + h) − cos c is its linear part −sin c·h to within 2h²",
				"∀h:real. |h| < &1 ⇒ |cos(c + h) - cos(c) - -sin(c) * h| ≤ &2 * real_pow(h, 2)",
				Derive(func(d *Argument) {
					h := d.FixAs[Real]()
					near := d.Assume()
					square := d.TermAs[Real]("real_pow(h, 2)")
					split := d.Have(
						"by the addition formula the excess over the linear part is cos c·(cos h − 1) − sin c·(sin h − h)",
						"cos(c + h) - cos(c) - -sin(c) * h = cos(c) * (cos(h) - &1) - sin(c) * (sin(h) - h)",
						ByArith(CosAdd.At(c, h)))
					cosTerm := d.Have(
						"|cos c| ≤ 1 and, as |h| ≤ 1, |cos h − 1| ≤ h²: the cosine's term is at most h² in size",
						"|cos(c) * (cos(h) - &1)| ≤ real_pow(h, 2)",
						ByArith(
							near,
							CosQuadraticBound.At(h),
							CosAbsLessEqOne.At(c),
							real_order_ring.LessEqMul2.At(d.TermAs[Real]("|cos(c)|"), one,
								d.TermAs[Real]("|cos(h) - &1|"), square),
							real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("cos(c)")),
							real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("cos(h) - &1"))))
					sinTerm := d.Have(
						"|sin c| ≤ 1 and |sin h − h| ≤ h² likewise: the sine's term is at most h² in size",
						"|sin(c) * (sin(h) - h)| ≤ real_pow(h, 2)",
						ByArith(
							near,
							SinQuadraticBound.At(h),
							SinAbsLessEqOne.At(c),
							real_order_ring.LessEqMul2.At(d.TermAs[Real]("|sin(c)|"), one,
								d.TermAs[Real]("|sin(h) - h|"), square),
							real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("sin(c)")),
							real_sgn_abs.AbsNonneg.At(d.TermAs[Real]("sin(h) - h"))))
					d.Show(
						"the difference of the two terms is at most the sum of their sizes, 2h², in size",
						split.Rw(),
						ByArith(
							cosTerm,
							sinTerm,
							real_sgn_abs.AbsTriangle.At(d.TermAs[Real]("cos(c) * (cos(h) - &1)"),
								d.TermAs[Real]("-(sin(c) * (sin(h) - h))"))))
				}))
			arg.Show(
				"a first-order approximation with a quadratic remainder on a ball is a derivative",
				By(
					bound,
					real_derivative.DerivativeFromQuadraticRemainder.At(
						arg.TermAs[Fun[Real, Real]]("real_cos"),
						c,
						arg.TermAs[Real]("-sin(c)"),
						arg.TermAs[Real]("&2"),
						one)))
		}),
})}
