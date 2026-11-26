// formula.go — the Cauchy integral formula on a disc.

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/registry"
)

// DifferenceQuotientHolomorphic — for f holomorphic on a set s holding w, the
// difference quotient at w extends to a function φ on all of ℂ with
// f(z) − f(w) = φ(z)·(z − w), continuous on s and holomorphic on s off w.
// Carathéodory's form of the derivative at w gives φ, continuous at w. Near a
// point z of s other than w, φ is the quotient (f(u) − f(w))/(u − w), which has
// a derivative at z by the quotient rule; so φ has one too, and is continuous
// there.
var DifferenceQuotientHolomorphic = differenceQuotientHolomorphicThm{family.Add(registry.ProofEntry{
	Name: "DifferenceQuotientHolomorphic",
	Key:  "prop_20ab8385f97c90b6",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(complex). ∀f:(complex → complex). ∀w:complex.",
		Hypotheses: []string{
			"holomorphic_on(s, f)",
			"w ∈ s",
		},
		Conclusion: "∃φ:complex → complex. " +
			"    (∀z:complex. f(z) - f(w) = φ(z) * (z - w)) ∧ " +
			"    complex_continuous_on(s, φ) ∧ " +
			"    holomorphic_on(s ∖ {w}, φ)",
	},
		func(
			arg *Argument,
			s *Expr[Set[Complex]],
			f *Arrow[Complex, Complex],
			w *Expr[Complex],
			holomorphic, wIn Fact,
		) {
			derivatives := arg.Unfolded(holomorphic, complex_derivative.HolomorphicOnDef)
			l, atW := arg.UnpackAs[Complex](GroupPremises(wIn, derivatives.At(w)), "l")
			φ, patched := arg.ObtainAs[Fun[Complex, Complex]](
				"by Carathéodory, f(z) − f(w) is φ(z)·(z − w) for a φ continuous at w with φ(w) = l",
				"∃φ:complex → complex. "+
					"    (∀z:complex. f(z) - f(w) = φ(z) * (z - w)) ∧ complex_continuous_at(φ, w) ∧ φ(w) = l",
				By(atW, complex_derivative.DerivativeCaratheodory.At(f, w, l)))
			parts := arg.Conjuncts(
				patched,
				"f(z) − f(w) is φ(z)·(z − w) for every z",
				"φ is continuous at w",
				"φ(w) is l")
			quotient := arg.TermAs[Fun[Complex, Complex]]("λu:complex. (f(u) - f(w)) / (u - w)")
			numerator := arg.TermAs[Fun[Complex, Complex]]("λu:complex. f(u) - f(w)")
			denominator := arg.TermAs[Fun[Complex, Complex]]("λu:complex. u - w")
			identity := arg.TermAs[Fun[Complex, Complex]]("λu:complex. u")
			constantW := arg.TermAs[Fun[Complex, Complex]]("λu:complex. w")
			constantF := arg.TermAs[Fun[Complex, Complex]]("λu:complex. f(w)")
			zero, one := arg.TermAs[Complex]("&0"), arg.TermAs[Complex]("&1")
			away := arg.Have(
				"off w, φ has a derivative at each point of s",
				"∀z:complex. z ∈ s ∧ z ≠ w ⇒ ∃m:complex. complex_derivative_at(φ, z, m)",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					given := d.Assume()
					where := d.Conjuncts(
						given,
						"z lies in s",
						"z is not w")
					m, atZ := d.UnpackAs[Complex](GroupPremises(where[0], derivatives.At(z)), "m")
					step := d.TermAs[Complex]("z - w")
					gap := d.TermAs[Real]("|z - w|")
					nonzero := d.Have(
						"z − w is not 0",
						"z - w ≠ &0",
						ByArith(where[1]))
					apart := d.Have(
						"so z is at positive distance from w",
						"&0 < |z - w|",
						ByArith(nonzero, complex_abs.AbsPosIffNonzero.At(step)))
					agree := d.Have(
						"within |z − w| of z, φ is the difference quotient",
						"∀u:complex. |u - z| < |z - w| ⇒ φ(u) = (f(u) - f(w)) / (u - w)",
						Derive(func(e *Argument) {
							u := e.FixAs[Complex]("u")
							near := e.Assume()
							offset := e.TermAs[Complex]("u - w")
							notW := e.Have(
								"u is not w: |z − w| is at most |z − u| + |u − w|, where |z − u| = |u − z| is below |z − w|",
								"u - w ≠ &0",
								ByArith(
									near,
									complex_abs.AbsSubTriangle.At(z, u, w),
									complex_abs.AbsSubComm.At(z, u),
									complex_abs.AbsPosIffNonzero.At(offset)))
							e.Show(
								"φ(u)·(u − w) is f(u) − f(w)",
								ByArith(notW, Scaled(e.TermAs[Complex]("complex_inv(u - w)"), parts[0].At(u))))
						}))
					values := d.Have(
						"m − 0 is m, and 1 − 0 is 1",
						"m - &0 = m ∧ complex_of_real(&1) - &0 = &1",
						ByArith())
					top := d.Have(
						"f(u) − f(w), f less a constant, has derivative m − 0 = m at z",
						"complex_derivative_at(λu:complex. f(u) - f(w), z, m)",
						By(
							Normalized,
							values,
							atZ,
							complex_derivative.DerivativeConst.At(z, d.TermAs[Complex]("f(w)")),
							complex_derivative.DerivativeSub.At(f, constantF, z, m, zero)))
					bottom := d.Have(
						"u − w, the identity less a constant, has derivative 1 − 0 = 1 at z",
						"complex_derivative_at(λu:complex. u - w, z, &1)",
						By(
							values,
							complex_derivative.DerivativeId.At(z),
							complex_derivative.DerivativeConst.At(z, w),
							complex_derivative.DerivativeSub.At(identity, constantW, z, one, zero)))
					slope := d.TermAs[Complex]("(m * (z - w) - (f(z) - f(w)) * &1) / (z - w) ^ 2")
					d.Take(slope)
					d.Show(
						"by the quotient rule the difference quotient has "+
							"that derivative at z, and φ agrees with it near z",
						By(
							apart,
							agree,
							top,
							bottom,
							nonzero,
							complex_derivative.DerivativeDiv.At(numerator, denominator, z, m, one),
							complex_derivative.DerivativeLocal.At(φ, quotient, z, slope, gap)))
				}))
			holomorphicOff := arg.Have(
				"so φ is holomorphic on s without w",
				"holomorphic_on(s ∖ {w}, φ)",
				Unfold(complex_derivative.HolomorphicOnDef),
				BySets(away))
			continuousAt := arg.Have(
				"φ is continuous at each point of s",
				"∀z:complex. z ∈ s ⇒ complex_continuous_at(φ, z)",
				Derive(func(d *Argument) {
					z := d.FixAs[Complex]("z")
					zIn := d.Assume()
					d.Cases(d.Term("z = w"))
					d.When(
						"at w, by Carathéodory",
						func(e *Argument, same Fact) {
							e.Show(
								"φ is continuous at w",
								same.Rw(),
								By(parts[1]))
						})
					d.Otherwise(
						"elsewhere φ has a derivative",
						func(e *Argument, other Fact) {
							m, atZ := e.UnpackAs[Complex](GroupPremises(zIn, other, away.At(z)), "m")
							e.Show(
								"so is continuous there",
								By(atZ, complex_derivative.DerivativeContinuous.At(φ, z, m)))
						})
				}))
			arg.Take(φ)
			arg.Show(
				"φ will do",
				By(parts[0], holomorphicOff, continuousAt, complex_topology.ContinuousAtOn.At(s, φ)))
		}),
})}

// CauchyIntegralFormula — the Cauchy integral formula on a disc: for f
// holomorphic on the disc of radius R about c, and w inside the circle of
// radius r < R about c, the integral of f(z)/(z − w) round the circle is
// 2πi·f(w). The disc is open and convex, and the difference quotient at w
// extends to φ, continuous on the disc and holomorphic there off w; so φ has a
// primitive on the disc, and its integral round the circle, which lies in the
// disc and is closed, is 0. The circle misses w, so on it f(z)/(z − w) is
// φ(z) + f(w)·(z − w)⁻¹, and (z − w)⁻¹ integrates to 2πi round it.
var CauchyIntegralFormula = cauchyIntegralFormulaThm{family.Add(registry.ProofEntry{
	Name: "CauchyIntegralFormula",
	Key:  "prop_8cccbacf20647e0b",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c w:complex. ∀R r:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"r < R",
			"|w - c| < r",
		},
		Conclusion: "«circleInt»(λz:complex. f(z) / (z - w), c, r) = &(&2 * pi) * complex_i * f(w)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c, w *Expr[Complex],
			R, r *Expr[Real],
			holomorphic, smaller, inside Fact,
		) {
			disc := arg.TermAs[Set[Complex]]("«disc»(c, R)")
			value := arg.TermAs[Complex]("f(w)")
			reciprocal := arg.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv(z - w)")
			shifted := arg.TermAs[Fun[Complex, Complex]]("λz:complex. f(w) * complex_inv(z - w)")
			open := arg.Have(
				"the disc is open",
				"«disc»(c, R) ∈ complex_topology",
				By(complex_topology.DiscOpen.At(c, R)))
			convex := arg.Have(
				"and convex",
				"«convex»(«disc»(c, R))",
				By(At(DiscConvex, c, R)))
			centre := arg.Have(
				"w lies in the disc",
				"w ∈ «disc»(c, R)",
				By(arg.Have(
					"w is within R of c",
					"|w - c| < R",
					ByArith(inside, smaller))))
			φ, patched := arg.ObtainAs[Fun[Complex, Complex]](
				"the difference quotient at w extends to φ, continuous on the disc and holomorphic there off w",
				"∃φ:complex → complex. "+
					"    (∀z:complex. f(z) - f(w) = φ(z) * (z - w)) ∧ "+
					"    complex_continuous_on(«disc»(c, R), φ) ∧ "+
					"    holomorphic_on(«disc»(c, R) ∖ {w}, φ)",
				By(holomorphic, centre, DifferenceQuotientHolomorphic.At(disc, f, w)))
			parts := arg.Conjuncts(
				patched,
				"f(z) − f(w) is φ(z)·(z − w)",
				"φ is continuous on the disc",
				"φ is holomorphic on the disc off w")
			F, primitive := arg.ObtainAs[Fun[Complex, Complex]](
				"so φ has a primitive F on the convex open disc",
				"∃F:complex → complex. ∀z:complex. z ∈ «disc»(c, R) ⇒ complex_derivative_at(F, z, φ(z))",
				By(open, convex, parts[1], parts[2], ConvexPrimitive.At(disc, φ, w)))
			continuous := arg.Have(
				"the disc being open, φ is continuous at each of its points",
				"∀z:complex. z ∈ «disc»(c, R) ⇒ complex_continuous_at(φ, z)",
				By(open, parts[1], complex_topology.ContinuousOnOpenIff.At(disc, φ)))
			positive := arg.Have(
				"the radius r exceeds |w − c| ≥ 0, so is positive, and w is not on the circle",
				"&0 < r ∧ |w - c| ≠ r",
				ByArith(inside, complex_abs.AbsNonneg.At(arg.TermAs[Complex]("w - c"))))
			onCircle := arg.Have(
				"a point of the circle lies in the disc and is not w",
				"∀u:complex. |u - c| = r ⇒ u ∈ «disc»(c, R) ∧ u ≠ w",
				Derive(func(d *Argument) {
					d.FixAs[Complex]("u")
					on := d.Assume()
					within := d.Have(
						"u lies in the disc, r being less than R",
						"u ∈ «disc»(c, R)",
						ByArith(on, smaller))
					d.Show(
						"and is not w, which is not on the circle",
						By(Normalized, on, positive, within))
				}))
			primitiveOn := arg.Have(
				"on the circle, which lies in the disc, F has derivative φ and φ is continuous",
				"∀u:complex. |u - c| = r ⇒ complex_derivative_at(F, u, φ(u)) ∧ complex_continuous_at(φ, u)",
				By(onCircle, primitive, continuous))
			vanishes := arg.Have(
				"so φ integrates to 0 round the circle",
				"«circleInt»(φ, c, r) = &0",
				By(positive, primitiveOn, path_integral.CircleIntegralPrimitive.At(F, φ, c, r)))
			congruent := arg.Have(
				"on the circle f(u)/(u − w) is φ(u) + f(w)·(u − w)⁻¹",
				"∀u:complex. |u - c| = r ⇒ f(u) / (u - w) = φ(u) + f(w) * complex_inv(u - w)",
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					on := d.Assume()
					d.Show(
						"f(u) is f(w) + φ(u)·(u − w), and u is not w",
						ByArith(on, onCircle.At(u), Scaled(d.TermAs[Complex]("complex_inv(u - w)"), parts[0].At(u))))
				}))
			phiOn := arg.Have(
				"φ is continuous on the circle",
				"∀u:complex. |u - c| = r ⇒ complex_continuous_at(φ, u)",
				By(primitiveOn))
			reciprocalOn := arg.Have(
				"(z − w)⁻¹ is continuous on the circle, which misses w",
				"∀u:complex. |u - c| = r ⇒ complex_continuous_at(λz:complex. complex_inv(z - w), u)",
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					on := d.Assume()
					difference := d.Have(
						"z − w is continuous",
						"complex_continuous_at(λz:complex. z - w, u)",
						By(
							complex_topology.ContinuousAtId.At(u),
							complex_topology.ContinuousAtConst.At(u, w),
							complex_topology.ContinuousAtSub.At(
								d.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
								d.TermAs[Fun[Complex, Complex]]("λz:complex. w"),
								u)))
					apart := d.Have(
						"and not 0 at u, which is not w",
						"u - w ≠ &0",
						ByArith(on, onCircle.At(u)))
					d.Show(
						"so its inverse is continuous at u",
						By(
							difference,
							apart,
							complex_topology.ContinuousAtInv.At(d.TermAs[Fun[Complex, Complex]]("λz:complex. z - w"), u)))
				}))
			shiftedOn := arg.Have(
				"and so is f(w) times it",
				"∀u:complex. |u - c| = r ⇒ complex_continuous_at(λz:complex. f(w) * complex_inv(z - w), u)",
				Derive(func(d *Argument) {
					u := d.FixAs[Complex]("u")
					on := d.Assume()
					d.Show(
						"a constant times a continuous function is continuous",
						By(
							on,
							reciprocalOn.At(u),
							complex_topology.ContinuousAtConst.At(u, value),
							complex_topology.ContinuousAtMul.At(
								d.TermAs[Fun[Complex, Complex]]("λz:complex. f(w)"), reciprocal, u)))
				}))
			arg.Show(
				"so the integral of f(z)/(z − w) is that of φ, which is 0, plus f(w) times 2πi",
				ByArith(
					positive,
					congruent,
					phiOn,
					reciprocalOn,
					shiftedOn,
					vanishes,
					inside,
					path_integral.CircleIntegralCongruence.At(
						arg.TermAs[Fun[Complex, Complex]]("λz:complex. f(z) / (z - w)"),
						arg.TermAs[Fun[Complex, Complex]]("λz:complex. φ(z) + f(w) * complex_inv(z - w)"),
						c,
						r),
					path_integral.CircleIntegralAdd.At(φ, shifted, c, r),
					path_integral.CircleIntegralScale.At(reciprocal, c, r, value),
					CircleWindingInside.At(c, w, r)))
		}),
})}
