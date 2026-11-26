// maximum.go — the mean value property and the maximum modulus principle on a
// disc. A function holomorphic on a disc has parts continuous along every
// circle inside it, and the Cauchy integral formula at the centre says its
// integral along such a circle, taken against the time, is 2π times its value
// at the centre. Every point lies on the circle about c through it, at some
// time in ⟦0, 2π⟧. If the real part of a holomorphic function is at most its
// value at the centre all along a circle, the gap between the two is a
// continuous nonnegative function of the time with integral 0, so it
// vanishes. Turning f by conj(f(c)) makes the real part the component of f
// along f(c); when |f| is greatest at c this component is at most |f(c)|², so
// it equals |f(c)|² on every circle, and f is f(c).

package cauchy_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/registry"
)

// ContinuousAlongCircle — a function holomorphic on the disc of radius R about
// c has real and imaginary parts continuous, as functions of the time on
// ⟦0, 2π⟧, along the circle of radius r < R about c. f has a derivative, so
// is continuous, at each point of the disc, the circle's among them; and the
// circle's own parts are continuous, as it has a velocity at every time.
var ContinuousAlongCircle = continuousAlongCircleThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAlongCircle",
	Key:  "prop_8e1c0f8f93b4ce68",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R r:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"&0 < r",
			"r < R",
		},
		Conclusion: "real_continuous_on(⟦&0, &2 * pi⟧, λt:real. re(f(circle_path(c, r, t)))) ∧ " +
			"real_continuous_on(⟦&0, &2 * pi⟧, λt:real. im(f(circle_path(c, r, t))))",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R, r *Expr[Real],
			holomorphic, positive, smaller Fact,
		) {
			span := arg.TermAs[Set[Real]]("⟦&0, &2 * pi⟧")
			circle := arg.TermAs[Fun[Real, Complex]]("circle_path(c, r)")
			velocity := arg.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)")
			continuous := arg.Have(
				"f, holomorphic on the disc, is continuous at each of its points",
				"∀z:complex. z ∈ «disc»(c, R) ⇒ complex_continuous_at(f, z)",
				By(holomorphic, complex_derivative.HolomorphicOnContinuousAt))
			inDisc := arg.Have(
				"the circle lies in the disc, its points being r < R from c",
				"∀t:real. circle_path(c, r, t) ∈ «disc»(c, R)",
				arg.ForEach(func(t *Expr[Real]) Action {
					return ByArith(positive, smaller, path_integral.CirclePathRadius.At(c, r, t))
				}))
			arg.Show(
				"so f is continuous along the circle, whose own parts "+
					"are continuous as it has a velocity at every time",
				By(
					continuous,
					inDisc,
					path_integral.CirclePathDerivative,
					path_integral.PathDerivativeContinuousOn.At(circle, velocity, span),
					path_integral.ContinuousAlongPath.At(f, circle, span)))
		}),
})}

// MeanValueCircle — the mean value property: for f holomorphic on the disc of
// radius R about c and 0 < r < R, the integral over the times ⟦0, 2π⟧ of f
// along the circle of radius r about c is 2π·f(c). It is the Cauchy integral
// formula at the centre: there the integrand f(z)/(z − c)·i·r·e^{it} of the
// formula is i·f(z), since z − c is r·e^{it}, so i times the integral is
// 2πi·f(c).
var MeanValueCircle = meanValueCircleThm{family.Add(registry.ProofEntry{
	Name: "MeanValueCircle",
	Key:  "prop_fe7199f7be68114d",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R r:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"&0 < r",
			"r < R",
		},
		Conclusion: "complex_integral(λt:real. f(circle_path(c, r, t)), &0, &2 * pi) = &(&2 * pi) * f(c)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R, r *Expr[Real],
			holomorphic, positive, smaller Fact,
		) {
			zero, full := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&2 * pi")
			values := arg.TermAs[Fun[Real, Complex]]("λt:real. f(circle_path(c, r, t))")
			turned := arg.TermAs[Fun[Real, Complex]]("λt:real. complex_i * f(circle_path(c, r, t))")
			i := arg.TermAs[Complex]("complex_i")
			I, toI := arg.ObtainAs[Complex](
				"f along the circle has parts continuous on ⟦0, 2π⟧, so an integral I there",
				"∃I:complex. complex_has_integral(λt:real. f(circle_path(c, r, t)), &0, &2 * pi, I)",
				ByArith(
					holomorphic,
					positive,
					smaller,
					ContinuousAlongCircle.At(f, c, R, r),
					real_trigonometry.PiBounds,
					path_integral.ComplexContinuousIntegrable.At(values, zero, full)))
			formula := arg.Have(
				"by the integral formula at the centre, which lies inside "+
					"the circle, f(z)/(z − c) integrates to 2πi·f(c) round it",
				"«circleInt»(λz:complex. f(z) / (z - c), c, r) = &(&2 * pi) * complex_i * f(c)",
				ByArith(
					holomorphic,
					smaller,
					positive,
					complex_abs.AbsEqZero.At(arg.TermAs[Complex]("c - c")),
					CauchyIntegralFormula.At(f, c, c, R, r)))
			integrand := arg.Have(
				"along the circle the integrand f(z)/(z − c)·i·r·e^{it} of the formula is i·f(z)",
				"(λt:real. "+
					"    f(circle_path(c, r, t)) / "+
					"    (circle_path(c, r, t) - c) * "+
					"    (complex_i * &r * exp(complex_i * &t))) = "+
					"(λt:real. complex_i * f(circle_path(c, r, t)))",
				Derive(func(d *Argument) {
					d.Do(Funext())
					t := d.FixAs[Real]("t")
					point := d.TermAs[Complex]("&r * exp(complex_i * &t)")
					radius := d.Have(
						"at time t the circle lies at r·e^{it} from c",
						"circle_path(c, r, t) - c = &r * exp(complex_i * &t)",
						Simp(Fwd(path_integral.CirclePathDef)),
						ByArith())
					nonzero := d.Have(
						"which is not 0, its modulus being r",
						"&r * exp(complex_i * &t) ≠ &0",
						ByArith(
							positive,
							complex_abs.AbsMul.At(d.TermAs[Complex]("&r"), d.TermAs[Complex]("exp(complex_i * &t)")),
							complex_abs.AbsOfReal.At(r),
							complex_exp.AbsExpIOfReal.At(t),
							complex_abs.AbsPosIffNonzero.At(point)))
					d.Show(
						"so dividing f by r·e^{it} and multiplying by i·r·e^{it} leaves i·f",
						radius.Rw(),
						ByArith(nonzero))
				}))
			scaled := arg.Have(
				"so i times the integral I is 2πi·f(c)",
				"complex_i * I = &(&2 * pi) * complex_i * f(c)",
				By(
					arg.Unfolded(formula, path_integral.PathIntegralDef),
					integrand,
					toI,
					path_integral.ComplexHasIntegralScale.At(values, zero, full, i, I),
					path_integral.ComplexHasIntegralValue.At(turned, zero, full, arg.TermAs[Complex]("complex_i * I"))))
			arg.Show(
				"and as i·i = −1, I is 2π·f(c)",
				ByArith(
					toI,
					Scaled(i, scaled),
					Scaled(I, complex_field.ISquared),
					Scaled(arg.TermAs[Complex]("&(&2 * pi) * f(c)"), complex_field.ISquared),
					path_integral.ComplexHasIntegralValue.At(values, zero, full, I)))
		}),
})}

// RealPartConstantOnCircle — the maximum principle for the real part on a
// circle: if g is holomorphic on the disc of radius R about c and its real
// part is at most re(g(c)) at every time of ⟦0, 2π⟧ along the circle of
// radius r < R about c, then it is re(g(c)) at every such time. By the mean value property the
// real part integrates to 2π·re(g(c)) over the times, so the gap
// re(g(c)) − re(g) along the circle is a continuous nonnegative function with
// integral 0, and vanishes.
var RealPartConstantOnCircle = realPartConstantOnCircleThm{family.Add(registry.ProofEntry{
	Name: "RealPartConstantOnCircle",
	Key:  "prop_ec6cc2e6dbd9df7a",
	Build: family.Theorem(Statement{
		Binders: "∀g:(complex → complex). ∀c:complex. ∀R r t:real.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), g)",
			"&0 < r",
			"r < R",
			"∀s:real. &0 ≤ s ∧ s ≤ &2 * pi ⇒ re(g(circle_path(c, r, s))) ≤ re(g(c))",
			"&0 ≤ t",
			"t ≤ &2 * pi",
		},
		Conclusion: "re(g(circle_path(c, r, t))) = re(g(c))",
	},
		func(
			arg *Argument,
			g *Arrow[Complex, Complex],
			c *Expr[Complex],
			R, r, t *Expr[Real],
			holomorphic, positive, smaller, below, early, late Fact,
		) {
			zero, full := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&2 * pi")
			span := arg.TermAs[Set[Real]]("⟦&0, &2 * pi⟧")
			centre := arg.TermAs[Real]("re(g(c))")
			level := arg.TermAs[Fun[Real, Real]]("λs:real. re(g(c))")
			realPart := arg.TermAs[Fun[Real, Real]]("λs:real. re(g(circle_path(c, r, s)))")
			gap := arg.TermAs[Fun[Real, Real]]("λs:real. re(g(c)) - re(g(circle_path(c, r, s)))")
			mean := arg.Have(
				"by the mean value property, g integrates to 2π·g(c) along the circle",
				"complex_integral(λs:real. g(circle_path(c, r, s)), &0, &2 * pi) = &(&2 * pi) * g(c)",
				By(holomorphic, positive, smaller, MeanValueCircle.At(g, c, R, r)))
			meanParts := arg.Simplified(
				arg.Unfolded(mean, path_integral.ComplexIntegralDef),
				complex_field.Parts,
				Fwd(complex_field.ComplexMulDef),
				Fwd(complex_field.ComplexOfRealDef))
			along := arg.Conjuncts(
				GroupPremises(holomorphic, positive, smaller, ContinuousAlongCircle.At(g, c, R, r)),
				"the real part of g is continuous along the circle",
				"and so is its imaginary part")
			J, toJ := arg.ObtainAs[Real](
				"so the real part has an integral J over ⟦0, 2π⟧",
				"∃J:real. real_has_integral(λs:real. re(g(circle_path(c, r, s))), &0, &2 * pi, J)",
				ByArith(
					along[0],
					real_trigonometry.PiBounds,
					real_integral.ContinuousIntegrable.At(realPart, zero, full)))
			gapZero := arg.Have(
				"which is the real part 2π·re(g(c)) of the mean, so the gap re(g(c)) − re(g) integrates to 0",
				"real_integral(λs:real. re(g(c)) - re(g(circle_path(c, r, s))), &0, &2 * pi) = &0",
				ByArith(
					meanParts,
					toJ,
					real_trigonometry.PiBounds,
					real_integral.HasIntegralValue.At(realPart, zero, full, J),
					real_integral.HasIntegralConst.At(zero, full, centre),
					real_integral.HasIntegralSub.At(
						level, realPart, zero, full, arg.TermAs[Real]("re(g(c)) * (&2 * pi - &0)"), J),
					real_integral.HasIntegralValue.At(
						gap, zero, full, arg.TermAs[Real]("re(g(c)) * (&2 * pi - &0) - J"))))
			gapContinuous := arg.Have(
				"the gap is continuous on ⟦0, 2π⟧",
				"real_continuous_on(⟦&0, &2 * pi⟧, λs:real. re(g(c)) - re(g(circle_path(c, r, s))))",
				By(
					along[0],
					real_continuous.ContinuousOnConst.At(centre, span),
					real_continuous.ContinuousOnSub.At(level, realPart, span)))
			gapNonnegative := arg.Have(
				"and nonnegative there",
				"∀s:real. &0 ≤ s ∧ s ≤ &2 * pi ⇒ &0 ≤ re(g(c)) - re(g(circle_path(c, r, s)))",
				arg.ForEach(func(s *Expr[Real]) Action {
					return ByArith(below.At(s))
				}))
			proper := arg.Have(
				"and ⟦0, 2π⟧ has positive length",
				"&0 < &2 * pi",
				ByArith(real_trigonometry.PiBounds))
			arg.Show(
				"so the gap vanishes on ⟦0, 2π⟧, at t too",
				ByArith(
					proper,
					gapContinuous,
					gapNonnegative,
					gapZero,
					early,
					late,
					real_integral.NonnegIntegralZeroVanishes.At(gap, zero, full, t)))
		}),
})}

// MaximumModulus — the maximum modulus principle on a disc: a function
// holomorphic on the disc of radius R about c whose modulus there is
// greatest at the centre is constant on the disc. A point z other than c is
// reached at a time t by the circle about c through it. The real part of
// conj(f(c))·f is the component of f along f(c), at most |f(c)|·|f| ≤ |f(c)|²
// on the disc, with |f(c)|² its value at c; so it is |f(c)|² all along that
// circle, at z too. Then f(z) − f(c) has parts whose squares add up to
// |f(z)|² − 2·|f(c)|² + |f(c)|² ≤ 0, and both parts vanish.
var MaximumModulus = maximumModulusThm{family.Add(registry.ProofEntry{
	Name: "MaximumModulus",
	Key:  "prop_1ba40d26d5ea882d",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀R:real. ∀z:complex.",
		Hypotheses: []string{
			"holomorphic_on(«disc»(c, R), f)",
			"∀w:complex. |w - c| < R ⇒ |f(w)| ≤ |f(c)|",
			"|z - c| < R",
		},
		Conclusion: "f(z) = f(c)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			R *Expr[Real],
			holomorphic, bounded Fact,
			z *Expr[Complex],
			inside Fact,
		) {
			apart := arg.Unless(
				arg.TermAs[Bool]("z = c"),
				"at the centre itself there is nothing to prove",
				Given(func(b *Argument, same Fact) {
					b.Do(same.Rw(), Basic())
				}))
			radius := arg.TermAs[Real]("|z - c|")
			disc := arg.TermAs[Set[Complex]]("«disc»(c, R)")
			value := arg.TermAs[Complex]("f(c)")
			mirrored := arg.TermAs[Complex]("conj(f(c))")
			turned := arg.TermAs[Fun[Complex, Complex]]("λw:complex. conj(f(c)) * f(w)")
			positive := arg.Have(
				"the circle about c through z has positive radius |z − c|",
				"&0 < |z - c|",
				ByArith(apart, complex_abs.AbsPosIffNonzero.At(arg.TermAs[Complex]("z - c"))))
			t, reaches := arg.UnpackAs[Real](path_integral.CirclePathReaches.At(c, z), "t")
			when := arg.Conjuncts(
				reaches,
				"t is at least 0",
				"t is at most 2π",
				"the circle is at z at time t")
			turnedHolomorphic := arg.Have(
				"conj(f(c))·f is holomorphic on the disc too",
				"holomorphic_on(«disc»(c, R), λw:complex. conj(f(c)) * f(w))",
				By(
					holomorphic,
					complex_derivative.HolomorphicOnConst.At(disc, mirrored),
					complex_derivative.HolomorphicOnMul.At(
						disc, arg.TermAs[Fun[Complex, Complex]]("λw:complex. conj(f(c))"), f)))
			modulusOnCircle := arg.Have(
				"the circle lies in the disc, so |f| is at most |f(c)| on it",
				"∀s:real. |f(circle_path(c, |z - c|, s))| ≤ |f(c)|",
				Derive(func(d *Argument) {
					s := d.FixAs[Real]("s")
					d.Show(
						"the point at time s is |z − c| < R from c",
						ByArith(
							bounded.At(d.TermAs[Complex]("circle_path(c, |z - c|, s)")),
							inside,
							positive,
							path_integral.CirclePathRadius.At(c, radius, s)))
				}))
			atCentre := arg.Have(
				"at c the component is |f(c)|²",
				"re(conj(f(c)) * f(c)) = |f(c)| * |f(c)|",
				Simp(complex_field.Parts, Fwd(complex_field.ComplexMulDef), Fwd(complex_field.ComplexConjDef)),
				ByArith(complex_abs.AbsSquare.At(value)))
			componentOnCircle := arg.Have(
				"so on it the component re(conj(f(c))·f) of f along f(c) is at most its value |f(c)|² at c",
				Statement{
					Binders: "∀s:real.",
					Hypotheses: []string{
						"&0 ≤ s",
						"s ≤ &2 * pi",
					},
					Conclusion: "re(conj(f(c)) * f(circle_path(c, |z - c|, s))) ≤ re(conj(f(c)) * f(c))",
				},
				Derive(func(d *Argument) {
					s := d.FixAs[Real]("s")
					point := d.TermAs[Complex]("f(circle_path(c, |z - c|, s))")
					d.Show(
						"it is at most |conj(f(c))·f| = |f(c)|·|f| ≤ |f(c)|·|f(c)|",
						ByArith(
							modulusOnCircle.At(s),
							complex_abs.ReLessEqAbs.At(d.TermAs[Complex]("conj(f(c)) * f(circle_path(c, |z - c|, s))")),
							complex_abs.AbsMul.At(mirrored, point),
							atCentre,
							complex_abs.AbsConj.At(value),
							complex_abs.AbsNonneg.At(value),
							complex_abs.AbsSquare.At(value),
							real_order_ring.LessEqMulLeft.At(
								d.TermAs[Real]("|f(c)|"),
								d.TermAs[Real]("|f(circle_path(c, |z - c|, s))|"),
								d.TermAs[Real]("|f(c)|"))))
				}))
			component := arg.Have(
				"by the maximum principle for the real part, that "+
					"component is its value at c all along the circle, at z too",
				"re(conj(f(c)) * f(circle_path(c, |z - c|, t))) = re(conj(f(c)) * f(c))",
				By(
					turnedHolomorphic,
					positive,
					inside,
					componentOnCircle,
					when[0],
					when[1],
					RealPartConstantOnCircle.At(turned, c, R, radius, t)))
			inner := arg.Simplified(
				component,
				complex_field.Parts,
				Fwd(complex_field.ComplexMulDef),
				Fwd(complex_field.ComplexConjDef))
			squares := arg.Have(
				"and |f(z)|² is at most |f(c)|²",
				"|f(z)| * |f(z)| ≤ |f(c)| * |f(c)|",
				ByArith(bounded.At(z), inside, complex_abs.AbsNonneg.At(arg.TermAs[Complex]("f(z)"))))
			parts := arg.Have(
				"so the parts of f(z) − f(c) have squares adding "+
					"up to |f(z)|² − 2·|f(c)|² + |f(c)|² ≤ 0, and vanish",
				"re(f(z)) = re(f(c)) ∧ im(f(z)) = im(f(c))",
				ByArith(
					inner,
					when[2],
					squares,
					complex_abs.AbsSquare.At(arg.TermAs[Complex]("f(z)")),
					complex_abs.AbsSquare.At(value),
					real_order_ring.SumSquaresEqZero.At(
						arg.TermAs[Real]("re(f(z)) - re(f(c))"),
						arg.TermAs[Real]("im(f(z)) - im(f(c))"))))
			arg.Show(
				"so f(z) is f(c)",
				By(parts, complex_field.ComplexEq.At(arg.TermAs[Complex]("f(z)"), value)))
		}),
})}
