// circle.go — the circle as a path: its velocity, its piecewise smoothness
// over ⟦0, 2π⟧ and over any parameter interval, the right half-circle about
// 0 as a path from −iR to iR, its closedness, its radius and, about 0, its
// modulus, the time in ⟦0, 2π⟧ at which the circle about c through a point
// reaches it, and its length, and the integral of 1/(z − c) once round it, 2πi,
// which is not 0; the integral of a character e^{imt} over one period, 2π
// at m = 0 and 0 at every other integer m; and the integral round a circle
// of positive radius as an integral over the circle's points, which sees a
// function only there, is linear in functions continuous there, is 0 for a
// function with a primitive there, and is at most the length times a bound,
// as is the integral along an arc of the circle about 0.

package path_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_log"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// CirclePathDerivative — the circle about c of radius r moves at velocity
// i·r·exp(it) at every time t: by Euler's formula its point at s has parts
// re(c) + r·cos s and im(c) + r·sin s, whose derivatives at t are
// r·(−sin t) and r·cos t, and these are the parts of i·r·(cos t + i·sin t).
var CirclePathDerivative = circlePathDerivativeThm{family.Add(registry.ProofEntry{
	Name: "CirclePathDerivative",
	Key:  "prop_fe97a6be2a12c13b",
	Build: family.Theorem("∀c:complex. ∀r t:real. "+
		"    path_derivative_at(circle_path(c, r), t, complex_i * &r * exp(complex_i * &t))",
		func(a *Argument, c *Expr[Complex], r, t *Expr[Real]) {
			circle := a.Have(
				"by Euler's formula the circle's point at s has parts re(c) + r·cos s and im(c) + r·sin s",
				"circle_path(c, r) = λs:real. complex(re(c) + r * cos(s), im(c) + r * sin(s))",
				Funext(),
				Simp(
					Fwd(CirclePathDef),
					Fwd(complex_exp.EulerOfReal),
					complex_field.Parts,
					Fwd(complex_field.PartsAdd),
					Fwd(complex_field.PartsMul),
					Fwd(complex_field.PartsOfReal),
					Fwd(complex_field.PartsI)),
				ByArith())
			velocity := a.Have(
				"and i·r·exp(it) = i·r·(cos t + i·sin t) has parts r·(−sin t) and r·cos t",
				"complex_i * &r * exp(complex_i * &t) = complex(r * -sin(t), r * cos(t))",
				Simp(
					Fwd(complex_exp.EulerOfReal),
					complex_field.Parts,
					Fwd(complex_field.PartsAdd),
					Fwd(complex_field.PartsMul),
					Fwd(complex_field.PartsOfReal),
					Fwd(complex_field.PartsI)),
				ByArith())
			zero := a.TermAs[Real]("&0")
			a.Show(
				"read part by part, each part of the circle is to have "+
					"the matching part of the velocity as its derivative",
				Simp(Fwd(circle), Fwd(velocity), Fwd(complex_derivative.PathDerivativeAtDef)),
				SplitConj(
					Case(
						"the real part re(c) + r·cos s, a constant plus r times "+
							"the cosine, has derivative 0 + r·(−sin t) = r·(−sin t)",
						By(
							real_derivative.DerivativeAdd.At(
								a.TermAs[Fun[Real, Real]]("λs:real. re(c)"),
								a.TermAs[Fun[Real, Real]]("λs:real. r * cos(s)"),
								t,
								zero,
								a.TermAs[Real]("r * -sin(t)")),
							real_derivative.DerivativeConst.At(a.TermAs[Real]("re(c)"), t),
							real_derivative.DerivativeScale.At(
								a.TermAs[Fun[Real, Real]]("real_cos"),
								t,
								a.TermAs[Real]("-sin(t)"),
								r),
							real_trigonometry.CosDerivative.At(t),
							real_construction.AddLeftId)),
					Case(
						"the imaginary part im(c) + r·sin s, a constant plus "+
							"r times the sine, has derivative 0 + r·cos t = r·cos t",
						By(
							real_derivative.DerivativeAdd.At(
								a.TermAs[Fun[Real, Real]]("λs:real. im(c)"),
								a.TermAs[Fun[Real, Real]]("λs:real. r * sin(s)"),
								t,
								zero,
								a.TermAs[Real]("r * cos(t)")),
							real_derivative.DerivativeConst.At(a.TermAs[Real]("im(c)"), t),
							real_derivative.DerivativeScale.At(
								a.TermAs[Fun[Real, Real]]("real_sin"),
								t,
								a.TermAs[Real]("cos(t)"),
								r),
							real_trigonometry.SinDerivative.At(t),
							real_construction.AddLeftId))))
		}),
})}

// CircleArcPiecewiseSmooth — the circle about c of radius r, run over any
// ordered parameter interval, is a piecewise smooth path with velocity i·r·exp(it).
var CircleArcPiecewiseSmooth = circleArcPiecewiseSmoothThm{family.Add(registry.ProofEntry{
	Name: "CircleArcPiecewiseSmooth",
	Key:  "prop_16f3cea23f44073c",
	Build: family.Theorem(Statement{
		Binders:    "∀c:complex. ∀r a b:real.",
		Hypotheses: []string{"a ≤ b"},
		Conclusion: "piecewise_smooth_path(circle_path(c, r), " +
			"    λt:real. complex_i * &r * exp(complex_i * &t), " +
			"    a, " +
			"    b)",
	},
		func(arg *Argument, c *Expr[Complex], r, a, b *Expr[Real], ordered Fact) {
			parts := arg.Have(
				"the circle has a velocity at every point, so its parts are continuous on ⟦a, b⟧",
				"real_continuous_on(⟦a, b⟧, λt:real. re(circle_path(c, r, t))) ∧ "+
					"real_continuous_on(⟦a, b⟧, λt:real. im(circle_path(c, r, t)))",
				By(
					PathDerivativeContinuousOn.At(
						arg.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						arg.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						arg.TermAs[Set[Real]]("⟦a, b⟧")),
					CirclePathDerivative))
			velocity := arg.Have(
				"by Euler's formula the velocity i·r·exp(it) has parts r·(−sin t) and r·cos t",
				"∀t:real. complex_i * &r * exp(complex_i * &t) = complex(r * -sin(t), r * cos(t))",
				Simp(
					Fwd(complex_exp.EulerOfReal),
					complex_field.Parts,
					Fwd(complex_field.PartsAdd),
					Fwd(complex_field.PartsMul),
					Fwd(complex_field.PartsOfReal),
					Fwd(complex_field.PartsI)),
				ByArith())
			velocityFactor := arg.TermAs[Complex]("complex_i * &r")
			arg.Show(
				"each clause of piecewise smoothness on ⟦a, b⟧, the velocity read in its parts",
				Simp(Fwd(velocity), Fwd(PiecewiseSmoothPathDef)),
				SplitConjAll(
					Case(
						"the parameter interval is ordered",
						By(ordered)),
					Case(
						"the real part of the circle is continuous on ⟦a, b⟧",
						By(parts)),
					Case(
						"and so is its imaginary part",
						By(parts)),
					Case(
						"no point need be set aside",
						Witness(arg.TermAs[Set[Real]]("∅")),
						SplitConjAll(
							Case(
								"the empty set is finite",
								By(finite_set.FiniteRules)),
							Case(
								"inside ⟦a, b⟧ the circle has velocity i·r·exp(it)",
								arg.ForEach(func(t *Expr[Real]) Action {
									return By(velocity.At(t), CirclePathDerivative.At(c, r, t))
								})),
							Case(
								"the velocity is bounded by |i·r|",
								Witness(arg.TermAs[Real]("|complex_i * &r|")),
								Derive(func(d *Argument) {
									t := d.FixAs[Real]("t")
									d.Show(
										"its modulus at t is |i·r|·|exp(it)| = |i·r|·1",
										By(
											velocity.At(t),
											complex_abs.AbsMul.At(velocityFactor, d.TermAs[Complex]("exp(complex_i * &t)")),
											complex_exp.AbsExpIOfReal.At(t),
											real_ring.MulRightId,
											real_order_ring.LessEqRefl))
								})),
							Case(
								"its real part r·(−sin t) is continuous, r times the negated sine",
								By(
									real_continuous.ContinuousOnMul,
									real_continuous.ContinuousOnConst,
									real_continuous.ContinuousOnNeg,
									real_trigonometry.SinContinuousOn)),
							Case(
								"and its imaginary part r·cos t, r times the cosine",
								By(
									real_continuous.ContinuousOnMul,
									real_continuous.ContinuousOnConst,
									real_trigonometry.CosContinuousOn))))))
		}),
	Reading: "The half-circles of Newman's contour are the intervals ⟦−π/2, π/2⟧ and ⟦π/2, 3π/2⟧.",
})}

// RightArcPath — the right half of the circle |z| = R, run over
// −π/2 ≤ t ≤ π/2, is a piecewise smooth path from −iR to iR.
var RightArcPath = rightArcPathThm{family.Add(registry.ProofEntry{
	Name: "RightArcPath",
	Key:  "prop_35de4a65e3aac6fe",
	Build: family.Theorem(Statement{
		Binders: "∀R:real.",
		Conclusion: "piecewise_smooth_path(circle_path(&0, R), " +
			"    λt:real. complex_i * &R * exp(complex_i * &t), " +
			"    -(pi / &2), " +
			"    pi / &2) ∧ " +
			"circle_path(&0, R, -(pi / &2)) = -(complex_i * &R) ∧ " +
			"circle_path(&0, R, pi / &2) = complex_i * &R",
	}, func(arg *Argument, R *Expr[Real]) {
		smooth := arg.Have(
			"the arc over the ordered interval −π/2 ≤ t ≤ π/2 is piecewise smooth",
			"piecewise_smooth_path(circle_path(&0, R), "+
				"    λt:real. complex_i * &R * exp(complex_i * &t), "+
				"    -(pi / &2), "+
				"    pi / &2)",
			ByArith(
				real_trigonometry.PiBounds,
				CircleArcPiecewiseSmooth.At(
					arg.TermAs[Complex]("&0"), R, arg.TermAs[Real]("-(pi / &2)"), arg.TermAs[Real]("pi / &2"))))
		start := arg.Have(
			"at −π/2 the cosine vanishes and the sine is −1, so the arc starts at −iR",
			"circle_path(&0, R, -(pi / &2)) = -(complex_i * &R)",
			Simp(
				Fwd(CirclePathDef),
				Fwd(complex_exp.EulerOfReal),
				Fwd(real_trigonometry.CosNeg),
				Fwd(real_trigonometry.SinNeg),
				Fwd(real_trigonometry.PiHalfZero),
				Fwd(real_trigonometry.SinPiHalf)),
			Simp(Fwd(complex_field.OfRealNeg)),
			ByArith())
		end := arg.Have(
			"at π/2 the cosine vanishes and the sine is 1, so it ends at iR",
			"circle_path(&0, R, pi / &2) = complex_i * &R",
			Simp(
				Fwd(CirclePathDef),
				Fwd(complex_exp.EulerOfReal),
				Fwd(real_trigonometry.PiHalfZero),
				Fwd(real_trigonometry.SinPiHalf)),
			ByArith())
		arg.Show(
			"the smooth arc and its two ends",
			By(smooth, start, end))
	}),
})}

// CirclePiecewiseSmooth — the circle about c of radius r, run once on
// ⟦0, 2π⟧ at velocity i·r·exp(it), is a piecewise smooth path.
var CirclePiecewiseSmooth = circlePiecewiseSmoothThm{family.Add(registry.ProofEntry{
	Name: "CirclePiecewiseSmooth",
	Key:  "prop_a401d4c97247bf2c",
	Build: family.Theorem("∀c:complex. ∀r:real. "+
		"    piecewise_smooth_path(circle_path(c, r), "+
		"        λt:real. complex_i * &r * exp(complex_i * &t), "+
		"        &0, "+
		"        &2 * pi)",
		func(a *Argument, c *Expr[Complex], r *Expr[Real]) {
			ordered := a.Have(
				"the interval is ordered since π is positive",
				"&0 ≤ &2 * pi",
				ByArith(real_trigonometry.PiBounds))
			a.Show(
				"the circle over this parameter interval is piecewise smooth",
				By(ordered, CircleArcPiecewiseSmooth.At(c, r, a.TermAs[Real]("&0"), a.TermAs[Real]("&2 * pi"))))
		}),
})}

// CirclePathClosed — the circle is a closed path: run once round ⟦0, 2π⟧
// it ends where it began, since by Euler's formula exp(2πi) and exp(0)
// have the cosine and sine of 2π and of 0 as their parts, and these agree
// by periodicity.
var CirclePathClosed = circlePathClosedThm{family.Add(registry.ProofEntry{
	Name: "CirclePathClosed",
	Key:  "prop_fe3eea55db8550a9",
	Build: family.Theorem("∀c:complex. ∀r:real. circle_path(c, r, &2 * pi) = circle_path(c, r, &0)",
		func(a *Argument, c *Expr[Complex], r *Expr[Real]) {
			zero := a.TermAs[Real]("&0")
			a.Show(
				"the points at 2π and at 0 are c + r·(cos 2π + i·sin "+
					"2π) and c + r·(cos 0 + i·sin 0), equal by periodicity",
				Simp(Fwd(CirclePathDef)),
				ByArith(
					complex_exp.EulerOfReal.At(a.TermAs[Real]("&2 * pi")),
					complex_exp.EulerOfReal.At(zero),
					real_trigonometry.CosPeriodic.At(zero),
					real_trigonometry.SinPeriodic.At(zero)))
		}),
})}

// CirclePathRadius — every point of the circle about c of radius r lies
// at distance |r| from c: it is c + r·exp(it), and |exp(it)| = 1.
var CirclePathRadius = circlePathRadiusThm{family.Add(registry.ProofEntry{
	Name: "CirclePathRadius",
	Key:  "prop_f454dcc708e3b540",
	Build: family.Theorem("∀c:complex. ∀r t:real. |circle_path(c, r, t) - c| = |r|",
		func(a *Argument, c *Expr[Complex], r, t *Expr[Real]) {
			radius := a.Have(
				"at time t the circle lies at r·exp(it) from c",
				"circle_path(c, r, t) - c = &r * exp(complex_i * &t)",
				Simp(Fwd(CirclePathDef)),
				ByArith())
			a.Show(
				"whose modulus is |r|·|exp(it)| = |r|",
				radius.Rw(),
				ByArith(
					complex_abs.AbsMul.At(a.TermAs[Complex]("&r"), a.TermAs[Complex]("exp(complex_i * &t)")),
					complex_abs.AbsOfReal.At(r),
					complex_exp.AbsExpIOfReal.At(t)))
		}),
})}

// CirclePathModulus — every point of the circle of radius R > 0 about 0
// has modulus R.
var CirclePathModulus = circlePathModulusThm{family.Add(registry.ProofEntry{
	Name: "CirclePathModulus",
	Key:  "prop_3d7641300defdd9a",
	Build: family.Theorem(Statement{
		Binders:    "∀R t:real.",
		Hypotheses: []string{"&0 < R"},
		Conclusion: "|circle_path(&0, R, t)| = R",
	}, func(arg *Argument, R, t *Expr[Real], positive Fact) {
		subtract := arg.Have(
			"subtracting zero fixes the point of the circle",
			"circle_path(&0, R, t) - &0 = circle_path(&0, R, t)",
			ByArith())
		distance := arg.Simplified(CirclePathRadius.At(arg.TermAs[Complex]("&0"), R, t), Fwd(subtract))
		arg.Show(
			"the distance from zero is the positive radius",
			ByArith(distance, positive, real_sgn_abs.AbsFixedIffNonneg.At(R)))
	}),
})}

// CirclePathReaches — every point z lies on the circle about c of radius
// |z − c|, which reaches it at a time in ⟦0, 2π⟧: z − c is |z − c|·e^{iθ} for
// an angle −π < θ ≤ π, and a negative angle is moved into ⟦π, 2π⟧ by a full
// turn, which leaves e^{iθ} unchanged.
var CirclePathReaches = circlePathReachesThm{family.Add(registry.ProofEntry{
	Name: "CirclePathReaches",
	Key:  "prop_4fdfba5aeb999c52",
	Build: family.Theorem("∀c z:complex. ∃t:real. "+
		"    &0 ≤ t ∧ t ≤ &2 * pi ∧ circle_path(c, |z - c|, t) = z",
		func(arg *Argument, c, z *Expr[Complex]) {
			θ, polar := arg.UnpackAs[Real](complex_log.PolarFormExists.At(arg.TermAs[Complex]("z - c")), "θ")
			angle := arg.Conjuncts(
				polar,
				"θ exceeds −π",
				"θ is at most π",
				"z − c is |z − c|·e^{iθ}")
			radius := arg.TermAs[Real]("|z - c|")
			arg.Cases(arg.Term("&0 ≤ θ"))
			arg.When(
				"a nonnegative angle is already a time in ⟦0, 2π⟧",
				func(b *Argument, nonnegative Fact) {
					b.Take(θ)
					b.Show(
						"at which the circle is at c + (z − c) = z",
						ByArith(
							nonnegative,
							angle[1],
							angle[2],
							real_trigonometry.PiBounds,
							CirclePathDef.At(c, radius, θ)))
				})
			arg.Otherwise(
				"a negative angle is moved forward by a full turn",
				func(b *Argument, negative Fact) {
					turned := b.TermAs[Real]("θ + &2 * pi")
					period := b.Have(
						"which leaves e^{iθ} unchanged, cosine and sine having period 2π",
						"exp(complex_i * &(θ + &2 * pi)) = exp(complex_i * &θ)",
						ByArith(
							complex_exp.EulerOfReal.At(turned),
							complex_exp.EulerOfReal.At(θ),
							real_trigonometry.CosPeriodic.At(θ),
							real_trigonometry.SinPeriodic.At(θ)))
					b.Take(turned)
					b.Show(
						"so θ + 2π is a time in ⟦π, 2π⟧ at which the circle is at z",
						ByArith(
							negative,
							period,
							angle[0],
							angle[2],
							real_trigonometry.PiBounds,
							CirclePathDef.At(c, radius, turned)))
				})
		}),
})}

// CircleLength — the circle of radius r has length 2π·|r|: its speed
// |i·r·exp(it)| = |i|·|r|·|exp(it)| is the constant |r|, which integrates
// over ⟦0, 2π⟧ to 2π·|r|.
var CircleLength = circleLengthThm{family.Add(registry.ProofEntry{
	Name: "CircleLength",
	Key:  "prop_b1685a57759320c4",
	Build: family.Theorem("∀r:real. "+
		"    real_integral(λt:real. |complex_i * &r * exp(complex_i * &t)|, &0, &2 * pi) = &2 * pi * |r|",
		func(a *Argument, r *Expr[Real]) {
			speed := a.Have(
				"the circle's speed is the constant |r|",
				"∀t:real. |complex_i * &r * exp(complex_i * &t)| = |r|",
				Derive(func(b *Argument) {
					t := b.FixAs[Real]("t")
					b.Show(
						"|i·r·exp(it)| is |i|·|r|·|exp(it)| = 1·|r|·1",
						ByArith(
							complex_abs.AbsMul.At(
								b.TermAs[Complex]("complex_i * &r"), b.TermAs[Complex]("exp(complex_i * &t)")),
							complex_abs.AbsMul.At(b.TermAs[Complex]("complex_i"), b.TermAs[Complex]("&r")),
							complex_abs.AbsI,
							complex_abs.AbsOfReal.At(r),
							complex_exp.AbsExpIOfReal.At(t)))
				}))
			zero, span := a.TermAs[Real]("&0"), a.TermAs[Real]("&2 * pi")
			size := a.TermAs[Real]("|r|")
			a.Show(
				"and the constant |r| integrates over ⟦0, 2π⟧ to |r|·(2π − 0)",
				Simp(Fwd(speed)),
				ByArith(
					real_trigonometry.PiBounds,
					real_integral.HasIntegralConst.At(zero, span, size),
					real_integral.HasIntegralValue.At(
						a.TermAs[Fun[Real, Real]]("λt:real. |r|"),
						zero,
						span,
						a.TermAs[Real]("|r| * (&2 * pi - &0)"))))
		}),
})}

// CircleIntegralInverse — once around the circle of positive radius r
// about c, the integral of 1/(z − c) is 2π·i. At time t the circle is at
// c + r·exp(it), so 1/(z − c) times the velocity i·r·exp(it) is i, r·exp(it)
// being of modulus r > 0 and so not 0; and the constant i integrates over
// ⟦0, 2π⟧ to i·(2π − 0).
var CircleIntegralInverse = circleIntegralInverseThm{family.Add(registry.ProofEntry{
	Name: "CircleIntegralInverse",
	Key:  "prop_694bd32e2141a11b",
	Build: family.Theorem(Statement{
		Binders: "∀c:complex. ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
		},
		Conclusion: "«circleInt»(λz:complex. complex_inv(z - c), c, r) = &(&2 * pi) * complex_i",
	},
		func(arg *Argument, c *Expr[Complex], r *Expr[Real], positive Fact) {
			constant := arg.Have(
				"along the circle the integrand is i at every time t",
				"(λt:real. complex_inv(circle_path(c, r, t) - c) * (complex_i * &r * exp(complex_i * &t))) = "+
					"(λt:real. complex_i)",
				Derive(func(b *Argument) {
					b.Do(Funext())
					t := b.FixAs[Real]("t")
					point := b.TermAs[Complex]("&r * exp(complex_i * &t)")
					radius := b.Have(
						"at time t the circle lies at r·exp(it) from c",
						"circle_path(c, r, t) - c = &r * exp(complex_i * &t)",
						Simp(Fwd(CirclePathDef)),
						ByArith())
					nonzero := b.Have(
						"which is not 0: its modulus is r·|exp(it)| = r > 0",
						"&r * exp(complex_i * &t) ≠ &0",
						ByArith(
							positive,
							complex_abs.AbsMul.At(b.TermAs[Complex]("&r"), b.TermAs[Complex]("exp(complex_i * &t)")),
							complex_abs.AbsOfNonnegReal.At(r),
							complex_exp.AbsExpIOfReal.At(t),
							complex_abs.AbsPosIffNonzero.At(point)))
					b.Show(
						"so the inverse of r·exp(it) times i·r·exp(it) is i",
						radius.Rw(),
						ByArith(
							nonzero,
							Scaled(
								b.TermAs[Complex]("complex_i"),
								field.MulLeftInverse.Read(complex_field.Field).At(point))))
				}))
			arg.Show(
				"so the integral is that of the constant i over ⟦0, 2π⟧, which is i·(2π − 0)",
				Unfold(PathIntegralDef),
				constant.Rw(),
				ByArith(
					real_trigonometry.PiBounds,
					ComplexIntegralConst.At(
						arg.TermAs[Real]("&0"), arg.TermAs[Real]("&2 * pi"), arg.TermAs[Complex]("complex_i"))))
		}),
})}

// CircleCharacterIntegral — the integral of e^{imt} over one period ⟦0, 2π⟧ is
// 2π at m = 0 and 0 at every other integer m. At m = 0 the integrand is the
// constant one. Otherwise the character has velocity i·e^{imt}·m, the
// exponential along the line t ↦ mt by the chain rule, so G(t) = e^{imt}/(im),
// the character scaled by 1/(im), is a primitive; it takes the same value at
// both ends because the cosine and the sine have period 2π, so the
// Newton–Leibniz theorem for complex integrals gives zero.
var CircleCharacterIntegral = circleCharacterIntegralThm{family.Add(registry.ProofEntry{
	Name: "CircleCharacterIntegral",
	Key:  "prop_db62cfc29012e335",
	Build: family.Theorem(
		"∀m:int. "+
			"    complex_integral(λt:real. exp(complex_i * &(real_of_int(m) * t)), &0, &2 * pi) = "+
			"    COND(m = &0, &(&2 * pi), &0)",
		func(a *Argument, m *Expr[Int]) {
			zero, period := a.TermAs[Real]("&0"), a.TermAs[Real]("&2 * pi")
			mReal := a.TermAs[Real]("real_of_int(m)")
			character := a.TermAs[Fun[Real, Complex]]("λt:real. exp(complex_i * &(real_of_int(m) * t))")
			a.Cases(a.TermAs[Bool]("m = &0"))
			a.When(
				"at m = 0 the integrand is one, whose integral over the period is 2π",
				func(b *Argument, trivial Fact) {
					one := b.Have(
						"at m = 0 the integrand e^{i·0·t} = cos 0 + i·sin 0 is one at every t",
						"∀t:real. exp(complex_i * &(real_of_int(m) * t)) = &1",
						Derive(func(c *Argument) {
							c.FixAs[Real]()
							c.Show(
								"the integer 0 is the real 0, and Euler's formula "+
									"at the real 0·t gives cos 0 + i·sin 0, which is 1",
								ByArith(
									trivial,
									int_construction.OfNumBridge.At(c.TermAs[Nat]("0")),
									complex_exp.EulerOfReal.At(c.TermAs[Real]("real_of_int(m) * t")),
									real_trigonometry.CosZero,
									real_trigonometry.SinZero))
						}))
					b.Show(
						"so the integral is that of the constant one over ⟦0, 2π⟧, which is 1·(2π − 0)",
						Simp(Fwd(one)),
						ByArith(real_trigonometry.PiBounds, ComplexIntegralConst.At(zero, period, b.TermAs[Complex]("&1"))))
				})
			a.Otherwise(
				"for m ≠ 0, G(t) = e^{imt}/(im) is a primitive that returns to its value after one period",
				func(b *Argument, nonzero Fact) {
					frequency := b.Have(
						"the frequency i·m is not zero: i is not, and nor is the real m, the integer m not being 0",
						"complex_i * &real_of_int(m) ≠ &0",
						ByArith(
							nonzero,
							int_construction.RepresentativeInjective.At(m, b.TermAs[Int]("&0")),
							int_construction.OfNumBridge.At(b.TermAs[Nat]("0")),
							complex_field.INonzero))
					identity, unit := b.TermAs[Fun[Real, Real]]("λx:real. x"), b.TermAs[Real]("&1")
					line := b.Have(
						"the line s ↦ m·s, read in ℂ, has velocity m: its parts m·s and 0 have derivatives m and 0",
						"∀t:real. path_derivative_at(λs:real. &(real_of_int(m) * s), t, &real_of_int(m))",
						Simp(Fwd(complex_derivative.PathDerivativeAtDef), Fwd(complex_field.PartsOfReal)),
						b.ForEach(func(t *Expr[Real]) Action {
							return ByArith(
								real_derivative.DerivativeConst,
								real_derivative.DerivativeId.At(t),
								real_derivative.DerivativeScale.At(identity, t, unit, mReal))
						}))
					linePath := b.TermAs[Fun[Real, Complex]]("λs:real. &(real_of_int(m) * s)")
					i := b.TermAs[Complex]("complex_i")
					wave := b.Have(
						"so the character, z ↦ e^{iz} along that line, has "+
							"velocity i·e^{imt}·m (the chain rule along a path)",
						"∀t:real. "+
							"    path_derivative_at(λs:real. exp(complex_i * &(real_of_int(m) * s)), "+
							"        t, "+
							"        complex_i * exp(complex_i * &(real_of_int(m) * t)) * &real_of_int(m))",
						Derive(func(c *Argument) {
							t := c.FixAs[Real]()
							point := c.TermAs[Complex]("&(real_of_int(m) * t)")
							c.Show(
								"z ↦ e^{iz} has derivative i·e^{iz} at the point m·t of the line",
								By(
									line.At(t),
									complex_power_series.ExpScaledDerivative.At(i, point),
									PathDerivativeCompose.At(
										c.TermAs[Fun[Complex, Complex]]("λw:complex. exp(complex_i * w)"),
										linePath,
										t,
										c.TermAs[Complex]("complex_i * exp(complex_i * &(real_of_int(m) * t))"),
										c.TermAs[Complex]("&real_of_int(m)"))))
						}))
					G, GDef := b.LetAs[Fun[Real, Complex]](
						"G", "λt:real. exp(complex_i * &(real_of_int(m) * t)) / (complex_i * &real_of_int(m))")
					inverse := b.TermAs[Complex]("complex_inv(complex_i * &real_of_int(m))")
					primitive := b.Have(
						"G is the character scaled by 1/(i·m), so its velocity "+
							"is i·e^{imt}·m scaled by 1/(i·m), which is e^{imt}",
						"∀t:real. path_derivative_at(G, t, exp(complex_i * &(real_of_int(m) * t)))",
						Derive(func(c *Argument) {
							t := c.FixAs[Real]()
							value := c.TermAs[Complex]("exp(complex_i * &(real_of_int(m) * t))")
							scaling := c.TermAs[Fun[Complex, Complex]](
								"λz:complex. complex_inv(complex_i * &real_of_int(m)) * z")
							c.Show(
								"z ↦ z/(i·m) has derivative 1/(i·m) at the character's value, and i·m cancels against 1/(i·m)",
								ByArith(
									frequency,
									GDef,
									wave.At(t),
									complex_derivative.DerivativeId.At(value),
									complex_derivative.DerivativeScale.At(
										c.TermAs[Fun[Complex, Complex]]("λz:complex. z"),
										value,
										c.TermAs[Complex]("&1"),
										inverse),
									PathDerivativeCompose.At(
										scaling,
										character,
										t,
										c.TermAs[Complex]("complex_inv(complex_i * &real_of_int(m)) * &1"),
										c.TermAs[Complex]("complex_i * exp(complex_i * &(real_of_int(m) * t)) * &real_of_int(m)"))))
						}))
					interval := b.TermAs[Set[Real]]("⟦&0, &2 * pi⟧")
					I, integral := b.ObtainAs[Complex](
						"the character, continuous on ⟦0, 2π⟧ as it has a velocity, has an integral I there",
						"∃I:complex. complex_has_integral(λt:real. exp(complex_i * &(real_of_int(m) * t)), &0, &2 * pi, I)",
						ByArith(
							real_trigonometry.PiBounds,
							wave,
							PathDerivativeContinuousOn.At(
								character,
								b.TermAs[Fun[Real, Complex]](
									"λt:real. complex_i * exp(complex_i * &(real_of_int(m) * t)) * &real_of_int(m)"),
								interval),
							ComplexContinuousIntegrable.At(character, zero, period)),
						Named("I"))
					periodic := b.Have(
						"the cosine and the sine have period 2π and m is an integer, so they agree at m·2π and at m·0",
						"cos(real_of_int(m) * (&2 * pi)) = cos(real_of_int(m) * &0) ∧ "+
							"sin(real_of_int(m) * (&2 * pi)) = sin(real_of_int(m) * &0)",
						ByArith(
							int_construction.RepresentativeIsInteger.At(m),
							real_trigonometry.CosPeriodicInteger.At(zero, mReal),
							real_trigonometry.SinPeriodicInteger.At(zero, mReal)))
					ends := b.Have(
						"so by Euler's formula G takes the same value at both ends of the period",
						"G(&2 * pi) = G(&0)",
						GDef.Rw(),
						By(
							periodic,
							complex_exp.EulerOfReal.At(b.TermAs[Real]("real_of_int(m) * (&2 * pi)")),
							complex_exp.EulerOfReal.At(b.TermAs[Real]("real_of_int(m) * &0"))))
					increment := b.Have(
						"by the Newton–Leibniz theorem I is the change of G over the period, G being continuous there",
						"I = G(&2 * pi) - G(&0)",
						By(
							primitive,
							integral,
							PathDerivativeContinuousOn.At(G, character, interval),
							ComplexNewtonLeibniz.At(G, character, zero, period, I)))
					b.Show(
						"so the integral is I = G(2π) − G(0) = 0, the value at m ≠ 0",
						ByArith(nonzero, increment, ends, integral, ComplexHasIntegralValue.At(character, zero, period, I)))
				})
		}),
})}

// TwoPiINonzero — 2πi, the integral of 1/(z − c) once round a circle about
// c, is not 0: its modulus is 2π·|i| = 2π, and π is positive.
var TwoPiINonzero = twoPiINonzeroThm{family.Add(registry.ProofEntry{
	Name: "TwoPiINonzero",
	Key:  "prop_c7e1726ce8474f4b",
	Build: family.Theorem("&(&2 * pi) * complex_i ≠ &0",
		func(a *Argument) {
			a.Show(
				"its modulus is 2π·|i| = 2π, which is positive",
				ByArith(
					real_trigonometry.PiBounds,
					complex_abs.AbsMul.At(a.TermAs[Complex]("&(&2 * pi)"), a.TermAs[Complex]("complex_i")),
					complex_abs.AbsOfReal.At(a.TermAs[Real]("&2 * pi")),
					complex_abs.AbsI,
					complex_abs.AbsPosIffNonzero.At(a.TermAs[Complex]("&(&2 * pi) * complex_i"))))
		}),
})}

// CircleIntegralCongruence — the integral round a circle sees a function only
// on the circle: two functions that agree at every point at distance r from c
// have the same integral round the circle about c of radius r > 0, every
// point of the circle lying at that distance.
var CircleIntegralCongruence = circleIntegralCongruenceThm{family.Add(registry.ProofEntry{
	Name: "CircleIntegralCongruence",
	Key:  "prop_cebc6e4586db9d20",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c:complex. ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
			"∀u:complex. |u - c| = r ⇒ f(u) = g(u)",
		},
		Conclusion: "«circleInt»(f, c, r) = «circleInt»(g, c, r)",
	},
		func(
			a *Argument,
			f, g *Arrow[Complex, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			positive, agree Fact,
		) {
			a.Show(
				"f and g agree at every point of the circle, which lies at distance |r| = r from c",
				By(
					agree,
					a.Have(
						"every point of the circle lies at distance r from c",
						"∀t:real. |circle_path(c, r, t) - c| = r",
						a.ForEach(func(t *Expr[Real]) Action {
							return ByArith(positive, CirclePathRadius.At(c, r, t))
						})),
					PathIntegralCongruence.At(
						f,
						g,
						a.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						a.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						a.TermAs[Real]("&0"),
						a.TermAs[Real]("&2 * pi"))))
		}),
})}

// CircleIntegralAdd — the integral round a circle of a sum of two functions
// continuous on the circle is the sum of their integrals: the integral along
// the circle, a piecewise smooth path, is linear in functions continuous
// along it.
var CircleIntegralAdd = circleIntegralAddThm{family.Add(registry.ProofEntry{
	Name: "CircleIntegralAdd",
	Key:  "prop_a423592079d61bed",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c:complex. ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
			"∀u:complex. |u - c| = r ⇒ complex_continuous_at(f, u)",
			"∀u:complex. |u - c| = r ⇒ complex_continuous_at(g, u)",
		},
		Conclusion: "«circleInt»(λz:complex. f(z) + g(z), c, r) = " +
			"«circleInt»(f, c, r) + «circleInt»(g, c, r)",
	},
		func(
			a *Argument,
			f, g *Arrow[Complex, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			positive, fContinuous, gContinuous Fact,
		) {
			radius := a.Have(
				"every point of the circle lies at distance |r| = r from c",
				"∀t:real. |circle_path(c, r, t) - c| = r",
				a.ForEach(func(t *Expr[Real]) Action {
					return ByArith(positive, CirclePathRadius.At(c, r, t))
				}))
			along := a.Have(
				"so f and g are continuous at every point of the circle",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"&0 ≤ t",
						"t ≤ &2 * pi",
					},
					Conclusion: "complex_continuous_at(f, circle_path(c, r, t)) ∧ " +
						"complex_continuous_at(g, circle_path(c, r, t))",
				},
				By(fContinuous, gContinuous, radius))
			a.Show(
				"and the integral of their sum along the circle is the sum of their integrals",
				By(
					along,
					CirclePiecewiseSmooth.At(c, r),
					PathIntegralAdd.At(
						f,
						g,
						a.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						a.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						a.TermAs[Real]("&0"),
						a.TermAs[Real]("&2 * pi"))))
		}),
})}

// CircleIntegralScale — the integral round a circle of a constant multiple of
// a function continuous on the circle is that multiple of its integral.
var CircleIntegralScale = circleIntegralScaleThm{family.Add(registry.ProofEntry{
	Name: "CircleIntegralScale",
	Key:  "prop_4d2872e699dde518",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀r:real. ∀k:complex.",
		Hypotheses: []string{
			"&0 < r",
			"∀u:complex. |u - c| = r ⇒ complex_continuous_at(f, u)",
		},
		Conclusion: "«circleInt»(λz:complex. k * f(z), c, r) = k * «circleInt»(f, c, r)",
	},
		func(
			a *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			k *Expr[Complex],
			positive, continuous Fact,
		) {
			radius := a.Have(
				"every point of the circle lies at distance |r| = r from c",
				"∀t:real. |circle_path(c, r, t) - c| = r",
				a.ForEach(func(t *Expr[Real]) Action {
					return ByArith(positive, CirclePathRadius.At(c, r, t))
				}))
			along := a.Have(
				"so f is continuous at every point of the circle",
				"∀t:real. &0 ≤ t ∧ t ≤ &2 * pi ⇒ complex_continuous_at(f, circle_path(c, r, t))",
				By(continuous, radius))
			a.Show(
				"and the integral of k·f along the circle is k times that of f",
				By(
					along,
					CirclePiecewiseSmooth.At(c, r),
					PathIntegralScale.At(
						f,
						a.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						a.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						a.TermAs[Real]("&0"),
						a.TermAs[Real]("&2 * pi"),
						k)))
		}),
})}

// CircleIntegralPrimitive — a function with a primitive on a circle
// integrates to 0 round it: the integral along the circle is the change of
// the primitive between its ends, and the circle is closed.
var CircleIntegralPrimitive = circleIntegralPrimitiveThm{family.Add(registry.ProofEntry{
	Name: "CircleIntegralPrimitive",
	Key:  "prop_2d40ebcd944e5dbf",
	Build: family.Theorem(Statement{
		Binders: "∀F f:(complex → complex). ∀c:complex. ∀r:real.",
		Hypotheses: []string{
			"&0 < r",
			"∀u:complex. |u - c| = r ⇒ complex_derivative_at(F, u, f(u)) ∧ complex_continuous_at(f, u)",
		},
		Conclusion: "«circleInt»(f, c, r) = &0",
	},
		func(
			a *Argument,
			F, f *Arrow[Complex, Complex],
			c *Expr[Complex],
			r *Expr[Real],
			positive, primitive Fact,
		) {
			radius := a.Have(
				"every point of the circle lies at distance |r| = r from c",
				"∀t:real. |circle_path(c, r, t) - c| = r",
				a.ForEach(func(t *Expr[Real]) Action {
					return ByArith(positive, CirclePathRadius.At(c, r, t))
				}))
			along := a.Have(
				"so at every point of the circle F has derivative f and f is continuous",
				"(∀t:real. "+
					"    &0 ≤ t ∧ t ≤ &2 * pi ⇒ "+
					"    complex_derivative_at(F, circle_path(c, r, t), f(circle_path(c, r, t)))) ∧ "+
					"(∀t:real. &0 ≤ t ∧ t ≤ &2 * pi ⇒ complex_continuous_at(f, circle_path(c, r, t)))",
				By(primitive, radius))
			a.Show(
				"and the integral is the change of F round the circle, which ends where it starts",
				ByArith(
					along,
					CirclePiecewiseSmooth.At(c, r),
					CirclePathClosed.At(c, r),
					PathIntegralPrimitive.At(
						F,
						f,
						a.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						a.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						a.TermAs[Real]("&0"),
						a.TermAs[Real]("&2 * pi"))))
		}),
})}

// CircleIntegralBound — the ML estimate round a circle: a function continuous
// on the circle about c of radius r > 0 and at most B in modulus there has
// integral round it at most B times the circle's length 2πr.
var CircleIntegralBound = circleIntegralBoundThm{family.Add(registry.ProofEntry{
	Name: "CircleIntegralBound",
	Key:  "prop_f8e6bf286d1d62a2",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c:complex. ∀r B:real.",
		Hypotheses: []string{
			"&0 < r",
			"∀u:complex. |u - c| = r ⇒ complex_continuous_at(f, u) ∧ |f(u)| ≤ B",
		},
		Conclusion: "|«circleInt»(f, c, r)| ≤ &2 * pi * r * B",
	},
		func(
			a *Argument,
			f *Arrow[Complex, Complex],
			c *Expr[Complex],
			r, B *Expr[Real],
			positive, bounded Fact,
		) {
			radius := a.Have(
				"every point of the circle lies at distance |r| = r from c",
				"∀t:real. |circle_path(c, r, t) - c| = r",
				a.ForEach(func(t *Expr[Real]) Action {
					return ByArith(positive, CirclePathRadius.At(c, r, t))
				}))
			along := a.Have(
				"so f is continuous and at most B in modulus at every point of the circle",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"&0 ≤ t",
						"t ≤ &2 * pi",
					},
					Conclusion: "complex_continuous_at(f, circle_path(c, r, t)) ∧ |f(circle_path(c, r, t))| ≤ B",
				},
				By(bounded, radius))
			ml := a.Have(
				"so by the ML estimate the integral is at most B times the circle's length",
				"|«circleInt»(f, c, r)| ≤ "+
					"B * real_integral(λt:real. |complex_i * &r * exp(complex_i * &t)|, &0, &2 * pi)",
				By(
					along,
					CirclePiecewiseSmooth.At(c, r),
					PathIntegralBound.At(
						f,
						a.TermAs[Fun[Real, Complex]]("circle_path(c, r)"),
						a.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &r * exp(complex_i * &t)"),
						a.TermAs[Real]("&0"),
						a.TermAs[Real]("&2 * pi"),
						B)))
			a.Show(
				"and that length is 2π·|r| = 2πr",
				ByArith(
					ml,
					CircleLength.At(r),
					a.Have(
						"r is positive, so |r| is r",
						"|r| = r",
						ByArith(positive))))
		}),
})}

// ArcIntegralBound — the ML estimate on an arc: a function continuous at the
// points of the circle of radius R > 0 about 0 over the parameter interval
// ⟦α, β⟧, and at most M in modulus there, has integral along the arc at
// most M times its length R(β − α), the speed |i·R·exp(it)| being R.
var ArcIntegralBound = arcIntegralBoundThm{family.Add(registry.ProofEntry{
	Name: "ArcIntegralBound",
	Key:  "prop_daface81e88bd99e",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀R α β M:real.",
		Hypotheses: []string{
			"&0 < R",
			"α ≤ β",
			"∀t:real. " +
				"    α ≤ t ∧ t ≤ β ⇒ " +
				"    complex_continuous_at(f, circle_path(&0, R, t)) ∧ |f(circle_path(&0, R, t))| ≤ M",
		},
		Conclusion: "|path_integral(f, circle_path(&0, R), λt:real. complex_i * &R * exp(complex_i * &t), α, β)| ≤ " +
			"M * (R * (β - α))",
	}, func(a *Argument, f *Arrow[Complex, Complex], R, α, β, M *Expr[Real], given Fact) {
		center := a.TermAs[Complex]("&0")
		circle := a.TermAs[Fun[Real, Complex]]("circle_path(&0, R)")
		velocity := a.TermAs[Fun[Real, Complex]]("λt:real. complex_i * &R * exp(complex_i * &t)")
		speed := a.Have(
			"the speed at each parameter is the radius",
			"∀t:real. |complex_i * &R * exp(complex_i * &t)| = R",
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				b.Show(
					"the unit imaginary and the imaginary exponential both have modulus one",
					ByArith(
						given,
						complex_abs.AbsI,
						complex_abs.AbsOfReal.At(R),
						complex_exp.AbsExpIOfReal.At(t),
						complex_abs.AbsMul.At(
							b.TermAs[Complex]("complex_i * &R"), b.TermAs[Complex]("exp(complex_i * &t)")),
						complex_abs.AbsMul.At(b.TermAs[Complex]("complex_i"), b.TermAs[Complex]("&R"))))
			}))
		length := a.Have(
			"integrating the constant speed multiplies it by the parameter span",
			"real_integral(λt:real. |complex_i * &R * exp(complex_i * &t)|, α, β) = R * (β - α)",
			Simp(Fwd(speed)),
			By(
				given,
				real_integral.HasIntegralConst.At(α, β, R),
				real_integral.HasIntegralValue.At(
					a.TermAs[Fun[Real, Real]]("λt:real. R"), α, β, a.TermAs[Real]("R * (β - α)"))))
		a.Show(
			"use the bound by path length",
			By(
				given,
				length,
				CircleArcPiecewiseSmooth.At(center, R, α, β),
				PathIntegralBound.At(f, circle, velocity, α, β, M)))
	}),
})}
