// contour.go — Newman's contour: the right half of the circle |z| = R,
// run from −iR to iR, closed on the left by three sides of the rectangle
// ⟦−δ, 0⟧ × ⟦−R, R⟧. The pieces are integrated one by one and never joined
// into a path: the integrals of 1/z over them add up to 2πi, by two
// primitives, and for H holomorphic on a convex open set holding the box
// −δ ≤ Re z ≤ R, |Im z| ≤ R the integrals of H(z)/z add up to 2πi·H(0), as
// they do over the two half-circles for H holomorphic on a larger disc.

package tauberian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/complex/cauchy_integral"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_derivative"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_exp"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_log"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// LeftSidesInBox — a point of the three sides iR → −δ + iR → −δ − iR → −iR
// lies in the box −δ ≤ Re z ≤ 0, |Im z| ≤ R, and is not 0.
var LeftSidesInBox = leftSidesInBoxThm{family.Add(registry.ProofEntry{
	Name: "LeftSidesInBox",
	Key:  "prop_d4f7893da918368c",
	Build: family.Theorem(Statement{
		Binders:    "∀R δ t:real.",
		Hypotheses: []string{"&0 < R", "&0 < δ", "&0 ≤ t", "t ≤ &1"},
		Conclusion: "«leftBox»(segment_path(complex_i * &R, -&δ + complex_i * &R, t)) ∧ " +
			"«leftBox»(segment_path(-&δ + complex_i * &R, -&δ - complex_i * &R, t)) ∧ " +
			"«leftBox»(segment_path(-&δ - complex_i * &R, -(complex_i * &R), t))",
		Abbrev: Abbrev{
			{Name: "leftBox", Text: "λz:complex. -δ ≤ re(z) ∧ re(z) ≤ &0 ∧ |im(z)| ≤ R ∧ z ≠ &0"},
		},
	}, func(arg *Argument, R, δ, t *Expr[Real], positiveR, positiveδ, lower, upper Fact) {
		_, aDef := arg.LetAs[Complex]("A", "complex_i * &R")
		_, bDef := arg.LetAs[Complex]("B", "-&δ + A")
		_, cDef := arg.LetAs[Complex]("C", "-&δ - A")
		_, dDef := arg.LetAs[Complex]("D", "-A")
		_, xDef := arg.LetAs[Complex]("x", "segment_path(A, B, t)")
		_, yDef := arg.LetAs[Complex]("y", "segment_path(B, C, t)")
		_, zDef := arg.LetAs[Complex]("z", "segment_path(C, D, t)")
		parts := arg.Have(
			"the straight sides interpolate their endpoint coordinates",
			"re(x) = -δ * t ∧ "+
				"im(x) = R ∧ "+
				"re(y) = -δ ∧ "+
				"im(y) = R - &2 * R * t ∧ "+
				"re(z) = -δ + δ * t ∧ "+
				"im(z) = -R",
			Simp(Fwd(xDef), Fwd(yDef), Fwd(zDef)),
			Simp(Fwd(bDef), Fwd(cDef), Fwd(dDef)),
			Simp(
				Fwd(aDef),
				Fwd(path_integral.SegmentPathDef),
				Fwd(complex_field.PartsNeg),
				Fwd(complex_field.PartsAdd),
				Fwd(complex_field.PartsSub),
				Fwd(complex_field.PartsMul),
				Fwd(complex_field.PartsOfReal),
				Fwd(complex_field.PartsI)),
			ByArith())
		scales := arg.Have(
			"both side lengths are nonnegative",
			"&0 ≤ δ ∧ &0 ≤ R",
			ByArith(positiveR, positiveδ))
		one := arg.TermAs[Real]("&1")
		width := arg.Have(
			"δt lies between zero and δ",
			"&0 ≤ δ * t ∧ δ * t ≤ δ",
			ByArith(scales, lower, upper, real_order_ring.LessEqMulLeft.At(δ, t, one)))
		height := arg.Have(
			"Rt lies between zero and R",
			"&0 ≤ R * t ∧ R * t ≤ R",
			ByArith(scales, lower, upper, real_order_ring.LessEqMulLeft.At(R, t, one)))
		arg.Show(
			"the sides lie in the left box and miss zero",
			ByArith(
				parts,
				positiveR,
				positiveδ,
				width,
				height,
				complex_field.PartsOfReal.At(arg.TermAs[Real]("&0"))))
	}),
})}

// ContourInverseIntegral — over the four pieces of the contour, the
// integrals of 1/z add up to 2πi.
var ContourInverseIntegral = contourInverseIntegralThm{family.Add(registry.ProofEntry{
	Name: "ContourInverseIntegral",
	Key:  "prop_98c0ba25c725bad7",
	Build: family.Sections(Statement{
		Binders: "∀R δ:real.",
		Hypotheses: []string{
			"&0 < R",
			"&0 < δ",
		},
		Conclusion: "«arcInt»(λz:complex. complex_inv(z), R, -(pi / &2), pi / &2) + " +
			"«sidesInt»(λz:complex. complex_inv(z), R, δ) = " +
			"&(&2 * pi) * complex_i",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			rightSlit := ctx.Lemma(
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"&0 ≤ re(z)",
						"z ≠ complex_of_real(&0)",
					},
					Conclusion: "z ∈ slit_plane",
				},
				func(arg *Argument, z *Expr[Complex], right Fact) {
					apart := arg.Have(
						"zero is the only point on the closed right half-plane that lies on the slit",
						"¬(re(z) ≤ &0 ∧ im(z) = &0)",
						ByArith(
							right,
							complex_abs.AbsLeParts.At(z),
							complex_abs.AbsNonneg.At(z),
							complex_abs.AbsEqZero.At(z)))
					arg.Show(
						"read the slit-plane definition",
						BySets(apart, complex_log.SlitPlaneDef))
				})
			negativeLog := ctx.Lemma(
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"re(z) ≤ &0",
						"z ≠ complex_of_real(&0)",
					},
					Conclusion: "complex_derivative_at(λw:complex. log(-w), z, complex_inv(z))",
				},
				func(arg *Argument, z *Expr[Complex], left, nonzero Fact) {
					inSlit := arg.Have(
						"the reflected point −z is on the right and nonzero, so off the slit",
						"-z ∈ slit_plane",
						ByArith(left, nonzero, complex_field.PartsNeg.At(z), At(rightSlit, arg.TermAs[Complex]("-z"))))
					identity := arg.TermAs[Fun[Complex, Complex]]("λw:complex. w")
					negation := arg.TermAs[Fun[Complex, Complex]]("λw:complex. -w")
					logarithm := arg.TermAs[Fun[Complex, Complex]]("complex_log")
					one := arg.TermAs[Complex]("complex_of_real(&1)")
					minusOne := arg.TermAs[Complex]("-complex_of_real(&1)")
					negatedAt := arg.Have(
						"negation has derivative minus one",
						"complex_derivative_at(λw:complex. -w, z, -complex_of_real(&1))",
						By(complex_derivative.DerivativeId.At(z), complex_derivative.DerivativeNeg.At(identity, z, one)))
					slope := arg.Have(
						"the two negative signs cancel in the derivative",
						"complex_inv(-z) * -complex_of_real(&1) = complex_inv(z)",
						ByArith(field.InvNeg.Read(complex_field.Field).At(z)))
					composed := arg.Have(
						"differentiate the logarithm after negation",
						"complex_derivative_at(complex_log ∘ (λw:complex. -w), z, complex_inv(-z) * -complex_of_real(&1))",
						By(
							inSlit,
							negatedAt,
							complex_log.LogDerivative.At(arg.TermAs[Complex]("-z")),
							complex_derivative.DerivativeChain.At(
								logarithm, negation, z, arg.TermAs[Complex]("complex_inv(-z)"), minusOne)))
					arg.Show(
						"read the composition and its derivative",
						By(arg.Simplified(composed, Fwd(functions.ComposeApply), Fwd(slope))))
				})
			leftPrimitive := ctx.Lemma(Statement{
				Binders: "∀a b:complex.",
				Hypotheses: []string{
					"∀t:real. " +
						"    &0 ≤ t ∧ t ≤ &1 ⇒ " +
						"    re(segment_path(a, b, t)) ≤ &0 ∧ segment_path(a, b, t) ≠ complex_of_real(&0)",
				},
				Conclusion: "«segInt»(complex_inv, a, b) = log(-b) - log(-a)",
			}, func(arg *Argument, a, b *Expr[Complex], segment Fact) {
				γ, pathDef := arg.LetAs[Fun[Real, Complex]]("γ", "segment_path(a, b)")
				V, velocityDef := arg.LetAs[Fun[Real, Complex]]("V", "λt:real. b - a")
				inverse := arg.TermAs[Fun[Complex, Complex]]("complex_inv")
				identity := arg.TermAs[Fun[Complex, Complex]]("λz:complex. z")
				derivative := arg.Have(
					"log of the negated point is a primitive on this segment",
					"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_derivative_at(λz:complex. log(-z), γ(t), complex_inv(γ(t)))",
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						within := c.Assume()
						c.Show(
							"apply the derivative in the reflected slit plane",
							By(within, segment.At(t), At(negativeLog, c.TermAs[Complex]("γ(t)"))))
					}))
				inverseContinuous := arg.Have(
					"the reciprocal is continuous along the segment",
					"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ complex_continuous_at(complex_inv, γ(t))",
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						within := c.Assume()
						point := c.TermAs[Complex]("γ(t)")
						c.Show(
							"use continuity of the reciprocal away from zero",
							By(
								within,
								segment.At(t),
								complex_topology.ContinuousAtId.At(point),
								complex_topology.ContinuousAtInv.At(identity, point)))
					}))
				start := arg.Have(
					"the segment starts at a",
					"γ(&0) = a",
					Simp(Fwd(pathDef), Fwd(path_integral.SegmentPathDef)),
					ByArith())
				end := arg.Have(
					"the segment ends at b",
					"γ(&1) = b",
					Simp(Fwd(pathDef), Fwd(path_integral.SegmentPathDef)),
					ByArith())
				smooth := arg.Have(
					"the segment is piecewise smooth",
					"piecewise_smooth_path(γ, V, &0, &1)",
					Simp(Fwd(pathDef), Fwd(velocityDef)),
					By(path_integral.SegmentPiecewiseSmooth.At(a, b)))
				integral := arg.Have(
					"the segment integral is the change of its primitive",
					"path_integral(complex_inv, γ, V, &0, &1) = log(-γ(&1)) - log(-γ(&0))",
					By(
						smooth,
						derivative,
						inverseContinuous,
						path_integral.PathIntegralPrimitive.At(
							arg.TermAs[Fun[Complex, Complex]]("λz:complex. log(-z)"),
							inverse,
							γ,
							V,
							arg.TermAs[Real]("&0"),
							arg.TermAs[Real]("&1"))))
				arg.Show(
					"evaluate at the two endpoints",
					By(arg.Simplified(integral, Fwd(start), Fwd(end))))
			})
			logArc := ctx.Lemma(Statement{
				Binders:    "∀R t:real.",
				Hypotheses: []string{"&0 < R", "-pi < t", "t ≤ pi"},
				Conclusion: "log(circle_path(complex_of_real(&0), R, t)) = &(log(R)) + complex_i * &t",
			}, func(arg *Argument, R, t *Expr[Real], positive, lower, upper Fact) {
				z, position := arg.LetAs[Complex]("z", "circle_path(complex_of_real(&0), R, t)")
				size := arg.Have(
					"the circle point has modulus R",
					"|z| = R",
					Simp(Fwd(position)),
					By(positive, path_integral.CirclePathModulus.At(R, t)))
				nonzero := arg.Have(
					"the point has positive modulus",
					"z ≠ complex_of_real(&0)",
					ByArith(size, positive, complex_abs.AbsEqZero.At(z)))
				polar := arg.Have(
					"the circle parameter gives the polar representation",
					"z = &(|z|) * exp(complex_i * &t)",
					Simp(Fwd(size)),
					Simp(Fwd(position), Fwd(path_integral.CirclePathDef)),
					ByArith())
				angle := arg.Have(
					"the parameter in the principal interval is the argument",
					"complex_arg(z) = t",
					By(nonzero, lower, upper, polar, complex_log.ArgUnique.At(z, t)))
				arg.Show(
					"read the logarithm from the modulus and argument",
					Simp(Fwd(complex_log.ComplexLogDef), Fwd(size), Fwd(angle)),
					Refl())
			})
			return ctx.Theorem(headline, func(arg *Argument, R, δ *Expr[Real], positiveR, positiveδ Fact) {
				arcPath := arg.Conjuncts(
					path_integral.RightArcPath.At(R),
					"the right half-circle is a piecewise smooth path",
					"it starts at −iR",
					"and ends at iR")
				A, aDef := arg.LetAs[Complex]("A", "complex_i * &R")
				B, bDef := arg.LetAs[Complex]("B", "-&δ + A")
				C, cDef := arg.LetAs[Complex]("C", "-&δ - A")
				D, dDef := arg.LetAs[Complex]("D", "-A")
				γ, circleDef := arg.LetAs[Fun[Real, Complex]]("γ", "circle_path(complex_of_real(&0), R)")
				v, _ := arg.LetAs[Fun[Real, Complex]]("v", "λt:real. A * exp(complex_i * &t)")
				inverse := arg.TermAs[Fun[Complex, Complex]]("complex_inv")
				identity := arg.TermAs[Fun[Complex, Complex]]("λz:complex. z")
				half := arg.TermAs[Real]("pi / &2")
				minusHalf := arg.TermAs[Real]("-(pi / &2)")

				leftPoints := arg.Have(
					"all three straight sides stay in the closed left half-plane and miss zero",
					Statement{
						Binders: "∀t:real.",
						Hypotheses: []string{
							"&0 ≤ t",
							"t ≤ &1",
						},
						Conclusion: "re(segment_path(A, B, t)) ≤ &0 ∧ " +
							"segment_path(A, B, t) ≠ complex_of_real(&0) ∧ " +
							"(re(segment_path(B, C, t)) ≤ &0 ∧ segment_path(B, C, t) ≠ complex_of_real(&0)) ∧ " +
							"(re(segment_path(C, D, t)) ≤ &0 ∧ segment_path(C, D, t) ≠ complex_of_real(&0))",
					},
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						within := c.Assume()
						c.Show(
							"read the three left-side bounds",
							Simp(Fwd(bDef), Fwd(cDef), Fwd(dDef)),
							Simp(Fwd(aDef)),
							By(positiveR, positiveδ, within, LeftSidesInBox.At(R, δ, t)))
					}))
				top := arg.Have(
					"evaluate the integral along the top side",
					"«segInt»(complex_inv, A, B) = log(-B) - log(-A)",
					By(leftPoints, At(leftPrimitive, A, B)))
				middle := arg.Have(
					"evaluate the integral along the middle side",
					"«segInt»(complex_inv, B, C) = log(-C) - log(-B)",
					By(leftPoints, At(leftPrimitive, B, C)))
				bottom := arg.Have(
					"evaluate the integral along the bottom side",
					"«segInt»(complex_inv, C, D) = log(-D) - log(-C)",
					By(leftPoints, At(leftPrimitive, C, D)))
				telescope := arg.Have(
					"the intermediate logarithms cancel along the straight sides",
					"«segInt»(complex_inv, A, B) + «segInt»(complex_inv, B, C) + «segInt»(complex_inv, C, D) = "+
						"log(-D) - log(-A)",
					ByArith(top, middle, bottom))
				negativeEnd := arg.Have(
					"negating the bottom endpoint gives the top endpoint",
					"-D = A",
					ByArith(dDef))
				sides := arg.Simplified(telescope, Fwd(negativeEnd), Rev(dDef))

				rightPoints := arg.Have(
					"the right half-circle stays in the closed right half-plane and misses zero",
					"∀t:real. -(pi / &2) ≤ t ∧ t ≤ pi / &2 ⇒ &0 ≤ re(γ(t)) ∧ γ(t) ≠ complex_of_real(&0)",
					Simp(Fwd(circleDef)),
					arg.ForEach(func(t *Expr[Real]) Action { return By(positiveR, RightArcInBox.At(R, t)) }))
				derivative := arg.Have(
					"log is a primitive of the reciprocal along the right arc",
					Statement{
						Binders:    "∀t:real.",
						Hypotheses: []string{"-(pi / &2) ≤ t", "t ≤ pi / &2"},
						Conclusion: "complex_derivative_at(complex_log, γ(t), complex_inv(γ(t)))",
					},
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						within := c.Assume()
						c.Show(
							"the point lies off the slit, where the principal logarithm differentiates",
							By(
								within,
								rightPoints.At(t),
								At(rightSlit, c.TermAs[Complex]("γ(t)")),
								complex_log.LogDerivative.At(c.TermAs[Complex]("γ(t)"))))
					}))
				inverseContinuous := arg.Have(
					"the reciprocal is continuous along the right arc",
					"∀t:real. -(pi / &2) ≤ t ∧ t ≤ pi / &2 ⇒ complex_continuous_at(complex_inv, γ(t))",
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						within := c.Assume()
						point := c.TermAs[Complex]("γ(t)")
						c.Show(
							"use the nonzero modulus and continuity of inversion",
							By(
								within,
								rightPoints.At(t),
								complex_topology.ContinuousAtId.At(point),
								complex_topology.ContinuousAtInv.At(identity, point)))
					}))
				rawArc := arg.Have(
					"the right arc integral is the change in the principal logarithm",
					"path_integral(complex_inv, γ, v, -(pi / &2), pi / &2) = log(γ(pi / &2)) - log(γ(-(pi / &2)))",
					By(
						arcPath[0],
						derivative,
						inverseContinuous,
						path_integral.PathIntegralPrimitive.At(
							arg.TermAs[Fun[Complex, Complex]]("complex_log"), inverse, γ, v, minusHalf, half)))
				arc := arg.Simplified(rawArc, Fwd(arcPath[1]), Fwd(arcPath[2]))
				angles := arg.Have(
					"the endpoint angles lie in the principal interval",
					"-pi < -(pi / &2) ∧ -(pi / &2) ≤ pi ∧ -pi < pi / &2 ∧ pi / &2 ≤ pi",
					ByArith(real_trigonometry.PiBounds))
				logD := arg.Have(
					"evaluate the logarithm at the bottom endpoint",
					"log(D) = &(log(R)) + complex_i * &(-(pi / &2))",
					Simp(Rev(arcPath[1])),
					Simp(Fwd(circleDef)),
					By(positiveR, angles, At(logArc, R, minusHalf)))
				logA := arg.Have(
					"evaluate the logarithm at the top endpoint",
					"log(A) = &(log(R)) + complex_i * &(pi / &2)",
					Simp(Rev(arcPath[2])),
					Simp(Fwd(circleDef)),
					By(positiveR, angles, At(logArc, R, half)))
				halfSum := arg.Have(
					"two half angles add to π",
					"pi / &2 + pi / &2 = pi",
					ByArith())
				halfEmbedded := arg.Have(
					"the embedding preserves the sum of the half angles",
					"&(pi / &2) + &(pi / &2) = complex_of_real(pi)",
					Simp(Rev(complex_field.OfRealAdd), Fwd(halfSum)),
					Refl())
				gap := arg.Have(
					"the logarithmic difference is iπ",
					"log(A) - log(D) = complex_of_real(pi) * complex_i",
					Simp(Fwd(logD), Fwd(logA), Fwd(complex_field.OfRealNeg)),
					CalcEq(
						Leg(
							arg.TermAs[Complex]("complex_i * (&(pi / &2) + &(pi / &2))"),
							"the real logarithmic terms cancel",
							ByArith()),
						FinalLeg(
							"the angles add to π",
							Simp(Fwd(halfEmbedded)),
							ByArith())))
				double := arg.Have(
					"the two half-circle contributions double π",
					"pi + pi = &2 * pi",
					ByArith())
				doubleEmbedded := arg.Have(
					"embed the sum of the two angles",
					"complex_of_real(pi) + complex_of_real(pi) = &(&2 * pi)",
					Simp(Rev(complex_field.OfRealAdd), Fwd(double)),
					Refl())
				arg.Show(
					"both parts contribute iπ",
					CalcEq(
						Leg(
							arg.TermAs[Complex]("(complex_of_real(pi) + complex_of_real(pi)) * complex_i"),
							"substitute the arc and side values",
							ByArith(arc, sides, gap)),
						FinalLeg(
							"combine the equal contributions",
							Simp(Fwd(doubleEmbedded)),
							Refl())))
			})
		}),
	Reading: "This is the winding of the contour once about " +
		"0, computed by two primitives; no winding index is formed.",
})}

// ContourFormula — for H holomorphic on a convex open set containing the
// contour and 0, the integrals of H(z)/z over the four pieces add up to
// 2πi·H(0).
var ContourFormula = contourFormulaThm{family.Add(registry.ProofEntry{
	Name: "ContourFormula",
	Key:  "prop_a1a9fe387330025e",
	Build: family.Sections(Statement{
		Binders: "∀H:(complex → complex). ∀V:set(complex). ∀R δ:real.",
		Hypotheses: []string{
			"&0 < R",
			"&0 < δ",
			"V ∈ complex_topology",
			"«convex»(V)",
			"holomorphic_on(V, H)",
			"∀z:complex. z ∈ «box»(R, δ) ⇒ z ∈ V",
		},
		Conclusion: "«arcInt»(λz:complex. H(z) / z, R, -(pi / &2), pi / &2) + " +
			"«sidesInt»(λz:complex. H(z) / z, R, δ) = " +
			"&(&2 * pi) * complex_i * H(complex_of_real(&0))",
		Abbrev: Abbrev{
			{Name: "leftBox", Text: "λz:complex. " +
				"    -δ ≤ re(z) ∧ re(z) ≤ &0 ∧ |im(z)| ≤ R ∧ z ≠ complex_of_real(&0)"},
			{Name: "admissible", Text: "λz:complex. z ∈ V ∧ z ≠ complex_of_real(&0)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			decompose := ctx.Lemma(Statement{
				Binders: "∀H F φ:(complex → complex). ∀γ v:(real → complex). ∀a b:real.",
				Hypotheses: []string{
					"∀z:complex. H(z) - H(complex_of_real(&0)) = φ(z) * z",
					"a ≤ b",
					"piecewise_smooth_path(γ, v, a, b)",
					"∀t:real. " +
						"    a ≤ t ∧ t ≤ b ⇒ " +
						"    γ(t) ≠ complex_of_real(&0) ∧ " +
						"    complex_derivative_at(F, γ(t), φ(γ(t))) ∧ " +
						"    complex_continuous_at(φ, γ(t))",
				},
				Conclusion: "path_integral(λz:complex. H(z) / z, γ, v, a, b) = " +
					"F(γ(b)) - F(γ(a)) + H(complex_of_real(&0)) * path_integral(complex_inv, γ, v, a, b)",
			}, func(
				arg *Argument, _, F, φ *Arrow[Complex, Complex], γ, v *Arrow[Real, Complex], a, b *Expr[Real],
				factor, ordered, smooth, along Fact,
			) {
				c, _ := arg.LetAs[Complex]("c", "H(complex_of_real(&0))")
				q, qDef := arg.LetAs[Fun[Complex, Complex]]("q", "λz:complex. H(z) / z")
				u, uDef := arg.LetAs[Fun[Complex, Complex]]("u", "λz:complex. c * complex_inv(z)")
				p, pDef := arg.LetAs[Fun[Complex, Complex]]("p", "λz:complex. φ(z) + u(z)")
				inverse := arg.TermAs[Fun[Complex, Complex]]("complex_inv")
				identity := arg.TermAs[Fun[Complex, Complex]]("λz:complex. z")
				regular := arg.Have(
					"away from zero the quotient splits into the regular part and a reciprocal",
					"∀z:complex. z ≠ complex_of_real(&0) ⇒ q(z) = p(z)",
					Derive(func(d *Argument) {
						z := d.FixAs[Complex]("z")
						nonzero := d.Assume()
						d.Show(
							"divide the difference-quotient identity by z",
							Simp(Fwd(qDef), Fwd(pDef), Fwd(uDef)),
							ByArith(nonzero, Scaled(d.TermAs[Complex]("complex_inv(z)"), factor.At(z))))
					}))
				limits := arg.Have(
					"the interval is ordered so its extrema are a and b",
					"min(a, b) = a ∧ max(a, b) = b",
					Simp(Fwd(real_sup_inf.RealMinDef), Fwd(real_sup_inf.RealMaxDef)),
					By(ordered))
				agree := arg.Have(
					"the integrands agree at every point between the parameter endpoints",
					"∀t:real. min(a, b) ≤ t ∧ t ≤ max(a, b) ⇒ q(γ(t)) = p(γ(t))",
					Derive(func(d *Argument) {
						t := d.FixAs[Real]("t")
						inside := d.Assume()
						within := d.Have(
							"the parameter lies between a and b",
							"a ≤ t ∧ t ≤ b",
							ByArith(limits, inside))
						nonzero := d.Have(
							"the path misses zero",
							"γ(t) ≠ complex_of_real(&0)",
							By(within, along.At(t)))
						d.Show(
							"read the factorization at this path point",
							By(nonzero, regular.At(d.TermAs[Complex]("γ(t)"))))
					}))
				primitive := arg.Have(
					"F has derivative φ along the path",
					"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_derivative_at(F, γ(t), φ(γ(t)))",
					Derive(func(d *Argument) {
						t := d.FixAs[Real]("t")
						d.Show(
							"read the derivative assumption at t",
							By(d.Assume(), along.At(t)))
					}))
				phiContinuous := arg.Have(
					"φ is continuous along the path",
					"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(φ, γ(t))",
					Derive(func(d *Argument) {
						t := d.FixAs[Real]("t")
						d.Show(
							"read the continuity assumption at t",
							By(d.Assume(), along.At(t)))
					}))
				invContinuous := arg.Have(
					"the reciprocal is continuous along the path",
					"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(complex_inv, γ(t))",
					Derive(func(d *Argument) {
						t := d.FixAs[Real]("t")
						point := d.TermAs[Complex]("γ(t)")
						d.Show(
							"the path's nonzero points are continuity points of inversion",
							By(
								d.Assume(),
								along.At(t),
								complex_topology.ContinuousAtId.At(point),
								complex_topology.ContinuousAtInv.At(identity, point)))
					}))
				uContinuous := arg.Have(
					"the fixed multiple of the reciprocal is continuous along the path",
					"∀t:real. a ≤ t ∧ t ≤ b ⇒ complex_continuous_at(u, γ(t))",
					Derive(func(d *Argument) {
						t := d.FixAs[Real]("t")
						within := d.Assume()
						point := d.TermAs[Complex]("γ(t)")
						d.Show(
							"multiply the reciprocal by the continuous constant",
							Simp(Fwd(uDef)),
							By(
								within,
								invContinuous.At(t),
								complex_topology.ContinuousAtConst.At(point, c),
								complex_topology.ContinuousAtMul.At(
									d.TermAs[Fun[Complex, Complex]]("λz:complex. c"), inverse, point)))
					}))
				same := arg.Have(
					"the original path integral equals that of the split integrand",
					"path_integral(q, γ, v, a, b) = path_integral(p, γ, v, a, b)",
					By(agree, path_integral.PathIntegralCongruence.At(q, p, γ, v, a, b)))
				sum := arg.Have(
					"the split integral adds the integrals of the two terms",
					"path_integral(p, γ, v, a, b) = path_integral(φ, γ, v, a, b) + path_integral(u, γ, v, a, b)",
					Simp(Fwd(pDef)),
					By(smooth, phiContinuous, uContinuous, path_integral.PathIntegralAdd.At(φ, u, γ, v, a, b)))
				scaled := arg.Have(
					"the pole integral is the residue times the integral of the reciprocal",
					"path_integral(u, γ, v, a, b) = c * path_integral(complex_inv, γ, v, a, b)",
					Simp(Fwd(uDef)),
					By(smooth, invContinuous, path_integral.PathIntegralScale.At(inverse, γ, v, a, b, c)))
				regularIntegral := arg.Have(
					"the regular integral is the change in the primitive",
					"path_integral(φ, γ, v, a, b) = F(γ(b)) - F(γ(a))",
					By(smooth, primitive, phiContinuous, path_integral.PathIntegralPrimitive.At(F, φ, γ, v, a, b)))
				arg.Show(
					"combine the regular and pole integrals",
					By(same, sum, scaled, regularIntegral))
			})
			return ctx.Theorem(headline, func(
				arg *Argument, H *Arrow[Complex, Complex], V *Expr[Set[Complex]], R, δ *Expr[Real],
				positiveR, positiveδ, open, convex, holomorphic, rectangle Fact,
			) {
				zero := arg.TermAs[Complex]("complex_of_real(&0)")
				residue := arg.TermAs[Complex]("H(complex_of_real(&0))")
				centreBounds := arg.Have(
					"the origin lies in the rectangle",
					"-δ ≤ re(complex_of_real(&0)) ∧ re(complex_of_real(&0)) ≤ R ∧ |im(complex_of_real(&0))| ≤ R",
					ByArith(positiveR, positiveδ, complex_field.PartsOfReal.At(arg.TermAs[Real]("&0"))))
				centre := arg.Have(
					"the origin lies in V",
					"complex_of_real(&0) ∈ V",
					By(centreBounds, rectangle.At(zero)))
				φ, patch := arg.ObtainAs[Fun[Complex, Complex]](
					"the difference quotient extends across the origin",
					"∃φ:(complex → complex). "+
						"    (∀z:complex. H(z) - H(complex_of_real(&0)) = φ(z) * (z - complex_of_real(&0))) ∧ "+
						"    complex_continuous_on(V, φ) ∧ "+
						"    holomorphic_on(V ∖ {complex_of_real(&0)}, φ)",
					By(holomorphic, centre, cauchy_integral.DifferenceQuotientHolomorphic.At(V, H, zero)))
				parts := arg.Conjuncts(
					patch,
					"φ is the difference quotient of H at the origin",
					"φ is continuous on V",
					"φ is holomorphic on V away from the origin")
				subtract := arg.Have(
					"subtracting the origin fixes each point",
					"∀z:complex. z - complex_of_real(&0) = z",
					StripQuant(),
					ByArith())
				factor := arg.Simplified(parts[0], Fwd(subtract))
				F, primitive := arg.ObtainAs[Fun[Complex, Complex]](
					"the regular part has a primitive on the convex open set",
					"∃F:(complex → complex). ∀z:complex. z ∈ V ⇒ complex_derivative_at(F, z, φ(z))",
					By(open, convex, parts[1], parts[2], cauchy_integral.ConvexPrimitive.At(V, φ, zero)))
				continuity := arg.Have(
					"φ is continuous at every point of V",
					"∀z:complex. z ∈ V ⇒ complex_continuous_at(φ, z)",
					By(open, parts[1], complex_topology.ContinuousOnOpenIff.At(V, φ)))

				arcPath := arg.Conjuncts(
					path_integral.RightArcPath.At(R),
					"the right half-circle is a piecewise smooth path",
					"it starts at −iR",
					"and ends at iR")
				A, aDef := arg.LetAs[Complex]("A", "complex_i * &R")
				B, bDef := arg.LetAs[Complex]("B", "-&δ + A")
				C, cDef := arg.LetAs[Complex]("C", "-&δ - A")
				D, dDef := arg.LetAs[Complex]("D", "-A")
				γ, circleDef := arg.LetAs[Fun[Real, Complex]]("γ", "circle_path(complex_of_real(&0), R)")
				v, velocityDef := arg.LetAs[Fun[Real, Complex]]("v", "λt:real. A * exp(complex_i * &t)")
				_, qDef := arg.LetAs[Fun[Complex, Complex]]("q", "λz:complex. H(z) / z")
				half := arg.TermAs[Real]("pi / &2")
				minusHalf := arg.TermAs[Real]("-(pi / &2)")
				onPath := arg.Have(
					"on a smooth path inside V and off zero the quotient integral has the stated split",
					Statement{
						Binders: "∀η w:(real → complex). ∀a b:real.",
						Hypotheses: []string{
							"a ≤ b",
							"piecewise_smooth_path(η, w, a, b)",
							"∀t:real. a ≤ t ∧ t ≤ b ⇒ «admissible»(η(t))",
						},
						Conclusion: "path_integral(q, η, w, a, b) = " +
							"F(η(b)) - F(η(a)) + H(complex_of_real(&0)) * path_integral(complex_inv, η, w, a, b)",
					},
					Derive(func(c *Argument) {
						η := c.FixAs[Fun[Real, Complex]]("η")
						w := c.FixAs[Fun[Real, Complex]]("w")
						a, b := c.FixAs[Real]("a"), c.FixAs[Real]("b")
						given := c.Assume()
						requirements := c.Conjuncts(
							given,
							"the parameter interval is ordered",
							"the path is piecewise smooth",
							"the path stays in V and off the origin")
						along := c.Have(
							"the path avoids the pole and admits the primitive and its derivative",
							Statement{
								Binders: "∀t:real.",
								Hypotheses: []string{
									"a ≤ t",
									"t ≤ b",
								},
								Conclusion: "η(t) ≠ complex_of_real(&0) ∧ " +
									"complex_derivative_at(F, η(t), φ(η(t))) ∧ " +
									"complex_continuous_at(φ, η(t))",
							},
							Derive(func(d *Argument) {
								t := d.FixAs[Real]("t")
								within := d.Assume()
								point := d.TermAs[Complex]("η(t)")
								inside := d.Have(
									"the path point is in V and not zero",
									"«admissible»(η(t))",
									By(within, At(requirements[2], t)))
								d.Show(
									"the derivative and continuity apply at the path point",
									By(inside, primitive.At(point), continuity.At(point)))
							}))
						c.Show(
							"apply the decomposition to this path",
							Simp(Fwd(qDef)),
							By(requirements[0], requirements[1], along, factor, At(decompose, H, F, φ, η, w, a, b)))
					}))
				onSegment := arg.Have(
					"along such a segment the quotient integral is the change "+
						"of the primitive plus H(0) times the integral of 1/z",
					Statement{
						Binders: "∀a b:complex.",
						Hypotheses: []string{
							"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ «admissible»(segment_path(a, b, t))",
						},
						Conclusion: "«segInt»(q, a, b) = " +
							"F(b) - F(a) + H(complex_of_real(&0)) * «segInt»(complex_inv, a, b)",
					},
					Derive(func(c *Argument) {
						a, b := c.FixAs[Complex]("a"), c.FixAs[Complex]("b")
						inside := c.Assume()
						atEnds := c.Have(
							"apply the smooth-path decomposition to the segment",
							"«segInt»(q, a, b) = "+
								"F(segment_path(a, b, &1)) - "+
								"F(segment_path(a, b, &0)) + "+
								"H(complex_of_real(&0)) * «segInt»(complex_inv, a, b)",
							By(
								inside,
								path_integral.SegmentPiecewiseSmooth.At(a, b),
								onPath.At(
									c.TermAs[Fun[Real, Complex]]("segment_path(a, b)"), c.TermAs[Fun[Real, Complex]]("λt:real. b - a"),
									c.TermAs[Real]("&0"), c.TermAs[Real]("&1"))))
						start := c.Have(
							"the segment starts at a",
							"segment_path(a, b, &0) = a",
							Simp(Fwd(path_integral.SegmentPathDef)),
							ByArith())
						end := c.Have(
							"the segment ends at b",
							"segment_path(a, b, &1) = b",
							Simp(Fwd(path_integral.SegmentPathDef)),
							ByArith())
						c.Show(
							"read the primitive at the segment endpoints",
							By(c.Simplified(atEnds, Fwd(start), Fwd(end))))
					}))
				leftInside := arg.Have(
					"nonzero points in the left rectangle are in V",
					"∀z:complex. «leftBox»(z) ⇒ «admissible»(z)",
					Derive(func(c *Argument) {
						z := c.FixAs[Complex]("z")
						left := c.Assume()
						bounds := c.Have(
							"the left rectangle is contained in the given rectangle",
							"-δ ≤ re(z) ∧ re(z) ≤ R ∧ |im(z)| ≤ R",
							ByArith(left, positiveR))
						c.Show(
							"apply the rectangle hypothesis",
							By(left, bounds, rectangle.At(z)))
					}))
				leftBounds := arg.Have(
					"the three sides meet the left-rectangle bounds and avoid the origin",
					Statement{
						Binders:    "∀t:real.",
						Hypotheses: []string{"&0 ≤ t", "t ≤ &1"},
						Conclusion: "«leftBox»(segment_path(A, B, t)) ∧ " +
							"«leftBox»(segment_path(B, C, t)) ∧ " +
							"«leftBox»(segment_path(C, D, t))",
					},
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						within := c.Assume()
						c.Show(
							"apply the straight-side geometry under the endpoint definitions",
							Simp(Fwd(bDef), Fwd(cDef), Fwd(dDef)),
							Simp(Fwd(aDef)),
							By(within, positiveR, positiveδ, LeftSidesInBox.At(R, δ, t)))
					}))
				sidesInside := arg.Have(
					"the three sides lie in V and avoid the origin",
					Statement{
						Binders:    "∀t:real.",
						Hypotheses: []string{"&0 ≤ t", "t ≤ &1"},
						Conclusion: "«admissible»(segment_path(A, B, t)) ∧ " +
							"«admissible»(segment_path(B, C, t)) ∧ " +
							"«admissible»(segment_path(C, D, t))",
					},
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						within := c.Assume()
						c.Show(
							"each side point is in the part of the rectangle covered by V",
							By(
								within,
								leftBounds.At(t),
								leftInside.At(c.TermAs[Complex]("segment_path(A, B, t)")),
								leftInside.At(c.TermAs[Complex]("segment_path(B, C, t)")),
								leftInside.At(c.TermAs[Complex]("segment_path(C, D, t)"))))
					}))
				top := arg.Have(
					"evaluate the quotient integral on the top side",
					"«segInt»(q, A, B) = F(B) - F(A) + H(complex_of_real(&0)) * «segInt»(complex_inv, A, B)",
					By(sidesInside, onSegment.At(A, B)))
				middle := arg.Have(
					"evaluate the quotient integral on the middle side",
					"«segInt»(q, B, C) = F(C) - F(B) + H(complex_of_real(&0)) * «segInt»(complex_inv, B, C)",
					By(sidesInside, onSegment.At(B, C)))
				bottom := arg.Have(
					"evaluate the quotient integral on the bottom side",
					"«segInt»(q, C, D) = F(D) - F(C) + H(complex_of_real(&0)) * «segInt»(complex_inv, C, D)",
					By(sidesInside, onSegment.At(C, D)))

				arcInside := arg.Have(
					"the right arc lies in V and avoids the origin",
					"∀t:real. -(pi / &2) ≤ t ∧ t ≤ pi / &2 ⇒ «admissible»(γ(t))",
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						within := c.Assume()
						bounds := c.Have(
							"the right arc lies in its bounding box and is nonzero",
							"&0 ≤ re(γ(t)) ∧ re(γ(t)) ≤ R ∧ |im(γ(t))| ≤ R ∧ γ(t) ≠ complex_of_real(&0)",
							Simp(Fwd(circleDef)),
							By(within, positiveR, RightArcInBox.At(R, t)))
						inRectangle := c.Have(
							"the right box lies in the given rectangle",
							"-δ ≤ re(γ(t)) ∧ re(γ(t)) ≤ R ∧ |im(γ(t))| ≤ R",
							ByArith(bounds, positiveδ))
						c.Show(
							"apply the rectangle hypothesis to the nonzero point",
							By(inRectangle, bounds, rectangle.At(c.TermAs[Complex]("γ(t)"))))
					}))
				ordered := arg.Have(
					"the right arc has ordered parameters",
					"-(pi / &2) ≤ pi / &2",
					ByArith(real_trigonometry.PiBounds))
				rawArc := arg.Have(
					"evaluate the quotient integral along the right arc",
					"path_integral(q, γ, v, -(pi / &2), pi / &2) = "+
						"F(γ(pi / &2)) - "+
						"F(γ(-(pi / &2))) + "+
						"H(complex_of_real(&0)) * path_integral(complex_inv, γ, v, -(pi / &2), pi / &2)",
					By(ordered, arcPath[0], arcInside, onPath.At(γ, v, minusHalf, half)))
				arc := arg.Simplified(rawArc, Fwd(arcPath[1]), Fwd(arcPath[2]))
				inverseIntegral := arg.Have(
					"the integrals of the reciprocal on all four pieces sum to two πi",
					"path_integral(complex_inv, γ, v, -(pi / &2), pi / &2) + "+
						"(«segInt»(complex_inv, A, B) + «segInt»(complex_inv, B, C) + «segInt»(complex_inv, C, D)) = "+
						"&(&2 * pi) * complex_i",
					Simp(Fwd(circleDef), Fwd(velocityDef)),
					Simp(Fwd(bDef), Fwd(cDef), Fwd(dDef)),
					Simp(Fwd(aDef)),
					By(positiveR, positiveδ, ContourInverseIntegral.At(R, δ)))
				arg.Show(
					"the four primitive increments cancel, leaving the pole contribution",
					ByArith(arc, top, middle, bottom, Scaled(residue, inverseIntegral)))
			})
		}),
	Reading: "The fourth hypothesis is the convexity of V and the sixth " +
		"puts the contour, with the point 0, inside V. The pieces are never " +
		"joined into one path: the primitive makes that unnecessary.",
})}

// CircleFormula — for H holomorphic on a disc of radius greater than R,
// the integrals of H(z)/z over the right and the left half-circle add up
// to 2πi·H(0).
var CircleFormula = circleFormulaThm{family.Add(registry.ProofEntry{
	Name: "CircleFormula",
	Key:  "prop_2b40c8cd0b26f44e",
	Build: family.Sections(Statement{
		Binders: "∀H:(complex → complex). ∀R ρ:real.",
		Hypotheses: []string{
			"&0 < R",
			"R < ρ",
			"holomorphic_on(«disc»(complex_of_real(&0), ρ), H)",
		},
		Conclusion: "«arcInt»(λz:complex. H(z) / z, R, -(pi / &2), pi / &2) + " +
			"«arcInt»(λz:complex. H(z) / z, R, pi / &2, &3 * pi / &2) = " +
			"&(&2 * pi) * complex_i * H(complex_of_real(&0))",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			periodicIntegral := ctx.Lemma(Statement{
				Binders: "∀u:(real → complex).",
				Hypotheses: []string{
					"∀t:real. u(t + &2 * pi) = u(t)",
					"real_continuous_on(⟦-(pi / &2), &2 * pi⟧, λt:real. re(u(t)))",
					"real_continuous_on(⟦-(pi / &2), &2 * pi⟧, λt:real. im(u(t)))",
				},
				Conclusion: "complex_integral(u, -(pi / &2), pi / &2) + " +
					"complex_integral(u, pi / &2, &3 * pi / &2) = " +
					"complex_integral(u, &0, &2 * pi)",
			}, func(arg *Argument, u *Arrow[Real, Complex], periodic, reContinuous, imContinuous Fact) {
				A, leftDef := arg.LetAs[Real]("A", "-(pi / &2)")
				B, rightDef := arg.LetAs[Real]("B", "&3 * pi / &2")
				C, middleDef := arg.LetAs[Real]("C", "pi / &2")
				P, periodDef := arg.LetAs[Real]("P", "&2 * pi")
				zero := arg.TermAs[Real]("&0")
				bounds := arg.Have(
					"all endpoints in the affine changes and splits are in the continuity interval",
					"A ≤ &0 ∧ "+
						"&0 ≤ C ∧ "+
						"C ≤ B ∧ "+
						"B ≤ P ∧ "+
						"A ≤ A ∧ "+
						"A ≤ C ∧ "+
						"A ≤ B ∧ "+
						"A ≤ P ∧ "+
						"&0 ≤ P ∧ "+
						"C ≤ P ∧ "+
						"P ≤ P ∧ "+
						"A ≤ A + C ∧ "+
						"A + C ≤ P ∧ "+
						"A ≤ B + C ∧ "+
						"B + C ≤ P",
					ByArith(leftDef, rightDef, middleDef, periodDef, real_trigonometry.PiBounds))
				leftEnd := arg.Have(
					"the left interval of length C ends at zero",
					"A + C = &0",
					ByArith(leftDef))
				rightEnd := arg.Have(
					"the right interval of length C ends at P",
					"B + C = P",
					ByArith(rightDef, middleDef, periodDef))
				translate := arg.Have(
					"B is A shifted by one period",
					"A + P = B",
					ByArith(leftDef, rightDef, middleDef, periodDef))
				left := arg.Have(
					"rescale the interval from A to zero to the unit interval",
					"complex_integral(λt:real. u(A + C * t) * &C, &0, &1) = complex_integral(u, A, A + C)",
					By(bounds, reContinuous, imContinuous, path_integral.ComplexIntegralAffine.At(u, A, P, C, A)))
				right := arg.Have(
					"rescale the interval from B to P to the unit interval",
					"complex_integral(λt:real. u(B + C * t) * &C, &0, &1) = complex_integral(u, B, B + C)",
					By(bounds, reContinuous, imContinuous, path_integral.ComplexIntegralAffine.At(u, A, P, C, B)))
				rescaled := arg.Have(
					"the two rescaled integrands agree by periodicity",
					"(λt:real. u(A + C * t) * &C) = (λt:real. u(B + C * t) * &C)",
					Funext(),
					Derive(func(c *Argument) {
						c.FixAs[Real]("t")
						shift := c.Have(
							"the affine arguments differ by the period",
							"B + C * t = A + C * t + P",
							ByArith(translate))
						c.Show(
							"periodicity identifies the two values",
							Simp(Fwd(shift), Fwd(periodic)),
							Refl())
					}))
				tails := arg.Have(
					"the omitted and added intervals have the same integral",
					"complex_integral(u, A, &0) = complex_integral(u, B, P)",
					By(arg.Simplified(left, Fwd(leftEnd), Fwd(rescaled)), arg.Simplified(right, Fwd(rightEnd))))
				atMiddle := arg.Have(
					"join the two half-circles",
					"complex_integral(u, A, C) + complex_integral(u, C, B) = complex_integral(u, A, B)",
					By(bounds, reContinuous, imContinuous, path_integral.ComplexIntegralAdditive.At(u, A, P, A, C, B)))
				atZero := arg.Have(
					"split the shifted full interval at zero",
					"complex_integral(u, A, &0) + complex_integral(u, &0, B) = complex_integral(u, A, B)",
					By(
						bounds,
						reContinuous,
						imContinuous,
						path_integral.ComplexIntegralAdditive.At(u, A, P, A, zero, B)))
				atRight := arg.Have(
					"split the standard interval at B",
					"complex_integral(u, &0, B) + complex_integral(u, B, P) = complex_integral(u, &0, P)",
					By(
						bounds,
						reContinuous,
						imContinuous,
						path_integral.ComplexIntegralAdditive.At(u, A, P, zero, B, P)))
				arg.Show(
					"replace the translated tail and add the intervals",
					ByArith(tails, atMiddle, atZero, atRight))
			})
			return ctx.Theorem(headline, func(
				arg *Argument,
				H *Arrow[Complex, Complex],
				R, ρ *Expr[Real],
				positive, smaller, holomorphic Fact,
			) {
				disc, discDef := arg.LetAs[Set[Complex]]("D", "«disc»(complex_of_real(&0), ρ)")
				γ, circleDef := arg.LetAs[Fun[Real, Complex]]("γ", "circle_path(complex_of_real(&0), R)")
				_, velocityDef := arg.LetAs[Fun[Real, Complex]](
					"v", "λt:real. complex_i * &R * exp(complex_i * &t)")
				_, quotientDef := arg.LetAs[Fun[Complex, Complex]]("q", "λz:complex. H(z) / z")
				u, integrandDef := arg.LetAs[Fun[Real, Complex]]("u", "λt:real. q(γ(t)) * v(t)")
				K, rotatedDef := arg.LetAs[Fun[Complex, Complex]]("K", "λz:complex. complex_i * H(z)")
				zero := arg.TermAs[Complex]("complex_of_real(&0)")
				left := arg.TermAs[Real]("-(pi / &2)")
				period := arg.TermAs[Real]("&2 * pi")
				I := arg.TermAs[Set[Real]]("⟦-(pi / &2), &2 * pi⟧")
				subtractZero := arg.Have(
					"subtracting the centre leaves each point fixed",
					"∀z:complex. z - complex_of_real(&0) = z",
					StripQuant(),
					ByArith())
				radius := arg.Have(
					"the circle has constant modulus R",
					"∀t:real. |γ(t)| = R",
					Simp(Fwd(circleDef)),
					arg.ForEach(func(t *Expr[Real]) Action {
						return By(positive, path_integral.CirclePathModulus.At(R, t))
					}))
				inDisc := arg.Have(
					"the circle lies in the disc of holomorphy",
					"∀t:real. γ(t) ∈ D",
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						inside := c.Have(
							"the modulus R is below ρ",
							"|γ(t) - complex_of_real(&0)| < ρ",
							Simp(Fwd(subtractZero)),
							ByArith(radius.At(t), smaller))
						c.Show(
							"read membership in the disc",
							BySets(discDef, inside))
					}))
				velocity := arg.Have(
					"the circle's velocity is i times its position",
					"∀t:real. v(t) = complex_i * γ(t)",
					StripQuant(),
					Simp(Fwd(velocityDef), Fwd(circleDef), Fwd(path_integral.CirclePathDef)),
					ByArith())
				cancel := arg.Have(
					"on the circle the integrand is i times H",
					"u = (λt:real. K(γ(t)))",
					Funext(),
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						point := c.TermAs[Complex]("γ(t)")
						nonzero := c.Have(
							"the circle misses its centre",
							"γ(t) ≠ complex_of_real(&0)",
							ByArith(radius.At(t), positive, complex_abs.AbsEqZero.At(point)))
						quotient := c.Have(
							"the nonzero point cancels its quotient",
							"H(γ(t)) / γ(t) * γ(t) = H(γ(t))",
							By(nonzero, field.DivRightMul.Read(complex_field.Field).At(H.Apply(point), point)))
						c.Show(
							"associate the velocity so the circle point cancels",
							Simp(Fwd(integrandDef), Fwd(quotientDef), Fwd(rotatedDef), Fwd(velocity)),
							CalcEq(
								Leg(
									c.TermAs[Complex]("complex_i * (H(γ(t)) / γ(t) * γ(t))"),
									"move i before the quotient",
									ByArith()),
								FinalLeg(
									"cancel the circle point",
									Simp(Fwd(quotient)),
									Refl())))
					}))
				holomorphicK := arg.Have(
					"multiplying H by i preserves holomorphy",
					"holomorphic_on(D, K)",
					Simp(Fwd(rotatedDef)),
					By(
						holomorphic,
						complex_derivative.HolomorphicOnConst.At(disc, arg.TermAs[Complex]("complex_i")),
						complex_derivative.HolomorphicOnMul.At(
							disc, arg.TermAs[Fun[Complex, Complex]]("λz:complex. complex_i"), H)))
				onCircle := arg.Have(
					"K is continuous at each point of the circle",
					"∀t:real. t ∈ ⟦-(pi / &2), &2 * pi⟧ ⇒ complex_continuous_at(K, γ(t))",
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						c.Assume()
						c.Show(
							"holomorphy on the disc implies continuity there",
							By(
								inDisc.At(t),
								holomorphicK,
								complex_derivative.HolomorphicOnContinuousAt.At(disc, K, c.TermAs[Complex]("γ(t)"))))
					}))
				ordered := arg.Have(
					"the continuity interval is ordered",
					"-(pi / &2) ≤ &2 * pi",
					ByArith(real_trigonometry.PiBounds))
				smooth := arg.Have(
					"the circle arc is piecewise smooth on that interval",
					"piecewise_smooth_path(γ, v, -(pi / &2), &2 * pi)",
					Simp(Fwd(circleDef), Fwd(velocityDef)),
					By(ordered, path_integral.CircleArcPiecewiseSmooth.At(zero, R, left, period)))
				pathContinuous := arg.Have(
					"the circle's real and imaginary parts are continuous",
					"real_continuous_on(⟦-(pi / &2), &2 * pi⟧, λt:real. re(γ(t))) ∧ "+
						"real_continuous_on(⟦-(pi / &2), &2 * pi⟧, λt:real. im(γ(t)))",
					By(arg.Unfolded(smooth, path_integral.PiecewiseSmoothPathDef)))
				integrandContinuous := arg.Have(
					"the integrand has continuous real and imaginary parts",
					"real_continuous_on(⟦-(pi / &2), &2 * pi⟧, λt:real. re(u(t))) ∧ "+
						"real_continuous_on(⟦-(pi / &2), &2 * pi⟧, λt:real. im(u(t)))",
					Simp(Fwd(cancel)),
					By(pathContinuous, onCircle, path_integral.ContinuousAlongPath.At(K, γ, I)))
				expPeriodic := arg.Have(
					"the unit-circle exponential has period two π",
					"∀t:real. exp(complex_i * &(t + &2 * pi)) = exp(complex_i * &t)",
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						c.Show(
							"both parts agree by the sine and cosine periodicity laws",
							ByArith(
								complex_exp.EulerOfReal.At(c.TermAs[Real]("t + &2 * pi")),
								complex_exp.EulerOfReal.At(t),
								real_trigonometry.CosPeriodic.At(t),
								real_trigonometry.SinPeriodic.At(t)))
					}))
				periodic := arg.Have(
					"the composed integrand inherits the circle's period",
					"∀t:real. u(t + &2 * pi) = u(t)",
					StripQuant(),
					Simp(Fwd(cancel), Fwd(circleDef), Fwd(path_integral.CirclePathDef), Fwd(expPeriodic)),
					Refl())

				centreInside := arg.Have(
					"the centre lies inside the small positive circle",
					"|complex_of_real(&0) - complex_of_real(&0)| < R",
					Simp(Fwd(subtractZero), Fwd(complex_abs.AbsOfReal)),
					ByArith(positive))
				cauchy := arg.Have(
					"Cauchy's formula on the standard full circle",
					"«arcInt»(λz:complex. H(z) / (z - complex_of_real(&0)), R, &0, &2 * pi) = "+
						"&(&2 * pi) * complex_i * H(complex_of_real(&0))",
					By(
						holomorphic,
						discDef,
						smaller,
						centreInside,
						cauchy_integral.CauchyIntegralFormula.At(H, zero, zero, ρ, R)))
				standard := arg.Have(
					"read off the integral of u on the standard interval",
					"complex_integral(u, &0, &2 * pi) = &(&2 * pi) * complex_i * H(complex_of_real(&0))",
					Simp(Fwd(integrandDef), Fwd(quotientDef), Fwd(circleDef), Fwd(velocityDef)),
					By(arg.Simplified(cauchy, Fwd(path_integral.PathIntegralDef), Fwd(subtractZero))))
				split := arg.Have(
					"periodicity moves the full integral to the two required half-circles",
					"complex_integral(u, -(pi / &2), pi / &2) + complex_integral(u, pi / &2, &3 * pi / &2) = "+
						"complex_integral(u, &0, &2 * pi)",
					By(periodic, integrandContinuous, At(periodicIntegral, u)))
				arg.Show(
					"read the two arc integrals in the same parameter",
					Simp(Fwd(path_integral.PathIntegralDef)),
					Simp(Rev(integrandDef)),
					By(split, standard))
			})
		}),
	Reading: "This is Cauchy's integral formula at the centre, written " +
		"over the two half-circles that Newman's estimate treats differently.",
})}
