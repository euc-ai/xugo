package lebesgue_riemann

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_inverse_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// GaussianIntegral — the integral of exp(−t²) over the line is √π. With
// «primitive»(t) the integral of the Gaussian over ⟦0, t⟧ and «angular»(t)
// the integral over ⟦0, 1⟧ of exp(−t²(1 + x²))/(1 + x²) — named for the
// substitution x = tan θ, under which dx/(1 + x²) = dθ and «angular»(0) =
// arctan 1 = π/4 — the square of the primitive plus «angular» has derivative
// 0 for t ≥ 0, so it is π/4 throughout, while 0 ≤ «angular»(t) ≤ exp(−t²)
// tends to 0. The derivative of «angular» comes from a quadratic remainder
// bound on the kernel exp(−a·t²)/a for 1 ≤ a ≤ 2: «scale»(t) = 4|t| + 2
// bounds a·|2t + h| when |h| < 1, so below «radius»(t) = 1/«scale»(t) the
// exponent moves by at most 1, and the remainder is at most «coefficient»(t)
// = 1 + «scale»(t)² times h². The windows ⟦−(n + 2), n + 2⟧ start where
// 1 + (n + 2)² exceeds 4(n + 1), so that 4·exp(−(n + 2)²) < 1/(n + 1); there
// the angular denominator «shape» spells 1 + R² ≤ exp(R²) at the radius R.
var GaussianIntegral = gaussianIntegralThm{family.Add(registry.ProofEntry{
	Name:    "GaussianIntegral",
	Key:     "prop_2666bd313092bc33",
	Reading: "The integrability conjunct is a claim, lebesgue_integral being total.",
	Build: family.Sections(Statement{
		Conclusion: "lebesgue_integrable(λt:real. real_exp(-real_pow(t, 2))) ∧ " +
			"lebesgue_integral(λt:real. real_exp(-real_pow(t, 2))) = real_sqrt(pi)",
		Abbrev: Abbrev{
			{Name: "gaussian", Text: "λx:real. real_exp(-real_pow(x, 2))"},
			{Name: "primitive", Text: "λt:real. real_integral(«gaussian», &0, t)"},
			{Name: "shape", Text: "λx:real. &1 + real_pow(x, 2)"},
			{Name: "exponent", Text: "λa:real. λt:real. -(real_pow(t, 2) * a)"},
			{Name: "shift", Text: "λa:real. λt:real. λh:real. -(a * h * (&2 * t + h))"},
			{Name: "kernel", Text: "λa:real. λt:real. real_exp(«exponent»(a, t)) * real_inv(a)"},
			{Name: "kernelSlope", Text: "λa:real. λt:real. -(&2 * t) * real_exp(«exponent»(a, t))"},
			{Name: "integrand", Text: "λt:real. λx:real. «kernel»(«shape»(x), t)"},
			{Name: "slopeIntegrand", Text: "λt:real. λx:real. «kernelSlope»(«shape»(x), t)"},
			{Name: "angular", Text: "λt:real. real_integral(«integrand»(t), &0, &1)"},
			{Name: "angularSlope", Text: "λt:real. real_integral(«slopeIntegrand»(t), &0, &1)"},
			{Name: "scale", Text: "λt:real. &4 * |t| + &2"},
			{Name: "radius", Text: "λt:real. &1 / «scale»(t)"},
			{Name: "coefficient", Text: "λt:real. &1 + real_pow(«scale»(t), 2)"},
			{Name: "exponentialRemainder", Text: "λu:real. real_exp(u) - &1 - u"},
			{Name: "kernelRemainder", Text: "λa:real. λt:real. λh:real. " +
				"    «kernel»(a, t + h) - «kernel»(a, t) - «kernelSlope»(a, t) * h"},
			{Name: "symmetricValue", Text: "λt:real. &2 * «primitive»(t)"},
			{Name: "windowRadius", Text: "λn:num. &n + &2"},
			{Name: "windowValues", Text: "λn:num. «symmetricValue»(«windowRadius»(n))"},
			{Name: "windowLower", Text: "λn:num. -«windowRadius»(n)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			kernelRemainderIdentity := ctx.Lemma(Statement{
				Binders: "∀a t h:real.",
				Hypotheses: []string{
					"&0 < a",
				},
				Conclusion: "«kernelRemainder»(a, t, h) = " +
					"exp(«exponent»(a, t)) * (real_inv(a) * «exponentialRemainder»(«shift»(a, t, h)) - h ^ 2)",
			},
				func(d *Argument, a, t, h *Expr[Real], positive Fact) {
					shiftedExponent := d.Have(
						"shifted exponent",
						"«exponent»(a, t + h) = «exponent»(a, t) + «shift»(a, t, h)",
						ByArith(),
					)
					inverseProduct := d.Have(
						"inverse product",
						"real_inv(a) * a = &1",
						ByArith(positive, At(field.MulLeftInverse.Read(real_field.Field), a)),
					)
					exponentialProduct := d.Have(
						"exponential product",
						"exp(«exponent»(a, t + h)) = exp(«exponent»(a, t)) * exp(«shift»(a, t, h))",
						By(
							shiftedExponent,
							At(
								real_exp_log.ExpAdd, d.TermAs[Real]("«exponent»(a, t)"), d.TermAs[Real]("«shift»(a, t, h)"))),
					)
					linearShift := d.Have(
						"linear shift",
						"real_inv(a) * «shift»(a, t, h) = -(h * (&2 * t + h))",
						ByArith(Scaled(d.TermAs[Real]("-(h * (&2 * t + h))"), inverseProduct)),
					)
					d.Show(
						"assemble the quadratic remainder",
						ByArith(
							Scaled(
								d.TermAs[Real]("exp(«exponent»(a, t))"),
								linearShift),
							Scaled(d.TermAs[Real]("real_inv(a)"), exponentialProduct)),
					)
				})

			kernelRemainderBound := ctx.Lemma(Statement{
				Binders: "∀a t h:real.",
				Hypotheses: []string{
					"&1 ≤ a",
					"a ≤ &2",
					"|h| < «radius»(t)",
				},
				Conclusion: "|«kernelRemainder»(a, t, h)| ≤ «coefficient»(t) * h ^ 2",
			},
				func(d *Argument, a, t, h *Expr[Real], bounds Fact) {
					scaleLower := d.Have(
						"scale lower",
						"&2 ≤ «scale»(t)",
						ByArith(At(real_sgn_abs.AbsNonneg, t)),
					)
					scaledIncrement := d.Have(
						"scaled increment",
						"|h| * «scale»(t) < &1",
						ByArith(
							bounds,
							scaleLower,
							At(
								real_order_field.LessThanDivMulLeft,
								d.TermAs[Real]("|h|"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("«scale»(t)"))),
					)
					smallIncrement := d.Have(
						"small increment",
						"|h| < &1",
						ByArith(
							scaleLower,
							scaledIncrement,
							At(real_sgn_abs.AbsNonneg, h),
							At(
								real_order_ring.LessEqMulLeft,
								d.TermAs[Real]("|h|"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("«scale»(t)"))),
					)
					doubledSize := d.Have(
						"doubled size",
						"|&2 * t| = &2 * |t|",
						ByArith(
							At(real_sgn_abs.AbsMul, d.TermAs[Real]("&2"), t),
							At(real_sgn_abs.AbsFixedIffNonneg, d.TermAs[Real]("&2"))),
					)
					linearFactorBound := d.Have(
						"linear factor bound",
						"|&2 * t + h| ≤ &2 * |t| + &1",
						ByArith(doubledSize, smallIncrement, At(real_sgn_abs.AbsTriangle, d.TermAs[Real]("&2 * t"), h)),
					)
					positiveShape := d.Have(
						"positive shape",
						"|a| = a",
						ByArith(bounds, At(real_sgn_abs.AbsFixedIffNonneg, a)),
					)
					shiftSize := d.Have(
						"shift size",
						"|«shift»(a, t, h)| = a * |h| * |&2 * t + h|",
						By(
							positiveShape,
							At(real_sgn_abs.AbsEven, d.TermAs[Real]("a * h * (&2 * t + h)")),
							At(real_sgn_abs.AbsMul, d.TermAs[Real]("a * h"), d.TermAs[Real]("&2 * t + h")),
							At(real_sgn_abs.AbsMul, a, h)),
					)
					shapeFactorBound := d.Have(
						"shape factor bound",
						"a * |&2 * t + h| ≤ «scale»(t)",
						ByArith(
							bounds,
							linearFactorBound,
							At(real_sgn_abs.AbsNonneg, d.TermAs[Real]("&2 * t + h")),
							At(
								real_order_ring.LessEqMul2,
								a,
								d.TermAs[Real]("&2"),
								d.TermAs[Real]("|&2 * t + h|"),
								d.TermAs[Real]("&2 * |t| + &1"))),
					)
					shiftBound := d.Have(
						"shift bound",
						"|«shift»(a, t, h)| ≤ «scale»(t) * |h|",
						ByArith(
							shiftSize,
							shapeFactorBound,
							At(real_sgn_abs.AbsNonneg, h),
							At(
								real_order_ring.LessEqMulRight,
								d.TermAs[Real]("a * |&2 * t + h|"),
								d.TermAs[Real]("«scale»(t)"),
								d.TermAs[Real]("|h|"))),
					)
					smallShift := d.Have(
						"the exponent's increment is at most 1",
						"|«shift»(a, t, h)| ≤ &1",
						ByArith(shiftBound, scaledIncrement))
					exponentialError := d.Have(
						"so the exponential's remainder is at most the increment squared",
						"|«exponentialRemainder»(«shift»(a, t, h))| ≤ «shift»(a, t, h) ^ 2",
						By(smallShift, At(real_exp_log.ExpQuadraticBound, d.TermAs[Real]("«shift»(a, t, h)"))))
					scaledMagnitude := d.Have(
						"scaled magnitude",
						"|«scale»(t) * h| = «scale»(t) * |h|",
						ByArith(
							scaleLower,
							At(real_sgn_abs.AbsMul, d.TermAs[Real]("«scale»(t)"), h),
							At(real_sgn_abs.AbsFixedIffNonneg, d.TermAs[Real]("«scale»(t)"))),
					)
					squaredShiftBound := d.Have(
						"squared shift bound",
						"«shift»(a, t, h) ^ 2 ≤ («scale»(t) * h) ^ 2",
						ByArith(
							shiftBound,
							scaledMagnitude,
							At(
								real_pow.AbsLessEqIffPowTwoLessEq,
								d.TermAs[Real]("«shift»(a, t, h)"),
								d.TermAs[Real]("«scale»(t) * h"))),
					)
					inverseNonnegative := d.Have(
						"inverse nonnegative",
						"&0 ≤ real_inv(a)",
						ByArith(bounds, At(real_order_field.InvNonneg, a)),
					)
					inverseOne := d.Have(
						"the inverse of one is one",
						"real_inv(&1) = &1",
						ByArith(At(field.MulLeftInverse.Read(real_field.Field), d.TermAs[Real]("&1"))))
					inverseUpper := d.Have(
						"inversion reverses the order above one",
						"real_inv(a) ≤ &1",
						ByArith(bounds, inverseOne, At(real_order_field.InvAntitoneWeak, d.TermAs[Real]("&1"), a)))
					exponentNonpositive := d.Have(
						"exponent nonpositive",
						"«exponent»(a, t) ≤ &0",
						ByArith(bounds, At(real_pow.PowTwoNonneg, t)),
					)
					exponentialNonnegative := d.Have(
						"exponential nonnegative",
						"&0 ≤ exp(«exponent»(a, t))",
						ByArith(At(real_exp_log.ExpPositive, d.TermAs[Real]("«exponent»(a, t)"))),
					)
					exponentialUpper := d.Have(
						"exponential upper",
						"exp(«exponent»(a, t)) ≤ &1",
						ByArith(
							exponentNonpositive,
							At(real_exp_log.ExpLessIff, d.TermAs[Real]("&0"), d.TermAs[Real]("«exponent»(a, t)")),
							At(
								real_order_ring.NotLessThan, d.TermAs[Real]("exp(&0)"), d.TermAs[Real]("exp(«exponent»(a, t))")),
							real_exp_log.ExpZero),
					)
					scaledErrorSize := d.Have(
						"scaled error size",
						"|real_inv(a) * «exponentialRemainder»(«shift»(a, t, h))| = "+
							"real_inv(a) * |«exponentialRemainder»(«shift»(a, t, h))|",
						By(
							inverseNonnegative,
							At(
								real_sgn_abs.AbsMul,
								d.TermAs[Real]("real_inv(a)"),
								d.TermAs[Real]("«exponentialRemainder»(«shift»(a, t, h))")),
							At(real_sgn_abs.AbsFixedIffNonneg, d.TermAs[Real]("real_inv(a)"))),
					)
					inverseShrinksError := d.Have(
						"inverse shrinks error",
						"real_inv(a) * |«exponentialRemainder»(«shift»(a, t, h))| ≤ "+
							"|«exponentialRemainder»(«shift»(a, t, h))|",
						ByArith(
							inverseUpper,
							At(real_sgn_abs.AbsNonneg, d.TermAs[Real]("«exponentialRemainder»(«shift»(a, t, h))")),
							At(
								real_order_ring.LessEqMulRight,
								d.TermAs[Real]("real_inv(a)"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("|«exponentialRemainder»(«shift»(a, t, h))|"))),
					)
					innerErrorBound := d.Have(
						"inner error bound",
						"|real_inv(a) * «exponentialRemainder»(«shift»(a, t, h)) - h ^ 2| ≤ "+
							"|«exponentialRemainder»(«shift»(a, t, h))| + h ^ 2",
						ByArith(
							scaledErrorSize,
							inverseShrinksError,
							At(
								real_sgn_abs.AbsTriangle,
								d.TermAs[Real]("real_inv(a) * «exponentialRemainder»(«shift»(a, t, h))"),
								d.TermAs[Real]("-h ^ 2")),
							At(real_sgn_abs.AbsEven, d.TermAs[Real]("h ^ 2")),
							At(real_sgn_abs.AbsFixedIffNonneg, d.TermAs[Real]("h ^ 2")),
							At(real_pow.PowTwoNonneg, h),
							At(
								real_ring.RealSubDef,
								d.TermAs[Real]("real_inv(a) * «exponentialRemainder»(«shift»(a, t, h))"),
								d.TermAs[Real]("h ^ 2"))),
					)
					exponentialShrinksError := d.Have(
						"exponential shrinks error",
						"|exp(«exponent»(a, t)) * (real_inv(a) * «exponentialRemainder»(«shift»(a, t, h)) - h ^ 2)| ≤ "+
							"|real_inv(a) * «exponentialRemainder»(«shift»(a, t, h)) - h ^ 2|",
						ByArith(
							exponentialNonnegative,
							exponentialUpper,
							At(
								real_sgn_abs.AbsMul,
								d.TermAs[Real]("exp(«exponent»(a, t))"),
								d.TermAs[Real]("real_inv(a) * «exponentialRemainder»(«shift»(a, t, h)) - h ^ 2")),
							At(real_sgn_abs.AbsFixedIffNonneg, d.TermAs[Real]("exp(«exponent»(a, t))")),
							At(
								real_sgn_abs.AbsNonneg,
								d.TermAs[Real]("real_inv(a) * «exponentialRemainder»(«shift»(a, t, h)) - h ^ 2")),
							At(
								real_order_ring.LessEqMulRight,
								d.TermAs[Real]("exp(«exponent»(a, t))"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("|real_inv(a) * «exponentialRemainder»(«shift»(a, t, h)) - h ^ 2|"))),
					)
					remainderIdentity := d.Have(
						"remainder identity",
						"«kernelRemainder»(a, t, h) = "+
							"exp(«exponent»(a, t)) * (real_inv(a) * «exponentialRemainder»(«shift»(a, t, h)) - h ^ 2)",
						ByArith(bounds, At(kernelRemainderIdentity, a, t, h)),
					)
					remainderByInnerError := d.Have(
						"remainder by inner error",
						"|«kernelRemainder»(a, t, h)| ≤ |real_inv(a) * «exponentialRemainder»(«shift»(a, t, h)) - h ^ 2|",
						By(remainderIdentity, exponentialShrinksError),
					)
					errorSquare := d.Have(
						"the exponential's remainder is at most («scale»(t)·h)²",
						"|«exponentialRemainder»(«shift»(a, t, h))| ≤ («scale»(t) * h) ^ 2",
						By(
							exponentialError,
							squaredShiftBound,
							real_construction.LessEqTrans.At(
								d.TermAs[Real]("|«exponentialRemainder»(«shift»(a, t, h))|"),
								d.TermAs[Real]("«shift»(a, t, h) ^ 2"),
								d.TermAs[Real]("(«scale»(t) * h) ^ 2"))))
					quadraticPlusIncrement := d.Have(
						"so with h² it is at most «coefficient»(t)·h²",
						"|«exponentialRemainder»(«shift»(a, t, h))| + h ^ 2 ≤ «coefficient»(t) * h ^ 2",
						ByArith(Raw, errorSquare))
					d.Show(
						"chain the remainder bounds",
						ByArith(remainderByInnerError, innerErrorBound, quadraticPlusIncrement))
				})

			shapeBounds := ctx.Lemma(Statement{
				Binders: "∀x:real.",
				Hypotheses: []string{
					"&0 ≤ x",
					"x ≤ &1",
				},
				Conclusion: "&1 ≤ «shape»(x) ∧ «shape»(x) ≤ &2",
			},
				func(a *Argument, x *Expr[Real], unit Fact) {
					one := a.TermAs[Real]("&1")
					square := a.Have(
						"the square of a point of ⟦0, 1⟧ is at most 1",
						"x * x ≤ &1 * &1",
						ByArith(unit, real_order_ring.LessEqMul2.At(x, one, x, one)))
					a.Show(
						"so one plus the square lies between one and two",
						ByArith(square, real_pow.PowTwoNonneg.At(x)))
				})
			gaussianContinuity := ctx.Lemma("∀S:set(real). real_continuous_on(S, «gaussian»)",
				func(a *Argument, S *Expr[Set[Real]]) {
					form := a.Have(
						"the Gaussian is the exponential quadratic with centre 0, coefficient −1 and factor 1",
						"«gaussian» = (λx:real. &1 * exp(-&1 * ((x - &0) * (x - &0))))",
						Funext(),
						Simp(
							Fwd(real_pow.PowTwo),
							Fwd(real_ring.SubRightZero),
							Fwd(real_ring.MulLeftNeg),
							Fwd(real_construction.MulLeftId)),
						Basic())
					a.Show(
						"continuous on the line, the Gaussian is continuous on S",
						By(
							form,
							real_exp_log.ExponentialQuadraticContinuous.At(
								a.TermAs[Real]("&0"), a.TermAs[Real]("-&1"), a.TermAs[Real]("&1")),
							set_order.SubsetUniv.At(S),
							real_continuous.ContinuousOnSubset.At(
								a.TermAs[Fun[Real, Real]]("«gaussian»"), a.TermAs[Set[Real]]("𝕌"), S)))
				})

			angularIntegrability := ctx.Lemma("∀t:real. "+
				"    real_has_integral(λx:real. «integrand»(t, x), &0, &1, «angular»(t)) ∧ "+
				"    real_has_integral(λx:real. «slopeIntegrand»(t, x), &0, &1, «angularSlope»(t))",
				func(d *Argument, t *Expr[Real]) {
					squareDifferentiable := d.Have(
						"square differentiable",
						"∀x:real. x ∈ ⟦&0, &1⟧ ⇒ real_derivative_at(λx:real. x ^ 2, x, &2 * x ^ (2 - 1))",
						By(real_derivative.DerivativePow),
					)
					continuousSquare := d.Have(
						"continuous square",
						"real_continuous_on(⟦&0, &1⟧, λx:real. x ^ 2)",
						By(
							squareDifferentiable,
							At(
								real_derivative.DerivativeContinuousOn,
								d.TermAs[Fun[Real, Real]]("λx:real. x ^ 2"),
								d.TermAs[Fun[Real, Real]]("λx:real. &2 * x ^ (2 - 1)"),
								d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					continuousOne := d.Have(
						"continuous one",
						"real_continuous_on(⟦&0, &1⟧, λx:real. &1)",
						By(At(real_continuous.ContinuousOnConst, d.TermAs[Real]("&1"), d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					continuousShape := d.Have(
						"continuous shape",
						"real_continuous_on(⟦&0, &1⟧, «shape»)",
						By(
							continuousSquare,
							continuousOne,
							At(
								real_continuous.ContinuousOnAdd,
								d.TermAs[Fun[Real, Real]]("λx:real. &1"),
								d.TermAs[Fun[Real, Real]]("λx:real. x ^ 2"),
								d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					continuousParameterSquare := d.Have(
						"continuous parameter square",
						"real_continuous_on(⟦&0, &1⟧, λx:real. t ^ 2)",
						By(At(real_continuous.ContinuousOnConst, d.TermAs[Real]("t ^ 2"), d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					continuousScaledShape := d.Have(
						"continuous scaled shape",
						"real_continuous_on(⟦&0, &1⟧, λx:real. t ^ 2 * «shape»(x))",
						By(
							continuousParameterSquare,
							continuousShape,
							At(
								real_continuous.ContinuousOnMul,
								d.TermAs[Fun[Real, Real]]("λx:real. t ^ 2"),
								d.TermAs[Fun[Real, Real]]("«shape»"),
								d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					continuousExponent := d.Have(
						"continuous exponent",
						"real_continuous_on(⟦&0, &1⟧, λx:real. «exponent»(«shape»(x), t))",
						By(
							continuousScaledShape,
							At(
								real_continuous.ContinuousOnNeg,
								d.TermAs[Fun[Real, Real]]("λx:real. t ^ 2 * «shape»(x)"),
								d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					exponentInLine := d.Have(
						"exponent in line",
						"∀x:real. x ∈ ⟦&0, &1⟧ ⇒ «exponent»(«shape»(x), t) ∈ 𝕌",
						By(set_basic.InUniv.Inst[Real]()),
					)
					continuousComposition := d.Have(
						"continuous composition",
						"real_continuous_on(⟦&0, &1⟧, real_exp ∘ λx:real. «exponent»(«shape»(x), t))",
						By(
							exponentInLine,
							real_exp_log.ExpContinuous,
							continuousExponent,
							At(
								real_continuous.ContinuousOnCompose,
								d.TermAs[Fun[Real, Real]]("real_exp"),
								d.TermAs[Fun[Real, Real]]("λx:real. «exponent»(«shape»(x), t)"),
								d.TermAs[Set[Real]]("⟦&0, &1⟧"),
								d.TermAs[Set[Real]]("𝕌"))),
					)
					continuousExponentialFactor := d.Have(
						"continuous exponential factor",
						"real_continuous_on(⟦&0, &1⟧, λx:real. exp(«exponent»(«shape»(x), t)))",
						By(
							continuousComposition,
							functions.ComposeApply.At(
								d.TermAs[Fun[Real, Real]]("real_exp"),
								d.TermAs[Fun[Real, Real]]("λx:real. «exponent»(«shape»(x), t)"))),
					)
					inverseShapeDifferentiable := d.Have(
						"inverse shape differentiable",
						Statement{
							Binders: "∀x:real.",
							Hypotheses: []string{
								"x ∈ ⟦&0, &1⟧",
							},
							Conclusion: "real_derivative_at(λx:real. real_inv(«shape»(x)), " +
								"    x, " +
								"    -(&0 + &2 * x ^ (2 - 1)) / «shape»(x) ^ 2)",
						},
						Derive(func(e *Argument) {
							x := e.FixAs[Real]("x")
							e.Assume()
							shapeDerivative := e.Have(
								"shape derivative",
								"real_derivative_at(«shape», x, &0 + &2 * x ^ (2 - 1))",
								By(
									At(real_derivative.DerivativeConst, e.TermAs[Real]("&1"), x),
									At(real_derivative.DerivativePow, e.TermAs[Nat]("2"), x),
									At(
										real_derivative.DerivativeAdd,
										e.TermAs[Fun[Real, Real]]("λx:real. &1"),
										e.TermAs[Fun[Real, Real]]("λx:real. x ^ 2"),
										x,
										e.TermAs[Real]("&0"),
										e.TermAs[Real]("&2 * x ^ (2 - 1)"))),
							)
							shapeNonzero := e.Have(
								"shape nonzero",
								"«shape»(x) ≠ &0",
								ByArith(Raw, At(real_pow.PowTwoNonneg, x)),
							)
							e.Show(
								"differentiate the inverse shape",
								By(
									shapeDerivative,
									shapeNonzero,
									At(
										real_derivative.DerivativeInv,
										e.TermAs[Fun[Real, Real]]("«shape»"),
										x,
										e.TermAs[Real]("&0 + &2 * x ^ (2 - 1)"))),
							)
						}),
					)
					continuousInverseShape := d.Have(
						"continuous inverse shape",
						"real_continuous_on(⟦&0, &1⟧, λx:real. real_inv(«shape»(x)))",
						By(
							inverseShapeDifferentiable,
							At(
								real_derivative.DerivativeContinuousOn,
								d.TermAs[Fun[Real, Real]]("λx:real. real_inv(«shape»(x))"),
								d.TermAs[Fun[Real, Real]]("λx:real. -(&0 + &2 * x ^ (2 - 1)) / «shape»(x) ^ 2"),
								d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					continuousAngularIntegrand := d.Have(
						"continuous angular integrand",
						"real_continuous_on(⟦&0, &1⟧, λx:real. «integrand»(t, x))",
						By(
							continuousExponentialFactor,
							continuousInverseShape,
							At(
								real_continuous.ContinuousOnMul,
								d.TermAs[Fun[Real, Real]]("λx:real. exp(«exponent»(«shape»(x), t))"),
								d.TermAs[Fun[Real, Real]]("λx:real. real_inv(«shape»(x))"),
								d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					continuousSlopeFactor := d.Have(
						"continuous slope factor",
						"real_continuous_on(⟦&0, &1⟧, λx:real. -(&2 * t))",
						By(
							At(
								real_continuous.ContinuousOnConst, d.TermAs[Real]("-(&2 * t)"), d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					continuousSlopeIntegrand := d.Have(
						"continuous slope integrand",
						"real_continuous_on(⟦&0, &1⟧, λx:real. «slopeIntegrand»(t, x))",
						By(
							continuousExponentialFactor,
							continuousSlopeFactor,
							At(
								real_continuous.ContinuousOnMul,
								d.TermAs[Fun[Real, Real]]("λx:real. -(&2 * t)"),
								d.TermAs[Fun[Real, Real]]("λx:real. exp(«exponent»(«shape»(x), t))"),
								d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
					)
					unitIntervalOrdered := d.Have(
						"unit interval ordered",
						"&0 ≤ &1",
						ByArith(Raw),
					)
					d.Show(
						"the kernel and the slope, continuous on ⟦0, 1⟧, have their integrals there",
						By(
							unitIntervalOrdered,
							continuousAngularIntegrand,
							continuousSlopeIntegrand,
							real_integral.ContinuousHasIntegral.At(
								d.TermAs[Fun[Real, Real]]("λx:real. «integrand»(t, x)"),
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&1")),
							real_integral.ContinuousHasIntegral.At(
								d.TermAs[Fun[Real, Real]]("λx:real. «slopeIntegrand»(t, x)"),
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&1"))),
					)
				})

			angularDerivative := ctx.Lemma("∀t:real. real_derivative_at(«angular», t, «angularSlope»(t))",
				func(d *Argument, t *Expr[Real]) {
					positiveScale := d.Have(
						"positive scale",
						"&0 < «scale»(t)",
						ByArith(Raw, At(real_sgn_abs.AbsNonneg, t)),
					)
					positiveRadius := d.Have(
						"positive radius",
						"&0 < «radius»(t)",
						ByArith(
							positiveScale,
							At(real_order_field.DivPos, d.TermAs[Real]("&1"), d.TermAs[Real]("«scale»(t)"))),
					)
					remainder := d.Have(
						"below «radius»(t), at every point of ⟦0, 1⟧ the integrand's "+
							"quadratic remainder is at most «coefficient»(t)·h²",
						Statement{
							Binders: "∀h x:real.",
							Hypotheses: []string{
								"|h| < «radius»(t)",
								"&0 ≤ x",
								"x ≤ &1",
							},
							Conclusion: "|«integrand»(t + h, x) - «integrand»(t, x) - «slopeIntegrand»(t, x) * h| ≤ " +
								"«coefficient»(t) * h ^ 2",
						},
						Derive(func(e *Argument) {
							h := e.FixAs[Real]("h")
							x := e.FixAs[Real]("x")
							small := e.Assume()
							e.Show(
								"it is the kernel's remainder at a = «shape»(x), which lies in ⟦1, 2⟧",
								By(small, At(shapeBounds, x), At(kernelRemainderBound, e.TermAs[Real]("«shape»(x)"), t, h)))
						}))
					d.Show(
						"so the angular integral is differentiated under the integral sign",
						By(
							positiveRadius,
							remainder,
							angularIntegrability,
							real_integral.DerivativeUnderIntegral.At(
								d.TermAs[Op[Real]]("«integrand»"),
								d.TermAs[Op[Real]]("«slopeIntegrand»"),
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&1"),
								t,
								d.TermAs[Real]("«coefficient»(t)"),
								d.TermAs[Real]("«radius»(t)"))))
				})

			angularSlopeValue := ctx.Lemma(Statement{
				Binders: "∀t:real.",
				Hypotheses: []string{
					"&0 ≤ t",
				},
				Conclusion: "«angularSlope»(t) = -(&2 * «gaussian»(t) * «primitive»(t))",
			},
				func(d *Argument, t *Expr[Real], nonnegative Fact) {
					negativeFactor := d.Have(
						"negative factor",
						"-(&2 * «gaussian»(t)) < &0",
						ByArith(Raw, At(real_exp_log.ExpPositive, d.TermAs[Real]("-t ^ 2"))),
					)
					inverseFactorProduct := d.Have(
						"inverse factor product",
						"real_inv(-(&2 * «gaussian»(t))) * -(&2 * «gaussian»(t)) = &1",
						ByArith(
							negativeFactor,
							At(field.MulLeftInverse.Read(real_field.Field), d.TermAs[Real]("-(&2 * «gaussian»(t))"))),
					)
					rescaledSlopeIntegral := d.Have(
						"rescaled slope integral",
						"real_has_integral(λx:real. real_inv(-(&2 * «gaussian»(t))) * «slopeIntegrand»(t, x), "+
							"    &0, "+
							"    &1, "+
							"    real_inv(-(&2 * «gaussian»(t))) * «angularSlope»(t))",
						By(
							At(angularIntegrability, t),
							At(
								real_integral.HasIntegralScale,
								d.TermAs[Fun[Real, Real]]("λx:real. «slopeIntegrand»(t, x)"),
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("«angularSlope»(t)"),
								d.TermAs[Real]("real_inv(-(&2 * «gaussian»(t)))"))),
					)
					affineAgreement := d.Have(
						"affine agreement",
						Statement{
							Binders: "∀x:real.",
							Hypotheses: []string{
								"&0 ≤ x",
								"x ≤ &1",
							},
							Conclusion: "real_inv(-(&2 * «gaussian»(t))) * «slopeIntegrand»(t, x) = «gaussian»(&0 + t * x) * t",
						},
						Derive(func(e *Argument) {
							e.FixAs[Real]("x")
							e.Assume()
							splitExponent := e.Have(
								"split exponent",
								"«exponent»(«shape»(x), t) = -t ^ 2 + -(&0 + t * x) ^ 2",
								ByArith(Raw),
							)
							splitExponential := e.Have(
								"split exponential",
								"exp(«exponent»(«shape»(x), t)) = «gaussian»(t) * «gaussian»(&0 + t * x)",
								By(
									splitExponent,
									At(real_exp_log.ExpAdd, e.TermAs[Real]("-t ^ 2"), e.TermAs[Real]("-(&0 + t * x) ^ 2"))),
							)
							factorizedSlope := e.Have(
								"factorized slope",
								"«slopeIntegrand»(t, x) = -(&2 * «gaussian»(t)) * «gaussian»(&0 + t * x) * t",
								splitExponential.Rw(),
								ByArith(Raw),
							)
							e.Show(
								"cancel the constant factor against its inverse",
								factorizedSlope.Rw(),
								Derive(func(g *Argument) {
									restoredIntegrandGrouping := g.Have(
										"restored integrand grouping",
										"real_inv(-(&2 * «gaussian»(t))) * (-(&2 * «gaussian»(t)) * «gaussian»(&0 + t * x) * t) = "+
											"real_inv(-(&2 * «gaussian»(t))) * -(&2 * «gaussian»(t)) * «gaussian»(&0 + t * x) * t",
										ByArith(Raw),
									)
									affineUnitProduct := g.Have(
										"affine unit product",
										"&1 * «gaussian»(&0 + t * x) * t = «gaussian»(&0 + t * x) * t",
										ByArith(Raw),
									)
									g.Show(
										"the scaled slope is the affine integrand",
										By(inverseFactorProduct, restoredIntegrandGrouping, affineUnitProduct),
									)
								}),
							)
						}),
					)
					affineHasIntegral := d.Have(
						"affine has integral",
						"real_has_integral(λx:real. «gaussian»(&0 + t * x) * t, "+
							"    &0, "+
							"    &1, "+
							"    real_inv(-(&2 * «gaussian»(t))) * «angularSlope»(t))",
						By(
							rescaledSlopeIntegral,
							affineAgreement,
							At(
								real_integral.HasIntegralCongruence,
								d.TermAs[Fun[Real, Real]](
									"λx:real. real_inv(-(&2 * «gaussian»(t))) * «slopeIntegrand»(t, x)"),
								d.TermAs[Fun[Real, Real]]("λx:real. «gaussian»(&0 + t * x) * t"),
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("real_inv(-(&2 * «gaussian»(t))) * «angularSlope»(t)"))),
					)
					gaussianOnPositiveInterval := d.Have(
						"gaussian on positive interval",
						"real_continuous_on(⟦&0, t⟧, «gaussian»)",
						By(At(gaussianContinuity, d.TermAs[Set[Real]]("⟦&0, t⟧"))),
					)
					affineEndpoint := d.Have(
						"affine endpoint",
						"&0 + t = t",
						ByArith(Raw),
					)
					endpointBounds := d.Have(
						"endpoint bounds",
						"&0 ≤ &0 ∧ &0 ≤ t ∧ &0 ≤ &0 + t ∧ &0 + t ≤ t",
						ByArith(Raw, nonnegative),
					)
					affineSubstitution := d.Have(
						"affine substitution",
						"real_integral(λx:real. «gaussian»(&0 + t * x) * t, &0, &1) = «primitive»(t)",
						By(
							gaussianOnPositiveInterval,
							endpointBounds,
							affineEndpoint,
							At(
								real_integral.IntegralAffineSubstitution,
								d.TermAs[Fun[Real, Real]]("«gaussian»"),
								d.TermAs[Real]("&0"),
								t,
								t,
								d.TermAs[Real]("&0"))),
					)
					affineIntegralValue := d.Have(
						"affine integral value",
						"real_integral(λx:real. «gaussian»(&0 + t * x) * t, &0, &1) = "+
							"real_inv(-(&2 * «gaussian»(t))) * «angularSlope»(t)",
						By(
							affineHasIntegral,
							At(
								real_integral.HasIntegralValue,
								d.TermAs[Fun[Real, Real]]("λx:real. «gaussian»(&0 + t * x) * t"),
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("real_inv(-(&2 * «gaussian»(t))) * «angularSlope»(t)"))),
					)
					primitiveAsRescaledSlope := d.Have(
						"primitive as rescaled slope",
						"«primitive»(t) = real_inv(-(&2 * «gaussian»(t))) * «angularSlope»(t)",
						By(affineSubstitution, affineIntegralValue),
					)
					restoreSlopeGrouping := d.Have(
						"restore slope grouping",
						"-(&2 * «gaussian»(t)) * (real_inv(-(&2 * «gaussian»(t))) * «angularSlope»(t)) = "+
							"real_inv(-(&2 * «gaussian»(t))) * -(&2 * «gaussian»(t)) * «angularSlope»(t)",
						ByArith(Raw),
					)
					slopeUnitProduct := d.Have(
						"slope unit product",
						"&1 * «angularSlope»(t) = «angularSlope»(t)",
						ByArith(Raw),
					)
					restoredSlope := d.Have(
						"restored slope",
						"«angularSlope»(t) = -(&2 * «gaussian»(t)) * «primitive»(t)",
						By(primitiveAsRescaledSlope, restoreSlopeGrouping, inverseFactorProduct, slopeUnitProduct),
					)
					d.Show(
						"recover the slope integral after the affine substitution",
						ByArith(Raw, restoredSlope),
					)
				})

			angularBounds := ctx.Lemma("∀t:real. &0 ≤ «angular»(t) ∧ «angular»(t) ≤ «gaussian»(t)",
				func(d *Argument, t *Expr[Real]) {
					angularHasIntegral := d.Have(
						"angular has integral",
						"real_has_integral(λx:real. «integrand»(t, x), &0, &1, «angular»(t))",
						By(At(angularIntegrability, t)),
					)
					orderedUnitInterval := d.Have(
						"ordered unit interval",
						"&0 ≤ &1",
						ByArith(Raw),
					)
					zeroHasIntegral := d.Have(
						"zero has integral",
						"real_has_integral(λx:real. &0, &0, &1, &0 * (&1 - &0))",
						By(
							orderedUnitInterval,
							At(
								real_integral.HasIntegralConst, d.TermAs[Real]("&0"), d.TermAs[Real]("&1"), d.TermAs[Real]("&0"))),
					)
					constantGaussianHasIntegral := d.Have(
						"constant gaussian has integral",
						"real_has_integral(λx:real. «gaussian»(t), &0, &1, «gaussian»(t) * (&1 - &0))",
						By(
							orderedUnitInterval,
							At(
								real_integral.HasIntegralConst,
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("«gaussian»(t)"))),
					)
					pointwiseBounds := d.Have(
						"pointwise bounds",
						"∀x:real. &0 ≤ x ∧ x ≤ &1 ⇒ &0 ≤ «integrand»(t, x) ∧ «integrand»(t, x) ≤ «gaussian»(t)",
						Derive(func(e *Argument) {
							x := e.FixAs[Real]("x")
							unit := e.Assume()
							shapeLower := e.Have(
								"shape lower",
								"&1 ≤ «shape»(x)",
								By(unit, At(shapeBounds, x)),
							)
							inverseShapeNonnegative := e.Have(
								"inverse shape nonnegative",
								"&0 ≤ real_inv(«shape»(x))",
								ByArith(shapeLower, At(real_order_field.InvNonneg, e.TermAs[Real]("«shape»(x)"))),
							)
							inverseOne := e.Have(
								"inverse one",
								"real_inv(&1) = &1",
								ByArith(At(field.MulLeftInverse.Read(real_field.Field), e.TermAs[Real]("&1"))),
							)
							inverseShapeUpper := e.Have(
								"inverse shape upper",
								"real_inv(«shape»(x)) ≤ &1",
								ByArith(
									shapeLower,
									inverseOne,
									At(real_order_field.InvAntitoneWeak, e.TermAs[Real]("&1"), e.TermAs[Real]("«shape»(x)"))),
							)
							exponentComparison := e.Have(
								"exponent comparison",
								"«exponent»(«shape»(x), t) ≤ -t ^ 2",
								ByArith(
									shapeLower,
									At(real_pow.PowTwoNonneg, t),
									At(
										real_order_ring.LessEqMulLeft,
										e.TermAs[Real]("t ^ 2"),
										e.TermAs[Real]("&1"),
										e.TermAs[Real]("«shape»(x)"))),
							)
							positiveExponential := e.Have(
								"positive exponential",
								"&0 ≤ exp(«exponent»(«shape»(x), t))",
								ByArith(Raw, At(real_exp_log.ExpPositive, e.TermAs[Real]("«exponent»(«shape»(x), t)"))),
							)
							exponentialComparison := e.Have(
								"exponential comparison",
								"exp(«exponent»(«shape»(x), t)) ≤ «gaussian»(t)",
								By(
									exponentComparison,
									At(
										real_exp_log.ExpLessIff, e.TermAs[Real]("-t ^ 2"), e.TermAs[Real]("«exponent»(«shape»(x), t)")),
									At(
										real_order_ring.NotLessThan,
										e.TermAs[Real]("«gaussian»(t)"),
										e.TermAs[Real]("exp(«exponent»(«shape»(x), t))")),
									At(
										real_order_ring.NotLessThan,
										e.TermAs[Real]("-t ^ 2"),
										e.TermAs[Real]("«exponent»(«shape»(x), t)"))),
							)
							kernelBelowExponential := e.Have(
								"kernel below exponential",
								"«integrand»(t, x) ≤ exp(«exponent»(«shape»(x), t))",
								ByArith(
									positiveExponential,
									inverseShapeUpper,
									At(
										real_order_ring.LessEqMulLeft,
										e.TermAs[Real]("exp(«exponent»(«shape»(x), t))"),
										e.TermAs[Real]("real_inv(«shape»(x))"),
										e.TermAs[Real]("&1"))),
							)
							kernelUpper := e.Have(
								"kernel upper",
								"«integrand»(t, x) ≤ «gaussian»(t)",
								ByArith(kernelBelowExponential, exponentialComparison),
							)
							e.Show(
								"bound the kernel between zero and the Gaussian",
								ByArith(positiveExponential, inverseShapeNonnegative, kernelUpper),
							)
						}),
					)
					pointwiseNonnegative := d.Have(
						"pointwise nonnegative",
						"∀x:real. &0 ≤ x ∧ x ≤ &1 ⇒ &0 ≤ «integrand»(t, x)",
						By(pointwiseBounds),
					)
					pointwiseUpper := d.Have(
						"pointwise upper",
						"∀x:real. &0 ≤ x ∧ x ≤ &1 ⇒ «integrand»(t, x) ≤ «gaussian»(t)",
						By(pointwiseBounds),
					)
					integratedLowerBound := d.Have(
						"integrated lower bound",
						"&0 * (&1 - &0) ≤ «angular»(t)",
						By(
							pointwiseNonnegative,
							zeroHasIntegral,
							angularHasIntegral,
							At(
								real_integral.HasIntegralLessEq,
								d.TermAs[Fun[Real, Real]]("λx:real. &0"),
								d.TermAs[Fun[Real, Real]]("λx:real. «integrand»(t, x)"),
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("&0 * (&1 - &0)"),
								d.TermAs[Real]("«angular»(t)"))),
					)
					integratedUpperBound := d.Have(
						"integrated upper bound",
						"«angular»(t) ≤ «gaussian»(t) * (&1 - &0)",
						By(
							pointwiseUpper,
							angularHasIntegral,
							constantGaussianHasIntegral,
							At(
								real_integral.HasIntegralLessEq,
								d.TermAs[Fun[Real, Real]]("λx:real. «integrand»(t, x)"),
								d.TermAs[Fun[Real, Real]]("λx:real. «gaussian»(t)"),
								d.TermAs[Real]("&0"),
								d.TermAs[Real]("&1"),
								d.TermAs[Real]("«angular»(t)"),
								d.TermAs[Real]("«gaussian»(t) * (&1 - &0)"))),
					)
					d.Show(
						"integrate the two bounds",
						ByArith(Raw, integratedLowerBound, integratedUpperBound),
					)
				})

			gaussianRiemannIntegral := ctx.Lemma(Statement{
				Binders: "∀a b:real.",
				Hypotheses: []string{
					"a ≤ b",
				},
				Conclusion: "real_has_integral(«gaussian», a, b, real_integral(«gaussian», a, b))",
			},
				func(arg *Argument, a, b *Expr[Real], ordered Fact) {
					arg.Show(
						"the Gaussian, continuous on ⟦a, b⟧, has its integral there",
						By(
							ordered,
							At(gaussianContinuity, arg.TermAs[Set[Real]]("⟦a, b⟧")),
							real_integral.ContinuousHasIntegral.At(arg.TermAs[Fun[Real, Real]]("«gaussian»"), a, b)))
				})

			gaussianRiemannNonnegative := ctx.Lemma(Statement{
				Binders: "∀a b:real.",
				Hypotheses: []string{
					"a ≤ b",
				},
				Conclusion: "&0 ≤ real_integral(«gaussian», a, b)",
			},
				func(arg *Argument, a, b *Expr[Real], ordered Fact) {
					positive := arg.Have(
						"the Gaussian is an exponential, so positive",
						"∀x:real. &0 ≤ «gaussian»(x)",
						Derive(func(d *Argument) {
							d.FixAs[Real]()
							d.Show(
								"exp is positive",
								ByArith(real_exp_log.ExpPositive.At(d.TermAs[Real]("-x ^ 2"))))
						}))
					arg.Show(
						"the Gaussian has its integral over ⟦a, b⟧, and a nonnegative function a nonnegative one",
						By(
							positive,
							ordered,
							At(gaussianRiemannIntegral, a, b),
							real_integral.RiemannIntegralNonneg.At(
								arg.TermAs[Fun[Real, Real]]("«gaussian»"),
								a,
								b,
								arg.TermAs[Real]("real_integral(«gaussian», a, b)"))))
				})

			reflection := ctx.Lemma(Statement{
				Binders: "∀t:real.",
				Hypotheses: []string{
					"&0 ≤ t",
				},
				Conclusion: "real_integral(«gaussian», -t, t) = «symmetricValue»(t)",
			},
				func(d *Argument, t *Expr[Real], nonnegative Fact) {
					gaussian := d.TermAs[Fun[Real, Real]]("«gaussian»")
					reflected := d.TermAs[Fun[Real, Real]]("λx:real. «gaussian»(-x) * -&1")
					zero, minusOne := d.TermAs[Real]("&0"), d.TermAs[Real]("-&1")
					left := d.TermAs[Real]("-t")
					positiveHalf := d.Have(
						"the Gaussian has its integral over ⟦0, t⟧",
						"real_has_integral(«gaussian», &0, t, «primitive»(t))",
						By(nonnegative, At(gaussianRiemannIntegral, zero, t)))
					negated := d.Have(
						"so −1 times it has −1 times that integral",
						"real_has_integral(λx:real. -&1 * «gaussian»(x), &0, t, -&1 * «primitive»(t))",
						By(
							positiveHalf,
							real_integral.HasIntegralScale.At(gaussian, zero, t, d.TermAs[Real]("«primitive»(t)"), minusOne)))
					even := d.Have(
						"the Gaussian is even, so −G(x) is G(−x)·(−1)",
						"∀x:real. &0 ≤ x ∧ x ≤ t ⇒ -&1 * «gaussian»(x) = «gaussian»(-x) * -&1",
						Derive(func(e *Argument) {
							e.FixAs[Real]("x")
							e.Assume()
							square := e.Have(
								"squaring removes the sign",
								"-(-x) ^ 2 = -x ^ 2",
								ByArith(Raw))
							e.Show(
								"reflect the argument",
								square.Rw(),
								ByArith(Raw))
						}))
					reflectedIntegral := d.Have(
						"so G(−x)·(−1) has the integral −∫₀ᵗ G",
						"real_has_integral(λx:real. «gaussian»(-x) * -&1, &0, t, -&1 * «primitive»(t))",
						By(
							even,
							negated,
							real_integral.HasIntegralCongruence.At(
								d.TermAs[Fun[Real, Real]]("λx:real. -&1 * «gaussian»(x)"),
								reflected,
								zero,
								t,
								d.TermAs[Real]("-&1 * «primitive»(t)"))))
					slope := d.Have(
						"x ↦ −x has derivative −1 and maps ⟦0, t⟧ inside (−t − 1, 1)",
						"∀x:real. &0 ≤ x ∧ x ≤ t ⇒ real_derivative_at(λx:real. -x, x, -&1) ∧ -t - &1 < -x ∧ -x < &1",
						Derive(func(e *Argument) {
							x := e.FixAs[Real]("x")
							inside := e.Assume()
							e.Show(
								"negate the identity's derivative",
								ByArith(
									inside,
									real_derivative.DerivativeId.At(x),
									real_derivative.DerivativeNeg.At(e.TermAs[Fun[Real, Real]]("λx:real. x"), x, e.TermAs[Real]("&1"))))
						}))
					substitution := d.Have(
						"substitute x ↦ −x",
						"real_integral(λx:real. «gaussian»(-x) * -&1, &0, t) = real_integral(«gaussian», -&0, -t)",
						By(
							nonnegative,
							slope,
							At(gaussianContinuity, d.TermAs[Set[Real]]("⟦-t - &1, &1⟧")),
							real_continuous.ContinuousOnConst.At(minusOne, d.TermAs[Set[Real]]("⟦&0, t⟧")),
							real_integral.IntegralSubstitution.At(
								gaussian,
								d.TermAs[Fun[Real, Real]]("λx:real. -x"),
								d.TermAs[Fun[Real, Real]]("λx:real. -&1"),
								zero,
								t,
								d.TermAs[Real]("-t - &1"),
								d.TermAs[Real]("&1"))))
					reflectedValue := d.Have(
						"so the primitive at −t is −1 times the primitive at t",
						"«primitive»(-t) = -&1 * «primitive»(t)",
						By(
							substitution,
							reflectedIntegral,
							real_ring.NegZero,
							real_integral.HasIntegralValue.At(reflected, zero, t, d.TermAs[Real]("-&1 * «primitive»(t)"))))
					order := d.Have(
						"−t ≤ 0",
						"-t ≤ &0",
						ByArith(Raw, nonnegative))
					negativeHalf := d.Have(
						"the Gaussian has its integral over ⟦−t, 0⟧",
						"real_has_integral(«gaussian», -t, &0, real_integral(«gaussian», -t, &0))",
						By(order, At(gaussianRiemannIntegral, left, zero)))
					reversed := d.Have(
						"reversing ⟦−t, 0⟧ negates its integral",
						"«primitive»(-t) = -real_integral(«gaussian», -t, &0)",
						By(
							negativeHalf,
							real_integral.IntegralReverse.At(
								gaussian, left, zero, d.TermAs[Real]("real_integral(«gaussian», -t, &0)"))))
					halves := d.Have(
						"so the two halves have one integral",
						"real_integral(«gaussian», -t, &0) = «primitive»(t)",
						ByArith(Raw, reflectedValue, reversed))
					split := d.Have(
						"⟦−t, t⟧ splits at 0",
						"real_integral(«gaussian», -t, &0) + «primitive»(t) = real_integral(«gaussian», -t, t)",
						By(
							order,
							nonnegative,
							negativeHalf,
							positiveHalf,
							real_integral.IntegralAdditiveOrdered.At(
								gaussian,
								left,
								zero,
								t,
								d.TermAs[Real]("real_integral(«gaussian», -t, &0)"),
								d.TermAs[Real]("«primitive»(t)"))))
					d.Show(
						"add the two equal halves",
						ByArith(Raw, split, halves))
				})
			initialValues := ctx.Lemma("«primitive»(&0) = &0 ∧ «angular»(&0) = π / &4",
				func(a *Argument) {
					a.Do(
						SplitConj(
							Case(
								"evaluate the primitive at zero",

								Derive(func(d *Argument) {
									gaussianAtZero := d.Have(
										"gaussian at zero",
										"real_continuous_on(⟦&0, &0⟧, «gaussian»)",
										By(At(gaussianContinuity, d.TermAs[Set[Real]]("⟦&0, &0⟧"))),
									)
									degenerateInterval := d.Have(
										"degenerate interval",
										"&0 ≤ &0",
										ByArith(Raw),
									)
									additivityAtZero := d.Have(
										"additivity at zero",
										"«primitive»(&0) + «primitive»(&0) = «primitive»(&0)",
										By(
											degenerateInterval,
											gaussianAtZero,
											At(
												real_integral.IntegralAdditive,
												d.TermAs[Fun[Real, Real]]("«gaussian»"),
												d.TermAs[Real]("&0"),
												d.TermAs[Real]("&0"),
												d.TermAs[Real]("&0"),
												d.TermAs[Real]("&0"),
												d.TermAs[Real]("&0"))),
									)
									d.Show(
										"additivity on the degenerate interval gives zero",
										ByArith(Raw, additivityAtZero),
									)
								}),
							),
							Case(
								"evaluate the angular integral at zero",

								Derive(func(d *Argument) {
									angularAtZero := d.Have(
										"angular at zero",
										"real_has_integral(λx:real. «integrand»(&0, x), &0, &1, «angular»(&0))",
										By(At(angularIntegrability, d.TermAs[Real]("&0"))),
									)
									inverseShapeAgreement := d.Have(
										"inverse shape agreement",
										"∀x:real. &0 ≤ x ∧ x ≤ &1 ⇒ «integrand»(&0, x) = real_inv(«shape»(x))",
										Derive(func(e *Argument) {
											e.FixAs[Real]("x")
											e.Assume()
											zeroExponent := e.Have(
												"zero exponent",
												"«exponent»(«shape»(x), &0) = &0",
												ByArith(Raw),
											)
											zeroExponential := e.Have(
												"zero exponential",
												"exp(«exponent»(«shape»(x), &0)) = &1",
												By(zeroExponent, real_exp_log.ExpZero),
											)
											e.Show(
												"the kernel at zero is the inverse shape",
												zeroExponential.Rw(),
												ByArith(Raw),
											)
										}),
									)
									inverseShapeIntegral := d.Have(
										"inverse shape integral",
										"real_has_integral(λx:real. real_inv(«shape»(x)), &0, &1, «angular»(&0))",
										By(
											inverseShapeAgreement,
											angularAtZero,
											At(
												real_integral.HasIntegralCongruence,
												d.TermAs[Fun[Real, Real]]("λx:real. «integrand»(&0, x)"),
												d.TermAs[Fun[Real, Real]]("λx:real. real_inv(«shape»(x))"),
												d.TermAs[Real]("&0"),
												d.TermAs[Real]("&1"),
												d.TermAs[Real]("«angular»(&0)"))),
									)
									arctanDifferentiable := d.Have(
										"arctan differentiable",
										"∀x:real. x ∈ ⟦&0, &1⟧ ⇒ real_derivative_at(arctan, x, real_inv(«shape»(x)))",
										By(real_inverse_trigonometry.ArctanDerivative),
									)
									arctanContinuous := d.Have(
										"arctan continuous",
										"real_continuous_on(⟦&0, &1⟧, arctan)",
										By(
											arctanDifferentiable,
											At(
												real_derivative.DerivativeContinuousOn,
												d.TermAs[Fun[Real, Real]]("real_arctan"),
												d.TermAs[Fun[Real, Real]]("λx:real. real_inv(«shape»(x))"),
												d.TermAs[Set[Real]]("⟦&0, &1⟧"))),
									)
									arctanDerivativeInside := d.Have(
										"arctan derivative inside",
										"∀x:real. &0 < x ∧ x < &1 ⇒ real_derivative_at(arctan, x, real_inv(«shape»(x)))",
										By(real_inverse_trigonometry.ArctanDerivative),
									)
									d.Show(
										"evaluate the arctangent at the two endpoints",
										ByArith(
											arctanContinuous,
											arctanDerivativeInside,
											inverseShapeIntegral,
											At(
												real_integral.NewtonLeibniz,
												d.TermAs[Fun[Real, Real]]("real_arctan"),
												d.TermAs[Fun[Real, Real]]("λx:real. real_inv(«shape»(x))"),
												d.TermAs[Real]("&0"),
												d.TermAs[Real]("&1"),
												d.TermAs[Real]("«angular»(&0)")),
											real_inverse_trigonometry.ArctanOne,
											real_inverse_trigonometry.ArctanZero),
									)
								}),
							),
						),
					)
				})

			constantIdentity := ctx.Lemma(Statement{
				Binders: "∀t:real.",
				Hypotheses: []string{
					"&0 ≤ t",
				},
				Conclusion: "«primitive»(t) * «primitive»(t) + «angular»(t) = π / &4",
			},
				func(d *Argument, t *Expr[Real], nonnegative Fact) {
					continuousGaussian := d.Have(
						"continuous gaussian",
						"real_continuous_on(⟦&0, t⟧, «gaussian»)",
						By(At(gaussianContinuity, d.TermAs[Set[Real]]("⟦&0, t⟧"))),
					)
					continuousPrimitive := d.Have(
						"continuous primitive",
						"real_continuous_on(⟦&0, t⟧, «primitive»)",
						ByArith(
							nonnegative,
							continuousGaussian,
							At(
								real_integral.IntegralContinuousOn,
								d.TermAs[Fun[Real, Real]]("«gaussian»"),
								d.TermAs[Real]("&0"),
								t,
								d.TermAs[Real]("&0"))),
					)
					differentiableAngular := d.Have(
						"differentiable angular",
						"∀x:real. x ∈ ⟦&0, t⟧ ⇒ real_derivative_at(«angular», x, «angularSlope»(x))",
						By(angularDerivative),
					)
					continuousAngular := d.Have(
						"continuous angular",
						"real_continuous_on(⟦&0, t⟧, «angular»)",
						By(
							differentiableAngular,
							At(
								real_derivative.DerivativeContinuousOn,
								d.TermAs[Fun[Real, Real]]("«angular»"),
								d.TermAs[Fun[Real, Real]]("«angularSlope»"),
								d.TermAs[Set[Real]]("⟦&0, t⟧"))),
					)
					continuousPrimitiveSquare := d.Have(
						"continuous primitive square",
						"real_continuous_on(⟦&0, t⟧, λx:real. «primitive»(x) * «primitive»(x))",
						By(
							continuousPrimitive,
							At(
								real_continuous.ContinuousOnMul,
								d.TermAs[Fun[Real, Real]]("«primitive»"),
								d.TermAs[Fun[Real, Real]]("«primitive»"),
								d.TermAs[Set[Real]]("⟦&0, t⟧"))),
					)
					continuousSum := d.Have(
						"continuous sum",
						"real_continuous_on(⟦&0, t⟧, λx:real. «primitive»(x) * «primitive»(x) + «angular»(x))",
						By(
							continuousPrimitiveSquare,
							continuousAngular,
							At(
								real_continuous.ContinuousOnAdd,
								d.TermAs[Fun[Real, Real]]("λx:real. «primitive»(x) * «primitive»(x)"),
								d.TermAs[Fun[Real, Real]]("«angular»"),
								d.TermAs[Set[Real]]("⟦&0, t⟧"))),
					)
					zeroDerivative := d.Have(
						"zero derivative",
						Statement{
							Binders: "∀x:real.",
							Hypotheses: []string{
								"&0 < x",
								"x < t",
							},
							Conclusion: "real_derivative_at(λx:real. «primitive»(x) * «primitive»(x) + «angular»(x), x, &0)",
						},
						Derive(func(e *Argument) {
							x := e.FixAs[Real]("x")
							inside := e.Assume()
							primitiveDerivative := e.Have(
								"primitive derivative",
								"real_derivative_at(«primitive», x, «gaussian»(x))",
								By(
									inside,
									continuousGaussian,
									At(
										real_integral.IntegralDerivative,
										e.TermAs[Fun[Real, Real]]("«gaussian»"),
										e.TermAs[Real]("&0"),
										t,
										x)),
							)
							angularLocalDerivative := e.Have(
								"angular local derivative",
								"real_derivative_at(«angular», x, «angularSlope»(x))",
								By(At(angularDerivative, x)),
							)
							squareLocalDerivative := e.Have(
								"square local derivative",
								"real_derivative_at(λx:real. «primitive»(x) * «primitive»(x), "+
									"    x, "+
									"    «gaussian»(x) * «primitive»(x) + «primitive»(x) * «gaussian»(x))",
								By(
									primitiveDerivative,
									At(
										real_derivative.DerivativeMul,
										e.TermAs[Fun[Real, Real]]("«primitive»"),
										e.TermAs[Fun[Real, Real]]("«primitive»"),
										x,
										e.TermAs[Real]("«gaussian»(x)"),
										e.TermAs[Real]("«gaussian»(x)"))),
							)
							sumDerivative := e.Have(
								"sum derivative",
								"real_derivative_at(λx:real. «primitive»(x) * «primitive»(x) + «angular»(x), "+
									"    x, "+
									"    «gaussian»(x) * «primitive»(x) + «primitive»(x) * «gaussian»(x) + «angularSlope»(x))",
								By(
									squareLocalDerivative,
									angularLocalDerivative,
									At(
										real_derivative.DerivativeAdd,
										e.TermAs[Fun[Real, Real]]("λx:real. «primitive»(x) * «primitive»(x)"),
										e.TermAs[Fun[Real, Real]]("«angular»"),
										x,
										e.TermAs[Real]("«gaussian»(x) * «primitive»(x) + «primitive»(x) * «gaussian»(x)"),
										e.TermAs[Real]("«angularSlope»(x)"))),
							)
							nonnegativePoint := e.Have(
								"nonnegative point",
								"&0 ≤ x",
								ByArith(Raw, inside),
							)
							slopeFormula := e.Have(
								"slope formula",
								"«angularSlope»(x) = -(&2 * «gaussian»(x) * «primitive»(x))",
								By(nonnegativePoint, At(angularSlopeValue, x)),
							)
							cancelledSlope := e.Have(
								"cancelled slope",
								"«gaussian»(x) * «primitive»(x) + «primitive»(x) * «gaussian»(x) + «angularSlope»(x) = &0",
								ByArith(Raw, slopeFormula),
							)
							e.Show(
								"the two derivatives cancel on the interior",
								By(sumDerivative, cancelledSlope),
							)
						}),
					)
					valueAtOrigin := d.Have(
						"value at origin",
						"«primitive»(t) * «primitive»(t) + «angular»(t) = "+
							"«primitive»(&0) * «primitive»(&0) + «angular»(&0)",
						ByArith(
							nonnegative,
							zeroDerivative,
							continuousSum,
							At(
								real_derivative.DerivativeZeroConstant,
								d.TermAs[Fun[Real, Real]]("λx:real. «primitive»(x) * «primitive»(x) + «angular»(x)"),
								d.TermAs[Real]("&0"),
								t,
								t)),
					)
					d.Show(
						"the sum is constant and equals its value at zero",
						ByArith(valueAtOrigin, initialValues),
					)
				})

			symmetricDistance := ctx.Lemma(Statement{
				Binders: "∀t:real.",
				Hypotheses: []string{
					"&0 ≤ t",
				},
				Conclusion: "&0 ≤ «symmetricValue»(t) ∧ " +
					"«symmetricValue»(t) ≤ real_sqrt(pi) ∧ " +
					"|real_sqrt(pi) * «symmetricValue»(t) - real_sqrt(pi) * real_sqrt(pi)| ≤ &4 * «angular»(t)",
			},
				func(d *Argument, t *Expr[Real], nonnegative Fact) {
					piPositive := d.Have(
						"pi positive",
						"&0 < π",
						By(real_trigonometry.PiBounds),
					)
					piNonnegative := d.Have(
						"pi nonnegative",
						"&0 ≤ π",
						ByArith(Raw, piPositive),
					)
					rootPositive := d.Have(
						"root positive",
						"&0 < real_sqrt(pi)",
						By(piPositive, At(real_sqrt.SqrtPos, d.TermAs[Real]("π"))),
					)
					rootSquare := d.Have(
						"root square",
						"real_sqrt(pi) ^ 2 = π",
						By(piNonnegative, At(real_sqrt.SqrtPowTwo, d.TermAs[Real]("π"))),
					)
					primitiveNonnegative := d.Have(
						"primitive nonnegative",
						"&0 ≤ «primitive»(t)",
						By(nonnegative, At(gaussianRiemannNonnegative, d.TermAs[Real]("&0"), t)),
					)
					angularNonnegative := d.Have(
						"angular nonnegative",
						"&0 ≤ «angular»(t)",
						By(At(angularBounds, t)),
					)
					integralIdentity := d.Have(
						"integral identity",
						"«primitive»(t) * «primitive»(t) + «angular»(t) = π / &4",
						By(nonnegative, At(constantIdentity, t)),
					)
					symmetricSquareIdentity := d.Have(
						"symmetric square identity",
						"«symmetricValue»(t) ^ 2 + &4 * «angular»(t) = π",
						ByArith(Raw, integralIdentity),
					)
					symmetricNonnegative := d.Have(
						"symmetric nonnegative",
						"&0 ≤ «symmetricValue»(t)",
						ByArith(Raw, primitiveNonnegative),
					)
					symmetricSquareBound := d.Have(
						"symmetric square bound",
						"«symmetricValue»(t) ^ 2 ≤ π",
						ByArith(Raw, angularNonnegative, symmetricSquareIdentity),
					)
					symmetricUpper := d.Have(
						"symmetric upper",
						"«symmetricValue»(t) ≤ real_sqrt(pi)",
						By(
							symmetricSquareBound,
							At(real_sqrt.SqrtLowerBound, d.TermAs[Real]("«symmetricValue»(t)"), d.TermAs[Real]("π"))),
					)
					signedDistance := d.Have(
						"signed distance",
						"real_sqrt(pi) * «symmetricValue»(t) - real_sqrt(pi) * real_sqrt(pi) ≤ &0",
						ByArith(
							rootPositive,
							symmetricUpper,
							At(
								real_order_ring.LessEqMulLeft,
								d.TermAs[Real]("real_sqrt(pi)"),
								d.TermAs[Real]("«symmetricValue»(t)"),
								d.TermAs[Real]("real_sqrt(pi)"))),
					)
					absoluteDistance := d.Have(
						"absolute distance",
						"|real_sqrt(pi) * «symmetricValue»(t) - real_sqrt(pi) * real_sqrt(pi)| = "+
							"-(real_sqrt(pi) * «symmetricValue»(t) - real_sqrt(pi) * real_sqrt(pi))",
						By(
							signedDistance,
							At(
								real_sgn_abs.AbsNegatedIffNonpos,
								d.TermAs[Real]("real_sqrt(pi) * «symmetricValue»(t) - real_sqrt(pi) * real_sqrt(pi)"))),
					)
					squareComparison := d.Have(
						"square comparison",
						"«symmetricValue»(t) * «symmetricValue»(t) ≤ real_sqrt(pi) * «symmetricValue»(t)",
						By(
							symmetricNonnegative,
							symmetricUpper,
							At(
								real_order_ring.LessEqMulRight,
								d.TermAs[Real]("«symmetricValue»(t)"),
								d.TermAs[Real]("real_sqrt(pi)"),
								d.TermAs[Real]("«symmetricValue»(t)"))),
					)
					distanceComparison := d.Have(
						"distance comparison",
						"-(real_sqrt(pi) * «symmetricValue»(t) - real_sqrt(pi) * real_sqrt(pi)) ≤ &4 * «angular»(t)",
						ByArith(Raw, rootSquare, symmetricSquareIdentity, squareComparison),
					)
					d.Show(
						"combine the symmetric integral and distance bounds",
						By(symmetricNonnegative, symmetricUpper, absoluteDistance, distanceComparison),
					)
				})

			exponentialDecay := ctx.Lemma("∀n:num. &4 * «gaussian»(«windowRadius»(n)) < real_inv(&n + &1)",
				func(d *Argument, n *Expr[Nat]) {
					indexNonnegative := d.Have(
						"index nonnegative",
						"&0 ≤ &n",
						By(At(real_order_ring.NumNonneg, n)),
					)
					denominatorPositive := d.Have(
						"denominator positive",
						"&0 < &n + &1",
						ByArith(Raw, indexNonnegative),
					)
					squaredRadiusNonnegative := d.Have(
						"squared radius nonnegative",
						"&0 ≤ «windowRadius»(n) ^ 2",
						By(At(real_pow.PowTwoNonneg, d.TermAs[Real]("«windowRadius»(n)"))),
					)
					exponentialLowerBound := d.Have(
						"exponential lower bound",
						"«shape»(«windowRadius»(n)) ≤ exp(«windowRadius»(n) ^ 2)",
						By(
							squaredRadiusNonnegative,
							At(real_exp_log.ExpLowerBound, d.TermAs[Real]("«windowRadius»(n) ^ 2"))),
					)
					polynomialGrowth := d.Have(
						"polynomial growth",
						"&4 * (&n + &1) < «shape»(«windowRadius»(n))",
						ByArith(Raw, indexNonnegative, At(real_pow.PowTwoNonneg, d.TermAs[Real]("&n"))),
					)
					exponentialGrowth := d.Have(
						"exponential growth",
						"&4 * (&n + &1) < exp(«windowRadius»(n) ^ 2)",
						ByArith(polynomialGrowth, exponentialLowerBound),
					)
					gaussianPositive := d.Have(
						"gaussian positive",
						"&0 < «gaussian»(«windowRadius»(n))",
						By(At(real_exp_log.ExpPositive, d.TermAs[Real]("-«windowRadius»(n) ^ 2"))),
					)
					growthPositive := d.Have(
						"growth positive",
						"&0 < exp(«windowRadius»(n) ^ 2)",
						By(At(real_exp_log.ExpPositive, d.TermAs[Real]("«windowRadius»(n) ^ 2"))),
					)
					inverseGrowthProduct := d.Have(
						"inverse growth product",
						"real_inv(exp(«windowRadius»(n) ^ 2)) * exp(«windowRadius»(n) ^ 2) = &1",
						ByArith(
							growthPositive,
							At(field.MulLeftInverse.Read(real_field.Field), d.TermAs[Real]("exp(«windowRadius»(n) ^ 2)"))),
					)
					gaussianAsInverse := d.Have(
						"gaussian as inverse",
						"«gaussian»(«windowRadius»(n)) = real_inv(exp(«windowRadius»(n) ^ 2))",
						By(At(real_exp_log.ExpNeg, d.TermAs[Real]("«windowRadius»(n) ^ 2"))),
					)
					inverseExponentialProduct := d.Have(
						"inverse exponential product",
						"«gaussian»(«windowRadius»(n)) * exp(«windowRadius»(n) ^ 2) = &1",
						By(gaussianAsInverse, inverseGrowthProduct),
					)
					inverseDenominatorProduct := d.Have(
						"inverse denominator product",
						"real_inv(&n + &1) * (&n + &1) = &1",
						ByArith(
							denominatorPositive,
							At(field.MulLeftInverse.Read(real_field.Field), d.TermAs[Real]("&n + &1"))),
					)
					multipliedGrowth := d.Have(
						"multiplied growth",
						"&4 * (&n + &1) * «gaussian»(«windowRadius»(n)) < "+
							"exp(«windowRadius»(n) ^ 2) * «gaussian»(«windowRadius»(n))",
						By(
							exponentialGrowth,
							gaussianPositive,
							At(
								real_order_ring.LessThanMulRight,
								d.TermAs[Real]("&4 * (&n + &1)"),
								d.TermAs[Real]("exp(«windowRadius»(n) ^ 2)"),
								d.TermAs[Real]("«gaussian»(«windowRadius»(n))"))),
					)
					denominatorComparison := d.Have(
						"denominator comparison",
						"&4 * «gaussian»(«windowRadius»(n)) * (&n + &1) < real_inv(&n + &1) * (&n + &1)",
						ByArith(Raw, multipliedGrowth, inverseExponentialProduct, inverseDenominatorProduct),
					)
					d.Show(
						"cancel the positive denominator",
						By(
							denominatorPositive,
							denominatorComparison,
							At(
								real_order_ring.LessThanCancelMulRight,
								d.TermAs[Real]("&4 * «gaussian»(«windowRadius»(n))"),
								d.TermAs[Real]("real_inv(&n + &1)"),
								d.TermAs[Real]("&n + &1"))),
					)
				})
			windowConvergence := ctx.Lemma("«windowValues» ⟶ real_sqrt(pi)",
				func(a *Argument) {
					root := a.TermAs[Real]("real_sqrt(pi)")
					rootPositive := a.Have(
						"√π is positive",
						"&0 < real_sqrt(pi)",
						By(real_trigonometry.PiBounds, real_sqrt.SqrtPos.At(a.TermAs[Real]("π"))))
					inverseRoot := a.Have(
						"1/√π times √π is 1",
						"real_inv(real_sqrt(pi)) * real_sqrt(pi) = &1",
						ByArith(rootPositive, At(field.MulLeftInverse.Read(real_field.Field), root)))
					reciprocalError := a.Have(
						"√π times the n-th window value is within 1/(n + 1) of π",
						"∀n:num. |real_sqrt(pi) * «windowValues»(n) - real_sqrt(pi) * real_sqrt(pi)| < real_inv(&n + &1)",
						Derive(func(d *Argument) {
							n := d.FixAs[Nat]("n")
							radius := d.TermAs[Real]("«windowRadius»(n)")
							nonnegativeRadius := d.Have(
								"the radius is nonnegative",
								"&0 ≤ «windowRadius»(n)",
								ByArith(Raw, real_order_ring.NumNonneg.At(n)))
							d.Show(
								"the distance is at most 4·«angular» at the radius, below 4·«gaussian» there, below 1/(n + 1)",
								ByArith(
									nonnegativeRadius,
									At(symmetricDistance, radius),
									At(angularBounds, radius),
									At(exponentialDecay, n)))
						}))
					scaledLimit := a.Have(
						"so √π times the window values tend to π",
						"(λn:num. real_sqrt(pi) * «windowValues»(n)) ⟶ real_sqrt(pi) * real_sqrt(pi)",
						By(
							reciprocalError,
							real_sequences.WithinReciprocalConverges.At(
								a.TermAs[Fun[Nat, Real]]("λn:num. real_sqrt(pi) * «windowValues»(n)"),
								a.TermAs[Real]("real_sqrt(pi) * real_sqrt(pi)"))))
					rescaled := a.Have(
						"and 1/√π times those tend to π/√π",
						"(λn:num. real_inv(real_sqrt(pi)) * (real_sqrt(pi) * «windowValues»(n))) ⟶ "+
							"real_inv(real_sqrt(pi)) * (real_sqrt(pi) * real_sqrt(pi))",
						By(
							scaledLimit,
							real_sequences.LimitScale.At(
								a.TermAs[Fun[Nat, Real]]("λn:num. real_sqrt(pi) * «windowValues»(n)"),
								a.TermAs[Real]("real_sqrt(pi) * real_sqrt(pi)"),
								a.TermAs[Real]("real_inv(real_sqrt(pi))"))))
					sequence := a.Have(
						"1/√π cancels √π in each term",
						"(λn:num. real_inv(real_sqrt(pi)) * (real_sqrt(pi) * «windowValues»(n))) = «windowValues»",
						Funext(),
						Derive(func(d *Argument) {
							d.FixAs[Nat]("n")
							d.Show(
								"cancel √π",
								ByArith(Scaled(d.TermAs[Real]("«windowValues»(n)"), inverseRoot)))
						}))
					limit := a.Have(
						"and in the limit",
						"real_inv(real_sqrt(pi)) * (real_sqrt(pi) * real_sqrt(pi)) = real_sqrt(pi)",
						ByArith(Scaled(root, inverseRoot)))
					a.Show(
						"so the window values tend to √π",
						By(rescaled, sequence, limit))
				})
			return ctx.Theorem(headline,
				func(a *Argument) {
					integrandNonnegative := a.Have(
						"the Gaussian is positive",
						"∀x:real. &0 ≤ «gaussian»(x)",
						Derive(func(d *Argument) {
							d.FixAs[Real]("x")
							d.Show(
								"exp is positive",
								ByArith(Raw, real_exp_log.ExpPositive.At(d.TermAs[Real]("-x ^ 2"))))
						}))
					orderedWindows := a.Have(
						"each window ⟦−(n + 2), n + 2⟧ is ordered",
						"∀n:num. «windowLower»(n) ≤ «windowRadius»(n)",
						Derive(func(d *Argument) {
							n := d.FixAs[Nat]("n")
							d.Show(
								"its radius n + 2 is positive",
								ByArith(real_order_ring.NumNonneg.At(n)))
						}),
					)
					nestedWindows := a.Have(
						"the windows grow with n",
						"∀n:num. «windowLower»(n + 1) ≤ «windowLower»(n) ∧ «windowRadius»(n) ≤ «windowRadius»(n + 1)",
						Derive(func(d *Argument) {
							n := d.FixAs[Nat]("n")
							d.Show(
								"the radius grows with n",
								ByArith(real_construction.OfNumAdd.At(n, d.TermAs[Nat]("1"))))
						}))
					coveringWindows := a.Have(
						"every point lies in some window",
						"∀x:real. ∃n:num. x ∈ ⟦«windowLower»(n), «windowRadius»(n)⟧",
						Derive(func(d *Argument) {
							x := d.FixAs[Real]("x")
							n, bounds := d.ObtainAs[Nat](
								"x lies in some ⟦−n, n⟧",
								"∃n:num. -&n ≤ x ∧ x ≤ &n",
								By(real_archimedean.ExistsNumBounds.At(x)))
							d.Show(
								"and so in the larger window about n",
								Witness(n),
								ByArith(
									bounds,
									real_topology.ClosedIntervalMembership.At(
										x, d.TermAs[Real]("«windowLower»(n)"), d.TermAs[Real]("«windowRadius»(n)"))))
						}))
					windowLimit := a.Have(
						"each window integral is the symmetric value at its radius, so they converge to √π",
						"(λn:num. real_integral(«gaussian», «windowLower»(n), «windowRadius»(n))) ⟶ real_sqrt(pi)",
						Derive(func(d *Argument) {
							same := d.Have(
								"the integral over ⟦−(n + 2), n + 2⟧ is twice the primitive at n + 2",
								"(λn:num. real_integral(«gaussian», «windowLower»(n), «windowRadius»(n))) = «windowValues»",
								Funext(),
								Derive(func(e *Argument) {
									n := e.FixAs[Nat]("n")
									radius := e.TermAs[Real]("«windowRadius»(n)")
									nonnegRadius := e.Have(
										"the radius n + 2 is nonnegative",
										"&0 ≤ «windowRadius»(n)",
										ByArith(real_order_ring.NumNonneg.At(n)))
									e.Show(
										"reflection at the nonnegative radius",
										By(nonnegRadius, At(reflection, radius)))
								}))
							d.Show(
								"the symmetric values converge to √π",
								By(same, windowConvergence))
						}),
					)
					gaussian := a.TermAs[Fun[Real, Real]]("«gaussian»")
					integral := a.Have(
						"so the Gaussian is integrable on the line, with integral √π",
						"real_integrable(𝕌, «lebesgueSets», lebesgue_outer_measure, «gaussian») ∧ "+
							"measure_integral(𝕌, «lebesgueSets», lebesgue_outer_measure, «gaussian») = real_sqrt(pi)",
						By(
							integrandNonnegative,
							At(gaussianContinuity, a.TermAs[Set[Real]]("𝕌")),
							orderedWindows,
							nestedWindows,
							coveringWindows,
							windowLimit,
							LebesgueIntegralByWindows.At(
								gaussian,
								a.TermAs[Fun[Nat, Real]]("«windowLower»"),
								a.TermAs[Fun[Nat, Real]]("«windowRadius»"),
								a.TermAs[Real]("real_sqrt(pi)"))),
					)
					a.Show(
						"which is the chapter's Lebesgue integral",
						By(
							integral,
							lebesgue_integral.LebesgueIntegrableIff.At(gaussian),
							lebesgue_integral.LebesgueIntegralEq.At(gaussian)),
					)
				})
		}),
})}
