package real_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// UniformSmoothApproximation — a bounded uniformly continuous function on the
// line is uniformly within ε of a function with three bounded derivatives. The
// average of f over [x, x + d] has the difference quotient of f as its
// derivative, so the triple average at width d is the bottom of a tower of
// three derivatives, the k-th a k-fold difference quotient of a (3 − k)-fold
// average of f, bounded by (2/d)^k·B; and where f moves by at most e over a
// distance d, each average moves it by at most e. Uniform continuity at ε/4
// gives the width.
var UniformSmoothApproximation = uniformSmoothApproximationThm{family.Add(registry.ProofEntry{
	Name: "UniformSmoothApproximation",
	Key:  "prop_d70c21d6646bd658",
	Reading: "D is a tower of derivatives, D(k + 1) the derivative of D(k) for k ≤ 2, and one bound " +
		"holds D(0), …, D(3): D(0) is three times differentiable, bounded with its three derivatives.",
	Build: family.Sections(Statement{
		Binders: "∀f:(real → real). ∀B ε:real.",
		Hypotheses: []string{
			"real_uniformly_continuous_on(𝕌, f)",
			"«boundedBy»(f, B)",
			"&0 < ε",
		},
		Conclusion: "∃D:(num → real → real). «boundedTower»(D) ∧ «boundedBy»(λx:real. D(0, x) - f(x), ε)",
		Abbrev: Abbrev{
			{Name: "average", Text: "λδ:real. λf:(real → real). λx:real. " +
				"    real_inv(δ) * real_integral(f, x, x + δ)"},
			{Name: "difference", Text: "λδ:real. λf:(real → real). λx:real. real_inv(δ) * (f(x + δ) - f(x))"},
			{Name: "boundedTower", Text: "λD:(num → real → real). " +
				"    (∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))) ∧ " +
				"    (∃M:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |D(k)(y)| ≤ M)"},
			{Name: "boundedBy", Text: "λf:(real → real). λB:real. ∀x:real. |f(x)| ≤ B"},
			{Name: "averagedTwice", Text: "λd:real. λf:(real → real). «average»(d, «average»(d, f))"},
			{Name: "averagedThrice", Text: "λd:real. λf:(real → real). «average»(d, «averagedTwice»(d, f))"},
			{Name: "smoothedFirst", Text: "λd:real. λf:(real → real). «difference»(d, «averagedTwice»(d, f))"},
			{Name: "smoothedSecond", Text: "λd:real. λf:(real → real). " +
				"    «difference»(d, «difference»(d, «average»(d, f)))"},
			{Name: "smoothedThird", Text: "λd:real. λf:(real → real). " +
				"    «difference»(d, «difference»(d, «difference»(d, f)))"},
			{Name: "smoothedTower", Text: "λd:real. λf:(real → real). λk:num. " +
				"    COND(k = 0, " +
				"        «averagedThrice»(d, f), " +
				"        COND(k = 1, " +
				"            «smoothedFirst»(d, f), " +
				"            COND(k = 2, «smoothedSecond»(d, f), «smoothedThird»(d, f))))"},
			{Name: "incrementBound", Text: "λd:real. λB:real. real_inv(d) * (&2 * B)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A function continuous on the line is continuous on ⟦a, b⟧, so it has its integral there.
			globalHasIntegral := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀a b:real.",
				Hypotheses: []string{
					"real_continuous_on(𝕌, f)",
					"a ≤ b",
				},
				Conclusion: "real_has_integral(f, a, b, real_integral(f, a, b))",
			},
				func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], continuous, ordered Fact) {
					inLine := arg.Have(
						"⟦a, b⟧ is a part of the line",
						"⟦a₀, b₀⟧ ⊆ 𝕌",
						BySets(),
					)
					onInterval := arg.Have(
						"so f is continuous on ⟦a, b⟧",
						"real_continuous_on(⟦a₀, b₀⟧, f₀)",
						By(
							continuous,
							inLine,
							real_continuous.ContinuousOnSubset.At(
								f, arg.TermAs[Set[Real]]("𝕌"), arg.TermAs[Set[Real]]("⟦a₀, b₀⟧"))),
					)
					arg.Show(
						"so it has its integral real_integral(f, a, b) there",
						By(ordered, onInterval, ContinuousHasIntegral.At(f, a, b)),
					)
				})

			translateDerivative := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀d x m:real.",
				Hypotheses: []string{
					"real_derivative_at(f, x + d, m)",
				},
				Conclusion: "real_derivative_at(λy:real. f(y + d), x, m)",
			},
				func(a *Argument, f *Arrow[Real, Real], d, x, m *Expr[Real], atShifted Fact) {
					shift := a.Have(
						"the shift y ↦ y + d has derivative 1 + 0",
						"real_derivative_at(λy:real. y + d₀, x₀, &1 + &0)",
						By(
							real_derivative.DerivativeId.At(x),
							real_derivative.DerivativeConst.At(d, x),
							real_derivative.DerivativeAdd.At(
								a.TermAs[Fun[Real, Real]]("λy:real. y"),
								a.TermAs[Fun[Real, Real]]("λy:real. d₀"),
								x,
								a.TermAs[Real]("&1"),
								a.TermAs[Real]("&0"))),
					)
					composite := a.Have(
						"y ↦ f(y + d) is f after the shift",
						"f₀ ∘ (λy:real. y + d₀) = λy:real. f₀(y + d₀)",
						By(functions.ComposeApply.At(f, a.TermAs[Fun[Real, Real]]("λy:real. y + d₀"))),
					)
					chain := a.Have(
						"by the chain rule it has derivative m·(1 + 0) at x",
						"real_derivative_at(λy:real. f₀(y + d₀), x₀, m₀ * (&1 + &0))",
						By(
							atShifted,
							shift,
							composite,
							real_derivative.DerivativeChain.At(
								f, a.TermAs[Fun[Real, Real]]("λy:real. y + d₀"), x, m, a.TermAs[Real]("&1 + &0"))),
					)
					unit := a.Have(
						"m·(1 + 0) = m",
						"m₀ * (&1 + &0) = m₀",
						ByArith(Raw),
					)
					a.Show(
						"so y ↦ f(y + d) has derivative m at x",
						By(Normalized, chain, unit),
					)
				})

			// With F(y) = ∫ f from x − 1 to y, the average of f over [y, y + d] is
			// (F(y + d) − F(y))/d for y near x, and F has derivative f there (the fundamental
			// theorem): so the average has derivative (f(x + d) − f(x))/d at x.
			averageDerivative := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀d x:real.",
				Hypotheses: []string{
					"&0 < d",
					"real_continuous_on(𝕌, f)",
				},
				Conclusion: "real_derivative_at(λx:real. «average»(d, f, x), x, «difference»(d, f, x))",
			},
				func(a *Argument, f *Arrow[Real, Real], d, x *Expr[Real], pos, continuous Fact) {
					inLine := a.Have(
						"⟦x − 1, x + d + 1⟧ is a part of the line",
						"⟦x₀ - &1, x₀ + d₀ + &1⟧ ⊆ 𝕌",
						BySets(),
					)
					onInterval := a.Have(
						"so f is continuous on ⟦x − 1, x + d + 1⟧",
						"real_continuous_on(⟦x₀ - &1, x₀ + d₀ + &1⟧, f₀)",
						By(
							continuous,
							inLine,
							real_continuous.ContinuousOnSubset.At(
								f, a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Real]]("⟦x₀ - &1, x₀ + d₀ + &1⟧"))),
					)
					primitiveAtX := a.Have(
						"F has derivative f(x) at x",
						"real_derivative_at(λy:real. real_integral(f₀, x₀ - &1, y), x₀, f₀(x₀))",
						ByArith(
							pos,
							continuous,
							onInterval,
							IntegralDerivative.At(
								f, a.TermAs[Real]("x₀ - &1"), a.TermAs[Real]("x₀ + d₀ + &1"), x)),
					)
					primitiveAtShift := a.Have(
						"and derivative f(x + d) at x + d",
						"real_derivative_at(λy:real. real_integral(f₀, x₀ - &1, y), x₀ + d₀, f₀(x₀ + d₀))",
						ByArith(
							pos,
							continuous,
							onInterval,
							IntegralDerivative.At(
								f, a.TermAs[Real]("x₀ - &1"), a.TermAs[Real]("x₀ + d₀ + &1"), a.TermAs[Real]("x₀ + d₀"))),
					)
					shiftedPrimitive := a.Have(
						"so y ↦ F(y + d) has derivative f(x + d) at x",
						"real_derivative_at(λy:real. (λy:real. real_integral(f₀, x₀ - &1, y))(y + d₀), x₀, f₀(x₀ + d₀))",
						By(
							primitiveAtShift,
							At(
								translateDerivative,
								a.TermAs[Fun[Real, Real]]("λy:real. real_integral(f₀, x₀ - &1, y)"),
								d,
								x,
								a.TermAs[Real]("f₀(x₀ + d₀)"))),
					)
					primitiveIncrement := a.Have(
						"y ↦ F(y + d) − F(y) has derivative f(x + d) − f(x) at x",
						"real_derivative_at(λy:real. "+
							"        (λy:real. (λy:real. real_integral(f₀, x₀ - &1, y))(y + d₀))(y) - "+
							"        (λy:real. real_integral(f₀, x₀ - &1, y))(y), "+
							"    x₀, "+
							"    f₀(x₀ + d₀) - f₀(x₀))",
						By(
							shiftedPrimitive,
							primitiveAtX,
							real_derivative.DerivativeSub.At(
								a.TermAs[Fun[Real, Real]]("λy:real. (λy:real. real_integral(f₀, x₀ - &1, y))(y + d₀)"),
								a.TermAs[Fun[Real, Real]]("λy:real. real_integral(f₀, x₀ - &1, y)"),
								x,
								a.TermAs[Real]("f₀(x₀ + d₀)"),
								a.TermAs[Real]("f₀(x₀)"))),
					)
					scaledIncrement := a.Have(
						"and divided by d, the difference quotient of f at x",
						"real_derivative_at(λy:real. "+
							"        real_inv(d₀) * "+
							"        (λy:real. "+
							"            (λy:real. (λy:real. real_integral(f₀, x₀ - &1, y))(y + d₀))(y) - "+
							"            (λy:real. real_integral(f₀, x₀ - &1, y))(y))(y), "+
							"    x₀, "+
							"    «difference»(d₀, f₀, x₀))",
						By(
							primitiveIncrement,
							real_derivative.DerivativeScale.At(
								a.TermAs[Fun[Real, Real]](
									"λy:real. "+
										"    (λy:real. (λy:real. real_integral(f₀, x₀ - &1, y))(y + d₀))(y) - "+
										"    (λy:real. real_integral(f₀, x₀ - &1, y))(y)"),
								x,
								a.TermAs[Real]("f₀(x₀ + d₀) - f₀(x₀)"),
								a.TermAs[Real]("real_inv(d₀)"))),
					)
					nearX := a.Have(
						"within 1 of x the average is (F(y + d) − F(y))/d",
						Statement{
							Binders: "∀y:real.",
							Hypotheses: []string{
								"|y - x₀| < &1",
							},
							Conclusion: "(λx:real. «average»(d₀, f₀, x))(y) = " +
								"(λy:real. " +
								"    real_inv(d₀) * " +
								"    (λy:real. " +
								"        (λy:real. (λy:real. real_integral(f₀, x₀ - &1, y))(y + d₀))(y) - " +
								"        (λy:real. real_integral(f₀, x₀ - &1, y))(y))(y))(y)",
						},
						Derive(func(b *Argument) {
							y := b.FixAs[Real]()
							nearY := b.Assume()
							between := b.Have(
								"y lies strictly between x − 1 and x + 1",
								"x₀ - &1 < y₀ ∧ y₀ < x₀ + &1",
								By(nearY, real_sgn_abs.AbsBetween.At(x, y, b.TermAs[Real]("&1"))),
							)
							ordered := b.Have(
								"so x − 1 ≤ y ≤ y + d ≤ x + d + 1",
								"x₀ - &1 ≤ x₀ - &1 ∧ "+
									"x₀ - &1 ≤ x₀ + d₀ + &1 ∧ "+
									"x₀ - &1 ≤ y₀ ∧ "+
									"y₀ ≤ x₀ + d₀ + &1 ∧ "+
									"x₀ - &1 ≤ y₀ + d₀ ∧ "+
									"y₀ + d₀ ≤ x₀ + d₀ + &1",
								ByArith(Raw, pos, continuous, between),
							)
							additive := b.Have(
								"F(y) + ∫ f from y to y + d is F(y + d)",
								"real_integral(f₀, x₀ - &1, y₀) + real_integral(f₀, y₀, y₀ + d₀) = "+
									"real_integral(f₀, x₀ - &1, y₀ + d₀)",
								By(
									ordered,
									onInterval,
									IntegralAdditive.At(
										f,
										b.TermAs[Real]("x₀ - &1"),
										b.TermAs[Real]("x₀ + d₀ + &1"),
										b.TermAs[Real]("x₀ - &1"),
										y,
										b.TermAs[Real]("y₀ + d₀"))),
							)
							increment := b.Have(
								"so ∫ f from y to y + d is F(y + d) − F(y)",
								"real_integral(f₀, y₀, y₀ + d₀) = "+
									"real_integral(f₀, x₀ - &1, y₀ + d₀) - real_integral(f₀, x₀ - &1, y₀)",
								ByArith(Raw, additive),
							)
							b.Show(
								"and the average at y is that increment divided by d",
								By(increment),
							)
						}),
					)
					one := a.Have(
						"the radius 1 is positive",
						"&0 < &1",
						ByArith(Raw),
					)
					a.Show(
						"the average agrees with (F(y + d) − F(y))/d near x, so it has the same derivative",
						By(
							one,
							nearX,
							scaledIncrement,
							real_derivative.DerivativeLocal.At(
								a.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"),
								a.TermAs[Fun[Real, Real]](
									"λy:real. "+
										"    real_inv(d₀) * "+
										"    (λy:real. "+
										"        (λy:real. (λy:real. real_integral(f₀, x₀ - &1, y))(y + d₀))(y) - "+
										"        (λy:real. real_integral(f₀, x₀ - &1, y))(y))(y)"),
								x,
								a.TermAs[Real]("&1"),
								a.TermAs[Real]("«difference»(d₀, f₀, x₀)"))),
					)
				})

			differenceDerivative := ctx.Lemma(Statement{
				Binders: "∀f g:(real → real). ∀d x:real.",
				Hypotheses: []string{
					"real_derivative_at(f, x, g(x))",
					"real_derivative_at(f, x + d, g(x + d))",
				},
				Conclusion: "real_derivative_at(λx:real. «difference»(d, f, x), x, «difference»(d, g, x))",
			},
				func(a *Argument, f, g *Arrow[Real, Real], d, x *Expr[Real], atX, atShift Fact) {
					shifted := a.Have(
						"y ↦ f(y + d) has derivative g(x + d) at x",
						"real_derivative_at(λy:real. f₀(y + d₀), x₀, g₀(x₀ + d₀))",
						By(atShift, At(translateDerivative, f, d, x, a.TermAs[Real]("g₀(x₀ + d₀)"))),
					)
					increment := a.Have(
						"so y ↦ f(y + d) − f(y) has derivative g(x + d) − g(x)",
						"real_derivative_at(λy:real. f₀(y + d₀) - f₀(y), x₀, g₀(x₀ + d₀) - g₀(x₀))",
						By(
							atX,
							shifted,
							real_derivative.DerivativeSub.At(
								a.TermAs[Fun[Real, Real]]("λy:real. f₀(y + d₀)"),
								f,
								x,
								a.TermAs[Real]("g₀(x₀ + d₀)"),
								a.TermAs[Real]("g₀(x₀)"))),
					)
					a.Show(
						"and divided by d, the difference quotient of g",
						By(
							increment,
							real_derivative.DerivativeScale.At(
								a.TermAs[Fun[Real, Real]]("λy:real. f₀(y + d₀) - f₀(y)"),
								x,
								a.TermAs[Real]("g₀(x₀ + d₀) - g₀(x₀)"),
								a.TermAs[Real]("real_inv(d₀)"))),
					)
				})

			inverseScale := ctx.Lemma(Statement{
				Binders: "∀d v:real.",
				Hypotheses: []string{
					"&0 < d",
				},
				Conclusion: "real_inv(d) * (v * d) = v",
			},
				func(a *Argument, d, v *Expr[Real], pos Fact) {
					inverse := a.Have(
						"d is positive, so 1/d·d = 1",
						"real_inv(d₀) * d₀ = &1",
						ByArith(pos, field.MulLeftInverse.Read(real_field.Field).At(d)),
					)
					regrouped := a.Have(
						"1/d·(v·d) = (1/d·d)·v",
						"real_inv(d₀) * (v₀ * d₀) = real_inv(d₀) * d₀ * v₀",
						ByArith(Raw),
					)
					unit := a.Have(
						"1·v = v",
						"&1 * v₀ = v₀",
						ByArith(Raw),
					)
					a.Show(
						"so 1/d·(v·d) = v",
						By(Normalized, inverse, regrouped, unit),
					)
				})

			// The average of f over [x, x + d] differs from c by the integral of f − c divided by d,
			// which the bound on |f − c| holds below B.
			averageBound := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀d x c B:real.",
				Hypotheses: []string{
					"&0 < d",
					"real_continuous_on(𝕌, f)",
					"∀y:real. x ≤ y ∧ y ≤ x + d ⇒ |f(y) - c| ≤ B",
				},
				Conclusion: "|«average»(d, f, x) - c| ≤ B",
			},
				func(a *Argument, f *Arrow[Real, Real], d, x, c, B *Expr[Real], pos, continuous, near Fact) {
					ordered := a.Have(
						"x ≤ x + d",
						"x₀ ≤ x₀ + d₀",
						ByArith(Raw, pos),
					)
					integral := a.Have(
						"f has its integral over [x, x + d]",
						"real_has_integral(f₀, x₀, x₀ + d₀, real_integral(f₀, x₀, x₀ + d₀))",
						By(ordered, continuous, At(globalHasIntegral, f, x, a.TermAs[Real]("x₀ + d₀"))),
					)
					length := a.Have(
						"the interval from x to x + d has length d",
						"x₀ + d₀ - x₀ = d₀",
						ByArith(Raw),
					)
					nearConstant := a.Have(
						"within B of c on the interval, f has its integral within B·d of c·d",
						"|real_integral(f₀, x₀, x₀ + d₀) - c₀ * d₀| ≤ B₀ * d₀",
						By(
							Normalized,
							integral,
							near,
							length,
							HasIntegralNearConstant.At(
								f, x, a.TermAs[Real]("x₀ + d₀"), a.TermAs[Real]("real_integral(f₀, x₀, x₀ + d₀)"), c, B)),
					)
					inversePos := a.Have(
						"1/d is nonnegative",
						"&0 ≤ real_inv(d₀)",
						ByArith(pos, real_order_field.InvPos.At(d)),
					)
					inverseAbs := a.Have(
						"so |1/d| = 1/d",
						"|real_inv(d₀)| = real_inv(d₀)",
						By(inversePos, real_sgn_abs.AbsFixedIffNonneg.At(a.TermAs[Real]("real_inv(d₀)"))),
					)
					scaledAbs := a.Have(
						"and |(∫ f − c·d)/d| = |∫ f − c·d|/d",
						"|real_inv(d₀) * (real_integral(f₀, x₀, x₀ + d₀) - c₀ * d₀)| = "+
							"real_inv(d₀) * |real_integral(f₀, x₀, x₀ + d₀) - c₀ * d₀|",
						By(
							inverseAbs,
							real_sgn_abs.AbsMul.At(
								a.TermAs[Real]("real_inv(d₀)"), a.TermAs[Real]("real_integral(f₀, x₀, x₀ + d₀) - c₀ * d₀"))),
					)
					scaledBound := a.Have(
						"dividing the integral bound by d",
						"real_inv(d₀) * |real_integral(f₀, x₀, x₀ + d₀) - c₀ * d₀| ≤ real_inv(d₀) * (B₀ * d₀)",
						By(
							nearConstant,
							inversePos,
							real_order_ring.LessEqMulLeft.At(
								a.TermAs[Real]("real_inv(d₀)"),
								a.TermAs[Real]("|real_integral(f₀, x₀, x₀ + d₀) - c₀ * d₀|"),
								a.TermAs[Real]("B₀ * d₀"))),
					)
					boundCancels := a.Have(
						"B·d/d = B",
						"real_inv(d₀) * (B₀ * d₀) = B₀",
						By(pos, At(inverseScale, d, B)),
					)
					centreCancels := a.Have(
						"c·d/d = c",
						"real_inv(d₀) * (c₀ * d₀) = c₀",
						By(pos, At(inverseScale, d, c)),
					)
					averageMinusCentre := a.Have(
						"(∫ f − c·d)/d is the average less c·d/d",
						"real_inv(d₀) * (real_integral(f₀, x₀, x₀ + d₀) - c₀ * d₀) = "+
							"«average»(d₀, f₀, x₀) - real_inv(d₀) * (c₀ * d₀)",
						ByArith(Raw),
					)
					a.Show(
						"so the average is within B of c",
						By(scaledAbs, scaledBound, boundCancels, centreCancels, averageMinusCentre),
					)
				})

			averageContinuous := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀d:real.",
				Hypotheses: []string{
					"&0 < d",
					"real_continuous_on(𝕌, f)",
				},
				Conclusion: "real_continuous_on(𝕌, λx:real. «average»(d, f, x))",
			},
				func(a *Argument, f *Arrow[Real, Real], d *Expr[Real], pos, continuous Fact) {
					differentiable := a.Have(
						"the average has a derivative at every point of the line",
						"∀x:real. x ∈ 𝕌 ⇒ real_derivative_at(λx:real. «average»(d₀, f₀, x), x, «difference»(d₀, f₀, x))",
						Derive(func(b *Argument) {
							x := b.FixAs[Real]()
							b.Assume()
							b.Show(
								"its derivative at x is the difference quotient of f",
								By(pos, continuous, At(averageDerivative, f, d, x)))
						}),
					)
					a.Show(
						"so the average is continuous on the line",
						By(
							differentiable,
							real_derivative.DerivativeContinuousOn.At(
								a.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"),
								a.TermAs[Fun[Real, Real]]("λx:real. «difference»(d₀, f₀, x)"),
								a.TermAs[Set[Real]]("𝕌"))),
					)
				})

			// On [x, x + d] the values of f stay within B + e of g(x): within B of g there, and g
			// moves by at most e over a distance d. The average over [x, x + d] keeps that bound.
			averageNear := ctx.Lemma(Statement{
				Binders: "∀f g:(real → real). ∀d e B:real.",
				Hypotheses: []string{
					"&0 < d",
					"real_continuous_on(𝕌, f)",
					"∀x y:real. |x - y| ≤ d ⇒ |g(x) - g(y)| ≤ e",
					"«boundedBy»(λx:real. f(x) - g(x), B)",
				},
				Conclusion: "«boundedBy»(λx:real. «average»(d, f, x) - g(x), B + e)",
			},
				func(
					a *Argument,
					f, g *Arrow[Real, Real],
					d, e, B *Expr[Real],
					pos, continuous, modulus, near Fact,
				) {
					x := a.FixAs[Real]()
					onWindow := a.Have(
						"on [x, x + d] the values of f are within B + e of g(x)",
						"∀y:real. x₀ ≤ y ∧ y ≤ x₀ + d₀ ⇒ |f₀(y) - g₀(x₀)| ≤ B₀ + e₀",
						Derive(func(b *Argument) {
							b.FixAs[Real]()
							inWindow := b.Assume()
							gap := b.Have(
								"y is within d of x",
								"|y₀ - x₀| ≤ d₀",
								ByArith(pos, inWindow, real_sgn_abs.AbsBounds.At(b.TermAs[Real]("y₀ - x₀"), d)),
							)
							gMoves := b.Have(
								"so g moves by at most e from x to y",
								"|g₀(y₀) - g₀(x₀)| ≤ e₀",
								By(modulus, gap),
							)
							fNearG := b.Have(
								"f is within B of g at y",
								"|f₀(y₀) - g₀(y₀)| ≤ B₀",
								By(near),
							)
							split := b.Have(
								"f(y) − g(x) is (f(y) − g(y)) + (g(y) − g(x))",
								"f₀(y₀) - g₀(x₀) = f₀(y₀) - g₀(y₀) + (g₀(y₀) - g₀(x₀))",
								ByArith(Raw),
							)
							triangle := b.Have(
								"so the triangle inequality splits |f(y) − g(x)|",
								"|f₀(y₀) - g₀(x₀)| ≤ |f₀(y₀) - g₀(y₀)| + |g₀(y₀) - g₀(x₀)|",
								By(
									split,
									real_sgn_abs.AbsTriangle.At(
										b.TermAs[Real]("f₀(y₀) - g₀(y₀)"), b.TermAs[Real]("g₀(y₀) - g₀(x₀)"))),
							)
							b.Show(
								"and |f(y) − g(x)| ≤ B + e",
								ByArith(Raw, triangle, fNearG, gMoves),
							)
						}),
					)
					a.Show(
						"so the average of f over [x, x + d] is within B + e of g(x)",
						By(
							pos,
							continuous,
							onWindow,
							At(averageBound, f, d, x, a.TermAs[Real]("g₀(x₀)"), a.TermAs[Real]("B₀ + e₀"))),
					)
				})

			averagePreservesBound := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀d B:real.",
				Hypotheses: []string{
					"&0 < d",
					"real_continuous_on(𝕌, f)",
					"«boundedBy»(f, B)",
				},
				Conclusion: "«boundedBy»(λx:real. «average»(d, f, x), B)",
			},
				func(a *Argument, f *Arrow[Real, Real], d, B *Expr[Real], pos, continuous, bounded Fact) {
					x := a.FixAs[Real]()
					onWindow := a.Have(
						"on [x, x + d] the values of f are within B of 0",
						"∀y:real. x₀ ≤ y ∧ y ≤ x₀ + d₀ ⇒ |f₀(y) - &0| ≤ B₀",
						By(Normalized, bounded, real_ring.SubRightZero),
					)
					averageNearZero := a.Have(
						"so the average over [x, x + d] is within B of 0",
						"|«average»(d₀, f₀, x₀) - &0| ≤ B₀",
						By(pos, continuous, onWindow, At(averageBound, f, d, x, a.TermAs[Real]("&0"), B)),
					)
					a.Show(
						"that is, bounded by B",
						By(averageNearZero, real_ring.SubRightZero.At(a.TermAs[Real]("«average»(d₀, f₀, x₀)"))),
					)
				})

			differencePreservesBound := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀d B:real.",
				Hypotheses: []string{
					"&0 < d",
					"«boundedBy»(f, B)",
				},
				Conclusion: "«boundedBy»(λx:real. «difference»(d, f, x), «incrementBound»(d, B))",
			},
				func(a *Argument, f *Arrow[Real, Real], d, B *Expr[Real], pos, bounded Fact) {
					a.FixAs[Real]()
					endpoints := a.Have(
						"f is bounded by B at x and at x + d",
						"|f₀(x₀ + d₀)| ≤ B₀ ∧ |f₀(x₀)| ≤ B₀",
						By(bounded),
					)
					increment := a.Have(
						"so its increment over [x, x + d] is at most 2B",
						"|f₀(x₀ + d₀) - f₀(x₀)| ≤ &2 * B₀",
						ByArith(
							endpoints,
							real_sgn_abs.AbsTriangleSub.At(a.TermAs[Real]("f₀(x₀ + d₀)"), a.TermAs[Real]("f₀(x₀)"))),
					)
					inversePos := a.Have(
						"1/d is nonnegative",
						"&0 ≤ real_inv(d₀)",
						ByArith(pos, real_order_field.InvPos.At(d)),
					)
					inverseAbs := a.Have(
						"so |1/d| = 1/d",
						"|real_inv(d₀)| = real_inv(d₀)",
						By(inversePos, real_sgn_abs.AbsFixedIffNonneg.At(a.TermAs[Real]("real_inv(d₀)"))),
					)
					scaledBound := a.Have(
						"dividing the increment bound by d",
						"real_inv(d₀) * |f₀(x₀ + d₀) - f₀(x₀)| ≤ «incrementBound»(d₀, B₀)",
						By(
							increment,
							inversePos,
							real_order_ring.LessEqMulLeft.At(
								a.TermAs[Real]("real_inv(d₀)"),
								a.TermAs[Real]("|f₀(x₀ + d₀) - f₀(x₀)|"),
								a.TermAs[Real]("&2 * B₀"))),
					)
					a.Show(
						"so the difference quotient at x is at most 2B/d",
						By(
							inverseAbs,
							scaledBound,
							real_sgn_abs.AbsMul.At(a.TermAs[Real]("real_inv(d₀)"), a.TermAs[Real]("f₀(x₀ + d₀) - f₀(x₀)"))),
					)
				})

			// The tower: the triple average has the difference quotient of the double average as its
			// derivative, that one the difference quotient of the difference quotient of the single
			// average, and that one the third difference quotient of f. Each step is the derivative of
			// an average (a difference quotient of what is averaged) or of a difference quotient (the
			// difference quotient of the derivative).
			towerDerivatives := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀d:real.",
				Hypotheses: []string{
					"&0 < d",
					"real_continuous_on(𝕌, f)",
				},
				Conclusion: "∀x:real. " +
					"    real_derivative_at(λx:real. «averagedThrice»(d, f, x), x, «smoothedFirst»(d, f, x)) ∧ " +
					"    real_derivative_at(λx:real. «smoothedFirst»(d, f, x), x, «smoothedSecond»(d, f, x)) ∧ " +
					"    real_derivative_at(λx:real. «smoothedSecond»(d, f, x), x, «smoothedThird»(d, f, x))",
			},
				func(a *Argument, f *Arrow[Real, Real], d *Expr[Real], pos, continuous Fact) {
					averageContinuity := a.Have(
						"the average of f is continuous",
						"real_continuous_on(𝕌, λx:real. «average»(d₀, f₀, x))",
						By(pos, continuous, At(averageContinuous, f, d)),
					)
					doubleAverageContinuity := a.Have(
						"and so is the double average",
						"real_continuous_on(𝕌, λx:real. «averagedTwice»(d₀, f₀, x))",
						By(
							pos,
							averageContinuity,
							At(averageContinuous, a.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"), d)),
					)
					averageSlope := a.Have(
						"the average has the difference quotient of f as its derivative",
						"∀t:real. "+
							"    real_derivative_at(λx:real. «average»(d₀, f₀, x), t, (λx:real. «difference»(d₀, f₀, x))(t))",
						Derive(func(b *Argument) {
							t := b.FixAs[Real]()
							b.Show(
								"by the derivative of an average at t",
								By(pos, continuous, At(averageDerivative, f, d, t)))
						}),
					)
					doubleAverageSlope := a.Have(
						"the double average has the difference quotient of the average as its derivative",
						"∀t:real. "+
							"    real_derivative_at(λx:real. «averagedTwice»(d₀, f₀, x), "+
							"        t, "+
							"        (λx:real. real_inv(d₀) * («average»(d₀, f₀, x + d₀) - «average»(d₀, f₀, x)))(t))",
						Derive(func(b *Argument) {
							t := b.FixAs[Real]()
							b.Show(
								"by the derivative of an average at t",
								By(
									pos,
									averageContinuity,
									At(averageDerivative, b.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"), d, t)))
						}),
					)
					tripleAverageSlope := a.Have(
						"the triple average has the first smoothed difference as its derivative",
						"∀t:real. "+
							"    real_derivative_at(λx:real. «averagedThrice»(d₀, f₀, x), "+
							"        t, "+
							"        (λx:real. «smoothedFirst»(d₀, f₀, x))(t))",
						Derive(func(b *Argument) {
							t := b.FixAs[Real]()
							b.Show(
								"by the derivative of an average at t",
								By(
									pos,
									doubleAverageContinuity,
									At(averageDerivative, b.TermAs[Fun[Real, Real]]("λx:real. «averagedTwice»(d₀, f₀, x)"), d, t)))
						}),
					)
					firstSmoothedSlope := a.Have(
						"the first smoothed difference has the second as its derivative",
						"∀t:real. "+
							"    real_derivative_at(λx:real. «smoothedFirst»(d₀, f₀, x), "+
							"        t, "+
							"        (λx:real. «smoothedSecond»(d₀, f₀, x))(t))",
						Derive(func(b *Argument) {
							t := b.FixAs[Real]()
							b.Show(
								"by the derivative of a difference quotient at t",
								By(
									doubleAverageSlope,
									At(
										differenceDerivative,
										b.TermAs[Fun[Real, Real]]("λx:real. «averagedTwice»(d₀, f₀, x)"),
										b.TermAs[Fun[Real, Real]](
											"λx:real. real_inv(d₀) * («average»(d₀, f₀, x + d₀) - «average»(d₀, f₀, x))"),
										d,
										t)))
						}),
					)
					averageQuotientSlope := a.Have(
						"the difference quotient of the average has that of f's difference quotient as its derivative",
						"∀t:real. "+
							"    real_derivative_at( "+
							"        λx:real. real_inv(d₀) * («average»(d₀, f₀, x + d₀) - «average»(d₀, f₀, x)), "+
							"        t, "+
							"        (λx:real. real_inv(d₀) * («difference»(d₀, f₀, x + d₀) - «difference»(d₀, f₀, x)))(t))",
						Derive(func(b *Argument) {
							t := b.FixAs[Real]()
							b.Show(
								"by the derivative of a difference quotient at t",
								By(
									averageSlope,
									At(
										differenceDerivative,
										b.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"),
										b.TermAs[Fun[Real, Real]]("λx:real. «difference»(d₀, f₀, x)"),
										d,
										t)))
						}),
					)
					secondSmoothedSlope := a.Have(
						"the second smoothed difference has the third as its derivative",
						"∀t:real. "+
							"    real_derivative_at(λx:real. «smoothedSecond»(d₀, f₀, x), "+
							"        t, "+
							"        (λx:real. «smoothedThird»(d₀, f₀, x))(t))",
						Derive(func(b *Argument) {
							t := b.FixAs[Real]()
							b.Show(
								"by the derivative of a difference quotient at t",
								By(
									averageQuotientSlope,
									At(
										differenceDerivative,
										b.TermAs[Fun[Real, Real]](
											"λx:real. real_inv(d₀) * («average»(d₀, f₀, x + d₀) - «average»(d₀, f₀, x))"),
										b.TermAs[Fun[Real, Real]](
											"λx:real. real_inv(d₀) * («difference»(d₀, f₀, x + d₀) - «difference»(d₀, f₀, x))"),
										d,
										t)))
						}),
					)
					a.Show(
						"the three steps of the tower hold at every point",
						Derive(func(b *Argument) {
							b.FixAs[Real]()
							b.Show(
								"at x, each step by its own slope",
								By(tripleAverageSlope, firstSmoothedSlope, secondSmoothedSlope),
							)
						}),
					)
				})

			// Each average moves the function by at most e, since f moves by at most e over a distance
			// d; three of them move it by at most 3e.
			averagedThriceNear := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀d e:real.",
				Hypotheses: []string{
					"&0 < d",
					"real_continuous_on(𝕌, f)",
					"∀x y:real. |x - y| ≤ d ⇒ |f(x) - f(y)| ≤ e",
				},
				Conclusion: "«boundedBy»(λx:real. «averagedThrice»(d, f, x) - f(x), &3 * e)",
			},
				func(a *Argument, f *Arrow[Real, Real], d, e *Expr[Real], pos, continuous, modulus Fact) {
					averageContinuity := a.Have(
						"the average of f is continuous",
						"real_continuous_on(𝕌, λx:real. «average»(d₀, f₀, x))",
						By(pos, continuous, At(averageContinuous, f, d)),
					)
					doubleAverageContinuity := a.Have(
						"and so is the double average",
						"real_continuous_on(𝕌, λx:real. «averagedTwice»(d₀, f₀, x))",
						By(
							pos,
							averageContinuity,
							At(averageContinuous, a.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"), d)),
					)
					itself := a.Have(
						"f is within 0 of itself",
						"«boundedBy»(λx:real. f₀(x) - f₀(x), &0)",
						By(
							Normalized,
							real_ring.SubRefl,
							real_sgn_abs.AbsOfZero,
							real_order_ring.LessEqRefl.At(a.TermAs[Real]("&0"))),
					)
					once := a.Have(
						"the average is within e of f",
						"«boundedBy»(λx:real. (λx:real. «average»(d₀, f₀, x))(x) - f₀(x), &0 + e₀)",
						By(pos, continuous, modulus, itself, At(averageNear, f, f, d, e, a.TermAs[Real]("&0"))),
					)
					twice := a.Have(
						"the double average within 2e",
						"«boundedBy»(λx:real. (λx:real. «averagedTwice»(d₀, f₀, x))(x) - f₀(x), &0 + e₀ + e₀)",
						By(
							pos,
							modulus,
							averageContinuity,
							once,
							At(
								averageNear,
								a.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"),
								f,
								d,
								e,
								a.TermAs[Real]("&0 + e₀"))),
					)
					thrice := a.Have(
						"the triple average within 3e",
						"«boundedBy»(λx:real. (λx:real. «averagedThrice»(d₀, f₀, x))(x) - f₀(x), &0 + e₀ + e₀ + e₀)",
						By(
							pos,
							modulus,
							doubleAverageContinuity,
							twice,
							At(
								averageNear,
								a.TermAs[Fun[Real, Real]]("λx:real. «averagedTwice»(d₀, f₀, x)"),
								f,
								d,
								e,
								a.TermAs[Real]("&0 + e₀ + e₀"))),
					)
					sum := a.Have(
						"0 + e + e + e = 3e",
						"&0 + e₀ + e₀ + e₀ = &3 * e₀",
						ByArith(Raw),
					)
					a.Show(
						"so the triple average is within 3e of f",
						By(thrice, sum),
					)
				})

			// The smoothed tower of f at width d is a tower of three derivatives bounded together: its
			// k-th function is a k-fold difference quotient of a (3 − k)-fold average of f. An average
			// keeps the bound B of f, and a difference quotient of a function bounded by C is bounded by
			// 2C/d, so the k-th function is bounded by (2/d)^k·B, and the sum of the four bounds bounds
			// them all.
			smoothTower := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀d B:real.",
				Hypotheses: []string{
					"&0 < d",
					"real_continuous_on(𝕌, f)",
					"«boundedBy»(f, B)",
				},
				Conclusion: "(∀k:num. ∀y:real. " +
					"    k ≤ 2 ⇒ real_derivative_at(«smoothedTower»(d, f, k), y, «smoothedTower»(d, f, k + 1, y))) ∧ " +
					"(∃B:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |«smoothedTower»(d, f, k, y)| ≤ B) ∧ " +
					"«smoothedTower»(d, f, 0) = λx:real. «averagedThrice»(d, f, x)",
			},
				func(a *Argument, f *Arrow[Real, Real], d, B *Expr[Real], pos, continuous, bounded Fact) {
					bottom := a.Have(
						"the tower starts at the triple average",
						"(λk:num. «smoothedTower»(d₀, f₀, k))(0) = λx:real. «averagedThrice»(d₀, f₀, x)",
						ByArith(Raw),
					)
					towerSteps := a.Have(
						"each function of the tower has the next as its derivative",
						"∀x:real. "+
							"    real_derivative_at(λx:real. «averagedThrice»(d₀, f₀, x), "+
							"        x, "+
							"        (λx:real. «smoothedFirst»(d₀, f₀, x))(x)) ∧ "+
							"    real_derivative_at(λx:real. «smoothedFirst»(d₀, f₀, x), "+
							"        x, "+
							"        (λx:real. «smoothedSecond»(d₀, f₀, x))(x)) ∧ "+
							"    real_derivative_at(λx:real. «smoothedSecond»(d₀, f₀, x), "+
							"        x, "+
							"        (λx:real. «smoothedThird»(d₀, f₀, x))(x))",
						By(pos, continuous, At(towerDerivatives, f, d)),
					)
					steps := a.Have(
						"so the tower at k has the tower at k + 1 as its derivative, for k ≤ 2",
						Statement{
							Binders: "∀k:num. ∀y:real.",
							Hypotheses: []string{
								"k ≤ 2",
							},
							Conclusion: "real_derivative_at((λk:num. «smoothedTower»(d₀, f₀, k))(k), " +
								"    y, " +
								"    (λk:num. «smoothedTower»(d₀, f₀, k))(k + 1, y))",
						},
						Derive(func(b *Argument) {
							b.FixAs[Nat]()
							y := b.FixAs[Real]()
							atMostTwo := b.Assume()
							kCases := b.Have(
								"k is 0, 1 or 2",
								"k₀ = 0 ∨ k₀ = 1 ∨ k₀ = 2",
								ByArith(Raw, atMostTwo),
							)
							b.Do(kCases.SplitDisj(
								LeftHolds(
									"for k = 0 or k = 1, the tower steps down by one derivative",
									Given(func(c *Argument, kAtMostOne Fact) {
										c.Do(kAtMostOne.SplitDisj(
											LeftHolds(
												"at k = 0, the triple average has the first smoothed difference as its derivative",
												Given(func(m *Argument, isZero Fact) {
													next := m.Have(
														"then k + 1 = 1",
														"k₀ + 1 = 1",
														ByArith(Raw, isZero),
													)
													m.Show(
														"the first step of the tower",
														next.Rw(),
														isZero.Rw(),
														ByArith(Raw, towerSteps.At(y)),
													)
												}),
											),
											RightHolds(
												"at k = 1, the first smoothed difference has the second as its derivative",
												Given(func(m *Argument, isOne Fact) {
													next := m.Have(
														"then k + 1 = 2",
														"k₀ + 1 = 2",
														ByArith(Raw, isOne),
													)
													m.Show(
														"the second step of the tower",
														next.Rw(),
														isOne.Rw(),
														ByArith(Raw, towerSteps.At(y)),
													)
												}),
											),
										))
									}),
								),
								RightHolds(
									"at k = 2, the second smoothed difference has the third as its derivative",
									Given(func(m *Argument, isTwo Fact) {
										next := m.Have(
											"then k + 1 = 3",
											"k₀ + 1 = 3",
											ByArith(Raw, isTwo),
										)
										m.Show(
											"the third step of the tower",
											next.Rw(),
											isTwo.Rw(),
											ByArith(Raw, towerSteps.At(y)),
										)
									}),
								),
							))
						}),
					)
					averageContinuity := a.Have(
						"the average of f is continuous",
						"real_continuous_on(𝕌, λx:real. «average»(d₀, f₀, x))",
						By(pos, continuous, At(averageContinuous, f, d)),
					)
					doubleAverageContinuity := a.Have(
						"and so is the double average",
						"real_continuous_on(𝕌, λx:real. «averagedTwice»(d₀, f₀, x))",
						By(
							pos,
							averageContinuity,
							At(averageContinuous, a.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"), d)),
					)
					averageBounded := a.Have(
						"the average keeps the bound B",
						"∀z:real. |(λx:real. «average»(d₀, f₀, x))(z)| ≤ B₀",
						By(pos, continuous, bounded, At(averagePreservesBound, f, d, B)),
					)
					doubleAverageBounded := a.Have(
						"so does the double average",
						"∀z:real. |(λx:real. «averagedTwice»(d₀, f₀, x))(z)| ≤ B₀",
						By(
							pos,
							averageContinuity,
							averageBounded,
							At(averagePreservesBound, a.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"), d, B)),
					)
					tripleAverageBounded := a.Have(
						"and the triple average, the tower at 0",
						"∀z:real. |(λx:real. «averagedThrice»(d₀, f₀, x))(z)| ≤ B₀",
						By(
							pos,
							doubleAverageContinuity,
							doubleAverageBounded,
							At(averagePreservesBound, a.TermAs[Fun[Real, Real]]("λx:real. «averagedTwice»(d₀, f₀, x)"), d, B)),
					)
					firstSmoothedBounded := a.Have(
						"the tower at 1, a difference quotient of the double average, is within 2B/d",
						"∀z:real. |(λx:real. «smoothedFirst»(d₀, f₀, x))(z)| ≤ «incrementBound»(d₀, B₀)",
						By(
							pos,
							doubleAverageBounded,
							At(
								differencePreservesBound, a.TermAs[Fun[Real, Real]]("λx:real. «averagedTwice»(d₀, f₀, x)"), d, B)),
					)
					averageQuotientBounded := a.Have(
						"a difference quotient of the average is within 2B/d",
						"∀z:real. "+
							"    |(λx:real. real_inv(d₀) * («average»(d₀, f₀, x + d₀) - «average»(d₀, f₀, x)))(z)| ≤ "+
							"    «incrementBound»(d₀, B₀)",
						By(
							pos,
							averageBounded,
							At(differencePreservesBound, a.TermAs[Fun[Real, Real]]("λx:real. «average»(d₀, f₀, x)"), d, B)),
					)
					secondSmoothedBounded := a.Have(
						"so the tower at 2, a difference quotient of that, is within (2/d)²B",
						"∀z:real. "+
							"    |(λx:real. «smoothedSecond»(d₀, f₀, x))(z)| ≤ «incrementBound»(d₀, «incrementBound»(d₀, B₀))",
						By(
							pos,
							averageQuotientBounded,
							At(
								differencePreservesBound,
								a.TermAs[Fun[Real, Real]](
									"λx:real. real_inv(d₀) * («average»(d₀, f₀, x + d₀) - «average»(d₀, f₀, x))"),
								d,
								a.TermAs[Real]("«incrementBound»(d₀, B₀)"))),
					)
					quotientBounded := a.Have(
						"a difference quotient of f is within 2B/d",
						"∀z:real. |(λx:real. «difference»(d₀, f₀, x))(z)| ≤ «incrementBound»(d₀, B₀)",
						By(pos, bounded, At(differencePreservesBound, f, d, B)),
					)
					doubleQuotientBounded := a.Have(
						"a difference quotient of that is within (2/d)²B",
						"∀z:real. "+
							"    |(λx:real. real_inv(d₀) * («difference»(d₀, f₀, x + d₀) - «difference»(d₀, f₀, x)))(z)| ≤ "+
							"    «incrementBound»(d₀, «incrementBound»(d₀, B₀))",
						By(
							pos,
							quotientBounded,
							At(
								differencePreservesBound,
								a.TermAs[Fun[Real, Real]]("λx:real. «difference»(d₀, f₀, x)"),
								d,
								a.TermAs[Real]("«incrementBound»(d₀, B₀)"))),
					)
					thirdSmoothedBounded := a.Have(
						"and the tower at 3, a difference quotient of that, is within (2/d)³B",
						"∀z:real. "+
							"    |(λx:real. «smoothedThird»(d₀, f₀, x))(z)| ≤ "+
							"    «incrementBound»(d₀, «incrementBound»(d₀, «incrementBound»(d₀, B₀)))",
						By(
							pos,
							doubleQuotientBounded,
							At(
								differencePreservesBound,
								a.TermAs[Fun[Real, Real]](
									"λx:real. real_inv(d₀) * («difference»(d₀, f₀, x + d₀) - «difference»(d₀, f₀, x))"),
								d,
								a.TermAs[Real]("«incrementBound»(d₀, «incrementBound»(d₀, B₀))"))),
					)
					atZero := a.Have(
						"f is bounded by B at 0",
						"|f₀(&0)| ≤ B₀",
						By(bounded),
					)
					boundNonneg := a.Have(
						"so B is nonnegative",
						"&0 ≤ B₀",
						ByArith(Raw, atZero, real_sgn_abs.AbsNonneg.At(a.TermAs[Real]("f₀(&0)"))),
					)
					inverseNonneg := a.Have(
						"1/d is nonnegative",
						"&0 ≤ real_inv(d₀)",
						ByArith(pos, real_order_field.InvNonneg.At(d)),
					)
					firstNonneg := a.Have(
						"so 2B/d is nonnegative",
						"&0 ≤ «incrementBound»(d₀, B₀)",
						ByArith(Raw, inverseNonneg, boundNonneg),
					)
					secondNonneg := a.Have(
						"and (2/d)²B",
						"&0 ≤ «incrementBound»(d₀, «incrementBound»(d₀, B₀))",
						ByArith(Raw, inverseNonneg, firstNonneg),
					)
					thirdNonneg := a.Have(
						"and (2/d)³B",
						"&0 ≤ «incrementBound»(d₀, «incrementBound»(d₀, «incrementBound»(d₀, B₀)))",
						ByArith(Raw, inverseNonneg, secondNonneg),
					)
					towerBound := a.Have(
						"the sum of the four bounds bounds the whole tower",
						"∃M:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |«smoothedTower»(d₀, f₀, k, y)| ≤ M",
						Witness(a.TermAs[Real](
							"B₀ + "+
								"«incrementBound»(d₀, B₀) + "+
								"«incrementBound»(d₀, «incrementBound»(d₀, B₀)) + "+
								"«incrementBound»(d₀, «incrementBound»(d₀, «incrementBound»(d₀, B₀)))")),
						Derive(func(b *Argument) {
							b.FixAs[Nat]()
							y := b.FixAs[Real]()
							atMostThree := b.Assume()
							kCases := b.Have(
								"k is 0, 1, 2 or 3",
								"k₀ = 0 ∨ k₀ = 1 ∨ k₀ = 2 ∨ k₀ = 3",
								ByArith(Raw, atMostThree),
							)
							b.Do(kCases.SplitDisj(
								LeftHolds(
									"for k ≤ 2 the tower is within the sum of the four bounds",
									Given(func(c *Argument, kAtMostTwo Fact) {
										c.Do(kAtMostTwo.SplitDisj(
											LeftHolds(
												"for k ≤ 1 the tower is within the sum of the four bounds",
												Given(func(c *Argument, kAtMostOne Fact) {
													c.Do(kAtMostOne.SplitDisj(
														LeftHolds(
															"at k = 0 the triple average is within B, the first term of the sum",
															Given(func(m *Argument, isZero Fact) {
																underSum := m.Have(
																	"B is at most the sum of the four nonnegative bounds",
																	"B₀ ≤ "+
																		"B₀ + "+
																		"«incrementBound»(d₀, B₀) + "+
																		"«incrementBound»(d₀, «incrementBound»(d₀, B₀)) + "+
																		"«incrementBound»(d₀, «incrementBound»(d₀, «incrementBound»(d₀, B₀)))",
																	ByArith(Raw, boundNonneg, firstNonneg, secondNonneg, thirdNonneg),
																)
																m.Show(
																	"so the tower at 0 is within the sum",
																	isZero.Rw(),
																	ByArith(Raw, tripleAverageBounded.At(y), underSum),
																)
															}),
														),
														RightHolds(
															"at k = 1 the first smoothed difference is within 2B/d, the second term of the sum",
															Given(func(m *Argument, isOne Fact) {
																underSum := m.Have(
																	"2B/d is at most the sum of the four nonnegative bounds",
																	"«incrementBound»(d₀, B₀) ≤ "+
																		"B₀ + "+
																		"«incrementBound»(d₀, B₀) + "+
																		"«incrementBound»(d₀, «incrementBound»(d₀, B₀)) + "+
																		"«incrementBound»(d₀, «incrementBound»(d₀, «incrementBound»(d₀, B₀)))",
																	ByArith(Raw, boundNonneg, firstNonneg, secondNonneg, thirdNonneg),
																)
																m.Show(
																	"so the tower at 1 is within the sum",
																	isOne.Rw(),
																	ByArith(Raw, firstSmoothedBounded.At(y), underSum),
																)
															}),
														),
													))
												}),
											),
											RightHolds(
												"at k = 2 the second smoothed difference is within (2/d)²B, the third term of the sum",
												Given(func(m *Argument, isTwo Fact) {
													underSum := m.Have(
														"(2/d)²B is at most the sum of the four nonnegative bounds",
														"«incrementBound»(d₀, «incrementBound»(d₀, B₀)) ≤ "+
															"B₀ + "+
															"«incrementBound»(d₀, B₀) + "+
															"«incrementBound»(d₀, «incrementBound»(d₀, B₀)) + "+
															"«incrementBound»(d₀, «incrementBound»(d₀, «incrementBound»(d₀, B₀)))",
														ByArith(Raw, boundNonneg, firstNonneg, secondNonneg, thirdNonneg),
													)
													m.Show(
														"so the tower at 2 is within the sum",
														isTwo.Rw(),
														ByArith(Raw, secondSmoothedBounded.At(y), underSum),
													)
												}),
											),
										))
									}),
								),
								RightHolds(
									"at k = 3 the third smoothed difference is within (2/d)³B, the last term of the sum",
									Given(func(m *Argument, isThree Fact) {
										underSum := m.Have(
											"(2/d)³B is at most the sum of the four nonnegative bounds",
											"«incrementBound»(d₀, «incrementBound»(d₀, «incrementBound»(d₀, B₀))) ≤ "+
												"B₀ + "+
												"«incrementBound»(d₀, B₀) + "+
												"«incrementBound»(d₀, «incrementBound»(d₀, B₀)) + "+
												"«incrementBound»(d₀, «incrementBound»(d₀, «incrementBound»(d₀, B₀)))",
											ByArith(Raw, boundNonneg, firstNonneg, secondNonneg, thirdNonneg),
										)
										m.Show(
											"so the tower at 3 is within the sum",
											isThree.Rw(),
											ByArith(Raw, thirdSmoothedBounded.At(y), underSum),
										)
									}),
								),
							))
						}),
					)
					a.Show(
						"the tower's steps, its bound and its start",
						By(steps, towerBound, bottom),
					)
				})

			// Uniform continuity gives a radius r for ε/4. Averaged three times at width r/2, f moves
			// by at most 3ε/4 < ε, and the smoothed tower at width r/2 is a tower of three bounded
			// derivatives starting at that triple average.
			return ctx.Theorem(headline,
				func(a *Argument, f *Arrow[Real, Real], B, ε *Expr[Real], uniform, bounded, pos Fact) {
					continuous := a.Have(
						"f is continuous",
						"real_continuous_on(𝕌, f₀)",
						By(uniform, real_continuous.UniformlyContinuousContinuous.At(f, a.TermAs[Set[Real]]("𝕌"))),
					)
					quarter := a.Have(
						"ε/4 is positive",
						"&0 < ε₀ / &4",
						ByArith(Raw, pos),
					)
					_, radius := a.ObtainAs[Real](
						"uniform continuity gives a radius r for ε/4",
						"∃r:real. &0 < r ∧ (∀x y:real. |x - y| < r ⇒ |f₀(x) - f₀(y)| < ε₀ / &4)",
						By(
							uniform,
							quarter,
							real_continuous.RealUniformlyContinuousOnDef.At(a.TermAs[Set[Real]]("𝕌"), f),
							set_basic.InUniv.Inst[Real]()),
					)
					halfRadius := a.Have(
						"r/2 is positive and less than r",
						"&0 < r₀ / &2 ∧ r₀ / &2 < r₀",
						ByArith(Raw, radius),
					)
					modulus := a.Have(
						"so f moves by at most ε/4 over a distance r/2",
						"∀x y:real. |x - y| ≤ r₀ / &2 ⇒ |f₀(x) - f₀(y)| ≤ ε₀ / &4",
						Derive(func(b *Argument) {
							b.FixAs[Real]()
							b.FixAs[Real]()
							closeBy := b.Assume()
							within := b.Have(
								"two points within r/2 are within r",
								"|x₀ - y₀| < r₀",
								ByArith(Raw, closeBy, halfRadius),
							)
							moved := b.Have(
								"so their values are within ε/4",
								"|f₀(x₀) - f₀(y₀)| < ε₀ / &4",
								By(within, radius),
							)
							b.Show(
								"and at most ε/4 apart",
								ByArith(Raw, moved),
							)
						}),
					)
					tower := a.Have(
						"the smoothed tower at width r/2 is a tower of three bounded derivatives",
						"(∀k:num. ∀y:real. "+
							"    k ≤ 2 ⇒ "+
							"    real_derivative_at(«smoothedTower»(r₀ / &2, f₀, k), "+
							"        y, "+
							"        «smoothedTower»(r₀ / &2, f₀, k + 1, y))) ∧ "+
							"(∃B:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |«smoothedTower»(r₀ / &2, f₀, k, y)| ≤ B) ∧ "+
							"(λk:num. «smoothedTower»(r₀ / &2, f₀, k))(0) = λx:real. «averagedThrice»(r₀ / &2, f₀, x)",
						By(bounded, halfRadius, continuous, At(smoothTower, f, a.TermAs[Real]("r₀ / &2"), B)),
					)
					tripleAverageNear := a.Have(
						"its bottom, the triple average, is within 3ε/4 of f",
						"«boundedBy»(λx:real. «averagedThrice»(r₀ / &2, f₀, x) - f₀(x), &3 * (ε₀ / &4))",
						By(
							halfRadius,
							continuous,
							modulus,
							At(averagedThriceNear, f, a.TermAs[Real]("r₀ / &2"), a.TermAs[Real]("ε₀ / &4"))),
					)
					threeQuarters := a.Have(
						"3ε/4 ≤ ε",
						"&3 * (ε₀ / &4) ≤ ε₀",
						ByArith(Raw, pos),
					)
					a.Show(
						"the smoothed tower at width r/2 approximates f within ε",
						Witness(a.TermAs[Fun2[Nat, Real, Real]]("«smoothedTower»(r₀ / &2, f₀)")),
						SplitConj(
							Case(
								"it is a tower of three bounded derivatives",
								By(tower),
							),
							Case(
								"and its bottom is within ε of f",
								Derive(func(b *Argument) {
									b.FixAs[Real]()
									near := b.Have(
										"at x the bottom of the tower is within 3ε/4 of f(x)",
										"|(λk:num. «smoothedTower»(r₀ / &2, f₀, k))(0, x₀) - f₀(x₀)| ≤ &3 * (ε₀ / &4)",
										By(tower, tripleAverageNear),
									)
									b.Show(
										"so within ε",
										ByArith(Raw, near, threeQuarters),
									)
								}),
							),
						),
					)
				})
		}),
})}
