// derivative.go — the derivatives of the power, in its base and in its
// exponent. Both are the chain rule through exp: near a positive base the
// power is y ↦ exp(a·log y), and at a fixed positive base it is
// b ↦ exp(b·log x). The power at a linear exponent, t ↦ x^(−δt), has an
// exponential primitive, which integrates it over ⟦0, 1⟧.

package real_rpow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// RpowDerivativeBase — at a positive x the power y ↦ y^a has derivative
// a·x^(a−1).
//
// On the ball of radius x about x every point is positive, so there the
// power is y ↦ exp(a·log y), and a derivative sees only a ball
// (DerivativeLocal). By the chain rule that function has derivative
// exp(a·log x)·(a/x) = x^a·a/x, and x^a = x^(a−1)·x turns it into a·x^(a−1).
var RpowDerivativeBase = rpowDerivativeBaseThm{family.Add(registry.ProofEntry{
	Name: "RpowDerivativeBase",
	Key:  "prop_860d9d14e69799b",
	Build: family.Theorem(Statement{
		Binders: "∀x a:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "real_derivative_at(λy:real. real_rpow(y, a), x, a * real_rpow(x, a - &1))",
		Abbrev: Abbrev{
			{Name: "slope", Text: "exp(a * log(x)) * (a * real_inv(x))"},
		},
	},
		func(arg *Argument, x, a *Expr[Real], positive Fact) {
			aLogX := arg.TermAs[Real]("a * log(x)")
			scaledInverse := arg.TermAs[Real]("a * real_inv(x)")
			inner := arg.Have(
				"y ↦ a·log y has derivative a/x at x",
				"real_derivative_at(λy:real. a * log(y), x, a * real_inv(x))",
				By(
					positive,
					real_exp_log.LogDerivative.At(x),
					real_derivative.DerivativeScale.At(
						arg.TermAs[Fun[Real, Real]]("real_log"),
						x,
						arg.TermAs[Real]("real_inv(x)"),
						a)))
			chain := arg.Have(
				"so by the chain rule y ↦ exp(a·log y) has derivative exp(a·log x)·(a/x) at x",
				"real_derivative_at(λy:real. exp(a * log(y)), x, «slope»)",
				By(
					inner,
					real_exp_log.ExpDerivative.At(aLogX),
					real_derivative.DerivativeChain.At(
						arg.TermAs[Fun[Real, Real]]("real_exp"),
						arg.TermAs[Fun[Real, Real]]("λy:real. a * log(y)"),
						x,
						arg.TermAs[Real]("exp(a * log(x))"),
						scaledInverse),
					functions.ComposeApply))
			agree := arg.Have(
				"on the ball of radius x about x every point is positive, so there the power is y ↦ exp(a·log y)",
				"∀y:real. |y - x| < x ⇒ real_rpow(y, a) = exp(a * log(y))",
				Derive(func(b *Argument) {
					y := b.FixAs[Real]()
					near := b.Assume()
					positiveY := b.Have(
						"y is positive",
						"&0 < y",
						ByArith(near))
					b.Show(
						"so y^a is exp(a·log y)",
						By(positiveY, RpowExp.At(y, a)))
				}))
			local := arg.Have(
				"a derivative sees only a ball, so the power has that derivative at x too",
				"real_derivative_at(λy:real. real_rpow(y, a), x, «slope»)",
				By(
					positive,
					agree,
					chain,
					real_derivative.DerivativeLocal.At(
						arg.TermAs[Fun[Real, Real]]("λy:real. real_rpow(y, a)"),
						arg.TermAs[Fun[Real, Real]]("λy:real. exp(a * log(y))"),
						x,
						x,
						arg.TermAs[Real]("«slope»"))))
			exponent := arg.Have(
				"a − 1 + 1 = a",
				"a - &1 + &1 = a",
				ByArith())
			split := arg.Have(
				"x^a = x^(a−1)·x¹ = x^(a−1)·x",
				"real_rpow(x, a) = real_rpow(x, a - &1) * x",
				ByArith(
					exponent,
					positive,
					RpowAdd.At(x, arg.TermAs[Real]("a - &1"), arg.TermAs[Real]("&1")),
					RpowOneExponent.At(x)))
			value := arg.Have(
				"exp(a·log x)·(a/x) = x^a·(a/x) = x^(a−1)·x·(a/x) = a·x^(a−1)",
				"«slope» = a * real_rpow(x, a - &1)",
				ByArith(Scaled(scaledInverse, split), positive, Scaled(scaledInverse, RpowExp.At(x, a))))
			arg.Show(
				"the derivative exp(a·log x)·(a/x) is a·x^(a−1)",
				value.RwRev(),
				By(local))
		}),
})}

// RpowDerivativeExponent — at a positive base x the power b ↦ x^b has
// derivative x^a·log x at a: it is b ↦ exp(b·log x), whose inner function
// b ↦ b·log x has derivative log x, and exp is its own derivative.
var RpowDerivativeExponent = rpowDerivativeExponentThm{family.Add(registry.ProofEntry{
	Name: "RpowDerivativeExponent",
	Key:  "prop_3268ee33cf0f824a",
	Build: family.Theorem(Statement{
		Binders: "∀x a:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "real_derivative_at(λb:real. real_rpow(x, b), a, real_rpow(x, a) * log(x))",
	},
		func(arg *Argument, x, a *Expr[Real], _ Fact) {
			logX := arg.TermAs[Real]("log(x)")
			inner := arg.Have(
				"b ↦ b·log x has derivative 1·log x + a·0 = log x at a, by the product rule",
				"real_derivative_at(λb:real. b * log(x), a, log(x))",
				ByArith(
					real_derivative.DerivativeId.At(a),
					real_derivative.DerivativeConst.At(logX, a),
					real_derivative.DerivativeMul.At(
						arg.TermAs[Fun[Real, Real]]("λb:real. b"),
						arg.TermAs[Fun[Real, Real]]("λb:real. log(x)"),
						a,
						arg.TermAs[Real]("&1"),
						arg.TermAs[Real]("&0"))))
			arg.Show(
				"x^b is exp(b·log x) at every b, and by the chain rule its derivative at a is exp(a·log x)·log x",
				Simp(Fwd(RealRpowDef)),
				By(
					inner,
					real_exp_log.ExpDerivative.At(arg.TermAs[Real]("a * log(x)")),
					real_derivative.DerivativeChain.At(
						arg.TermAs[Fun[Real, Real]]("real_exp"),
						arg.TermAs[Fun[Real, Real]]("λb:real. b * log(x)"),
						a,
						arg.TermAs[Real]("exp(a * log(x))"),
						logX),
					functions.ComposeApply))
		}),
})}

// RpowExponentIntegral — at a base x > 1, M·δ·x^(−δt) integrates over
// ⟦0, 1⟧ to M(1 − x^(−δ))/log x: x^(−δt) is exp(−δ·log x·t), and
// −(M/log x)·exp(−δ·log x·t) is a primitive, so Newton–Leibniz gives the
// change of the primitive between the ends.
var RpowExponentIntegral = rpowExponentIntegralThm{family.Add(registry.ProofEntry{
	Name: "RpowExponentIntegral",
	Key:  "prop_41b93c28e4bcd2d8",
	Build: family.Theorem(Statement{
		Binders:    "∀x δ M:real.",
		Hypotheses: []string{"&1 < x"},
		Conclusion: "real_has_integral(λt:real. M * δ * real_rpow(x, -δ * t), " +
			"    &0, " +
			"    &1, " +
			"    M * (&1 - real_rpow(x, -δ)) / log(x))",
		Abbrev: Abbrev{
			{Name: "rate", Text: "-δ * log(x)"},
			{Name: "profile", Text: "λt:real. exp(«rate» * t)"},
		},
	}, func(a *Argument, x, δ, M *Expr[Real], given Fact) {
		one := a.TermAs[Real]("&1")
		zero := a.TermAs[Real]("&0")
		k := a.TermAs[Real]("«rate»")
		unit := a.TermAs[Set[Real]]("⟦&0, &1⟧")
		id := a.TermAs[Fun[Real, Real]]("λt:real. t")
		exp := a.TermAs[Fun[Real, Real]]("real_exp")
		linear := a.TermAs[Fun[Real, Real]]("λt:real. «rate» * t")
		power := a.TermAs[Fun[Real, Real]]("«profile»")
		majorant := a.TermAs[Fun[Real, Real]]("λt:real. M * δ * «profile»(t)")
		primitive := a.TermAs[Fun[Real, Real]]("λt:real. -(M / log(x)) * «profile»(t)")
		scaleDerivative := a.Have(
			"the derivative of a multiple of the exponential profile",
			"∀c t:real. real_derivative_at(λu:real. c * «profile»(u), t, c * («profile»(t) * «rate»))",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				t := b.FixAs[Real]("t")
				kt := b.TermAs[Real]("«rate» * t")
				slope := b.TermAs[Real]("«profile»(t) * «rate»")
				inner := b.Have(
					"the linear argument has constant derivative",
					"real_derivative_at(λu:real. «rate» * u, t, «rate»)",
					ByArith(real_derivative.DerivativeId.At(t), real_derivative.DerivativeScale.At(id, t, one, k)))
				composed := b.Have(
					"the exponential differentiates by the chain rule",
					"real_derivative_at(real_exp ∘ (λu:real. «rate» * u), t, «profile»(t) * «rate»)",
					By(
						inner,
						real_exp_log.ExpDerivative.At(kt),
						real_derivative.DerivativeChain.At(exp, linear, t, b.TermAs[Real]("«profile»(t)"), k)))
				b.Show(
					"scale the profile derivative",
					By(
						b.Simplified(composed, Fwd(functions.ComposeApply)),
						real_derivative.DerivativeScale.At(power, t, slope, c)))
			}))
		logPos := a.Have(
			"the logarithm of a base above one is positive",
			"&0 < log(x)",
			ByArith(given, real_exp_log.LogOne, real_exp_log.LogLessIff.At(one, x)))
		derivative := a.Have(
			"the specified primitive differentiates to the majorant",
			"∀t:real. real_derivative_at(λu:real. -(M / log(x)) * «profile»(u), t, M * δ * «profile»(t))",
			Derive(func(b *Argument) {
				t := b.FixAs[Real]("t")
				b.Show(
					"cancel the nonzero logarithm in the derivative",
					ByArith(logPos, scaleDerivative.At(b.TermAs[Real]("-(M / log(x))"), t)))
			}))
		fContinuous := a.Have(
			"the differentiable majorant is continuous on the unit interval",
			"real_continuous_on(⟦&0, &1⟧, λt:real. M * δ * «profile»(t))",
			By(
				scaleDerivative,
				real_derivative.DerivativeContinuousOn.At(majorant,
					a.TermAs[Fun[Real, Real]]("λt:real. M * δ * («profile»(t) * «rate»)"), unit)))
		primitiveContinuous := a.Have(
			"the primitive is continuous on the unit interval",
			"real_continuous_on(⟦&0, &1⟧, λt:real. -(M / log(x)) * «profile»(t))",
			By(derivative, real_derivative.DerivativeContinuousOn.At(primitive, majorant, unit)))
		integral := a.Have(
			"Newton–Leibniz gives the change of the primitive",
			"real_has_integral(λt:real. M * δ * «profile»(t), "+
				"    &0, "+
				"    &1, "+
				"    -(M / log(x)) * «profile»(&1) - -(M / log(x)) * «profile»(&0))",
			By(
				fContinuous,
				primitiveContinuous,
				derivative,
				real_integral.NewtonLeibnizContinuous.At(primitive, majorant, zero, one)))
		basePos := a.Have(
			"the base is positive",
			"&0 < x",
			ByArith(given))
		forms := a.Have(
			"the exponential profile is the real power at the linear exponent",
			"(λt:real. M * δ * «profile»(t)) = (λt:real. M * δ * real_rpow(x, -δ * t))",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[Real]("t")
				exponent := b.Have(
					"put the variable at the end of the exponent product",
					"(-δ * t) * log(x) = «rate» * t",
					ByArith())
				powerForm := b.Have(
					"expand the power at the positive base",
					"real_rpow(x, -δ * t) = exp((-δ * t) * log(x))",
					By(basePos, RpowExp.At(x, b.TermAs[Real]("-δ * t"))))
				b.Show(
					"the two forms of the profile are equal",
					Simp(Fwd(powerForm), Fwd(exponent)),
					Basic())
			}))
		value := a.Have(
			"evaluate the primitive at both ends",
			"-(M / log(x)) * «profile»(&1) - -(M / log(x)) * «profile»(&0) = "+
				"M * (&1 - real_rpow(x, -δ)) / log(x)",
			ByArith(given, logPos, real_exp_log.ExpZero, RpowExp.At(x, a.TermAs[Real]("-δ"))))
		a.Show(
			"read the integral in power form",
			By(forms, value, integral))
	}),
})}
