// quarter.go — the sine and the cosine across a quarter turn: each is the
// other read backwards from π/2, so the cosine is positive on
// ⟬−π/2, π/2⟭ and nonnegative on ⟦−π/2, π/2⟧; the sine rises strictly on
// ⟦−π/2, π/2⟧ and takes there every value of ⟦−1, 1⟧; and the two agree at
// π/4.

package real_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/registry"
)

// CosSubHalfPi — the cosine of π/2 − x is the sine of x: by the
// subtraction formula, cos(π/2 − x) = cos(π/2)·cos x + sin(π/2)·sin x,
// and cos(π/2) = 0, sin(π/2) = 1.
var CosSubHalfPi = cosSubHalfPiThm{family.Add(registry.ProofEntry{
	Name: "CosSubHalfPi",
	Key:  "prop_1e4faea14a465d8e",
	Build: family.Theorem("∀x:real. cos(pi / &2 - x) = sin(x)",
		func(arg *Argument, x *Expr[Real]) {
			arg.Show(
				"cos(π/2 − x) = cos(π/2)·cos x + sin(π/2)·sin x = 0·cos x + 1·sin x",
				ByArith(CosSub.At(arg.TermAs[Real]("pi / &2"), x), PiHalfZero, SinPiHalf))
		}),
})}

// SinSubHalfPi — the sine of π/2 − x is the cosine of x: by the
// subtraction formula, sin(π/2 − x) = sin(π/2)·cos x − cos(π/2)·sin x.
var SinSubHalfPi = sinSubHalfPiThm{family.Add(registry.ProofEntry{
	Name: "SinSubHalfPi",
	Key:  "prop_13c0a4de478fd4ff",
	Build: family.Theorem("∀x:real. sin(pi / &2 - x) = cos(x)",
		func(arg *Argument, x *Expr[Real]) {
			arg.Show(
				"sin(π/2 − x) = sin(π/2)·cos x − cos(π/2)·sin x = 1·cos x − 0·sin x",
				ByArith(SinSub.At(arg.TermAs[Real]("pi / &2"), x), PiHalfZero, SinPiHalf))
		}),
})}

// CosPositiveHalfPi — the cosine is positive on ⟬−π/2, π/2⟭: there
// cos x = sin(π/2 − x), and π/2 − x lies in ⟬0, π⟭, where the sine is
// positive.
var CosPositiveHalfPi = cosPositiveHalfPiThm{family.Add(registry.ProofEntry{
	Name: "CosPositiveHalfPi",
	Key:  "prop_dcae5b29715fcaf6",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"-(pi / &2) < x",
			"x < pi / &2",
		},
		Conclusion: "&0 < cos(x)",
	},
		func(arg *Argument, x *Expr[Real], within Fact) {
			arg.Show(
				"cos x = sin(π/2 − x), and π/2 − x lies in ⟬0, π⟭, where the sine is positive",
				ByArith(within, SinSubHalfPi.At(x), SinPositivePi.At(arg.TermAs[Real]("pi / &2 - x"))))
		}),
})}

// CosNonnegHalfPi — the cosine is nonnegative on ⟦−π/2, π/2⟧: positive
// inside (CosPositiveHalfPi), and 0 at π/2 and, the cosine being even, at
// −π/2.
var CosNonnegHalfPi = cosNonnegHalfPiThm{family.Add(registry.ProofEntry{
	Name: "CosNonnegHalfPi",
	Key:  "prop_3e31ec47646d0b00",
	Build: family.Theorem(Statement{
		Binders:    "∀t:real.",
		Hypotheses: []string{"-(pi / &2) ≤ t", "t ≤ pi / &2"},
		Conclusion: "&0 ≤ cos(t)",
	}, func(a *Argument, t *Expr[Real], given Fact) {
		half := a.TermAs[Real]("pi / &2")
		a.Cases(a.TermAs[Bool]("-(pi / &2) < t ∧ t < pi / &2"))
		a.When(
			"the cosine is positive in the interior",
			func(b *Argument, strict Fact) {
				b.Show(
					"use positivity on the open half-turn",
					ByArith(strict, CosPositiveHalfPi.At(t)))
			})
		a.Otherwise(
			"the cosine vanishes at both endpoints",
			func(b *Argument, endpoint Fact) {
				b.Cases(b.TermAs[Bool]("t = pi / &2"))
				b.When(
					"the cosine of the upper endpoint is zero",
					func(c *Argument, upper Fact) {
						c.Show(
							"use the value at positive half pi",
							upper.Rw(),
							By(PiHalfZero))
					})
				b.Otherwise(
					"the cosine at the lower endpoint is the same",
					func(c *Argument, notUpper Fact) {
						lower := c.Have(
							"the remaining endpoint is negative half pi",
							"t = -(pi / &2)",
							ByArith(given, endpoint, notUpper))
						c.Show(
							"cosine is even",
							lower.Rw(),
							ByArith(CosNeg.At(half), PiHalfZero))
					})
			})
	}),
})}

// SinStrictlyIncreasingHalfPi — the sine rises strictly on
// ⟦−π/2, π/2⟧: it is continuous there, and its derivative, the cosine,
// is positive on ⟬−π/2, π/2⟭.
var SinStrictlyIncreasingHalfPi = sinStrictlyIncreasingHalfPiThm{family.Add(registry.ProofEntry{
	Name: "SinStrictlyIncreasingHalfPi",
	Key:  "prop_a1396915611d9606",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"-(pi / &2) ≤ x",
			"x < y",
			"y ≤ pi / &2",
		},
		Conclusion: "sin(x) < sin(y)",
	},
		func(arg *Argument, x, y *Expr[Real], order Fact) {
			sin, cos := arg.TermAs[Fun[Real, Real]]("real_sin"), arg.TermAs[Fun[Real, Real]]("real_cos")
			arg.Show(
				"the sine is continuous on ⟦−π/2, π/2⟧ and its derivative, "+
					"the cosine, is positive inside, so it rises strictly there",
				By(
					order,
					SinContinuousOn.At(arg.TermAs[Set[Real]]("⟦-(pi / &2), pi / &2⟧")),
					SinDerivative,
					CosPositiveHalfPi,
					real_derivative.DerivativePositiveStrictlyIncreasing.At(sin, cos,
						arg.TermAs[Real]("-(pi / &2)"), arg.TermAs[Real]("pi / &2"), x, y)))
		}),
})}

// SinSurjectiveHalfPi — the sine takes every value of ⟦−1, 1⟧ on
// ⟦−π/2, π/2⟧: it is continuous there and runs from sin(−π/2) = −1 to
// sin(π/2) = 1, so the intermediate value theorem finds each value
// between.
var SinSurjectiveHalfPi = sinSurjectiveHalfPiThm{family.Add(registry.ProofEntry{
	Name: "SinSurjectiveHalfPi",
	Key:  "prop_6152db0ea809f704",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"|y| ≤ &1",
		},
		Conclusion: "∃x:real. -(pi / &2) ≤ x ∧ x ≤ pi / &2 ∧ sin(x) = y",
	},
		func(arg *Argument, y *Expr[Real], bounded Fact) {
			sin := arg.TermAs[Fun[Real, Real]]("real_sin")
			half := arg.TermAs[Real]("pi / &2")
			bottom := arg.Have(
				"the sine is odd, so sin(−π/2) = −sin(π/2) = −1",
				"sin(-(pi / &2)) = -&1",
				ByArith(SinNeg.At(half), SinPiHalf))
			ends := arg.Have(
				"y lies between sin(−π/2) = −1 and sin(π/2) = 1",
				"-(pi / &2) ≤ pi / &2 ∧ sin(-(pi / &2)) ≤ y ∧ y ≤ sin(pi / &2)",
				ByArith(bounded, bottom, PiBounds, SinPiHalf))
			arg.Show(
				"the sine is continuous on ⟦−π/2, π/2⟧, so it takes "+
					"the value y there, by the intermediate value theorem",
				By(
					SinContinuousOn.At(arg.TermAs[Set[Real]]("⟦-(pi / &2), pi / &2⟧")),
					ends,
					real_continuous.IntermediateValue.At(sin, arg.TermAs[Real]("-(pi / &2)"), half, y)))
		}),
})}

// SinEqCosPiQuarter — the sine and the cosine agree at π/4, which is
// π/2 − π/4: sin(π/4) = cos(π/2 − π/4) = cos(π/4).
var SinEqCosPiQuarter = sinEqCosPiQuarterThm{family.Add(registry.ProofEntry{
	Name: "SinEqCosPiQuarter",
	Key:  "prop_589ba7e6cfc8f57f",
	Build: family.Theorem("sin(pi / &4) = cos(pi / &4)",
		func(arg *Argument) {
			quarter := arg.Have(
				"π/4 is π/2 less π/4",
				"pi / &2 - pi / &4 = pi / &4",
				ByArith())
			arg.Show(
				"so sin(π/4) = cos(π/2 − π/4) = cos(π/4)",
				By(quarter, CosSubHalfPi.At(arg.TermAs[Real]("pi / &4"))))
		}),
})}
