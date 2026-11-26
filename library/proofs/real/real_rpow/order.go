// order.go — the power increases in its base at a positive exponent,
// decreases strictly at a negative exponent and weakly at an exponent at
// most 0; it increases in its exponent, strictly at a base above 1 and
// weakly at a base at least 1. Exp and log preserve order, and positive
// reciprocals reverse it.

package real_rpow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// RpowLessBase — at a positive exponent the power is strictly increasing
// in a nonnegative base. For positive x, log x < log y, so a·log x <
// a·log y, and exp is increasing; at x = 0 the power is 0, below the
// positive y^a.
var RpowLessBase = rpowLessBaseThm{family.Add(registry.ProofEntry{
	Name: "RpowLessBase",
	Key:  "prop_1913d437ff6ba093",
	Build: family.Theorem(Statement{
		Binders: "∀x y a:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"x < y",
			"&0 < a",
		},
		Conclusion: "real_rpow(x, a) < real_rpow(y, a)",
	},
		func(arg *Argument, x, y, a *Expr[Real], nonneg, below, positiveA Fact) {
			positiveY := arg.Have(
				"y is positive, being above x ≥ 0",
				"&0 < y",
				ByArith(nonneg, below))
			arg.Cases(arg.Term("&0 < x"))
			arg.When(
				"for positive x, exp(a·log x) < exp(a·log y)",
				func(b *Argument, positiveX Fact) {
					b.Show(
						"log x < log y, log being increasing; a > 0 keeps it, and exp is increasing",
						Simp(Fwd(RealRpowDef)),
						ByArith(
							below,
							positiveA,
							positiveX,
							positiveY,
							real_exp_log.ExpLessIff.At(b.TermAs[Real]("a * log(x)"), b.TermAs[Real]("a * log(y)")),
							real_exp_log.LogLessIff.At(x, y)))
				})
			arg.Otherwise(
				"otherwise x is 0, and 0 to the power a is 0",
				func(b *Argument, notPositive Fact) {
					zero := b.Have(
						"x is 0",
						"x = &0",
						ByArith(notPositive, nonneg))
					b.Show(
						"0^a = 0, a being nonzero, and y^a is positive",
						ByArith(zero, positiveA, positiveY, RpowZeroBase.At(a), RpowPositive.At(y, a)))
				})
		}),
})}

// RpowLessBaseNegative — at a negative exponent the power is strictly
// decreasing in a positive base. Powers with the positive opposite
// exponent increase, and their positive reciprocals reverse the order.
var RpowLessBaseNegative = rpowLessBaseNegativeThm{family.Add(registry.ProofEntry{
	Name: "RpowLessBaseNegative",
	Key:  "prop_85160f5c051c2420",
	Build: family.Theorem(Statement{
		Binders: "∀x y a:real.",
		Hypotheses: []string{
			"&0 < x",
			"x < y",
			"a < &0",
		},
		Conclusion: "real_rpow(y, a) < real_rpow(x, a)",
	},
		func(arg *Argument, x, y, a *Expr[Real], conditions Fact) {
			reciprocals := arg.Have(
				"the negative power is the reciprocal of the power with the positive opposite exponent",
				"∀t:real. &0 < t ⇒ real_rpow(t, a) = real_inv(real_rpow(t, -a))",
				Derive(func(b *Argument) {
					b.FixAs[Real]("t")
					b.Assume()
					b.Show(
						"the negative-power law and double negation give the reciprocal representation",
						Simp(Rev(RpowNeg), Fwd(real_ring.NegNeg)),
						Refl())
				}))
			opposite := arg.TermAs[Real]("-a")
			increasing := arg.Have(
				"the positive opposite-exponent powers are positive and increase between the bases",
				"&0 < real_rpow(x, -a) ∧ real_rpow(x, -a) < real_rpow(y, -a)",
				ByArith(conditions, RpowPositive.At(x, opposite), RpowLessBase.At(x, y, opposite)))
			arg.Show(
				"taking positive reciprocals reverses the comparison of the opposite-exponent powers",
				ByArith(
					conditions,
					increasing,
					reciprocals.At(x),
					reciprocals.At(y),
					real_order_field.InvAntitone.At(
						arg.TermAs[Real]("real_rpow(x, -a)"),
						arg.TermAs[Real]("real_rpow(y, -a)"))))
		}),
})}

// RpowLessEqBaseNonpos — at an exponent at most 0 the power is decreasing
// in a positive base: log x ≤ log y, multiplying by a ≤ 0 reverses the
// comparison, and exp is increasing.
var RpowLessEqBaseNonpos = rpowLessEqBaseNonposThm{family.Add(registry.ProofEntry{
	Name: "RpowLessEqBaseNonpos",
	Key:  "prop_484287439848f196",
	Build: family.Theorem(Statement{
		Binders: "∀x y a:real.",
		Hypotheses: []string{
			"&0 < x",
			"x ≤ y",
			"a ≤ &0",
		},
		Conclusion: "real_rpow(y, a) ≤ real_rpow(x, a)",
	},
		func(arg *Argument, x, y, a *Expr[Real], positive, ordered, nonpositive Fact) {
			positiveY := arg.Have(
				"y is positive, being at least x",
				"&0 < y",
				ByArith(positive, ordered))
			scaled := arg.Have(
				"log x ≤ log y, log being increasing, and multiplying by a ≤ 0 reverses the comparison",
				"a * log(y) ≤ a * log(x)",
				ByArith(positive, ordered, nonpositive, positiveY, real_exp_log.LogLessIff.At(y, x)))
			arg.Show(
				"exp is increasing",
				Simp(Fwd(RealRpowDef)),
				ByArith(
					scaled,
					real_exp_log.ExpLessIff.At(arg.TermAs[Real]("a * log(x)"), arg.TermAs[Real]("a * log(y)"))))
		}),
})}

// RpowLessExponent — at a base above 1 the power is strictly increasing in
// the exponent: log x > log 1 = 0, so a·log x < b·log x, and exp is
// increasing.
var RpowLessExponent = rpowLessExponentThm{family.Add(registry.ProofEntry{
	Name: "RpowLessExponent",
	Key:  "prop_4339bfe0313075c2",
	Build: family.Theorem(Statement{
		Binders: "∀x a b:real.",
		Hypotheses: []string{
			"&1 < x",
			"a < b",
		},
		Conclusion: "real_rpow(x, a) < real_rpow(x, b)",
	},
		func(arg *Argument, x, a, b *Expr[Real], aboveOne, below Fact) {
			positive := arg.Have(
				"x is positive",
				"&0 < x",
				ByArith(aboveOne))
			logPositive := arg.Have(
				"log x > log 1 = 0, log being increasing",
				"&0 < log(x)",
				By(positive, aboveOne, real_exp_log.LogLessIff.At(arg.TermAs[Real]("&1"), x), real_exp_log.LogOne))
			arg.Show(
				"a·log x < b·log x, log x being positive, and exp is increasing",
				Simp(Fwd(RealRpowDef)),
				ByArith(
					below,
					logPositive,
					real_exp_log.ExpLessIff.At(arg.TermAs[Real]("a * log(x)"), arg.TermAs[Real]("b * log(x)"))))
		}),
})}

// RpowLessEqExponent — at a base at least 1 the power is increasing in
// the exponent: log x ≥ 0, so a·log x ≤ b·log x, and exp is increasing.
var RpowLessEqExponent = rpowLessEqExponentThm{family.Add(registry.ProofEntry{
	Name: "RpowLessEqExponent",
	Key:  "prop_c3cca3c4570b64f9",
	Build: family.Theorem(Statement{
		Binders: "∀x a b:real.",
		Hypotheses: []string{
			"&1 ≤ x",
			"a ≤ b",
		},
		Conclusion: "real_rpow(x, a) ≤ real_rpow(x, b)",
	},
		func(arg *Argument, x, a, b *Expr[Real], atLeastOne, below Fact) {
			arg.Have(
				"x is positive",
				"&0 < x",
				ByArith(atLeastOne))
			arg.Show(
				"a·log x ≤ b·log x, log x being nonnegative, and exp is increasing",
				Simp(Fwd(RealRpowDef)),
				ByArith(
					below,
					atLeastOne,
					real_exp_log.LogNonneg.At(x),
					real_exp_log.ExpLessIff.At(arg.TermAs[Real]("b * log(x)"), arg.TermAs[Real]("a * log(x)"))))
		}),
})}
