// laws.go — the algebra of real powers: their sign, the exponents 0 and
// 1, the bases 0 and 1, the exponent laws, the powers of a product and of
// a reciprocal, the natural powers and the square root. For a positive
// base every law is a law of exp and log read through x^a = exp(a·log x);
// at the base 0 the definition's values are checked case by case.

package real_rpow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// RpowExp — the power of a positive base is exp(a·log x): the
// definition's first branch, read where the sign of the base selects it.
var RpowExp = rpowExpThm{family.Add(registry.ProofEntry{
	Name: "RpowExp",
	Key:  "prop_c6de1dcd44fa02eb",
	Build: family.Theorem(Statement{
		Binders: "∀x a:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "real_rpow(x, a) = exp(a * log(x))",
	},
		func(arg *Argument, x, a *Expr[Real], _ Fact) {
			arg.Show(
				"x is positive, so the definition gives exp(a·log x)",
				Simp(Fwd(RealRpowDef)),
				Refl())
		}),
})}

// RpowPositive — a positive base has a positive power: x^a is exp(a·log x),
// and exp is positive.
var RpowPositive = rpowPositiveThm{family.Add(registry.ProofEntry{
	Name: "RpowPositive",
	Key:  "prop_e3684c26ad4ccf82",
	Build: family.Theorem(Statement{
		Binders: "∀x a:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "&0 < real_rpow(x, a)",
	},
		func(arg *Argument, x, a *Expr[Real], _ Fact) {
			arg.Show(
				"x^a is exp(a·log x) for positive x, and exp is positive",
				Simp(Fwd(RealRpowDef)),
				Cite(real_exp_log.ExpPositive))
		}),
})}

// RpowNonneg — every power is nonnegative: a positive base has a positive
// power, and at any other base the definition gives 1 or 0.
var RpowNonneg = rpowNonnegThm{family.Add(registry.ProofEntry{
	Name: "RpowNonneg",
	Key:  "prop_e61f8b68712ae4a7",
	Build: family.Theorem("∀x a:real. &0 ≤ real_rpow(x, a)",
		func(arg *Argument, x, a *Expr[Real]) {
			arg.Cases(arg.Term("&0 < x"))
			arg.When(
				"a positive base has a positive power",
				func(b *Argument, positive Fact) {
					b.Show(
						"x^a is positive",
						ByArith(positive, RpowPositive.At(x, a)))
				})
			arg.Otherwise(
				"at a base that is not positive the power is 1 or 0",
				Simp(Fwd(RealRpowDef)),
				CondRewrite(),
				ByArith())
		}),
})}

// RpowZeroExponent — anything to the power 0 is 1: exp(0·log x) = exp(0)
// for positive x, and the definition's value at the exponent 0 otherwise.
var RpowZeroExponent = rpowZeroExponentThm{family.Add(registry.ProofEntry{
	Name: "RpowZeroExponent",
	Key:  "prop_a8f21d0cd3dcb41d",
	Build: family.Theorem("∀x:real. real_rpow(x, &0) = &1",
		func(arg *Argument, x *Expr[Real]) {
			arg.Cases(arg.Term("&0 < x"))
			arg.When(
				"for positive x the power is exp(0·log x) = exp(0) = 1",
				Simp(Fwd(RealRpowDef), Fwd(real_ring.MulLeftZero), Fwd(real_exp_log.ExpZero)),
				Refl())
			arg.Otherwise(
				"at a base that is not positive the definition gives 1 at the exponent 0",
				Simp(Fwd(RealRpowDef)),
				Basic())
		}),
})}

// RpowZeroBase — 0 to a nonzero power is 0: 0 is not positive, and the
// exponent is not 0, so the definition gives 0.
var RpowZeroBase = rpowZeroBaseThm{family.Add(registry.ProofEntry{
	Name: "RpowZeroBase",
	Key:  "prop_cff714c6d037fdab",
	Build: family.Theorem(Statement{
		Binders: "∀a:real.",
		Hypotheses: []string{
			"a ≠ &0",
		},
		Conclusion: "real_rpow(&0, a) = &0",
	},
		func(arg *Argument, a *Expr[Real], _ Fact) {
			arg.Show(
				"0 is not positive and a is not 0, so the definition gives 0",
				Simp(Fwd(RealRpowDef), Fwd(real_order_ring.LessThanIrrefl)),
				Basic())
		}),
})}

// RpowEqZero — a power of a nonnegative base at a nonzero exponent is 0
// exactly when the base is: a positive base has a positive power, and 0
// to a nonzero power is 0.
var RpowEqZero = rpowEqZeroThm{family.Add(registry.ProofEntry{
	Name: "RpowEqZero",
	Key:  "prop_2d1d4c550331a292",
	Build: family.Theorem(Statement{
		Binders: "∀x a:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"a ≠ &0",
		},
		Conclusion: "real_rpow(x, a) = &0 ⇔ x = &0",
	},
		func(arg *Argument, x, a *Expr[Real], nonneg, nonzero Fact) {
			arg.Iff()
			arg.Forward(
				"a power that is 0 has a base that is not positive, and so is 0",
				func(b *Argument, vanishes Fact) {
					b.Show(
						"a positive base would have a positive power, and x is nonnegative",
						ByArith(vanishes, nonneg, RpowPositive.At(x, a)))
				})
			arg.Backward(
				"0 to a nonzero power is 0",
				func(b *Argument, zero Fact) {
					b.Show(
						"x is 0 and a is not, so x^a = 0^a = 0",
						ByArith(zero, nonzero, RpowZeroBase.At(a)))
				})
		}),
})}

// RpowOneExponent — a nonnegative x to the power 1 is x: exp(1·log x) =
// exp(log x) = x for positive x, and at x = 0 the definition gives 0.
var RpowOneExponent = rpowOneExponentThm{family.Add(registry.ProofEntry{
	Name: "RpowOneExponent",
	Key:  "prop_c54104dc659037e2",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "real_rpow(x, &1) = x",
	},
		func(arg *Argument, x *Expr[Real], nonneg Fact) {
			arg.Cases(arg.Term("&0 < x"))
			arg.When(
				"for positive x the power is exp(1·log x) = exp(log x) = x",
				Simp(Fwd(RealRpowDef), Fwd(real_construction.MulLeftId), Fwd(real_exp_log.ExpLog)),
				Refl())
			arg.Otherwise(
				"otherwise x is 0, and the definition gives 0 at the exponent 1",
				func(b *Argument, notPositive Fact) {
					b.Show(
						"0 to the power 1 is 0, which is x",
						Simp(Fwd(RealRpowDef)),
						ByArith(notPositive, nonneg))
				})
		}),
})}

// RpowOneBase — 1 to any power is 1: exp(a·log 1) = exp(a·0) = exp(0).
var RpowOneBase = rpowOneBaseThm{family.Add(registry.ProofEntry{
	Name: "RpowOneBase",
	Key:  "prop_689d767353527865",
	Build: family.Theorem("∀a:real. real_rpow(&1, a) = &1",
		func(arg *Argument, a *Expr[Real]) {
			arg.Show(
				"1 is positive, so 1^a is exp(a·log 1) = exp(a·0) = exp(0) = 1",
				Simp(
					Fwd(RealRpowDef),
					Fwd(real_order_ring.ZeroLessThanOne),
					Fwd(real_exp_log.LogOne),
					Fwd(real_ring.MulRightZero),
					Fwd(real_exp_log.ExpZero)),
				Refl())
		}),
})}

// RpowAdd — a power of a positive base turns a sum of exponents into a
// product: (a + b)·log x = a·log x + b·log x, and exp turns the sum into
// a product.
var RpowAdd = rpowAddThm{family.Add(registry.ProofEntry{
	Name: "RpowAdd",
	Key:  "prop_f11965a118a59238",
	Build: family.Theorem(Statement{
		Binders: "∀x a b:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "real_rpow(x, a + b) = real_rpow(x, a) * real_rpow(x, b)",
	},
		func(arg *Argument, x, a, b *Expr[Real], _ Fact) {
			arg.Show(
				"exp((a + b)·log x) = exp(a·log x + b·log x) = exp(a·log x)·exp(b·log x)",
				Simp(Fwd(RealRpowDef), Fwd(real_ring.RightDistrib), Fwd(real_exp_log.ExpAdd)),
				Refl())
		}),
})}

// RpowAddOne — raising the exponent of a nonnegative base by 1 multiplies
// the power by the base. For positive x, x^(a + 1) = x^a·x¹ = x^a·x; at
// x = 0 the exponent a + 1 is positive, so both sides are 0.
var RpowAddOne = rpowAddOneThm{family.Add(registry.ProofEntry{
	Name: "RpowAddOne",
	Key:  "prop_59d9de375b23f7ec",
	Build: family.Theorem(Statement{
		Binders: "∀x a:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"&0 ≤ a",
		},
		Conclusion: "real_rpow(x, a + &1) = x * real_rpow(x, a)",
	},
		func(arg *Argument, x, a *Expr[Real], nonnegX, nonnegA Fact) {
			arg.Cases(arg.Term("&0 < x"))
			arg.When(
				"for positive x, x^(a + 1) is x^a·x¹ = x^a·x",
				func(b *Argument, positive Fact) {
					b.Show(
						"a power of a positive base turns a sum of exponents into a product",
						ByArith(positive, RpowAdd.At(x, a, b.TermAs[Real]("&1")), RpowOneExponent.At(x)))
				})
			arg.Otherwise(
				"otherwise x is 0, and both sides are 0",
				func(b *Argument, notPositive Fact) {
					zero := b.Have(
						"x is 0",
						"x = &0",
						ByArith(notPositive, nonnegX))
					b.Show(
						"0 to the positive power a + 1 is 0, and so is 0·0^a",
						zero.Rw(),
						ByArith(nonnegA, RpowZeroBase.At(b.TermAs[Real]("a + &1"))))
				})
		}),
})}

// RpowNeg — a power of a positive base at −a is the reciprocal of the
// power at a: (−a)·log x = −(a·log x), and exp turns the negative into
// the reciprocal.
var RpowNeg = rpowNegThm{family.Add(registry.ProofEntry{
	Name: "RpowNeg",
	Key:  "prop_b0d858275fb699ba",
	Build: family.Theorem(Statement{
		Binders: "∀x a:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "real_rpow(x, -a) = real_inv(real_rpow(x, a))",
	},
		func(arg *Argument, x, a *Expr[Real], _ Fact) {
			arg.Show(
				"exp((−a)·log x) = exp(−(a·log x)) = 1/exp(a·log x)",
				Simp(Fwd(RealRpowDef), Fwd(real_ring.MulLeftNeg), Fwd(real_exp_log.ExpNeg)),
				Refl())
		}),
})}

// RpowInvBase — the power of the reciprocal of a nonnegative base is the
// reciprocal of the power. At a = 0 both sides are 1. For positive x the
// reciprocal is positive and log(1/x) = −log x, so (1/x)^a =
// exp(−(a·log x)) = 1/exp(a·log x); and the reciprocal of 0 is 0, so at
// x = 0 and a ≠ 0 both sides are 0.
var RpowInvBase = rpowInvBaseThm{family.Add(registry.ProofEntry{
	Name: "RpowInvBase",
	Key:  "prop_8c00e4240cbfd15c",
	Build: family.Theorem(Statement{
		Binders: "∀x a:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "real_rpow(real_inv(x), a) = real_inv(real_rpow(x, a))",
	},
		func(arg *Argument, x, a *Expr[Real], nonneg Fact) {
			arg.Unless(
				arg.Term("a = &0"),
				"at a = 0 both sides are 1",
				Given(func(c *Argument, zeroA Fact) {
					c.Show(
						"(1/x)⁰ = 1 = 1/1 = 1/x⁰",
						zeroA.Rw(),
						Simp(Fwd(RpowZeroExponent), Fwd(field.InvOne.Read(real_field.Field))),
						Refl())
				}))
			arg.Cases(arg.Term("&0 < x"))
			arg.When(
				"for positive x, 1/x is positive and (1/x)^a = exp(a·(−log x)) = exp(−(a·log x)) = 1/exp(a·log x)",
				Simp(
					Fwd(RealRpowDef),
					Fwd(real_order_field.InvPos),
					Fwd(real_exp_log.LogInv),
					Fwd(real_ring.MulRightNeg),
					Fwd(real_exp_log.ExpNeg)),
				Refl())
			arg.Otherwise(
				"otherwise x is 0, whose reciprocal is 0",
				func(b *Argument, notPositive Fact) {
					zero := b.Have(
						"x is 0",
						"x = &0",
						ByArith(notPositive, nonneg))
					b.Show(
						"(1/0)^a = 0^a = 0 = 1/0, a being nonzero",
						zero.Rw(),
						Simp(Fwd(real_construction.InvZero), Fwd(RpowZeroBase)),
						Refl())
				})
		}),
})}

// LogRpow — the logarithm of a power of a positive base is the exponent
// times the logarithm of the base: log undoes exp in log(exp(a·log x)).
var LogRpow = logRpowThm{family.Add(registry.ProofEntry{
	Name: "LogRpow",
	Key:  "prop_8ae885271ef963fe",
	Build: family.Theorem(Statement{
		Binders: "∀x a:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "log(real_rpow(x, a)) = a * log(x)",
	},
		func(arg *Argument, x, a *Expr[Real], _ Fact) {
			arg.Show(
				"log(exp(a·log x)) is a·log x",
				Simp(Fwd(RealRpowDef), Fwd(real_exp_log.LogExp)),
				Refl())
		}),
})}

// RpowNat — at a natural exponent the real power is the natural power. For
// positive x, exp(n·log x) = exp(log x)ⁿ = xⁿ; at x = 0 both are 1 for
// n = 0 and 0 after.
var RpowNat = rpowNatThm{family.Add(registry.ProofEntry{
	Name: "RpowNat",
	Key:  "prop_59dad4caa59e6891",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀n:num.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "real_rpow(x, &n) = real_pow(x, n)",
	},
		func(arg *Argument, x *Expr[Real], n *Expr[Nat], nonneg Fact) {
			arg.Cases(arg.Term("&0 < x"))
			arg.When(
				"for positive x the power is exp(n·log x) = exp(log x)ⁿ = xⁿ",
				Simp(Fwd(RealRpowDef), Fwd(real_exp_log.ExpNatMul), Fwd(real_exp_log.ExpLog)),
				Refl())
			arg.Otherwise(
				"otherwise x is 0, and both powers of 0 are 1 at n = 0 and 0 after",
				func(b *Argument, notPositive Fact) {
					zero := b.Have(
						"x is 0",
						"x = &0",
						ByArith(notPositive, nonneg))
					b.Show(
						"the definition gives 1 exactly when &n = 0, that is n = 0, as 0ⁿ does",
						zero.Rw(),
						Simp(Fwd(RealRpowDef), Fwd(real_pow.ZeroPow), Fwd(real_construction.OfNumEq)),
						Refl())
				})
		}),
})}

// RpowRpow — a power of a power of a nonnegative base is the power at the
// product of the exponents. If a or b is 0 both sides are 1. Otherwise,
// for positive x, x^a = exp(a·log x) is positive and log undoes exp, so
// (x^a)^b = exp(b·(a·log x)) = exp((a·b)·log x); and at x = 0 the
// exponents a, b and a·b are all nonzero, so both sides are 0.
var RpowRpow = rpowRpowThm{family.Add(registry.ProofEntry{
	Name: "RpowRpow",
	Key:  "prop_6312d1d3a07ec002",
	Build: family.Theorem(Statement{
		Binders: "∀x a b:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "real_rpow(real_rpow(x, a), b) = real_rpow(x, a * b)",
	},
		func(arg *Argument, x, a, b *Expr[Real], nonneg Fact) {
			nonzeroA := arg.Unless(
				arg.Term("a = &0"),
				"at a = 0 both sides are 1: x⁰ = 1, 1ᵇ = 1 and x^(0·b) = x⁰",
				Given(func(c *Argument, zeroA Fact) {
					c.Show(
						"(x⁰)ᵇ = 1ᵇ = 1 = x⁰ = x^(0·b)",
						zeroA.Rw(),
						Simp(Fwd(RpowZeroExponent), Fwd(real_ring.MulLeftZero), Fwd(RpowOneBase)),
						Refl())
				}))
			nonzeroB := arg.Unless(
				arg.Term("b = &0"),
				"at b = 0 both sides are 1: anything to the power 0 is 1, and a·0 = 0",
				Given(func(c *Argument, zeroB Fact) {
					c.Show(
						"(x^a)⁰ = 1 = x⁰ = x^(a·0)",
						zeroB.Rw(),
						Simp(Fwd(RpowZeroExponent), Fwd(real_ring.MulRightZero)),
						Refl())
				}))
			arg.Cases(arg.Term("&0 < x"))
			arg.When(
				"for positive x both sides are exp of one exponent",
				func(c *Argument, _ Fact) {
					regroup := c.Have(
						"the two exponents agree",
						"b * (a * log(x)) = a * b * log(x)",
						ByArith())
					c.Show(
						"x^a = exp(a·log x) is positive, so (x^a)^b = "+
							"exp(b·log(exp(a·log x))) = exp(b·(a·log x)) = exp((a·b)·log x)",
						Simp(Fwd(RealRpowDef), Fwd(real_exp_log.ExpPositive), Fwd(real_exp_log.LogExp)),
						By(Normalized, regroup))
				})
			arg.Otherwise(
				"otherwise x is 0, and 0 to each of the nonzero exponents b and a·b is 0",
				func(c *Argument, notPositive Fact) {
					zero := c.Have(
						"x is 0",
						"x = &0",
						ByArith(notPositive, nonneg))
					c.Have(
						"a·b is not 0, as neither a nor b is",
						"a * b ≠ &0",
						ByArith(nonzeroA, nonzeroB))
					c.Show(
						"(0^a)^b = 0^b = 0 = 0^(a·b)",
						zero.Rw(),
						Simp(Fwd(RpowZeroBase)),
						Refl())
				})
		}),
})}

// RpowMulBase — the power of a product of nonnegative reals is the product
// of the powers. At a = 0 both sides are 1, and with a base 0 both are 0;
// for positive x and y, log turns x·y into log x + log y and exp turns
// a·(log x + log y) back into the product exp(a·log x)·exp(a·log y).
var RpowMulBase = rpowMulBaseThm{family.Add(registry.ProofEntry{
	Name: "RpowMulBase",
	Key:  "prop_b480567b7cb449b",
	Build: family.Theorem(Statement{
		Binders: "∀x y a:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"&0 ≤ y",
		},
		Conclusion: "real_rpow(x * y, a) = real_rpow(x, a) * real_rpow(y, a)",
	},
		func(arg *Argument, x, y, a *Expr[Real], nonnegX, nonnegY Fact) {
			arg.Unless(
				arg.Term("a = &0"),
				"at a = 0 both sides are 1",
				Given(func(c *Argument, zeroA Fact) {
					c.Show(
						"anything to the power 0 is 1, and 1 = 1·1",
						zeroA.Rw(),
						Simp(Fwd(RpowZeroExponent), Fwd(real_construction.MulLeftId)),
						Refl())
				}))
			nonzeroX := arg.Unless(
				arg.Term("x = &0"),
				"at x = 0 both sides are 0",
				Given(func(c *Argument, zeroX Fact) {
					c.Show(
						"(0·y)^a = 0^a = 0 = 0·y^a, a being nonzero",
						zeroX.Rw(),
						Simp(Fwd(real_ring.MulLeftZero), Fwd(RpowZeroBase)),
						Refl())
				}))
			nonzeroY := arg.Unless(
				arg.Term("y = &0"),
				"at y = 0 both sides are 0",
				Given(func(c *Argument, zeroY Fact) {
					c.Show(
						"(x·0)^a = 0^a = 0 = x^a·0, a being nonzero",
						zeroY.Rw(),
						Simp(Fwd(real_ring.MulRightZero), Fwd(RpowZeroBase)),
						Refl())
				}))
			positiveX := arg.Have(
				"x is positive",
				"&0 < x",
				ByArith(nonnegX, nonzeroX))
			positiveY := arg.Have(
				"y is positive",
				"&0 < y",
				ByArith(nonnegY, nonzeroY))
			arg.Have(
				"so is x·y",
				"&0 < x * y",
				ByArith(positiveX, positiveY))
			arg.Show(
				"exp(a·log(x·y)) = exp(a·(log x + log y)) = exp(a·log x)·exp(a·log y)",
				Simp(
					Fwd(RealRpowDef),
					Fwd(real_exp_log.LogMul),
					Fwd(real_construction.LeftDistrib),
					Fwd(real_exp_log.ExpAdd)),
				Refl())
		}),
})}

// RpowSqrt — the power 1/2 of a nonnegative real is its square root. The
// power is nonnegative, and it squares back to x: (x^(1/2))² is
// (x^(1/2))^2 as a real power, which is x^(1/2·2) = x¹ = x. A nonnegative
// number whose square is x is x's root (SqrtUnique).
var RpowSqrt = rpowSqrtThm{family.Add(registry.ProofEntry{
	Name: "RpowSqrt",
	Key:  "prop_ca1a753f40674ebf",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "real_rpow(x, &1 / &2) = real_sqrt(x)",
	},
		func(arg *Argument, x *Expr[Real], nonneg Fact) {
			root := arg.TermAs[Real]("real_rpow(x, &1 / &2)")
			rootNonneg := arg.Have(
				"the power is nonnegative",
				"&0 ≤ real_rpow(x, &1 / &2)",
				Cite(RpowNonneg))
			half := arg.Have(
				"twice a half is 1",
				"&1 / &2 * &2 = &1",
				ByArith())
			square := arg.Have(
				"it squares back to x: its square is its real power 2, which is x^(1/2·2) = x¹ = x",
				"real_pow(real_rpow(x, &1 / &2), 2) = x",
				Simp(Rev(RpowNat), Fwd(RpowRpow)),
				half.Rw(),
				By(nonneg, RpowOneExponent))
			arg.Show(
				"a nonnegative number whose square is x is the square root of x",
				By(square, rootNonneg, real_sqrt.SqrtUnique.At(x, root)))
		}),
})}
