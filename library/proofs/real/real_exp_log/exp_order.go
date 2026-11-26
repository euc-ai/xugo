// exp_order.go — the order of the exponential function: a lower bound
// from its series, positivity, the bound x·exp(−x) ≤ 1, and strict
// monotonicity.

package real_exp_log

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/registry"
)

// ExpLowerBound — exp lies above its tangent line at 0 on the
// nonnegative reals. At x ≥ 0 every term xⁿ/n! of the series is
// nonnegative, so a partial sum is at most the sum exp(x), and the
// partial sum up to 1 is x⁰/0! + x¹/1! = 1 + x.
var ExpLowerBound = expLowerBoundThm{family.Add(registry.ProofEntry{
	Name: "ExpLowerBound",
	Key:  "prop_964a5703d643dd71",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "&1 + x ≤ exp(x)",
	},
		func(arg *Argument, x *Expr[Real], nonneg Fact) {
			zero, one := arg.TermAs[Nat]("0"), arg.TermAs[Nat]("1")

			terms := arg.Have(
				"every term of the series is nonnegative",
				"∀n:num. &0 ≤ real_pow(x, n) / &factorial(n)",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					positive := d.Have(
						"n! is not 0, so its image in ℝ is positive",
						"&0 < &factorial(n)",
						ByArith(
							nat_arith.FactorialNonzero.At(n),
							real_order_ring.OfNumLessThan.At(zero, d.TermAs[Nat]("factorial(n)"))))
					d.Show(
						"xⁿ is nonnegative with x, and dividing it by the positive n! keeps it so",
						ByArith(nonneg, positive, real_pow.PowNonneg.At(x, n)))
				}))

			partial := arg.BigOpAs[Nat, Real]("Σ_{k∈0 .. 1} real_pow(x, k) / &factorial(k)")
			first := arg.Have(
				"peeling the top point off the partial sum up to 1 leaves x⁰/0! + x¹/1!, which is 1 + x",
				"Σ_{k∈0 .. 1} real_pow(x, k) / &factorial(k) = &1 + x",
				ByArith(
					real_sum.PeelRight.At(one, zero, partial.Summand()),
					real_sum.IntervalPoint.At(zero, partial.Summand())))

			arg.Show(
				"exp(x) is the sum of the series, and a partial sum of a nonnegative series is at most its sum",
				first.RwRev(), // ↦ Σ_{k∈0 .. 1} xᵏ/k! ≤ exp(x)
				By(
					terms,
					ExpSums.At(x),
					real_series.SumsPartialLessEq.At(partial.Summand(), arg.TermAs[Real]("exp(x)"), one)))
		}),
})}

// ExpPositive — exp(x) is the square of exp(x/2), exp turning the sum
// x/2 + x/2 into a product, and exp(x/2) is not 0, its product with
// exp(−x/2) being exp(0) = 1. A square of a nonzero real is positive.
var ExpPositive = expPositiveThm{family.Add(registry.ProofEntry{
	Name: "ExpPositive",
	Key:  "prop_c6dd0eb242a4c07d",
	Build: family.Theorem("∀x:real. &0 < exp(x)",
		func(arg *Argument, x *Expr[Real]) {
			half := arg.TermAs[Real]("x / &2")
			halves := arg.Have(
				"x is the sum of its two halves",
				"x / &2 + x / &2 = x",
				ByArith())
			square := arg.Have(
				"so exp(x) = exp(x/2 + x/2) is the square of exp(x/2)",
				"exp(x) = exp(x / &2) * exp(x / &2)",
				By(halves, ExpAdd.At(half, half)))
			unit := arg.Have(
				"exp(x/2)·exp(−x/2) = exp(x/2 + (−x/2)) = exp(0) = 1",
				"exp(x / &2) * exp(-(x / &2)) = &1",
				By(ExpAdd.At(half, arg.TermAs[Real]("-(x / &2)")), real_ring.AddRightInv.At(half), ExpZero))
			arg.Show(
				"a product equal to 1 has no factor 0, so exp(x/2) is not 0 and its square exp(x) is positive",
				ByArith(
					square,
					unit,
					real_ring.MulEqZero.At(arg.TermAs[Real]("exp(x / &2)"), arg.TermAs[Real]("exp(-(x / &2))"))))
		}),
})}

// ExpNegMulBound — from 0 on, x·exp(−x) is at most 1: exp(x) times it
// is x, as exp(x)·exp(−x) = exp(0) = 1, and x < 1 + x ≤ exp(x); the
// positive exp(x) cancels.
var ExpNegMulBound = expNegMulBoundThm{family.Add(registry.ProofEntry{
	Name: "ExpNegMulBound",
	Key:  "prop_f5e980b7aaefd3f1",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "x * exp(-x) ≤ &1",
	},
		func(arg *Argument, x *Expr[Real], nonneg Fact) {
			unit := arg.Have(
				"exp(x)·exp(−x) = exp(x + (−x)) = exp(0) = 1",
				"exp(x) * exp(-x) = &1",
				By(ExpAdd.At(x, arg.TermAs[Real]("-x")), real_ring.AddRightInv.At(x), ExpZero))
			scaled := arg.Have(
				"so exp(x) times x·exp(−x) is x, below 1 + x ≤ exp(x)",
				"exp(x) * (x * exp(-x)) ≤ exp(x) * &1",
				ByArith(Scaled(x, unit), nonneg, ExpLowerBound.At(x)))
			arg.Show(
				"and the positive exp(x) cancels",
				ByArith(ExpPositive.At(x), scaled))
		}),
})}

// ExpLessIff — exp is strictly increasing, so the order of two values of
// exp is the order of their arguments. For u < v the functional equation
// splits exp(v) as exp(u)·exp(v − u), and the tangent line at 0 puts the
// second factor above 1, so exp(v) is the positive exp(u) scaled up.
// Conversely, exp(x) < exp(y) excludes x = y, and it excludes y < x,
// which would put exp(y) below exp(x).
var ExpLessIff = expLessIffThm{family.Add(registry.ProofEntry{
	Name: "ExpLessIff",
	Key:  "prop_ddeca1dcf0d91523",
	Build: family.Theorem("∀x y:real. exp(x) < exp(y) ⇔ x < y",
		func(arg *Argument, x, y *Expr[Real]) {
			increasing := arg.Have(
				"exp is strictly increasing",
				"∀u v:real. u < v ⇒ exp(u) < exp(v)",
				Derive(func(d *Argument) {
					u := d.FixAs[Real]()
					d.FixAs[Real]()
					uBelowV := d.Assume()
					split := d.Have(
						"exp(u)·exp(v − u) is exp(u + (v − u)), which is exp(v)",
						"exp(v) = exp(u) * exp(v - u)",
						Simp(Rev(ExpAdd), Fwd(real_ring.SubAddLeft)),
						Refl())
					above := d.Have(
						"v − u is positive, so exp(v − u) ≥ 1 + (v − u) > 1",
						"&1 < exp(v - u)",
						ByArith(uBelowV, ExpLowerBound.At(d.TermAs[Real]("v - u"))))
					d.Show(
						"so exp(v) is the positive exp(u) times a factor above 1",
						split.Rw(), // ↦ exp(u) < exp(u)·exp(v − u)
						ByArith(above, ExpPositive.At(u)))
				}))

			arg.Iff()
			arg.Backward(
				"this is the monotonicity just proved",
				func(b *Argument, xBelowY Fact) {
					b.Show(
						"read at x < y",
						By(increasing.At(x, y), xBelowY))
				})
			arg.Forward(
				"exp(x) < exp(y) leaves only x < y",
				func(b *Argument, valuesOrdered Fact) {
					b.Cases(b.Term("x = y"))
					b.When(
						"x = y is impossible",
						func(c *Argument, same Fact) {
							c.Show(
								"it would make exp(x) < exp(y) read exp(y) < exp(y)",
								same.Rw(), // ↦ y < y, with exp(y) < exp(y) resident
								ByArith(valuesOrdered))
						})
					b.Otherwise(
						"for x ≠ y it remains to exclude y < x",
						func(c *Argument, distinct Fact) {
							c.Show(
								"y < x would put exp(y) below exp(x), so by totality x < y",
								ByArith(distinct, increasing.At(y, x), valuesOrdered))
						})
				})
		}),
})}

// ExpInjective — exp takes each value once: two different arguments are
// ordered one way or the other, and exp orders their values the same
// way, so the values differ.
var ExpInjective = expInjectiveThm{family.Add(registry.ProofEntry{
	Name: "ExpInjective",
	Key:  "prop_3f97c89c26d814b4",
	Build: family.Theorem("∀x y:real. exp(x) = exp(y) ⇔ x = y",
		func(arg *Argument, x, y *Expr[Real]) {
			arg.Iff()
			arg.Forward(
				"equal values: neither argument is below the other",
				func(b *Argument, same Fact) {
					b.Show(
						"neither x < y nor y < x, for exp would order the equal values strictly",
						ByArith(same, ExpLessIff.At(x, y), ExpLessIff.At(y, x)))
				})
			arg.Backward(
				"equal arguments",
				func(b *Argument, equal Fact) {
					b.Show(
						"equal arguments have equal values",
						By(Normalized, equal))
				})
		}),
})}
