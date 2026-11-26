// addition.go — the addition formulas, from the Cauchy product and the
// binomial theorem divided by N! (real_exp_log's ExpProductTerm) split by
// the parity of its index; the circle identity and the bounds it gives.
//
// A sum over `0 .. n` read through real_sum.IntervalCongruence carries
// its guard `0 ≤ k ∧ k ≤ n`; the first half is that law's lower bound
// at 0.

package real_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// SinProductTerm — the sine series' term at x + y, as the two Cauchy
// products cos·sin and sin·cos. The binomial theorem at the odd power
// 2n + 1, divided by (2n + 1)!, is a sum over 0 .. 2n + 1; split by the
// parity of its index, its even-indexed terms are those of the first
// product and its odd-indexed ones those of the second, each times the
// sign (−1)ⁿ that the signs of the two factors multiply to.
var SinProductTerm = sinProductTermThm{family.Add(registry.ProofEntry{
	Name: "SinProductTerm",
	Key:  "prop_785ae920c00a2f35",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real. ∀n:num.",
		Conclusion: "Σ_{k∈0 .. n} real_pow(-&1, k) * " +
			"real_pow(x, 2 * k) / " +
			"&factorial(2 * k) * " +
			"(real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1)) + " +
			"(Σ_{k∈0 .. n} real_pow(-&1, k) * " +
			"    real_pow(x, 2 * k + 1) / " +
			"    &factorial(2 * k + 1) * " +
			"    (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k)) / &factorial(2 * (n - k)))) = " +
			"real_pow(-&1, n) * real_pow(x + y, 2 * n + 1) / &factorial(2 * n + 1)",
		Abbrev: Abbrev{
			{Name: "evenTerm", Text: "real_pow(x, 2 * k) / " +
				"&factorial(2 * k) * " +
				"(real_pow(y, 2 * n + 1 - 2 * k) / &factorial(2 * n + 1 - 2 * k))"},
			{Name: "oddTerm", Text: "real_pow(x, 2 * k + 1) / " +
				"&factorial(2 * k + 1) * " +
				"(real_pow(y, 2 * n + 1 - (2 * k + 1)) / &factorial(2 * n + 1 - (2 * k + 1)))"},
		},
	},
		func(arg *Argument, x, y *Expr[Real], n *Expr[Nat]) {
			// The k-th terms of the two Cauchy products, as in SinAdd; and
			// the binomial term xʲ/j!·y²ⁿ⁺¹⁻ʲ/(2n + 1 − j)! at the even point
			// j = 2k and at the odd point j = 2k + 1.
			const (
				cosSinTerm = "real_pow(-&1, k) * real_pow(x, 2 * k) / &factorial(2 * k) * " +
					"(real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1))"
				sinCosTerm = "real_pow(-&1, k) * real_pow(x, 2 * k + 1) / &factorial(2 * k + " +
					"1) * (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k)) / &factorial(2 * (n - k)))"
				evenTerm = "real_pow(x, 2 * k) / &factorial(2 * k) * " +
					"(real_pow(y, 2 * n + 1 - 2 * k) / &factorial(2 * n + 1 - 2 * k))"
				oddTerm = "real_pow(x, 2 * k + 1) / &factorial(2 * k + 1) * (real_pow(y, " +
					"2 * n + 1 - (2 * k + 1)) / &factorial(2 * n + 1 - (2 * k + 1)))"
			)

			signs := arg.Have(
				"the signs of the two factors multiply to (−1)ⁿ",
				"∀k:num. k ≤ n ⇒ real_pow(-&1, k) * real_pow(-&1, n - k) = real_pow(-&1, n)",
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					below := d.Assume()
					exponents := d.Have(
						"the two exponents add up to n",
						"k + (n - k) = n",
						ByArith(below))
					d.Show(
						"so the product is −1 to the power k + (n − k), by the law of exponents",
						By(exponents, real_pow.PowAdd.At(d.TermAs[Real]("-&1"), k, d.TermAs[Nat]("n - k"))))
				}))

			even := arg.Have(
				"the first product's k-th term is (−1)ⁿ times the binomial term at 2k",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"0 ≤ k",
						"k ≤ n",
					},
					Conclusion: "real_pow(-&1, k) * " +
						"real_pow(x, 2 * k) / " +
						"&factorial(2 * k) * " +
						"(real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1)) = " +
						"real_pow(-&1, n) * " +
						"(real_pow(x, 2 * k) / " +
						"    &factorial(2 * k) * " +
						"    (real_pow(y, 2 * n + 1 - 2 * k) / &factorial(2 * n + 1 - 2 * k)))",
				},
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					inRange := d.Assume()
					exponent := d.Have(
						"y's exponent 2(n − k) + 1 is 2n + 1 − 2k, as k ≤ n",
						"2 * (n - k) + 1 = 2 * n + 1 - 2 * k",
						ByArith(inRange))
					d.Show(
						"gather the two signs, which multiply to (−1)ⁿ",
						CalcEq(
							Leg(
								d.TermAs[Real]("real_pow(-&1, k) * real_pow(-&1, n - k) * («evenTerm»)"),
								"the signs apart from the powers, y's exponent written 2n + 1 − 2k",
								exponent.Rw(),
								ByArith()),
							FinalLeg(
								"(−1)ᵏ·(−1)ⁿ⁻ᵏ = (−1)ⁿ, as k ≤ n",
								By(signs.At(k), inRange))))
				}))
			odd := arg.Have(
				"and the second product's k-th term is (−1)ⁿ times the binomial term at 2k + 1",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"0 ≤ k",
						"k ≤ n",
					},
					Conclusion: "real_pow(-&1, k) * " +
						"real_pow(x, 2 * k + 1) / " +
						"&factorial(2 * k + 1) * " +
						"(real_pow(-&1, n - k) * real_pow(y, 2 * (n - k)) / &factorial(2 * (n - k))) = " +
						"real_pow(-&1, n) * " +
						"(real_pow(x, 2 * k + 1) / " +
						"    &factorial(2 * k + 1) * " +
						"    (real_pow(y, 2 * n + 1 - (2 * k + 1)) / &factorial(2 * n + 1 - (2 * k + 1))))",
				},
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					inRange := d.Assume()
					exponent := d.Have(
						"y's exponent 2(n − k) is 2n + 1 − (2k + 1)",
						"2 * (n - k) = 2 * n + 1 - (2 * k + 1)",
						ByArith(inRange))
					d.Show(
						"gather the two signs, which multiply to (−1)ⁿ",
						CalcEq(
							Leg(
								d.TermAs[Real]("real_pow(-&1, k) * real_pow(-&1, n - k) * («oddTerm»)"),
								"the signs apart from the powers, y's exponent written 2n + 1 − (2k + 1)",
								exponent.Rw(),
								ByArith()),
							FinalLeg(
								"(−1)ᵏ·(−1)ⁿ⁻ᵏ = (−1)ⁿ, as k ≤ n",
								By(signs.At(k), inRange))))
				}))

			evenSum := arg.Have(
				"so, term by term, the first sum is the sum of those multiples at the even points",
				"Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"real_pow(x, 2 * k) / "+
					"&factorial(2 * k) * "+
					"(real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1)) = "+
					"Σ_{k∈0 .. n} real_pow(-&1, n) * "+
					"(real_pow(x, 2 * k) / "+
					"    &factorial(2 * k) * "+
					"    (real_pow(y, 2 * n + 1 - 2 * k) / &factorial(2 * n + 1 - 2 * k)))",
				By(even, real_sum.IntervalCongruence))
			oddSum := arg.Have(
				"and the second the sum of those at the odd points",
				"Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"real_pow(x, 2 * k + 1) / "+
					"&factorial(2 * k + 1) * "+
					"(real_pow(-&1, n - k) * real_pow(y, 2 * (n - k)) / &factorial(2 * (n - k))) = "+
					"Σ_{k∈0 .. n} real_pow(-&1, n) * "+
					"(real_pow(x, 2 * k + 1) / "+
					"    &factorial(2 * k + 1) * "+
					"    (real_pow(y, 2 * n + 1 - (2 * k + 1)) / &factorial(2 * n + 1 - (2 * k + 1))))",
				By(odd, real_sum.IntervalCongruence))

			arg.Show(
				"the two sums are (−1)ⁿ times the binomial theorem "+
					"at 2n + 1, divided by (2n + 1)! and split by parity",
				evenSum.Rw(),
				oddSum.Rw(),
				CalcEq(
					Leg(
						arg.TermAs[Real](
							"real_pow(-&1, n) * "+
								"Σ_{j∈0 .. 2 * n + 1} real_pow(x, j) / "+
								"&factorial(j) * "+
								"(real_pow(y, 2 * n + 1 - j) / &factorial(2 * n + 1 - j))"),
						"(−1)ⁿ comes out of both sums, which are the even- "+
							"and the odd-indexed halves of one sum over 0 .. 2n + 1",
						Simp(Fwd(real_sum.IntervalEvenOdd), Rev(real_sum.ScalarLeft.Inst[Nat]())),
						ByArith()),
					FinalLeg(
						"and that sum is (x + y)²ⁿ⁺¹/(2n + 1)! by the binomial theorem divided by (2n + 1)!",
						Simp(Fwd(real_exp_log.ExpProductTerm)),
						ByArith())))
		}),
})}

// SinAdd — the addition formula for the sine. The cosine and the sine
// series converge absolutely, so the Cauchy product of the cosine series
// at x with the sine series at y sums to cos x·sin y, and that of the
// sine series at x with the cosine series at y to sin x·cos y. Added term
// by term, the two products are the sine series at x + y, which sums to
// sin(x + y), and a series has only one sum.
var SinAdd = sinAddThm{family.Add(registry.ProofEntry{
	Name: "SinAdd",
	Key:  "prop_39091c66afa4f4da",
	Build: family.Theorem(Statement{
		Binders:    "∀x y:real.",
		Conclusion: "sin(x + y) = sin(x) * cos(y) + cos(x) * sin(y)",
	},
		func(arg *Argument, x, y *Expr[Real]) {
			// The k-th terms of the two Cauchy products at n: the cosine
			// series at x against the sine series at y, and the sine series
			// at x against the cosine series at y.
			const (
				cosSinTerm = "real_pow(-&1, k) * real_pow(x, 2 * k) / &factorial(2 * k) * " +
					"(real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1))"
				sinCosTerm = "real_pow(-&1, k) * real_pow(x, 2 * k + 1) / &factorial(2 * k + " +
					"1) * (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k)) / &factorial(2 * (n - k)))"
			)

			_, cosXAbsolute := arg.UnpackAs[Real](CosAbsolutelyConvergent.At(x))
			_, sinYAbsolute := arg.UnpackAs[Real](SinAbsolutelyConvergent.At(y))
			cosSin := arg.Have(
				"the cosine series at x and the sine series at y converge "+
					"absolutely, so their Cauchy product sums to cos x·sin y",
				"real_sums(λn:num. "+
					"        Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"        real_pow(x, 2 * k) / "+
					"        &factorial(2 * k) * "+
					"        (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1)), "+
					"    cos(x) * sin(y))",
				By(CosSums.At(x), SinSums.At(y), cosXAbsolute, sinYAbsolute, real_series.CauchyProduct))

			_, sinXAbsolute := arg.UnpackAs[Real](SinAbsolutelyConvergent.At(x))
			_, cosYAbsolute := arg.UnpackAs[Real](CosAbsolutelyConvergent.At(y))
			sinCos := arg.Have(
				"and so do the sine series at x and the cosine "+
					"series at y, whose Cauchy product sums to sin x·cos y",
				"real_sums(λn:num. "+
					"        Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"        real_pow(x, 2 * k + 1) / "+
					"        &factorial(2 * k + 1) * "+
					"        (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k)) / &factorial(2 * (n - k))), "+
					"    sin(x) * cos(y))",
				By(SinSums.At(x), CosSums.At(y), sinXAbsolute, cosYAbsolute, real_series.CauchyProduct))

			sum := arg.Have(
				"added term by term, the two products sum to cos x·sin y + sin x·cos y",
				"real_sums(λn:num. "+
					"        Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"        real_pow(x, 2 * k) / "+
					"        &factorial(2 * k) * "+
					"        (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1)) + "+
					"        Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"        real_pow(x, 2 * k + 1) / "+
					"        &factorial(2 * k + 1) * "+
					"        (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k)) / &factorial(2 * (n - k))), "+
					"    cos(x) * sin(y) + sin(x) * cos(y))",
				By(cosSin, sinCos, real_series.SumsAdd))
			sineSeries := arg.Have(
				"the n-th term of that series is the sine series' term at x + y, so it is the sine series at x + y",
				"real_sums(λn:num. real_pow(-&1, n) * real_pow(x + y, 2 * n + 1) / &factorial(2 * n + 1), "+
					"    cos(x) * sin(y) + sin(x) * cos(y))",
				By(sum, SinProductTerm))

			arg.Show(
				"so sin(x + y) is the sum of the two products",
				CalcEq(
					Leg(
						arg.TermAs[Real]("cos(x) * sin(y) + sin(x) * cos(y)"),
						"the sine series at x + y sums to sin(x + y) as well, and a series has only one sum",
						By(sineSeries, SinSums.At(arg.TermAs[Real]("x + y")), real_series.SumsUnique)),
					FinalLeg(
						"the two products, in the statement's order",
						Cite(real_construction.AddSym))))
		}),
})}

// CosProductTerm — the binomial theorem at the even exponent 2(n + 1),
// divided by (2(n + 1))! and split by the parity of its index. The even
// points 2k, k ≤ n + 1, carry the terms of the cosine product, each up to
// the sign (−1)ᵏ·(−1)ⁿ⁺¹⁻ᵏ = (−1)ⁿ⁺¹; the odd points 2k + 1, k ≤ n, carry
// those of the sine product, each up to (−1)ᵏ·(−1)ⁿ⁻ᵏ = (−1)ⁿ = −(−1)ⁿ⁺¹,
// which is why the sine product is subtracted. The common sign comes out
// of both sums, and what is left is the whole binomial sum.
var CosProductTerm = cosProductTermThm{family.Add(registry.ProofEntry{
	Name: "CosProductTerm",
	Key:  "prop_abf469b0c7ef4902",
	Build: family.Sections(Statement{
		Binders: "∀x y:real. ∀n:num.",
		Conclusion: "Σ_{k∈0 .. n + 1} real_pow(-&1, k) * " +
			"real_pow(x, 2 * k) / " +
			"&factorial(2 * k) * " +
			"(real_pow(-&1, n + 1 - k) * real_pow(y, 2 * (n + 1 - k)) / &factorial(2 * (n + 1 - k))) - " +
			"(Σ_{k∈0 .. n} real_pow(-&1, k) * " +
			"    real_pow(x, 2 * k + 1) / " +
			"    &factorial(2 * k + 1) * " +
			"    (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1))) = " +
			"real_pow(-&1, n + 1) * real_pow(x + y, 2 * (n + 1)) / &factorial(2 * (n + 1))",
		Abbrev: Abbrev{
			{Name: "evenTerm", Text: "real_pow(x, 2 * k) / " +
				"&factorial(2 * k) * " +
				"(real_pow(y, 2 * (n + 1) - 2 * k) / &factorial(2 * (n + 1) - 2 * k))"},
			{Name: "oddTerm", Text: "real_pow(x, 2 * k + 1) / " +
				"&factorial(2 * k + 1) * " +
				"(real_pow(y, 2 * (n + 1) - (2 * k + 1)) / &factorial(2 * (n + 1) - (2 * k + 1)))"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The parity split at an even bound: one point past the odd
			// bound IntervalEvenOdd splits at, and that point is even.
			evenBoundParity := ctx.Lemma(
				"∀n:num. ∀f:(num → real). "+
					"    Σ_{j∈0 .. 2 * (n + 1)} f(j) = Σ_{k∈0 .. n + 1} f(2 * k) + Σ_{k∈0 .. n} f(2 * k + 1)",
				func(arg *Argument, n *Expr[Nat], f *Arrow[Nat, Real]) {
					zero := arg.Ctx().Nat(0)
					evens := arg.TermAs[Fun[Nat, Real]]("λk:num. f(2 * k)")
					top := arg.Have(
						"the even bound 2(n + 1) is the successor of the odd bound 2n + 1",
						"2 * (n + 1) = suc(2 * n + 1)",
						ByArith())
					arg.Show(
						"peel the top point off, split the rest by parity, and hand the top point to the even half",
						CalcEq(
							Leg(
								arg.TermAs[Real]("Σ_{j∈0 .. 2 * n + 1} f(j) + f(2 * (n + 1))"),
								"the top point 2(n + 1) comes off the interval",
								By(
									top,
									real_sum.IntervalClauses.At(zero, arg.TermAs[Nat]("2 * n + 1"), f),
									nat_order.ZeroLessEq.At(arg.TermAs[Nat]("suc(2 * n + 1)")))),
							FinalLeg(
								"0 .. 2n + 1 splits by parity, and 2(n + 1) is the even half's point at n + 1",
								ByArith(
									real_sum.IntervalEvenOdd.At(n, f),
									real_sum.IntervalClauses.At(zero, n, evens),
									nat_arith.Add1.At(n),
									nat_order.ZeroLessEq.At(arg.TermAs[Nat]("suc(n)")))),
						))
				})

			signProduct := ctx.Lemma(
				Statement{
					Binders: "∀m k:num.",
					Hypotheses: []string{
						"k ≤ m",
					},
					Conclusion: "real_pow(-&1, k) * real_pow(-&1, m - k) = real_pow(-&1, m)",
				},
				func(arg *Argument, m, k *Expr[Nat], below Fact) {
					exponents := arg.Have(
						"the two exponents add up to m",
						"k + (m - k) = m",
						ByArith(below))
					arg.Show(
						"so the product is −1 to the power k + (m − k), by the law of exponents",
						By(exponents, real_pow.PowAdd.At(arg.TermAs[Real]("-&1"), k, arg.TermAs[Nat]("m - k"))))
				})

			return ctx.Theorem(headline, func(arg *Argument, x, y *Expr[Real], n *Expr[Nat]) {
				// The k-th terms of the two Cauchy products; the binomial term
				// xʲ/j!·y²⁽ⁿ⁺¹⁾⁻ʲ/(2(n + 1) − j)!; and that term at the even point
				// j = 2k and at the odd point j = 2k + 1.
				const (
					cosineTerm = "real_pow(-&1, k) * real_pow(x, 2 * k) / &factorial(2 * k) * " +
						"(real_pow(-&1, n + 1 - k) * real_pow(y, 2 * (n + 1 - k)) / &factorial(2 * (n + 1 - k)))"
					sineTerm = "real_pow(-&1, k) * real_pow(x, 2 * k + 1) / &factorial(2 * k + 1) * " +
						"(real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1))"
					binomialTerm = "real_pow(x, j) / &factorial(j) * " +
						"(real_pow(y, 2 * (n + 1) - j) / &factorial(2 * (n + 1) - j))"
					evenTerm = "real_pow(x, 2 * k) / &factorial(2 * k) * (real_pow(y, " +
						"2 * (n + 1) - 2 * k) / &factorial(2 * (n + 1) - 2 * k))"
					oddTerm = "real_pow(x, 2 * k + 1) / &factorial(2 * k + 1) * (real_pow(y, " +
						"2 * (n + 1) - (2 * k + 1)) / &factorial(2 * (n + 1) - (2 * k + 1)))"
				)
				zero := arg.Ctx().Nat(0)
				nPlusOne := arg.TermAs[Nat]("n + 1")
				sign := arg.TermAs[Real]("real_pow(-&1, n + 1)")
				minusSign := arg.TermAs[Real]("-real_pow(-&1, n + 1)")

				flip := arg.Have(
					"one more factor −1 turns the sign over",
					"real_pow(-&1, n + 1) = -real_pow(-&1, n)",
					ByArith(real_pow.PowAddOne.At(arg.TermAs[Real]("-&1"), n)))

				even := arg.Have(
					"the cosine product's k-th term is (−1)ⁿ⁺¹ times the binomial term at 2k",
					Statement{
						Binders: "∀k:num.",
						Hypotheses: []string{
							"0 ≤ k",
							"k ≤ n + 1",
						},
						Conclusion: "real_pow(-&1, k) * " +
							"real_pow(x, 2 * k) / " +
							"&factorial(2 * k) * " +
							"(real_pow(-&1, n + 1 - k) * real_pow(y, 2 * (n + 1 - k)) / &factorial(2 * (n + 1 - k))) = " +
							"real_pow(-&1, n + 1) * " +
							"(real_pow(x, 2 * k) / " +
							"    &factorial(2 * k) * " +
							"    (real_pow(y, 2 * (n + 1) - 2 * k) / &factorial(2 * (n + 1) - 2 * k)))",
					},
					Derive(func(d *Argument) {
						k := d.FixAs[Nat]()
						inRange := d.Assume()
						exponent := d.Have(
							"y's exponent 2(n + 1 − k) is 2(n + 1) − 2k",
							"2 * (n + 1 - k) = 2 * (n + 1) - 2 * k",
							ByArith())
						d.Show(
							"gather the two signs, which multiply to (−1)ⁿ⁺¹",
							CalcEq(
								Leg(
									d.TermAs[Real]("real_pow(-&1, k) * real_pow(-&1, n + 1 - k) * («evenTerm»)"),
									"the signs apart from the powers, y's exponent written 2(n + 1) − 2k",
									exponent.Rw(),
									ByArith()),
								FinalLeg(
									"(−1)ᵏ·(−1)ⁿ⁺¹⁻ᵏ = (−1)ⁿ⁺¹, as k ≤ n + 1",
									By(At(signProduct, nPlusOne, k), inRange))))
					}))
				odd := arg.Have(
					"the sine product's k-th term is −(−1)ⁿ⁺¹ times the binomial term at 2k + 1",
					Statement{
						Binders: "∀k:num.",
						Hypotheses: []string{
							"0 ≤ k",
							"k ≤ n",
						},
						Conclusion: "real_pow(-&1, k) * " +
							"real_pow(x, 2 * k + 1) / " +
							"&factorial(2 * k + 1) * " +
							"(real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1)) = " +
							"-real_pow(-&1, n + 1) * " +
							"(real_pow(x, 2 * k + 1) / " +
							"    &factorial(2 * k + 1) * " +
							"    (real_pow(y, 2 * (n + 1) - (2 * k + 1)) / &factorial(2 * (n + 1) - (2 * k + 1))))",
					},
					Derive(func(d *Argument) {
						k := d.FixAs[Nat]()
						inRange := d.Assume()
						exponent := d.Have(
							"y's exponent 2(n − k) + 1 is 2(n + 1) − (2k + 1), as k ≤ n",
							"2 * (n - k) + 1 = 2 * (n + 1) - (2 * k + 1)",
							ByArith(inRange))
						d.Show(
							"gather the two signs, which multiply to (−1)ⁿ = −(−1)ⁿ⁺¹",
							CalcEq(
								Leg(
									d.TermAs[Real]("real_pow(-&1, k) * real_pow(-&1, n - k) * («oddTerm»)"),
									"the signs apart from the powers, y's exponent written 2(n + 1) − (2k + 1)",
									exponent.Rw(),
									ByArith()),
								Leg(
									d.TermAs[Real]("real_pow(-&1, n) * («oddTerm»)"),
									"(−1)ᵏ·(−1)ⁿ⁻ᵏ = (−1)ⁿ, as k ≤ n",
									By(At(signProduct, n, k), inRange)),
								FinalLeg(
									"and (−1)ⁿ is −(−1)ⁿ⁺¹",
									ByArith(flip))))
					}))

				cosines := arg.BigOpAs[Nat, Real]("Σ_{k∈0 .. n + 1} " + cosineTerm)
				sines := arg.BigOpAs[Nat, Real]("Σ_{k∈0 .. n} " + sineTerm)
				evensSigned := arg.BigOpAs[Nat, Real]("Σ_{k∈0 .. n + 1} real_pow(-&1, n + 1) * (" + evenTerm + ")")
				oddsSigned := arg.BigOpAs[Nat, Real]("Σ_{k∈0 .. n} -real_pow(-&1, n + 1) * (" + oddTerm + ")")
				evens := arg.BigOpAs[Nat, Real]("Σ_{k∈0 .. n + 1} " + evenTerm)
				odds := arg.BigOpAs[Nat, Real]("Σ_{k∈0 .. n} " + oddTerm)
				binomial := arg.BigOpAs[Nat, Real]("Σ_{j∈0 .. 2 * (n + 1)} " + binomialTerm)

				arg.Show(
					"signed, the two products' terms are the binomial terms at the even and at the odd points",
					CalcEq(
						Leg(
							arg.TermAs[Real](
								"Σ_{k∈0 .. n + 1} real_pow(-&1, n + 1) * "+
									"(real_pow(x, 2 * k) / "+
									"    &factorial(2 * k) * "+
									"    (real_pow(y, 2 * (n + 1) - 2 * k) / &factorial(2 * (n + 1) - 2 * k))) - "+
									"Σ_{k∈0 .. n} -real_pow(-&1, n + 1) * (real_pow(x, 2 * k + 1) / &factorial(2 * k + 1) * (real_pow(y, 2 * (n + 1) - (2 * k + 1)) / &factorial(2 * (n + 1) - (2 * k + 1))))"),
							"term by term, as above",
							By(
								even,
								odd,
								real_sum.IntervalCongruence.At(zero, nPlusOne, cosines.Summand(), evensSigned.Summand()),
								real_sum.IntervalCongruence.At(zero, n, sines.Summand(), oddsSigned.Summand()))),
						Leg(
							arg.TermAs[Real](
								"real_pow(-&1, n + 1) * "+
									"(Σ_{k∈0 .. n + 1} real_pow(x, 2 * k) / "+
									"    &factorial(2 * k) * "+
									"    (real_pow(y, 2 * (n + 1) - 2 * k) / &factorial(2 * (n + 1) - 2 * k)) + "+
									"    Σ_{k∈0 .. n} real_pow(x, 2 * k + 1) / "+
									"    &factorial(2 * k + 1) * "+
									"    (real_pow(y, 2 * (n + 1) - (2 * k + 1)) / &factorial(2 * (n + 1) - (2 * k + 1))))"),
							"the sign is the same in every term, so it comes out of both sums",
							ByArith(
								real_sum.ScalarLeft.At(sign, evens.Summand(), evens.Range()),
								real_sum.ScalarLeft.At(minusSign, odds.Summand(), odds.Range()))),
						Leg(
							arg.TermAs[Real](
								"real_pow(-&1, n + 1) * "+
									"Σ_{j∈0 .. 2 * (n + 1)} real_pow(x, j) / "+
									"&factorial(j) * "+
									"(real_pow(y, 2 * (n + 1) - j) / &factorial(2 * (n + 1) - j))"),
							"the even and the odd points together are all of 0 .. 2(n + 1)",
							By(At(evenBoundParity, n, binomial.Summand()))),
						FinalLeg(
							"and the binomial theorem divided by (2(n + 1))! "+
								"sums the binomial terms to (x + y)²⁽ⁿ⁺¹⁾/(2(n + 1))!",
							Simp(Fwd(real_exp_log.ExpProductTerm)),
							ByArith()),
					))
			})
		}),
})}

// CosAdd — the addition formula of the cosine. Both series converge
// absolutely, so the Cauchy product of the cosine series at x and at y
// sums to cos x·cos y, and that of the sine series to sin x·sin y. The
// degrees do not line up term by term — the n-th term of the sine
// product has degree 2n + 2 — so the cosine product and the cosine series
// at x + y are read from their second term on: their first terms are 1,
// the shifted product sums to cos x·cos y − 1 and the shifted series at
// x + y to cos(x + y) − 1. By CosProductTerm the shifted series at x + y
// plus the sine product is the shifted product term by term, so that
// product has the two sums cos x·cos y − 1 and
// cos(x + y) − 1 + sin x·sin y, and a series has only one sum.
var CosAdd = cosAddThm{family.Add(registry.ProofEntry{
	Name: "CosAdd",
	Key:  "prop_89258f83d35aa289",
	Build: family.Theorem(Statement{
		Binders:    "∀x y:real.",
		Conclusion: "cos(x + y) = cos(x) * cos(y) - sin(x) * sin(y)",
	},
		func(arg *Argument, x, y *Expr[Real]) {
			// The cosine product's n-th term and its term at n + 1; the sine
			// product's n-th term; the cosine series' term at x + y and n + 1.
			_, cosXAbsolute := arg.UnpackAs[Real](CosAbsolutelyConvergent.At(x))
			_, cosYAbsolute := arg.UnpackAs[Real](CosAbsolutelyConvergent.At(y))
			cosineProduct := arg.Have(
				"the cosine series at x and at y converge absolutely, so their Cauchy product sums to cos x·cos y",
				"real_sums(λn:num. "+
					"        Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"        real_pow(x, 2 * k) / "+
					"        &factorial(2 * k) * "+
					"        (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k)) / &factorial(2 * (n - k))), "+
					"    cos(x) * cos(y))",
				By(CosSums.At(x), CosSums.At(y), cosXAbsolute, cosYAbsolute, real_series.CauchyProduct))

			_, sinXAbsolute := arg.UnpackAs[Real](SinAbsolutelyConvergent.At(x))
			_, sinYAbsolute := arg.UnpackAs[Real](SinAbsolutelyConvergent.At(y))
			sineProduct := arg.Have(
				"and so do the sine series at x and at y, whose Cauchy product sums to sin x·sin y",
				"real_sums(λn:num. "+
					"        Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"        real_pow(x, 2 * k + 1) / "+
					"        &factorial(2 * k + 1) * "+
					"        (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1)), "+
					"    sin(x) * sin(y))",
				By(SinSums.At(x), SinSums.At(y), sinXAbsolute, sinYAbsolute, real_series.CauchyProduct))

			productStart := arg.Have(
				"the cosine product's first term is the product of the two first terms, 1·1 = 1",
				"Σ_{k∈0 .. 0} real_pow(-&1, k) * "+
					"real_pow(x, 2 * k) / "+
					"&factorial(2 * k) * "+
					"(real_pow(-&1, 0 - k) * real_pow(y, 2 * (0 - k)) / &factorial(2 * (0 - k))) = "+
					"&1",
				ByArith(real_sum.IntervalPoint))
			shiftedProduct := arg.Have(
				"so from its second term on the cosine product sums to cos x·cos y − 1",
				"real_sums(λn:num. "+
					"        Σ_{k∈0 .. n + 1} real_pow(-&1, k) * "+
					"        real_pow(x, 2 * k) / "+
					"        &factorial(2 * k) * "+
					"        (real_pow(-&1, n + 1 - k) * "+
					"            real_pow(y, 2 * (n + 1 - k)) / "+
					"            &factorial(2 * (n + 1 - k))), "+
					"    cos(x) * cos(y) - &1)",
				By(
					productStart,
					cosineProduct,
					real_series.SumsShift.At(
						arg.TermAs[Fun[Nat, Real]](
							"λn:num. "+
								"    Σ_{k∈0 .. n} real_pow(-&1, k) * "+
								"    real_pow(x, 2 * k) / "+
								"    &factorial(2 * k) * "+
								"    (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k)) / &factorial(2 * (n - k)))"),
						arg.TermAs[Real]("cos(x) * cos(y)"))))

			seriesStart := arg.Have(
				"the cosine series' first term at x + y is 1",
				"real_pow(-&1, 0) * real_pow(x + y, 2 * 0) / &factorial(2 * 0) = &1",
				ByArith())
			shiftedSeries := arg.Have(
				"so from its second term on the cosine series at x + y sums to cos(x + y) − 1",
				"real_sums( "+
					"    λn:num. real_pow(-&1, n + 1) * real_pow(x + y, 2 * (n + 1)) / &factorial(2 * (n + 1)), "+
					"    cos(x + y) - &1)",
				By(
					seriesStart,
					CosSums.At(arg.TermAs[Real]("x + y")),
					real_series.SumsShift.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(-&1, n) * real_pow(x + y, 2 * n) / &factorial(2 * n)"),
						arg.TermAs[Real]("cos(x + y)"))))

			together := arg.Have(
				"adding the sine product to it termwise, the sums add",
				"real_sums(λn:num. "+
					"        real_pow(-&1, n + 1) * real_pow(x + y, 2 * (n + 1)) / &factorial(2 * (n + 1)) + "+
					"        Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"        real_pow(x, 2 * k + 1) / "+
					"        &factorial(2 * k + 1) * "+
					"        (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1)), "+
					"    cos(x + y) - &1 + sin(x) * sin(y))",
				By(shiftedSeries, sineProduct, real_series.SumsAdd))
			termwise := arg.Have(
				"and that termwise sum is the shifted cosine product: "+
					"CosProductTerm, the sine product's term taken across",
				"(λn:num. "+
					"    real_pow(-&1, n + 1) * real_pow(x + y, 2 * (n + 1)) / &factorial(2 * (n + 1)) + "+
					"    Σ_{k∈0 .. n} real_pow(-&1, k) * "+
					"    real_pow(x, 2 * k + 1) / "+
					"    &factorial(2 * k + 1) * "+
					"    (real_pow(-&1, n - k) * real_pow(y, 2 * (n - k) + 1) / &factorial(2 * (n - k) + 1))) = "+
					"(λn:num. "+
					"    Σ_{k∈0 .. n + 1} real_pow(-&1, k) * "+
					"    real_pow(x, 2 * k) / "+
					"    &factorial(2 * k) * "+
					"    (real_pow(-&1, n + 1 - k) * real_pow(y, 2 * (n + 1 - k)) / &factorial(2 * (n + 1 - k))))",
				Funext(),
				arg.ForEach(func(n *Expr[Nat]) Action { return ByArith(CosProductTerm.At(x, y, n)) }))
			bothSums := arg.Have(
				"so the shifted cosine product also sums to cos(x + y) − 1 + sin x·sin y",
				"real_sums(λn:num. "+
					"        Σ_{k∈0 .. n + 1} real_pow(-&1, k) * "+
					"        real_pow(x, 2 * k) / "+
					"        &factorial(2 * k) * "+
					"        (real_pow(-&1, n + 1 - k) * "+
					"            real_pow(y, 2 * (n + 1 - k)) / "+
					"            &factorial(2 * (n + 1 - k))), "+
					"    cos(x + y) - &1 + sin(x) * sin(y))",
				termwise.RwRev(),
				By(together))

			unique := arg.Have(
				"a series has only one sum",
				"cos(x + y) - &1 + sin(x) * sin(y) = cos(x) * cos(y) - &1",
				By(bothSums, shiftedProduct, real_series.SumsUnique))
			arg.Show(
				"which, with sin x·sin y taken across, is the addition formula",
				ByArith(unique))
		}),
})}

// SinSquareAddCosSquare — the point (cos x, sin x) lies on the unit
// circle. The addition formula at x and −x reads cos(x − x) as
// cos x·cos(−x) − sin x·sin(−x); the cosine is even and the sine odd, so
// that is cos²x + sin²x, and cos(x − x) = cos 0 = 1.
var SinSquareAddCosSquare = sinSquareAddCosSquareThm{family.Add(registry.ProofEntry{
	Name: "SinSquareAddCosSquare",
	Key:  "prop_e5bcfba9fbb19dd6",
	Build: family.Theorem("∀x:real. real_pow(sin(x), 2) + real_pow(cos(x), 2) = &1",
		func(arg *Argument, x *Expr[Real]) {
			cancel := arg.Have(
				"x + −x is 0",
				"x + -x = &0",
				ByArith())
			atZero := arg.Have(
				"so cos(x + −x) is cos 0 = 1",
				"cos(x + -x) = &1",
				By(cancel, CosZero))
			circle := arg.Have(
				"and by the addition formula it is cos x·cos(−x) − sin x·sin(−x) = cos²x + sin²x",
				"cos(x + -x) = cos(x) * cos(x) + sin(x) * sin(x)",
				Simp(Fwd(CosAdd), Fwd(CosNeg), Fwd(SinNeg)),
				ByArith())
			arg.Show(
				"so cos²x + sin²x = 1",
				ByArith(atZero, circle))
		}),
})}

// SinAbsLessEqOne — the sine lies between −1 and 1: its square is at
// most sin²x + cos²x = 1.
var SinAbsLessEqOne = sinAbsLessEqOneThm{family.Add(registry.ProofEntry{
	Name: "SinAbsLessEqOne",
	Key:  "prop_22ae1f7091cfee3",
	Build: family.Theorem("∀x:real. |sin(x)| ≤ &1",
		func(arg *Argument, x *Expr[Real]) {
			value, other := arg.TermAs[Real]("sin(x)"), arg.TermAs[Real]("cos(x)")
			square := arg.Have(
				"sin²x is at most sin²x + cos²x = 1",
				"real_pow(sin(x), 2) ≤ &1",
				ByArith(SinSquareAddCosSquare.At(x), real_pow.PowTwoNonneg.At(other)))
			arg.Show(
				"and sizes compare as their squares do: |sin x| ≤ |1| = 1",
				By(
					Normalized,
					square,
					real_pow.AbsLessEqIffPowTwoLessEq.At(value, arg.TermAs[Real]("&1")),
					real_sgn_abs.AbsOfOne,
					real_pow.OnePow.At(arg.TermAs[Nat]("2"))))
		}),
})}

// CosAbsLessEqOne — the cosine lies between −1 and 1, as the sine does.
var CosAbsLessEqOne = cosAbsLessEqOneThm{family.Add(registry.ProofEntry{
	Name: "CosAbsLessEqOne",
	Key:  "prop_4eec99461456c2d9",
	Build: family.Theorem("∀x:real. |cos(x)| ≤ &1",
		func(arg *Argument, x *Expr[Real]) {
			value, other := arg.TermAs[Real]("cos(x)"), arg.TermAs[Real]("sin(x)")
			square := arg.Have(
				"cos²x is at most sin²x + cos²x = 1",
				"real_pow(cos(x), 2) ≤ &1",
				ByArith(SinSquareAddCosSquare.At(x), real_pow.PowTwoNonneg.At(other)))
			arg.Show(
				"and sizes compare as their squares do: |cos x| ≤ |1| = 1",
				By(
					Normalized,
					square,
					real_pow.AbsLessEqIffPowTwoLessEq.At(value, arg.TermAs[Real]("&1")),
					real_sgn_abs.AbsOfOne,
					real_pow.OnePow.At(arg.TermAs[Nat]("2"))))
		}),
})}
