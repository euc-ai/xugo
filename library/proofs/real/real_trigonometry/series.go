// series.go — the series of the sine and the cosine: the convergence of
// the two series, their sums, their values at 0 and their parity.

package real_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// CosAbsolutelyConvergent — the cosine series converges absolutely, by
// comparison with the exponential series at x·x. The size of its n-th
// term is (x·x)ⁿ/(2n)!, and as n! ≤ (2n)! that is at most (x·x)ⁿ/n!,
// the n-th term of the exponential series at x·x, which sums to
// exp(x·x).
var CosAbsolutelyConvergent = cosAbsolutelyConvergentThm{family.Add(registry.ProofEntry{
	Name: "CosAbsolutelyConvergent",
	Key:  "prop_132b3ed9f884918e",
	Build: family.Theorem("∀x:real. ∃s:real. "+
		"    real_sums(λn:num. |real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n)|, s)",
		func(arg *Argument, x *Expr[Real]) {
			square, absX := arg.TermAs[Real]("x * x"), arg.TermAs[Real]("|x|")

			bound := arg.Have(
				"the size of each term is at most the exponential series' term at x·x",
				"∀n:num. "+
					"    ||real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n)|| ≤ "+
					"    real_pow(x * x, n) / &factorial(n)",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					factorialN, factorialEven := d.TermAs[Nat]("factorial(n)"), d.TermAs[Nat]("factorial(2 * n)")

					positive := d.Have(
						"n! is not 0, so its image in ℝ is positive",
						"&0 < &factorial(n)",
						ByArith(
							nat_arith.FactorialNonzero.At(n),
							real_order_ring.OfNumLessThan.At(d.TermAs[Nat]("0"), factorialN)))
					larger := d.Have(
						"n ≤ 2n, so n! ≤ (2n)!, in ℕ and so in ℝ",
						"&factorial(n) ≤ &factorial(2 * n)",
						ByArith(
							nat_order.FactorialMonotone.At(n, d.TermAs[Nat]("2 * n")),
							real_construction.OfNumLessEq.At(factorialN, factorialEven)))
					reciprocals := d.Have(
						"so the reciprocal of (2n)! is at most that of n!",
						"real_inv(&factorial(2 * n)) ≤ real_inv(&factorial(n))",
						By(
							positive,
							larger,
							real_order_field.InvAntitoneWeak.At(
								d.TermAs[Real]("&factorial(n)"), d.TermAs[Real]("&factorial(2 * n)"))))
					evenPower := d.Have(
						"(x·x)ⁿ is a power of a square, so it is nonnegative",
						"&0 ≤ real_pow(x * x, n)",
						ByArith(real_pow.PowNonneg.At(square, n)))

					d.Show(
						"so the size of the term is (x·x)ⁿ/(2n)!, at most (x·x)ⁿ/n!",
						real_order_ring.OrderCalc(d.Ctx()).CalcLeibniz(
							d.TermAs[Real]("||real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n)||"),
							EqLeg(
								d.TermAs[Real]("real_pow(|x|, 2 * n) / &factorial(2 * n)"),
								"a size is its own size, sizes pass through products, quotients and powers, and |−1|ⁿ = 1ⁿ = 1",
								Simp(
									Fwd(real_sgn_abs.AbsIdempotent),
									Fwd(real_sgn_abs.AbsDiv),
									Fwd(real_sgn_abs.AbsMul),
									Fwd(real_sgn_abs.AbsOfNum),
									Fwd(real_pow.AbsPow),
									Fwd(real_sgn_abs.AbsEven),
									Fwd(real_pow.OnePow),
									Fwd(real_construction.MulLeftId)),
								Refl()),
							EqLeg(
								d.TermAs[Real]("real_pow(x * x, n) / &factorial(2 * n)"),
								"|x|²ⁿ = (|x|²)ⁿ, and |x|² = x² = x·x",
								By(
									real_pow.PowPow.At(absX, d.TermAs[Nat]("2"), n),
									real_pow.SquareOfAbs.At(x),
									real_pow.PowTwo.At(x))),
							LeLeg(
								d.TermAs[Real]("real_pow(x * x, n) / &factorial(n)"),
								"the reciprocals' order, scaled by the nonnegative (x·x)ⁿ",
								ByArith(
									reciprocals,
									evenPower,
									real_order_ring.LessEqMulLeft.At(d.TermAs[Real]("real_pow(x * x, n)"),
										d.TermAs[Real]("real_inv(&factorial(2 * n))"), d.TermAs[Real]("real_inv(&factorial(n))"))))))
				}))

			arg.Show(
				"the cosine series is dominated in size by the "+
					"exponential series at x·x, so it converges absolutely",
				By(
					bound,
					real_exp_log.ExpSums.At(square),
					real_series.Comparison.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. |real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n)|"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(x * x, n) / &factorial(n)"),
						arg.TermAs[Real]("exp(x * x)"), arg.TermAs[Nat]("0"))))
		}),
})}

// SinAbsolutelyConvergent — the sine series converges absolutely, by
// comparison with |x| times the exponential series at x·x. Its n-th term
// has size |x|²ⁿ⁺¹/(2n + 1)! = |x|·(x·x)ⁿ/(2n + 1)!, and n! ≤ (2n + 1)!
// puts that below |x|·(x·x)ⁿ/n!, the n-th term of a series summing to
// |x|·exp(x·x).
var SinAbsolutelyConvergent = sinAbsolutelyConvergentThm{family.Add(registry.ProofEntry{
	Name: "SinAbsolutelyConvergent",
	Key:  "prop_a7db2ddfc924b0d9",
	Build: family.Theorem("∀x:real. ∃s:real. "+
		"    real_sums(λn:num. |real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)|, s)",
		func(arg *Argument, x *Expr[Real]) {
			square, absX := arg.TermAs[Real]("x * x"), arg.TermAs[Real]("|x|")

			dominating := arg.Have(
				"|x| times the exponential series at x·x sums to |x|·exp(x·x)",
				"real_sums(λn:num. |x| * (real_pow(x * x, n) / &factorial(n)), |x| * exp(x * x))",
				By(
					real_series.SumsScale.At(arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(x * x, n) / &factorial(n)"),
						arg.TermAs[Real]("exp(x * x)"), absX),
					real_exp_log.ExpSums.At(square)))

			bound := arg.Have(
				"the size of each term is at most the matching term of that series",
				"∀n:num. "+
					"    ||real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)|| ≤ "+
					"    |x| * (real_pow(x * x, n) / &factorial(n))",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					factorialN, factorialOdd := d.TermAs[Nat]("factorial(n)"), d.TermAs[Nat]("factorial(2 * n + 1)")

					positive := d.Have(
						"n! is not 0, so its image in ℝ is positive",
						"&0 < &factorial(n)",
						ByArith(
							nat_arith.FactorialNonzero.At(n),
							real_order_ring.OfNumLessThan.At(d.TermAs[Nat]("0"), factorialN)))
					larger := d.Have(
						"n ≤ 2n + 1, so n! ≤ (2n + 1)!, in ℕ and so in ℝ",
						"&factorial(n) ≤ &factorial(2 * n + 1)",
						ByArith(
							nat_order.FactorialMonotone.At(n, d.TermAs[Nat]("2 * n + 1")),
							real_construction.OfNumLessEq.At(factorialN, factorialOdd)))
					reciprocals := d.Have(
						"so the reciprocal of (2n + 1)! is at most that of n!",
						"real_inv(&factorial(2 * n + 1)) ≤ real_inv(&factorial(n))",
						By(
							positive,
							larger,
							real_order_field.InvAntitoneWeak.At(
								d.TermAs[Real]("&factorial(n)"), d.TermAs[Real]("&factorial(2 * n + 1)"))))
					evenPower := d.Have(
						"(x·x)ⁿ is a power of a square, so it is nonnegative",
						"&0 ≤ real_pow(x * x, n)",
						ByArith(real_pow.PowNonneg.At(square, n)))

					d.Show(
						"so the size of the term is |x|·(x·x)ⁿ/(2n + 1)!, at most |x|·(x·x)ⁿ/n!",
						real_order_ring.OrderCalc(d.Ctx()).CalcLeibniz(
							d.TermAs[Real]("||real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)||"),
							EqLeg(
								d.TermAs[Real]("real_pow(|x|, 2 * n + 1) / &factorial(2 * n + 1)"),
								"a size is its own size, sizes pass through products, quotients and powers, and |−1|ⁿ = 1ⁿ = 1",
								Simp(
									Fwd(real_sgn_abs.AbsIdempotent),
									Fwd(real_sgn_abs.AbsDiv),
									Fwd(real_sgn_abs.AbsMul),
									Fwd(real_sgn_abs.AbsOfNum),
									Fwd(real_pow.AbsPow),
									Fwd(real_sgn_abs.AbsEven),
									Fwd(real_pow.OnePow),
									Fwd(real_construction.MulLeftId)),
								Refl()),
							EqLeg(
								d.TermAs[Real]("|x| * real_pow(x * x, n) / &factorial(2 * n + 1)"),
								"|x|²ⁿ⁺¹ = |x|·(|x|²)ⁿ, and |x|² = x² = x·x",
								By(
									real_pow.PowAddOne.At(absX, d.TermAs[Nat]("2 * n")),
									real_pow.PowPow.At(absX, d.TermAs[Nat]("2"), n),
									real_pow.SquareOfAbs.At(x),
									real_pow.PowTwo.At(x))),
							LeLeg(
								d.TermAs[Real]("|x| * (real_pow(x * x, n) / &factorial(n))"),
								"the reciprocals' order, scaled by the nonnegative |x|·(x·x)ⁿ",
								ByArith(
									reciprocals,
									evenPower,
									real_sgn_abs.AbsNonneg.At(x),
									real_order_ring.LessEqMulLeft.At(d.TermAs[Real]("|x| * real_pow(x * x, n)"),
										d.TermAs[Real]("real_inv(&factorial(2 * n + 1))"), d.TermAs[Real]("real_inv(&factorial(n))"))))))
				}))

			arg.Show(
				"the sine series is dominated in size by a series with a sum, so it converges absolutely",
				By(
					bound,
					dominating,
					real_series.Comparison.At(
						arg.TermAs[Fun[Nat, Real]](
							"λn:num. |real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)|"),
						arg.TermAs[Fun[Nat, Real]]("λn:num. |x| * (real_pow(x * x, n) / &factorial(n))"),
						arg.TermAs[Real]("|x| * exp(x * x)"), arg.TermAs[Nat]("0"))))
		}),
})}

// CosSums — the cosine series sums to real_cos(x). It converges
// absolutely, so it converges: the comparison test, read against the
// series of its own sizes. real_cos(x) is the choice of a sum, so it is
// one.
var CosSums = cosSumsThm{family.Add(registry.ProofEntry{
	Name: "CosSums",
	Key:  "prop_58ed0afa8c2dabc2",
	Build: family.Theorem("∀x:real. "+
		"    real_sums(λn:num. real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n), cos(x))",
		func(arg *Argument, x *Expr[Real]) {
			arg.Do(Unfold(RealCosDef))

			series := arg.TermAs[Fun[Nat, Real]](
				"λn:num. real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n)")
			sizes := arg.TermAs[Fun[Nat, Real]](
				"λn:num. |real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n)|")
			t, absolutely := arg.UnpackAs[Real](CosAbsolutelyConvergent.At(x))
			converges := arg.Have(
				"the series has a sum: each term is at most its own size, and the sizes have a sum",
				"∃s:real. real_sums(λn:num. real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n), s)",
				By(
					absolutely,
					real_order_ring.LessEqRefl,
					real_series.Comparison.At(series, sizes, t, arg.TermAs[Nat]("0"))))
			arg.Show(
				"cos(x) is the choice of such a sum, so it is one",
				By(converges))
		}),
})}

// SinSums — the sine series sums to real_sin(x), as the cosine series
// sums to real_cos(x).
var SinSums = sinSumsThm{family.Add(registry.ProofEntry{
	Name: "SinSums",
	Key:  "prop_f5bb8a24293e0d2d",
	Build: family.Theorem("∀x:real. "+
		"    real_sums(λn:num. real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1), sin(x))",
		func(arg *Argument, x *Expr[Real]) {
			arg.Do(Unfold(RealSinDef))

			series := arg.TermAs[Fun[Nat, Real]](
				"λn:num. real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)")
			sizes := arg.TermAs[Fun[Nat, Real]](
				"λn:num. |real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)|")
			t, absolutely := arg.UnpackAs[Real](SinAbsolutelyConvergent.At(x))
			converges := arg.Have(
				"the series has a sum: each term is at most its own size, and the sizes have a sum",
				"∃s:real. real_sums(λn:num. real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1), s)",
				By(
					absolutely,
					real_order_ring.LessEqRefl,
					real_series.Comparison.At(series, sizes, t, arg.TermAs[Nat]("0"))))
			arg.Show(
				"sin(x) is the choice of such a sum, so it is one",
				By(converges))
		}),
})}

// CosZero — the cosine is 1 at 0. At 0 every term of the series past
// the first is 0, since 0²ⁱ = 0 for i ≥ 1, and the first is
// (−1)⁰·0⁰/0! = 1: every partial sum is 1, so the series at 0 sums to 1,
// and a series has one sum.
var CosZero = cosZeroThm{family.Add(registry.ProofEntry{
	Name: "CosZero",
	Key:  "prop_22bad445d5472894",
	Build: family.Theorem("cos(&0) = &1",
		func(arg *Argument) {
			series := arg.TermAs[Fun[Nat, Real]](
				"λk:num. real_pow(-&1, k) * real_pow(&0, 2 * k) / &factorial(2 * k)")
			partialSums := arg.Have(
				"every partial sum of the series at 0 is its first term, (−1)⁰·0⁰/0! = 1",
				"(λn:num. Σ_{k∈0 .. n} real_pow(-&1, k) * real_pow(&0, 2 * k) / &factorial(2 * k)) = (λn:num. &1)",
				Funext(),
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					tail := d.Have(
						"past the first, each term is 0, as 0²ⁱ = 0 for i ≥ 1",
						"∀i:num. 1 ≤ i ∧ i ≤ n ⇒ real_pow(-&1, i) * real_pow(&0, 2 * i) / &factorial(2 * i) = &0",
						Derive(func(e *Argument) {
							e.FixAs[Nat]()
							past := e.Assume()
							e.Show(
								"2i is not 0, so 0²ⁱ is 0",
								ByArith(past, real_pow.ZeroPow.At(e.TermAs[Nat]("2 * i"))))
						}))
					zero, one := d.TermAs[Nat]("0"), d.TermAs[Nat]("1")
					d.Show(
						"peel the first term off 0 .. n: it is 1, and the rest is a sum of zeros over 1 .. n",
						ByArith(
							tail,
							real_sum.PeelLeft.At(zero, n, series),
							nat_order.ZeroLessEq.At(n),
							real_sum.IntervalEqZero.At(one, n, series),
							real_pow.ZeroPow.At(d.TermAs[Nat]("2 * 0"))))
				}))
			sums := arg.Have(
				"so the partial sums are the constant sequence 1, and the series at 0 sums to 1",
				"real_sums(λn:num. real_pow(-&1, n) * real_pow(&0, 2 * n) / &factorial(2 * n), &1)",
				Simp(Fwd(real_series.RealSumsDef)),
				partialSums.Rw(),
				By(real_sequences.LimitConst.At(arg.TermAs[Real]("&1"))))
			arg.Show(
				"cos(0) is a sum of the same series, and a series has only one sum",
				By(sums, CosSums.At(arg.TermAs[Real]("&0")), real_series.SumsUnique))
		}),
})}

// CosNeg — the cosine is even. An even power forgets the sign,
// (−x)²ⁿ = ((−x)²)ⁿ = (x²)ⁿ = x²ⁿ, so the series at −x is the series at
// x: it sums to cos(−x) and to cos(x), and a series has one sum.
var CosNeg = cosNegThm{family.Add(registry.ProofEntry{
	Name: "CosNeg",
	Key:  "prop_6c6596016fb51fa0",
	Build: family.Theorem("∀x:real. cos(-x) = cos(x)",
		func(arg *Argument, x *Expr[Real]) {
			even := arg.Have(
				"an even power forgets the sign — the ring's law at ℝ, whose power is its product's",
				"∀n:num. real_pow(-x, 2 * n) = real_pow(x, 2 * n)",
				Simp(Fwd(real_pow.MonoidPow)),
				By(comm_ring.NegPowEven.Read(real_ring.CommRing)))
			same := arg.Have(
				"so the series at −x is the series at x, term by term",
				"(λn:num. real_pow(-&1, n) * real_pow(-x, 2 * n) / &factorial(2 * n)) = "+
					"(λn:num. real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n))",
				Funext(),
				arg.ForEach(func(n *Expr[Nat]) Action { return By(even.At(n)) }))
			atNeg := arg.Have(
				"and the series at x sums to cos(−x)",
				"real_sums(λn:num. real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n), cos(-x))",
				same.RwRev(),
				By(CosSums.At(arg.TermAs[Real]("-x"))))
			arg.Show(
				"it sums to cos(x) as well, and a series has only one sum",
				By(atNeg, CosSums.At(x), real_series.SumsUnique))
		}),
})}

// SinNeg — the sine is odd. An odd power keeps the sign,
// (−x)²ⁿ⁺¹ = (−x)·(−x)²ⁿ = −x·x²ⁿ = −x²ⁿ⁺¹, so the series at −x is the
// series at x scaled by −1, which sums to −sin(x); it sums to sin(−x) as
// well, and a series has one sum.
var SinNeg = sinNegThm{family.Add(registry.ProofEntry{
	Name: "SinNeg",
	Key:  "prop_1a13e6cfe6de915e",
	Build: family.Theorem("∀x:real. sin(-x) = -sin(x)",
		func(arg *Argument, x *Expr[Real]) {
			odd := arg.Have(
				"an odd power keeps the sign — the ring's law at ℝ, whose power is its product's",
				"∀n:num. real_pow(-x, 2 * n + 1) = -real_pow(x, 2 * n + 1)",
				Simp(Fwd(real_pow.MonoidPow)),
				By(comm_ring.NegPowOdd.Read(real_ring.CommRing)))
			scaled := arg.Have(
				"so the series at −x is the series at x scaled by −1, term by term",
				"(λn:num. real_pow(-&1, n) * real_pow(-x, 2 * n + 1) / &factorial(2 * n + 1)) = "+
					"(λn:num. -&1 * (real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)))",
				Funext(),
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					power := d.Have(
						"the n-th term's power of −x is minus that of x",
						"real_pow(-x, 2 * n + 1) = -real_pow(x, 2 * n + 1)",
						By(odd.At(n)))
					d.Show(
						"so the n-th terms agree",
						power.Rw(),
						ByArith())
				}))
			atNeg := arg.Have(
				"the series at x scaled by −1 sums to sin(−x)",
				"real_sums(λn:num. -&1 * (real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)), "+
					"    sin(-x))",
				scaled.RwRev(),
				By(SinSums.At(arg.TermAs[Real]("-x"))))
			series := arg.TermAs[Fun[Nat, Real]](
				"λn:num. real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)")
			sinX, minusOne := arg.TermAs[Real]("sin(x)"), arg.TermAs[Real]("-&1")
			negated := arg.Have(
				"and to −1·sin(x)",
				"real_sums(λn:num. -&1 * (real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)), "+
					"    -&1 * sin(x))",
				By(SinSums.At(x), real_series.SumsScale.At(series, sinX, minusOne)))
			unique := arg.Have(
				"a series has only one sum",
				"sin(-x) = -&1 * sin(x)",
				By(atNeg, negated, real_series.SumsUnique))
			arg.Show(
				"and −1·sin(x) is −sin(x)",
				ByArith(unique))
		}),
})}

// SinZero — the sine is 0 at 0: sin 0 = sin(−0) = −sin 0, and the only
// number equal to its own negative is 0.
var SinZero = sinZeroThm{family.Add(registry.ProofEntry{
	Name: "SinZero",
	Key:  "prop_5e0fbf3a1257684e",
	Build: family.Theorem("sin(&0) = &0",
		func(arg *Argument) {
			zero := arg.TermAs[Real]("&0")
			negZero := arg.Have(
				"−0 is 0",
				"-&0 = &0",
				ByArith())
			odd := arg.Have(
				"so sin 0 = sin(−0) = −sin 0",
				"sin(&0) = -sin(&0)",
				By(Normalized, negZero, SinNeg.At(zero)))
			arg.Show(
				"and a number equal to its negative is 0",
				ByArith(odd))
		}),
})}
