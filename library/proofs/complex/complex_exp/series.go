// series.go — the three series converge, each because the sizes of its
// terms are dominated by ℝ's exponential series at |z|.

package complex_exp

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_series"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/registry"
)

// ExpSums — the exponential series sums to exp(z). The size of its n-th
// term is |z|ⁿ/n!, the n-th term of ℝ's exponential series at |z|, which
// sums to exp|z|; a series whose sizes have a sum has a sum, and exp(z)
// is the choice of one.
var ExpSums = expSumsThm{family.Add(registry.ProofEntry{
	Name: "ExpSums",
	Key:  "prop_bae603ca4149de2f",
	Build: family.Theorem("∀z:complex. "+
		"    complex_sums(λn:num. z ^ n / complex_of_real(&factorial(n)), exp(z))",
		func(arg *Argument, z *Expr[Complex]) {
			arg.Do(Unfold(ComplexExpDef))
			sizes := arg.Have(
				"the size of the n-th term is the n-th term of ℝ's exponential series at |z|",
				"(λn:num. |z ^ n / complex_of_real(&factorial(n))|) = (λn:num. real_pow(|z|, n) / &factorial(n))",
				Funext(),
				arg.ForEach(func(*Expr[Nat]) Action {
					// the size of a quotient, of an embedded natural number, and of a power
					return Chain(Simp(
						Fwd(complex_abs.AbsDiv),
						Fwd(complex_abs.AbsOfReal),
						Fwd(real_sgn_abs.AbsOfNum),
						Fwd(complex_abs.AbsPow)), Refl())
				}))
			absolute := arg.Have(
				"so the sizes sum to exp |z|",
				"real_sums(λn:num. |z ^ n / complex_of_real(&factorial(n))|, exp(|z|))",
				sizes.Rw(),
				By(real_exp_log.ExpSums.At(arg.TermAs[Real]("|z|"))))
			converges := arg.Have(
				"a series whose sizes have a sum has a sum",
				"∃s:complex. complex_sums(λn:num. z ^ n / complex_of_real(&factorial(n)), s)",
				By(absolute, complex_series.AbsoluteConvergence))
			arg.Show(
				"exp(z) is the choice of such a sum, so it is one",
				By(converges))
		}),
})}

// CosSums — the cosine series sums to cos(z). The size of its n-th term
// is |z|²ⁿ/(2n)!, the even term of ℝ's exponential series at |z|, at most
// that series' n-th pair, and the series of pairs sums to exp|z|; so the
// series has a sum by comparison, and cos(z) is the choice of one.
var CosSums = cosSumsThm{family.Add(registry.ProofEntry{
	Name: "CosSums",
	Key:  "prop_a07187cd53413e94",
	Build: family.Theorem(Statement{
		Binders: "∀z:complex.",
		Conclusion: "complex_sums(λn:num. " +
			"        complex_of_real(real_pow(-&1, n)) * z ^ (2 * n) / complex_of_real(&factorial(2 * n)), " +
			"    cos(z))",
	},
		func(arg *Argument, z *Expr[Complex]) {
			arg.Do(Unfold(ComplexCosDef))
			size := arg.TermAs[Real]("|z|")
			pairs := arg.Have(
				"ℝ's exponential series at |z|, two terms at a time, sums to exp |z|",
				"real_sums(λn:num. "+
					"        real_pow(|z|, 2 * n) / &factorial(2 * n) + "+
					"        real_pow(|z|, 2 * n + 1) / &factorial(2 * n + 1), "+
					"    exp(|z|))",
				By(real_exp_log.ExpSums.At(size), real_series.SumsPair))
			bound := arg.Have(
				"the size of each term is at most the pair: it is "+
					"the pair's first term, the second being nonnegative",
				"∀n:num. "+
					"    |complex_of_real(real_pow(-&1, n)) * z ^ (2 * n) / complex_of_real(&factorial(2 * n))| ≤ "+
					"    real_pow(|z|, 2 * n) / &factorial(2 * n) + real_pow(|z|, 2 * n + 1) / &factorial(2 * n + 1)",
				Derive(func(d *Argument) {
					d.FixAs[Nat]()
					signSize := d.Have(
						"|(−1)ⁿ| = |−1|ⁿ = 1",
						"|real_pow(-&1, n)| = &1",
						Simp(
							Fwd(real_pow.AbsPow),
							Fwd(real_sgn_abs.AbsEven),
							Fwd(real_sgn_abs.AbsOfNum),
							Fwd(real_pow.OnePow)),
						Refl())
					termSize := d.Have(
						"the size of the n-th term is |z|²ⁿ/(2n)!",
						"|«cosTerm»| = «evenSizeTerm»",
						Simp(
							Fwd(complex_abs.AbsDiv),
							Fwd(complex_abs.AbsMul),
							Fwd(complex_abs.AbsPow),
							Fwd(complex_abs.AbsOfReal),
							Fwd(real_sgn_abs.AbsOfNum)),
						ByArith(signSize))
					odd := d.TermAs[Nat]("2 * n + 1")
					second := d.Have(
						"the pair's second term is nonnegative",
						"&0 ≤ «oddSizeTerm»",
						ByArith(
							real_pow.PowNonneg.At(size, odd),
							complex_abs.AbsNonneg.At(z),
							nat_arith.FactorialNonzero.At(odd),
							real_order_ring.OfNumLessThan.At(d.TermAs[Nat]("0"), d.TermAs[Nat]("factorial(2 * n + 1)"))))
					d.Show(
						"so the size is at most the pair",
						ByArith(termSize, second))
				}))
			converges := arg.Have(
				"so the series has a sum, by comparison with the pairs",
				"∃s:complex. "+
					"    complex_sums(λn:num. "+
					"            complex_of_real(real_pow(-&1, n)) * "+
					"            z ^ (2 * n) / "+
					"            complex_of_real(&factorial(2 * n)), "+
					"        s)",
				By(
					bound,
					pairs,
					complex_series.Comparison.At(
						arg.TermAs[Fun[Nat, Complex]](
							"λn:num. complex_of_real(real_pow(-&1, n)) * z ^ (2 * n) / complex_of_real(&factorial(2 * n))"),
						arg.TermAs[Fun[Nat, Real]](
							"λn:num. "+
								"    real_pow(|z|, 2 * n) / &factorial(2 * n) + real_pow(|z|, 2 * n + 1) / &factorial(2 * n + 1)"),
						arg.TermAs[Real]("exp(|z|)"))))
			arg.Show(
				"cos(z) is the choice of such a sum, so it is one",
				By(converges))
		}),
})}

// SinSums — the sine series sums to sin(z), as the cosine series sums to
// cos(z): the size of its n-th term is |z|²ⁿ⁺¹/(2n+1)!, the odd term of
// the same pair.
var SinSums = sinSumsThm{family.Add(registry.ProofEntry{
	Name: "SinSums",
	Key:  "prop_d628ad0a834b29e9",
	Build: family.Theorem(Statement{
		Binders: "∀z:complex.",
		Conclusion: "complex_sums(λn:num. " +
			"        complex_of_real(real_pow(-&1, n)) * " +
			"        z ^ (2 * n + 1) / " +
			"        complex_of_real(&factorial(2 * n + 1)), " +
			"    sin(z))",
	},
		func(arg *Argument, z *Expr[Complex]) {
			arg.Do(Unfold(ComplexSinDef))
			size := arg.TermAs[Real]("|z|")
			pairs := arg.Have(
				"ℝ's exponential series at |z|, two terms at a time, sums to exp |z|",
				"real_sums(λn:num. "+
					"        real_pow(|z|, 2 * n) / &factorial(2 * n) + "+
					"        real_pow(|z|, 2 * n + 1) / &factorial(2 * n + 1), "+
					"    exp(|z|))",
				By(real_exp_log.ExpSums.At(size), real_series.SumsPair))
			bound := arg.Have(
				"the size of each term is at most the pair: it is "+
					"the pair's second term, the first being nonnegative",
				"∀n:num. "+
					"    |complex_of_real(real_pow(-&1, n)) * "+
					"    z ^ (2 * n + 1) / "+
					"    complex_of_real(&factorial(2 * n + 1))| ≤ "+
					"    real_pow(|z|, 2 * n) / &factorial(2 * n) + real_pow(|z|, 2 * n + 1) / &factorial(2 * n + 1)",
				Derive(func(d *Argument) {
					d.FixAs[Nat]()
					signSize := d.Have(
						"|(−1)ⁿ| = |−1|ⁿ = 1",
						"|real_pow(-&1, n)| = &1",
						Simp(
							Fwd(real_pow.AbsPow),
							Fwd(real_sgn_abs.AbsEven),
							Fwd(real_sgn_abs.AbsOfNum),
							Fwd(real_pow.OnePow)),
						Refl())
					termSize := d.Have(
						"the size of the n-th term is |z|²ⁿ⁺¹/(2n+1)!",
						"|«sinTerm»| = «oddSizeTerm»",
						Simp(
							Fwd(complex_abs.AbsDiv),
							Fwd(complex_abs.AbsMul),
							Fwd(complex_abs.AbsPow),
							Fwd(complex_abs.AbsOfReal),
							Fwd(real_sgn_abs.AbsOfNum)),
						ByArith(signSize))
					even := d.TermAs[Nat]("2 * n")
					first := d.Have(
						"the pair's first term is nonnegative",
						"&0 ≤ «evenSizeTerm»",
						ByArith(
							real_pow.PowNonneg.At(size, even),
							complex_abs.AbsNonneg.At(z),
							nat_arith.FactorialNonzero.At(even),
							real_order_ring.OfNumLessThan.At(d.TermAs[Nat]("0"), d.TermAs[Nat]("factorial(2 * n)"))))
					d.Show(
						"so the size is at most the pair",
						ByArith(termSize, first))
				}))
			converges := arg.Have(
				"so the series has a sum, by comparison with the pairs",
				"∃s:complex. "+
					"    complex_sums(λn:num. "+
					"            complex_of_real(real_pow(-&1, n)) * "+
					"            z ^ (2 * n + 1) / "+
					"            complex_of_real(&factorial(2 * n + 1)), "+
					"        s)",
				By(
					bound,
					pairs,
					complex_series.Comparison.At(
						arg.TermAs[Fun[Nat, Complex]](
							"λn:num. "+
								"    complex_of_real(real_pow(-&1, n)) * z ^ (2 * n + 1) / complex_of_real(&factorial(2 * n + 1))"),
						arg.TermAs[Fun[Nat, Real]](
							"λn:num. "+
								"    real_pow(|z|, 2 * n) / &factorial(2 * n) + real_pow(|z|, 2 * n + 1) / &factorial(2 * n + 1)"),
						arg.TermAs[Real]("exp(|z|)"))))
			arg.Show(
				"sin(z) is the choice of such a sum, so it is one",
				By(converges))
		}),
})}
