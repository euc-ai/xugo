// estimates.go — the cosine and the sine between their Taylor
// polynomials, from the alternating-series bound, and what they give:
// cos 2 < 0, sin x > 0 on ⟬0, 2⟭, and the bounds near 0.

package real_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// CosTaylorBounds — for |x| ≤ 2 the cosine lies between its Taylor
// polynomials of degrees 2 and 4. Past its first two terms, 1 and
// −x²/2, the cosine series is the alternating series of the terms
// x²⁽ⁿ⁺²⁾/(2(n + 2))!, and these do not increase: x²ᵏ⁺²/(2k + 2)! is
// x²ᵏ/(2k)! times x²/((2k + 1)(2k + 2)), at most 1 since
// x² ≤ 4 ≤ (2k + 1)(2k + 2) once k ≥ 1. By the alternating-series bound
// what the series has left, cos x − (1 − x²/2), lies between 0 and the
// first of those terms, x⁴/4! = x⁴/24.
var CosTaylorBounds = cosTaylorBoundsThm{family.Add(registry.ProofEntry{
	Name: "CosTaylorBounds",
	Key:  "prop_86f8eb8a50d39a7f",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"|x| ≤ &2",
		},
		Conclusion: "&1 - real_pow(x, 2) / &2 ≤ cos(x) ∧ " +
			"cos(x) ≤ &1 - real_pow(x, 2) / &2 + real_pow(x, 4) / &24",
		Abbrev: Abbrev{
			{Name: "term", Text: "real_pow(x, 2 * k) / &factorial(2 * k)"},
			{Name: "nextTerm", Text: "real_pow(x, 2 * (k + 1)) / &factorial(2 * (k + 1))"},
			{Name: "remainder", Text: "cos(x) - (&1 - real_pow(x, 2) / &2)"},
		},
	},
		func(arg *Argument, x *Expr[Real], near Fact) {
			absX, two := arg.TermAs[Real]("|x|"), arg.TermAs[Real]("&2")
			unsigned := arg.Have(
				"a square forgets the sign: x² = |x|² = |x|·|x|",
				"real_pow(x, 2) = |x| * |x|",
				By(Normalized, real_pow.SquareOfAbs.At(x), real_pow.PowTwo.At(absX)))
			sizes := arg.Have(
				"|x| ≤ 2 times itself, |x| being nonnegative",
				"|x| * |x| ≤ &2 * &2",
				By(near, real_sgn_abs.AbsNonneg.At(x), real_order_ring.LessEqMul2.At(absX, two, absX, two)))
			square := arg.Have(
				"so x² ≤ 4",
				"real_pow(x, 2) ≤ &4",
				ByArith(unsigned, sizes))

			terms := arg.Have(
				"each x²ᵏ/(2k)! is nonnegative, an even power over a positive factorial",
				"∀k:num. &0 ≤ real_pow(x, 2 * k) / &factorial(2 * k)",
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					d.Show(
						"x²ᵏ = (x²)ᵏ with x² ≥ 0, and (2k)! ≠ 0",
						ByArith(
							real_pow.PowTwoNonneg.At(x),
							real_pow.PowNonneg.At(d.TermAs[Real]("real_pow(x, 2)"), k),
							real_pow.PowPow.At(x, d.TermAs[Nat]("2"), k),
							nat_arith.FactorialNonzero.At(d.TermAs[Nat]("2 * k")),
							real_order_ring.OfNumLessThan.At(d.TermAs[Nat]("0"), d.TermAs[Nat]("factorial(2 * k)"))))
				}))

			ratio := arg.Have(
				"x²ᵏ⁺²/(2k + 2)! is x²ᵏ/(2k)! times x²/((2k + 1)(2k + 2)), so, "+
					"the terms being nonnegative, no larger once k ≥ 1, as x² ≤ 4",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"1 ≤ k",
					},
					Conclusion: "real_pow(x, 2 * (k + 1)) / &factorial(2 * (k + 1)) ≤ " +
						"real_pow(x, 2 * k) / &factorial(2 * k)",
				},
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					past := d.Assume()
					index := d.Have(
						"the index 2(k + 1) is two steps past 2k",
						"2 * (k + 1) = suc(suc(2 * k))",
						ByArith())
					factorials := d.Have(
						"so (2k + 2)! = (2k + 2)·(2k + 1)·(2k)!",
						"factorial(2 * (k + 1)) = (2 * k + 1) * (2 * k + 2) * factorial(2 * k)",
						index.Rw(),
						Simp(Fwd(nat_arith.Factorial)),
						ByArith())
					powers := d.Have(
						"and x²ᵏ⁺² = x·x·x²ᵏ",
						"real_pow(x, 2 * (k + 1)) = x * x * real_pow(x, 2 * k)",
						index.Rw(),
						Simp(Fwd(real_pow.PowExpSucClause)),
						ByArith())
					next := d.Have(
						"so the next term is x²/((2k + 1)(2k + 2)) times this one",
						"«nextTerm» = x * x / &((2 * k + 1) * (2 * k + 2)) * («term»)",
						powers.Rw(),
						factorials.Rw(),
						// the embedding and the reciprocal split over the products
						Simp(
							Fwd(real_construction.OfNumMul),
							Fwd(real_field.RealDivDef),
							Fwd(field.InvMul.Read(real_field.Field))),
						ByArith())
					atMostOne := d.Have(
						"the ratio is at most 1: x² ≤ 4 ≤ (2k + 1)(2k + 2) as k ≥ 1",
						"x * x / &((2 * k + 1) * (2 * k + 2)) ≤ &1",
						ByArith(
							past,
							square,
							real_construction.OfNumLessEq.At(d.TermAs[Nat]("4"), d.TermAs[Nat]("(2 * k + 1) * (2 * k + 2)"))))
					d.Show(
						"a nonnegative term times a ratio at most 1 is at most itself",
						next.Rw(),
						ByArith(atMostOne, terms.At(k)))
				}))
			decreasing := arg.Have(
				"so the terms from k = 2 on are nonnegative and do not increase",
				"∀n:num. "+
					"    &0 ≤ real_pow(x, 2 * (n + 1 + 1)) / &factorial(2 * (n + 1 + 1)) ∧ "+
					"    real_pow(x, 2 * (n + 1 + 1 + 1)) / &factorial(2 * (n + 1 + 1 + 1)) ≤ "+
					"    real_pow(x, 2 * (n + 1 + 1)) / &factorial(2 * (n + 1 + 1))",
				Derive(func(d *Argument) {
					d.FixAs[Nat]()
					index := d.TermAs[Nat]("n + 1 + 1")
					d.Show(
						"the term at k = n + 2 is nonnegative, and the next is no larger",
						ByArith(terms.At(index), ratio.At(index)))
				}))

			alternating := arg.Have(
				"dropping the first two terms, 1 and −x²/2, leaves the "+
					"alternating series of the rest, summing to cos x − (1 − x²/2)",
				"real_sums( "+
					"    λn:num. real_pow(-&1, n) * (real_pow(x, 2 * (n + 1 + 1)) / &factorial(2 * (n + 1 + 1))), "+
					"    «remainder»)",
				Derive(func(d *Argument) {
					series := d.TermAs[Fun[Nat, Real]](
						"λn:num. real_pow(-&1, n) * real_pow(x, 2 * n) / &factorial(2 * n)")
					zero, one := d.TermAs[Nat]("0"), d.TermAs[Nat]("1")
					remainder := d.Have(
						"the first two terms contribute 1 − x²/2, leaving the cosine remainder",
						"cos(x) - Σ_{k∈0 .. 1} (real_pow(-&1, k) * real_pow(x, 2 * k) / &factorial(2 * k)) = «remainder»",
						ByArith(real_sum.PeelRight.At(one, zero, series), real_sum.IntervalPoint.At(zero, series)))
					tail := d.Have(
						"dropping those two terms leaves the series from index 2, summing to the remainder",
						"real_sums(λn:num. "+
							"        real_pow(-&1, n + 1 + 1) * real_pow(x, 2 * (n + 1 + 1)) / &factorial(2 * (n + 1 + 1)), "+
							"    «remainder»)",
						By(remainder, CosSums.At(x), real_series.SumsOffset.At(series, d.TermAs[Real]("cos(x)"), one)))
					termwise := d.Have(
						"whose terms are (−1)ⁿ times x²⁽ⁿ⁺²⁾/(2(n + 2))!, as (−1)ⁿ⁺² = −(−(−1)ⁿ) = (−1)ⁿ",
						"(λn:num. "+
							"    real_pow(-&1, n + 1 + 1) * real_pow(x, 2 * (n + 1 + 1)) / &factorial(2 * (n + 1 + 1))) = "+
							"(λn:num. real_pow(-&1, n) * (real_pow(x, 2 * (n + 1 + 1)) / &factorial(2 * (n + 1 + 1))))",
						Funext(),
						d.ForEach(func(*Expr[Nat]) Action {
							return Chain(Simp(
								Fwd(real_pow.PowAddOne),
								Fwd(real_ring.NegMinusOne),
								Fwd(real_ring.NegNeg)), ByArith())
						}))
					d.Show(
						"so the rest is the alternating series of those terms",
						termwise.RwRev(),
						By(tail))
				}))

			between := arg.Have(
				"by the alternating-series bound cos x − (1 − x²/2) lies between 0 and the first term of the rest",
				"&0 ≤ «remainder» ∧ «remainder» ≤ real_pow(x, 2 * (0 + 1 + 1)) / &factorial(2 * (0 + 1 + 1))",
				By(
					decreasing,
					alternating,
					real_series.AlternatingBound.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(x, 2 * (n + 1 + 1)) / &factorial(2 * (n + 1 + 1))"),
						arg.TermAs[Real]("«remainder»"))))
			arg.Show(
				"and that term is x⁴/4! = x⁴/24",
				ByArith(between))
		}),
})}

// SinTaylorBounds — on ⟦0, 2⟧ the sine lies between its Taylor
// polynomials of degrees 3 and 1. Dropping the first term x of the sine
// series and changing sign leaves the alternating series of the terms
// x²ⁿ⁺³/(2n + 3)!, which sums to x − sin x. For 0 ≤ x ≤ 2 those terms
// are nonnegative and do not increase: each is the one before times
// x²/((2n+4)(2n+5)), and x² ≤ 4. So the alternating-series bound puts
// x − sin x between 0 and the first of them, x³/3! = x³/6.
var SinTaylorBounds = sinTaylorBoundsThm{family.Add(registry.ProofEntry{
	Name: "SinTaylorBounds",
	Key:  "prop_b55b99893ddd8c2",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"x ≤ &2",
		},
		Conclusion: "x - real_pow(x, 3) / &6 ≤ sin(x) ∧ sin(x) ≤ x",
		Abbrev: Abbrev{
			{Name: "term", Text: "real_pow(x, 2 * k + 1) / &factorial(2 * k + 1)"},
			{Name: "nextTerm", Text: "real_pow(x, 2 * (k + 1) + 1) / &factorial(2 * (k + 1) + 1)"},
			{Name: "firstTerm", Text: "real_pow(-&1, 0) * real_pow(x, 2 * 0 + 1) / &factorial(2 * 0 + 1)"},
		},
	},
		func(arg *Argument, x *Expr[Real], bounds Fact) {
			// The unsigned term x²ᵏ⁺¹/(2k + 1)! and the next one; the
			// series' first term and its terms without it; and the unsigned
			// terms from k = 1 on and the next one.
			const (
				term        = "real_pow(x, 2 * k + 1) / &factorial(2 * k + 1)"
				nextTerm    = "real_pow(x, 2 * (k + 1) + 1) / &factorial(2 * (k + 1) + 1)"
				shiftedOnce = "real_pow(-&1, n + 1) * real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1)"
				tailTerm    = "real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1)"
				tailNext    = "real_pow(x, 2 * (n + 1 + 1) + 1) / &factorial(2 * (n + 1 + 1) + 1)"
			)

			parts := arg.Conjuncts(
				bounds,
				"x is nonnegative",
				"x is at most 2")
			nonnegative, atMostTwo := parts[0], parts[1]

			terms := arg.Have(
				"for x ≥ 0 each x²ᵏ⁺¹/(2k + 1)! is nonnegative",
				"∀k:num. &0 ≤ real_pow(x, 2 * k + 1) / &factorial(2 * k + 1)",
				Derive(func(d *Argument) {
					d.FixAs[Nat]()
					odd := d.TermAs[Nat]("2 * k + 1")
					d.Show(
						"a power of x ≥ 0 over the positive (2k + 1)!",
						ByArith(
							nonnegative,
							real_pow.PowNonneg.At(x, odd),
							nat_arith.FactorialNonzero.At(odd),
							real_order_ring.OfNumLessThan.At(d.TermAs[Nat]("0"), d.TermAs[Nat]("factorial(2 * k + 1)"))))
				}))

			ratio := arg.Have(
				"x²ᵏ⁺³/(2k + 3)! is x²ᵏ⁺¹/(2k + 1)! times x²/((2k + 2)(2k + 3)), so, "+
					"the terms being nonnegative, no larger where x² ≤ (2k + 2)(2k + 3)",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"x * x ≤ &((2 * k + 2) * (2 * k + 3))",
					},
					Conclusion: "real_pow(x, 2 * (k + 1) + 1) / &factorial(2 * (k + 1) + 1) ≤ " +
						"real_pow(x, 2 * k + 1) / &factorial(2 * k + 1)",
				},
				Derive(func(d *Argument) {
					k := d.FixAs[Nat]()
					small := d.Assume()
					index := d.Have(
						"the index 2(k + 1) + 1 is two steps past 2k + 1",
						"2 * (k + 1) + 1 = suc(suc(2 * k + 1))",
						ByArith())
					factorials := d.Have(
						"so (2k + 3)! = (2k + 3)·(2k + 2)·(2k + 1)!",
						"factorial(2 * (k + 1) + 1) = (2 * k + 2) * (2 * k + 3) * factorial(2 * k + 1)",
						index.Rw(),
						Simp(Fwd(nat_arith.Factorial)),
						ByArith())
					powers := d.Have(
						"and x²ᵏ⁺³ = x·x·x²ᵏ⁺¹",
						"real_pow(x, 2 * (k + 1) + 1) = x * x * real_pow(x, 2 * k + 1)",
						index.Rw(),
						Simp(Fwd(real_pow.PowExpSucClause)),
						ByArith())
					next := d.Have(
						"so the next term is x²/((2k + 2)(2k + 3)) times this one",
						"«nextTerm» = x * x / &((2 * k + 2) * (2 * k + 3)) * («term»)",
						powers.Rw(),
						factorials.Rw(),
						// the embedding and the reciprocal split over the products
						Simp(
							Fwd(real_construction.OfNumMul),
							Fwd(real_field.RealDivDef),
							Fwd(field.InvMul.Read(real_field.Field))),
						ByArith())
					positive := d.Have(
						"(2k + 2)(2k + 3) is positive",
						"&0 < &((2 * k + 2) * (2 * k + 3))",
						ByArith(
							real_order_ring.OfNumLessThan.At(d.TermAs[Nat]("0"), d.TermAs[Nat]("(2 * k + 2) * (2 * k + 3)"))))
					atMostOne := d.Have(
						"so the ratio is at most 1",
						"x * x / &((2 * k + 2) * (2 * k + 3)) ≤ &1",
						ByArith(small, positive))
					d.Show(
						"a nonnegative term times a ratio at most 1 is at most itself",
						next.Rw(),
						ByArith(atMostOne, terms.At(k)))
				}))

			two := arg.TermAs[Real]("&2")
			square := arg.Have(
				"x² ≤ 2·2 = 4",
				"x * x ≤ &4",
				By(nonnegative, atMostTwo, real_order_ring.LessEqMul2.At(x, two, x, two)))
			decreasing := arg.Have(
				"so the terms from k = 1 on are nonnegative and do not increase: x² ≤ 4 ≤ (2n + 4)(2n + 5)",
				"∀n:num. "+
					"    &0 ≤ real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1) ∧ "+
					"    real_pow(x, 2 * (n + 1 + 1) + 1) / &factorial(2 * (n + 1 + 1) + 1) ≤ "+
					"    real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1)",
				Derive(func(d *Argument) {
					d.FixAs[Nat]()
					index := d.TermAs[Nat]("n + 1")
					large := d.Have(
						"4 ≤ (2n + 4)(2n + 5) in ℕ, and so in ℝ",
						"&4 ≤ &((2 * (n + 1) + 2) * (2 * (n + 1) + 3))",
						ByArith(real_construction.OfNumLessEq.At(
							d.TermAs[Nat]("4"), d.TermAs[Nat]("(2 * (n + 1) + 2) * (2 * (n + 1) + 3)"))))
					d.Show(
						"the term at k = n + 1 is nonnegative, and the ratio from it to the next is at most 1",
						ByArith(terms.At(index), ratio.At(index), square, large))
				}))

			alternating := arg.Have(
				"dropping the first term x and changing sign leaves the "+
					"alternating series of the rest, summing to x − sin x",
				"real_sums( "+
					"    λn:num. real_pow(-&1, n) * (real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1)), "+
					"    x - sin(x))",
				Derive(func(d *Argument) {
					series := d.TermAs[Fun[Nat, Real]](
						"λn:num. real_pow(-&1, n) * real_pow(x, 2 * n + 1) / &factorial(2 * n + 1)")
					shifted := d.Have(
						"without its first term the sine series sums to sin x less that term",
						"real_sums( "+
							"    λn:num. real_pow(-&1, n + 1) * real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1), "+
							"    sin(x) - «firstTerm»)",
						By(SinSums.At(x), real_series.SumsShift.At(series, d.TermAs[Real]("sin(x)"))))
					negated := d.Have(
						"and its negative to −1 times that",
						"real_sums(λn:num. "+
							"        -&1 * "+
							"        (real_pow(-&1, n + 1) * real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1)), "+
							"    -&1 * (sin(x) - «firstTerm»))",
						By(
							shifted,
							real_series.SumsScale.At(
								d.TermAs[Fun[Nat, Real]](
									"λn:num. real_pow(-&1, n + 1) * real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1)"),
								d.TermAs[Real]("sin(x) - «firstTerm»"),
								d.TermAs[Real]("-&1"))))
					termwise := d.Have(
						"whose terms −1·(−1)ⁿ⁺¹·x²ⁿ⁺³/(2n + 3)! are (−1)ⁿ·x²ⁿ⁺³/(2n + 3)!",
						"(λn:num. "+
							"    -&1 * "+
							"    (real_pow(-&1, n + 1) * real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1))) = "+
							"(λn:num. real_pow(-&1, n) * (real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1)))",
						Funext(),
						d.ForEach(func(*Expr[Nat]) Action { return Chain(Simp(Fwd(real_pow.PowAddOne)), ByArith()) }))
					value := d.Have(
						"and whose sum is x − sin x, the first term (−1)⁰·x¹/1! being x",
						"-&1 * (sin(x) - «firstTerm») = x - sin(x)",
						ByArith())
					d.Show(
						"so the alternating series of the rest sums to x − sin x",
						termwise.RwRev(),
						By(negated, value))
				}))

			between := arg.Have(
				"by the alternating-series bound x − sin x lies between 0 and the first term of the rest",
				"&0 ≤ x - sin(x) ∧ x - sin(x) ≤ real_pow(x, 2 * (0 + 1) + 1) / &factorial(2 * (0 + 1) + 1)",
				By(
					decreasing,
					alternating,
					real_series.AlternatingBound.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(x, 2 * (n + 1) + 1) / &factorial(2 * (n + 1) + 1)"),
						arg.TermAs[Real]("x - sin(x)"))))
			arg.Show(
				"and that term is x³/3! = x³/6",
				ByArith(between))
		}),
})}

// CosTwoNegative — the cosine is negative at 2: the Taylor bound at 2
// puts cos 2 at most 1 − 4/2 + 16/24 = −1/3.
var CosTwoNegative = cosTwoNegativeThm{family.Add(registry.ProofEntry{
	Name: "CosTwoNegative",
	Key:  "prop_f36cd542c41ed9d3",
	Build: family.Theorem("cos(&2) < &0",
		func(arg *Argument) {
			arg.Show(
				"cos 2 ≤ 1 − 2²/2 + 2⁴/24 = −1/3",
				ByArith(CosTaylorBounds.At(arg.TermAs[Real]("&2"))))
		}),
})}

// SinPositive — the sine is positive on ⟬0, 2⟭: by the Taylor bound it
// is at least x − x³/6, and x³ = x·x² < 4x there.
var SinPositive = sinPositiveThm{family.Add(registry.ProofEntry{
	Name: "SinPositive",
	Key:  "prop_ca64bcbb899eea13",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 < x",
			"x < &2",
		},
		Conclusion: "&0 < sin(x)",
	},
		func(arg *Argument, x *Expr[Real], between Fact) {
			two, square := arg.TermAs[Real]("&2"), arg.TermAs[Real]("x * x")
			arg.Show(
				"sin x ≥ x − x³/6, and x·x < 2·2 makes x³ = x·(x·x) < 4x, so x − x³/6 > x/3 > 0",
				ByArith(
					between,
					SinTaylorBounds.At(x),
					real_order_ring.LessThanMul2.At(x, two, x, two),
					real_order_ring.LessThanMulLeft.At(x, square, arg.TermAs[Real]("&4"))))
		}),
})}

// CosQuadraticBound — near 0 the cosine is 1 to within h²: it is at
// least 1 − h²/2 by the Taylor bound and at most 1, as every value of
// the cosine is.
var CosQuadraticBound = cosQuadraticBoundThm{family.Add(registry.ProofEntry{
	Name: "CosQuadraticBound",
	Key:  "prop_f8eb70fd7b17dce5",
	Build: family.Theorem(Statement{
		Binders: "∀h:real.",
		Hypotheses: []string{
			"|h| ≤ &1",
		},
		Conclusion: "|cos(h) - &1| ≤ real_pow(h, 2)",
	},
		func(arg *Argument, h *Expr[Real], near Fact) {
			arg.Show(
				"1 − h²/2 ≤ cos h ≤ 1, and h²/2 ≤ h²",
				ByArith(near, CosTaylorBounds.At(h), CosAbsLessEqOne.At(h), real_pow.PowTwoNonneg.At(h)))
		}),
})}

// SinQuadraticBound — near 0 the sine is h to within h². For 0 ≤ t ≤ 1
// the Taylor bound puts sin t − t between −t³/6 and 0, and t³ = t·t² is
// at most t²; the sine is odd, so a negative h is −t with the same
// bound.
var SinQuadraticBound = sinQuadraticBoundThm{family.Add(registry.ProofEntry{
	Name: "SinQuadraticBound",
	Key:  "prop_eddf5ad2f0771592",
	Build: family.Theorem(Statement{
		Binders: "∀h:real.",
		Hypotheses: []string{
			"|h| ≤ &1",
		},
		Conclusion: "|sin(h) - h| ≤ real_pow(h, 2)",
	},
		func(arg *Argument, h *Expr[Real], near Fact) {
			one := arg.TermAs[Real]("&1")
			onRight := arg.Have(
				"for 0 ≤ t ≤ 1, sin t − t lies between −t³/6 and 0, and t³ = t·t² ≤ t²",
				"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ -real_pow(t, 2) ≤ sin(t) - t ∧ sin(t) - t ≤ real_pow(t, 2)",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]()
					within := d.Assume()
					d.Show(
						"the Taylor bound, with t·t² ≤ 1·t²",
						ByArith(
							within,
							SinTaylorBounds.At(t),
							real_pow.PowTwoNonneg.At(t),
							real_order_ring.LessEqMulRight.At(t, one, d.TermAs[Real]("real_pow(t, 2)"))))
				}))
			negative := arg.Unless(
				arg.Term("&0 ≤ h"),
				"a nonnegative h is such a t",
				Given(func(b *Argument, nonneg Fact) {
					b.Show(
						"the bound on the right",
						ByArith(near, nonneg, onRight.At(h)))
				}))
			arg.Show(
				"a negative h is −t for t = −h ≤ 1, where (−h)² = h², and sin(−h) − (−h) = −(sin h − h)",
				ByArith(near, negative, SinNeg.At(h), onRight.At(arg.TermAs[Real]("-h"))))
		}),
})}
