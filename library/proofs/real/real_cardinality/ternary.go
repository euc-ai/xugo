// ternary.go — the ternary expansion with digits 0 and 1: a set of
// naturals s is read as the real Σ_{n∈s} 3⁻ⁿ, the injection of the sets
// of naturals into ℝ.

package real_cardinality

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// TernaryDigitBounds — each term of the expansion lies between 0 and
// 3⁻ⁿ: it is one or the other.
var TernaryDigitBounds = ternaryDigitBoundsThm{family.Add(registry.ProofEntry{
	Name: "TernaryDigitBounds",
	Key:  "prop_b294242e4812b5f3",
	Build: family.Theorem("∀s:set(num). ∀n:num. "+
		"    &0 ≤ ternary_digits(s, n) ∧ ternary_digits(s, n) ≤ real_pow(real_inv(&3), n)",
		Opening(Unfold(ternaryDigitsDef), func(a *Argument, s *Expr[Set[Nat]], n *Expr[Nat]) {
			nonneg := a.Have(
				"3⁻ⁿ is a power of the positive 3⁻¹, so not negative",
				"&0 ≤ real_pow(real_inv(&3), n)",
				ByArith(real_pow.PowNonneg.At(a.TermAs[Real]("real_inv(&3)"), n)))
			a.Cases(a.Term("n ∈ s"))
			a.When(
				"n ∈ s: the term is 3⁻ⁿ itself",
				func(b *Argument, member Fact) {
					b.Show(
						"between 0 and itself",
						ByArith(Normalized, nonneg, member))
				})
			a.Otherwise(
				"n ∉ s: the term is 0",
				func(b *Argument, notMember Fact) {
					b.Show(
						"between 0 and 3⁻ⁿ",
						ByArith(Normalized, nonneg, notMember))
				})
		})),
})}

// TernaryConverges — by comparison with the geometric series of ratio
// 3⁻¹: each term lies between 0 and 3⁻ⁿ, so is at most 3⁻ⁿ in size,
// and Σ 3⁻ⁿ sums since |3⁻¹| < 1.
var TernaryConverges = ternaryConvergesThm{family.Add(registry.ProofEntry{
	Name: "TernaryConverges",
	Key:  "prop_ef8e3fe41965cfab",
	Build: family.Theorem("∀s:set(num). ∃x:real. real_sums(ternary_digits(s), x)",
		func(a *Argument, s *Expr[Set[Nat]]) {
			third := a.TermAs[Real]("real_inv(&3)")
			bounded := a.Have(
				"each term lies between 0 and 3⁻ⁿ, so is at most 3⁻ⁿ in size",
				"∀n:num. |ternary_digits(s, n)| ≤ real_pow(real_inv(&3), n)",
				a.ForEach(func(n *Expr[Nat]) Action { return ByArith(TernaryDigitBounds.At(s, n)) }))
			geometric := a.Have(
				"|3⁻¹| < 1, so the geometric series of ratio 3⁻¹ sums",
				"real_sums(λn:num. real_pow(real_inv(&3), n), real_inv(&1 - real_inv(&3)))",
				ByArith(real_series.Geometric.At(third)))
			a.Show(
				"the series of s, dominated by it from the first term on, sums by comparison",
				By(bounded, geometric, Where(real_series.Comparison, "N", a.TermAs[Nat]("0"))))
		}),
})}

// TernaryFirstDifference — in a ternary expansion with digits 0 and 1,
// the first place where two expansions differ decides which number is
// larger. Up to that place n the partial sums differ by exactly 3⁻ⁿ.
// Past it the larger expansion only gains, its terms being nonnegative,
// while the smaller gains at most the geometric tail from 3^-(n+1),
// which sums to 3⁻ⁿ/2.
var TernaryFirstDifference = ternaryFirstDifferenceThm{family.Add(registry.ProofEntry{
	Name: "TernaryFirstDifference",
	Key:  "prop_b0b1d1ef6ddbec4d",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(num). ∀x y:real. ∀n:num.",
		Hypotheses: []string{
			"∀k:num. k < n ⇒ (k ∈ s ⇔ k ∈ t)",
			"n ∈ s",
			"n ∉ t",
			"real_sums(ternary_digits(s), x)",
			"real_sums(ternary_digits(t), y)",
		},
		Conclusion: "y < x",
	},
		func(a *Argument, s, t *Expr[Set[Nat]], x, y *Expr[Real], n *Expr[Nat], hyps Fact) {
			parts := a.Conjuncts(
				hyps,
				"below n the digits of s and t agree",
				"n is in s",
				"n is not in t",
				"the series of s sums to x",
				"the series of t sums to y")
			agree, inS, notInT, sumsX, sumsY := parts[0], parts[1], parts[2], parts[3], parts[4]

			third := a.TermAs[Real]("real_inv(&3)")
			seriesS := a.TermAs[Fun[Nat, Real]]("ternary_digits(s)")
			seriesT := a.TermAs[Fun[Nat, Real]]("ternary_digits(t)")
			zero := a.TermAs[Nat]("0")

			termS := a.Have(
				"n being in s, the n-th term of the series of s is 3⁻ⁿ",
				"ternary_digits(s, n) = real_pow(real_inv(&3), n)",
				By(inS, ternaryDigitsDef.At(s, n)))
			termT := a.Have(
				"n not being in t, the n-th term of the series of t is 0",
				"ternary_digits(t, n) = &0",
				By(notInT, ternaryDigitsDef.At(t, n)))
			partial := a.Have(
				"up to n the s-partial sum exceeds the t-partial sum by exactly 3⁻ⁿ",
				"Σ_{k∈0 .. n} ternary_digits(s, k) = Σ_{k∈0 .. n} ternary_digits(t, k) + real_pow(real_inv(&3), n)",
				Derive(func(b *Argument) {
					b.Cases(b.Term("n = 0"))
					b.When(
						"n = 0: each partial sum is its one term, 3⁰ for s and 0 for t",
						func(c *Argument, atZero Fact) {
							c.Show(
								"read both sums over 0 .. 0 as their value at 0",
								ByArith(
									atZero,
									termS,
									termT,
									real_sum.IntervalPoint.At(zero, seriesS),
									real_sum.IntervalPoint.At(zero, seriesT)))
						})
					b.Otherwise(
						"n > 0: peel the n-th term off both sums; below n the terms agree",
						func(c *Argument, nonzero Fact) {
							agreeBelow := c.Have(
								"up to n − 1 the terms of the two series are equal",
								"∀i:num. 0 ≤ i ∧ i ≤ n - 1 ⇒ ternary_digits(s, i) = ternary_digits(t, i)",
								Derive(func(d *Argument) {
									i := d.FixAs[Nat]()
									bounds := d.Assume()
									below := d.Have(
										"an index up to n − 1 lies below n",
										"i < n",
										ByArith(nonzero, bounds))
									d.Show(
										"where s and t agree, and so do their terms",
										By(Normalized, agree.At(i), below, ternaryDigitsDef.At(s, i), ternaryDigitsDef.At(t, i)))
								}))
							same := c.Have(
								"so the partial sums up to n − 1 are equal",
								"Σ_{k∈0 .. n - 1} ternary_digits(s, k) = Σ_{k∈0 .. n - 1} ternary_digits(t, k)",
								By(agreeBelow, real_sum.IntervalCongruence.At(zero, c.TermAs[Nat]("n - 1"), seriesS, seriesT)))
							c.Show(
								"and the n-th term is 3⁻ⁿ for s and 0 for t",
								ByArith(
									same,
									termS,
									termT,
									nonzero,
									real_sum.PeelRight.At(n, zero, seriesS),
									real_sum.PeelRight.At(n, zero, seriesT)))
						})
				}))

			xAbove := a.Have(
				"x is at least its partial sum up to n, no term of the series of s being negative",
				"Σ_{k∈0 .. n} ternary_digits(s, k) ≤ x",
				By(sumsX, TernaryDigitBounds, real_series.SumsPartialLessEq.At(seriesS, x, n)))

			yBelow := a.Have(
				"y exceeds its partial sum up to n by at most 3⁻ⁿ/2",
				"y - Σ_{k∈0 .. n} ternary_digits(t, k) ≤ real_pow(real_inv(&3), n) / &2",
				Derive(func(b *Argument) {
					next := b.TermAs[Nat]("n + 1")
					tail := b.Have(
						"the series of t past n sums to y less the partial sum up to n",
						"real_sums(λk:num. ternary_digits(t, k + n + 1), y - Σ_{k∈0 .. n} ternary_digits(t, k))",
						By(sumsY, real_series.SumsOffset.At(seriesT, y, n)))
					inverse := b.Have(
						"(1 − 3⁻¹)·(3/2) = 1, so (1 − 3⁻¹)⁻¹ = 3/2",
						"real_inv(&1 - real_inv(&3)) = &3 / &2",
						ByArith(field.InvRightUnique.Read(real_field.Field).At(
							b.TermAs[Real]("&1 - real_inv(&3)"), b.TermAs[Real]("&3 / &2"))))
					geometric := b.Have(
						"|3⁻¹| < 1, so the geometric series of ratio 3⁻¹ sums to (1 − 3⁻¹)⁻¹ = 3/2",
						"real_sums(λk:num. real_pow(real_inv(&3), k), &3 / &2)",
						ByArith(inverse, real_series.Geometric.At(third)))
					value := b.Have(
						"3^-(n+1)·(3/2) = 3⁻ⁿ/2: the next power is a third of 3⁻ⁿ",
						"real_pow(real_inv(&3), n + 1) * (&3 / &2) = real_pow(real_inv(&3), n) / &2",
						Simp(Fwd(real_pow.PowAddOne)),
						ByArith())
					scaled := b.Have(
						"so the geometric series from 3^-(n+1) sums to 3⁻ⁿ/2",
						"real_sums(λk:num. real_pow(real_inv(&3), n + 1) * real_pow(real_inv(&3), k), "+
							"    real_pow(real_inv(&3), n) / &2)",
						By(
							geometric,
							value,
							real_series.SumsScale.At(
								b.TermAs[Fun[Nat, Real]]("λk:num. real_pow(real_inv(&3), k)"), b.TermAs[Real]("&3 / &2"),
								b.TermAs[Real]("real_pow(real_inv(&3), n + 1)"))))
					termwise := b.Have(
						"term by term the series of t past n is at most that geometric series",
						"∀k:num. ternary_digits(t, k + n + 1) ≤ real_pow(real_inv(&3), n + 1) * real_pow(real_inv(&3), k)",
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]()
							exponent := c.Have(
								"the exponent k + n + 1 is (n + 1) + k",
								"k + n + 1 = n + 1 + k",
								ByArith())
							split := c.Have(
								"so 3^-(k+n+1) splits as 3^-(n+1)·3⁻ᵏ",
								"real_pow(real_inv(&3), k + n + 1) = real_pow(real_inv(&3), n + 1) * real_pow(real_inv(&3), k)",
								exponent.Rw(),
								Cite(real_pow.PowAdd, third, next, k))
							c.Show(
								"and the (k + n + 1)-th term of the series of t is at most 3^-(k+n+1)",
								ByArith(split, TernaryDigitBounds.At(t, c.TermAs[Nat]("k + n + 1"))))
						}))
					b.Show(
						"a series termwise below another sums to no more",
						By(termwise, tail, scaled, real_series.SumsLessEq))
				}))

			a.Show(
				"x is at least the t-partial sum plus 3⁻ⁿ, y at most that sum plus 3⁻ⁿ/2, and 3⁻ⁿ > 0",
				ByArith(partial, xAbove, yBelow, real_pow.PowPos.At(third, n)))
		}),
})}

// TernaryInjective — two different sets of naturals differ somewhere,
// hence at a least place n, below which they agree. Whichever of them
// holds n then has, by the first-difference comparison, the strictly
// larger ternary sum — so the two sums cannot both be x.
var TernaryInjective = ternaryInjectiveThm{family.Add(registry.ProofEntry{
	Name: "TernaryInjective",
	Key:  "prop_e035baceeaacd7ea",
	Build: family.Theorem(Statement{
		Binders: "∀s t:set(num). ∀x:real.",
		Hypotheses: []string{
			"real_sums(ternary_digits(s), x)",
			"real_sums(ternary_digits(t), x)",
		},
		Conclusion: "s = t",
	},
		func(a *Argument, s, t *Expr[Set[Nat]], x *Expr[Real], sums Fact) {
			different := a.SupposeNot()
			differsAt := a.TermAs[Set[Nat]]("λk:num. ¬(k ∈ s ⇔ k ∈ t)")
			somewhere := a.Have(
				"different sets differ at some place",
				"∃k:num. ¬(k ∈ s ⇔ k ∈ t)",
				By(different, set_basic.Extension))
			n, least := a.ObtainAs[Nat](
				"hence at a least place n, below which they agree",
				"∃n:num. ¬(n ∈ s ⇔ n ∈ t) ∧ (∀k:num. k < n ⇒ (k ∈ s ⇔ k ∈ t))",
				By(somewhere, nat_order.WellOrdering.At(differsAt)))
			a.Cases(a.Term("n ∈ s"))
			a.When(
				"n ∈ s, n ∉ t: the expansion of s, with the 1 at n, sums to more than that of t",
				func(b *Argument, inS Fact) {
					b.Show(
						"so x < x, which no number is",
						By(
							Normalized,
							inS,
							least,
							sums,
							TernaryFirstDifference.At(s, t, x, x, n),
							real_order_ring.LessThanIrrefl.At(x)))
				})
			a.Otherwise(
				"n ∈ t, n ∉ s: the expansion of t, with the 1 at n, sums to more than that of s",
				func(b *Argument, notInS Fact) {
					agree := b.Have(
						"below n, t and s agree",
						"∀k:num. k < n ⇒ (k ∈ t ⇔ k ∈ s)",
						By(least))
					b.Show(
						"so x < x again",
						By(
							Normalized,
							notInS,
							agree,
							least,
							sums,
							TernaryFirstDifference.At(t, s, x, x, n),
							real_order_ring.LessThanIrrefl.At(x)))
				})
		}),
})}

// PowersetNumLeReal — send each set of naturals to the sum of its
// ternary expansion, the value ε chooses among the sums of that series.
// The series has a sum (TernaryConverges), so the chosen value is one;
// two sets sent to one value then have expansions with a common sum,
// and are one set (TernaryInjective). This is the half of |ℝ| = |P(ℕ)|
// that makes ℝ uncountable.
var PowersetNumLeReal = powersetNumLeRealThm{family.Add(registry.ProofEntry{
	Name: "PowersetNumLeReal",
	Key:  "prop_289de710551e991a",
	Build: family.Theorem("card_le(𝕌⟨A:set(num)⟩, 𝕌⟨A:real⟩)",
		Opening(Chain(Unfold(cardinal.CardLeDef), Unfold(functions.InjectiveOnDef)), func(a *Argument) {
			a.Take(a.TermAs[Fun[Set[Nat], Real]]("λs:set(num). εx:real. real_sums(ternary_digits(s), x)"))
			chosenSums := a.Have(
				"each expansion has a sum, so the value chosen among its sums is one",
				"∀s:set(num). real_sums(ternary_digits(s), εx:real. real_sums(ternary_digits(s), x))",
				By(TernaryConverges))
			a.Show(
				"every value is a real, and two sets sent to one "+
					"value have expansions summing to it, so are one set",
				Simp(Fwd(set_basic.InUniv.Inst[Real]())),
				By(chosenSums, TernaryInjective))
		})),
})}
