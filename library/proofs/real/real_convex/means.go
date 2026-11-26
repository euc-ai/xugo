// means.go — the inequality of arithmetic and geometric means, equally
// weighted and weighted, read from Jensen's inequality for −log, the
// logarithm of a product of positive reals being the sum of the
// logarithms.

package real_convex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// AmGm — the inequality of arithmetic and geometric means, in power form:
// for nonnegative x(1), …, x(n), their product is at most the n-th power
// of their mean. With n = 0 both sides are 1; with a vanishing term the
// product is 0 and the power of the nonnegative mean is not below it.
// Otherwise every term is positive, and Jensen's inequality for −log at
// the weights 1/n says the mean of the logarithms is at most the
// logarithm of the mean; the mean of the logarithms is the logarithm of
// the product divided by n, so log(product) ≤ log(mean^n), and the
// logarithm increases.
var AmGm = amGmThm{family.Add(registry.ProofEntry{
	Name: "AmGm",
	Key:  "prop_52eb1615e4c241da",
	Build: family.Theorem(Statement{
		Binders: "∀x:num → real. ∀n:num.",
		Hypotheses: []string{
			"∀i:num. i ∈ 1 .. n ⇒ &0 ≤ x(i)",
		},
		Conclusion: "Π_{i∈1 .. n} x(i) ≤ real_pow(«mean», n)",
		Abbrev: Abbrev{
			{Name: "mean", Text: "(Σ_{i∈1 .. n} x(i)) / &n"},
		},
	}, func(a *Argument, x *Expr[Fun[Nat, Real]], n *Expr[Nat], nonneg Fact) {
		one := a.TermAs[Nat]("1")
		segment := a.TermAs[Set[Nat]]("1 .. n")
		mean := a.TermAs[Real]("«mean»")
		a.Cases(a.Term("0 < n"))
		a.Otherwise(
			"n = 0: the empty product and the zeroth power are both 1",
			func(b *Argument, notPositive Fact) {
				zero := b.Have(
					"n is zero",
					"n = 0",
					ByArith(notPositive))
				b.Do(zero.Rw())
				empty := b.Have(
					"the segment 1 .. 0 is empty",
					"1 .. 0 = ∅",
					By(num_segment.Empty.At(one, b.TermAs[Nat]("0"))),
				)
				b.Show(
					"1 ≤ 1",
					empty.Rw(),
					Simp(Fwd(real_product.ProductClauses), Fwd(real_pow.PowExpZeroClause)),
					ByArith(),
				)
			})
		a.When(
			"n > 0",
			func(b *Argument, positiveCount Fact) {
				count := b.Have(
					"so &n is positive",
					"&0 < &n",
					ByArith(positiveCount))
				b.Cases(b.Term("∀i:num. i ∈ 1 .. n ⇒ &0 < x(i)"))
				b.Otherwise(
					"some term vanishes: the product is 0, and the mean is nonnegative",
					func(c *Argument, notAll Fact) {
						j, notPositive := c.ObtainAs[Nat](
							"some term x(j) is not positive",
							"∃j:num. j ∈ 1 .. n ∧ ¬(&0 < x(j))",
							By(Normalized, notAll),
						)
						at := c.Conjuncts(
							notPositive,
							"j lies in 1 .. n",
							"x(j) is not positive")
						vanishes := c.Have(
							"x(j) = 0",
							"x(j) = &0",
							ByArith(nonneg.At(j), at[0], at[1]))
						product := c.Have(
							"so the product is 0",
							"Π_{i∈1 .. n} x(i) = &0",
							By(real_product.ProductZero.At(segment, x, j), num_segment.Finite.At(one, n), at[0], vanishes),
						)
						total := c.Have(
							"the terms sum to at least 0",
							"&0 ≤ Σ_{i∈1 .. n} x(i)",
							By(real_sum.Nonneg.At(segment, x), nonneg),
						)
						meanNonneg := c.Have(
							"so does their mean",
							"&0 ≤ «mean»",
							ByArith(total, count))
						c.Show(
							"a power of a nonnegative number is nonnegative",
							ByArith(product, real_pow.PowNonneg.At(mean, n), meanNonneg),
						)
					})
				b.When(
					"every term is positive: Jensen's inequality for −log at the weights 1/n",
					func(c *Argument, positive Fact) {
						weight := c.TermAs[Real]("&1 / &n")
						weights := c.Have(
							"the weights 1/n are nonnegative, and the terms positive reals",
							"∀i:num. i ∈ 1 .. n ⇒ &0 ≤ &1 / &n ∧ x(i) ∈ {y:real | &0 < y}",
							c.ForEach(func(i *Expr[Nat]) Action {
								return ByArith(count, positive.At(i))
							}),
						)
						unit := c.Have(
							"n weights 1/n total one",
							"Σ_{i∈1 .. n} &1 / &n = &1",
							ByArith(real_sum.IntervalConst.At(weight, n, one), count),
						)
						positives := c.Have(
							"the positive reals form an interval",
							"real_interval({y:real | &0 < y})",
							Unfold(real_topology.RealIntervalDef),
							ByArith(),
						)
						average := c.Have(
							"the terms weighted by 1/n sum to their mean",
							"Σ_{i∈1 .. n} &1 / &n * x(i) = «mean»",
							ByArith(real_sum.ScalarLeft.At(weight, x, segment)),
						)
						jensen := c.Have(
							"Jensen's inequality for the convex −log on the positive reals",
							"-log(«mean») ≤ Σ_{i∈1 .. n} &1 / &n * -log(x(i))",
							By(
								Jensen.At(
									c.TermAs[Fun[Real, Real]]("λy:real. -log(y)"),
									c.TermAs[Set[Real]]("{y:real | &0 < y}"),
									segment,
									c.TermAs[Fun[Nat, Real]]("λi:num. &1 / &n"),
									x),
								NegLogConvex,
								positives,
								num_segment.Finite.At(one, n),
								weights,
								unit,
								average),
						)
						averageLogs := c.Have(
							"its right side is minus the mean of the logarithms",
							"Σ_{i∈1 .. n} &1 / &n * -log(x(i)) = -(Σ_{i∈1 .. n} log(x(i))) / &n",
							ByArith(
								real_sum.ScalarLeft.At(weight, c.TermAs[Fun[Nat, Real]]("λi:num. -log(x(i))"), segment),
								Scaled(weight, real_sum.Neg.At(c.TermAs[Fun[Nat, Real]]("λi:num. log(x(i))"), segment))),
						)
						product := c.Have(
							"the product is positive, and its logarithm is the sum of the logarithms",
							"&0 < Π_{i∈1 .. n} x(i) ∧ log(Π_{i∈1 .. n} x(i)) = Σ_{i∈1 .. n} log(x(i))",
							By(real_exp_log.LogProduct.At(segment, x), num_segment.Finite.At(one, n), positive),
						)
						nonempty := c.Have(
							"1 .. n has a point",
							"1 .. n ≠ ∅",
							ByArith(num_segment.Empty.At(one, n), positiveCount))
						total := c.Have(
							"the terms sum to a positive number",
							"&0 < Σ_{i∈1 .. n} x(i)",
							By(real_sum.PositiveAll.At(segment, x), num_segment.Finite.At(one, n), nonempty, positive),
						)
						meanPositive := c.Have(
							"so their mean is positive",
							"&0 < «mean»",
							ByArith(total, count))
						meanOfLogs := c.Have(
							"the mean of the logarithms is at most the logarithm of the mean",
							"(Σ_{i∈1 .. n} log(x(i))) / &n ≤ log(«mean»)",
							ByArith(jensen, averageLogs),
						)
						sumOfLogs := c.Have(
							"so the sum of the logarithms is at most n times it",
							"Σ_{i∈1 .. n} log(x(i)) ≤ log(«mean») * &n",
							ByArith(
								meanOfLogs,
								count,
								real_order_field.LessEqDivMulRight.At(
									c.TermAs[Real]("Σ_{i∈1 .. n} log(x(i))"),
									c.TermAs[Real]("log(«mean»)"),
									c.TermAs[Real]("&n"))),
						)
						logs := c.Have(
							"log of the product ≤ log of the n-th power of the mean",
							"log(Π_{i∈1 .. n} x(i)) ≤ log(real_pow(«mean», n))",
							ByArith(sumOfLogs, product, meanPositive, real_exp_log.LogPow.At(mean, n)),
						)
						c.Show(
							"the logarithm increases on the positive reals",
							By(
								real_exp_log.LogLessIff.At(
									c.TermAs[Real]("real_pow(«mean», n)"), c.TermAs[Real]("Π_{i∈1 .. n} x(i)")),
								real_pow.PowPos.At(mean, n),
								logs,
								meanPositive,
								product,
								real_order_ring.NotLessThan),
						)
					})
			})
	}),
})}

// WeightedAmGm — the weighted inequality of arithmetic and geometric means:
// for finitely many positive reals x(i) and nonnegative weights w(i)
// summing to 1, the product of the powers x(i)^w(i) is at most the weighted
// mean Σ w(i)·x(i). Jensen's inequality for the convex −log puts −log of
// the mean below Σ w(i)·(−log x(i)), and each term w(i)·(−log x(i)) is
// −log x(i)^w(i), so that sum is −log of the product; log is increasing.
var WeightedAmGm = weightedAmGmThm{family.Add(registry.ProofEntry{
	Name: "WeightedAmGm",
	Key:  "prop_b25ecb79822d45e6",
	Build: family.Theorem(Statement{
		Binders: "∀k:set(A). ∀w x:A → real.",
		Hypotheses: []string{
			"finite(k)",
			"∀i:A. i ∈ k ⇒ &0 ≤ w(i) ∧ &0 < x(i)",
			"Σ_{i∈k} w(i) = &1",
		},
		Conclusion: "Π_{i∈k} real_rpow(x(i), w(i)) ≤ Σ_{i∈k} w(i) * x(i)",
	}, func(a *Argument, k *Expr[Set[A]], w, x *Arrow[A, Real], finiteK, weights, total Fact) {
		positiveReals := a.TermAs[Set[Real]]("{u:real | &0 < u}")
		interval := a.Have(
			"the positive reals form an interval",
			"real_interval({u:real | &0 < u})",
			Unfold(real_topology.RealIntervalDef),
			ByArith(),
		)
		jensen := a.Have(
			"Jensen's inequality for the convex −log at the points x(i)",
			"-log(Σ_{i∈k} w(i) * x(i)) ≤ Σ_{i∈k} w(i) * -log(x(i))",
			By(
				Jensen.At(a.TermAs[Fun[Real, Real]]("λu:real. -log(u)"), positiveReals, k, w, x),
				NegLogConvex,
				interval,
				finiteK,
				weights,
				total),
		)
		mean := a.Have(
			"the weighted mean, a convex combination of positive reals, is positive",
			"&0 < Σ_{i∈k} w(i) * x(i)",
			By(ConvexCombinationIn.At(positiveReals, k, w, x), interval, finiteK, weights, total),
		)
		product := a.Have(
			"the powers x(i)^w(i) are positive, so their product is, and its logarithm is the sum of theirs",
			"&0 < Π_{i∈k} real_rpow(x(i), w(i)) ∧ "+
				"log(Π_{i∈k} real_rpow(x(i), w(i))) = Σ_{i∈k} log(real_rpow(x(i), w(i)))",
			By(
				real_exp_log.LogProduct.At(k, a.TermAs[Fun[A, Real]]("λi:A. real_rpow(x(i), w(i))")),
				finiteK,
				weights,
				real_rpow.RpowPositive),
		)
		termwise := a.Have(
			"each term w(i)·(−log x(i)) is −log x(i)^w(i)",
			"∀i:A. i ∈ k ⇒ w(i) * -log(x(i)) = -log(real_rpow(x(i), w(i)))",
			a.ForEach(func(i *Expr[A]) Action {
				return ByArith(weights.At(i), real_rpow.LogRpow.At(x.Apply(i), w.Apply(i)))
			}),
		)
		sums := a.Have(
			"so Jensen's right side is −log of the product",
			"Σ_{i∈k} w(i) * -log(x(i)) = -Σ_{i∈k} log(real_rpow(x(i), w(i)))",
			By(
				real_sum.Neg.At(a.TermAs[Fun[A, Real]]("λi:A. log(real_rpow(x(i), w(i)))"), k),
				real_sum.Congruence.At(
					k,
					a.TermAs[Fun[A, Real]]("λi:A. w(i) * -log(x(i))"),
					a.TermAs[Fun[A, Real]]("λi:A. -log(real_rpow(x(i), w(i)))")),
				termwise),
		)
		a.Show(
			"log of the product is at most log of the mean, and log is increasing",
			ByArith(
				jensen,
				sums,
				mean,
				product,
				real_exp_log.LogLessIff.At(
					a.TermAs[Real]("Σ_{i∈k} w(i) * x(i)"),
					a.TermAs[Real]("Π_{i∈k} real_rpow(x(i), w(i))"))),
		)
	}),
})}
