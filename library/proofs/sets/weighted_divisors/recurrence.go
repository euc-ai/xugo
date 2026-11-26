// recurrence.go — the logarithmic recurrence of the weighted counts: count
// each effective divisor of degree n together with a marked occurrence of one
// of its points, the mark weighted by the point's weight, in two orders. An
// effective divisor D holds k copies of x when k ≤ D(x): its value at x,
// unweighted, counts the copies, and k copies weigh k·w(x) — where product.go
// says D spends w(x)·D(x) at x, the value weighted.

package weighted_divisors

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// WeightedCountAtLeast — the effective divisors of degree n that hold at
// least k copies of a point x of S of positive weight are as many as the
// effective divisors of degree n − k·w(x), when k·w(x) ≤ n. Taking k away at
// x and adding it back are inverse to each other between the two sets: adding
// k raises the degree by k·w(x) (WeightedRaise), and taking it away from a
// divisor that has at least k there undoes an addition. The divisors of the
// lower degree are finitely many, their points weighing at most n.
var WeightedCountAtLeast = weightedCountAtLeastThm{family.Add(registry.ProofEntry{
	Name: "WeightedCountAtLeast",
	Key:  "prop_38174ce2b92ec86c",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀w:(A → num). ∀n:num. ∀x:A. ∀k:num.",
		Hypotheses: []string{
			"finite(«lowWeight»)",
			"x ∈ S",
			"0 < w(x)",
			"k * w(x) ≤ n",
		},
		Conclusion: "card(«atLeast») = weighted_count(S, w, n - k * w(x))",
		Abbrev: Abbrev{
			{Name: "atLeast", Text: "{D:A → num | " +
				"    weighted_effective(S, w, D) ∧ weighted_degree(w, D) = n ∧ k ≤ D(x)}"},
			{Name: "below", Text: "{D:A → num | " +
				"    weighted_effective(S, w, D) ∧ weighted_degree(w, D) = n - k * w(x)}"},
			{Name: "raise", Text: "λD:A → num. λy:A. D(y) + COND(y = x, k, 0)"},
			{Name: "lower", Text: "λD:A → num. λy:A. D(y) - COND(y = x, k, 0)"},
		},
	},
		func(a *Argument, S *Expr[Set[A]], w *Arrow[A, Nat], n *Expr[Nat], x *Expr[A], k *Expr[Nat],
			finiteLowWeight, xInS, positive, fits Fact) {
			lowerDegree := a.TermAs[Nat]("n - k * w(x)")
			lighter := a.Have(
				"a weight at most n − k·w(x) is at most n",
				"∀y:A. w(y) ≤ n - k * w(x) ⇒ w(y) ≤ n",
				ByArith())
			fewerPoints := a.Have(
				"so the points of weight at most n − k·w(x) are among those of weight at most n",
				"{y:A | y ∈ S ∧ w(y) ≤ n - k * w(x)} ⊆ «lowWeight»",
				BySets(lighter))
			belowFinite := a.Have(
				"and the effective divisors of degree n − k·w(x) are finitely many",
				"finite(«below»)",
				By(
					finiteLowWeight,
					fewerPoints,
					finite_set.FiniteSubset,
					WeightedDivisorsFinite.At(S, w, lowerDegree)))
			up := a.Have(
				"adding k at x to a divisor of degree n − k·w(x) gives one "+
					"of degree n with at least k at x, and taking k away undoes it",
				"∀D:A → num. D ∈ «below» ⇒ «raise»(D) ∈ «atLeast» ∧ «lower»(«raise»(D)) = D",
				Derive(func(b *Argument) {
					D := b.FixAs[Fun[A, Nat]]("D")
					inBelow := b.Assume()
					b.Show(
						"adding k at x raises the degree by k·w(x), to n",
						ByArith(inBelow, xInS, positive, fits, WeightedRaise.At(S, w, D, x, k)))
				}))
			down := a.Have(
				"taking k away at x from a divisor of degree n with at least k "+
					"there gives one of degree n − k·w(x), and adding k back undoes it",
				Statement{
					Binders: "∀D:A → num.",
					Hypotheses: []string{
						"weighted_effective(S, w, D)",
						"weighted_degree(w, D) = n",
						"k ≤ D(x)",
					},
					Conclusion: "«lower»(D) ∈ «below» ∧ «raise»(«lower»(D)) = D",
				},
				Derive(func(b *Argument) {
					b.FixAs[Fun[A, Nat]]("D")
					parts := b.Conjuncts(
						b.Assume(),
						"D is effective",
						"of degree n",
						"with at least k at x")
					support := b.Conjuncts(
						b.Unfolded(parts[0], WeightedEffectiveDef),
						"the support of D is finite",
						"and lies in S, at points of positive weight")
					fewer := b.Have(
						"taking k away at x leaves a value nonzero only where D's is",
						"∀y:A. «lower»(D, y) ≠ 0 ⇒ D(y) ≠ 0",
						ByArith())
					within := b.Have(
						"so the lowered divisor's support lies in D's",
						"fun_support(0, λy:A. «lower»(D, y)) ⊆ fun_support(0, D)",
						BySets(fewer))
					loweredEffective := b.Have(
						"and the lowered divisor is effective",
						"weighted_effective(S, w, «lower»(D))",
						Unfold(WeightedEffectiveDef),
						By(support[0], support[1], fewer, within, finite_set.FiniteSubset))
					back := b.Have(
						"what is taken away is at most D, so adding k back at x gives D",
						"«raise»(«lower»(D)) = D",
						By(parts[2], nat_order.ZeroLessEq, nat_monus.SubAddCancel))
					degrees := b.Have(
						"adding k at x raises the lowered degree by k·w(x)",
						"weighted_degree(w, D) = weighted_degree(w, «lower»(D)) + k * w(x)",
						By(
							positive,
							back,
							xInS,
							loweredEffective,
							WeightedRaise.At(S, w, b.TermAs[Fun[A, Nat]]("«lower»(D)"), x, k)))
					b.Show(
						"so the lowered divisor has degree n − k·w(x)",
						ByArith(back, parts[1], degrees, loweredEffective))
				}))
			a.Show(
				"the two maps are inverse to each other, so the "+
					"divisors of degree n with at least k at x are as many",
				By(
					up,
					down,
					belowFinite,
					cardinality.MutualInversesCard.At(
						a.TermAs[Set[Fun[A, Nat]]]("«below»"),
						a.TermAs[Set[Fun[A, Nat]]]("«atLeast»"),
						a.TermAs[Fun[Fun[A, Nat], Fun[A, Nat]]]("«raise»"),
						a.TermAs[Fun[Fun[A, Nat], Fun[A, Nat]]]("«lower»")),
					WeightedCountDef.At(S, w, lowerDegree)))
		}),
})}

// WeightedMultiplicitySum — the values at a point x of S of positive weight,
// summed over the effective divisors of degree n, add up to the counts at
// n − m summed over the multiples m of w(x) from w(x) to n. A value D(x)
// counts the k ≥ 1 with k ≤ D(x), and k·w(x) ≤ n for each of them; summed
// the other way round, each such k counts the divisors with at least k at x,
// which are weighted_count(S, w, n − k·w(x)) (WeightedCountAtLeast), and
// k ↦ k·w(x) carries those k one to one onto the multiples of w(x) up to n.
var WeightedMultiplicitySum = weightedMultiplicitySumThm{family.Add(registry.ProofEntry{
	Name: "WeightedMultiplicitySum",
	Key:  "prop_361d65f0b982c2c9",
	Build: family.Theorem(Statement{
		Binders: "∀S:set(A). ∀w:(A → num). ∀n:num. ∀x:A.",
		Hypotheses: []string{
			"finite(«lowWeight»)",
			"x ∈ S",
			"0 < w(x)",
		},
		Conclusion: "nat_sum(«divisors», λD:A → num. D(x)) = " +
			"nat_sum(«multiples», λm:num. weighted_count(S, w, n - m))",
		Abbrev: Abbrev{
			{Name: "multiples", Text: "{m:num | 0 < m ∧ m ≤ n ∧ w(x) ∣ m}"},
			{Name: "copies", Text: "{k:num | 0 < k ∧ k * w(x) ≤ n}"},
		},
	},
		func(
			a *Argument,
			S *Expr[Set[A]],
			w *Arrow[A, Nat],
			n *Expr[Nat],
			x *Expr[A],
			finiteLowWeight, xInS, positive Fact,
		) {
			divisors := a.TermAs[Set[Fun[A, Nat]]]("«divisors»")
			copies := a.TermAs[Set[Nat]]("«copies»")
			divisorsFinite := a.Have(
				"the effective divisors of degree n are finitely many",
				"finite(«divisors»)",
				By(finiteLowWeight, WeightedDivisorsFinite.At(S, w, n)))
			fewCopies := a.Have(
				"k copies of x weigh at least k, w(x) being positive",
				"∀k:num. k * w(x) ≤ n ⇒ k ≤ n",
				ByArith(positive, nat_order.LessEqMulNonzero))
			copiesBelowN := a.Have(
				"so the numbers of copies that fit in degree n are at most n",
				"«copies» ⊆ {k:num | k ≤ n}",
				BySets(fewCopies))
			copiesFinite := a.Have(
				"and they are finitely many",
				"finite(«copies»)",
				By(copiesBelowN, finite_set.FiniteSubset, num_segment.FiniteBelow.At(n)))
			layers := a.Have(
				"the value of each such D at x counts the numbers of copies k with k ≤ D(x)",
				"∀D:(A → num). D ∈ «divisors» ⇒ D(x) = nat_sum(«copies», λk:num. COND(k ≤ D(x), 1, 0))",
				Derive(func(b *Argument) {
					D := b.FixAs[Fun[A, Nat]]("D")
					ofDegreeN := b.Assume()
					value := b.TermAs[Nat]("D(x)")
					heavy := b.Have(
						"the term of x in the degree of D is at most the degree, n",
						"w(x) * D(x) ≤ n",
						ByArith(ofDegreeN, WeightedEffectiveDef.At(S, w, D), WeightedDegreeSplit.At(w, D, x)))
					fewer := b.Have(
						"so k copies of x weigh at most n for every k ≤ D(x)",
						"∀k:num. k ≤ D(x) ⇒ k * w(x) ≤ n",
						ByArith(heavy, nat_order.LessEqMulRightCancel))
					fitting := b.Have(
						"and the numbers of copies up to D(x) are the k from 1 to D(x)",
						"∀k:num. (0 < k ∧ k * w(x) ≤ n) ∧ k ≤ D(x) ⇔ 1 ≤ k ∧ k ≤ D(x)",
						ByArith(fewer))
					segment := b.Have(
						"which is the interval 1 .. D(x)",
						"{k:num | k ∈ «copies» ∧ k ≤ D(x)} = 1 .. D(x)",
						BySets(fitting, num_segment.IntervalDef))
					upToValue := b.TermAs[Set[Nat]]("1 .. D(x)")
					b.Show(
						"which are D(x) many",
						By(
							segment,
							nat_sum.Restrict.At(
								copies,
								b.TermAs[Set[Nat]]("λk:num. k ≤ D(x)"),
								b.TermAs[Fun[Nat, Nat]]("λk:num. 1")),
							nat_sum.SumOfOnes.At(upToValue),
							num_segment.Finite.At(b.TermAs[Nat]("1"), value),
							num_segment.CardFromOne.At(value)))
				}))
			atLeastK := a.Have(
				"for each number of copies k, the divisors with at least "+
					"k copies of x are as many as those of degree n − k·w(x)",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"k ∈ «copies»",
					},
					Conclusion: "nat_sum(«divisors», λD:(A → num). COND(k ≤ D(x), 1, 0)) = " +
						"weighted_count(S, w, n - k * w(x))",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					fitsK := b.Assume()
					enough := b.TermAs[Set[Fun[A, Nat]]]("λD:A → num. k ≤ D(x)")
					counted := b.Have(
						"summing 1 over the divisors with at least k copies of x counts them",
						"nat_sum(«divisors», λD:A → num. COND(k ≤ D(x), 1, 0)) = "+
							"card({D:A → num | weighted_effective(S, w, D) ∧ weighted_degree(w, D) = n ∧ k ≤ D(x)})",
						By(
							divisorsFinite,
							nat_sum.Restrict.At(
								divisors,
								enough,
								b.TermAs[Fun[Fun[A, Nat], Nat]]("λD:A → num. 1")),
							finite_set.FiniteRestrict.At(divisors, enough),
							nat_sum.SumOfOnes.At(
								b.TermAs[Set[Fun[A, Nat]]]("{D:A → num | D ∈ «divisors» ∧ k ≤ D(x)}"))))
					b.Show(
						"and they are as many as the divisors of degree n − k·w(x)",
						By(finiteLowWeight, positive, counted, xInS, fitsK, WeightedCountAtLeast.At(S, w, n, x, k)))
				}))
			scaling := a.TermAs[Fun[Nat, Nat]]("λk:num. k * w(x)")
			injective := a.Have(
				"multiplying by the positive weight w(x) is one to one",
				"injective_on(«copies», λk:num. k * w(x))",
				Unfold(functions.InjectiveOnDef),
				By(positive, nat_arith.MulEqLCancel, nat_arith.MulSym, nat_order.LessThanIrrefl))
			multipleOf := a.Have(
				"k copies of x weigh a positive multiple of w(x) when k is positive",
				"∀k:num. 0 < k ⇒ 0 < k * w(x) ∧ w(x) ∣ k * w(x)",
				By(
					Normalized,
					positive,
					nat_divides.DividesFactor,
					nat_arith.MulSym,
					nat_arith.MulEqZero,
					nat_order.PosIffNonzero))
			quotient := a.Have(
				"and a positive multiple of w(x) is the weight of a positive number of copies",
				"∀m:num. 0 < m ∧ w(x) ∣ m ⇒ ∃k:num. 0 < k ∧ m = k * w(x)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					parts := b.Conjuncts(
						b.Assume(),
						"m is positive",
						"and a multiple of w(x)")
					q, factor := b.UnpackAs[Nat](b.Unfolded(parts[1], nat_divides.DividesFactor), "q")
					b.Take(q)
					b.Show(
						"m = w(x)·q is positive, so q is",
						By(Normalized, parts[0], factor, nat_arith.MulSym, nat_arith.MulZero, nat_order.PosIffNonzero))
				}))
			multiples := a.Have(
				"so k ↦ k·w(x) carries the numbers of copies onto the multiples of w(x) up to n",
				"image(λk:num. k * w(x), «copies») = «multiples»",
				BySets(multipleOf, quotient))
			a.Show(
				"count each occurrence of x by its copies k, then "+
					"each k by the divisors with at least k copies of x",
				CalcEq(
					Leg(
						a.TermAs[Nat]("nat_sum(«divisors», λD:A → num. nat_sum(«copies», λk:num. COND(k ≤ D(x), 1, 0)))"),
						"each value at x counts its numbers of copies",
						By(layers, nat_sum.Congruence)),
					Leg(
						a.TermAs[Nat]("nat_sum(«copies», λk:num. nat_sum(«divisors», λD:A → num. COND(k ≤ D(x), 1, 0)))"),
						"the two finite sums are exchanged",
						By(divisorsFinite, copiesFinite, nat_sum.Swap)),
					Leg(
						a.TermAs[Nat]("nat_sum(«copies», λk:num. weighted_count(S, w, n - k * w(x)))"),
						"for each k, the divisors with at least k copies of x are counted at degree n − k·w(x)",
						By(
							atLeastK,
							nat_sum.Congruence.At(
								copies,
								a.TermAs[Fun[Nat, Nat]]("λk:num. nat_sum(«divisors», λD:A → num. COND(k ≤ D(x), 1, 0))"),
								a.TermAs[Fun[Nat, Nat]]("λk:num. weighted_count(S, w, n - k * w(x))")))),
					FinalLeg(
						"and the sum is carried along k ↦ k·w(x) onto the multiples of w(x)",
						multiples.RwRev(),
						By(
							injective,
							nat_sum.Image.At(
								copies,
								scaling,
								a.TermAs[Fun[Nat, Nat]]("λm:num. weighted_count(S, w, n - m)")),
							functions.ComposeApply))))
		}),
})}

// WeightedCountRecurrence — the logarithmic recurrence of the weighted counts:
// n times the number of effective divisors of degree n is the sum, over m
// from 1 to n, of the total weight of the points whose weight divides m times
// the number of effective divisors of degree n − m. Both sides count an
// effective divisor D of degree n together with a marked occurrence of one of
// its points x, the mark weighted by w(x): each D carries its degree n,
// and at each point x of weight at most n the occurrences add up to the
// counts at n − m over the multiples m of w(x) (WeightedMultiplicitySum);
// grouped by m instead of by x, the marks at m weigh the points whose weight
// divides m.
var WeightedCountRecurrence = weightedCountRecurrenceThm{family.Add(registry.ProofEntry{
	Name: "WeightedCountRecurrence",
	Key:  "prop_e21bd93090748cdb",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(A). ∀w:(A → num). ∀n:num.",
		Hypotheses: []string{"finite(«lowWeight»)"},
		Conclusion: "n * weighted_count(S, w, n) = " +
			"nat_sum(«oneToN», λm:num. weighted_multiples(S, w, m) * weighted_count(S, w, n - m))",
	},
		func(a *Argument, S *Expr[Set[A]], w *Arrow[A, Nat], n *Expr[Nat], finiteLowWeight Fact) {
			lowWeight := a.TermAs[Set[A]]("«lowWeight»")
			divisors := a.TermAs[Set[Fun[A, Nat]]]("«divisors»")
			oneToN := a.TermAs[Set[Nat]]("«oneToN»")
			divisorsFinite := a.Have(
				"the effective divisors of degree n are finitely many",
				"finite(«divisors»)",
				By(finiteLowWeight, WeightedDivisorsFinite.At(S, w, n)))
			indicesFinite := a.Have(
				"and so are the indices from 1 to n",
				"finite(«oneToN»)",
				By(
					num_segment.FiniteBelow.At(n),
					finite_set.FiniteRestrict.At(
						a.TermAs[Set[Nat]]("{m:num | m ≤ n}"),
						a.TermAs[Set[Nat]]("λm:num. 0 < m"))))
			overLowWeight := a.Have(
				"the degree of each such D is its sum over the points of weight at most n",
				"∀D:(A → num). D ∈ «divisors» ⇒ weighted_degree(w, D) = nat_sum(«lowWeight», λx:A. w(x) * D(x))",
				Derive(func(b *Argument) {
					D := b.FixAs[Fun[A, Nat]]("D")
					ofDegreeN := b.Assume()
					within := b.Have(
						"a point where D does not vanish is a point of S of weight at most the degree, n",
						"fun_support(0, D) ⊆ «lowWeight»",
						BySets(ofDegreeN, WeightedSupportBound))
					b.Show(
						"so the degree may be summed there",
						By(within, WeightedDegreeOver.At(w, D, lowWeight)))
				}))
			perPoint := a.Have(
				"at a point x of weight at most n, the terms w(x)·D(x) sum to w(x) "+
					"times the counts at n − m over the indices m that w(x) divides",
				Statement{
					Binders: "∀x:A.",
					Hypotheses: []string{
						"x ∈ «lowWeight»",
					},
					Conclusion: "nat_sum(«divisors», λD:(A → num). w(x) * D(x)) = " +
						"nat_sum(«oneToN», λm:num. COND(w(x) ∣ m, w(x) * weighted_count(S, w, n - m), 0))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					lowX := b.Assume()
					weight := w.Apply(x)
					multiplesOfX := b.TermAs[Set[Nat]]("{m:num | 0 < m ∧ m ≤ n ∧ w(x) ∣ m}")
					divides := b.TermAs[Set[Nat]]("λm:num. w(x) ∣ m")
					scaled := b.Have(
						"scaled by w(x), the values at x sum to the counts at n − m over the multiples m of w(x)",
						"w(x) * nat_sum(«divisors», λD:A → num. D(x)) = "+
							"w(x) * nat_sum({m:num | 0 < m ∧ m ≤ n ∧ w(x) ∣ m}, λm:num. weighted_count(S, w, n - m))",
						Derive(func(c *Argument) {
							positive := c.Assuming(
								c.TermAs[Bool]("0 < w(x)"),
								"where w(x) = 0 both sides are 0",
								Given(func(d *Argument, weightless Fact) {
									d.Do(By(weightless, nat_order.PosIffNonzero, nat_arith.MulLeftZeroClause))
								}))
							c.Show(
								"where w(x) is positive the two sums agree (WeightedMultiplicitySum)",
								By(finiteLowWeight, lowX, positive, WeightedMultiplicitySum.At(S, w, n, x)))
						}))
					b.Show(
						"the factor w(x) goes into both sums, and the multiples of w(x) are the indices it divides",
						By(
							divisorsFinite,
							indicesFinite,
							scaled,
							nat_sum.ScalarLeft.At(
								weight,
								b.TermAs[Fun[Fun[A, Nat], Nat]]("λD:A → num. D(x)"),
								divisors),
							finite_set.FiniteRestrict.At(oneToN, divides),
							nat_sum.ScalarLeft.At(
								weight,
								b.TermAs[Fun[Nat, Nat]]("λm:num. weighted_count(S, w, n - m)"),
								multiplesOfX),
							nat_sum.Restrict.At(
								oneToN,
								divides,
								b.TermAs[Fun[Nat, Nat]]("λm:num. w(x) * weighted_count(S, w, n - m)"))))
				}))
			perIndex := a.Have(
				"at an index m from 1 to n, the terms sum over the points to the "+
					"weight of the points whose weight divides m times the count at n − m",
				Statement{
					Binders: "∀m:num.",
					Hypotheses: []string{
						"m ∈ «oneToN»",
					},
					Conclusion: "nat_sum(«lowWeight», λx:A. COND(w(x) ∣ m, w(x) * weighted_count(S, w, n - m), 0)) = " +
						"weighted_multiples(S, w, m) * weighted_count(S, w, n - m)",
				},
				Derive(func(b *Argument) {
					b.FixAs[Nat]("m")
					inRange := b.Assume()
					divides := b.TermAs[Set[A]]("λx:A. w(x) ∣ m")
					multiplesOfM := b.TermAs[Set[A]]("{x:A | x ∈ S ∧ w(x) ∣ m}")
					bounded := b.Have(
						"a weight dividing m is at most m, so at most n",
						"∀x:A. w(x) ∣ m ⇒ w(x) ≤ n",
						ByArith(inRange, nat_divides.DividesLessEq))
					sameSet := b.Have(
						"so the points of weight at most n whose weight divides "+
							"m are all the points of S whose weight divides m",
						"{x:A | x ∈ «lowWeight» ∧ w(x) ∣ m} = {x:A | x ∈ S ∧ w(x) ∣ m}",
						BySets(bounded))
					restricted := b.Have(
						"the terms that survive are those at the points of S whose weight divides m",
						"nat_sum(«lowWeight», λx:A. COND(w(x) ∣ m, w(x) * weighted_count(S, w, n - m), 0)) = "+
							"nat_sum({x:A | x ∈ S ∧ w(x) ∣ m}, λx:A. weighted_count(S, w, n - m) * w(x))",
						By(
							sameSet,
							nat_sum.Restrict.At(
								lowWeight,
								divides,
								b.TermAs[Fun[A, Nat]]("λx:A. w(x) * weighted_count(S, w, n - m)")),
							nat_arith.MulSym))
					multiplesFinite := b.Have(
						"those points are finitely many",
						"finite({x:A | x ∈ S ∧ w(x) ∣ m})",
						By(finiteLowWeight, sameSet, finite_set.FiniteRestrict.At(lowWeight, divides)))
					value := b.Have(
						"and their weights sum to the weighted multiples of m, m being positive",
						"weighted_multiples(S, w, m) = nat_sum({x:A | x ∈ S ∧ w(x) ∣ m}, w)",
						By(inRange, WeightedMultiplesDef, nat_order.LessThanIrrefl))
					b.Show(
						"the common factor, the count at n − m, comes out",
						By(
							multiplesFinite,
							restricted,
							value,
							nat_sum.ScalarLeft.At(
								b.TermAs[Nat]("weighted_count(S, w, n - m)"),
								w,
								multiplesOfM),
							nat_arith.MulSym))
				}))
			a.Show(
				"count each divisor D of degree n with a weighted mark on one "+
					"of its points, first by D, then by the weight the mark divides",
				CalcEq(
					Leg(
						a.TermAs[Nat]("nat_sum(«divisors», λD:A → num. n)"),
						"summing n over the effective divisors of degree n is n times their number",
						By(
							divisorsFinite,
							WeightedCountDef,
							nat_sum.SumOfOnes.At(divisors),
							nat_sum.ScalarLeft.At(
								n,
								a.TermAs[Fun[Fun[A, Nat], Nat]]("λD:A → num. 1"),
								divisors),
							nat_arith.MulOne)),
					Leg(
						a.TermAs[Nat]("nat_sum(«divisors», λD:A → num. weighted_degree(w, D))"),
						"each of them has degree n",
						By(nat_sum.Congruence)),
					Leg(
						a.TermAs[Nat]("nat_sum(«divisors», λD:A → num. nat_sum(«lowWeight», λx:A. w(x) * D(x)))"),
						"each degree is a sum over the points of weight at most n",
						By(overLowWeight, nat_sum.Congruence)),
					Leg(
						a.TermAs[Nat]("nat_sum(«lowWeight», λx:A. nat_sum(«divisors», λD:A → num. w(x) * D(x)))"),
						"the sums over divisors and over points are exchanged",
						By(finiteLowWeight, divisorsFinite, nat_sum.Swap)),
					Leg(
						a.TermAs[Nat](
							"nat_sum(«lowWeight», "+
								"    λx:A. nat_sum(«oneToN», λm:num. COND(w(x) ∣ m, w(x) * weighted_count(S, w, n - m), 0)))"),
						"at each point the marks are counted by the multiples of its weight",
						By(perPoint, nat_sum.Congruence)),
					Leg(
						a.TermAs[Nat](
							"nat_sum(«oneToN», "+
								"    λm:num. nat_sum(«lowWeight», λx:A. COND(w(x) ∣ m, w(x) * weighted_count(S, w, n - m), 0)))"),
						"the sums over points and over indices are exchanged",
						By(finiteLowWeight, indicesFinite, nat_sum.Swap)),
					FinalLeg(
						"and at each index m the points whose weight divides "+
							"m contribute their weights times the count at n − m",
						By(
							perIndex,
							nat_sum.Congruence.At(
								oneToN,
								a.TermAs[Fun[Nat, Nat]](
									"λm:num. nat_sum(«lowWeight», λx:A. COND(w(x) ∣ m, w(x) * weighted_count(S, w, n - m), 0))"),
								a.TermAs[Fun[Nat, Nat]]("λm:num. weighted_multiples(S, w, m) * weighted_count(S, w, n - m)"))))))
		}),
})}
