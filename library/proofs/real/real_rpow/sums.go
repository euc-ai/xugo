// sums.go — sums and growth of real powers of the natural numbers: the
// step between consecutive powers, the tail and the head of the sum of
// n^(−x−1) and n^(x−1), the convergence of Σ n^(−σ) for σ > 1, and the
// logarithm against a small power.

package real_rpow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// RpowStepBounds — the decrement of a negative power between consecutive
// positive naturals lies between its endpoint derivative magnitudes.
// The mean value theorem realizes the decrement at an interior point;
// negative-exponent powers decrease, giving the endpoint squeeze.
var RpowStepBounds = rpowStepBoundsThm{family.Add(registry.ProofEntry{
	Name: "RpowStepBounds",
	Key:  "prop_c7eae3bedcee194a",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀n:num.",
		Hypotheses: []string{
			"&0 < x",
			"0 < n",
		},
		Conclusion: "x * real_rpow(&(n + 1), -x - &1) ≤ real_rpow(&n, -x) - real_rpow(&(n + 1), -x) ∧ " +
			"real_rpow(&n, -x) - real_rpow(&(n + 1), -x) ≤ x * real_rpow(&n, -x - &1)",
	},
		func(a *Argument, x *Expr[Real], n *Expr[Nat], conditions Fact) {
			p, exponentDef := a.LetAs[Real]("p", "-x - &1")
			derivative := a.Have(
				"the negative power has derivative -x times the power with exponent p",
				"∀t:real. &0 < t ⇒ real_derivative_at(λy:real. real_rpow(y, -x), t, -x * real_rpow(t, p))",
				exponentDef.Rw(),
				By(RpowDerivativeBase))
			positiveInterval := a.Have(
				"the positive reals form an interval",
				"real_interval({t:real | &0 < t})",
				Unfold(real_topology.RealIntervalDef),
				ByArith())
			endpoints := a.Have(
				"the consecutive endpoints are positive and strictly ordered",
				"&0 < &n ∧ &0 < &(n + 1) ∧ &n < &(n + 1)",
				ByArith(conditions))
			left := a.TermAs[Real]("&n")
			right := a.TermAs[Real]("&(n + 1)")
			c, meanValue := a.ObtainAs[Real](
				"the mean value theorem realizes the power increment at an interior point",
				"∃c:real. "+
					"    &n < c ∧ "+
					"    c < &(n + 1) ∧ "+
					"    real_rpow(&(n + 1), -x) - real_rpow(&n, -x) = -x * real_rpow(c, p) * (&(n + 1) - &n)",
				By(
					positiveInterval,
					derivative,
					endpoints,
					real_derivative.MeanValueOnInterval.At(
						a.TermAs[Fun[Real, Real]]("λt:real. real_rpow(t, -x)"),
						a.TermAs[Fun[Real, Real]]("λt:real. -x * real_rpow(t, p)"),
						a.TermAs[Set[Real]]("{t:real | &0 < t}"),
						left,
						right)))
			step := a.Have(
				"the interval has unit length, so the decrement is x times the power at c",
				"real_rpow(&n, -x) - real_rpow(&(n + 1), -x) = x * real_rpow(c, p)",
				ByArith(meanValue))
			decreasing := a.Have(
				"the negative-exponent power decreases across the interval and squeezes its value at c",
				"real_rpow(&(n + 1), p) ≤ real_rpow(c, p) ∧ real_rpow(c, p) ≤ real_rpow(&n, p)",
				ByArith(
					exponentDef,
					conditions,
					meanValue,
					endpoints,
					RpowLessBaseNegative.At(left, c, p),
					RpowLessBaseNegative.At(c, right, p)))
			a.Show(
				"multiply the endpoint squeeze by positive x and use the mean-value step formula",
				ByArith(step, decreasing, conditions))
		}),
})}

// RpowTailSumBound — a tail of the negative-power sum is bounded by the
// power at its starting index, divided by the positive exponent.
// Shift each summand onto a consecutive-power decrement, sum the step
// bounds, and telescope; the final power is nonnegative and can be dropped.
var RpowTailSumBound = rpowTailSumBoundThm{family.Add(registry.ProofEntry{
	Name: "RpowTailSumBound",
	Key:  "prop_9bafad7cc0be9807",
	Reading: "The bound does not depend on M, so it bounds the tail of the series; " +
		"for M ≤ N the sum is empty and the bound is the nonnegative right side.",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀N M:num.",
		Hypotheses: []string{
			"&0 < x",
			"0 < N",
		},
		Conclusion: "Σ_{n∈N + 1 .. M} real_rpow(&n, -x - &1) ≤ real_rpow(&N, -x) / x",
	},
		func(a *Argument, x *Expr[Real], N, M *Expr[Nat], conditions Fact) {
			tail := a.BigOpAs[Nat, Real]("Σ_{n∈N + 1 .. M} real_rpow(&n, -x - &1)")
			nonempty := a.Unless(
				a.TermAs[Bool]("M ≤ N"),
				"when M ≤ N the tail is empty and the bound is nonnegative",
				Given(func(b *Argument, empty Fact) {
					b.Show(
						"the empty tail is zero, below the nonnegative power quotient",
						ByArith(
							empty,
							conditions,
							real_sum.EmptyInterval.At(M, b.TermAs[Nat]("N + 1"), tail.Summand()),
							RpowNonneg.At(b.TermAs[Real]("&N"), b.TermAs[Real]("-x"))))
				}))
			last := a.TermAs[Nat]("M - 1")
			endpoint := a.Have(
				"the shifted interval is nonempty and its last index has successor M",
				"N ≤ M - 1 ∧ M - 1 + 1 = M",
				ByArith(nonempty))
			shifted := a.BigOpAs[Nat, Real]("Σ_{k∈N .. M - 1} real_rpow(&(k + 1), -x - &1)")
			shift := a.Have(
				"shift the tail down by one to match the right endpoints of the power steps",
				"Σ_{n∈N + 1 .. M} real_rpow(&n, -x - &1) = Σ_{k∈N .. M - 1} real_rpow(&(k + 1), -x - &1)",
				By(endpoint, real_sum.Shift.At(N, last, a.TermAs[Nat]("1"), tail.Summand())))
			steps := a.Have(
				"each shifted summand times x is bounded by the corresponding power decrement",
				Statement{
					Binders: "∀k:num.",
					Hypotheses: []string{
						"N ≤ k",
						"k ≤ M - 1",
					},
					Conclusion: "x * real_rpow(&(k + 1), -x - &1) ≤ real_rpow(&k, -x) - real_rpow(&(k + 1), -x)",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					inRange := b.Assume()
					b.Show(
						"k is positive above N, so the lower step bound applies",
						ByArith(inRange, conditions, RpowStepBounds.At(x, k)))
				}))
			decrements := a.BigOpAs[Nat, Real]("Σ_{k∈N .. M - 1} (real_rpow(&k, -x) - real_rpow(&(k + 1), -x))")
			telescope := a.Have(
				"the consecutive decrements telescope to the two endpoint powers",
				"Σ_{k∈N .. M - 1} (real_rpow(&k, -x) - real_rpow(&(k + 1), -x)) = "+
					"real_rpow(&N, -x) - real_rpow(&M, -x)",
				By(
					endpoint,
					real_sum.TelescopeDown.At(N, last, a.TermAs[Fun[Nat, Real]]("λk:num. real_rpow(&k, -x)"))))
			weighted := a.BigOpAs[Nat, Real]("Σ_{k∈N .. M - 1} x * real_rpow(&(k + 1), -x - &1)")
			tailBound := a.Have(
				"sum the step bounds and pull x outside the shifted tail",
				"x * (Σ_{n∈N + 1 .. M} real_rpow(&n, -x - &1)) ≤ real_rpow(&N, -x) - real_rpow(&M, -x)",
				ByArith(
					steps,
					telescope,
					shift,
					real_sum.ScalarLeft.At(x, shifted.Summand(), shifted.Range()),
					real_sum.IntervalMonotone.At(N, last, weighted.Summand(), decrements.Summand())))
			a.Show(
				"drop the nonnegative final power and divide by positive x",
				ByArith(tailBound, conditions, RpowNonneg.At(a.TermAs[Real]("&M"), a.TermAs[Real]("-x"))))
		}),
})}

// RpowHeadSumBound — the power sum at the positive integers up to N is bounded by
// the final power times the reciprocal index and reciprocal exponent.
// The mean value theorem compares each summand to a consecutive power
// increment; the endpoint used depends on whether the slope increases.
var RpowHeadSumBound = rpowHeadSumBoundThm{family.Add(registry.ProofEntry{
	Name: "RpowHeadSumBound",
	Key:  "prop_d15d6cb33c1eca14",
	Reading: "The term N^x/N is needed only for x > 1, where " +
		"the last term is not covered by a step ending at N.",
	Build: family.Sections(Statement{
		Binders: "∀x:real. ∀N:num.",
		Hypotheses: []string{
			"&0 < x",
			"0 < N",
		},
		Conclusion: "Σ_{n∈1 .. N} real_rpow(&n, x - &1) ≤ real_rpow(&N, x) * (&1 / &N + &1 / x)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			slopeEstimate := ctx.Lemma(Statement{
				Binders: "∀x:real. ∀n:num.",
				Hypotheses: []string{
					"&0 < x",
					"0 < n",
				},
				Conclusion: "(x ≤ &1 ⇒ " +
					"    x * real_rpow(&(n + 1), x - &1) ≤ real_rpow(&(n + 1), x) - real_rpow(&n, x)) ∧ " +
					"(&1 < x ⇒ x * real_rpow(&n, x - &1) ≤ real_rpow(&(n + 1), x) - real_rpow(&n, x))",
			},
				func(a *Argument, x *Expr[Real], n *Expr[Nat], conditions Fact) {
					derivative := a.Have(
						"the derivative of the x-th power is x times the power with exponent x minus one",
						"∀t:real. &0 < t ⇒ real_derivative_at(λy:real. real_rpow(y, x), t, x * real_rpow(t, x - &1))",
						By(RpowDerivativeBase))
					positiveInterval := a.Have(
						"the positive reals form an interval",
						"real_interval({t:real | &0 < t})",
						Unfold(real_topology.RealIntervalDef),
						ByArith())
					endpoints := a.Have(
						"the consecutive endpoints are positive and strictly ordered",
						"&0 < &n ∧ &0 < &(n + 1) ∧ &n < &(n + 1)",
						ByArith(conditions))
					left := a.TermAs[Real]("&n")
					right := a.TermAs[Real]("&(n + 1)")
					c, meanValue := a.ObtainAs[Real](
						"the mean value theorem realizes the power increment at an interior point",
						"∃c:real. "+
							"    &n < c ∧ "+
							"    c < &(n + 1) ∧ "+
							"    real_rpow(&(n + 1), x) - real_rpow(&n, x) = x * real_rpow(c, x - &1) * (&(n + 1) - &n)",
						By(
							positiveInterval,
							derivative,
							endpoints,
							real_derivative.MeanValueOnInterval.At(
								a.TermAs[Fun[Real, Real]]("λt:real. real_rpow(t, x)"),
								a.TermAs[Fun[Real, Real]]("λt:real. x * real_rpow(t, x - &1)"),
								a.TermAs[Set[Real]]("{t:real | &0 < t}"),
								left,
								right)))
					increment := a.Have(
						"the unit interval makes the increment equal to the derivative at c",
						"real_rpow(&(n + 1), x) - real_rpow(&n, x) = x * real_rpow(c, x - &1)",
						ByArith(meanValue))
					a.Show(
						"compare the derivative at c to the appropriate endpoint slope",
						SplitConj(
							Case(
								"when x is at most one the right endpoint gives the lower slope",
								Derive(func(b *Argument) {
									atMostOne := b.Assume()
									decreasing := b.Have(
										"the power with exponent at most 0 decreases from c to the right endpoint",
										"real_rpow(&(n + 1), x - &1) ≤ real_rpow(c, x - &1)",
										ByArith(
											atMostOne,
											meanValue,
											endpoints,
											RpowLessEqBaseNonpos.At(c, right, b.TermAs[Real]("x - &1"))))
									b.Show(
										"multiply the slope comparison by positive x and use the increment formula",
										ByArith(increment, decreasing, conditions))
								})),
							Case(
								"when x exceeds one the left endpoint gives the lower slope",
								Derive(func(b *Argument) {
									aboveOne := b.Assume()
									b.Show(
										"the positive-exponent slope increases between the left endpoint and c",
										ByArith(
											increment,
											aboveOne,
											conditions,
											meanValue,
											endpoints,
											RpowLessBase.At(left, c, b.TermAs[Real]("x - &1"))))
								}))))
				})
			return ctx.Theorem(headline,
				func(a *Argument, x *Expr[Real], N *Expr[Nat], conditions Fact) {
					head := a.BigOpAs[Nat, Real]("Σ_{n∈1 .. N} real_rpow(&n, x - &1)")
					one := a.TermAs[Nat]("1")
					moreThanOne := a.Unless(
						a.TermAs[Bool]("N = 1"),
						"with one summand the positive reciprocal exponent supplies the excess in the bound",
						Given(func(b *Argument, singleton Fact) {
							b.Show(
								"the sole summand and the final power are one",
								ByArith(
									singleton,
									conditions,
									real_sum.IntervalPoint.At(one, head.Summand()),
									RpowOneBase.At(b.TermAs[Real]("x - &1")),
									RpowOneBase.At(x),
									real_order_field.DivPos.At(b.TermAs[Real]("&1"), x)))
						}))
					last := a.TermAs[Nat]("N - 1")
					endpoint := a.Have(
						"the step interval is nonempty and its final successor is N",
						"1 ≤ N - 1 ∧ N - 1 + 1 = N",
						ByArith(moreThanOne, conditions))
					increments := a.BigOpAs[Nat, Real]("Σ_{k∈1 .. N - 1} (real_rpow(&(k + 1), x) - real_rpow(&k, x))")
					telescope := a.Have(
						"the consecutive power increments telescope from one to the final power",
						"Σ_{k∈1 .. N - 1} (real_rpow(&(k + 1), x) - real_rpow(&k, x)) = real_rpow(&N, x) - &1",
						By(
							endpoint,
							RpowOneBase.At(x),
							real_sum.TelescopeUp.At(one, last, a.TermAs[Fun[Nat, Real]]("λk:num. real_rpow(&k, x)"))))
					a.Cases(a.TermAs[Bool]("x ≤ &1"))
					a.When(
						"for x at most one, match every term after the first to a step ending at its index",
						func(b *Argument, atMostOne Fact) {
							steps := b.Have(
								"each right endpoint summand times x is bounded by its consecutive power increment",
								Statement{
									Binders:    "∀k:num.",
									Hypotheses: []string{"1 ≤ k", "k ≤ N - 1"},
									Conclusion: "x * real_rpow(&(k + 1), x - &1) ≤ real_rpow(&(k + 1), x) - real_rpow(&k, x)",
								},
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]("k")
									inRange := d.Assume()
									d.Show(
										"the right endpoint slope estimate applies at every positive step index",
										ByArith(atMostOne, inRange, conditions, At(slopeEstimate, x, k)))
								}))
							shifted := b.BigOpAs[Nat, Real]("Σ_{k∈1 .. N - 1} real_rpow(&(k + 1), x - &1)")
							shift := b.Have(
								"shifting the indices identifies the right endpoint sum with the tail after one",
								"Σ_{k∈1 .. N - 1} real_rpow(&(k + 1), x - &1) = Σ_{n∈2 .. N} real_rpow(&n, x - &1)",
								ByArith(endpoint, real_sum.Shift.At(one, last, one, head.Summand())))
							weighted := b.BigOpAs[Nat, Real]("Σ_{k∈1 .. N - 1} x * real_rpow(&(k + 1), x - &1)")
							tailBound := b.Have(
								"sum the step estimates, pull out x, and telescope",
								"x * (Σ_{n∈2 .. N} real_rpow(&n, x - &1)) ≤ real_rpow(&N, x) - &1",
								ByArith(
									steps,
									shift,
									telescope,
									real_sum.ScalarLeft.At(x, shifted.Summand(), shifted.Range()),
									real_sum.IntervalMonotone.At(one, last, weighted.Summand(), increments.Summand())))
							headBound := b.Have(
								"the first term is one and x is at most one, so "+
									"the whole head is bounded by the final power over x",
								"Σ_{n∈1 .. N} real_rpow(&n, x - &1) ≤ real_rpow(&N, x) / x",
								ByArith(
									atMostOne,
									tailBound,
									conditions,
									real_sum.PeelLeft.At(one, N, head.Summand()),
									RpowOneBase.At(b.TermAs[Real]("x - &1"))))
							b.Show(
								"adding the positive final power over N gives the claimed bound",
								ByArith(
									headBound,
									conditions,
									RpowPositive.At(b.TermAs[Real]("&N"), x),
									real_order_field.DivPos.At(
										b.TermAs[Real]("real_rpow(&N, x)"),
										b.TermAs[Real]("&N"))))
						})
					a.Otherwise(
						"for x above one, match every term before the last to a step starting at its index",
						func(b *Argument, aboveOne Fact) {
							steps := b.Have(
								"each left endpoint summand times x is bounded by its consecutive power increment",
								"∀k:num. 1 ≤ k ∧ k ≤ N - 1 ⇒ x * real_rpow(&k, x - &1) ≤ real_rpow(&(k + 1), x) - real_rpow(&k, x)",
								Derive(func(d *Argument) {
									k := d.FixAs[Nat]("k")
									inRange := d.Assume()
									d.Show(
										"the left endpoint slope estimate applies at every positive step index",
										ByArith(aboveOne, inRange, conditions, At(slopeEstimate, x, k)))
								}))
							early := b.BigOpAs[Nat, Real]("Σ_{k∈1 .. N - 1} real_rpow(&k, x - &1)")
							weighted := b.BigOpAs[Nat, Real]("Σ_{k∈1 .. N - 1} x * real_rpow(&k, x - &1)")
							earlyBound := b.Have(
								"sum the step estimates, pull out x, and telescope",
								"x * (Σ_{k∈1 .. N - 1} real_rpow(&k, x - &1)) ≤ real_rpow(&N, x) - &1",
								ByArith(
									steps,
									telescope,
									real_sum.ScalarLeft.At(x, early.Summand(), early.Range()),
									real_sum.IntervalMonotone.At(one, last, weighted.Summand(), increments.Summand())))
							finalTerm := b.Have(
								"the last summand is the final power divided by N",
								"real_rpow(&N, x - &1) = real_rpow(&N, x) / &N",
								ByArith(
									conditions,
									real_ring.SubAddRight.At(x, b.TermAs[Real]("&1")),
									RpowAdd.At(
										b.TermAs[Real]("&N"),
										b.TermAs[Real]("x - &1"),
										b.TermAs[Real]("&1")),
									RpowOneExponent.At(b.TermAs[Real]("&N"))))
							b.Show(
								"peel off the last term and add its exact value to the bound for the earlier terms",
								ByArith(
									finalTerm,
									earlyBound,
									conditions,
									real_order_field.DivPos.At(b.TermAs[Real]("&1"), x),
									real_order_field.LessEqDivMulLeft.At(early, b.TermAs[Real]("real_rpow(&N, x) - &1"), x),
									real_sum.PeelRight.At(N, one, head.Summand())))
						})
				})
		}),
})}

// RpowSeriesConverges — the negative-power series converges when its
// exponent is above one, with the sum bounded by one plus the reciprocal
// exponent gap. The tail estimate bounds all partial sums; their terms
// are nonnegative, so they increase to a limit that retains the bound.
var RpowSeriesConverges = rpowSeriesConvergesThm{family.Add(registry.ProofEntry{
	Name:    "RpowSeriesConverges",
	Key:     "prop_f3f973a948494b46",
	Reading: "The series is indexed from n = 1 by the shift n + 1; at σ ≤ 1 it has no sum.",
	Build: family.Theorem(Statement{
		Binders:    "∀σ:real.",
		Hypotheses: []string{"&1 < σ"},
		Conclusion: "∃t:real. real_sums(λn:num. real_rpow(&(n + 1), -σ), t) ∧ t ≤ &1 + &1 / (σ - &1)",
	},
		func(a *Argument, σ *Expr[Real], aboveOne Fact) {
			δ, gapDef := a.LetAs[Real]("δ", "σ - &1")
			B, boundDef := a.LetAs[Real]("B", "&1 + &1 / δ")
			s, partialDef := a.LetAs[Fun[Nat, Real]]("s", "λN:num. Σ_{k∈0 .. N} real_rpow(&(k + 1), -σ)")
			gap := a.Have(
				"the exponent gap is positive and the tail exponent simplifies to -σ",
				"&0 < δ ∧ -δ - &1 = -σ",
				ByArith(gapDef, aboveOne))
			zero := a.TermAs[Nat]("0")
			one := a.TermAs[Nat]("1")
			powers := a.TermAs[Fun[Nat, Real]]("λk:num. real_rpow(&k, -σ)")
			negativeSigma := a.TermAs[Real]("-σ")
			bounded := a.Have(
				"every partial sum is at most one plus the reciprocal exponent gap",
				"∀N:num. s(N) ≤ B",
				partialDef.Rw(),
				Derive(func(b *Argument) {
					N := b.FixAs[Nat]("N")
					top := b.TermAs[Nat]("N + 1")
					tail := b.Have(
						"the terms after the first are bounded by the reciprocal gap",
						"Σ_{k∈2 .. N + 1} real_rpow(&k, -σ) ≤ &1 / δ",
						Derive(func(c *Argument) {
							parts := c.Conjuncts(
								gap,
								"the gap δ is positive",
								"the tail exponent is -σ")
							c.Show(
								"apply the tail bound at the positive gap and starting index one",
								parts[1].RwRev(),
								ByArith(parts[0], RpowTailSumBound.At(δ, one, top), RpowOneBase.At(c.TermAs[Real]("-δ"))))
						}))
					b.Show(
						"shift to index one, peel off its unit value, and bound the remaining tail",
						ByArith(
							boundDef,
							tail,
							real_sum.Shift.At(zero, N, one, powers),
							real_sum.PeelLeft.At(one, top, powers),
							RpowOneBase.At(negativeSigma)))
				}))
			shiftedPowers := a.TermAs[Fun[Nat, Real]]("λk:num. real_rpow(&(k + 1), -σ)")
			increasing := a.Have(
				"the partial sums increase because each newly added term is nonnegative",
				"∀N:num. s(N) ≤ s(N + 1)",
				partialDef.Rw(),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("N")
					b.Show(
						"peel off the next nonnegative power",
						ByArith(
							real_sum.PeelRight.At(b.TermAs[Nat]("N + 1"), zero, shiftedPowers),
							RpowNonneg.At(b.TermAs[Real]("&(N + 1 + 1)"), negativeSigma)))
				}))
			L, limitDef := a.LetAs[Real]("L", "sup(image(s, 𝕌))")
			limit := a.Have(
				"the bounded increasing partial sums tend to their supremum",
				"s ⟶ L",
				limitDef.Rw(),
				By(increasing, bounded, Where(real_sequences.IncreasingBoundedConvergesToSup, "B", B)))
			limitBound := a.Have(
				"the limit retains the upper bound of every partial sum",
				"L ≤ B",
				By(
					bounded,
					limit,
					real_sequences.LimitConst.At(B),
					Where(real_sequences.LimitLessEq, "a", s).Where("b", a.TermAs[Fun[Nat, Real]]("λn:num. B")).Where(
						"N", zero)))
			a.Take(L)
			a.Show(
				"the partial-sum limit is the series sum, with the claimed bound",
				Unfold(real_series.RealSumsDef),
				partialDef.RwRev(),
				By(limit, limitBound))
		}),
})}

// LogLessEqRpow — the logarithm is below every positive power above 1:
// exp lies above its tangent at zero, evaluated at the nonnegative
// ε·log x; division by the positive ε gives the bound.
var LogLessEqRpow = logLessEqRpowThm{family.Add(registry.ProofEntry{
	Name: "LogLessEqRpow",
	Key:  "prop_179e46ae83d444bd",
	Build: family.Theorem(Statement{
		Binders: "∀ε x:real.",
		Hypotheses: []string{
			"&0 < ε",
			"&1 ≤ x",
		},
		Conclusion: "log(x) ≤ real_rpow(x, ε) / ε",
	},
		func(a *Argument, ε, x *Expr[Real], conditions Fact) {
			exponentialBound := a.Have(
				"exp's tangent at zero gives the bound when evaluated at nonnegative ε·log x",
				"&1 + ε * log(x) ≤ exp(ε * log(x))",
				ByArith(
					conditions,
					real_exp_log.LogNonneg.At(x),
					real_exp_log.ExpLowerBound.At(a.TermAs[Real]("ε * log(x)"))))
			a.Show(
				"the exponential is x^ε, and division by positive ε gives the bound",
				ByArith(exponentialBound, conditions, RpowExp.At(x, ε)))
		}),
})}

// LogOverRpowTendsToZero — the logarithm divided by any positive power
// tends to zero. The quotient is squeezed between zero and a scaled
// negative half power, which tends to zero.
var LogOverRpowTendsToZero = logOverRpowTendsToZeroThm{family.Add(registry.ProofEntry{
	Name: "LogOverRpowTendsToZero",
	Key:  "prop_d054c9f58143f000",
	Build: family.Theorem(Statement{
		Binders:    "∀ε:real.",
		Hypotheses: []string{"&0 < ε"},
		Conclusion: "(λn:num. log(&(n + 1)) / real_rpow(&(n + 1), ε)) ⟶ &0",
	},
		func(a *Argument, ε *Expr[Real], positive Fact) {
			δ, halfDef := a.LetAs[Real]("δ", "ε / &2")
			half := a.Have(
				"the half exponent is positive and cancels half the full exponent",
				"&0 < δ ∧ -δ + ε = δ",
				ByArith(halfDef, positive))
			inverseHalf := a.TermAs[Real]("real_inv(δ)")
			bounds := a.Have(
				"the logarithmic quotient lies between zero and the scaled negative half power",
				"∀n:num. "+
					"    &0 ≤ log(&(n + 1)) / real_rpow(&(n + 1), ε) ∧ "+
					"    log(&(n + 1)) / real_rpow(&(n + 1), ε) ≤ real_inv(δ) * real_rpow(&(n + 1), -δ)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					base := b.TermAs[Real]("&(n + 1)")
					baseBounds := b.Have(
						"each shifted natural base is at least one and positive",
						"&1 ≤ &(n + 1) ∧ &0 < &(n + 1)",
						ByArith())
					powerCancellation := b.Have(
						"multiplying the negative half power by the full power leaves the positive half power",
						"real_rpow(&(n + 1), -δ) * real_rpow(&(n + 1), ε) = real_rpow(&(n + 1), δ)",
						By(baseBounds, half, RpowAdd.At(base, b.TermAs[Real]("-δ"), ε)))
					b.Show(
						"log is nonnegative above one, and its half-power bound gives the upper estimate",
						ByArith(
							Scaled(inverseHalf, powerCancellation),
							baseBounds,
							half,
							real_exp_log.LogNonneg.At(base),
							RpowPositive.At(base, ε),
							LogLessEqRpow.At(δ, base)))
				}))
			zero := a.TermAs[Real]("&0")
			negativePower := a.TermAs[Fun[Nat, Real]]("λn:num. real_rpow(&(n + 1), -δ)")
			upper := a.TermAs[Fun[Nat, Real]]("λn:num. real_inv(δ) * real_rpow(&(n + 1), -δ)")
			upperLimit := a.Have(
				"the negative half power tends to zero, and scaling preserves that limit",
				"(λn:num. real_inv(δ) * real_rpow(&(n + 1), -δ)) ⟶ &0",
				ByArith(
					half,
					RpowNegTendsToZero.At(δ),
					real_sequences.LimitScale.At(negativePower, zero, inverseHalf)))
			a.Show(
				"the quotient tends to zero by the squeeze theorem",
				By(
					bounds,
					upperLimit,
					real_sequences.LimitConst.At(zero),
					Where(real_sequences.LimitSqueeze, "a", a.TermAs[Fun[Nat, Real]]("λn:num. &0")).Where(
						"c", upper).Where(
						"N", a.TermAs[Nat]("0"))))
		}),
})}

// RpowNegTendsToZero — a negative power of the positive naturals tends to
// zero. A natural bound above (1/ε)^(1/δ) makes the positive δ-th power
// exceed 1/ε; taking reciprocals gives the required error bound.
var RpowNegTendsToZero = rpowNegTendsToZeroThm{family.Add(registry.ProofEntry{
	Name: "RpowNegTendsToZero",
	Key:  "prop_2cdae7bc61f664aa",
	Build: family.Theorem(Statement{
		Binders:    "∀δ:real.",
		Hypotheses: []string{"&0 < δ"},
		Conclusion: "(λn:num. real_rpow(&(n + 1), -δ)) ⟶ &0",
	},
		func(a *Argument, δ *Expr[Real], positiveExponent Fact) {
			a.Do(Unfold(real_sequences.RealConvergesToDef))
			ε := a.FixAs[Real]("ε")
			positiveError := a.Assume()
			B, thresholdDef := a.LetAs[Real]("B", "real_rpow(real_inv(ε), real_inv(δ))")
			threshold := a.Have(
				"B is positive and its δ-th power is exactly 1/ε",
				"&0 < B ∧ real_rpow(B, δ) = real_inv(ε)",
				Derive(func(b *Argument) {
					b.Show(
						"the power of a power has exponent 1, and a positive base has a positive power",
						ByArith(
							thresholdDef,
							positiveExponent,
							positiveError,
							real_order_ring.NonzeroOfPositive.At(δ),
							field.MulLeftInverse.Read(real_field.Field).At(δ),
							RpowPositive.At(b.TermAs[Real]("real_inv(ε)"), b.TermAs[Real]("real_inv(δ)")),
							RpowRpow.At(b.TermAs[Real]("real_inv(ε)"), b.TermAs[Real]("real_inv(δ)"), δ),
							RpowOneExponent.At(b.TermAs[Real]("real_inv(ε)"))))
				}))
			N, aboveThreshold := a.ObtainAs[Nat](
				"Archimedes places B below a natural number",
				"∃N:num. B ≤ &N",
				By(real_archimedean.ExistsNumAbove))
			a.Take(N)
			a.FixAs[Nat]("n")
			past := a.Assume()
			base := a.TermAs[Real]("&(n + 1)")
			largePower := a.Have(
				"beyond N, the positive δ-th power exceeds 1/ε",
				"real_inv(ε) < real_rpow(&(n + 1), δ)",
				ByArith(past, aboveThreshold, positiveExponent, threshold, RpowLessBase.At(B, base, δ)))
			a.Show(
				"taking reciprocals puts the nonnegative negative power within ε of zero",
				ByArith(
					largePower,
					positiveError,
					RpowNeg.At(base, δ),
					real_order_field.InvAntitone.At(
						a.TermAs[Real]("real_inv(ε)"), a.TermAs[Real]("real_rpow(&(n + 1), δ)")),
					field.InvInv.Read(real_field.Field).At(ε),
					real_sgn_abs.AbsBetween.At(a.TermAs[Real]("&0"), a.TermAs[Real]("real_rpow(&(n + 1), -δ)"), ε),
					RpowNonneg.At(base, a.TermAs[Real]("-δ"))))
		}),
})}

// LogRpowSeriesConverges — the logarithm-weighted negative-power series
// converges for exponents above one. A small positive power bounds the
// logarithm, leaving a convergent power series after multiplication;
// scaling that series gives an absolute comparison.
var LogRpowSeriesConverges = logRpowSeriesConvergesThm{family.Add(registry.ProofEntry{
	Name: "LogRpowSeriesConverges",
	Key:  "prop_310d16320cedc5f2",
	Build: family.Theorem(Statement{
		Binders:    "∀σ:real.",
		Hypotheses: []string{"&1 < σ"},
		Conclusion: "∃t:real. real_sums(λn:num. log(&(n + 1)) * real_rpow(&(n + 1), -σ), t)",
	},
		func(a *Argument, σ *Expr[Real], aboveOne Fact) {
			ε, smallDef := a.LetAs[Real]("ε", "(σ - &1) / &2")
			q, comparisonDef := a.LetAs[Real]("q", "σ - ε")
			exponents := a.Have(
				"the logarithmic exponent is positive, the comparison "+
					"exponent is above one, and the product exponents agree",
				"&0 < ε ∧ &1 < q ∧ ε + -σ = -q",
				ByArith(comparisonDef, smallDef, aboveOne))
			parts := a.Conjuncts(
				exponents,
				"ε is positive",
				"q is above one",
				"the product exponent is -q")
			inverseSmall := a.TermAs[Real]("real_inv(ε)")
			negativeSigma := a.TermAs[Real]("-σ")
			domination := a.Have(
				"each logarithm-weighted term is absolutely dominated by the scaled q-power term",
				"∀n:num. |log(&(n + 1)) * real_rpow(&(n + 1), -σ)| ≤ real_inv(ε) * real_rpow(&(n + 1), -q)",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					base := b.TermAs[Real]("&(n + 1)")
					baseBounds := b.Have(
						"the shifted natural base is at least one and positive",
						"&1 ≤ &(n + 1) ∧ &0 < &(n + 1)",
						ByArith())
					powerProduct := b.Have(
						"the small positive power times the original negative power is the comparison power",
						"real_rpow(&(n + 1), ε) * real_rpow(&(n + 1), -σ) = real_rpow(&(n + 1), -q)",
						By(baseBounds, parts[2], RpowAdd.At(base, ε, negativeSigma)))
					rawBounds := b.Have(
						"log is nonnegative above one, and its ε-power bound gives the product estimate",
						"&0 ≤ log(&(n + 1)) * real_rpow(&(n + 1), -σ) ∧ "+
							"log(&(n + 1)) * real_rpow(&(n + 1), -σ) ≤ real_inv(ε) * real_rpow(&(n + 1), -q)",
						ByArith(
							Scaled(inverseSmall, powerProduct),
							baseBounds,
							parts[0],
							real_exp_log.LogNonneg.At(base),
							RpowNonneg.At(base, negativeSigma),
							LogLessEqRpow.At(ε, base)))
					b.Show(
						"the term is nonnegative, so its absolute value obeys the same estimate",
						ByArith(
							rawBounds,
							real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("log(&(n + 1)) * real_rpow(&(n + 1), -σ)"))))
				}))
			comparison := a.TermAs[Fun[Nat, Real]]("λn:num. real_rpow(&(n + 1), -q)")
			t, comparisonSum := a.ObtainAs[Real](
				"the q-power series has a sum because q is above one",
				"∃t:real. real_sums(λn:num. real_rpow(&(n + 1), -q), t)",
				By(parts[1], RpowSeriesConverges.At(q)))
			scaled := a.TermAs[Fun[Nat, Real]]("λn:num. real_inv(ε) * real_rpow(&(n + 1), -q)")
			a.Show(
				"scale the convergent q-power series and apply absolute comparison from index zero",
				By(
					domination,
					comparisonSum,
					real_series.SumsScale.At(comparison, t, inverseSmall),
					Where(real_series.Comparison, "b", scaled).Where("N", a.TermAs[Nat]("0"))))
		}),
})}
