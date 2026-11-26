// sums.go — the algebra and order of sums: uniqueness, termwise sums,
// differences and multiples, the series of zeros, order against another
// series and against the partial
// sums, dropping the first terms, summing two terms at a time, and the
// bounds on the sum of an alternating series.

package real_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// SumsUnique — a series has at most one sum: two sums are two limits of
// one sequence of partial sums.
var SumsUnique = sumsUniqueThm{family.Add(registry.ProofEntry{
	Name: "SumsUnique",
	Key:  "prop_9857829eb19e0ab4",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀s t:real.",
		Hypotheses: []string{
			"real_sums(a, s)",
			"real_sums(a, t)",
		},
		Conclusion: "s = t",
	},
		func(arg *Argument, a *Arrow[Nat, Real], s, t *Expr[Real], sums Fact) {
			partial := arg.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k∈0 .. n} a(k)")
			arg.Show(
				"both are limits of the partial sums, and a sequence has one limit",
				By(sums, RealSumsDef, real_sequences.LimitUnique.At(partial, s, t)))
		}),
})}

// SumsAdd — the termwise sum of two series sums to the sum of their
// sums: each partial sum of a + b is the sum of the partial sums of a
// and b, and limits add.
var SumsAdd = sumsAddThm{family.Add(registry.ProofEntry{
	Name: "SumsAdd",
	Key:  "prop_18744c364a199cb8",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀s t:real.",
		Hypotheses: []string{
			"real_sums(a, s)",
			"real_sums(b, t)",
		},
		Conclusion: "real_sums(λn:num. a(n) + b(n), s + t)",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], s, t *Expr[Real], sums Fact) {
			toS := arg.Have(
				"a's partial sums tend to s",
				"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
				By(sums, RealSumsDef))
			toT := arg.Have(
				"b's partial sums tend to t",
				"(λn:num. Σ_{k∈0 .. n} b(k)) ⟶ t",
				By(sums, RealSumsDef))
			both := arg.Have(
				"so their sum tends to s + t",
				"(λn:num. Σ_{k∈0 .. n} a(k) + Σ_{k∈0 .. n} b(k)) ⟶ s + t",
				By(real_sequences.LimitAdd, toS, toT))
			termwise := arg.Have(
				"and the partial sum of a + b is the sum of the partial sums",
				"(λn:num. Σ_{k∈0 .. n} (a(k) + b(k))) ⟶ s + t",
				Derive(func(d *Argument) {
					d.Do(Simp(Rev(real_sum.IntervalAdd)))
					d.Show(
						"Σ (a(k) + b(k)) read back as Σ a(k) + Σ b(k)",
						By(both))
				}))
			arg.Show(
				"which is what the series a + b summing to s + t says",
				By(termwise, RealSumsDef))
		}),
})}

// SumsScale — a scalar multiple of a series sums to the multiple of its
// sum: each partial sum of c·a is c times the partial sum of a, and
// limits scale.
var SumsScale = sumsScaleThm{family.Add(registry.ProofEntry{
	Name: "SumsScale",
	Key:  "prop_ee4657ac4de2f04f",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀s c:real.",
		Hypotheses: []string{
			"real_sums(a, s)",
		},
		Conclusion: "real_sums(λn:num. c * a(n), c * s)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], s, c *Expr[Real], sums Fact) {
			toS := arg.Have(
				"a's partial sums tend to s",
				"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
				By(sums, RealSumsDef))
			scaled := arg.Have(
				"so c times them tends to c·s",
				"(λn:num. c * Σ_{k∈0 .. n} a(k)) ⟶ c * s",
				By(real_sequences.LimitScale, toS))
			termwise := arg.Have(
				"and the partial sum of c·a is c times the partial sum of a",
				"(λn:num. Σ_{k∈0 .. n} c * a(k)) ⟶ c * s",
				Derive(func(d *Argument) {
					d.Do(Simp(Rev(real_sum.ScalarLeft.Inst[Nat]())))
					d.Show(
						"Σ c·a(k) read back as c·Σ a(k)",
						By(scaled))
				}))
			arg.Show(
				"which is what the series c·a summing to c·s says",
				By(termwise, RealSumsDef))
		}),
})}

// SumsSub — the difference of two series sums to the difference of
// their sums: the partial sums of a − b are the differences of the
// partial sums, which tend to s − t.
var SumsSub = sumsSubThm{family.Add(registry.ProofEntry{
	Name: "SumsSub",
	Key:  "prop_944fba684a7ae6b7",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀s t:real.",
		Hypotheses: []string{
			"real_sums(a, s)",
			"real_sums(b, t)",
		},
		Conclusion: "real_sums(λn:num. a(n) - b(n), s - t)",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], s, t *Expr[Real], sums Fact) {
			toS := arg.Have(
				"a's partial sums tend to s",
				"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
				By(sums, RealSumsDef))
			toT := arg.Have(
				"b's partial sums tend to t",
				"(λn:num. Σ_{k∈0 .. n} b(k)) ⟶ t",
				By(sums, RealSumsDef))
			both := arg.Have(
				"so their difference tends to s − t",
				"(λn:num. Σ_{k∈0 .. n} a(k) - Σ_{k∈0 .. n} b(k)) ⟶ s - t",
				By(real_sequences.LimitSub, toS, toT))
			termwise := arg.Have(
				"and the partial sum of a − b is the difference of the partial sums",
				"(λn:num. Σ_{k∈0 .. n} (a(k) - b(k))) ⟶ s - t",
				Derive(func(d *Argument) {
					d.Do(Simp(Fwd(real_sum.IntervalSub)))
					d.Show(
						"Σ (a(k) − b(k)) read back as Σ a(k) − Σ b(k)",
						By(both))
				}))
			arg.Show(
				"which is what the series a − b summing to s − t says",
				By(termwise, RealSumsDef))
		}),
})}

// SumsZero — the series of zeros sums to 0: every partial sum is 0, and
// a constant sequence tends to its value.
var SumsZero = sumsZeroThm{family.Add(registry.ProofEntry{
	Name: "SumsZero",
	Key:  "prop_a3c5cb7bef4bfbe5",
	Build: family.Theorem("real_sums(λn:num. &0, &0)",
		func(arg *Argument) {
			arg.Show(
				"every partial sum is a sum of zeros, 0, and the constant sequence 0 tends to 0",
				Simp(Fwd(RealSumsDef)),
				Simp(Fwd(real_sum.Zero.Inst[Nat]())),
				By(real_sequences.LimitConst.At(arg.TermAs[Real]("&0"))))
		}),
})}

// SumsLessEq — a series nowhere above another sums to no more: its
// partial sums are nowhere above the other's, and limits keep order.
var SumsLessEq = sumsLessEqThm{family.Add(registry.ProofEntry{
	Name: "SumsLessEq",
	Key:  "prop_de8949d94e69c69f",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀s t:real.",
		Hypotheses: []string{
			"∀n:num. a(n) ≤ b(n)",
			"real_sums(a, s)",
			"real_sums(b, t)",
		},
		Conclusion: "s ≤ t",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], s, t *Expr[Real], hyps Fact) {
			parts := arg.Conjuncts(
				hyps,
				"a is nowhere above b",
				"a sums to s",
				"b sums to t")
			below, sumsA, sumsB := parts[0], parts[1], parts[2]
			toS := arg.Have(
				"a's partial sums tend to s",
				"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
				By(sumsA, RealSumsDef))
			toT := arg.Have(
				"b's partial sums tend to t",
				"(λn:num. Σ_{k∈0 .. n} b(k)) ⟶ t",
				By(sumsB, RealSumsDef))
			zero := arg.TermAs[Nat]("0")
			partial := arg.Have(
				"each partial sum of a is at most b's, term by term — "+
					"stated from index 0, the guard the order of limits reads",
				"∀n:num. 0 ≤ n ⇒ Σ_{k∈0 .. n} a(k) ≤ Σ_{k∈0 .. n} b(k)",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return By(below, real_sum.IntervalMonotone.At(zero, n, a, b))
				}))
			arg.Show(
				"limits keep order",
				By(partial, toS, toT, real_sequences.LimitLessEq))
		}),
})}

// SumsPartialLessEq — a partial sum of a nonnegative series is at most
// its sum. Past index n the partial sums only take in more nonnegative
// terms, so none of them falls below the one up to n; the constant
// sequence at that partial sum tends to it, and limits keep an order
// that holds past some index.
var SumsPartialLessEq = sumsPartialLessEqThm{family.Add(registry.ProofEntry{
	Name: "SumsPartialLessEq",
	Key:  "prop_cf451598accdca4d",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀s:real. ∀n:num.",
		Hypotheses: []string{
			"∀n:num. &0 ≤ a(n)",
			"real_sums(a, s)",
		},
		Conclusion: "Σ_{k∈0 .. n} a(k) ≤ s",
	},
		func(arg *Argument, a *Arrow[Nat, Real], s *Expr[Real], n *Expr[Nat], hyps Fact) {
			parts := arg.Conjuncts(
				hyps,
				"the terms of a are nonnegative",
				"a sums to s")
			nonneg, sums := parts[0], parts[1]
			zero := arg.TermAs[Nat]("0")
			grows := arg.Have(
				"past n no partial sum falls below the one up to n: the sum up to m adds only nonnegative terms",
				"∀m:num. n ≤ m ⇒ Σ_{k∈0 .. n} a(k) ≤ Σ_{k∈0 .. m} a(k)",
				arg.ForEach(func(m *Expr[Nat]) Action {
					return By(Normalized, nonneg, real_sum.IntervalExtend.At(zero, n, m, a))
				}))
			toS := arg.Have(
				"the partial sums tend to s",
				"(λm:num. Σ_{k∈0 .. m} a(k)) ⟶ s",
				By(sums, RealSumsDef))
			arg.Show(
				"the constant sequence at the partial sum up to n tends to it, and limits keep order past n",
				By(
					grows,
					toS,
					real_sequences.LimitConst.At(arg.TermAs[Real]("Σ_{k∈0 .. n} a(k)")),
					real_sequences.LimitLessEq))
		}),
})}

// SumsShift — dropping a series' first term drops it from the sum.
// Peeling a(0) off a partial sum of a to n + 1 leaves the shifted
// series' partial sum to n. So a's partial sums tend to s exactly when
// they do from n + 1 on, and subtracting the constant a(0) from those,
// or adding it back to the shifted series' partial sums, carries the
// limit between s and s − a(0).
var SumsShift = sumsShiftThm{family.Add(registry.ProofEntry{
	Name: "SumsShift",
	Key:  "prop_64864d8474d725aa",
	Build: family.Theorem("∀a:(num → real). ∀s:real. "+
		"    real_sums(a, s) ⇔ real_sums(λn:num. a(n + 1), s - a(0))",
		func(arg *Argument, a *Arrow[Nat, Real], s *Expr[Real]) {
			peel := arg.Have(
				"a partial sum to n + 1 is a(0) plus the shifted series' partial sum to n",
				"∀n:num. Σ_{k∈0 .. n + 1} a(k) = a(0) + Σ_{k∈0 .. n} a(k + 1)",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					zero, next := d.TermAs[Nat]("0"), d.TermAs[Nat]("n + 1")
					d.Show(
						"peel a(0) off the interval 0 .. n + 1, and index the rest from 0",
						By(
							real_sum.PeelLeft.At(zero, next, a),
							nat_order.ZeroLessEq.At(next),
							real_sum.Shift.At(zero, n, d.TermAs[Nat]("1"), a)))
				}))
			rest := arg.Have(
				"so the shifted series' partial sum to n is a's to n + 1 less a(0)",
				"∀n:num. Σ_{k∈0 .. n} a(k + 1) = Σ_{k∈0 .. n + 1} a(k) - a(0)",
				arg.ForEach(func(n *Expr[Nat]) Action { return ByArith(peel.At(n)) }))

			// The two directions carry the limit through the same partial
			// sums and the same constant a(0).
			partialSums := arg.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k∈0 .. n} a(k)")
			constantFirst := arg.TermAs[Fun[Nat, Real]]("λn:num. a(0)")
			first := arg.TermAs[Real]("a(0)")
			arg.Iff()
			arg.Forward(
				"a's partial sums from n + 1 on tend to s, and less a(0) they are the shifted series'",
				func(b *Argument, sums Fact) {
					toSum := b.Have(
						"a's partial sums tend to s",
						"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
						By(sums, RealSumsDef))
					fromNext := b.Have(
						"so they do from n + 1 on",
						"(λn:num. Σ_{k∈0 .. n + 1} a(k)) ⟶ s",
						By(toSum, real_sequences.LimitShift.At(partialSums, s)))
					nextPartialSums := b.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k∈0 .. n + 1} a(k)")
					less := b.Have(
						"less the constant a(0), they tend to s − a(0)",
						"(λn:num. Σ_{k∈0 .. n + 1} a(k) - a(0)) ⟶ s - a(0)",
						By(
							fromNext,
							real_sequences.LimitSub.At(nextPartialSums, constantFirst, s, first),
							real_sequences.LimitConst.At(first)))
					b.Show(
						"and these are the shifted series' partial sums",
						By(less, rest, RealSumsDef))
				})
			arg.Backward(
				"the shifted series' partial sums plus a(0) are a's from n + 1 on, and they tend to s",
				func(b *Argument, sums Fact) {
					toRemainder := b.Have(
						"the shifted series' partial sums tend to s − a(0)",
						"(λn:num. Σ_{k∈0 .. n} a(k + 1)) ⟶ s - a(0)",
						By(sums, RealSumsDef))
					shiftedPartialSums := b.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k∈0 .. n} a(k + 1)")
					remainder := b.TermAs[Real]("s - a(0)")
					more := b.Have(
						"plus the constant a(0), they tend to a(0) + (s − a(0)) = s",
						"(λn:num. a(0) + Σ_{k∈0 .. n} a(k + 1)) ⟶ s",
						By(
							toRemainder,
							real_sequences.LimitAdd.At(constantFirst, shiftedPartialSums, first, remainder),
							real_sequences.LimitConst.At(first),
							real_ring.SubAddLeft.At(s, first)))
					fromNext := b.Have(
						"and these are a's partial sums to n + 1",
						"(λn:num. Σ_{k∈0 .. n + 1} a(k)) ⟶ s",
						By(more, peel))
					b.Show(
						"so a's partial sums tend to s",
						By(fromNext, real_sequences.LimitShift.At(partialSums, s), RealSumsDef))
				})
		}),
})}

// SumsOffset — dropping a series' first m + 1 terms drops them from the
// sum; m + 1, because the partial sum runs over the closed interval
// 0 .. m, so that m = 0 is SumsShift. By induction on m: at 0 it is
// SumsShift, and each further step
// shifts once more — the tail past m + 1 is the tail past m with its first
// term a(m + 1) dropped, and the partial sum to m + 1 is the one to m plus
// that same term.
var SumsOffset = sumsOffsetThm{family.Add(registry.ProofEntry{
	Name: "SumsOffset",
	Key:  "prop_6a9bc9659d409e48",
	Build: family.Theorem("∀a:(num → real). ∀s:real. ∀m:num. "+
		"    real_sums(a, s) ⇔ real_sums(λn:num. a(n + m + 1), s - Σ_{k∈0 .. m} a(k))",
		func(arg *Argument, a *Arrow[Nat, Real], s *Expr[Real], m *Expr[Nat]) {
			arg.Induct(m)
			arg.Base(
				"at m = 0: n + 0 + 1 is n + 1 and the partial sum to 0 is a(0), so this is dropping the first term",
				Simp(Fwd(nat_arith.AddZero), Fwd(real_sum.IntervalPoint)),
				Cite(SumsShift))
			arg.Step(
				"m ↦ m + 1: shift once more — the tail past m + 1 is "+
					"the tail past m with its first term a(m + 1) dropped",
				func(b *Argument, ih Fact) {
					remainder := b.Have(
						"the partial sum to m + 1 takes a(m + 1) more off s",
						"s - Σ_{k∈0 .. m + 1} a(k) = s - Σ_{k∈0 .. m} a(k) - a(m + 1)",
						ByArith(real_sum.PeelRight.At(b.TermAs[Nat]("m + 1"), b.TermAs[Nat]("0"), a)))
					reindex := b.Have(
						"the tail past m + 1 is the tail past m read one index on",
						"(λn:num. a(n + (m + 1) + 1)) = (λn:num. a(n + 1 + m + 1))",
						Funext(),
						Derive(func(d *Argument) {
							d.FixAs[Nat]()
							index := d.Have(
								"at each n the two indices agree",
								"n + (m + 1) + 1 = n + 1 + m + 1",
								ByArith())
							d.Show(
								"and so do the terms",
								By(index))
						}))
					tail := b.TermAs[Fun[Nat, Real]]("λn:num. a(n + m + 1)")
					rest := b.TermAs[Real]("s - Σ_{k∈0 .. m} a(k)")
					once := b.Have(
						"SumsShift at the tail past m, whose first term is a(m + 1): it "+
							"drops that term from the sum, taking the partial sum to m + 1 off s",
						"real_sums(λn:num. a(n + m + 1), s - Σ_{k∈0 .. m} a(k)) ⇔ "+
							"real_sums(λn:num. a(n + (m + 1) + 1), s - Σ_{k∈0 .. m + 1} a(k))",
						reindex.Rw(),
						By(remainder, SumsShift.At(tail, rest), nat_arith.AddLeftZeroClause.At(m)))
					b.Show(
						"the hypothesis, then one more shift, suc(m) being m + 1",
						By(ih, once, nat_arith.Add1.At(m)))
				})
		}),
})}

// SumsPair — summing a series two terms at a time keeps its sum. The
// paired series' partial sum to n takes in a's terms up to the odd bound
// 2n + 1: split into its even and odd terms, it merges into a's partial
// sum to 2n + 1. So the paired series' partial sums are a's partial sums
// at the strictly rising indices 2n + 1, a subsequence of a sequence
// tending to s.
var SumsPair = sumsPairThm{family.Add(registry.ProofEntry{
	Name: "SumsPair",
	Key:  "prop_adb56560634b70e7",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀s:real.",
		Hypotheses: []string{
			"real_sums(a, s)",
		},
		Conclusion: "real_sums(λn:num. a(2 * n) + a(2 * n + 1), s)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], s *Expr[Real], sums Fact) {
			toS := arg.Have(
				"a's partial sums tend to s",
				"(λn:num. Σ_{k∈0 .. n} a(k)) ⟶ s",
				By(sums, RealSumsDef))
			rises := arg.Have(
				"the odd bounds 2n + 1 rise strictly",
				"∀k:num. 2 * k + 1 < 2 * (k + 1) + 1",
				ByArith())
			odd := arg.Have(
				"so a's partial sums at the odd bounds, a subsequence of them, tend to s too",
				"(λn:num. Σ_{k∈0 .. n} a(k)) ∘ (λn:num. 2 * n + 1) ⟶ s",
				By(rises, toS, real_sequences.LimitSubsequence))

			zero := arg.TermAs[Nat]("0")
			evens := arg.TermAs[Fun[Nat, Real]]("λk:num. a(2 * k)")
			odds := arg.TermAs[Fun[Nat, Real]]("λk:num. a(2 * k + 1)")
			paired := arg.Have(
				"and they are the paired series' partial sums: the "+
					"pairs up to n are a's even and odd terms up to 2n + 1",
				"(λn:num. Σ_{k∈0 .. n} (a(2 * k) + a(2 * k + 1))) = "+
					"(λn:num. Σ_{k∈0 .. n} a(k)) ∘ (λn:num. 2 * n + 1)",
				Simp(Fwd(functions.ComposeApply.Inst(
					TypeBinder.BindA[Nat](), TypeBinder.BindB[Nat](), TypeBinder.BindC[Real]()))),
				Funext(),
				arg.ForEach(func(n *Expr[Nat]) Action {
					return By(real_sum.IntervalAdd.At(zero, n, evens, odds), real_sum.IntervalEvenOdd.At(n, a))
				}))
			arg.Show(
				"so the paired series' partial sums tend to s: it sums to s",
				Simp(Fwd(RealSumsDef)),
				paired.Rw(),
				By(odd))
		}),
})}

// AlternatingBound — an alternating series whose terms are nonnegative
// and do not increase, summing to s, has s between 0 and its first term.
// Such a sum is at least 0: taken two terms at a time it
// adds up the differences between an even-indexed term and the next,
// each nonnegative, so its sum is at least the first of them. Dropping
// the first term and changing sign leaves another such series, the
// alternating series of the tail a(n + 1), summing to a(0) − s; so
// s ≤ a(0) as well.
var AlternatingBound = alternatingBoundThm{family.Add(registry.ProofEntry{
	Name: "AlternatingBound",
	Key:  "prop_230358c0227ab610",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀s:real.",
		Hypotheses: []string{
			"∀n:num. &0 ≤ a(n) ∧ a(n + 1) ≤ a(n)",
			"real_sums(λn:num. real_pow(-&1, n) * a(n), s)",
		},
		Conclusion: "&0 ≤ s ∧ s ≤ a(0)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], s *Expr[Real], hyps Fact) {
			parts := arg.Conjuncts(
				hyps,
				"the terms are nonnegative and do not increase",
				"the alternating series sums to s")
			decreasing, sums := parts[0], parts[1]

			minusOne, two := arg.TermAs[Real]("-&1"), arg.TermAs[Nat]("2")
			square := arg.Have(
				"(−1)² = 1",
				"real_pow(-&1, 2) = &1",
				ByArith())
			even := arg.Have(
				"so (−1)²ⁿ = ((−1)²)ⁿ = 1ⁿ = 1",
				"∀n:num. real_pow(-&1, 2 * n) = &1",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return By(square, real_pow.PowPow.At(minusOne, two, n), real_pow.OnePow.At(n))
				}))
			odd := arg.Have(
				"and (−1)²ⁿ⁺¹ = −1·(−1)²ⁿ = −1",
				"∀n:num. real_pow(-&1, 2 * n + 1) = -&1",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					d.Show(
						"one more factor −1 on the even power",
						ByArith(even.At(n), real_pow.PowAddOne.At(minusOne, d.TermAs[Nat]("2 * n"))))
				}))

			nonnegative := arg.Have(
				"an alternating series whose terms are nonnegative and do not increase has a nonnegative sum",
				Statement{
					Binders: "∀b:(num → real). ∀t:real.",
					Hypotheses: []string{
						"∀n:num. &0 ≤ b(n) ∧ b(n + 1) ≤ b(n)",
						"real_sums(λn:num. real_pow(-&1, n) * b(n), t)",
					},
					Conclusion: "&0 ≤ t",
				},
				Derive(func(d *Argument) {
					d.FixAs[Fun[Nat, Real]]()
					t := d.FixAs[Real]()
					bParts := d.Conjuncts(
						d.Assume(),
						"b's terms are nonnegative and do not increase",
						"its alternating series sums to t")
					bDecreasing, bSums := bParts[0], bParts[1]
					inPairs := d.Have(
						"summed two terms at a time, the series still sums to t",
						"real_sums(λn:num. real_pow(-&1, 2 * n) * b(2 * n) + real_pow(-&1, 2 * n + 1) * b(2 * n + 1), t)",
						By(bSums, SumsPair.At(d.TermAs[Fun[Nat, Real]]("λn:num. real_pow(-&1, n) * b(n)"), t)))
					pairsNonnegative := d.Have(
						"with the signs 1 and −1 each pair is b(2n) − b(2n + 1), nonnegative as b does not increase",
						"∀n:num. &0 ≤ real_pow(-&1, 2 * n) * b(2 * n) + real_pow(-&1, 2 * n + 1) * b(2 * n + 1)",
						Derive(func(e *Argument) {
							n := e.FixAs[Nat]()
							e.Show(
								"b does not increase from 2n to 2n + 1",
								ByArith(Normalized, even.At(n), odd.At(n), bDecreasing.At(e.TermAs[Nat]("2 * n"))))
						}))
					firstPair := d.BigOpAs[Nat, Real](
						"Σ_{k∈0 .. 0} (real_pow(-&1, 2 * k) * b(2 * k) + real_pow(-&1, 2 * k + 1) * b(2 * k + 1))")
					zero := d.TermAs[Nat]("0")
					firstBelow := d.Have(
						"a series of nonnegative terms sums to at least its first partial sum",
						"Σ_{k∈0 .. 0} (real_pow(-&1, 2 * k) * b(2 * k) + real_pow(-&1, 2 * k + 1) * b(2 * k + 1)) ≤ t",
						By(pairsNonnegative, inPairs, SumsPartialLessEq.At(firstPair.Summand(), t, zero)))
					d.Show(
						"and that partial sum is the first pair, at least 0",
						ByArith(
							firstBelow,
							pairsNonnegative.At(zero),
							real_sum.IntervalPoint.At(zero, firstPair.Summand())))
				}))

			alternating := arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(-&1, n) * a(n)")
			tail := arg.Have(
				"dropping the first term and changing sign leaves the "+
					"alternating series of the tail a(n + 1), summing to a(0) − s",
				"real_sums(λn:num. real_pow(-&1, n) * a(n + 1), a(0) - s)",
				Derive(func(d *Argument) {
					shifted := d.Have(
						"without its first term the series sums to s − (−1)⁰·a(0)",
						"real_sums(λn:num. real_pow(-&1, n + 1) * a(n + 1), s - real_pow(-&1, 0) * a(0))",
						By(sums, SumsShift.At(alternating, s)))
					negated := d.Have(
						"and its negative to −1·(s − (−1)⁰·a(0))",
						"real_sums(λn:num. -&1 * (real_pow(-&1, n + 1) * a(n + 1)), -&1 * (s - real_pow(-&1, 0) * a(0)))",
						By(
							shifted,
							SumsScale.At(d.TermAs[Fun[Nat, Real]]("λn:num. real_pow(-&1, n + 1) * a(n + 1)"),
								d.TermAs[Real]("s - real_pow(-&1, 0) * a(0)"), minusOne)))
					termwise := d.Have(
						"whose terms −1·(−1)ⁿ⁺¹·a(n + 1) are (−1)ⁿ·a(n + 1)",
						"(λn:num. -&1 * (real_pow(-&1, n + 1) * a(n + 1))) = (λn:num. real_pow(-&1, n) * a(n + 1))",
						Funext(),
						d.ForEach(func(*Expr[Nat]) Action { return Chain(Simp(Fwd(real_pow.PowAddOne)), ByArith()) }))
					value := d.Have(
						"and whose sum is a(0) − s, as (−1)⁰ = 1",
						"-&1 * (s - real_pow(-&1, 0) * a(0)) = a(0) - s",
						ByArith(real_pow.PowExpZeroClause.At(minusOne)))
					d.Show(
						"so the tail's alternating series sums to a(0) − s",
						termwise.RwRev(),
						By(negated, value))
				}))
			tailDecreasing := arg.Have(
				"the tail a(n + 1) is again nonnegative and non-increasing",
				"∀n:num. &0 ≤ a(n + 1) ∧ a(n + 1 + 1) ≤ a(n + 1)",
				Derive(func(d *Argument) {
					d.FixAs[Nat]()
					d.Show(
						"a's own terms from n + 1 on",
						By(decreasing.At(d.TermAs[Nat]("n + 1"))))
				}))

			lower := arg.Have(
				"the lower bound at a: 0 ≤ s",
				"&0 ≤ s",
				By(nonnegative.At(a, s), hyps))
			upper := arg.Have(
				"the lower bound at the tail: 0 ≤ a(0) − s",
				"&0 ≤ a(0) - s",
				By(
					nonnegative.At(arg.TermAs[Fun[Nat, Real]]("λn:num. a(n + 1)"), arg.TermAs[Real]("a(0) - s")),
					tailDecreasing,
					tail))
			arg.Show(
				"so s lies between 0 and a(0)",
				ByArith(lower, upper))
		}),
})}
