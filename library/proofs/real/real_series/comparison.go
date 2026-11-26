// comparison.go — comparing a series with another term by term: the
// comparison test, the bound on the sum, and the ratio test.

package real_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

// Comparison — the comparison test, carried by both directions of the
// Cauchy criterion. Since b has a sum, past some M its tails are below
// ε in size. A tail of a starting past N + M runs over indices past N,
// where |a(k)| is at most b(k), so in size it is at most the same tail
// of b, which is at most its own size and so below ε. The tails of a
// thus become uniformly small, and a has a sum.
var Comparison = comparisonThm{family.Add(registry.ProofEntry{
	Name: "Comparison",
	Key:  "prop_191d0a415705b81f",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀t:real. ∀N:num.",
		Hypotheses: []string{
			"∀n:num. N ≤ n ⇒ |a(n)| ≤ b(n)",
			"real_sums(b, t)",
		},
		Conclusion: "∃s:real. real_sums(a, s)",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], t *Expr[Real], N *Expr[Nat], hyps Fact) {
			parts := arg.Conjuncts(
				hyps,
				"past N each |a(n)| is at most b(n)",
				"b sums to t")
			bounded, sums := parts[0], parts[1]
			bTails := arg.Have(
				"b has a sum, so its tails become uniformly small",
				"∀ε:real. &0 < ε ⇒ ∃M:num. ∀m n:num. M ≤ m ⇒ |Σ_{k∈m .. n} b(k)| < ε",
				Simp(Rev(SumsCauchy)),
				By(Normalized, sums))
			aTails := arg.Have(
				"so do a's: past N + M a tail of a is at most the same tail of b",
				"∀ε:real. &0 < ε ⇒ ∃M:num. ∀m n:num. M ≤ m ⇒ |Σ_{k∈m .. n} a(k)| < ε",
				Derive(func(d *Argument) {
					ε := d.FixAs[Real]()
					pos := d.Assume()
					_, small := d.ObtainAs[Nat](
						"past some M every tail of b is below ε",
						"∃M:num. ∀m n:num. M ≤ m ⇒ |Σ_{k∈m .. n} b(k)| < ε",
						By(bTails.At(ε), pos))
					d.Take(d.TermAs[Nat]("N + M"))
					m := d.FixAs[Nat]()
					n := d.FixAs[Nat]()
					past := d.Assume()
					termwise := d.Have(
						"every k from m to n is past m, hence past N, so |a(k)| is at most b(k)",
						"∀k:num. m ≤ k ∧ k ≤ n ⇒ |a(k)| ≤ b(k)",
						d.ForEach(func(k *Expr[Nat]) Action {
							return ByArith(bounded.At(k), past)
						}))
					bTail := d.TermAs[Real]("Σ_{k∈m .. n} b(k)")
					d.Show(
						"so the tail of a is at most the same tail of b, at "+
							"most its size, which is below ε as it starts past M",
						ByArith(
							termwise,
							real_sum.IntervalDominated.At(m, n, a, b),
							real_sgn_abs.AbsDominates.At(bTail),
							past,
							small.At(m, n)))
				}))
			arg.Show(
				"a series whose tails become uniformly small has a sum, by the Cauchy criterion",
				By(aTails, SumsCauchy))
		}),
})}

// ComparisonBound — a series dominated termwise in size sums to no more
// in size: every term of a lies between −b(n) and b(n), so its sum lies
// between the sums of −b and of b, which are −t and t.
var ComparisonBound = comparisonBoundThm{family.Add(registry.ProofEntry{
	Name: "ComparisonBound",
	Key:  "prop_5ac38138f1e9ec55",
	Build: family.Theorem(Statement{
		Binders: "∀a b:(num → real). ∀s t:real.",
		Hypotheses: []string{
			"∀n:num. |a(n)| ≤ b(n)",
			"real_sums(a, s)",
			"real_sums(b, t)",
		},
		Conclusion: "|s| ≤ t",
	},
		func(arg *Argument, a, b *Arrow[Nat, Real], s, t *Expr[Real], hyps Fact) {
			parts := arg.Conjuncts(
				hyps,
				"b dominates a in size",
				"a sums to s",
				"b sums to t")
			dominated, toS, toT := parts[0], parts[1], parts[2]
			above := arg.Have(
				"every term of a is at most b's, the upper side of the two-sided reading of |a(n)| ≤ b(n)",
				"∀n:num. a(n) ≤ b(n)",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return By(dominated.At(n), real_sgn_abs.AbsBounds.At(a.Apply(n), b.Apply(n)))
				}))
			below := arg.Have(
				"and at least the negative of b's, the lower side",
				"∀n:num. -b(n) ≤ a(n)",
				arg.ForEach(func(n *Expr[Nat]) Action {
					return By(dominated.At(n), real_sgn_abs.AbsBounds.At(a.Apply(n), b.Apply(n)))
				}))
			negated := arg.Have(
				"−b is b scaled by −1, so it sums to −1 times t",
				"real_sums(λn:num. -b(n), -t)",
				Simp(Rev(real_ring.NegMinusOne)),
				By(toT, SumsScale))
			upper := arg.Have(
				"a is nowhere above b, so s is at most t",
				"s ≤ t",
				By(above, toS, toT, SumsLessEq))
			lower := arg.Have(
				"−b is nowhere above a, so −t is at most s",
				"-t ≤ s",
				By(below, negated, toS, SumsLessEq))
			arg.Show(
				"s lies between −t and t, which is |s| ≤ t",
				By(upper, lower, real_sgn_abs.AbsBounds.At(s, t)))
		}),
})}

// Ratio — the ratio test. Raising the ratio c to r = max(c, 1/2)
// keeps the hypothesis and puts r strictly between 0 and 1. Past N the
// terms then decay at least geometrically, |a(N + k)| ≤ |a(N)|·rᵏ, by
// induction on k; writing n ≥ N as N + d, the decay at d bounds |a(n)|
// by K·rⁿ with K = |a(N)|/rᴺ. That is K times the geometric series of
// r, which sums to K·(1 − r)⁻¹, and a has a sum by comparison.
var Ratio = ratioThm{family.Add(registry.ProofEntry{
	Name: "Ratio",
	Key:  "prop_a2465b0bf876b43c",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀c:real. ∀N:num.",
		Hypotheses: []string{
			"c < &1",
			"∀n:num. N ≤ n ⇒ |a(n + 1)| ≤ c * |a(n)|",
		},
		Conclusion: "∃s:real. real_sums(a, s)",
	},
		func(arg *Argument, a *Arrow[Nat, Real], c *Expr[Real], N *Expr[Nat], hyps Fact) {
			given := arg.Conjuncts(
				hyps,
				"c is below 1",
				"past N each term is at most c times the one before in size")
			below, ratioC := given[0], given[1]

			r, reduced := arg.ObtainAs[Real](
				"the ratio may be taken strictly between 0 and 1: max(c, 1/2) is one",
				"∃r:real. &0 < r ∧ r < &1 ∧ ∀n:num. N ≤ n ⇒ |a(n + 1)| ≤ r * |a(n)|",
				Derive(func(d *Argument) {
					half := d.TermAs[Real]("&1 / &2")
					raised := d.TermAs[Real]("max(c, &1 / &2)")
					d.Take(raised)
					above := real_sup_inf.MaxUpperBound.At(c, half)
					bounds := d.Have(
						"max(c, 1/2) is at least 1/2, and it is c or 1/2, both below 1",
						"&0 < max(c, &1 / &2) ∧ max(c, &1 / &2) < &1",
						ByArith(below, above, real_sup_inf.MaxIsArgument.At(c, half)))
					holds := d.Have(
						"the hypothesis holds at the larger ratio, since |a(n)| ≥ 0",
						"∀n:num. N ≤ n ⇒ |a(n + 1)| ≤ max(c, &1 / &2) * |a(n)|",
						Derive(func(e *Argument) {
							n := e.FixAs[Nat]()
							past := e.Assume()
							size := e.TermAs[Real]("|a(n)|")
							e.Show(
								"c·|a(n)| is at most max(c, 1/2)·|a(n)|",
								ByArith(
									ratioC.At(n),
									past,
									above,
									real_sgn_abs.AbsNonneg.At(a.Apply(n)),
									real_order_ring.LessEqMulRight.At(c, raised, size)))
						}))
					d.Show(
						"so max(c, 1/2) is such a ratio",
						By(bounds, holds))
				}))
			reducedParts := arg.Conjuncts(
				reduced,
				"r is positive",
				"r is below 1",
				"past N each term is at most r times the one before in size")
			positive, belowOne, ratioR := reducedParts[0], reducedParts[1], reducedParts[2]

			decay := arg.Have(
				"past N the terms shrink at least geometrically, by induction on k",
				"∀k:num. |a(N + k)| ≤ |a(N)| * real_pow(r, k)",
				Derive(func(d *Argument) {
					d.Induct("k")
					d.Base(
						"at k = 0 both sides are |a(N)|, as r⁰ = 1",
						ByArith(real_pow.PowExpZeroClause.At(r)))
					d.Step(
						"each step past N + k multiplies the bound by r",
						func(b *Argument, ih Fact) {
							k := b.TermAs[Nat]("k")
							next := b.Have(
								"the ratio at N + k, its index N + k + 1 spelled N + suc k",
								"|a(N + suc(k))| ≤ r * |a(N + k)|",
								Simp(Fwd(nat_arith.AddSuc), Fwd(nat_arith.Add1)),
								By(ratioR.At(b.TermAs[Nat]("N + k")), nat_order.LessEqAdd.At(N, k)))
							scaled := b.Have(
								"the bound on |a(N + k)|, scaled by the positive r",
								"r * |a(N + k)| ≤ r * (|a(N)| * real_pow(r, k))",
								ByArith(ih, positive))
							b.Show(
								"the two chained, with r·rᵏ = rᵏ⁺¹",
								Simp(Fwd(real_pow.PowExpSucClause)),
								ByArith(next, scaled))
						})
				}))

			dominated := arg.Have(
				"so past N each |a(n)| is at most K·rⁿ, with K = |a(N)|/rᴺ",
				"∀n:num. N ≤ n ⇒ |a(n)| ≤ |a(N)| / real_pow(r, N) * real_pow(r, n)",
				Derive(func(e *Argument) {
					n := e.FixAs[Nat]()
					past := e.Assume()
					offset, offsetEq := e.ObtainAs[Nat](
						"n is N plus an offset d",
						"∃d:num. n = N + d",
						By(past, nat_order.LessEqExists.At(n, N)))
					e.Show(
						"K·rᴺ⁺ᵈ is |a(N)|·rᵈ, the positive rᴺ cancelling, and that bounds |a(N + d)|",
						offsetEq.Rw(),
						Simp(Fwd(real_pow.PowAdd)),
						ByArith(decay.At(offset), positive, real_pow.PowPos.At(r, N)))
				}))

			small := arg.Have(
				"0 < r < 1 puts r below 1 in size",
				"|r| < &1",
				ByArith(positive, belowOne))
			geometric := arg.Have(
				"K times the geometric series of r sums to K·(1 − r)⁻¹",
				"real_sums(λn:num. |a(N)| / real_pow(r, N) * real_pow(r, n), "+
					"    |a(N)| / real_pow(r, N) * real_inv(&1 - r))",
				By(small, Geometric.At(r), SumsScale))
			arg.Show(
				"a is dominated past N by a series with a sum, so it has a sum by comparison",
				By(dominated, geometric, Comparison))
		}),
})}
