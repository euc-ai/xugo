// term_bounds.go — coefficient estimates for finite polynomial tails.

package complex_polynomial

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialLowerTermsBound — outside the unit disk, the modulus of the sum
// of the terms of index below d is at most the sum of their coefficient
// moduli times |z|^(d−1): each term is at most its coefficient modulus times
// that power, and the power factors out of the sum.
var PolynomialLowerTermsBound = polynomialLowerTermsBoundThm{family.Add(registry.ProofEntry{
	Name: "PolynomialLowerTermsBound",
	Key:  "prop_f4c589b86b5d1f85",
	Build: family.Theorem(Statement{
		Binders:    "∀d:num. ∀p:(num → complex). ∀z:complex.",
		Hypotheses: []string{"&1 ≤ |z|"},
		Conclusion: "|module_sum(complex_add, &0, «indices», «term»)| ≤ " +
			"sum(«indices», λi:num. |p(i)|) * |z| ^ (d - 1)",
		Abbrev: Abbrev{
			{Name: "indices", Text: "{i:num | i < d}"},
			{Name: "term", Text: "λi:num. p(i) * z ^ i"},
		},
	}, func(a *Argument, d *Expr[Nat], p *Arrow[Nat, Complex], z *Expr[Complex], outside Fact) {
		radius := a.TermAs[Real]("|z|")
		power := a.TermAs[Real]("|z| ^ (d - 1)")
		indices := a.TermAs[Set[Nat]]("«indices»")
		terms := a.TermAs[Fun[Nat, Complex]]("«term»")
		coefficients := a.TermAs[Fun[Nat, Real]]("λi:num. |p(i)|")
		bounds := a.TermAs[Fun[Nat, Real]]("λi:num. |p(i)| * |z| ^ (d - 1)")
		pointwise := a.Have(
			"each lower power is dominated by the highest possible lower power",
			"∀i:num. i < d ⇒ |«term»(i)| ≤ |p(i)| * |z| ^ (d - 1)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				below := b.Assume()
				powerBound := b.Have(
					"powers increase with their exponents outside the unit disk",
					"|z| ^ i ≤ |z| ^ (d - 1)",
					ByArith(below, outside, real_pow.PowMonoExp.At(radius, i, b.TermAs[Nat]("d - 1"))))
				b.Show(
					"modulus multiplicativity transfers the power bound to the summand",
					ByArith(
						powerBound,
						complex_abs.AbsNonneg.At(p.Apply(i)),
						complex_abs.AbsMul.At(p.Apply(i), b.TermAs[Complex]("z ^ i")),
						complex_abs.AbsPow.At(z, i)))
			}))
		dominated := a.Have(
			"the pointwise bounds price the finite complex sum",
			"|module_sum(complex_add, &0, «indices», «term»)| ≤ sum(«indices», λi:num. |p(i)| * |z| ^ (d - 1))",
			By(
				pointwise,
				num_segment.FiniteBelowStrict.At(d),
				complex_abs.AbsSumDominated.At(indices, terms, bounds)))
		a.Show(
			"factor out the common power from the sum of coefficient moduli",
			ByArith(dominated, real_sum.ScalarRight.At(power, coefficients, indices)))
	}),
})}

// PolynomialHigherTermsBound — inside the unit disk, the modulus of the sum
// of the terms of index above k, up to n, is at most the sum of their
// coefficient moduli times |z|^(k+1): each term is at most its coefficient
// modulus times that power, and the power factors out of the sum.
var PolynomialHigherTermsBound = polynomialHigherTermsBoundThm{family.Add(registry.ProofEntry{
	Name: "PolynomialHigherTermsBound",
	Key:  "prop_ebaf411c2a055bc",
	Build: family.Theorem(Statement{
		Binders:    "∀p:(num → complex). ∀k n:num. ∀z:complex.",
		Hypotheses: []string{"|z| ≤ &1"},
		Conclusion: "|module_sum(complex_add, &0, «indices», «term»)| ≤ " +
			"sum(«indices», λi:num. |p(i)|) * |z| ^ (k + 1)",
		Abbrev: Abbrev{
			{Name: "indices", Text: "{i:num | k < i ∧ i ≤ n}"},
			{Name: "term", Text: "λi:num. p(i) * z ^ i"},
		},
	}, func(a *Argument, p *Arrow[Nat, Complex], k, n *Expr[Nat], z *Expr[Complex], inside Fact) {
		radius := a.TermAs[Real]("|z|")
		power := a.TermAs[Real]("|z| ^ (k + 1)")
		indices := a.TermAs[Set[Nat]]("«indices»")
		terms := a.TermAs[Fun[Nat, Complex]]("«term»")
		coefficients := a.TermAs[Fun[Nat, Real]]("λi:num. |p(i)|")
		bounds := a.TermAs[Fun[Nat, Real]]("λi:num. |p(i)| * |z| ^ (k + 1)")
		pointwise := a.Have(
			"each higher power is dominated by the first possible higher power",
			"∀i:num. k < i ∧ i ≤ n ⇒ |«term»(i)| ≤ |p(i)| * |z| ^ (k + 1)",
			Derive(func(b *Argument) {
				i := b.FixAs[Nat]("i")
				inTail := b.Assume()
				powerBound := b.Have(
					"powers are nonincreasing in their exponents inside the unit disk",
					"|z| ^ i ≤ |z| ^ (k + 1)",
					ByArith(
						inTail,
						inside,
						complex_abs.AbsNonneg.At(z),
						real_pow.PowMonoExpBelowOne.At(radius, b.TermAs[Nat]("k + 1"), i)))
				b.Show(
					"modulus multiplicativity transfers the power bound to the summand",
					ByArith(
						powerBound,
						complex_abs.AbsNonneg.At(p.Apply(i)),
						complex_abs.AbsMul.At(p.Apply(i), b.TermAs[Complex]("z ^ i")),
						complex_abs.AbsPow.At(z, i)))
			}))
		finite := a.Have(
			"the tail is a restriction of a finite initial segment",
			"finite(«indices»)",
			By(
				num_segment.FiniteBelow.At(n),
				finite_set.FiniteRestrict.At(
					a.TermAs[Set[Nat]]("{i:num | i ≤ n}"), a.TermAs[Set[Nat]]("λi:num. k < i"))))
		dominated := a.Have(
			"the pointwise bounds price the finite complex sum",
			"|module_sum(complex_add, &0, «indices», «term»)| ≤ sum(«indices», λi:num. |p(i)| * |z| ^ (k + 1))",
			By(pointwise, finite, complex_abs.AbsSumDominated.At(indices, terms, bounds)))
		a.Show(
			"factor out the common power from the sum of coefficient moduli",
			ByArith(dominated, real_sum.ScalarRight.At(power, coefficients, indices)))
	}),
})}
