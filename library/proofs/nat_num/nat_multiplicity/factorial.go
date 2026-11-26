// factorial.go — Legendre's formula for the multiplicity of a prime in n!.

package nat_multiplicity

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// Legendre — Legendre's formula: the multiplicity of a prime p in n! is
// Σ_{i∈1 .. n} div(n, pⁱ). By induction on n. At 0, 0! = 1 has multiplicity
// 0 and the sum is empty. From n to n + 1: (n + 1)! = (n + 1)·n!, so the
// multiplicity grows by v_p(n + 1) (MultiplicityMul); each quotient
// div(n, pⁱ) grows by one exactly when pⁱ divides n + 1
// (nat_divides.DivSucIndicator), and the indicators count v_p(n + 1)
// (MultiplicityAsCount); the new term div(n, pⁿ⁺¹) is 0, as n < pⁿ⁺¹.
var Legendre = legendreThm{family.Add(registry.ProofEntry{
	Name: "Legendre",
	Key:  "prop_3cad985cfcd7081e",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "nat_multiplicity(p, factorial(n)) = Σ_{i∈1 .. n} div(n, p ^ i)",
	}, func(a *Argument, p *Expr[Nat], prime Fact) {
		base := a.Have(
			"a prime is at least 2",
			"2 ≤ p",
			By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
		n := ext.As[Nat](a.Binder("n"))
		a.Induct(n)
		a.Base(
			"0! = 1 has multiplicity 0, and the sum over 1 .. 0 is empty",
			func(b *Argument) {
				one, zero := b.TermAs[Nat]("1"), b.TermAs[Nat]("0")
				atOne := b.Have(
					"p⁰ = 1 divides 1 and p¹ = p does not, so the multiplicity of p in 1 is 0",
					"nat_multiplicity(p, 1) = 0",
					ByArith(
						base,
						MultiplicityUnique.At(p, one, zero),
						nat_arith.NatPow,
						nat_divides.DividesRefl.At(one),
						nat_arith.PowOne.At(p),
						nat_divides.DividesOne.At(p)))
				b.Show(
					"both sides are 0",
					ByArith(
						atOne,
						nat_arith.Factorial,
						nat_sum.IntervalClauses.At(one, zero, b.TermAs[Fun[Nat, Nat]]("λi:num. div(0, p ^ i)"))))
			})
		a.Step(
			"from n to n + 1 both sides grow by the multiplicity of p in n + 1",
			func(b *Argument, ih Fact) {
				one := b.TermAs[Nat]("1")
				sn := b.TermAs[Nat]("suc(n)")
				quotients := b.TermAs[Fun[Nat, Nat]]("λi:num. div(n, p ^ i)")
				product := b.Have(
					"(n + 1)! = (n + 1)·n!, and the multiplicity adds over the product",
					"nat_multiplicity(p, factorial(suc(n))) = "+
						"nat_multiplicity(p, suc(n)) + nat_multiplicity(p, factorial(n))",
					By(
						prime,
						nat_arith.Factorial,
						peano.SucNotZero.At(n),
						MultiplicityMul.At(p, sn, b.TermAs[Nat]("factorial(n)")),
						nat_arith.FactorialNonzero.At(n)))
				grows := b.Have(
					"each quotient by pⁱ grows by one exactly when pⁱ divides n + 1",
					"∀i:num. div(suc(n), p ^ i) = div(n, p ^ i) + COND(p ^ i ∣ suc(n), 1, 0)",
					Derive(func(c *Argument) {
						i := c.FixAs[Nat]("i")
						nonzero := c.Have(
							"pⁱ ≠ 0, as p ≥ 2",
							"p ^ i ≠ 0",
							ByArith(base, nat_arith.PowEqZero.At(p, i)))
						c.Show(
							"DivSucIndicator at d = pⁱ",
							By(
								Normalized,
								nonzero,
								nat_divides.DivSucIndicator.At(n, c.TermAs[Nat]("p ^ i")),
								nat_arith.Add1.At(n)))
					}))
				split := b.Have(
					"so the quotients at n + 1 sum to those of n over 1 .. n + 1, plus the count",
					"Σ_{i∈1 .. suc(n)} div(suc(n), p ^ i) = "+
						"Σ_{i∈1 .. suc(n)} div(n, p ^ i) + Σ_{i∈1 .. suc(n)} COND(p ^ i ∣ suc(n), 1, 0)",
					By(
						grows,
						nat_sum.Add.At(
							quotients,
							b.TermAs[Fun[Nat, Nat]]("λi:num. COND(p ^ i ∣ suc(n), 1, 0)"),
							b.TermAs[Set[Nat]]("1 .. suc(n)")),
						num_segment.Finite.At(one, sn)))
				vanish := b.Have(
					"the new quotient div(n, pⁿ⁺¹) is 0, as n < pⁿ⁺¹",
					"Σ_{i∈1 .. suc(n)} div(n, p ^ i) = Σ_{i∈1 .. n} div(n, p ^ i)",
					ByArith(
						base,
						nat_sum.IntervalClauses.At(one, n, quotients),
						nat_div_mod.DivEqZero.At(n, b.TermAs[Nat]("p ^ suc(n)")),
						nat_order.LessThanPowSelf.At(p, sn),
						nat_arith.PowEqZero.At(p, sn)))
				b.Show(
					"both sides grow by the multiplicity of p in n + 1, which counts the powers of p dividing it",
					ByArith(ih, product, split, vanish, base, peano.SucNotZero.At(n), MultiplicityAsCount.At(p, sn)))
			})
	}),
})}
