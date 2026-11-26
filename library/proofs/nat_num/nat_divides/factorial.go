// factorial.go — the divisors of a factorial: every number from 1 to m
// divides m!.

package nat_divides

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/registry"
)

// DividesFactorial — every number from 1 to m divides m!. By induction on
// m: no number lies between 1 and 0; and a number at most m + 1 is either
// at most m, a divisor of m! and so of (m + 1)! = (m + 1) · m!, or m + 1
// itself, the other factor.
var DividesFactorial = dividesFactorialThm{family.Add(registry.ProofEntry{
	Name: "DividesFactorial",
	Key:  "prop_b8c0981f9b5b941b",
	Build: family.Theorem(Statement{
		Binders: "∀d m:num.",
		Hypotheses: []string{
			"1 ≤ d",
			"d ≤ m",
		},
		Conclusion: "d ∣ factorial(m)",
	}, func(a *Argument, d *Expr[Nat], positive Fact) {
		a.Induct("m")
		a.Base(
			"no number from 1 on is at most 0",
			ByArith(positive))
		a.Step(
			"(m + 1)! is (m + 1) · m!, and a number up to m + 1 is at most m or is m + 1",
			func(b *Argument, ih Fact) {
				factorial, successor := b.TermAs[Nat]("factorial(m)"), b.TermAs[Nat]("suc(m)")
				bound := b.Assume()
				b.Do(Simp(Fwd(nat_arith.Factorial)))
				b.Cases(b.Term("d ≤ m"))
				b.When(
					"d ≤ m: d divides m!, so the product",
					func(c *Argument, below Fact) {
						c.Show(
							"a divisor of the factor m! divides the product, turned around",
							By(
								Normalized,
								below,
								ih,
								DividesMul.At(d, factorial, successor),
								nat_arith.MulSym.At(factorial, successor)))
					})
				b.Otherwise(
					"d is m + 1, the other factor",
					func(c *Argument, above Fact) {
						top := c.Have(
							"at most m + 1 but not at most m is m + 1",
							"d = suc(m)",
							ByArith(above, bound))
						c.Show(
							"d divides itself, hence the product it is a factor of",
							By(Normalized, top, DividesRefl.At(d), DividesMul.At(d, successor, factorial)))
					})
			})
	}),
})}
