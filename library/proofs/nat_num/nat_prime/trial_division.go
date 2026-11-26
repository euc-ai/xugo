// trial_division.go — certifying a given number prime: by trial division, a
// number with no prime divisor up to its square root is prime, and a number
// coprime to m!, with m + 1 past its square root, has none. A Bezout relation
// with m! is then a certificate of primality checked by one multiplication.

package nat_prime

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PrimeByTrialDivision — a number n ≥ 2 that no prime d with d² ≤ n divides is
// prime. A divisor e > 1 of n has a prime factor q ≤ e, which divides n, so
// the trial forbids q² ≤ n, and e² ≥ q² > n. Write a divisor d of n as
// n = d·y: unless d is 1 or n, both d and y exceed 1, so n is below both d²
// and y², while it is at least the smaller of the two.
var PrimeByTrialDivision = primeByTrialDivisionThm{family.Add(registry.ProofEntry{
	Name: "PrimeByTrialDivision",
	Key:  "prop_f0186883ce4eaa0d",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"2 ≤ n",
			"∀d:num. nat_prime(d) ∧ d * d ≤ n ⇒ ¬(d ∣ n)",
		},
		Conclusion: "nat_prime(n)",
	},
		func(a *Argument, n *Expr[Nat], large, trial Fact) {
			noSmall := a.Have(
				"a divisor e > 1 of n has e² > n: a prime factor q of e divides n and q² ≤ e²",
				"∀e:num. e ∣ n ∧ 1 < e ⇒ n < e * e",
				Derive(func(b *Argument) {
					e := b.FixAs[Nat]("e")
					divisor := b.Assume()
					q, factor := b.ObtainAs[Nat](
						"e has a prime factor q",
						"∃q:num. nat_prime(q) ∧ q ∣ e",
						By(divisor, PrimeFactor.At(e)))
					b.Show(
						"q divides n and q ≤ e, so the trial rules out q² ≤ n, and n < q² ≤ e²",
						ByArith(
							trial.At(q),
							factor,
							divisor,
							nat_divides.DividesTrans.At(q, e, n),
							nat_divides.DividesLessEq.At(q, e),
							nat_order.LessEqMul2.At(q, e, q, e)))
				}))
			divisors := a.Have(
				"a divisor of n is 1 or n",
				"∀d:num. d ∣ n ⇒ d = 1 ∨ d = n",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]("d")
					divides := b.Assume()
					y, cofactor := b.ObtainAs[Nat](
						"n = d·y",
						"∃y:num. n = d * y",
						By(divides, nat_divides.DividesFactor.At(d, n)))
					proper := b.Unless(
						b.TermAs[Bool]("y = 1"),
						"y = 1: then d is n",
						Given(func(c *Argument, unit Fact) {
							c.Do(ByArith(unit, cofactor))
						}))
					b.Show(
						"otherwise d and y both exceed 1, so n < d² and n < y², yet n = d·y is at least the smaller square",
						ByArith(
							proper,
							large,
							cofactor,
							divides,
							noSmall.At(d),
							noSmall.At(y),
							nat_divides.DividesOwnMultiple.At(y, d),
							nat_order.LessEqMulMono.At(d, d, y),
							nat_order.LessEqMulMono.At(y, y, d),
							nat_arith.MulEqZero.At(d, y)))
				}))
			notOne := a.Have(
				"n is not 1",
				"n ≠ 1",
				ByArith(large))
			a.Show(
				"a number other than 1 whose only divisors are 1 and itself is prime",
				By(divisors, notOne, OneOrPrime.At(n)))
		}),
})}

// CoprimeToFactorialPrime — a number p ≥ 2 below (m + 1)² that is coprime to
// m!, as a Bezout relation p·x = m!·y + 1 shows, is prime. A prime d with
// d² ≤ p is at most m, since (m + 1)² exceeds p, so d divides m!; were it to
// divide p it would divide p·x − m!·y = 1. Trial division then strikes nothing.
var CoprimeToFactorialPrime = coprimeToFactorialPrimeThm{family.Add(registry.ProofEntry{
	Name: "CoprimeToFactorialPrime",
	Key:  "prop_1dd6cb95ab7fdcda",
	Build: family.Theorem(Statement{
		Binders: "∀p m x y:num.",
		Hypotheses: []string{
			"2 ≤ p",
			"p < (m + 1) * (m + 1)",
			"p * x = factorial(m) * y + 1",
		},
		Conclusion: "nat_prime(p)",
	},
		func(a *Argument, p, m, x, y *Expr[Nat], large, below, bezout Fact) {
			next := a.TermAs[Nat]("m + 1")
			trial := a.Have(
				"no prime d with d² ≤ p divides p",
				"∀d:num. nat_prime(d) ∧ d * d ≤ p ⇒ ¬(d ∣ p)",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]("d")
					candidate := b.Assume()
					small := b.Have(
						"d is at most m: from m + 1 ≤ d would follow (m + 1)² ≤ d² ≤ p",
						"d ≤ m",
						ByArith(below, candidate, nat_order.LessEqMul2.At(next, d, next, d)))
					b.Show(
						"d divides m!·y, so dividing p·x = m!·y + 1 it would divide 1, yet d ≥ 2",
						ByArith(
							candidate,
							small,
							bezout,
							PrimeAtLeastTwo.At(d),
							nat_divides.DividesFactorial.At(d, m),
							nat_divides.DividesMul.At(d, p, x),
							nat_divides.DividesMul.At(d, b.TermAs[Nat]("factorial(m)"), y),
							nat_divides.DividesAddCancel.At(d, b.TermAs[Nat]("factorial(m) * y"), b.TermAs[Nat]("1")),
							nat_divides.DividesOne.At(d)))
				}))
			a.Show(
				"a number from 2 on that no prime up to its square root divides is prime",
				By(large, trial, PrimeByTrialDivision.At(p)))
		}),
})}
