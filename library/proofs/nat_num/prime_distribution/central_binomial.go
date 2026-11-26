// central_binomial.go — the prime factorization of the central binomial
// coefficient C(2n, n), the product of its prime powers over the primes up to
// 2n. The multiplicity of a prime p in it is the sum of the carries
// div(2n, pⁱ) − 2·div(n, pⁱ), each 0 or 1 and 0 once pⁱ exceeds 2n, so every
// prime power dividing C(2n, n) is at most 2n, a prime whose square exceeds 2n
// divides it at most once, and from n ≥ 3 a prime in ⟬2n/3, n⟧ not at all.

package prime_distribution

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The multiplicity of p in C(2n, n) as a sum of carries
// ---------------------------------------------------------------------------

// CentralBinomialMultiplicity — the multiplicity of a prime p in C(2n, n) is
// the sum over 1 .. 2n of the carries div(2n, pⁱ) − 2·div(n, pⁱ), the carries
// out of the digits of n + n in base p. Since
// n!·n!·C(2n, n) = (2n)!, the multiplicity is v((2n)!) − 2·v(n!), which
// Legendre's formula writes as sums of quotients; the sum for n! runs as well
// to 2n, its quotients past n being 0, and the two sums then subtract
// termwise, each quotient of 2n being at least twice that of n.
var CentralBinomialMultiplicity = centralBinomialMultiplicityThm{family.Add(registry.ProofEntry{
	Name: "CentralBinomialMultiplicity",
	Key:  "prop_cb57b12696e51dd",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "nat_multiplicity(p, binomial(2 * n, n)) = Σ_{i∈1 .. 2 * n} «carry»(i)",
		Abbrev: Abbrev{
			{Name: "carry", Text: "λi:num. div(2 * n, p ^ i) - 2 * div(n, p ^ i)"},
		},
	},
		func(a *Argument, p, n *Expr[Nat], prime Fact) {
			atLeastTwo := a.Have(
				"a prime is at least 2",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
			double := a.TermAs[Nat]("2 * n")
			segment := a.TermAs[Set[Nat]]("1 .. 2 * n")
			nFactorial := a.TermAs[Nat]("factorial(n)")
			vanish := a.Have(
				"past n the quotients of n by powers of p are 0, as n < i < pⁱ",
				"∀i:num. i ∈ 1 .. 2 * n ∧ i ∉ 1 .. n ⇒ div(n, p ^ i) = 0",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"i ∈ 1 .. 2n outside 1 .. n is past n, and n < i < pⁱ",
						ByArith(
							atLeastTwo,
							nat_order.LessThanPowSelf.At(p, i),
							nat_arith.PowEqZero.At(p, i),
							nat_div_mod.DivEqZero.At(n, b.TermAs[Nat]("p ^ i"))))
				}))
			inside := a.Have(
				"1 .. n lies inside 1 .. 2n",
				"1 .. n ⊆ 1 .. 2 * n",
				ByArith(num_segment.Subset.At(a.Ctx().Nat(1), n, a.Ctx().Nat(1), double)))
			pointwise := a.Have(
				"each quotient of 2n is twice that of n plus its carry, which is never negative",
				"∀i:num. div(2 * n, p ^ i) = 2 * div(n, p ^ i) + «carry»(i)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Show(
						"2·div(n, pⁱ) ≤ div(2n, pⁱ), pⁱ being nonzero",
						ByArith(
							nat_div_mod.FloorDoubleBound.At(n, b.TermAs[Nat]("p ^ i")),
							atLeastTwo,
							nat_arith.PowEqZero.At(p, i)))
				}))
			termwise := a.Have(
				"summed over 1 .. 2n, the quotients of 2n are twice those of n plus the carries",
				"Σ_{i∈1 .. 2 * n} div(2 * n, p ^ i) = "+
					"2 * (Σ_{i∈1 .. 2 * n} div(n, p ^ i)) + Σ_{i∈1 .. 2 * n} «carry»(i)",
				By(
					pointwise,
					nat_sum.Add.At(
						a.TermAs[Fun[Nat, Nat]]("λi:num. 2 * div(n, p ^ i)"),
						a.TermAs[Fun[Nat, Nat]]("«carry»"),
						segment),
					nat_sum.ScalarLeft.At(
						a.Ctx().Nat(2),
						a.TermAs[Fun[Nat, Nat]]("λi:num. div(n, p ^ i)"),
						segment),
					num_segment.Finite.At(a.Ctx().Nat(1), double)))
			a.Show(
				"v(C(2n, n)) = v((2n)!) − 2·v(n!), and Legendre's formula counts both",
				CalcEq(
					Leg(
						a.TermAs[Nat]("nat_multiplicity(p, factorial(2 * n)) - 2 * nat_multiplicity(p, factorial(n))"),
						"(2n)! = n!·n!·C(2n, n), and the multiplicity of p adds over the factors",
						ByArith(
							prime,
							binomial.FactorialFormula.At(double, n),
							nat_multiplicity.MultiplicityMul.At(
								p,
								a.TermAs[Nat]("factorial(n) * factorial(n)"),
								a.TermAs[Nat]("binomial(2 * n, n)")),
							nat_multiplicity.MultiplicityMul.At(p, nFactorial, nFactorial),
							nat_arith.FactorialNonzero.At(n),
							nat_arith.MulEqZero.At(nFactorial, nFactorial),
							binomial.EqZero.At(double, n))),
					Leg(
						a.TermAs[Nat]("Σ_{i∈1 .. 2 * n} div(2 * n, p ^ i) - 2 * (Σ_{i∈1 .. n} div(n, p ^ i))"),
						"Legendre's formula at 2n and at n",
						ByArith(prime, nat_multiplicity.Legendre.At(p, double), nat_multiplicity.Legendre.At(p, n))),
					Leg(
						a.TermAs[Nat]("Σ_{i∈1 .. 2 * n} div(2 * n, p ^ i) - 2 * (Σ_{i∈1 .. 2 * n} div(n, p ^ i))"),
						"the sum for n! runs as well to 2n, its new terms being 0",
						By(
							vanish,
							inside,
							nat_sum.Superset.At(
								a.TermAs[Set[Nat]]("1 .. n"),
								segment,
								a.TermAs[Fun[Nat, Nat]]("λi:num. div(n, p ^ i)")))),
					FinalLeg(
						"the two sums subtract termwise",
						ByArith(termwise))))
		}),
})}

// ---------------------------------------------------------------------------
// The prime powers dividing C(2n, n)
// ---------------------------------------------------------------------------

// CentralBinomialPrimePower — every prime power dividing C(2n, n) is at most
// 2n. The multiplicity of p is the sum of the carries over 1 .. 2n, and each
// carry is at most 1 (nat_div_mod.FloorDoubleBound) and 0 once pⁱ exceeds 2n,
// both quotients then vanishing. By induction on M, the carries up to M sum
// to at most M with p to their sum at most 2n: a carry of 1 at M + 1 needs
// p^(M+1) ≤ 2n, and the sum is then at most M + 1.
var CentralBinomialPrimePower = centralBinomialPrimePowerThm{family.Add(registry.ProofEntry{
	Name: "CentralBinomialPrimePower",
	Key:  "prop_2b1a651a47b8d5e",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"1 ≤ n",
		},
		Conclusion: "p ^ nat_multiplicity(p, binomial(2 * n, n)) ≤ 2 * n",
		Abbrev: Abbrev{
			{Name: "carry", Text: "λi:num. div(2 * n, p ^ i) - 2 * div(n, p ^ i)"},
		},
	},
		func(a *Argument, p, n *Expr[Nat], prime, positive Fact) {
			atLeastTwo := a.Have(
				"a prime is at least 2",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
			double := a.TermAs[Nat]("2 * n")
			carry := a.TermAs[Fun[Nat, Nat]]("«carry»")
			carries := a.Have(
				"each carry is at most 1, and 0 once pⁱ exceeds 2n",
				"∀i:num. «carry»(i) ≤ 1 ∧ (2 * n < p ^ i ⇒ «carry»(i) = 0)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					power := b.TermAs[Nat]("p ^ i")
					b.Show(
						"div(2n, pⁱ) is at most 2·div(n, pⁱ) + 1, and 0 once pⁱ exceeds 2n",
						ByArith(
							nat_div_mod.FloorDoubleBound.At(n, power),
							atLeastTwo,
							nat_arith.PowEqZero.At(p, i),
							nat_div_mod.DivEqZero.At(double, power)))
				}))
			partial := a.Have(
				"the carries up to M sum to at most M, and p to their sum is at most 2n",
				"∀M:num. Σ_{i∈1 .. M} «carry»(i) ≤ M ∧ p ^ (Σ_{i∈1 .. M} «carry»(i)) ≤ 2 * n",
				Derive(func(b *Argument) {
					m := ext.As[Nat](b.Binder("M"))
					b.Induct(m)
					b.Base(
						"the empty sum is 0, and p⁰ = 1 ≤ 2n",
						ByArith(
							positive,
							nat_sum.IntervalClauses.At(b.Ctx().Nat(1), b.Ctx().Nat(0), carry),
							nat_arith.NatPow))
					b.Step(
						"from M to M + 1 the sum takes the carry at M + 1",
						func(c *Argument, ih Fact) {
							next := c.TermAs[Nat]("suc(M)")
							sum := c.TermAs[Nat]("Σ_{i∈1 .. M} «carry»(i)")
							grown := c.TermAs[Nat]("Σ_{i∈1 .. suc(M)} «carry»(i)")
							c.Cases(c.TermAs[Bool]("2 * n < p ^ suc(M)"))
							c.When(
								"p^(M+1) exceeds 2n: the carry at M + 1 is 0, and the sum stays",
								func(d *Argument, beyond Fact) {
									d.Show(
										"both bounds carry over from M",
										ByArith(
											beyond,
											carries.At(next),
											ih,
											nat_sum.IntervalClauses.At(d.Ctx().Nat(1), m, carry),
											atLeastTwo,
											nat_order.LessEqPow.At(p, grown, sum)))
								})
							c.Otherwise(
								"p^(M+1) ≤ 2n: the carry at M + 1 is at most 1",
								func(d *Argument, within Fact) {
									d.Show(
										"the sum is at most M + 1, and p to it at most p^(M+1) ≤ 2n",
										ByArith(
											within,
											carries.At(next),
											ih,
											nat_sum.IntervalClauses.At(d.Ctx().Nat(1), m, carry),
											atLeastTwo,
											nat_order.LessEqPow.At(p, grown, next)))
								})
						})
				}))
			a.Show(
				"at M = 2n the sum of the carries is the multiplicity of p",
				ByArith(prime, partial.At(double), CentralBinomialMultiplicity.At(p, n)))
		}),
})}

// CentralBinomialFactorization — C(2n, n) is the product of its prime powers
// over the primes up to 2n: it is not 0, and a prime dividing it divides
// (2n)! = n!·n!·C(2n, n), so it is at most 2n.
var CentralBinomialFactorization = centralBinomialFactorizationThm{family.Add(registry.ProofEntry{
	Name: "CentralBinomialFactorization",
	Key:  "prop_16df3323554d0a85",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Conclusion: "binomial(2 * n, n) = " +
			"Π_{p∈«primes»(2 * n)} p ^ nat_multiplicity(p, binomial(2 * n, n))",
	},
		func(a *Argument, n *Expr[Nat]) {
			double := a.TermAs[Nat]("2 * n")
			central := a.TermAs[Nat]("binomial(2 * n, n)")
			divisors := a.Have(
				"a prime dividing C(2n, n) divides (2n)! = n!·n!·C(2n, n), so it is at most 2n",
				"∀p:num. nat_prime(p) ∧ p ∣ binomial(2 * n, n) ⇒ p ≤ 2 * n",
				Derive(func(b *Argument) {
					p := b.FixAs[Nat]("p")
					b.Show(
						"C(2n, n) divides (2n)!, and a prime divides (2n)! only up to 2n",
						ByArith(
							binomial.FactorialFormula.At(double, n),
							nat_divides.DividesOwnMultiple.At(central, b.TermAs[Nat]("factorial(n) * factorial(n)")),
							nat_divides.DividesTrans.At(p, central, b.TermAs[Nat]("factorial(2 * n)")),
							nat_prime.PrimeDividesFactorial.At(p, double)))
				}))
			a.Show(
				"so C(2n, n), which is not 0, is the product of its prime powers over the primes up to 2n",
				ByArith(
					divisors,
					nat_multiplicity.PrimeFactorizationProduct.At(double, central),
					binomial.EqZero.At(double, n)))
		}),
})}

// LargePrimeMultiplicityAtMostOne — a prime whose square exceeds 2n divides
// C(2n, n) at most once: p to its multiplicity is at most 2n < p², so the
// multiplicity is below 2; at n = 0 it is the empty sum of carries.
var LargePrimeMultiplicityAtMostOne = largePrimeMultiplicityAtMostOneThm{family.Add(registry.ProofEntry{
	Name: "LargePrimeMultiplicityAtMostOne",
	Key:  "prop_3d89559ac040f84f",
	Build: family.Theorem(Statement{
		Binders: "∀p n:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"2 * n < p * p",
		},
		Conclusion: "nat_multiplicity(p, binomial(2 * n, n)) ≤ 1",
	},
		func(a *Argument, p, n *Expr[Nat], prime, small Fact) {
			positive := a.Unless(
				a.TermAs[Bool]("n = 0"),
				"at n = 0 the sum of the carries runs over 1 .. 0 and is empty",
				Given(func(b *Argument, isZero Fact) {
					b.Do(ByArith(
						prime,
						isZero,
						CentralBinomialMultiplicity.At(p, n),
						nat_sum.IntervalClauses.At(
							b.Ctx().Nat(1),
							b.Ctx().Nat(0),
							b.TermAs[Fun[Nat, Nat]]("λi:num. div(2 * n, p ^ i) - 2 * div(n, p ^ i)"))))
				}))
			a.Show(
				"p to the multiplicity is at most 2n < p², so the multiplicity is below 2",
				ByArith(
					prime,
					positive,
					small,
					CentralBinomialPrimePower.At(p, n),
					nat_prime.PrimeAtLeastTwo.At(p),
					nat_order.LessEqPow.At(
						p,
						a.Ctx().Nat(2),
						a.TermAs[Nat]("nat_multiplicity(p, binomial(2 * n, n))"))))
		}),
})}

// MiddlePrimesDoNotDivide — a prime p with 2n < 3p and p ≤ n does not divide
// C(2n, n), once n ≥ 3. Its multiplicity is the sum of the carries: at i = 1,
// p ≤ n < 2p and 2p ≤ 2n < 3p give div(2n, p) − 2·div(n, p) = 2 − 2·1 = 0.
// From n ≥ 3, 3p > 2n ≥ 6 puts p at least 3, so p² ≥ 3p exceeds 2n and every
// later carry is 0 too. The bound on n is needed: at n = 2 the prime 2 has
// 2 ≤ 2 and 4 < 6, and divides C(4, 2) = 6.
var MiddlePrimesDoNotDivide = middlePrimesDoNotDivideThm{family.Add(registry.ProofEntry{
	Name: "MiddlePrimesDoNotDivide",
	Key:  "prop_d042a46dae8fb09d",
	Build: family.Theorem(Statement{
		Binders: "∀n p:num.",
		Hypotheses: []string{
			"3 ≤ n",
			"nat_prime(p)",
			"p ≤ n",
			"2 * n < 3 * p",
		},
		Conclusion: "¬(p ∣ binomial(2 * n, n))",
		Abbrev: Abbrev{
			{Name: "carry", Text: "λi:num. div(2 * n, p ^ i) - 2 * div(n, p ^ i)"},
		},
	},
		func(a *Argument, n, p *Expr[Nat], large, prime, atMost, above Fact) {
			atLeastTwo := a.Have(
				"a prime is at least 2",
				"2 ≤ p",
				By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
			double := a.TermAs[Nat]("2 * n")
			square := a.Have(
				"3p > 2n ≥ 6 puts p at least 3, so p² ≥ 3p > 2n",
				"2 * n < p * p",
				ByArith(large, above, nat_order.LessEqMulMono.At(p, a.Ctx().Nat(3), p)))
			carries := a.Have(
				"no carry survives: the first is 2 − 2·1, and past it pⁱ ≥ p² exceeds 2n",
				"∀i:num. i ∈ 1 .. 2 * n ⇒ «carry»(i) = 0",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]("i")
					b.Cases(b.TermAs[Bool]("i = 1"))
					b.When(
						"at i = 1: p ≤ n < 2p and 2p ≤ 2n < 3p, so div(n, p) = 1 and div(2n, p) = 2",
						func(c *Argument, first Fact) {
							c.Show(
								"the carry is 2 − 2·1 = 0",
								ByArith(
									first,
									above,
									atMost,
									atLeastTwo,
									nat_arith.PowOne.At(p),
									nat_div_mod.LessEqRightDivEq.At(p, double, c.Ctx().Nat(2)),
									nat_div_mod.LessEqRightDivEq.At(p, double, c.Ctx().Nat(3)),
									nat_div_mod.LessEqRightDivEq.At(p, n, c.Ctx().Nat(1)),
									nat_div_mod.LessEqRightDivEq.At(p, n, c.Ctx().Nat(2))))
						})
					b.Otherwise(
						"past i = 1: pⁱ exceeds 2n, and both quotients by it vanish",
						func(c *Argument, later Fact) {
							inRange := c.Assume()
							exceeds := c.Have(
								"pⁱ ≥ p² exceeds 2n",
								"2 * n < p ^ i",
								ByArith(later, square, inRange, atLeastTwo, nat_order.LessEqPow.At(p, c.Ctx().Nat(2), i)))
							c.Show(
								"so div(2n, pⁱ) = 0, and the carry with it",
								ByArith(
									exceeds,
									atLeastTwo,
									nat_arith.PowEqZero.At(p, i),
									nat_div_mod.DivEqZero.At(double, c.TermAs[Nat]("p ^ i"))))
						})
				}))
			none := a.Have(
				"so the multiplicity of p, the sum of the carries, is 0",
				"nat_multiplicity(p, binomial(2 * n, n)) = 0",
				ByArith(
					prime,
					carries,
					nat_sum.EqZero.At(a.TermAs[Set[Nat]]("1 .. 2 * n"), a.TermAs[Fun[Nat, Nat]]("«carry»")),
					num_segment.Finite.At(a.Ctx().Nat(1), double),
					CentralBinomialMultiplicity.At(p, n)))
			a.Show(
				"and p does not divide C(2n, n), which is not 0",
				ByArith(
					atLeastTwo,
					none,
					nat_multiplicity.DividesIff.At(p, a.TermAs[Nat]("binomial(2 * n, n)"), a.Ctx().Nat(1)),
					nat_arith.PowOne.At(p),
					binomial.EqZero.At(double, n)))
		}),
})}
