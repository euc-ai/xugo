// bertrand.go — Erdős's argument for Bertrand's postulate: with no prime in
// ⟬n, 2n⟧, every prime factor of C(2n, n) is at most 2n/3 or has its square
// at most 2n, which bounds the coefficient by the primorial of 2n/3 times a
// power of 2n; set against C(2n, n) ≥ 4ⁿ/(2n + 1), that bound fails for
// n ≥ 613. Below 613 a chain of primes, each less than twice the one before
// and each certified prime by a Bezout relation with a factorial, covers n.

package prime_distribution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Erdős's bound with no prime in ⟬n, 2n⟧
// ---------------------------------------------------------------------------

// NoPrimeBinomialBound — if no prime lies in ⟬n, 2n⟧, with n ≥ 3, then C(2n, n)
// is at most (2n) raised to the number of primes p with p² ≤ 2n, times the
// primorial of 2n/3. C(2n, n) is the product of its prime powers over the
// primes up to 2n, its prime divisors dividing (2n)!. A prime with p² ≤ 2n
// contributes at most 2n (CentralBinomialPrimePower); a larger one divides
// C(2n, n) at most once, so contributes at most p, and none in ⟬2n/3, n⟧
// divides it at all (MiddlePrimesDoNotDivide), while ⟬n, 2n⟧ holds no prime.
// So each prime power is at most the product of a factor 2n where p² ≤ 2n
// and a factor p where p ≤ 2n/3, and the two products are (2n)^(their count)
// and the primorial.
var NoPrimeBinomialBound = noPrimeBinomialBoundThm{family.Add(registry.ProofEntry{
	Name: "NoPrimeBinomialBound",
	Key:  "prop_4bfc3cd9317590c6",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"3 ≤ n",
			"¬(∃p:num. nat_prime(p) ∧ n < p ∧ p ≤ 2 * n)",
		},
		Conclusion: "binomial(2 * n, n) ≤ " +
			"(2 * n) ^ card({p:num | nat_prime(p) ∧ p * p ≤ 2 * n}) * primorial(div(2 * n, 3))",
		Abbrev: Abbrev{
			{Name: "primePower", Text: "λp:num. p ^ nat_multiplicity(p, binomial(2 * n, n))"},
			{Name: "squareBound", Text: "λp:num. COND(p * p ≤ 2 * n, 2 * n, 1)"},
			{Name: "thirdBound", Text: "λp:num. COND(p ≤ div(2 * n, 3), p, 1)"},
		},
	},
		func(a *Argument, n *Expr[Nat], large, noPrime Fact) {
			double := a.TermAs[Nat]("2 * n")
			central := a.TermAs[Nat]("binomial(2 * n, n)")
			primes := a.TermAs[Set[Nat]]("«primes»(2 * n)")
			termwise := a.Have(
				"each prime power is at most 2n where p² ≤ 2n, at most p where p ≤ 2n/3, and 1 otherwise",
				"∀p:num. p ∈ «primes»(2 * n) ⇒ «primePower»(p) ≤ «squareBound»(p) * «thirdBound»(p)",
				Derive(func(b *Argument) {
					p := b.FixAs[Nat]("p")
					member := b.Conjuncts(
						b.Assume(),
						"p is at most 2n",
						"p is prime")
					below, prime := member[0], member[1]
					atLeastTwo := b.Have(
						"a prime is at least 2",
						"2 ≤ p",
						By(prime, nat_prime.PrimeAtLeastTwo.At(p)))
					multiplicity := b.TermAs[Nat]("nat_multiplicity(p, binomial(2 * n, n))")
					b.Cases(b.TermAs[Bool]("p * p ≤ 2 * n"))
					b.When(
						"p² ≤ 2n: the prime power is at most 2n",
						func(c *Argument, small Fact) {
							c.Show(
								"and the factor for p ≤ 2n/3 is at least 1",
								ByArith(
									prime,
									small,
									large,
									CentralBinomialPrimePower.At(p, n),
									atLeastTwo,
									nat_order.LessEqMulMono.At(double, c.Ctx().Nat(1), c.TermAs[Nat]("«thirdBound»(p)"))))
						})
					b.Otherwise(
						"2n < p²: p divides C(2n, n) at most once",
						func(c *Argument, big Fact) {
							c.Cases(c.TermAs[Bool]("p ≤ div(2 * n, 3)"))
							c.When(
								"p ≤ 2n/3: the prime power is at most p",
								func(d *Argument, low Fact) {
									d.Show(
										"a multiplicity of at most 1 gives a power of at most p",
										ByArith(
											prime,
											big,
											low,
											LargePrimeMultiplicityAtMostOne.At(p, n),
											atLeastTwo,
											nat_order.LessEqPow.At(p, multiplicity, d.Ctx().Nat(1))))
								})
							c.Otherwise(
								"2n/3 < p: p lies in ⟬2n/3, n⟧ and does not divide C(2n, n)",
								func(d *Argument, high Fact) {
									middle := d.Have(
										"with no prime in ⟬n, 2n⟧, p is at most n",
										"p ≤ n",
										ByArith(prime, noPrime, below))
									absent := d.Have(
										"so 2n < 3p and p ≤ n, and p does not divide C(2n, n)",
										"¬(p ∣ binomial(2 * n, n))",
										ByArith(
											prime,
											high,
											middle,
											large,
											nat_div_mod.LessEqRightDivEq.At(d.Ctx().Nat(3), double, p),
											MiddlePrimesDoNotDivide.At(n, p)))
									none := d.Have(
										"so its multiplicity in C(2n, n), which is not 0, is 0",
										"nat_multiplicity(p, binomial(2 * n, n)) = 0",
										ByArith(
											atLeastTwo,
											absent,
											nat_multiplicity.DividesIff.At(p, central, d.Ctx().Nat(1)),
											binomial.EqZero.At(double, n),
											nat_arith.PowOne.At(p)))
									d.Show(
										"and the prime power is p⁰ = 1, as are both factors, p being past 2n/3 and p² past 2n",
										ByArith(
											atLeastTwo,
											high,
											big,
											none,
											nat_order.LessEqPow.At(p, multiplicity, d.Ctx().Nat(0)),
											nat_arith.NatPow))
								})
						})
				}))
			finite := PrimesFinite.At(double)
			rootBelow := a.Have(
				"p² ≤ 2n puts p at most 2n",
				"∀p:num. p * p ≤ 2 * n ⇒ p ≤ 2 * n",
				a.ForEach(func(p *Expr[Nat]) Action {
					return ByArith(nat_order.LessEqMulNonzero.At(p, p))
				}))
			thirdBelow := a.Have(
				"as does p ≤ 2n/3",
				"∀p:num. p ≤ div(2 * n, 3) ⇒ p ≤ 2 * n",
				a.ForEach(func(p *Expr[Nat]) Action {
					return ByArith(nat_div_mod.DivLessEq.At(double, a.Ctx().Nat(3)))
				}))
			squares := a.Have(
				"the primes with p² ≤ 2n are the primes up to 2n with p² ≤ 2n",
				"{p:num | nat_prime(p) ∧ p * p ≤ 2 * n} = {p:num | p ∈ «primes»(2 * n) ∧ p * p ≤ 2 * n}",
				BySets(rootBelow))
			thirds := a.Have(
				"and the primes up to 2n/3 are the primes up to 2n that are at most 2n/3",
				"{p:num | p ∈ «primes»(2 * n) ∧ p ≤ div(2 * n, 3)} = «primes»(div(2 * n, 3))",
				BySets(thirdBelow))
			squareSet := a.TermAs[Set[Nat]]("{p:num | nat_prime(p) ∧ p * p ≤ 2 * n}")
			squareFactors := a.Have(
				"the factors 2n stand at the primes with p² ≤ 2n, and multiply to 2n to their count",
				"Π_{p∈«primes»(2 * n)} «squareBound»(p) = (2 * n) ^ card({p:num | nat_prime(p) ∧ p * p ≤ 2 * n})",
				CalcEq(
					Leg(
						a.TermAs[Nat]("Π_{p∈{p:num | nat_prime(p) ∧ p * p ≤ 2 * n}} 2 * n"),
						"the factor is 2n where p² ≤ 2n and 1 elsewhere",
						By(
							squares,
							monoidal.Restrict.Read(nat_product.MonoidalNatMul).At(
								primes,
								a.TermAs[Set[Nat]]("λp:num. p * p ≤ 2 * n"),
								a.TermAs[Fun[Nat, Nat]]("λp:num. 2 * n")),
							nat_product.NeutralNatMul,
							nat_product.NatProductDef)),
					FinalLeg(
						"a product of the constant 2n over a finite set",
						BySets(
							finite,
							rootBelow,
							nat_product.NatProductConst.At(squareSet, double),
							finite_set.FiniteSubset.At(squareSet, primes)))))
			thirdFactors := a.Have(
				"the factors p stand at the primes up to 2n/3, and multiply to their primorial",
				"Π_{p∈«primes»(2 * n)} «thirdBound»(p) = primorial(div(2 * n, 3))",
				By(
					thirds,
					monoidal.Restrict.Read(nat_product.MonoidalNatMul).At(
						primes,
						a.TermAs[Set[Nat]]("λp:num. p ≤ div(2 * n, 3)"),
						a.TermAs[Fun[Nat, Nat]]("λp:num. p")),
					nat_product.NeutralNatMul,
					nat_product.NatProductDef,
					PrimorialDef))
			a.Show(
				"C(2n, n) = Π pᵛ ≤ Π (the two factors) = (2n)^(the count) · primorial(2n/3)",
				nat_order.OrderCalc(a.Ctx()).CalcLeibniz(central,
					EqLeg(
						a.TermAs[Nat]("Π_{p∈«primes»(2 * n)} «primePower»(p)"),
						"C(2n, n) is the product of its prime powers over the primes up to 2n",
						Cite(CentralBinomialFactorization, n)),
					LeLeg(
						a.TermAs[Nat]("Π_{p∈«primes»(2 * n)} «squareBound»(p) * «thirdBound»(p)"),
						"each prime power is at most its two factors",
						By(
							finite,
							termwise,
							nat_product.NatProductMonotone.At(
								primes,
								a.TermAs[Fun[Nat, Nat]]("«primePower»"),
								a.TermAs[Fun[Nat, Nat]]("λp:num. «squareBound»(p) * «thirdBound»(p)")))),
					EqLeg(
						a.TermAs[Nat]("(Π_{p∈«primes»(2 * n)} «squareBound»(p)) * Π_{p∈«primes»(2 * n)} «thirdBound»(p)"),
						"the product of the factors is the product of the two products",
						By(
							finite,
							monoidal.Pointwise.Read(nat_product.MonoidalNatMul).At(
								a.TermAs[Fun[Nat, Nat]]("«squareBound»"),
								a.TermAs[Fun[Nat, Nat]]("«thirdBound»"),
								primes),
							nat_product.NatProductDef)),
					EqLeg(
						a.TermAs[Nat]("(2 * n) ^ card({p:num | nat_prime(p) ∧ p * p ≤ 2 * n}) * primorial(div(2 * n, 3))"),
						"the two products",
						By(squareFactors, thirdFactors))))
		}),
})}

// ---------------------------------------------------------------------------
// The estimate for n ≥ 613
// ---------------------------------------------------------------------------

// BertrandLarge — for n ≥ 613 some prime lies in ⟬n, 2n⟧. Erdős: with none
// there, C(2n, n) ≤ (2n)^s·primorial(2n/3) (NoPrimeBinomialBound), s the
// number of primes p with p² ≤ 2n, while 4ⁿ ≤ (2n + 1)·C(2n, n). Bracket
// 4^i ≤ 2n < 4^(i + 1): such a p is at most 2·2^i, so s ≤ 2^i + 1, and with
// primorial(m) ≤ 4^m the two bounds give n ≤ (i + 1)(2^i + 2) + 2n/3, so
// n ≤ 3(i + 1)(2^i + 2). That is at most 612 for i ≤ 5, and below 4^i/2 ≤ n
// for i ≥ 6, where 8(i + 1) ≤ 2^i.
var BertrandLarge = bertrandLargeThm{family.Add(registry.ProofEntry{
	Name: "BertrandLarge",
	Key:  "prop_5bfa4fc862bd0055",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"613 ≤ n",
		},
		Conclusion: "∃p:num. nat_prime(p) ∧ n < p ∧ p ≤ 2 * n",
		Abbrev: Abbrev{
			{Name: "rootPrimes", Text: "{p:num | nat_prime(p) ∧ p * p ≤ 2 * n}"},
		},
	},
		func(a *Argument, n *Expr[Nat], large Fact) {
			noPrime := a.SupposeNot()
			double := a.TermAs[Nat]("2 * n")
			third := a.TermAs[Nat]("div(2 * n, 3)")
			count := a.TermAs[Nat]("card(«rootPrimes»)")
			i, bracket := a.ObtainAs[Nat](
				"2n lies between consecutive powers of 4",
				"∃i:num. 4 ^ i ≤ 2 * n ∧ 2 * n < 4 ^ (i + 1)",
				ByArith(large, nat_order.PowerBracket.At(a.Ctx().Nat(4), double)))
			power := a.TermAs[Nat]("2 ^ i")
			justAbove := a.TermAs[Nat]("2 * 2 ^ i + 1")
			outer := a.TermAs[Nat]("4 ^ (i + 1)")
			below := a.Have(
				"p² ≤ 2n < 4^(i + 1) = (2·2^i)², and a p just above 2·2^i would square past it, so p ≤ 2·2^i",
				"∀p:num. p * p ≤ 2 * n ⇒ p ≤ 2 * 2 ^ i",
				a.ForEach(func(p *Expr[Nat]) Action {
					return ByArith(
						bracket,
						nat_arith.MulPowDistrib.At(a.Ctx().Nat(2), a.Ctx().Nat(2), i),
						nat_arith.PowAdd.At(a.Ctx().Nat(4), i, a.Ctx().Nat(1)),
						nat_order.LessEqMul2.At(justAbove, p, justAbove, p))
				}))
			upTo := a.TermAs[Set[Nat]]("«primes»(2 * 2 ^ i)")
			inside := a.Have(
				"so the primes with p² ≤ 2n are primes up to 2·2^i",
				"«rootPrimes» ⊆ «primes»(2 * 2 ^ i)",
				BySets(below))
			finite := PrimesFinite.At(a.TermAs[Nat]("2 * 2 ^ i"))
			counted := a.Have(
				"and there are at most 2^i + 1 of them",
				"card(«rootPrimes») ≤ 2 ^ i + 1",
				ByArith(
					inside,
					finite,
					cardinality.CardSubset.At(a.TermAs[Set[Nat]]("«rootPrimes»"), upTo),
					PrimeCountingDoubleBound.At(power),
					PrimeCountingDef.At(a.TermAs[Nat]("2 * 2 ^ i"))))
			binomialBound := a.Have(
				"with no prime in ⟬n, 2n⟧, C(2n, n) ≤ (2n)^s·primorial(2n/3)",
				"binomial(2 * n, n) ≤ (2 * n) ^ card(«rootPrimes») * primorial(div(2 * n, 3))",
				ByArith(noPrime, large, NoPrimeBinomialBound.At(n)))
			powerBound := a.Have(
				"(2n)^s ≤ (4^(i + 1))^s ≤ (4^(i + 1))^(2^i + 1) = 4^((i + 1)(2^i + 1))",
				"(2 * n) ^ card(«rootPrimes») ≤ 4 ^ ((i + 1) * (2 ^ i + 1))",
				ByArith(
					counted,
					bracket,
					nat_order.PowBaseMonotone.At(double, outer, count),
					nat_order.LessEqPow.At(outer, count, a.TermAs[Nat]("2 ^ i + 1")),
					nat_arith.PowPow.At(a.Ctx().Nat(4), a.TermAs[Nat]("i + 1"), a.TermAs[Nat]("2 ^ i + 1"))))
			exponent := a.TermAs[Nat]("i + 1 + (i + 1) * (2 ^ i + 1) + div(2 * n, 3)")
			estimate := a.Have(
				"4ⁿ ≤ (2n + 1)·C(2n, n) ≤ 4^(i + 1)·4^((i + 1)(2^i + 1))·4^(2n/3)",
				"4 ^ n ≤ 4 ^ (i + 1 + (i + 1) * (2 ^ i + 1) + div(2 * n, 3))",
				nat_order.OrderCalc(a.Ctx()).CalcLeibniz(a.TermAs[Nat]("4 ^ n"),
					LeLeg(
						a.TermAs[Nat]("(2 * n + 1) * binomial(2 * n, n)"),
						"C(2n, n) is at least 4ⁿ/(2n + 1)",
						Cite(binomial.CentralBinomialLowerBound)),
					LeLeg(
						a.TermAs[Nat]("4 ^ (i + 1) * 4 ^ ((i + 1) * (2 ^ i + 1)) * 4 ^ div(2 * n, 3)"),
						"2n + 1 ≤ 4^(i + 1), and C(2n, n) ≤ (2n)^s·primorial(2n/3) ≤ 4^((i + 1)(2^i + 1))·4^(2n/3)",
						ByArith(
							bracket,
							binomialBound,
							powerBound,
							PrimorialBound.At(third),
							nat_order.LessEqMul2.At(
								a.TermAs[Nat]("(2 * n) ^ card(«rootPrimes»)"),
								a.TermAs[Nat]("4 ^ ((i + 1) * (2 ^ i + 1))"),
								a.TermAs[Nat]("primorial(div(2 * n, 3))"),
								a.TermAs[Nat]("4 ^ div(2 * n, 3)")),
							nat_order.LessEqMul2.At(
								a.TermAs[Nat]("2 * n + 1"),
								outer,
								a.TermAs[Nat]("binomial(2 * n, n)"),
								a.TermAs[Nat]("4 ^ ((i + 1) * (2 ^ i + 1)) * 4 ^ div(2 * n, 3)")))),
					EqLeg(
						a.TermAs[Nat]("4 ^ (i + 1 + (i + 1) * (2 ^ i + 1) + div(2 * n, 3))"),
						"the exponents add",
						ByArith(nat_arith.PowAdd))))
			few := a.Have(
				"so n ≤ (i + 1)(2^i + 2) + 2n/3, and as 3·(2n/3) ≤ 2n, n ≤ 3(i + 1)(2^i + 2)",
				"n ≤ 3 * (i + 1) * (2 ^ i + 2)",
				ByArith(
					estimate,
					nat_order.LessEqPow.At(a.Ctx().Nat(4), n, exponent),
					nat_div_mod.DivMulLessEq.At(double, a.Ctx().Nat(3))))
			a.Cases(a.TermAs[Bool]("i ≤ 5"))
			a.When(
				"i ≤ 5: then 3(i + 1)(2^i + 2) ≤ 3·6·34 = 612 < n",
				func(b *Argument, small Fact) {
					b.Show(
						"2^i ≤ 32 and i·2^i ≤ 5·32",
						ByArith(
							few,
							large,
							small,
							nat_order.PowTwoMonotone.At(i, b.Ctx().Nat(5)),
							nat_order.LessEqMul2.At(i, b.Ctx().Nat(5), power, b.Ctx().Nat(32))))
				})
			a.Otherwise(
				"i ≥ 6: then 8(i + 1) ≤ 2^i, and 3(i + 1)(2^i + 2) < 4^i/2 ≤ n",
				func(b *Argument, big Fact) {
					k, shift := b.ObtainAs[Nat](
						"i is k + 6 for some k",
						"∃k:num. i = k + 6",
						Witness(b.TermAs[Nat]("i - 6")),
						ByArith(big))
					growth := b.Have(
						"8(i + 1) ≤ 2^i, as 2^i = 64·2^k and k < 2^k",
						"8 * (i + 1) ≤ 2 ^ i",
						ByArith(
							shift,
							nat_arith.PowAdd.At(b.Ctx().Nat(2), k, b.Ctx().Nat(6)),
							nat_order.LessThanPowTwoSelf.At(k)))
					b.Show(
						"24(i + 1)(2^i + 2) ≤ 3·2^i(2^i + 2) = 3·4^i + 6·2^i < 4·4^i ≤ 8n, as 56 ≤ 2^i gives 56·2^i ≤ 4^i",
						ByArith(
							few,
							big,
							growth,
							bracket,
							nat_arith.MulPowDistrib.At(b.Ctx().Nat(2), b.Ctx().Nat(2), i),
							nat_order.LessEqMul2.At(
								b.TermAs[Nat]("8 * (i + 1)"),
								power,
								b.TermAs[Nat]("2 ^ i + 2"),
								b.TermAs[Nat]("2 ^ i + 2")),
							nat_order.LessEqMul2.At(b.Ctx().Nat(56), power, power, power)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Bertrand's postulate
// ---------------------------------------------------------------------------

// BertrandChainPrimes — 3, 5, 7, 13, 23, 43, 83, 163, 317 and 631 are prime:
// with 2 they are Bertrand's chain, each below twice the one before. Each p is
// certified by nat_prime.CoprimeToFactorialPrime at the m with m² ≤ p < (m + 1)² and a
// Bezout relation p·x = m!·y + 1. The factorials up to 10! come from their
// recursion; 12!, 17! and 20! follow from (n + 1)! = (n + 1)·n!, and 25! is
// kept as 6375600 = 25·24·23·22·21 times 20!, multiplied out only in 631's
// relation.
var BertrandChainPrimes = bertrandChainPrimesThm{family.Add(registry.ProofEntry{
	Name: "BertrandChainPrimes",
	Key:  "prop_7ca8a39abb2bfe27",
	Build: family.Theorem(
		"nat_prime(3) ∧ "+
			"nat_prime(5) ∧ "+
			"nat_prime(7) ∧ "+
			"nat_prime(13) ∧ "+
			"nat_prime(23) ∧ "+
			"nat_prime(43) ∧ "+
			"nat_prime(83) ∧ "+
			"nat_prime(163) ∧ "+
			"nat_prime(317) ∧ "+
			"nat_prime(631)",
		func(a *Argument) {
			step := a.Have(
				"(n + 1)! = (n + 1)·n!",
				"∀n:num. factorial(n + 1) = (n + 1) * factorial(n)",
				ByArith(nat_arith.Factorial, nat_arith.Add1))
			twelve := a.Have(
				"12! = 12·11·10!",
				"factorial(12) = 479001600",
				ByArith(nat_arith.Factorial, step.At(a.Ctx().Nat(10)), step.At(a.Ctx().Nat(11))))
			seventeen := a.Have(
				"17! = 17·16·15·14·13·12!",
				"factorial(17) = 355687428096000",
				ByArith(
					twelve,
					step.At(a.Ctx().Nat(12)),
					step.At(a.Ctx().Nat(13)),
					step.At(a.Ctx().Nat(14)),
					step.At(a.Ctx().Nat(15)),
					step.At(a.Ctx().Nat(16))))
			twenty := a.Have(
				"20! = 20·19·18·17!",
				"factorial(20) = 2432902008176640000",
				ByArith(seventeen, step.At(a.Ctx().Nat(17)), step.At(a.Ctx().Nat(18)), step.At(a.Ctx().Nat(19))))
			twentyFive := a.Have(
				"25! = 25·24·23·22·21·20!",
				"factorial(25) = 6375600 * factorial(20)",
				ByArith(
					step.At(a.Ctx().Nat(20)),
					step.At(a.Ctx().Nat(21)),
					step.At(a.Ctx().Nat(22)),
					step.At(a.Ctx().Nat(23)),
					step.At(a.Ctx().Nat(24))))
			a.Show(
				"each p of the chain has p·x = m!·y + 1 with m² ≤ p < (m + 1)²",
				ByArith(
					nat_arith.Factorial,
					twelve,
					seventeen,
					twenty,
					twentyFive,
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(3), a.Ctx().Nat(1), a.Ctx().Nat(1), a.Ctx().Nat(2)),
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(5), a.Ctx().Nat(2), a.Ctx().Nat(1), a.Ctx().Nat(2)),
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(7), a.Ctx().Nat(2), a.Ctx().Nat(1), a.Ctx().Nat(3)),
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(13), a.Ctx().Nat(3), a.Ctx().Nat(1), a.Ctx().Nat(2)),
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(23), a.Ctx().Nat(4), a.Ctx().Nat(23), a.Ctx().Nat(22)),
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(43), a.Ctx().Nat(6), a.Ctx().Nat(67), a.Ctx().Nat(4)),
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(83), a.Ctx().Nat(9), a.Ctx().Nat(271067), a.Ctx().Nat(62)),
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(163), a.Ctx().Nat(12), a.Ctx().Nat(167503627), a.Ctx().Nat(57)),
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(317), a.Ctx().Nat(17), a.Ctx().Nat(34783313157653), a.Ctx().Nat(31)),
					// 631's witness x is past int64, so it is read from its text
					nat_prime.CoprimeToFactorialPrime.At(
						a.Ctx().Nat(631), a.Ctx().Nat(25), a.TermAs[Nat]("393311189688265888659271"), a.Ctx().Nat(16))))
		}),
})}

// BertrandSmall — Bertrand's postulate for 1 ≤ n < 613, the range the
// estimate leaves. The primes 2, 3, 5, 7, 13, 23, 43, 83, 163, 317, 631 each
// lie below twice the one before, so for n from one of them up to the next
// that next prime lies in ⟬n, 2n⟧; from 317 on, 631 serves up to 612.
var BertrandSmall = bertrandSmallThm{family.Add(registry.ProofEntry{
	Name: "BertrandSmall",
	Key:  "prop_7a20dfca40e92fe2",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"1 ≤ n",
			"n < 613",
		},
		Conclusion: "∃p:num. nat_prime(p) ∧ n < p ∧ p ≤ 2 * n",
	},
		func(a *Argument, n *Expr[Nat], positive, small Fact) {
			atLeast2 := a.Unless(
				a.TermAs[Bool]("n < 2"),
				"n = 1: the prime 2 lies in ⟬1, 2⟧",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(2))
					b.Show(
						"n < 2 ≤ 2n",
						ByArith(positive, below, nat_prime.PrimeTwo))
				}))
			atLeast3 := a.Unless(
				a.TermAs[Bool]("n < 3"),
				"n = 2: the prime 3 lies in ⟬2, 4⟧",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(3))
					b.Show(
						"n < 3 ≤ 4 ≤ 2n",
						ByArith(atLeast2, below, BertrandChainPrimes))
				}))
			atLeast5 := a.Unless(
				a.TermAs[Bool]("n < 5"),
				"3 ≤ n < 5: take the prime 5",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(5))
					b.Show(
						"n < 5 ≤ 6 ≤ 2n",
						ByArith(atLeast3, below, BertrandChainPrimes))
				}))
			atLeast7 := a.Unless(
				a.TermAs[Bool]("n < 7"),
				"5 ≤ n < 7: take the prime 7",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(7))
					b.Show(
						"n < 7 ≤ 10 ≤ 2n",
						ByArith(atLeast5, below, BertrandChainPrimes))
				}))
			atLeast13 := a.Unless(
				a.TermAs[Bool]("n < 13"),
				"7 ≤ n < 13: take the prime 13",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(13))
					b.Show(
						"n < 13 ≤ 14 ≤ 2n",
						ByArith(atLeast7, below, BertrandChainPrimes))
				}))
			atLeast23 := a.Unless(
				a.TermAs[Bool]("n < 23"),
				"13 ≤ n < 23: take the prime 23",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(23))
					b.Show(
						"n < 23 ≤ 26 ≤ 2n",
						ByArith(atLeast13, below, BertrandChainPrimes))
				}))
			atLeast43 := a.Unless(
				a.TermAs[Bool]("n < 43"),
				"23 ≤ n < 43: take the prime 43",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(43))
					b.Show(
						"n < 43 ≤ 46 ≤ 2n",
						ByArith(atLeast23, below, BertrandChainPrimes))
				}))
			atLeast83 := a.Unless(
				a.TermAs[Bool]("n < 83"),
				"43 ≤ n < 83: take the prime 83",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(83))
					b.Show(
						"n < 83 ≤ 86 ≤ 2n",
						ByArith(atLeast43, below, BertrandChainPrimes))
				}))
			atLeast163 := a.Unless(
				a.TermAs[Bool]("n < 163"),
				"83 ≤ n < 163: take the prime 163",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(163))
					b.Show(
						"n < 163 ≤ 166 ≤ 2n",
						ByArith(atLeast83, below, BertrandChainPrimes))
				}))
			atLeast317 := a.Unless(
				a.TermAs[Bool]("n < 317"),
				"163 ≤ n < 317: take the prime 317",
				Given(func(b *Argument, below Fact) {
					b.Take(b.Ctx().Nat(317))
					b.Show(
						"n < 317 ≤ 326 ≤ 2n",
						ByArith(atLeast163, below, BertrandChainPrimes))
				}))
			a.Take(a.Ctx().Nat(631))
			a.Show(
				"317 ≤ n < 613: n < 631 ≤ 634 ≤ 2n",
				ByArith(atLeast317, small, BertrandChainPrimes))
		}),
})}

// Bertrand — Bertrand's postulate: for every n ≥ 1 some prime p has
// n < p ≤ 2n. Below 613 a chain of primes each less than twice the one
// before supplies it (BertrandSmall); from 613 on Erdős's estimate does
// (BertrandLarge).
var Bertrand = bertrandThm{family.Add(registry.ProofEntry{
	Name: "Bertrand",
	Key:  "prop_12a9504292aa3776",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"1 ≤ n",
		},
		Conclusion: "∃p:num. nat_prime(p) ∧ n < p ∧ p ≤ 2 * n",
	},
		func(a *Argument, n *Expr[Nat], positive Fact) {
			a.Cases(a.TermAs[Bool]("n < 613"))
			a.When(
				"n < 613: the chain of small primes",
				func(b *Argument, small Fact) {
					b.Show(
						"a chain prime lies in ⟬n, 2n⟧",
						By(BertrandSmall.At(n), positive, small))
				})
			a.Otherwise(
				"613 ≤ n: Erdős's estimate",
				func(b *Argument, large Fact) {
					b.Show(
						"Erdős's estimate puts a prime in ⟬n, 2n⟧",
						ByArith(large, BertrandLarge.At(n)))
				})
		}),
})}
