// chebyshev.go — Chebyshev's bounds on π(n): C(2m, m) ≤ (2m)^π(2m) from its
// prime powers, hence 2ⁿ ≤ n^(2π(n)); n^π(n) ≤ 64ⁿ from the primorial past
// √n; and the two read through the logarithm as
// (log 2 / 2)·n ≤ π(n)·log n ≤ 5n.

package prime_distribution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/real/real_exp_log"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The two bounds as powers
// ---------------------------------------------------------------------------

// CentralBinomialUpperBound — C(2m, m) is at most 2m raised to the number of
// primes up to 2m: its prime divisors divide (2m)!, so they are among those
// primes, it is the product of its prime powers over them, and each of those
// powers is at most 2m (CentralBinomialPrimePower).
var CentralBinomialUpperBound = centralBinomialUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "CentralBinomialUpperBound",
	Key:  "prop_f72d00dc4ed3422f",
	Build: family.Theorem(Statement{
		Binders: "∀m:num.",
		Hypotheses: []string{
			"1 ≤ m",
		},
		Conclusion: "binomial(2 * m, m) ≤ (2 * m) ^ prime_counting(2 * m)",
	},
		func(a *Argument, m *Expr[Nat], positive Fact) {
			double := a.TermAs[Nat]("2 * m")
			central := a.TermAs[Nat]("binomial(2 * m, m)")
			primes := a.TermAs[Set[Nat]]("«primes»(2 * m)")
			termwise := a.Have(
				"each prime power dividing C(2m, m) is at most 2m",
				"∀p:num. p ∈ «primes»(2 * m) ⇒ p ^ nat_multiplicity(p, binomial(2 * m, m)) ≤ 2 * m",
				a.ForEach(func(p *Expr[Nat]) Action {
					return By(positive, CentralBinomialPrimePower.At(p, m))
				}))
			finite := PrimesFinite.At(double)
			a.Show(
				"C(2m, m) = Π pᵛ ≤ (2m)^π(2m)",
				nat_order.OrderCalc(a.Ctx()).CalcLeibniz(central,
					EqLeg(
						a.TermAs[Nat]("Π_{p∈«primes»(2 * m)} p ^ nat_multiplicity(p, binomial(2 * m, m))"),
						"C(2m, m) is the product of its prime powers over the primes up to 2m",
						Cite(CentralBinomialFactorization, m)),
					LeLeg(
						a.TermAs[Nat]("(2 * m) ^ prime_counting(2 * m)"),
						"each of its π(2m) prime powers is at most 2m",
						By(
							finite,
							termwise,
							nat_product.NatProductUpperBound.At(
								primes,
								a.TermAs[Fun[Nat, Nat]]("λp:num. p ^ nat_multiplicity(p, binomial(2 * m, m))"),
								double),
							PrimeCountingDef.At(double)))))
		}),
})}

// ChebyshevLowerPower — for n ≥ 2, two to the n is at most n raised to twice
// the number of primes up to n. Write n as 2m or 2m + 1. Then
// 2ⁿ ≤ 2·4ᵐ ≤ 2(2m + 1)·C(2m, m) ≤ 2(2m + 1)·(2m)^π(2m)
// (binomial.CentralBinomialLowerBound, CentralBinomialUpperBound), and
// (2m)^π(2m) is at most n^π(n). From n = 3 on, 2 and 3 make π(n) ≥ 2, so the
// spare factor 2(2m + 1) ≤ n² is at most n^π(n) as well; at n = 2, π(2) ≥ 1
// is enough.
var ChebyshevLowerPower = chebyshevLowerPowerThm{family.Add(registry.ProofEntry{
	Name: "ChebyshevLowerPower",
	Key:  "prop_9d4c97bbe19b7e5d",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"2 ≤ n",
		},
		Conclusion: "2 ^ n ≤ n ^ (2 * prime_counting(n))",
	},
		func(a *Argument, n *Expr[Nat], large Fact) {
			count := a.TermAs[Nat]("prime_counting(n)")
			primes := a.TermAs[Set[Nat]]("«primes»(n)")
			finite := PrimesFinite.At(n)
			notTwo := a.Unless(
				a.TermAs[Bool]("n = 2"),
				"n = 2: the prime 2 makes π(2) ≥ 1, and 2² ≤ 2^(2π(2))",
				Given(func(b *Argument, isTwo Fact) {
					some := b.Have(
						"2 is a prime up to n, so π(n) ≥ 1",
						"1 ≤ prime_counting(n)",
						BySets(
							finite,
							large,
							nat_prime.PrimeTwo,
							cardinality.CardSubset.At(b.TermAs[Set[Nat]]("{2}"), primes),
							cardinality.CardSing.At(b.Ctx().Nat(2)),
							PrimeCountingDef.At(n)))
					b.Do(ByArith(
						isTwo,
						some,
						nat_order.LessEqPow.At(b.Ctx().Nat(2), b.Ctx().Nat(2), b.TermAs[Nat]("2 * prime_counting(n)"))))
				}))
			atLeastThree := a.Have(
				"so n is at least 3",
				"3 ≤ n",
				ByArith(large, notTwo))
			pair := a.Have(
				"2 and 3 are primes up to n, 3 being the first of Bertrand's chain primes",
				"{2, 3} ⊆ «primes»(n)",
				BySets(large, atLeastThree, nat_prime.PrimeTwo, BertrandChainPrimes))
			pairCount := a.Have(
				"and they are two",
				"card({2, 3}) = 2",
				ByArith(
					set_basic.InSing.At(a.Ctx().Nat(2), a.Ctx().Nat(3)),
					cardinality.InsertCountsOneMore.At(a.TermAs[Set[Nat]]("{3}"), a.Ctx().Nat(2)),
					finite_set.FiniteSing.At(a.Ctx().Nat(3)),
					cardinality.CardSing.At(a.Ctx().Nat(3))))
			several := a.Have(
				"so π(n) ≥ 2",
				"2 ≤ prime_counting(n)",
				By(
					finite,
					pair,
					pairCount,
					cardinality.CardSubset.At(a.TermAs[Set[Nat]]("{2, 3}"), primes),
					PrimeCountingDef.At(n)))
			m, half := a.ObtainAs[Nat](
				"n is 2m or 2m + 1, with m = ⌊n/2⌋",
				"∃m:num. 2 * m ≤ n ∧ n ≤ 2 * m + 1",
				Witness(a.TermAs[Nat]("div(n, 2)")),
				ByArith(nat_div_mod.Division.At(n, a.Ctx().Nat(2))))
			double := a.TermAs[Nat]("2 * m")
			central := a.TermAs[Nat]("binomial(2 * m, m)")
			spare := a.TermAs[Nat]("2 * (2 * m + 1)")
			square := a.TermAs[Nat]("n * n")
			halfCount := a.TermAs[Nat]("prime_counting(2 * m)")
			halfPower := a.TermAs[Nat]("(2 * m) ^ prime_counting(2 * m)")
			power := a.TermAs[Nat]("n ^ prime_counting(n)")
			spareBound := a.Have(
				"the spare factor 2(2m + 1) is at most 3n ≤ n²",
				"2 * (2 * m + 1) ≤ n * n",
				ByArith(half, atLeastThree, nat_order.LessEqMul2.At(a.Ctx().Nat(3), n, n, n)))
			grows := a.Have(
				"(2m)^π(2m) ≤ n^π(2m) ≤ n^π(n), as 2m ≤ n",
				"(2 * m) ^ prime_counting(2 * m) ≤ n ^ prime_counting(n)",
				ByArith(
					large,
					half,
					nat_order.PowBaseMonotone.At(double, n, halfCount),
					nat_order.LessEqPow.At(n, halfCount, count),
					PrimeCountingMonotone.At(double, n)))
			a.Show(
				"2ⁿ ≤ 2·4ᵐ ≤ 2(2m + 1)·C(2m, m) ≤ 2(2m + 1)·(2m)^π(2m) ≤ n²·n^π(n) ≤ n^(2π(n))",
				nat_order.OrderCalc(a.Ctx()).CalcLeibniz(a.TermAs[Nat]("2 ^ n"),
					LeLeg(
						a.TermAs[Nat]("2 * 4 ^ m"),
						"n ≤ 2m + 1, and 2^(2m + 1) = 2·4ᵐ",
						ByArith(
							half,
							nat_order.LessEqPow.At(a.Ctx().Nat(2), n, a.TermAs[Nat]("2 * m + 1")),
							nat_arith.PowAdd.At(a.Ctx().Nat(2), double, a.Ctx().Nat(1)),
							nat_arith.PowPow.At(a.Ctx().Nat(2), a.Ctx().Nat(2), m))),
					LeLeg(
						a.TermAs[Nat]("2 * ((2 * m + 1) * binomial(2 * m, m))"),
						"4ᵐ ≤ (2m + 1)·C(2m, m)",
						ByArith(binomial.CentralBinomialLowerBound.At(m))),
					LeLeg(
						a.TermAs[Nat]("2 * ((2 * m + 1) * (2 * m) ^ prime_counting(2 * m))"),
						"m ≥ 1, so C(2m, m) ≤ (2m)^π(2m)",
						ByArith(
							half,
							atLeastThree,
							CentralBinomialUpperBound.At(m),
							nat_order.LessEqMulMono.At(spare, central, halfPower))),
					LeLeg(
						a.TermAs[Nat]("n * n * n ^ prime_counting(n)"),
						"the spare factor is at most n², and (2m)^π(2m) ≤ n^π(n)",
						ByArith(spareBound, grows, nat_order.LessEqMul2.At(spare, square, halfPower, power))),
					LeLeg(
						a.TermAs[Nat]("n ^ prime_counting(n) * n ^ prime_counting(n)"),
						"n² ≤ n^π(n), as π(n) ≥ 2",
						ByArith(
							large,
							several,
							nat_order.LessEqPow.At(n, a.Ctx().Nat(2), count),
							nat_order.LessEqMulMono.At(power, square, power))),
					EqLeg(
						a.TermAs[Nat]("n ^ (2 * prime_counting(n))"),
						"n^π(n)·n^π(n) = (n·n)^π(n) = n^(2π(n))",
						ByArith(
							nat_arith.PowPow.At(n, a.Ctx().Nat(2), count),
							nat_arith.MulPowDistrib.At(n, n, count),
							nat_arith.PowTwo.At(n)))))
		}),
})}

// ChebyshevUpperPower — n raised to the number of primes up to n is at most
// 64 to the n. Take m with m² ≤ n < (m + 1)². The primes up to m are at most m
// in number, and n < (m + 1)² ≤ 4ᵐ, so they contribute n^π(m) ≤ (4ᵐ)ᵐ ≤ 4ⁿ.
// Each of the k primes in ⟬m, n⟧ is at least m + 1, whose square exceeds n, so
// nᵏ ≤ ((m + 1)ᵏ)² is at most the square of their product, which divides out
// of primorial(n) ≤ 4ⁿ (PrimorialSplit, PrimorialBound). So
// n^π(n) = n^π(m)·nᵏ ≤ 4ⁿ·16ⁿ = 64ⁿ.
var ChebyshevUpperPower = chebyshevUpperPowerThm{family.Add(registry.ProofEntry{
	Name: "ChebyshevUpperPower",
	Key:  "prop_dafb6456fd9c63cd",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Conclusion: "n ^ prime_counting(n) ≤ 64 ^ n",
	},
		func(a *Argument, n *Expr[Nat]) {
			count := a.TermAs[Nat]("prime_counting(n)")
			positive := a.Unless(
				a.TermAs[Bool]("n = 0"),
				"n = 0: 0^π(0) ≤ 0⁰ = 1 = 64⁰",
				Given(func(b *Argument, isZero Fact) {
					b.Do(ByArith(isZero, nat_order.LessEqPow.At(n, count, b.Ctx().Nat(0))))
				}))
			m, bracket := a.UnpackAs[Nat](nat_order.SquareBracket.At(n), "m")
			parts := a.Conjuncts(
				bracket,
				"m² ≤ n",
				"n < (m + 1)²")
			below, above := parts[0], parts[1]
			ordered := a.Have(
				"m ≤ m² ≤ n",
				"m ≤ n",
				ByArith(below, nat_order.LessEqMulNonzero.At(m, m)))
			next := a.TermAs[Nat]("m + 1")
			twoPower := a.TermAs[Nat]("2 ^ m")
			fourPower := a.TermAs[Nat]("4 ^ m")
			window := a.TermAs[Set[Nat]]("«primesBetween»(m, n)")
			width := a.TermAs[Nat]("card(«primesBetween»(m, n))")
			primeProduct := a.TermAs[Nat]("Π_{p∈«primesBetween»(m, n)} p")
			bound := a.TermAs[Nat]("4 ^ n")
			root := a.Have(
				"n < (m + 1)² ≤ (2ᵐ)² = 4ᵐ, as m < 2ᵐ",
				"n ≤ 4 ^ m",
				ByArith(
					above,
					nat_order.LessThanPowTwoSelf.At(m),
					nat_order.LessEqMul2.At(next, twoPower, next, twoPower),
					nat_arith.MulPowDistrib.At(a.Ctx().Nat(2), a.Ctx().Nat(2), m)))
			lowPrimes := a.Have(
				"the primes up to m contribute n^π(m) ≤ nᵐ ≤ (4ᵐ)ᵐ ≤ 4ⁿ",
				"n ^ prime_counting(m) ≤ 4 ^ n",
				nat_order.OrderCalc(a.Ctx()).CalcLeibniz(a.TermAs[Nat]("n ^ prime_counting(m)"),
					LeLeg(
						a.TermAs[Nat]("n ^ m"),
						"at most m primes are at most m",
						ByArith(
							positive,
							PrimeCountingLessEqSelf.At(m),
							nat_order.LessEqPow.At(n, a.TermAs[Nat]("prime_counting(m)"), m))),
					LeLeg(
						a.TermAs[Nat]("(4 ^ m) ^ m"),
						"n ≤ 4ᵐ",
						By(root, nat_order.PowBaseMonotone.At(n, fourPower, m))),
					EqLeg(
						a.TermAs[Nat]("4 ^ (m * m)"),
						"(4ᵐ)ᵐ = 4^(m²)",
						By(nat_arith.PowPow.At(a.Ctx().Nat(4), m, m))),
					LeLeg(
						bound,
						"m² ≤ n",
						By(below, nat_order.LessEqPow.At(a.Ctx().Nat(4), a.TermAs[Nat]("m * m"), n)))))
			finiteWindow := a.Have(
				"only finitely many primes lie in ⟬m, n⟧",
				"finite(«primesBetween»(m, n))",
				BySets(
					finite_set.FiniteSubset.At(window, a.TermAs[Set[Nat]]("{x:num | x ≤ n}")),
					num_segment.FiniteBelow))
			pastRoot := a.Have(
				"a prime in ⟬m, n⟧ is at least m + 1",
				"∀p:num. p ∈ «primesBetween»(m, n) ⇒ m + 1 ≤ p",
				a.ForEach(func(_ *Expr[Nat]) Action {
					return ByArith()
				}))
			productAtLeast := a.Have(
				"so their product is at least (m + 1)ᵏ",
				"(m + 1) ^ card(«primesBetween»(m, n)) ≤ Π_{p∈«primesBetween»(m, n)} p",
				By(
					finiteWindow,
					pastRoot,
					nat_product.NatProductLowerBound.At(window, a.TermAs[Fun[Nat, Nat]]("λp:num. p"), next)))
			productAtMost := a.Have(
				"and at most 4ⁿ, a factor of primorial(n) = primorial(m)·Π",
				"Π_{p∈«primesBetween»(m, n)} p ≤ 4 ^ n",
				ByArith(
					ordered,
					PrimorialPositive.At(m),
					PrimorialSplit.At(m, n),
					PrimorialBound.At(n),
					nat_order.LessEqMulRightCancel.At(a.Ctx().Nat(1), a.TermAs[Nat]("primorial(m)"), primeProduct)))
			nextPower := a.TermAs[Nat]("(m + 1) ^ card(«primesBetween»(m, n))")
			highPrimes := a.Have(
				"the primes in ⟬m, n⟧ contribute nᵏ ≤ ((m + 1)²)ᵏ ≤ (4ⁿ)²",
				"n ^ card(«primesBetween»(m, n)) ≤ 4 ^ n * 4 ^ n",
				nat_order.OrderCalc(a.Ctx()).CalcLeibniz(a.TermAs[Nat]("n ^ card(«primesBetween»(m, n))"),
					LeLeg(
						a.TermAs[Nat]("((m + 1) * (m + 1)) ^ card(«primesBetween»(m, n))"),
						"n < (m + 1)²",
						ByArith(above, nat_order.PowBaseMonotone.At(n, a.TermAs[Nat]("(m + 1) * (m + 1)"), width))),
					EqLeg(
						a.TermAs[Nat]("(m + 1) ^ card(«primesBetween»(m, n)) * (m + 1) ^ card(«primesBetween»(m, n))"),
						"((m + 1)²)ᵏ = (m + 1)ᵏ·(m + 1)ᵏ",
						By(nat_arith.MulPowDistrib.At(next, next, width))),
					LeLeg(
						a.TermAs[Nat]("4 ^ n * 4 ^ n"),
						"(m + 1)ᵏ ≤ Π ≤ 4ⁿ",
						ByArith(
							productAtLeast,
							productAtMost,
							nat_order.LessEqMul2.At(nextPower, bound, nextPower, bound)))))
			a.Show(
				"n^π(n) = n^π(m)·nᵏ ≤ 4ⁿ·(4ⁿ·4ⁿ) = 64ⁿ",
				nat_order.OrderCalc(a.Ctx()).CalcLeibniz(a.TermAs[Nat]("n ^ prime_counting(n)"),
					EqLeg(
						a.TermAs[Nat]("n ^ prime_counting(m) * n ^ card(«primesBetween»(m, n))"),
						"π(n) is π(m) plus the number of primes in ⟬m, n⟧",
						ByArith(
							ordered,
							PrimeCountingSplit.At(m, n),
							nat_arith.PowAdd.At(n, a.TermAs[Nat]("prime_counting(m)"), width))),
					LeLeg(
						a.TermAs[Nat]("4 ^ n * (4 ^ n * 4 ^ n)"),
						"the primes up to m contribute at most 4ⁿ, those in ⟬m, n⟧ at most 4ⁿ·4ⁿ",
						ByArith(
							lowPrimes,
							highPrimes,
							nat_order.LessEqMul2.At(
								a.TermAs[Nat]("n ^ prime_counting(m)"),
								bound,
								a.TermAs[Nat]("n ^ card(«primesBetween»(m, n))"),
								a.TermAs[Nat]("4 ^ n * 4 ^ n")))),
					EqLeg(
						a.TermAs[Nat]("64 ^ n"),
						"4ⁿ·16ⁿ = 64ⁿ",
						ByArith(
							nat_arith.MulPowDistrib.At(a.Ctx().Nat(4), a.Ctx().Nat(16), n),
							nat_arith.MulPowDistrib.At(a.Ctx().Nat(4), a.Ctx().Nat(4), n)))))
		}),
})}

// ---------------------------------------------------------------------------
// Taking logarithms
// ---------------------------------------------------------------------------

// ChebyshevUpperBound — the upper Chebyshev bound: for n > 0, π(n)·log n is
// at most 5n. Take logarithms of n^π(n) ≤ 64ⁿ (ChebyshevUpperPower); the
// constant 6·log 2 is below 5, since exp(5/6) = exp(5/12)² ≥ (17/12)² > 2.
var ChebyshevUpperBound = chebyshevUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "ChebyshevUpperBound",
	Key:  "prop_e6d4518dad88d7d6",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"0 < n",
		},
		Conclusion: "&prime_counting(n) * log(&n) ≤ &5 * &n",
	},
		func(a *Argument, n *Expr[Nat], positive Fact) {
			count := a.TermAs[Nat]("prime_counting(n)")
			fiveTwelfths := a.TermAs[Real]("&5 / &12")
			logs := a.Have(
				"taking logarithms of n^π(n) ≤ 64ⁿ",
				"&prime_counting(n) * log(&n) ≤ &n * log(&64)",
				ByArith(
					positive,
					ChebyshevUpperPower.At(n),
					real_exp_log.LogPowerLessEq.At(n, a.Ctx().Nat(64), count, n)))
			logTwo := a.Have(
				"log 2 < 5/6: exp(5/6) = exp(5/12)², and exp(5/12) ≥ 1 + 5/12 with (17/12)² > 2",
				"log(&2) < &5 / &6",
				ByArith(
					real_exp_log.ExpLowerBound.At(fiveTwelfths),
					real_exp_log.ExpAdd.At(fiveTwelfths, fiveTwelfths),
					real_exp_log.ExpLog.At(a.TermAs[Real]("&2")),
					real_exp_log.ExpLessIff.At(a.TermAs[Real]("log(&2)"), a.TermAs[Real]("&5 / &12 + &5 / &12"))))
			a.Show(
				"so π(n)·log n ≤ n·log 64 = 6n·log 2 ≤ 5n",
				ByArith(
					logs,
					logTwo,
					real_exp_log.LogPow.At(a.TermAs[Real]("&2"), a.Ctx().Nat(6)),
					real_order_ring.LessEqMulLeft.At(
						a.TermAs[Real]("&n"), a.TermAs[Real]("log(&64)"), a.TermAs[Real]("&5"))))
		}),
})}

// ChebyshevBounds — Chebyshev's bounds: for n ≥ 2, π(n)·log n is at least half
// of n·log 2 and at most 5n. Take logarithms of 2ⁿ ≤ n^(2π(n))
// (ChebyshevLowerPower); the upper half is ChebyshevUpperBound.
var ChebyshevBounds = chebyshevBoundsThm{family.Add(registry.ProofEntry{
	Name: "ChebyshevBounds",
	Key:  "prop_a5331e91bbc45dbd",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"2 ≤ n",
		},
		Conclusion: "log(&2) / &2 * &n ≤ &prime_counting(n) * log(&n) ∧ " +
			"&prime_counting(n) * log(&n) ≤ &5 * &n",
	},
		func(a *Argument, n *Expr[Nat], large Fact) {
			count := a.TermAs[Nat]("prime_counting(n)")
			doubleCount := a.TermAs[Nat]("2 * prime_counting(n)")
			lowerLogs := a.Have(
				"taking logarithms of 2ⁿ ≤ n^(2π(n))",
				"&n * log(&2) ≤ &(2 * prime_counting(n)) * log(&n)",
				ByArith(
					large,
					ChebyshevLowerPower.At(n),
					real_exp_log.LogPowerLessEq.At(a.Ctx().Nat(2), n, n, doubleCount)))
			lower := a.Have(
				"so (log 2 / 2)·n ≤ π(n)·log n, 2π(n) read as 2·π(n)",
				"log(&2) / &2 * &n ≤ &prime_counting(n) * log(&n)",
				ByArith(
					lowerLogs,
					Scaled(a.TermAs[Real]("log(&n)"), real_construction.OfNumMul.At(a.Ctx().Nat(2), count))))
			a.Show(
				"the lower bound together with the upper one",
				ByArith(large, lower, ChebyshevUpperBound.At(n)))
		}),
})}
