// jacobi.go — the Jacobi symbol (a/n), the product over the primes p
// dividing n of (a/p) to the multiplicity of p in n, read through one
// observation: the product may be taken over ANY set of primes that holds
// the prime divisors of n. A prime of the larger set that does not divide
// n occurs in n to the power 0, so its factor is (a/p)⁰ = 1 and the product
// does not see it.
//
// Taken over no primes at all, that gives (a/1) = 1; taken over {p}, that
// (a/p) is the Legendre symbol at a prime p, which occurs in itself once.
// And it is what makes (a/n) multiplicative in n: the primes dividing m·n
// hold those of m and those of n, so the three symbols are products over
// one finite set, and the exponents add there because the multiplicities
// do. For odd n the symbol is multiplicative in a as well, with no change
// of index set at all: every prime of n is odd, and the Legendre symbol at
// an odd prime is multiplicative.

package quadratic_reciprocity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/int_num/quadratic_residue"
	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_product"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The symbol over any set of primes holding the prime divisors
// ---------------------------------------------------------------------------

// JacobiOverPrimes — (a/n) is the product of (a/p) to the multiplicity of p
// in n over any set s of primes holding the prime divisors of n: a prime of
// s that does not divide n occurs in n to the power 0, so its factor is 1.
var JacobiOverPrimes = jacobiOverPrimesThm{family.Add(registry.ProofEntry{
	Name: "JacobiOverPrimes",
	Key:  "prop_1a5b29a93c4241cc",
	Build: family.Theorem(Statement{
		Binders: "∀a:int. ∀n:num. ∀s:set(num).",
		Hypotheses: []string{
			"∀p:num. p ∈ s ⇒ nat_prime(p)",
			"«primeDivisors»(n) ⊆ s",
		},
		Conclusion: "jacobi_symbol(a, n) = Π_{p∈s} legendre_symbol(a, p) ^ nat_multiplicity(p, n)",
	}, func(arg *Argument, a *Expr[Int], n *Expr[Nat], s *Expr[Set[Nat]], primes, divisors Fact) {
		silent := arg.Have(
			"a prime of s that does not divide n contributes (a/p)⁰ = 1",
			"∀p:num. p ∈ s ∧ p ∉ «primeDivisors»(n) ⇒ legendre_symbol(a, p) ^ nat_multiplicity(p, n) = 1",
			By(primes, nat_multiplicity.MultiplicityOfNonDivisor, int_pow.PowClauses))
		arg.Show(
			"so the product over the prime divisors of n may be taken over s",
			Unfold(JacobiSymbolDef),
			By(silent, divisors, int_product.IntProductSuperset))
	}),
})}

// JacobiAtOne — (a/1) = 1: no prime divides 1, so the symbol is the product
// over no primes.
var JacobiAtOne = jacobiAtOneThm{family.Add(registry.ProofEntry{
	Name: "JacobiAtOne",
	Key:  "prop_46a45d6fa35daf8b",
	Build: family.Theorem("∀a:int. jacobi_symbol(a, 1) = 1",
		func(arg *Argument, a *Expr[Int]) {
			none := arg.Have(
				"no prime divides 1",
				"«primeDivisors»(1) ⊆ ∅",
				BySets(nat_divides.DividesOne, nat_prime.PrimeDef))
			arg.Show(
				"so (a/1) is the product over no primes, which is 1",
				By(
					none,
					JacobiOverPrimes.At(a, arg.Ctx().Nat(1), arg.TermAs[Set[Nat]]("∅")),
					set_basic.NotInEmpty,
					int_product.IntProductClauses))
		}),
})}

// JacobiOne — (1/n) = 1 for every n: at each prime p, (1/p) = 1, so every
// factor (1/p) to the multiplicity of p in n is 1, and the product over the
// primes dividing n is the product over no primes.
var JacobiOne = jacobiOneThm{family.Add(registry.ProofEntry{
	Name: "JacobiOne",
	Key:  "prop_73dc69fa1a58ff57",
	Build: family.Theorem("∀n:num. jacobi_symbol(1, n) = 1",
		func(arg *Argument, n *Expr[Nat]) {
			ones := arg.Have(
				"(1/p) = 1 at a prime p, which is not 1, so every factor of (1/n) is 1",
				"∀p:num. p ∈ «primeDivisors»(n) ⇒ legendre_symbol(1, p) ^ nat_multiplicity(p, n) = 1",
				By(nat_prime.PrimeDef, quadratic_residue.LegendreOne, int_pow.OnePow))
			arg.Show(
				"so (1/n) is a product of ones, which is the product over no primes",
				CalcEq(
					Leg(
						arg.TermAs[Int]("Π_{p∈«primeDivisors»(n)} legendre_symbol(1, p) ^ nat_multiplicity(p, n)"),
						"by definition",
						Cite(JacobiSymbolDef)),
					// ∅ is written at num: the index p takes its type from the set it
					// runs over, and ∅ alone names no element type.
					Leg(
						arg.TermAs[Int]("Π_{p∈∅⟨A:num⟩} legendre_symbol(1, p) ^ nat_multiplicity(p, n)"),
						"the factors at the primes of n are all 1",
						By(ones, int_product.IntProductSuperset, set_order.EmptySubset)),
					FinalLeg(
						"a product over no primes is 1",
						By(int_product.IntProductClauses))))
		}),
})}

// JacobiPrime — at a prime p the Jacobi symbol is the Legendre symbol: the
// only prime dividing p is p, which occurs in p once, so (a/p) is the
// product over {p} of its one factor (a/p)¹.
var JacobiPrime = jacobiPrimeThm{family.Add(registry.ProofEntry{
	Name: "JacobiPrime",
	Key:  "prop_7fcddd5fa2cf0598",
	Build: family.Theorem(Statement{
		Binders: "∀a:int. ∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "jacobi_symbol(a, p) = legendre_symbol(a, p)",
	}, func(arg *Argument, a *Expr[Int], p *Expr[Nat], prime Fact) {
		only := arg.Have(
			"the only prime dividing p is p",
			"«primeDivisors»(p) ⊆ {p}",
			BySets(prime, nat_prime.PrimeDividesPrime))
		arg.Show(
			"(a/p) is a product over {p}, whose one factor is (a/p) to the power 1",
			CalcEq(
				Leg(
					arg.TermAs[Int]("Π_{q∈{p}} legendre_symbol(a, q) ^ nat_multiplicity(q, p)"),
					"the symbol taken over the primes of {p}",
					By(prime, only, JacobiOverPrimes.At(a, p, arg.TermAs[Set[Nat]]("{p}")), set_basic.InSing)),
				Leg(
					arg.TermAs[Int]("legendre_symbol(a, p) ^ nat_multiplicity(p, p)"),
					"a product over one point is its one factor",
					Unfold(int_product.IntProductDef),
					By(monoidal.Sing, int_real_lift.MonoidalMul)),
				FinalLeg(
					"and p occurs in itself once",
					ByArith(prime, nat_multiplicity.MultiplicitySelf.At(p), nat_prime.PrimeAtLeastTwo.At(p)))))
	}),
})}

// ---------------------------------------------------------------------------
// Multiplicativity in each argument
// ---------------------------------------------------------------------------

// JacobiMulRight — the Jacobi symbol is multiplicative in its lower
// argument: (a/m·n) = (a/m)·(a/n) for nonzero m and n. The primes dividing
// m·n are finitely many and hold those of m and those of n, so all three
// symbols are products over that one set. There the multiplicity of p in m·n
// is the sum of its multiplicities in m and in n, so each factor of (a/m·n)
// is a factor of (a/m) times one of (a/n), and the product splits with its
// factors.
var JacobiMulRight = jacobiMulRightThm{family.Add(registry.ProofEntry{
	Name: "JacobiMulRight",
	Key:  "prop_4c6714fe8f6769e9",
	Build: family.Theorem(Statement{
		Binders: "∀a:int. ∀m n:num.",
		Hypotheses: []string{
			"m ≠ 0",
			"n ≠ 0",
		},
		Conclusion: "jacobi_symbol(a, m * n) = jacobi_symbol(a, m) * jacobi_symbol(a, n)",
	}, func(arg *Argument, a *Expr[Int], m, n *Expr[Nat], mNonzero, nNonzero Fact) {
		primeDivisors := arg.TermAs[Set[Nat]]("«primeDivisors»(m * n)")
		finite := arg.Have(
			"finitely many primes divide m·n, which is not 0",
			"finite(«primeDivisors»(m * n))",
			By(
				mNonzero,
				nNonzero,
				nat_prime.PrimeDivisorsFinite.At(arg.TermAs[Nat]("m * n")),
				nat_arith.MulEqZero.At(m, n)))
		divisors := arg.Have(
			"a prime dividing m, or dividing n, divides m·n",
			"«primeDivisors»(m) ⊆ «primeDivisors»(m * n) ∧ «primeDivisors»(n) ⊆ «primeDivisors»(m * n)",
			BySets(nat_divides.DividesMul, nat_arith.MulSym))
		exponents := arg.Have(
			"at a prime of m·n the exponents add, so the factor splits",
			Statement{
				Binders: "∀p:num.",
				Hypotheses: []string{
					"p ∈ «primeDivisors»(m * n)",
				},
				Conclusion: "legendre_symbol(a, p) ^ nat_multiplicity(p, m * n) = " +
					"legendre_symbol(a, p) ^ nat_multiplicity(p, m) * legendre_symbol(a, p) ^ nat_multiplicity(p, n)",
			},
			By(mNonzero, nNonzero, nat_multiplicity.MultiplicityMul, int_pow.PowAdd))
		arg.Show(
			"so (a/m·n) splits into (a/m)·(a/n), all three read over the primes of m·n",
			CalcEq(
				Leg(
					arg.TermAs[Int]("Π_{p∈«primeDivisors»(m * n)} legendre_symbol(a, p) ^ nat_multiplicity(p, m * n)"),
					"by definition",
					Cite(JacobiSymbolDef)),
				Leg(
					arg.TermAs[Int]("Π_{p∈«primeDivisors»(m * n)} legendre_symbol(a, p) ^ nat_multiplicity(p, m) * "+
						"legendre_symbol(a, p) ^ nat_multiplicity(p, n)"),
					"each factor splits",
					Unfold(int_product.IntProductDef),
					By(exponents, monoidal.Congruence, int_real_lift.MonoidalMul)),
				Leg(
					arg.TermAs[Int]("(Π_{p∈«primeDivisors»(m * n)} legendre_symbol(a, p) ^ nat_multiplicity(p, m)) * "+
						"(Π_{p∈«primeDivisors»(m * n)} legendre_symbol(a, p) ^ nat_multiplicity(p, n))"),
					"a product over a finite set of products is the product of the two products",
					Unfold(int_product.IntProductDef),
					By(finite, monoidal.Pointwise, int_real_lift.MonoidalMul)),
				FinalLeg(
					"which are (a/m) and (a/n), each taken over the primes of m·n, which hold the primes of m and of n",
					By(divisors, JacobiOverPrimes.At(a, m, primeDivisors), JacobiOverPrimes.At(a, n, primeDivisors)))))
	}),
})}

// JacobiMulLeft — for odd n the Jacobi symbol is multiplicative in its upper
// argument: (a·b/n) = (a/n)·(b/n). Every prime p dividing n is odd, so the
// Legendre symbol at p is multiplicative, and its power at the multiplicity
// of p in n splits with it; the three symbols are products over the primes
// of n, finitely many since n is not 0, and the product splits with its
// factors.
var JacobiMulLeft = jacobiMulLeftThm{family.Add(registry.ProofEntry{
	Name: "JacobiMulLeft",
	Key:  "prop_4855f8f8167f74e9",
	Build: family.Theorem(Statement{
		Binders: "∀a b:int. ∀n:num.",
		Hypotheses: []string{
			"nat_odd(n)",
		},
		Conclusion: "jacobi_symbol(a * b, n) = jacobi_symbol(a, n) * jacobi_symbol(b, n)",
	}, func(arg *Argument, a, b *Expr[Int], n *Expr[Nat], odd Fact) {
		finite := arg.Have(
			"finitely many primes divide n, which is odd and so not 0",
			"finite(«primeDivisors»(n))",
			By(odd, nat_prime.PrimeDivisorsFinite.At(n), nat_parity.NatOdd))
		factors := arg.Have(
			"a prime dividing n is not 2, n being odd, so the factor at it splits",
			Statement{
				Binders: "∀p:num.",
				Hypotheses: []string{
					"p ∈ «primeDivisors»(n)",
				},
				Conclusion: "legendre_symbol(a * b, p) ^ nat_multiplicity(p, n) = " +
					"legendre_symbol(a, p) ^ nat_multiplicity(p, n) * legendre_symbol(b, p) ^ nat_multiplicity(p, n)",
			},
			Derive(func(c *Argument) {
				p := c.FixAs[Nat]("p")
				divides := c.Assume()
				c.Show(
					"(a·b/p) = (a/p)·(b/p) at a prime other than 2, and "+
						"a power of a product is the product of the powers",
					By(
						odd,
						divides,
						nat_parity.TwoNotDividesOdd.At(n),
						quadratic_residue.LegendreMul.At(a, b, p),
						int_pow.MulPow.At(
							c.TermAs[Int]("legendre_symbol(a, p)"),
							c.TermAs[Int]("legendre_symbol(b, p)"),
							c.TermAs[Nat]("nat_multiplicity(p, n)"))))
			}))
		arg.Show(
			"so (a·b/n) splits into (a/n)·(b/n), all three products over the primes of n",
			CalcEq(
				Leg(
					arg.TermAs[Int]("Π_{p∈«primeDivisors»(n)} legendre_symbol(a * b, p) ^ nat_multiplicity(p, n)"),
					"by definition",
					Cite(JacobiSymbolDef)),
				Leg(
					arg.TermAs[Int]("Π_{p∈«primeDivisors»(n)} legendre_symbol(a, p) ^ nat_multiplicity(p, n) * "+
						"legendre_symbol(b, p) ^ nat_multiplicity(p, n)"),
					"each factor splits",
					Unfold(int_product.IntProductDef),
					By(factors, monoidal.Congruence, int_real_lift.MonoidalMul)),
				Leg(
					arg.TermAs[Int]("(Π_{p∈«primeDivisors»(n)} legendre_symbol(a, p) ^ nat_multiplicity(p, n)) * "+
						"(Π_{p∈«primeDivisors»(n)} legendre_symbol(b, p) ^ nat_multiplicity(p, n))"),
					"a product over a finite set of products is the product of the two products",
					Unfold(int_product.IntProductDef),
					By(finite, monoidal.Pointwise, int_real_lift.MonoidalMul)),
				FinalLeg(
					"which are (a/n) and (b/n) by definition",
					By(JacobiSymbolDef.At(a, n), JacobiSymbolDef.At(b, n)))))
	}),
})}
