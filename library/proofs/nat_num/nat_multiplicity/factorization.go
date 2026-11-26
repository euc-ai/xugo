// factorization.go — a number is the product of its prime powers over the
// primes up to any bound on its prime divisors, and a product of distinct
// primes each dividing a number divides it.

package nat_multiplicity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// PrimeFactorizationProduct — a nonzero number whose prime divisors are at
// most N is the product, over the primes up to N, of each prime to its
// multiplicity. By induction on N, for every such number at once. At 0 there
// is no prime, so the number has no prime divisor and is 1. At N + 1, if
// N + 1 is not prime nothing changes; if it is a prime q, the number is
// q^v·c with q ∤ c, the prime divisors of c are at most N, and below q the
// multiplicities in n and in c agree, so the induction factors c and the new
// factor is q^v.
var PrimeFactorizationProduct = primeFactorizationProductThm{family.Add(registry.ProofEntry{
	Name: "PrimeFactorizationProduct",
	Key:  "prop_90e36978ac1f522",
	Build: family.Theorem(Statement{
		Binders: "∀N n:num.",
		Hypotheses: []string{
			"n ≠ 0",
			"∀p:num. nat_prime(p) ∧ p ∣ n ⇒ p ≤ N",
		},
		Conclusion: "n = Π_{p∈«primes»(N)} p ^ nat_multiplicity(p, n)",
		Abbrev: Abbrev{
			{Name: "primes", Text: "λm:num. {p:num | p ≤ m ∧ nat_prime(p)}"},
		},
	},
		func(a *Argument) {
			a.Induct("N")
			a.Base(
				"no prime is at most 0, so n has no prime divisor and is 1, the empty product",
				func(b *Argument) {
					n := b.FixAs[Nat]("n")
					given := b.Conjuncts(
						b.Assume(),
						"n is not 0",
						"its prime divisors are at most 0")
					nonzero, bounded := given[0], given[1]
					noPrime := b.Have(
						"every prime is at least 2",
						"∀p:num. ¬(p ≤ 0 ∧ nat_prime(p))",
						b.ForEach(func(p *Expr[Nat]) Action {
							return ByArith(nat_prime.PrimeAtLeastTwo.At(p))
						}))
					none := b.Have(
						"so the primes up to 0 are none",
						"«primes»(0) = ∅",
						BySets(noPrime))
					one := b.Have(
						"n is 1: past 1 it would have a prime divisor, which is at least 2",
						"n = 1",
						Derive(func(c *Argument) {
							notOne := c.SupposeNot()
							q, divides := c.ObtainAs[Nat](
								"a number past 1 has a prime divisor q",
								"∃q:num. nat_prime(q) ∧ q ∣ n",
								ByArith(nonzero, notOne, nat_prime.PrimeFactor.At(n)))
							c.Show(
								"q would be at most 0",
								ByArith(bounded.At(q), divides, nat_prime.PrimeAtLeastTwo.At(q)))
						}))
					b.Show(
						"and the product over ∅ is 1",
						By(none, one, nat_product.NatProductClauses))
				})
			a.Step(
				"from N to N + 1: the primes gain N + 1 exactly when it is prime",
				func(b *Argument, ih Fact) {
					n := b.FixAs[Nat]("n")
					given := b.Conjuncts(
						b.Assume(),
						"n is not 0",
						"its prime divisors are at most N + 1")
					nonzero, bounded := given[0], given[1]
					q := b.TermAs[Nat]("suc(N)")
					upTo := b.Have(
						"a number up to N + 1 is one up to N, or N + 1 itself",
						"∀p:num. p ≤ suc(N) ⇔ p ≤ N ∨ p = suc(N)",
						ByArith())
					b.Cases(b.TermAs[Bool]("nat_prime(suc(N))"))
					b.Otherwise(
						"N + 1 is not prime: the primes, and the prime divisors of n, stay at most N",
						func(c *Argument, composite Fact) {
							same := c.Have(
								"the primes up to N + 1 are those up to N",
								"«primes»(suc(N)) = «primes»(N)",
								BySets(composite, upTo))
							below := c.Have(
								"a prime divisor of n is at most N + 1, and not N + 1",
								"∀p:num. nat_prime(p) ∧ p ∣ n ⇒ p ≤ N",
								By(Normalized, composite, upTo, bounded))
							c.Show(
								"the factorization up to N is the one up to N + 1",
								By(ih.At(n), nonzero, below, same))
						})
					b.When(
						"N + 1 is a prime q: split off q to its multiplicity",
						func(c *Argument, prime Fact) {
							atLeastTwo := c.Have(
								"a prime is at least 2",
								"2 ≤ suc(N)",
								By(prime, nat_prime.PrimeAtLeastTwo.At(q)))
							cofactor, split := c.UnpackAs[Nat](
								GroupPremises(atLeastTwo, nonzero, MultiplicityCofactor.At(q, n)),
								"c")
							parts := c.Conjuncts(
								split,
								"n = q^v·c",
								"q does not divide c")
							factored, coprime := parts[0], parts[1]
							power := c.TermAs[Nat]("suc(N) ^ nat_multiplicity(suc(N), n)")
							cNonzero := c.Have(
								"c is not 0, as n is not",
								"c ≠ 0",
								By(nonzero, factored, nat_arith.MulZero))
							cBounded := c.Have(
								"a prime divisor of c divides n and is not q, so it is at most N",
								"∀p:num. nat_prime(p) ∧ p ∣ c ⇒ p ≤ N",
								Derive(func(d *Argument) {
									p := d.FixAs[Nat]("p")
									d.Show(
										"p divides c, which divides n = q^v·c",
										By(
											Normalized,
											coprime,
											upTo.At(p),
											bounded.At(p),
											factored,
											nat_divides.DividesTrans.At(p, cofactor, n),
											nat_divides.DividesOwnMultiple.At(cofactor, power)))
								}))
							agree := c.Have(
								"below q the prime powers in n and in c agree",
								"∀p:num. p ∈ «primes»(N) ⇒ p ^ nat_multiplicity(p, n) = p ^ nat_multiplicity(p, c)",
								Derive(func(d *Argument) {
									p := d.FixAs[Nat]("p")
									member := d.Conjuncts(
										d.Assume(),
										"p is at most N",
										"p is prime")
									below, primeP := member[0], member[1]
									notDivides := d.Have(
										"p is a prime other than q, so it does not divide a power of q",
										"¬(p ∣ suc(N) ^ nat_multiplicity(suc(N), n))",
										ByArith(
											primeP,
											prime,
											below,
											nat_prime.PrimeDividesPower.At(p, q, d.TermAs[Nat]("nat_multiplicity(suc(N), n)")),
											nat_prime.PrimeDividesPrime.At(p, q)))
									d.Show(
										"so p does not divide q^v, and its multiplicity in n = q^v·c is the one in c",
										ByArith(
											primeP,
											prime,
											cNonzero,
											notDivides,
											factored,
											nat_prime.PrimeAtLeastTwo.At(p),
											nat_prime.PrimeAtLeastTwo.At(q),
											nat_arith.PowEqZero.At(q, d.TermAs[Nat]("nat_multiplicity(suc(N), n)")),
											nat_divides.OneDivides.At(power),
											nat_arith.NatPow,
											MultiplicityUnique.At(p, power, d.TermAs[Nat]("0")),
											MultiplicityMul.At(p, power, cofactor)))
								}))
							congruent := c.Have(
								"so the products over the primes up to N agree",
								"Π_{p∈«primes»(N)} p ^ nat_multiplicity(p, n) = Π_{p∈«primes»(N)} p ^ nat_multiplicity(p, c)",
								Simp(Fwd(nat_product.NatProductDef)),
								By(agree, monoidal.Congruence, nat_product.MonoidalNatMul))
							rest := c.Have(
								"and the induction factors c",
								"Π_{p∈«primes»(N)} p ^ nat_multiplicity(p, n) = c",
								By(ih.At(cofactor), cNonzero, cBounded, congruent))
							grown := c.Have(
								"the primes up to N + 1 are q and those up to N",
								"«primes»(suc(N)) = insert(suc(N), «primes»(N))",
								BySets(prime, upTo))
							fresh := c.Have(
								"those are finitely many, and q is not among them",
								"finite(«primes»(N)) ∧ suc(N) ∉ «primes»(N)",
								ByArith(
									finite_set.FiniteRestrict.At(
										c.TermAs[Set[Nat]]("{x:num | x ≤ N}"), c.TermAs[Set[Nat]]("nat_prime")),
									num_segment.FiniteBelow))
							peeled := c.Have(
								"the product over insert(q, …) takes the one new factor q^v",
								"Π_{p∈insert(suc(N), «primes»(N))} p ^ nat_multiplicity(p, n) = "+
									"suc(N) ^ nat_multiplicity(suc(N), n) * Π_{p∈«primes»(N)} p ^ nat_multiplicity(p, n)",
								By(fresh, nat_product.NatProductClauses))
							c.Show(
								"n = q^v·c is the product up to N + 1",
								By(grown, factored, rest, peeled))
						})
				})
		}),
})}

// ProductOfPrimesDivides — the product of a finite set of primes each of which
// divides N divides N. Induction on the set, for every N at once: a fresh prime
// x divides N = x·c, and every other prime of the set divides N without
// dividing x, so it divides the cofactor c, which the product of the rest then
// divides.
var ProductOfPrimesDivides = productOfPrimesDividesThm{family.Add(registry.ProofEntry{
	Name: "ProductOfPrimesDivides",
	Key:  "prop_d5ac66d2c80d9307",
	Build: family.Theorem(Statement{
		Binders: "∀s:set(num). ∀N:num.",
		Hypotheses: []string{
			"finite(s)",
			"∀p:num. p ∈ s ⇒ nat_prime(p) ∧ p ∣ N",
		},
		Conclusion: "Π_{p∈s} p ∣ N",
	},
		func(a *Argument, s *Expr[Set[Nat]], N *Expr[Nat], finite, divisors Fact) {
			// The property carried along the induction: the product over t
			// divides every number all of t's members are prime divisors of.
			dividesEach := a.TermAs[Set[Set[Nat]]](
				"λt:set(num). ∀k:num. (∀p:num. p ∈ t ⇒ nat_prime(p) ∧ p ∣ k) ⇒ Π_{p∈t} p ∣ k")
			a.Show(
				"by induction on the finite set s, adding one fresh prime at a time",
				ByInduction(finite_set.FiniteInductFresh.At(dividesEach, s), finite, divisors,
					Case(
						"the product over ∅ is 1, which divides every number",
						By(nat_product.NatProductClauses, nat_divides.OneDivides)),
					Case(
						"a fresh prime x times the product over t divides "+
							"k: x divides k = x·c, and the primes of t divide c",
						Derive(func(b *Argument) {
							x := b.FixAs[Nat]()
							b.FixAs[Set[Nat]]("t") // the set the fresh prime x joins
							step := b.Conjuncts(
								b.Assume(),
								"the product over t divides each number its members divide",
								"x is not in t",
								"t is finite")
							inductive, fresh, finiteT := step[0], step[1], step[2]
							k := b.FixAs[Nat]("k")
							divides := b.Assume()
							head := b.Have(
								"x is one of the primes, so a prime dividing k",
								"nat_prime(x) ∧ x ∣ k",
								BySets(divides))
							c, cofactor := b.ObtainAs[Nat](
								"so k is x times a cofactor c",
								"∃c:num. k = x * c",
								By(head, nat_divides.DividesFactor.At(x, k)))
							rest := b.Have(
								"a prime q of t divides k = x·c and is not x, so it divides c",
								"∀q:num. q ∈ t ⇒ nat_prime(q) ∧ q ∣ c",
								Derive(func(d *Argument) {
									q := d.FixAs[Nat]()
									inT := d.Assume()
									primeDivisor := d.Have(
										"q is in insert(x, t), so a prime dividing k",
										"nat_prime(q) ∧ q ∣ k",
										BySets(divides, inT))
									d.Show(
										"q is not the prime x, so does not divide it, and divides c",
										By(
											fresh,
											inT,
											cofactor,
											head,
											primeDivisor,
											nat_prime.EuclidLemma.At(q, x, c),
											nat_prime.PrimeDividesPrime.At(q, x)))
								}))
							inner := b.Have(
								"so the product over t divides c",
								"Π_{p∈t} p ∣ c",
								By(inductive.At(c), rest))
							_, quotient := b.ObtainAs[Nat](
								"c is that product times some y",
								"∃y:num. c = (Π_{p∈t} p) * y",
								By(inner, nat_divides.DividesFactor.At(b.TermAs[Nat]("Π_{p∈t} p"), c)))
							scaled := b.Have(
								"so x times the product over t divides x·c = k",
								"x * (Π_{p∈t} p) ∣ k",
								By(cofactor, quotient, nat_divides.DividesFactor, nat_arith.MulAssoc))
							b.Show(
								"and x times the product over t is the product over insert(x, t)",
								By(finiteT, fresh, scaled, nat_product.NatProductClauses))
						}))))
		}),
})}
