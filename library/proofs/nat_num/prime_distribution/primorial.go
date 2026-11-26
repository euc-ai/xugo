// primorial.go — π and the primorial. The primes up to n are finitely many
// and fall apart at any cut m ≤ n into those up to m and those in ⟬m, n⟧. π
// counts them: at most n of them, never fewer as n grows, and at most m + 1 up
// to 2m. The primorial multiplies them: it is at least 1, and at most 4ⁿ by
// Erdős's argument through C(2m + 1, m).

package prime_distribution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_product"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_multiplicity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The primes up to n
// ---------------------------------------------------------------------------

// PrimesFinite — only finitely many primes are at most n: they lie among the
// numbers up to n, which are finitely many.
var PrimesFinite = primesFiniteThm{family.Add(registry.ProofEntry{
	Name: "PrimesFinite",
	Key:  "prop_ea5ef109f51a62fb",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Conclusion: "finite(«primes»(n))",
	},
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"the primes up to n are the numbers up to n that are prime",
				By(
					finite_set.FiniteRestrict.At(
						a.TermAs[Set[Nat]]("{x:num | x ≤ n}"), a.TermAs[Set[Nat]]("nat_prime")),
					num_segment.FiniteBelow))
		}),
})}

// PrimesSplit — cut at m ≤ n, the primes up to n are those up to m together
// with those in ⟬m, n⟧: every number up to n is at most m or past it, and none
// is both. Both parts are finite, as the primes up to n are.
var PrimesSplit = primesSplitThm{family.Add(registry.ProofEntry{
	Name: "PrimesSplit",
	Key:  "prop_ce9c1d441a516996",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "«primes»(n) = «primes»(m) ∪ «primesBetween»(m, n) ∧ " +
			"disjoint(«primes»(m), «primesBetween»(m, n)) ∧ " +
			"finite(«primes»(m)) ∧ " +
			"finite(«primesBetween»(m, n))",
	},
		func(a *Argument, m, n *Expr[Nat], ordered Fact) {
			cut := a.Have(
				"a number up to n is at most m, or past m and at most n",
				"∀p:num. p ≤ n ⇔ p ≤ m ∨ m < p ∧ p ≤ n",
				ByArith(ordered))
			parts := a.Have(
				"so the primes up to n are those up to m together with those in ⟬m, n⟧",
				"«primes»(n) = «primes»(m) ∪ «primesBetween»(m, n)",
				BySets(cut))
			apart := a.Have(
				"no number is both at most m and past m",
				"disjoint(«primes»(m), «primesBetween»(m, n))",
				BySets(nat_order.NotLessEq))
			finite := PrimesFinite.At(n)
			a.Show(
				"so each of the two parts is finite",
				By(parts, apart, finite, finite_set.FiniteUnion))
		}),
})}

// ---------------------------------------------------------------------------
// Counting the primes
// ---------------------------------------------------------------------------

// PrimeCountingLessEqSelf — at most n primes are at most n: each of them is
// at least 2, so they lie in 1 .. n, which has n points.
var PrimeCountingLessEqSelf = primeCountingLessEqSelfThm{family.Add(registry.ProofEntry{
	Name: "PrimeCountingLessEqSelf",
	Key:  "prop_e99ec8a509a2d3a",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Conclusion: "prime_counting(n) ≤ n",
	},
		func(a *Argument, n *Expr[Nat]) {
			pointwise := a.Have(
				"a prime up to n is at least 2, so it lies in 1 .. n",
				"∀p:num. p ≤ n ∧ nat_prime(p) ⇒ p ∈ 1 .. n",
				a.ForEach(func(p *Expr[Nat]) Action {
					return ByArith(nat_prime.PrimeAtLeastTwo.At(p))
				}))
			inside := a.Have(
				"so the primes up to n are among 1 .. n",
				"«primes»(n) ⊆ 1 .. n",
				BySets(pointwise))
			a.Show(
				"and 1 .. n has n points",
				By(
					inside,
					cardinality.CardSubset.At(a.TermAs[Set[Nat]]("«primes»(n)"), a.TermAs[Set[Nat]]("1 .. n")),
					num_segment.Finite.At(a.Ctx().Nat(1), n),
					num_segment.CardFromOne.At(n),
					PrimeCountingDef.At(n)))
		}),
})}

// PrimeCountingMonotone — π grows with its argument: the primes up to m are
// among the finitely many primes up to n.
var PrimeCountingMonotone = primeCountingMonotoneThm{family.Add(registry.ProofEntry{
	Name: "PrimeCountingMonotone",
	Key:  "prop_9a05970f4e6775ef",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "prime_counting(m) ≤ prime_counting(n)",
	},
		func(a *Argument, m, n *Expr[Nat], ordered Fact) {
			inside := a.Have(
				"a prime up to m is a prime up to n",
				"«primes»(m) ⊆ «primes»(n)",
				BySets(ordered, nat_order.LessEqTrans))
			finite := PrimesFinite.At(n)
			a.Show(
				"a subset of a finite set has no more points",
				ByArith(
					inside,
					finite,
					cardinality.CardSubset.At(a.TermAs[Set[Nat]]("«primes»(m)"), a.TermAs[Set[Nat]]("«primes»(n)")),
					PrimeCountingDef.At(m),
					PrimeCountingDef.At(n)))
		}),
})}

// PrimeCountingSplit — cut at m ≤ n, π(n) is π(m) plus the number of primes in
// ⟬m, n⟧: the primes up to n fall apart into those up to m and those past it,
// and the count of a disjoint union of finite sets is the sum of the counts.
var PrimeCountingSplit = primeCountingSplitThm{family.Add(registry.ProofEntry{
	Name: "PrimeCountingSplit",
	Key:  "prop_8428fed1d94d760a",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "prime_counting(n) = prime_counting(m) + card(«primesBetween»(m, n))",
	},
		func(a *Argument, m, n *Expr[Nat], ordered Fact) {
			split := a.Conjuncts(
				GroupPremises(ordered, PrimesSplit.At(m, n)),
				"the primes up to n are those up to m together with those in ⟬m, n⟧",
				"the two parts are disjoint",
				"only finitely many primes are at most m",
				"and only finitely many lie in ⟬m, n⟧")
			parts, apart, finiteLow, finiteHigh := split[0], split[1], split[2], split[3]
			a.Show(
				"the count of the disjoint union is the sum of the counts",
				ByArith(
					parts,
					apart,
					set_basic.DisjointDef,
					finiteLow,
					finiteHigh,
					cardinality.CardUnion.At(
						a.TermAs[Set[Nat]]("«primes»(m)"), a.TermAs[Set[Nat]]("«primesBetween»(m, n)")),
					PrimeCountingDef.At(m),
					PrimeCountingDef.At(n)))
		}),
})}

// PrimeCountingDoubleBound — at most m + 1 primes are at most 2m: besides 2,
// every one of them is odd, 2t − 1 for some t in 1 .. m, and an image of
// 1 .. m has at most m points.
var PrimeCountingDoubleBound = primeCountingDoubleBoundThm{family.Add(registry.ProofEntry{
	Name: "PrimeCountingDoubleBound",
	Key:  "prop_a6cdb1b2a73c2fca",
	Build: family.Theorem(
		"∀m:num. prime_counting(2 * m) ≤ m + 1",
		func(a *Argument, m *Expr[Nat]) {
			a.Do(Unfold(PrimeCountingDef))
			odd := a.Have(
				"an odd prime p ≤ 2m is 2t − 1 with t = ⌊p/2⌋ + 1 in 1 .. m",
				"∀p:num. p ≤ 2 * m ∧ nat_prime(p) ∧ p ≠ 2 ⇒ p = 2 * (div(p, 2) + 1) - 1 ∧ div(p, 2) + 1 ∈ 1 .. m",
				Derive(func(b *Argument) {
					p := b.FixAs[Nat]("p")
					b.Show(
						"a prime other than 2 is odd, so p = 2⌊p/2⌋ + 1 < 2m",
						ByArith(
							nat_prime.PrimeOddUnlessTwo.At(p),
							nat_parity.OddIffModTwoOne.At(p),
							nat_div_mod.Division.At(p, b.Ctx().Nat(2))))
				}))
			odds := a.TermAs[Set[Nat]]("image(λt:num. 2 * t - 1, 1 .. m)")
			inside := a.Have(
				"so the primes up to 2m are 2 and some of the odd numbers 2t − 1 with t in 1 .. m",
				"«primes»(2 * m) ⊆ insert(2, image(λt:num. 2 * t - 1, 1 .. m))",
				BySets(odd))
			a.Show(
				"there are at most m odd numbers 2t − 1 with t in 1 .. m, and 2 is one more",
				ByArith(
					inside,
					cardinality.BoundedCountOfImage.At(
						a.TermAs[Fun[Nat, Nat]]("λt:num. 2 * t - 1"),
						a.TermAs[Set[Nat]]("1 .. m"),
						m),
					num_segment.Finite.At(a.Ctx().Nat(1), m),
					num_segment.CardFromOne.At(m),
					cardinality.InsertCountsAtMostOneMore.At(odds, a.Ctx().Nat(2), m),
					cardinality.BoundedCountOfSubset.At(
						a.TermAs[Set[Nat]]("«primes»(2 * m)"),
						a.TermAs[Set[Nat]]("insert(2, image(λt:num. 2 * t - 1, 1 .. m))"),
						a.TermAs[Nat]("suc(m)"))))
		}),
})}

// ---------------------------------------------------------------------------
// The primorial: its recursion, its split at a cut, and that it is at least 1
// ---------------------------------------------------------------------------

// PrimorialClauses — the primorial starts at 1 and takes the factor n + 1
// exactly when n + 1 is prime: the primes up to n + 1 are those up to n, with
// n + 1 among them when it is prime, and a product over a finite set takes one
// more factor for one more point.
var PrimorialClauses = primorialClausesThm{family.Add(registry.ProofEntry{
	Name: "PrimorialClauses",
	Key:  "prop_cb3609d4982be501",
	Build: family.Theorem(
		"primorial(0) = 1 ∧ "+
			"(∀n:num. primorial(n + 1) = COND(nat_prime(n + 1), (n + 1) * primorial(n), primorial(n)))",
		func(a *Argument) {
			a.Do(SplitConj(
				Case(
					"no prime is at most 0, so primorial(0) is the empty product",
					Derive(func(b *Argument) {
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
						b.Show(
							"and the product over ∅ is 1",
							Simp(Fwd(PrimorialDef)),
							none.Rw(),
							Simp(Fwd(nat_product.NatProductClauses)),
							Refl())
					})),
				Case(
					"n + 1 joins the product exactly when it is prime",
					Derive(func(b *Argument) {
						n := b.FixAs[Nat]("n")
						oneMore := b.Have(
							"a number up to n + 1 is one up to n, or n + 1 itself",
							"∀p:num. p ≤ n + 1 ⇔ p ≤ n ∨ p = n + 1",
							ByArith())
						b.Cases(b.TermAs[Bool]("nat_prime(n + 1)"))
						b.When(
							"n + 1 is prime: the product takes the one new factor n + 1",
							func(c *Argument, prime Fact) {
								grown := c.Have(
									"the primes up to n + 1 are those up to n, and n + 1 besides",
									"«primes»(n + 1) = insert(n + 1, «primes»(n))",
									BySets(prime, oneMore))
								c.Have(
									"only finitely many primes are at most n",
									"finite(«primes»(n))",
									By(PrimesFinite.At(n)))
								c.Have(
									"and n + 1 is not one of them",
									"n + 1 ∉ «primes»(n)",
									ByArith())
								c.Show(
									"the product over insert(n + 1, …) is n + 1 times the product "+
										"over the rest, the rest being finite and n + 1 new to it",
									Simp(Fwd(PrimorialDef)),
									grown.Rw(),
									Simp(Fwd(nat_product.NatProductClauses)),
									Refl())
							})
						b.Otherwise(
							"n + 1 is not prime: the product is unchanged",
							func(c *Argument, composite Fact) {
								same := c.Have(
									"the primes up to n + 1 are those up to n",
									"«primes»(n + 1) = «primes»(n)",
									BySets(composite, oneMore))
								c.Show(
									"so the two products are over one set",
									Simp(Fwd(PrimorialDef)),
									By(same))
							})
					})),
			))
		}),
})}

// PrimorialSplit — cut at m ≤ n, the primorial of n is the primorial of m
// times the product of the primes in ⟬m, n⟧: the primes up to n fall apart
// into those up to m and those past it, and a product over two disjoint finite
// sets is the product of the two products.
var PrimorialSplit = primorialSplitThm{family.Add(registry.ProofEntry{
	Name: "PrimorialSplit",
	Key:  "prop_d18a5a92ef4250be",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"m ≤ n",
		},
		Conclusion: "primorial(n) = primorial(m) * Π_{p∈«primesBetween»(m, n)} p",
	},
		func(a *Argument, m, n *Expr[Nat], ordered Fact) {
			split := a.Conjuncts(
				GroupPremises(ordered, PrimesSplit.At(m, n)),
				"the primes up to n are those up to m together with those in ⟬m, n⟧",
				"the two parts are disjoint",
				"only finitely many primes are at most m",
				"and only finitely many lie in ⟬m, n⟧")
			parts, apart, finiteLow, finiteHigh := split[0], split[1], split[2], split[3]
			product := a.Have(
				"a product over two disjoint finite sets is the product of the two products",
				"Π_{p∈«primes»(m) ∪ «primesBetween»(m, n)} p = "+
					"(Π_{p∈«primes»(m)} p) * Π_{p∈«primesBetween»(m, n)} p",
				Simp(Fwd(nat_product.NatProductDef)),
				By(monoidal.Union, nat_product.MonoidalNatMul, finiteLow, finiteHigh, apart))
			a.Show(
				"the first product is primorial(m)",
				By(PrimorialDef, parts, product))
		}),
})}

// PrimorialPositive — the primorial is at least 1: a product of primes, each
// at least 1, is at least the product of ones.
var PrimorialPositive = primorialPositiveThm{family.Add(registry.ProofEntry{
	Name: "PrimorialPositive",
	Key:  "prop_78aee50f56e41596",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Conclusion: "1 ≤ primorial(n)",
	},
		func(a *Argument, n *Expr[Nat]) {
			primes := a.TermAs[Set[Nat]]("«primes»(n)")
			finite := PrimesFinite.At(n)
			atLeastOne := a.Have(
				"every prime is at least 1",
				"∀p:num. p ∈ «primes»(n) ⇒ 1 ≤ p",
				a.ForEach(func(p *Expr[Nat]) Action {
					return ByArith(nat_prime.PrimeAtLeastTwo.At(p))
				}))
			a.Show(
				"so the product of the primes is at least 1 to their number, 1",
				ByArith(
					finite,
					atLeastOne,
					PrimorialDef.At(n),
					nat_product.NatProductLowerBound.At(primes, a.TermAs[Fun[Nat, Nat]]("λp:num. p"), a.Ctx().Nat(1)),
					nat_arith.OnePow.At(a.TermAs[Nat]("card(«primes»(n))"))))
		}),
})}

// ---------------------------------------------------------------------------
// The bound by 4ⁿ
// ---------------------------------------------------------------------------

// PrimorialBound — the product of the primes up to n is at most 4^n. Strong
// induction on n. The primorial changes only at primes, so at a number that is
// not prime the bound at n − 1 carries over, and at 2 it is twice the
// primorial of 1. At an odd prime n = 2m + 1 (Erdős) the primes up to n are
// those up to m + 1, whose product is at most 4^(m + 1) by induction, and those
// in ⟬m + 1, 2m + 1⟧, each of which divides binomial(2m + 1, m) ≤ 4^m.
var PrimorialBound = primorialBoundThm{family.Add(registry.ProofEntry{
	Name: "PrimorialBound",
	Key:  "prop_be80f7f0ddbb4817",
	Build: family.Theorem(
		"∀n:num. primorial(n) ≤ 4 ^ n",
		func(a *Argument) {
			a.Show(
				"by strong induction on n",
				ByInduction(nat_order.StrongInduction,
					Case(
						"granted the bound below n, it holds at n",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]()
							below := b.Assume()
							positive := b.Unless(
								b.TermAs[Bool]("n = 0"),
								"primorial(0) = 1 = 4^0",
								Given(func(c *Argument, isZero Fact) {
									c.Do(ByArith(isZero, PrimorialClauses))
								}))
							k, predecessor := b.ObtainAs[Nat](
								"n is past 0, the successor of some k",
								"∃k:num. n = k + 1",
								Witness(b.TermAs[Nat]("n - 1")),
								ByArith(positive))
							grows := b.Have(
								"the primorial takes the factor n at n exactly when n is prime",
								"primorial(n) = COND(nat_prime(n), n * primorial(k), primorial(k))",
								ByArith(predecessor, PrimorialClauses))
							b.Cases(b.TermAs[Bool]("nat_prime(n)"))
							b.Otherwise(
								"n is not prime: primorial(n) = primorial(k) ≤ 4^k ≤ 4^n",
								func(c *Argument, composite Fact) {
									c.Show(
										"the bound at k < n carries over",
										ByArith(
											composite,
											below.At(k),
											predecessor,
											grows,
											nat_arith.PowAdd.At(c.Ctx().Nat(4), k, c.Ctx().Nat(1))))
								})
							b.When(
								"n is prime",
								func(c *Argument, prime Fact) {
									notTwo := c.Unless(
										c.TermAs[Bool]("n = 2"),
										"primorial(2) = 2·primorial(1) ≤ 2·4 ≤ 4^2",
										Given(func(d *Argument, isTwo Fact) {
											previous := d.Have(
												"the predecessor of 2 is 1",
												"k = 1",
												ByArith(isTwo, predecessor))
											d.Do(ByArith(prime, below.At(k), previous, isTwo, predecessor, grows))
										}))
									notEven := c.Have(
										"a prime other than 2 is odd, so 2 does not divide it",
										"¬(2 ∣ n)",
										By(prime, notTwo, nat_prime.PrimeOddUnlessTwo.At(n), nat_parity.TwoNotDividesOdd.At(n)))
									m, half := c.ObtainAs[Nat](
										"so n = 2m + 1, with m = div(n, 2)",
										"∃m:num. n = 2 * m + 1",
										Witness(c.TermAs[Nat]("div(n, 2)")),
										ByArith(notEven, nat_divides.DividesMod.At(c.Ctx().Nat(2), n), nat_div_mod.Division))
									next := c.TermAs[Nat]("m + 1")
									past := c.Have(
										"n is at least 3, so m + 1 < n",
										"m + 1 < n",
										ByArith(half, notTwo, prime, nat_prime.PrimeAtLeastTwo.At(n)))
									window := c.TermAs[Set[Nat]]("«primesBetween»(m + 1, n)")
									windowProduct := c.TermAs[Nat]("Π_{p∈«primesBetween»(m + 1, n)} p")
									middle := c.TermAs[Nat]("binomial(2 * m + 1, m)")
									divisors := c.Have(
										"every prime of ⟬m + 1, n⟧ divides binomial(2m + 1, m)",
										"∀q:num. q ∈ «primesBetween»(m + 1, n) ⇒ nat_prime(q) ∧ q ∣ binomial(2 * m + 1, m)",
										c.ForEach(func(q *Expr[Nat]) Action {
											return ByArith(half, nat_prime.PrimesBetweenDivideBinomial.At(m, q))
										}))
									finiteWindow := c.Have(
										"only finitely many primes lie in ⟬m + 1, n⟧",
										"finite(«primesBetween»(m + 1, n))",
										BySets(
											finite_set.FiniteSubset.At(window, c.TermAs[Set[Nat]]("{x:num | x ≤ n}")),
											num_segment.FiniteBelow))
									atMostMiddle := c.Have(
										"so their product divides binomial(2m + 1, m), which is not 0, and is at most it",
										"Π_{p∈«primesBetween»(m + 1, n)} p ≤ binomial(2 * m + 1, m)",
										ByArith(
											finiteWindow,
											divisors,
											nat_multiplicity.ProductOfPrimesDivides.At(window, middle),
											nat_divides.DividesLessEq.At(windowProduct, middle),
											binomial.EqZero.At(c.TermAs[Nat]("2 * m + 1"), m)))
									exponents := c.Have(
										"the exponents add up to n",
										"m + 1 + m = n",
										ByArith(half))
									bigPower := c.TermAs[Nat]("4 ^ (m + 1)")
									c.Show(
										"Erdős: primorial(n) = primorial(m + 1)·Π ≤ 4^(m + 1)·binomial(2m + 1, m) ≤ 4^(m + 1)·4^m = 4^n",
										nat_order.OrderCalc(c.Ctx()).CalcLeibniz(c.TermAs[Nat]("primorial(n)"),
											EqLeg(
												c.TermAs[Nat]("primorial(m + 1) * Π_{p∈«primesBetween»(m + 1, n)} p"),
												"the primes up to n are those up to m + 1 and those in ⟬m + 1, n⟧",
												ByArith(half, PrimorialSplit.At(next, n))),
											LeLeg(
												c.TermAs[Nat]("4 ^ (m + 1) * Π_{p∈«primesBetween»(m + 1, n)} p"),
												"the bound at m + 1 < n",
												By(
													below.At(next),
													past,
													nat_order.LessEqMulRightCancel.At(c.TermAs[Nat]("primorial(m + 1)"), bigPower, windowProduct))),
											LeLeg(
												c.TermAs[Nat]("4 ^ (m + 1) * binomial(2 * m + 1, m)"),
												"the product over ⟬m + 1, n⟧ is at most binomial(2m + 1, m)",
												By(atMostMiddle, nat_order.LessEqMulMono.At(bigPower, windowProduct, middle))),
											LeLeg(
												c.TermAs[Nat]("4 ^ (m + 1) * 4 ^ m"),
												"binomial(2m + 1, m) ≤ 4^m",
												By(
													binomial.MiddleBinomialOddBound.At(m),
													nat_order.LessEqMulMono.At(bigPower, middle, c.TermAs[Nat]("4 ^ m")))),
											EqLeg(
												c.TermAs[Nat]("4 ^ n"),
												"4^(m + 1)·4^m = 4^(m + 1 + m) = 4^n",
												By(exponents, nat_arith.PowAdd.At(c.Ctx().Nat(4), next, m)))))
								})
						}))))
		}),
})}
