// nat_prime.go — the chapter's first subject: primality, defined in ℕ.
//
// Five parts, marked by banners:
//
// - What primality IS
// - The first prime, and primes dividing primes
// - Euclid's lemma
// - The descent: a square is p times a square only at zero
// - Squares modulo a prime

package nat_prime

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// What primality IS
// ---------------------------------------------------------------------------
//
// `nat_prime` is a definition, not a theorem: `nat_prime(p)` abbreviates
// "p ≠ 1, and every divisor of p is 1 or p". The members here are the
// three shapes the rest of the theory meets that definition in — by
// divisor structure, by the divide-or-be-coprime alternative, and by the
// exclusive form of that alternative — and the one bound the definition
// yields on sight, that a prime is at least 2. The three equivalences each
// stand on the one before, so the definition is unfolded twice in the
// file: at the top of the first member, and for the bound — which the
// third equivalence then reads its `p ≠ 1` from.

// OneOrPrime reads the definition of `nat_prime` back as a property of
// the divisor lattice: a number whose only divisors are 1 and itself is
// prime, with 1 the single exception the definition legislates away.
//
// Unfolding makes the two sides almost identical — the right-hand
// condition is literally the definition's second conjunct — so the whole
// argument is the exception. In the ⇐ direction it is free: a p₀ that
// fails the exception satisfies both conjuncts, and one that meets it is
// the other disjunct. In the ⇒ direction it is the only thing to check,
// and DividesOne is exactly the check: the divisors of 1 are just 1.
var OneOrPrime = oneOrPrimeThm{family.Add(registry.ProofEntry{
	Name: "OneOrPrime",
	Key:  "prop_326c47fcc77d63c5",
	Build: family.Theorem(
		"∀p:num. p = 1 ∨ nat_prime(p) ⇔ ∀d:num. d ∣ p ⇒ d = 1 ∨ d = p",
		func(a *Argument, p *Expr[Nat]) {
			one := a.Ctx().Nat(1)

			// ↦ p₀ = 1 ∨ (p₀ ≠ 1 ∧ ∀x. x ∣ p₀ ⇒ x = 1 ∨ x = p₀) ⇔ …:
			// the goal's right-hand side reappears as the definition's own
			// second conjunct, and everything below is about the first one.
			a.Do(Unfold(PrimeDef))

			a.Iff()
			// The branch hypothesis `p₀ = 1 ∨ nat_prime(p₀)` is never
			// named: the p₀ ≠ 1 side consumes it ambiently, and the
			// p₀ = 1 side does not need it at all.
			a.Forward(
				"nat_prime(p₀) carries the divisor condition already; p₀ = 1 is the case that has to be checked",
				func(b *Argument) {
					isOne := b.Assuming(
						Equal(p, one),
						"we may assume p₀ = 1 — the other case leaves nat_prime(p₀), whose second conjunct IS the claim",
						Basic())

					b.Show(
						"at p₀ = 1 the claim is that a divisor of 1 is 1, and both disjuncts say so",
						By(isOne, nat_divides.DividesOne))
				})
			a.Backward(
				"a p₀ with no divisors but 1 and itself meets the second "+
					"conjunct, and meets the first or else is the left disjunct",
				TrivialNormalized())
		}),
})}

// PrimeAtLeastTwo — a prime is at least 2. The definition rules 1 out by
// fiat, and it rules 0 out through the divisor clause read at a single
// divisor: 2 divides 0, as every number does, so a prime that was 0
// would have 2 among its divisors — a divisor that is neither 1 nor 0.
// What remains of `p ≠ 0 ∧ p ≠ 1` is arithmetic.
var PrimeAtLeastTwo = primeAtLeastTwoThm{family.Add(registry.ProofEntry{
	Name: "PrimeAtLeastTwo",
	Key:  "prop_2570bec8374a061e",
	Build: family.Theorem(
		Statement{
			Binders: "∀p:num.",
			Hypotheses: []string{
				"nat_prime(p)",
			},
			Conclusion: "2 ≤ p",
		},
		func(a *Argument, p *Expr[Nat]) {
			two := a.Ctx().Nat(2)

			// ↦ p₀ ≠ 1, ∀x. x ∣ p₀ ⇒ x = 1 ∨ x = p₀ ⊢ 2 ≤ p₀: the
			// definition's two conjuncts become the hypotheses.
			a.Do(Unfold(PrimeDef))
			notOne := a.Hyp("p ≠ 1")
			divisorCond := a.Hyp("∀x:num. x ∣ p ⇒ x = 1 ∨ x = p")

			nonzero := a.Have(
				"p₀ is not 0: 2 would then be one of its divisors, and 2 is neither 1 nor 0",
				"p ≠ 0",
				ByArith(Normalized, divisorCond.At(two), nat_divides.DividesZero.At(two)))

			a.Show(
				"a number that is neither 0 nor 1 is at least 2",
				ByArith(nonzero, notOne))
		}),
})}

// PrimeDividesOrCoprime is primality seen from the other side: a prime
// is a number that meets every other number in only one of two ways — it
// divides it, or it shares nothing with it. (1 again is the exception,
// and again by fiat: it divides everything, so it satisfies the
// condition without being prime.)
//
// `nat_prime` never enters the argument. What the alternative is really
// equivalent to is p's divisor condition — that 1 and p are its only
// divisors — and OneOrPrime already bridges from there to the
// `nat_prime` packaging. So the file's own lemma states the equivalence
// where the content is, and the headline composes the two.
var PrimeDividesOrCoprime = primeDividesOrCoprimeThm{family.Add(registry.ProofEntry{
	Name: "PrimeDividesOrCoprime",
	Key:  "prop_8c0d3faca43e5a7a",
	Build: family.Sections(
		"∀p:num. p = 1 ∨ nat_prime(p) ⇔ ∀n:num. p ∣ n ∨ nat_coprime(p, n)",
		func(ctx *Script, headline string) *GoalStackNode {
			divides := ctx.Const("nat_divides", natDividesType)

			// dividesOrCoprime — the theorem with the `nat_prime` packaging
			// removed, which is where the mathematics is. Read the right side
			// as a test the alternative applies to p₀ at every n: ⇐ runs that
			// test at n := a divisor of p₀, and its two outcomes land on the
			// two disjuncts the divisor condition asks for; ⇒ runs the divisor
			// condition against a common divisor of p₀ and an n₀ that p₀
			// misses.
			//
			// The ⇐ arm needs two facts about the relation, and they are the
			// two the divisor condition is made of: antisymmetry closes the
			// p₀ ∣ d₀ corner, and reflexivity supplies the common divisor
			// d₀ ∣ d₀.
			dividesOrCoprime := ctx.Lemma(
				"∀p:num. (∀d:num. d ∣ p ⇒ d = 1 ∨ d = p) ⇔ ∀n:num. p ∣ n ∨ nat_coprime(p, n)",
				func(a *Argument, p *Expr[Nat]) {
					a.Iff()
					a.Forward(
						"nothing but 1 and p₀ divides p₀, so any n₀ that p₀ misses shares only 1 with it",
						func(b *Argument, divisorCond Fact) {
							n := b.FixAs[Nat]() // let n₀ be arbitrary

							notDivides := b.Unless(
								divides.Apply(p, n),
								"p₀ ∣ n₀ is the left disjunct outright",
								TrivialNormalized())

							b.Show(
								"a common divisor of p₀ and n₀ is 1 or p₀ by the divisor condition, and p₀ is ruled out by p₀ ∤ n₀",
								By(
									notDivides,
									divisorCond,
									nat_gcd.Coprime.At(p, n))) // nat_coprime(p₀, n₀) ⇔ every common divisor of p₀ and n₀ is 1
						})
					a.Backward(
						"run the alternative at n := d₀ on a divisor d₀ of "+
							"p₀: p₀ ∣ d₀ forces d₀ = p₀, coprimality forces d₀ = 1",
						func(b *Argument, alternative Fact) {
							d := b.FixAs[Nat]() // let d₀ be arbitrary
							// …and assume d₀ divides p₀, the divisor
							// condition's antecedent.
							dDivP := b.Assume()

							notDivides := b.Unless(
								divides.Apply(p, d),
								"p₀ ∣ d₀ closes the loop with d₀ ∣ p₀ — the two are equal, which is the right disjunct",
								Given(func(c *Argument, pDivD Fact) {
									c.Show(
										"antisymmetry at (d₀, p₀)",
										By(dDivP, pDivD, nat_divides.DividesAntisym.At(d, p)))
								}))

							b.Show(
								"so the alternative at n := d₀ leaves p₀ and d₀ coprime; d₀ "+
									"is a common divisor of the two, hence 1 — the left disjunct",
								By(
									notDivides,
									alternative.At(d),
									dDivP,
									nat_divides.DividesRefl.At(d), // d₀ ∣ d₀
									nat_gcd.Coprime.At(p, d)))     // nat_coprime(p₀, d₀) ⇔ every common divisor of p₀ and d₀ is 1
						})
				})

			return ctx.Theorem(headline,
				func(a *Argument, p *Expr[Nat]) {
					a.Show(
						"OneOrPrime and the lemma equate p₀'s divisor condition to "+
							"the two sides of the headline, so citing both composes them",
						Cite(dividesOrCoprime, p), // the lemma at p₀
						// ↦ closes: bare, because OneOrPrime fires as a goal
						// rewrite — it replaces the headline's left side with
						// the divisor condition, which the line above has
						// already equated to the right side.
						Cite(OneOrPrime))
				})
		}),
})}

// PrimeCoprimeIffNotDivides sharpens the previous member's alternative
// into an exclusive one: for a prime, coprimality with n and
// divisibility of n are exact opposites. Exhaustiveness is
// PrimeDividesOrCoprime; disjointness is the observation that a prime
// dividing n is then a common divisor of p and n other than 1.
//
// So the exception moves out of the statement and into the proof: p = 1
// is exactly what makes the two cases overlap, and the two directions
// rule it out differently — ⇒ reads it off the bound the definition
// yields (PrimeAtLeastTwo), ⇐ derives it from the equivalence at n := p.
var PrimeCoprimeIffNotDivides = primeCoprimeIffNotDividesThm{family.Add(registry.ProofEntry{
	Name: "PrimeCoprimeIffNotDivides",
	Key:  "prop_8df296aee006a51e",
	Build: family.Theorem(
		"∀p:num. nat_prime(p) ⇔ ∀n:num. nat_coprime(p, n) ⇔ ¬(p ∣ n)",
		func(a *Argument, p *Expr[Nat]) {
			// Reflexivity at p₀ is what both directions turn on: it is
			// the common divisor that makes p₀ ∣ n₀ and coprimality
			// incompatible.
			selfDiv := nat_divides.DividesRefl.At(p) // p₀ ∣ p₀

			a.Iff()
			a.Forward(
				"nat_prime(p₀) supplies both halves: exhaustiveness "+
					"from PrimeDividesOrCoprime, disjointness from p₀ ≠ 1",
				func(b *Argument, isPrime Fact) {
					notOne := b.Have(
						"a prime is at least 2, so not 1",
						"p₀ ≠ 1",
						ByArith(isPrime, PrimeAtLeastTwo.At(p))) // nat_prime(p₀) ⇒ 2 ≤ p₀

					alternative := b.Have(
						"of the two disjuncts PrimeDividesOrCoprime offers "+
							"on the left, nat_prime(p₀) is the one that holds",
						"∀n:num. p₀ ∣ n ∨ nat_coprime(p₀, n)",
						// Bare: the cite fires as a goal rewrite,
						// turning the claim into
						// `p₀ = 1 ∨ nat_prime(p₀)`.
						By(isPrime, PrimeDividesOrCoprime))

					n := b.FixAs[Nat]() // let n₀ be arbitrary

					b.Iff()
					b.Forward(
						"p₀ ∣ n₀ would make p₀ a common divisor of p₀ and n₀, which coprimality collapses to 1",
						func(c *Argument, coprime Fact) {
							c.Show(
								"Coprime at (p₀, n₀), applied to the divisor p₀ itself, against p₀ ≠ 1",
								By(coprime, selfDiv, notOne, nat_gcd.Coprime.At(p, n)))
						})
					b.Backward(
						"p₀ ∤ n₀ leaves the alternative at n₀ with only its coprimality disjunct",
						func(c *Argument, notDivides Fact) {
							c.Show(
								"the alternative at n₀",
								By(notDivides, alternative.At(n)))
						})
				})
			a.Backward(
				"the equivalence at n := p₀ already says p₀ ≠ 1, and what is left is exhaustiveness",
				func(b *Argument, test Fact) {
					notOne := b.Have(
						"p₀ ∣ p₀ makes p₀ not coprime to itself; but 1 IS coprime to 1, since 1's only divisor is 1",
						"p₀ ≠ 1",
						By(
							test.At(p),
							selfDiv,
							nat_gcd.Coprime.At(p, p), // nat_coprime(p₀, p₀) ⇔ every divisor of p₀ is 1
							nat_divides.DividesOne))  // a divisor of 1 is 1

					b.Show(
						"the equivalence gives `p₀ ∣ n ∨ coprime(p₀, n)` at every n, "+
							"which PrimeDividesOrCoprime turns into `p₀ = 1 ∨ nat_prime(p₀)`",
						By(Normalized, test, notOne, PrimeDividesOrCoprime.At(p)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The first prime, and primes dividing primes
// ---------------------------------------------------------------------------
//
// Two facts about particular primes, each read through the first of the
// three shapes above: 2 is prime, its divisors squeezed between 1 and 2;
// and a prime divides another prime only by being it. Together they leave
// 2 dividing no other prime: every prime but 2 is odd, 2h + 1.

// PrimeTwo — 2 is prime. Its divisors are squeezed: a divisor of a
// nonzero number lies between 1 and the number, so a divisor of 2 is 1
// or 2, and that is the divisor condition OneOrPrime reads primality
// from — up to the exception it legislates, which 2 is not.
var PrimeTwo = primeTwoThm{family.Add(registry.ProofEntry{
	Name: "PrimeTwo",
	Key:  "prop_b562ff367099dc4b",
	Build: family.Theorem(
		"nat_prime(2)",
		func(a *Argument) {
			two := a.Ctx().Nat(2)

			onlyDivisors := a.Have(
				"a divisor of 2 lies between 1 and 2",
				"∀d:num. d ∣ 2 ⇒ d = 1 ∨ d = 2",
				Derive(func(b *Argument) {
					d := b.FixAs[Nat]()
					dividesTwo := b.Assume()
					b.Show(
						"the bound's other arm, 2 = 0, is dead, and nothing but 1 and 2 lies in the range",
						ByArith(dividesTwo, nat_divides.DividesLessEqStrong.At(d, two))) // d₀ ∣ 2 ⇒ 1 ≤ d₀ ∧ d₀ ≤ 2 ∨ 2 = 0
				}))

			a.Show(
				"OneOrPrime at 2 reads the divisor condition as 2 "+
					"= 1 ∨ nat_prime(2), and the first disjunct is out",
				By(onlyDivisors, OneOrPrime.At(two)))
		}),
})}

// PrimeDividesPrime — a prime q has no divisors but 1 and q, so a prime
// p that divides it is one of the two; and p, being prime, is at least
// 2, which leaves q. The converse is reflexivity.
var PrimeDividesPrime = primeDividesPrimeThm{family.Add(registry.ProofEntry{
	Name: "PrimeDividesPrime",
	Key:  "prop_48ba741e2373536",
	Build: family.Theorem(
		Statement{
			Binders: "∀p q:num.",
			Hypotheses: []string{
				"nat_prime(p)",
				"nat_prime(q)",
			},
			Conclusion: "p ∣ q ⇔ p = q",
		},
		func(a *Argument, p, q *Expr[Nat], primes Fact) {
			a.Iff()
			a.Forward(
				"p₀ is a divisor of the prime q₀, so 1 or q₀ — and a prime is not 1",
				func(b *Argument, divides Fact) {
					oneOrQ := b.Have(
						"the divisors of the prime q₀ are 1 and q₀, and p₀ is one of them",
						"p = 1 ∨ p = q",
						By(divides, primes, OneOrPrime.At(q))) // q₀ = 1 ∨ nat_prime(q₀) ⇔ every divisor of q₀ is 1 or q₀

					b.Show(
						"2 ≤ p₀ rules out p₀ = 1, which leaves p₀ = q₀",
						ByArith(oneOrQ, primes, PrimeAtLeastTwo.At(p)))
				})
			a.Backward(
				"a number divides itself",
				func(b *Argument, equal Fact) {
					b.Show(
						"rewritten by p₀ = q₀, the claim is q₀ ∣ q₀",
						equal.Rw(),
						By(nat_divides.DividesRefl))
				})
		}),
})}

// PrimeOddUnlessTwo — a prime other than 2 is odd: an even number is 2
// taken some number of times, so 2 divides it, and 2 divides a prime only
// by being it.
var PrimeOddUnlessTwo = primeOddUnlessTwoThm{family.Add(registry.ProofEntry{
	Name: "PrimeOddUnlessTwo",
	Key:  "prop_c81d9d91477af02a",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "nat_odd(p)",
	}, func(a *Argument, p *Expr[Nat], prime, notTwo Fact) {
		two := a.Ctx().Nat(2)
		a.Show(
			"were p even, 2 would divide it, and 2 divides the prime p only by being it",
			By(
				prime,
				notTwo,
				nat_parity.OddIffNotEven.At(p),
				nat_parity.EvenIffDouble.At(p),
				nat_divides.DividesFactor.At(two, p),
				PrimeDividesPrime.At(two, p),
				PrimeTwo))
	}),
})}

// OddPrimeHalf — an odd prime p is 2h + 1 for h = (p − 1)/2: 2 divides
// no prime but itself, so p leaves remainder 1 on division by 2, and p − 1
// is twice the quotient.
var OddPrimeHalf = oddPrimeHalfThm{family.Add(registry.ProofEntry{
	Name: "OddPrimeHalf",
	Key:  "prop_e37a56e397eca46b",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ≠ 2",
		},
		Conclusion: "p = 2 * div(p - 1, 2) + 1",
	}, func(arg *Argument, p *Expr[Nat], prime, odd Fact) {
		two := arg.TermAs[Nat]("2")
		arg.Show(
			"2 does not divide the prime p ≠ 2, so p = 2·div(p, 2) + 1 and p − 1 = 2·div(p, 2)",
			ByArith(
				prime,
				odd,
				PrimeDividesPrime.At(two, p),
				PrimeTwo,
				nat_divides.DividesMod.At(two, p),
				nat_div_mod.Division.At(p, two),
				nat_div_mod.DivUniq.At(
					arg.TermAs[Nat]("p - 1"), two, arg.TermAs[Nat]("div(p, 2)"), arg.TermAs[Nat]("0"))))
	}),
})}

// OddPrimeSplit — an odd number other than 1 is an odd prime times a smaller
// odd number: a prime p divides it, n = p·m, and both factors of the odd n
// are odd, so p is not 2 and m is not 0, and m < 2·m ≤ p·m = n.
var OddPrimeSplit = oddPrimeSplitThm{family.Add(registry.ProofEntry{
	Name: "OddPrimeSplit",
	Key:  "prop_e7da1eba71c26eb0",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"nat_odd(n)",
			"n ≠ 1",
		},
		Conclusion: "∃p m:num. nat_prime(p) ∧ p ≠ 2 ∧ nat_odd(p) ∧ nat_odd(m) ∧ n = p * m ∧ m < n",
	}, func(a *Argument, n *Expr[Nat], odd, notOne Fact) {
		pastOne := a.Have(
			"n is odd, so not 0, and it is not 1: it is past 1",
			"1 < n",
			ByArith(odd, notOne))
		p, prime := a.ObtainAs[Nat](
			"a prime p divides n",
			"∃p:num. nat_prime(p) ∧ p ∣ n",
			By(pastOne, PrimeFactor.At(n)))
		m, split := a.ObtainAs[Nat](
			"write n = p·m",
			"∃m:num. n = p * m",
			By(prime, nat_divides.DividesFactor.At(p, n)))
		parts := a.Have(
			"p and m are odd, their product n being odd",
			"nat_odd(p) ∧ nat_odd(m)",
			By(
				Normalized,
				odd,
				split,
				nat_parity.EvenMul.At(p, m),
				nat_parity.OddIffNotEven.At(n),
				nat_parity.OddIffNotEven.At(p),
				nat_parity.OddIffNotEven.At(m)))
		a.Take(p)
		a.Take(m)
		a.Show(
			"being odd, p is not 2 and m is not 0, so m < 2·m ≤ p·m = n",
			ByArith(
				split,
				prime,
				parts,
				nat_parity.OddIffModTwoOne.At(p),
				nat_parity.OddIffModTwoOne.At(m),
				PrimeAtLeastTwo.At(p),
				nat_order.LessEqMulMono.At(m, a.Ctx().Nat(2), p)))
	}),
})}

// ---------------------------------------------------------------------------
// Euclid's lemma
// ---------------------------------------------------------------------------
//
// Euclid's lemma: a prime that divides a product divides one of
// its factors — and its converse, which turns the lemma into a
// characterization: the moduli it holds of are exactly 0, 1 and the
// primes, and nothing else.
//
// The two directions are not the same theorem. That a divisor of a
// factor divides the product holds of every p and is one line of
// arithmetic; the converse is false in general — 6 divides 4·9 and
// neither factor — and holds for a prime exactly because a prime that
// misses one factor shares nothing with it.
//
// "Shares nothing with it" is coprimality, and nat_gcd.CoprimeCancel
// cancels it — through the gcd's universal property, with no Bézout
// coefficient; its godoc tells the argument.
//
// Most statements here bind `a` and `b`, which the corpus-wide Argument
// receiver `a` would shadow, so the receiver is `arg` throughout.

// EuclidLemma is Euclid's lemma with its degenerate moduli folded in.
//
//	⇐ holds of every p, prime or not: nat_divides.DividesMul, twice.
//	⇒ turns on how p meets b. PrimeDividesOrCoprime says a p that is 1 or
//	 prime either divides b — which is the right disjunct outright — or
//	 is coprime to it, and nat_gcd.CoprimeCancel turns that coprimality into
//	 p ∣ a. p = 0 is the one remaining alternative, and zeroCase settles
//	 it.
//
// The disjunctive form of the alternative is what the ⇒ direction wants
// rather than the exclusive PrimeCoprimeIffNotDivides, and it pays
// twice: p = 1 stops being a case of its own, since the disjunction
// already covers it.
var EuclidLemma = euclidLemmaThm{family.Add(registry.ProofEntry{
	Name: "EuclidLemma",
	Key:  "prop_cf88992ef6809926",
	Build: family.Sections(
		Statement{
			Binders: "∀p a b:num.",
			Hypotheses: []string{
				"p = 0 ∨ p = 1 ∨ nat_prime(p)",
			},
			Conclusion: "p ∣ a * b ⇔ p ∣ a ∨ p ∣ b",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			zero := ctx.Nat(0)

			// zeroCase — the degenerate modulus, and the only part of the
			// theorem that is about ℕ multiplication rather than about
			// divisibility: 0 divides nothing but 0, so the hypothesis says
			// the product vanishes.
			zeroCase := ctx.Lemma(Statement{
				Binders: "∀a b:num.",
				Hypotheses: []string{
					"0 ∣ a * b",
				},
				Conclusion: "0 ∣ a ∨ 0 ∣ b",
			},
				func(arg *Argument, a, b *Expr[Nat], vanishes Fact) {
					product := arg.TermAs[Nat]("a * b")

					arg.Show(
						"the product vanishes, so one factor does — and 0 divides that factor because it divides itself",
						By(
							vanishes,
							nat_divides.ZeroDivides.At(product), // 0 ∣ a₀·b₀ ⇒ a₀·b₀ = 0
							nat_arith.MulEqZero.At(a, b),        // a₀·b₀ = 0 ⇔ a₀ = 0 ∨ b₀ = 0
							nat_divides.DividesRefl.At(zero)))   // 0 ∣ 0
				})

			return ctx.Theorem(headline,
				func(arg *Argument, p, a, b *Expr[Nat], cases Fact) {
					arg.Iff()
					arg.Forward(
						"the direction the hypothesis on p₀ is there for",
						func(c *Argument, divProd Fact) {
							alternative := c.Have(
								"outside p₀ = 0 the hypothesis pins how p₀ meets b₀: it divides b₀, or it shares nothing with it",
								"p₀ = 0 ∨ p₀ ∣ b₀ ∨ nat_coprime(p₀, b₀)",
								// p₀ = 1 ∨ nat_prime(p₀) ⇔ ∀n. p₀ ∣ n ∨ nat_coprime(p₀, n),
								// read at n := b₀.
								By(cases, PrimeDividesOrCoprime.At(p)))

							c.Show(
								"each of the three lands on a disjunct — p₀ ∣ b₀ on the right one "+
									"outright, coprimality on the left one by cancellation, p₀ = 0 by zeroCase",
								By(
									alternative,
									divProd,
									At(zeroCase, a, b),                 // 0 ∣ a₀·b₀ ⇒ 0 ∣ a₀ ∨ 0 ∣ b₀
									nat_gcd.CoprimeCancel.At(p, a, b))) // nat_coprime(p₀, b₀) ∧ p₀ ∣ a₀·b₀ ⇒ p₀ ∣ a₀
						})
					arg.Backward(
						"a divisor of either factor divides the product, whatever p₀ is",
						func(c *Argument, either Fact) {
							c.Show(
								"a divisor of one factor divides the product, read from each side "+
									"in turn, and commutativity is what lets the second reading count",
								By(
									Normalized,
									either,
									nat_divides.DividesMul.At(p, a, b), // p₀ ∣ a₀ ⇒ p₀ ∣ a₀·b₀
									nat_divides.DividesMul.At(p, b, a), // p₀ ∣ b₀ ⇒ p₀ ∣ b₀·a₀
									nat_arith.MulSym.At(b, a)))         // b₀·a₀ = a₀·b₀
						})
				})
		}),
})}

// PrimeDividesPower — a prime dividing a power of m divides m: by induction
// on the exponent, a prime dividing m^(e+1) = m·m^e divides m or m^e
// (Euclid's lemma), and none divides m⁰ = 1.
var PrimeDividesPower = primeDividesPowerThm{family.Add(registry.ProofEntry{
	Name: "PrimeDividesPower",
	Key:  "prop_50e0e77203cab1a9",
	Build: family.Theorem(Statement{
		Binders: "∀p m e:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"p ∣ m ^ e",
		},
		Conclusion: "p ∣ m",
	},
		func(a *Argument, p, m *Expr[Nat], prime Fact) {
			a.Induct("e")
			a.Base(
				"m⁰ = 1, and a prime does not divide 1",
				ByArith(prime, PrimeAtLeastTwo.At(p), nat_divides.DividesOne.At(p), nat_arith.NatPow))
			a.Step(
				"a prime dividing m·mᵉ divides m or mᵉ",
				func(b *Argument, ih Fact) {
					b.Show(
						"Euclid's lemma, and the induction for mᵉ",
						By(Normalized, prime, ih, EuclidLemma.At(p, m, b.TermAs[Nat]("m ^ e")), nat_arith.NatPow))
				})
		}),
})}

// FactorOfPrimeSquare — a factor of the square of a prime is 1, the prime
// or its square: the prime divides one of the two factors, and cancelling
// it leaves a factor of the prime itself.
var FactorOfPrimeSquare = factorOfPrimeSquareThm{family.Add(registry.ProofEntry{
	Name: "FactorOfPrimeSquare",
	Key:  "prop_a1eff2903df63674",
	Build: family.Theorem(Statement{
		Binders: "∀p d e:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"d * e = p * p",
		},
		Conclusion: "d = 1 ∨ d = p ∨ d = p * p",
	}, func(a *Argument, p, d, e *Expr[Nat], prime, product Fact) {
		either := a.Have(
			"p divides the product d e = p p, so it divides d or e",
			"p ∣ d ∨ p ∣ e",
			By(Normalized, prime, product, EuclidLemma.At(p, d, e), nat_divides.DividesOwnMultiple.At(p, p)))
		a.Do(either.SplitDisj(
			LeftHolds(
				"p divides d: d = p x with x e = p, so x is 1 or p",
				Given(func(b *Argument, divides Fact) {
					x, factor := b.ObtainAs[Nat](
						"d is p times some x",
						"∃x:num. d = p * x",
						By(divides, nat_divides.DividesFactor.At(p, d)))
					cofactor := b.Have(
						"cancelling p from p x e = p p leaves x e = p",
						"x * e = p",
						ByArith(
							prime,
							Scaled(e, factor),
							product,
							nat_arith.MulEqLCancel.At(p, b.TermAs[Nat]("x * e"), p),
							PrimeAtLeastTwo.At(p)))
					xOneOrP := b.Have(
						"x divides the prime p, so x is 1 or p",
						"x = 1 ∨ x = p",
						By(prime, cofactor, nat_divides.DividesFactor.At(x, p), PrimeDef.At(p)))
					b.Do(xOneOrP.SplitDisj(
						LeftHolds(
							"x = 1, and d = p",
							Given(func(c *Argument, one Fact) {
								c.Show(
									"d is p",
									ByArith(factor, one))
							})),
						RightHolds(
							"x = p, and d = p p",
							Given(func(c *Argument, same Fact) {
								c.Show(
									"d is p p",
									ByArith(factor, same))
							}))))
				})),
			RightHolds(
				"p divides e: e = p y with d y = p, so d is 1 or p",
				Given(func(b *Argument, divides Fact) {
					_, factor := b.ObtainAs[Nat](
						"e is p times some y",
						"∃y:num. e = p * y",
						By(divides, nat_divides.DividesFactor.At(p, e)))
					cofactor := b.Have(
						"cancelling p from d p y = p p leaves d y = p",
						"d * y = p",
						ByArith(
							prime,
							Scaled(d, factor),
							product,
							nat_arith.MulEqLCancel.At(p, b.TermAs[Nat]("d * y"), p),
							PrimeAtLeastTwo.At(p)))
					b.Show(
						"d divides the prime p, so d is 1 or p",
						By(prime, cofactor, nat_divides.DividesFactor.At(d, p), PrimeDef.At(p)))
				}))))
	}),
})}

// ZeroOneOrPrime is EuclidLemma read backwards, and it makes the lemma a
// characterization: dividing a product only through a factor is not just
// something 0, 1 and the primes happen to do — it is all they do, and all
// anything does.
//
//	⇒ is EuclidLemma's own ⇒ arm, taken at each pair in turn.
//	⇐ is where the mathematics is, and it recovers p's DIVISOR structure
//	 from its behaviour on products. A divisor d of p comes with a
//	 cofactor x; p divides d·x for the trivial reason that it IS d·x, so
//	 the hypothesis sends p into one of the two factors, and each landing
//	 pins d. Into d: with d ∣ p already in hand, the two are equal. Into
//	 x: x = p likewise, so p = d·p, and cancelling the p leaves d = 1.
//	 Those two outcomes are precisely the divisor condition, which
//	 OneOrPrime carries back to `nat_prime`.
//
// p = 0 is conceded rather than proved, and it is the reason the ⇐
// direction cannot reach `nat_prime` alone: 0 does divide a product only
// through a factor, but every number divides 0, so its divisors are not a
// prime's. It is a genuine third case of the statement, not packaging.
var ZeroOneOrPrime = zeroOneOrPrimeThm{family.Add(registry.ProofEntry{
	Name: "ZeroOneOrPrime",
	Key:  "prop_6b87fa4308fbe5c",
	Build: family.Sections(
		"∀p:num. p = 0 ∨ p = 1 ∨ nat_prime(p) ⇔ ∀a b:num. p ∣ a * b ⇒ p ∣ a ∨ p ∣ b",
		func(ctx *Script, headline string) *GoalStackNode {
			divides := ctx.Const("nat_divides", natDividesType)
			zero, one := ctx.Nat(0), ctx.Nat(1)

			// onlyDivisors — the whole content of the hard direction, stated
			// where it lives: about p₀'s divisors, with `nat_prime` nowhere in
			// sight. The headline's job is then only to say that this divisor
			// condition IS primality, which OneOrPrime says.
			//
			// Nonzeroness is a real hypothesis and not bookkeeping: 0 meets
			// the multiplicative condition and fails this conclusion.
			onlyDivisors := ctx.Lemma(
				"∀p:num. p ≠ 0 ⇒ (∀a b:num. p ∣ a * b ⇒ p ∣ a ∨ p ∣ b) ⇒ ∀d:num. d ∣ p ⇒ d = 1 ∨ d = p",
				func(arg *Argument, p *Expr[Nat], nonzero, factorwise Fact) {
					d := arg.FixAs[Nat]() // let d₀ be arbitrary…
					dDivP := arg.Assume()

					x, factor := arg.ObtainAs[Nat](
						"…and let x₀ be the cofactor d ∣ p names",
						"∃x:num. p = d * x",
						By(dDivP, nat_divides.DividesFactor))

					alternative := arg.Have(
						"p divides the product d·x for the trivial reason that it is that "+
							"product, so the hypothesis sends it into one of the two factors",
						"p ∣ d ∨ p ∣ x",
						By(
							Normalized,
							factor,
							nat_divides.DividesRefl.At(p), // p₀ ∣ p₀
							factorwise.At(d, x)))          // p₀ ∣ d₀·x₀ ⇒ p₀ ∣ d₀ ∨ p₀ ∣ x₀

					pMissesD := arg.Unless(
						divides.Apply(p, d),
						"landing in d₀ closes the loop with d₀ ∣ p₀ — the "+
							"two divide each other, so d₀ = p₀, the right disjunct",
						Given(func(c *Argument, pDivD Fact) {
							c.Show(
								"antisymmetry at (d₀, p₀)",
								By(dDivP, pDivD, nat_divides.DividesAntisym.At(d, p)))
						}))

					cofactorIsP := arg.Have(
						"so it is x that p lands in; and x divides p in turn, "+
							"since p = x·d₀ reads the factorization the other way round",
						"x = p",
						By(
							Normalized,
							alternative,
							pMissesD,
							factor,
							nat_arith.MulSym.At(d, x),            // d₀·x₀ = x₀·d₀
							nat_divides.DividesFactor.At(x, p),   // x₀ ∣ p₀ ⇔ ∃y. p₀ = x₀·y
							nat_divides.DividesAntisym.At(x, p))) // x₀ ∣ p₀ ∧ p₀ ∣ x₀ ⇔ x₀ = p₀

					arg.Show(
						"the factorization is then p₀ = d₀·p₀, one copy of p₀ against another; "+
							"a nonzero p₀ cancels out of it and leaves d₀ = 1, the left disjunct",
						By(
							cofactorIsP,
							factor,
							nonzero,
							nat_arith.MulOne.At(p),                // p₀·1 = p₀
							nat_arith.MulSym.At(d, p),             // d₀·p₀ = p₀·d₀
							nat_arith.MulEqLCancel.At(p, one, d))) // p₀·1 = p₀·d₀ ⇔ p₀ = 0 ∨ 1 = d₀
				})

			return ctx.Theorem(headline,
				func(arg *Argument, p *Expr[Nat]) {
					arg.Iff()
					arg.Forward(
						"nothing to add: this is EuclidLemma's own ⇒ arm, once a₀ and b₀ are named",
						func(c *Argument, cases Fact) {
							a, b := c.FixAs[Nat](), c.FixAs[Nat]() // let a₀, b₀ be arbitrary…
							divProd := c.Assume()                  // …with p₀ ∣ a₀·b₀

							c.Show(
								"EuclidLemma at (p₀, a₀, b₀)",
								By(cases, divProd, EuclidLemma.At(p, a, b)))
						})
					arg.Backward(
						"the multiplicative condition recovers p₀'s divisors, "+
							"and having only 1 and p₀ among them is primality",
						func(c *Argument, factorwise Fact) {
							nonzero := c.Unless(
								Equal(p, zero),
								"p₀ = 0 is a disjunct of the goal outright — and it has "+
									"to be, since 0 satisfies the condition without being prime",
								TrivialNormalized())

							c.Show(
								"onlyDivisors turns the condition into p₀'s divisor "+
									"condition, which OneOrPrime reads as p₀ = 1 ∨ nat_prime(p₀)",
								By(
									factorwise,
									nonzero,
									At(onlyDivisors, p), // p₀ ≠ 0 ⇒ the condition ⇒ p₀'s divisor condition
									OneOrPrime))
						})
				})
		}),
})}

// ---------------------------------------------------------------------------
// The descent: a square is p times a square only at zero
// ---------------------------------------------------------------------------
//
// Euclid's lemma spent once more, as an infinite descent — the ℕ core of
// "√p is irrational", which real/rational states over the reals.

// SquareEqPrimeTimesSquare — a² = p·b² has no solution but a = b = 0 when
// p is prime.
//
// Descent, run as strong induction on a with b quantified inside the
// predicate; in the step the solution is written (n, k), and the smaller
// one it factors through is (k, c). A solution (a, b) puts p under a·a, hence under a by
// Euclid's lemma; writing a = p·c and cancelling one p out of
// p·(p·c²) = p·b² leaves b² = p·c² — the same equation, now headed by b.
// If b = 0 the original equation reads a·a = 0 and a vanishes with it.
// Otherwise b² is at least 1, so a² = p·b² ≥ 2·b² lies strictly above
// b², which puts b below a, and the induction hypothesis at b says the
// solution (b, c) is trivial — against b ≠ 0.
var SquareEqPrimeTimesSquare = squareEqPrimeTimesSquareThm{family.Add(registry.ProofEntry{
	Name: "SquareEqPrimeTimesSquare",
	Key:  "prop_a10065b6ad2cd8df",
	Build: family.Theorem(
		Statement{
			Binders: "∀p a b:num.",
			Hypotheses: []string{
				"nat_prime(p)",
				"a * a = p * (b * b)",
			},
			Conclusion: "a = 0 ∧ b = 0",
		},
		func(arg *Argument, p, a, b *Expr[Nat], solution Fact) {
			two, zero := arg.Ctx().Nat(2), arg.Ctx().Nat(0)
			mulAC := nat_arith.MulAC(arg.Ctx())

			atLeastTwo := arg.Have(
				"a prime is at least 2",
				"2 ≤ p",
				By(solution, PrimeAtLeastTwo.At(p))) // nat_prime(p₀) ⇒ 2 ≤ p₀

			// The induction predicate: n heads no solution but the trivial one.
			headsOnlyTrivial := arg.Term("λn:num. ∀k:num. n * n = p * (k * k) ⇒ n = 0 ∧ k = 0")

			arg.Show(
				"strong induction on a, with the descent from a solution "+
					"(a, b) to the solution (b, c) it factors through as the step",
				ByInduction(At(nat_order.StrongInduction, headsOnlyTrivial), solution,
					Case(
						"granted only trivial solutions below n, so at n: a solution (n, "+
							"k) descends to one headed by k, and k lies below n unless it is 0",
						Derive(func(step *Argument) {
							n := step.FixAs[Nat]() // the step's own point…
							below := step.Assume() // …with every m < n₀ heading only the trivial solution
							k := step.FixAs[Nat]() // a solution (n₀, k₀):
							eq := step.Assume()    // n₀·n₀ = p₀·(k₀·k₀)

							kSquared := step.TermAs[Nat]("k * k")

							pDivN := step.Have(
								"the equation exhibits k·k as the cofactor of p in "+
									"n·n, so p divides n·n — hence, being prime, n itself",
								"p ∣ n",
								By(
									Normalized,
									eq,
									solution,
									nat_divides.DividesFactor.At(p, step.TermAs[Nat]("n * n")), // p₀ ∣ n₀·n₀ ⇔ ∃x. n₀·n₀ = p₀·x
									EuclidLemma.At(p, n, n))) // p₀ = 0 ∨ p₀ = 1 ∨ nat_prime(p₀) ⇒ (p₀ ∣ n₀·n₀ ⇔ p₀ ∣ n₀ ∨ p₀ ∣ n₀)

							_, factor := step.Obtain(
								"so n is p taken c times",
								"∃c:num. n = p * c",
								By(pDivN, nat_divides.DividesFactor))

							squared := step.Have(
								"squaring the factorization regroups (p·c)·(p·c) as p·(p·(c·c))",
								"n * n = p * (p * (c * c))",
								By(
									Normalized,
									factor,
									mulAC.Eq(step.TermAs[Nat]("p * c * (p * c)"), step.TermAs[Nat]("p * (p * (c * c))"))))

							cancelled := step.Have(
								"so p·(p·(c·c)) = p·(k·k), and the nonzero p cancels: (k, c) solves the same equation",
								"k * k = p * (c * c)",
								ByArith(
									atLeastTwo,
									squared,
									eq,
									// p₀·(p₀·(c₀·c₀)) = p₀·(k₀·k₀) ⇔ p₀ = 0 ∨ p₀·(c₀·c₀) = k₀·k₀
									nat_arith.MulEqLCancel.At(p, step.TermAs[Nat]("p * (c * c)"), kSquared)))

							nonzero := step.Unless(
								Equal(k, zero),
								"k vanishes, so n·n = p·0 = 0 and n vanishes with it",
								Given(func(sub *Argument, isZero Fact) {
									sub.Show(
										"a vanishing square has a vanishing root",
										ByArith(isZero, eq, nat_arith.MulEqZero.At(n, n))) // n₀·n₀ = 0 ⇔ n₀ = 0 ∨ n₀ = 0
								}))

							smaller := step.Have(
								"k·k is at least 1, so n·n = p·(k·k) ≥ 2·(k·k) lies strictly "+
									"above k·k; and squaring is monotone, so n ≤ k is impossible",
								"k < n",
								ByArith(
									nonzero,
									atLeastTwo,
									eq,
									nat_arith.MulEqZero.At(k, k), // k₀·k₀ = 0 ⇔ k₀ = 0 ∨ k₀ = 0
									// 2 ≤ p₀ ∧ k₀·k₀ ≤ k₀·k₀ ⇒ 2·(k₀·k₀) ≤ p₀·(k₀·k₀)
									nat_order.LessEqMul2.At(two, p, kSquared, kSquared),
									nat_order.LessEqMul2.At(n, k, n, k))) // n₀ ≤ k₀ ∧ n₀ ≤ k₀ ⇒ n₀·n₀ ≤ k₀·k₀

							step.Show(
								"the induction hypothesis at k: (k, c) is a solution headed by k, so k = 0 — against k ≠ 0",
								By(below.At(k), smaller, cancelled, nonzero))
						}))))
		}),
})}

// ---------------------------------------------------------------------------
// Squares modulo a prime
// ---------------------------------------------------------------------------
//
// Euclid's lemma read as a congruence. For a = b + 1, a² ≡ 1 (mod p) says
// p divides b·(b + 2), so a prime p divides b or b + 2: the square roots of
// 1 are 1 and p − 1. For y ≤ x, x² ≡ y² says p divides (x − y)(x + y), so
// below p/2 two numbers with one square are one number.

// SelfInverse — mod a prime p, a nonzero residue a is its own inverse
// exactly when it is 1 or p − 1. Write a = b + 1: then a² = 1 + b(b + 2),
// so a² ≡ 1 exactly when p divides b(b + 2), that is p ∣ b or p ∣ b + 2
// (EuclidLemma). As a < p, b lies below p and b + 2 at most at p, so
// p ∣ b says b = 0 and p ∣ b + 2 says b + 2 = p.
var SelfInverse = selfInverseThm{family.Add(registry.ProofEntry{
	Name: "SelfInverse",
	Key:  "prop_307ff40074b40d58",
	Build: family.Theorem(Statement{
		Binders: "∀p a:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"0 < a",
			"a < p",
		},
		Conclusion: "a * a ≡ 1 (mod p) ⇔ a = 1 ∨ a = p - 1",
	}, func(arg *Argument, p *Expr[Nat], prime Fact, a *Expr[Nat], bounds Fact) {
		one := arg.Ctx().Nat(1)
		b, shift := arg.ObtainAs[Nat](
			"a is past 0, so it is b + 1 for some b",
			"∃b:num. a = b + 1",
			Witness(arg.TermAs[Nat]("a - 1")),
			ByArith(bounds))
		square := arg.Have(
			"a² is 1 + b·(b + 2)",
			"a * a = 1 + b * (b + 2)",
			shift.Rw(),
			ByArith())
		reading := arg.Have(
			"so a² ≡ 1 exactly when p divides b·(b + 2), that is when p divides b or b + 2",
			"a * a ≡ 1 (mod p) ⇔ p ∣ b ∨ p ∣ b + 2",
			By(
				prime,
				square,
				nat_congruence.OffsetIffDivides.At(one, arg.TermAs[Nat]("b * (b + 2)"), p),
				nat_congruence.CongDef.At(arg.TermAs[Nat]("a * a"), one, p),
				nat_congruence.CongDef.At(one, arg.TermAs[Nat]("1 + b * (b + 2)"), p),
				EuclidLemma.At(p, b, arg.TermAs[Nat]("b + 2"))))
		arg.Iff()
		arg.Forward(
			"b lies below p and b + 2 at most at p, so p divides b only at 0 and b + 2 only at p",
			func(c *Argument, unit Fact) {
				c.Show(
					"so a is 1 or p − 1",
					ByArith(
						bounds,
						shift,
						reading,
						unit,
						nat_divides.DividesLessEq.At(p, b),
						nat_divides.DividesLessEq.At(p, c.TermAs[Nat]("b + 2"))))
			})
		arg.Backward(
			"a = 1 makes b = 0 and a = p − 1 makes b + 2 = p, both divisible by p",
			func(c *Argument, ends Fact) {
				cases := c.Have(
					"b is 0 or b + 2 is p",
					"b = 0 ∨ b + 2 = p",
					ByArith(bounds, shift, ends))
				c.Show(
					"p divides 0 and p",
					By(reading, cases, nat_divides.DividesZero.At(p), nat_divides.DividesRefl.At(p)))
			})
	}),
})}

// SquaresDistinctModPrime — the squares of 0, 1, …, (p − 1)/2 are pairwise
// incongruent modulo a prime p: if y ≤ x, then p divides x² − y² =
// (x − y)(x + y), hence one of the factors, and both lie below p.
var SquaresDistinctModPrime = squaresDistinctModPrimeThm{family.Add(registry.ProofEntry{
	Name: "SquaresDistinctModPrime",
	Key:  "prop_d8dedcb5e5ad8ba5",
	Build: family.Sections(
		Statement{
			Binders: "∀p x y:num.",
			Hypotheses: []string{
				"nat_prime(p)",
				"2 * x < p",
				"2 * y < p",
				"x * x ≡ y * y (mod p)",
			},
			Conclusion: "x = y",
		},
		func(ctx *Script, headline string) *GoalStackNode {
			ordered := ctx.Lemma(
				Statement{
					Binders: "∀p x y:num.",
					Hypotheses: []string{
						"nat_prime(p)",
						"2 * x < p",
						"y ≤ x",
						"x * x ≡ y * y (mod p)",
					},
					Conclusion: "x = y",
				},
				func(a *Argument, p, x, y *Expr[Nat], prime, small, below, congruent Fact) {
					sum := a.TermAs[Nat]("x + y")
					d, gap := a.ObtainAs[Nat](
						"x exceeds y by some d",
						"∃d:num. x = y + d",
						By(below, nat_order.LessEqExists.At(x, y)))
					difference := a.Have(
						"the difference of the squares is d·(x + y)",
						"x * x = y * y + d * (x + y)",
						ByArith(Scaled(sum, gap)))
					ySquare, gapTimesSum := a.TermAs[Nat]("y * y"), a.TermAs[Nat]("d * (x + y)")
					divides := a.Have(
						"p divides the difference of the squares",
						"p ∣ d * (x + y)",
						By(
							difference,
							congruent,
							nat_congruence.CongDef.At(a.TermAs[Nat]("x * x"), ySquare, p),
							nat_congruence.CongDef.At(ySquare, a.TermAs[Nat]("y * y + d * (x + y)"), p),
							nat_congruence.OffsetIffDivides.At(ySquare, gapTimesSum, p)))
					factor := a.Have(
						"so, being prime, p divides d or x + y",
						"p ∣ d ∨ p ∣ x + y",
						By(prime, divides, EuclidLemma.At(p, d, sum)))
					a.Show(
						"both lie below p, so the one p divides is 0",
						factor.SplitDisj(
							LeftHolds(
								"p ∣ d with d ≤ x < p: d = 0",
								Given(func(b *Argument, dDivisible Fact) {
									b.Show(
										"a multiple of p below p is 0",
										ByArith(small, gap, dDivisible, nat_divides.DividesLessEq.At(p, d)))
								})),
							RightHolds(
								"p ∣ x + y with x + y ≤ 2x < p: x = y = 0",
								Given(func(b *Argument, sumDivisible Fact) {
									b.Show(
										"a multiple of p below p is 0",
										ByArith(small, below, sumDivisible, nat_divides.DividesLessEq.At(p, sum)))
								}))))
				})

			return ctx.Theorem(headline,
				func(a *Argument, p, x, y *Expr[Nat], prime, xSmall, ySmall, congruent Fact) {
					a.Cases(a.TermAs[Bool]("y ≤ x"))
					a.When(
						"y ≤ x",
						func(b *Argument, below Fact) {
							b.Show(
								"the ordered case as it stands",
								By(prime, xSmall, below, congruent, At(ordered, p, x, y)))
						})
					a.Otherwise(
						"x < y: the ordered case with the roles exchanged",
						func(b *Argument, above Fact) {
							xSquare, ySquare := b.TermAs[Nat]("x * x"), b.TermAs[Nat]("y * y")
							b.Show(
								"the congruence reads both ways, as an equation of residues",
								By(
									prime,
									ySmall,
									above,
									congruent,
									At(ordered, p, y, x),
									nat_order.NotLessEq.At(y, x),
									nat_order.LessEqOfLessThan.At(x, y),
									nat_congruence.CongDef.At(xSquare, ySquare, p),
									nat_congruence.CongDef.At(ySquare, xSquare, p)))
						})
				})
		}),
})}
