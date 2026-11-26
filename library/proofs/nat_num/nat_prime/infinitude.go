// infinitude.go — the chapter's second subject, the infinitude of the
// primes: the two facts Euclid's argument turns on — the one about
// factorials, and the one that hands the argument its prime — and then
// the argument itself, with the bound it delivers.
//
// Three parts, marked by banners:
//
// - A prime divides n! exactly when it is at most n
// - Every number past 1 has a prime divisor, and a nonzero number finitely many
// - Past any number there is a prime, and the bound is n! + 1

package nat_prime

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// A prime divides n! exactly when it is at most n
// ---------------------------------------------------------------------------
//
// n! is the product of 1, …, n, so a prime at most n is one of its
// factors outright; that a prime NOT at most n misses n! is the
// substance, and it is Euclid's lemma applied n times over — a prime
// that divides a product divides a factor, and every factor of n! is
// too small.

// PrimeDividesFactorial — by induction on n, with the prime fixed
// throughout.
//
//	base  0! is 1, and a prime is neither 1 (the only divisor of 1)
//	      nor at most 0.
//	step  (n+1)! is (n+1) · n!, so by Euclid's lemma a prime divides it
//	      exactly when it divides one of the two factors. Dividing n+1
//	      puts it at most n+1, as a divisor of a nonzero number is at
//	      most it; dividing n! puts it at most n, by the induction
//	      hypothesis. Conversely a prime at most n+1 is n+1 itself — a
//	      factor — or at most n, hence a divisor of n! by the induction
//	      hypothesis, and a divisor of a factor divides the product.
var PrimeDividesFactorial = primeDividesFactorialThm{family.Add(registry.ProofEntry{
	Name: "PrimeDividesFactorial",
	Key:  "prop_fffa928a5229d753",
	Build: family.Theorem(
		Statement{
			Binders: "∀p n:num.",
			Hypotheses: []string{
				"nat_prime(p)",
			},
			Conclusion: "p ∣ factorial(n) ⇔ p ≤ n",
		},
		func(a *Argument, p, n *Expr[Nat], prime Fact) {
			// The two factors of (n+1)!, spelled over the statement's n: the
			// induction keeps the name, so inside the step they read at the
			// step's own point.
			sucN, factN := a.TermAs[Nat]("suc(n)"), a.TermAs[Nat]("factorial(n)")

			a.Induct(n)
			a.Base(
				"n = 0: 0! is 1, and a number at least 2 is neither 1 nor at most 0",
				func(b *Argument) {
					// ↦ p₀ = 1 ⇔ p₀ ≤ 0: 0! is 1, whose only divisor is 1.
					b.Show(
						"both sides are false of a number at least 2",
						Simp(Fwd(nat_arith.Factorial), Fwd(nat_divides.DividesOne)),
						ByArith(prime, PrimeAtLeastTwo.At(p)))
				})
			a.Step(
				"n → suc n: (n+1)! is the product suc n₀ · n₀!, and a prime meets a product through a factor",
				func(b *Argument, ih Fact) {
					// ↦ p₀ ∣ suc n₀ · factorial n₀ ⇔ p₀ ≤ suc n₀
					b.Do(Simp(Fwd(nat_arith.Factorial)))

					b.Iff()
					b.Forward(
						"Euclid's lemma sends p₀ into one of the two factors, and either landing bounds it",
						func(c *Argument, divProd Fact) {
							either := c.Have(
								"p₀ divides suc n₀ or n₀!",
								"p ∣ suc(n) ∨ p ∣ factorial(n)",
								By(
									prime,
									divProd,
									EuclidLemma.At(p, sucN, factN))) // p₀ ∣ suc n₀ · factorial n₀ ⇔ p₀ ∣ suc n₀ ∨ p₀ ∣ factorial n₀

							c.Show(
								"a divisor of the nonzero suc n₀ is at most it; a "+
									"divisor of n₀! is at most n₀ by the induction hypothesis",
								ByArith(
									ih,
									either,
									nat_divides.DividesLessEq.At(p, sucN))) // p₀ ∣ suc n₀ ⇒ p₀ ≤ suc n₀ ∨ suc n₀ = 0
						})
					b.Backward(
						"a prime at most suc n₀ is suc n₀ itself or at most n₀, and either way divides a factor",
						func(c *Argument, le Fact) {
							c.Cases(c.Term("p ≤ n"))
							c.When(
								"p₀ ≤ n₀: the induction hypothesis makes p₀ a divisor of n₀!, the right-hand factor",
								func(d *Argument, leN Fact) {
									d.Show(
										"a divisor of one factor divides the product, read "+
											"from the n₀! side, and commutativity turns it around",
										By(
											Normalized,
											leN,
											ih,
											nat_divides.DividesMul.At(p, factN, sucN), // p₀ ∣ factorial n₀ ⇒ p₀ ∣ factorial n₀ · suc n₀
											nat_arith.MulSym.At(factN, sucN)))         // factorial n₀ · suc n₀ = suc n₀ · factorial n₀
								})
							c.Otherwise(
								"p₀ is suc n₀ itself, the left-hand factor",
								func(d *Argument, notLeN Fact) {
									isSuc := d.Have(
										"at most suc n₀ but not at most n₀ is suc n₀ exactly",
										"p = suc(n)",
										ByArith(notLeN, le))

									// isSuc rewrites p₀ into suc n₀ inside DividesRefl's instance,
									// and the leaf then closes under normalization alone.
									d.Show(
										"p₀ divides itself, hence the product it is a factor of",
										By(
											Normalized,
											isSuc,
											nat_divides.DividesRefl.At(p), // p₀ ∣ p₀
											nat_divides.DividesMul.At(p, sucN, factN))) // p₀ ∣ suc n₀ ⇒ p₀ ∣ suc n₀ · factorial n₀
								})
						})
				})
		}),
})}

// ---------------------------------------------------------------------------
// Every number past 1 has a prime divisor, and a nonzero number finitely many
// ---------------------------------------------------------------------------
//
// The step Euclid's argument opens with: whatever n! + 1 is, some prime
// divides it. The proof is the textbook descent — a number past 1 is
// prime, or it has a proper divisor, which is smaller and past 1 too, so
// a prime dividing the divisor divides it — and a descent is a
// course-of-values induction, with "past 1" carried inside the
// predicate: 1 has no prime divisor, and 0 — which every prime divides
// — would need one NAMED, and the chapter never names a prime. A nonzero
// number has only finitely many prime divisors, each being at most it.

// PrimeFactor — course-of-values induction on n, with the step a two-way
// case on whether n is prime.
//
//	prime      n is its own prime divisor.
//	composite  n is neither 1 nor prime, so by OneOrPrime some divisor d
//	           of n is neither 1 nor n. It is not 0 either — 0 divides
//	           only 0 — so d is past 1; and a divisor of a nonzero number
//	           is at most it, so d ≠ n makes d < n. The induction
//	           hypothesis at d gives a prime dividing d, hence n.
var PrimeFactor = primeFactorThm{family.Add(registry.ProofEntry{
	Name: "PrimeFactor",
	Key:  "prop_b077d88660badfd0",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num.",
			Hypotheses: []string{
				"1 < n",
			},
			Conclusion: "∃p:num. nat_prime(p) ∧ p ∣ n",
		},
		func(a *Argument) {
			// No binder is fixed: the headline IS the principle's
			// conclusion ∀n. P(n), so the principle is cited bare and P is
			// read off it. ByInduction installs the principle as its file
			// states it, so one elimination closes, as nat_gcd's existence
			// proof does. The Normalized that proof adds after the principle
			// is inert here: the step's obligation meets the proved case
			// without it.
			a.Show(
				"course-of-values induction on n, with the descent to a proper divisor as the step",
				ByInduction(nat_order.StrongInduction,
					Case(
						"granted a prime divisor for every number past 1 below n, one is "+
							"found for n: n itself when prime, else one of a proper divisor's",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]()   // the step's own point
							below := b.Assume()   // every m < n₀ past 1 has a prime divisor
							pastOne := b.Assume() // 1 < n₀

							b.Cases(b.Term("nat_prime(n)"))
							b.When(
								"n₀ is prime: it is its own prime divisor",
								func(c *Argument, prime Fact) {
									c.Take(n)
									c.Show(
										"n₀ divides itself",
										By(prime, nat_divides.DividesRefl.At(n))) // n₀ ∣ n₀
								})
							b.Otherwise(
								"n₀ is composite: a proper divisor d₀ is smaller and past 1, and the prime below it serves",
								func(c *Argument, notPrime Fact) {
									notOne := c.Have(
										"past 1, n₀ is not 1",
										"n ≠ 1",
										ByArith(pastOne))

									d, proper := c.ObtainAs[Nat](
										"neither 1 nor prime, n₀ fails the divisor condition that "+
											"OneOrPrime reads primality as — some divisor is neither 1 nor n₀",
										"∃d:num. d ∣ n ∧ d ≠ 1 ∧ d ≠ n",
										By(notPrime, notOne, OneOrPrime.At(n))) // n₀ = 1 ∨ nat_prime(n₀) ⇔ every divisor of n₀ is 1 or n₀

									nonzero := c.Have(
										"d₀ is not 0: 0 divides only 0, and n₀ is past 1",
										"d ≠ 0",
										By(pastOne, proper, nat_divides.ZeroDivides.At(n))) // 0 ∣ n₀ ⇒ n₀ = 0

									between := c.Have(
										"so d₀ is past 1; and a divisor of the nonzero n₀ is at most it, which d₀ ≠ n₀ sharpens to d₀ < n₀",
										"1 < d ∧ d < n",
										ByArith(nonzero, pastOne, proper, nat_divides.DividesLessEq.At(d, n))) // d₀ ∣ n₀ ⇒ d₀ ≤ n₀ ∨ n₀ = 0

									p, primeBelow := c.ObtainAs[Nat](
										"the induction hypothesis at d₀ hands over a prime dividing d₀",
										"∃p:num. nat_prime(p) ∧ p ∣ d",
										By(below.At(d), between))

									c.Take(p)
									c.Show(
										"p₀ divides d₀, which divides n₀",
										By(primeBelow, proper, nat_divides.DividesTrans.At(p, d, n))) // p₀ ∣ d₀ ∧ d₀ ∣ n₀ ⇒ p₀ ∣ n₀
								})
						}))))
		}),
})}

// PrimeDivisorsFinite — a nonzero number has finitely many prime divisors:
// each is at most the number.
var PrimeDivisorsFinite = primeDivisorsFiniteThm{family.Add(registry.ProofEntry{
	Name: "PrimeDivisorsFinite",
	Key:  "prop_14ce07c16da55471",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"n ≠ 0",
		},
		Conclusion: "finite({p:num | nat_prime(p) ∧ p ∣ n})",
	}, func(a *Argument, n *Expr[Nat], nonzero Fact) {
		a.Show(
			"they lie among the numbers at most n, a finite set",
			BySets(
				nonzero,
				finite_set.FiniteSubset.At(
					a.TermAs[Set[Nat]]("{p:num | nat_prime(p) ∧ p ∣ n}"),
					a.TermAs[Set[Nat]]("{x:num | x ≤ n}")),
				num_segment.FiniteBelow,
				nat_divides.DividesLessEq))
	}),
})}

// ---------------------------------------------------------------------------
// Past any number there is a prime, and the bound is n! + 1
// ---------------------------------------------------------------------------
//
// Euclid's argument, with the bound it delivers: some prime divides
// n! + 1, and no prime at most n can. The bound is STATED rather than
// hidden in an ∃ because a stated bound can be cited, where "a larger
// prime exists" cannot be sized. The part closes with the same fact
// read as a set being infinite — the chapter's one member said in the
// vocabulary of sets.

// EuclidBound — take the prime PrimeFactor finds in n! + 1.
//
//	at most n! + 1  a divisor of a nonzero number is at most it.
//	past n          were p ≤ n, p would divide n! by
//	                PrimeDividesFactorial, so cancelling n! out of
//	                p ∣ n! + 1 would leave p ∣ 1, putting p at most 1 —
//	                and a prime is at least 2.
var EuclidBound = euclidBoundThm{family.Add(registry.ProofEntry{
	Name: "EuclidBound",
	Key:  "prop_5039c218f273d21c",
	Build: family.Theorem(
		"∀n:num. ∃p:num. nat_prime(p) ∧ n < p ∧ p ≤ factorial(n) + 1",
		func(a *Argument, n *Expr[Nat]) {
			// Euclid's number, and its two summands.
			euclidNumber, factN, one :=
				a.TermAs[Nat]("factorial(n) + 1"), a.TermAs[Nat]("factorial(n)"), a.Ctx().Nat(1)

			pastOne := a.Have(
				"n₀! + 1 is past 1, as n₀! is not 0",
				"1 < factorial(n) + 1",
				ByArith(nat_arith.FactorialNonzero.At(n))) // factorial n₀ ≠ 0

			prime, primeDiv := a.ObtainAs[Nat](
				"so some prime divides it",
				"∃p:num. nat_prime(p) ∧ p ∣ factorial(n) + 1",
				By(
					pastOne,
					PrimeFactor.At(euclidNumber))) // 1 < factorial n₀ + 1 ⇒ ∃p. nat_prime(p) ∧ p ∣ factorial n₀ + 1
			p := prime

			a.Take(p)
			bound := a.Have(
				"a divisor of the nonzero n₀! + 1 is at most it",
				"p ≤ factorial(n) + 1",
				ByArith(
					primeDiv,
					// p₀ ∣ factorial n₀ + 1 ⇒ p₀ ≤ factorial n₀ + 1 ∨ factorial n₀ + 1 = 0
					nat_divides.DividesLessEq.At(p, euclidNumber)))

			pastN := a.Unless(
				a.Term("p ≤ n"),
				"p₀ ≤ n₀ is absurd: p₀ would then divide n₀!, hence 1, and no prime does",
				Given(func(b *Argument, le Fact) {
					divFact := b.Have(
						"a prime at most n₀ divides n₀!",
						"p ∣ factorial(n)",
						By(le, primeDiv, PrimeDividesFactorial.At(p, n))) // nat_prime(p₀) ⇒ (p₀ ∣ factorial n₀ ⇔ p₀ ≤ n₀)

					divOne := b.Have(
						"cancelling n₀! out of p₀ ∣ n₀! + 1 leaves p₀ ∣ 1",
						"p ∣ 1",
						By(
							primeDiv,
							divFact,
							// p₀ ∣ factorial n₀ ⇒ (p₀ ∣ factorial n₀ + 1 ⇔ p₀ ∣ 1)
							nat_divides.DividesAddCancel.At(p, factN, one)))

					// The divisor of 1 is read as a BOUND, not as p₀ = 1: an equation
					// between a variable and a numeral resident beside 2 ≤ p₀ is a
					// shape the closer's conditioning stage rewrites badly today, and
					// the bound is the same law the upper bound above used.
					b.Show(
						"a divisor of 1 is at most 1, and a prime is at least 2",
						ByArith(
							divOne,
							primeDiv,
							nat_divides.DividesLessEq.At(p, one), // p₀ ∣ 1 ⇒ p₀ ≤ 1 ∨ 1 = 0
							PrimeAtLeastTwo.At(p)))               // nat_prime(p₀) ⇒ 2 ≤ p₀
				}))

			a.Show(
				"p₀ is prime, past n₀, and at most n₀! + 1",
				ByArith(primeDiv, pastN, bound))
		}),
})}

// PrimesInfinite — EuclidBound, read as a set being infinite.
//
// Were the primes a finite set, some interval 0 .. n would hold them
// all; Euclid's prime past n lies in the set, hence in the interval,
// hence at or below n.
var PrimesInfinite = primesInfiniteThm{family.Add(registry.ProofEntry{
	Name: "PrimesInfinite",
	Key:  "prop_80d9e78707fc9c92",
	Build: family.Theorem("infinite({p:num | nat_prime(p)})",
		func(a *Argument) {
			primes := a.TermAs[Set[Nat]]("{p:num | nat_prime(p)}")

			a.Do(Unfold(finite_set.InfiniteDef)) // ↦ ¬finite({p | nat_prime(p)})
			finite := a.SupposeNot()

			n, held := a.ObtainAs[Nat](
				"a finite set of numbers is held by some interval from 0",
				"∃n:num. {p:num | nat_prime(p)} ⊆ 0 .. n",
				By(
					finite,
					// finite({p | nat_prime(p)}) ⇔ ∃n. {p | nat_prime(p)} ⊆ 0 .. n
					num_segment.FiniteIffBounded.At(primes)))

			// Euclid's prime past n₀.
			_, pastN := a.UnpackAs[Nat](EuclidBound.At(n)) // nat_prime(p₀) ∧ n₀ < p₀ ∧ p₀ ≤ factorial(n₀) + 1

			under := a.Have(
				"being prime, p₀ lies in the set, hence in the interval, hence at or below n₀",
				"p ≤ n",
				BySets(held, pastN))

			a.Show(
				"and p₀ is past n₀",
				ByArith(pastN, under))
		}),
})}
