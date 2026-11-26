// factorization.go — the chapter's third subject, factorization into
// primes. It opens with Euclid's lemma extended from two factors to a
// list of them: the step on which unique factorization stands, since it
// is what finds a prime of one factorization among the factors of
// another. The existence half follows: every nonzero number is the
// product of a list of primes. Then comes the step unique
// factorization's induction takes: a prime of one factorization is
// found in the other, brought to its front, and cancelled. The
// uniqueness half closes the file: two lists of primes with the same
// product are rearrangements of each other.
//
// The lists here hold numbers, so a list definition is cited at that
// instance (`list.ListMemberDef.Inst[Nat]()`), and a list constant built in a
// body is spelled at it too (`nil⟨A:num⟩`): the chapter's vocabulary has
// no row for the list constructors, and a bare nil reads at a type
// variable.

package nat_prime

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/list"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// PrimeDividesListProduct — by induction on the list, with the prime
// fixed throughout.
//
//	base  the empty product is 1, whose only divisor is 1, and a prime is
//	      at least 2; nothing is a member of nil. Both sides are false.
//	step  the product of cons(h, t) is h · list_product(t), so by Euclid's
//	      lemma a prime divides it exactly when it divides h or the
//	      product of t. The induction hypothesis reads the second as a
//	      member of t that the prime divides, and list_member's clause at cons
//	      reads a member of cons(h, t) as h itself or a member of t.
var PrimeDividesListProduct = primeDividesListProductThm{family.Add(registry.ProofEntry{
	Name: "PrimeDividesListProduct",
	Key:  "prop_e7cb9d3e5931dae7",
	Build: family.Theorem(
		Statement{
			Binders: "∀p:num. ∀l:list(num).",
			Hypotheses: []string{
				"nat_prime(p)",
			},
			Conclusion: "p ∣ list_product(l) ⇔ ∃q:num. list_member(q, l) ∧ p ∣ q",
		},
		func(a *Argument, p *Expr[Nat], l *Expr[list.List[Nat]], prime Fact) {
			membership := list.ListMemberDef.Inst[Nat]()

			a.Induct(l)
			a.Base(
				"l = nil: the empty product is 1, which no number at least 2 divides, and nil has no members",
				func(b *Argument) {
					// ↦ p₀ = 1 ⇔ ∃q. ⊥ ∧ p₀ ∣ q
					b.Show(
						"both sides are false of a number at least 2",
						Simp(Fwd(list.ListProductClauses), Fwd(nat_divides.DividesOne), Fwd(membership)),
						ByArith(prime, PrimeAtLeastTwo.At(p)))
				})
			a.Step(
				"l = cons(h, t): the product is h · list_product(t), and a prime meets a product through a factor",
				func(b *Argument, ih Fact) {
					parts := b.StepArgs("h", "t")
					head, tailProduct := ext.As[Nat](parts[0]), b.TermAs[Nat]("list_product(t)")

					// ↦ p₀ ∣ h · list_product(t) ⇔ ∃q. list_member(q, cons(h, t)) ∧ p₀ ∣ q
					b.Do(Simp(Fwd(list.ListProductClauses)))

					split := b.Have(
						"by Euclid's lemma, p₀ divides the product exactly "+
							"when it divides the head or the product of the tail",
						"p ∣ h * list_product(t) ⇔ p ∣ h ∨ p ∣ list_product(t)",
						By(
							prime,
							// p₀ = 0 ∨ p₀ = 1 ∨ nat_prime(p₀) ⇒ (p₀ ∣ h·list_product(t) ⇔ p₀ ∣ h ∨ p₀ ∣ list_product(t))
							EuclidLemma.At(p, head, tailProduct)))

					b.Show(
						"the hypothesis reads the tail's disjunct as a member of t, and "+
							"list_member's clause makes the head or a member of t a member of cons(h, t)",
						By(ih, split, membership))
				})
		}),
})}

// FactorizationExists — course-of-values induction on n, with the step a
// two-way case on whether n is 1.
//
//	n = 1   the empty list serves: its product is 1, and it has no
//	        members.
//	n > 1   some prime p divides n; write n = p·k. The cofactor k is not
//	        0, as n is not, and it is below n, as p is at least 2. The
//	        hypothesis at k gives a list of primes with product k, and p
//	        put in front of it is a list of primes with product p·k = n.
var FactorizationExists = factorizationExistsThm{family.Add(registry.ProofEntry{
	Name: "FactorizationExists",
	Key:  "prop_1bf5fed27fc8b5e3",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num.",
			Hypotheses: []string{
				"n ≠ 0",
			},
			Conclusion: "∃l:list(num). (∀q:num. list_member(q, l) ⇒ nat_prime(q)) ∧ list_product(l) = n",
		},
		func(a *Argument) {
			// No binder is fixed: the headline IS the principle's
			// conclusion ∀n. P(n), whose P the induction below reads off it.

			membership := list.ListMemberDef.Inst[Nat]()

			a.Show(
				"course-of-values induction on n, with the descent to the cofactor of a prime divisor as the step",
				ByInduction(nat_order.StrongInduction,
					Case(
						"granted a list of primes for each nonzero number below n, n gets one: "+
							"the empty list at 1, else a prime divisor before its cofactor's list",
						Derive(func(b *Argument) {
							n := b.FixAs[Nat]()   // the step's own point
							below := b.Assume()   // every nonzero m < n₀ is the product of a list of primes
							nonzero := b.Assume() // n₀ ≠ 0

							b.Cases(b.Term("n = 1"))
							b.When(
								"n₀ = 1: the empty list has product 1 and no members",
								func(c *Argument, unit Fact) {
									c.Take(c.TermAs[list.List[Nat]]("nil⟨A:num⟩"))
									// ↦ (∀q. ⊥ ⇒ nat_prime(q)) ∧ 1 = n₀
									c.Show(
										"nothing is a member of nil, and the empty product is 1",
										Simp(Fwd(list.ListProductClauses), Fwd(membership)),
										By(unit))
								})
							b.Otherwise(
								"n₀ is past 1: a prime divisor p₀ put in front of a list for its cofactor",
								func(c *Argument, notOne Fact) {
									found, primeDivides := c.ObtainAs[Nat](
										"neither 0 nor 1, n₀ is past 1, so some prime divides it",
										"∃p:num. nat_prime(p) ∧ p ∣ n",
										ByArith(nonzero, notOne, PrimeFactor.At(n))) // 1 < n₀ ⇒ ∃p. nat_prime(p) ∧ p ∣ n₀
									p := found

									k, product := c.ObtainAs[Nat](
										"n₀ is p₀ taken k₀ times",
										"∃k:num. n = p * k",
										By(primeDivides, nat_divides.DividesFactor.At(p, n))) // p₀ ∣ n₀ ⇔ ∃x. n₀ = p₀ * x

									cofactorNonzero := c.Have(
										"k₀ is not 0, or p₀·k₀ = n₀ would be",
										"k ≠ 0",
										By(Normalized, nonzero, product, nat_arith.MulEqZero.At(p, k))) // p₀ * k₀ = 0 ⇔ p₀ = 0 ∨ k₀ = 0

									smaller := c.Have(
										"k₀ = k₀·1 is below k₀·p₀ = n₀, as k₀ is not 0 and the prime p₀ is past 1",
										"k < n",
										ByArith(
											cofactorNonzero,
											product,
											primeDivides,
											PrimeAtLeastTwo.At(p), // nat_prime(p₀) ⇒ 2 ≤ p₀
											nat_order.LessThanMulCancel.At(k, c.Ctx().Nat(1), p))) // k₀ * 1 < k₀ * p₀ ⇔ k₀ ≠ 0 ∧ 1 < p₀

									_, tailFactorization := c.Obtain(
										"the hypothesis at k₀ hands over a list t₀ of primes with product k₀",
										"∃t:list(num). (∀q:num. list_member(q, t) ⇒ nat_prime(q)) ∧ list_product(t) = k",
										By(below.At(k), smaller, cofactorNonzero))

									c.Take(c.TermAs[list.List[Nat]]("cons(p, t)"))
									// ↦ (∀q. q = p₀ ∨ list_member(q, t₀) ⇒ nat_prime(q)) ∧ p₀ * list_product(t₀) = n₀
									c.Show(
										"a member of cons(p₀, t₀) is p₀ or a member of t₀, prime either way, and the product is p₀·k₀ = n₀",
										Simp(Fwd(list.ListProductClauses), Fwd(membership)),
										By(product, primeDivides, tailFactorization))
								})
						}))))
		}),
})}

// ListProductCancelPrime — a straight chain through p's membership in m.
// p divides p·k, which is the product of m, so it divides a member of m;
// that member is a prime, so it is p itself, and p can be brought to the
// front of m, a rest r following. A rearrangement keeps the product, so
// p·k is p times the product of r, and p, being at least 2, cancels: the
// product of r is k. A member of r is a member of cons(p, r), hence of
// m, hence prime.
var ListProductCancelPrime = listProductCancelPrimeThm{family.Add(registry.ProofEntry{
	Name: "ListProductCancelPrime",
	Key:  "prop_4ec39961665d908d",
	Build: family.Theorem(
		Statement{
			Binders: "∀p k:num. ∀m:list(num).",
			Hypotheses: []string{
				"nat_prime(p)",
				"∀q:num. list_member(q, m) ⇒ nat_prime(q)",
				"p * k = list_product(m)",
			},
			Conclusion: "∃r:list(num). " +
				"    list_permutation(m, cons(p, r)) ∧ " +
				"    (∀q:num. list_member(q, r) ⇒ nat_prime(q)) ∧ " +
				"    list_product(r) = k",
		},
		func(a *Argument, p, k *Expr[Nat], m *Expr[list.List[Nat]], prime, primeMembers, products Fact) {

			divides := a.Have(
				"p₀ divides p₀·k₀, its own multiple, which is the product of m₀",
				"p ∣ list_product(m)",
				By(Normalized, products, nat_divides.DividesOwnMultiple.At(p, k)))

			divided, dividesFound := a.ObtainAs[Nat](
				"a prime dividing the product of a list divides one of its members",
				"∃q:num. list_member(q, m) ∧ p ∣ q",
				By(
					divides,
					prime,
					// nat_prime(p₀) ⇒ (p₀ ∣ list_product(m₀) ⇔ ∃q. list_member(q, m₀) ∧ p₀ ∣ q)
					PrimeDividesListProduct.At(p, m)))

			member := a.Have(
				"that member is a prime too, and a prime dividing a prime is that prime: p₀ is a member of m₀",
				"list_member(p, m)",
				By(
					Normalized,
					dividesFound,
					prime,
					primeMembers.At(divided),
					PrimeDividesPrime.At(p, divided))) // nat_prime(p₀) ∧ nat_prime(q₀) ⇒ (p₀ ∣ q₀ ⇔ p₀ = q₀)

			rest, rearranged := a.ObtainAs[list.List[Nat]](
				"a member of m₀ can be brought to its front, a rest r₀ following",
				"∃r:list(num). list_permutation(m, cons(p, r))",
				By(
					member,
					// list_member(p₀, m₀) ⇒ ∃r. list_permutation(m₀, cons(p₀, r))
					list.PermutationMoveToFront.At(p, m)))
			r := rest
			front := a.TermAs[list.List[Nat]]("cons(p, r)")

			frontProduct := a.Have(
				"a rearrangement keeps the product, and the product of cons(p₀, r₀) is p₀ times that of r₀",
				"list_product(m) = p * list_product(r)",
				By(
					Normalized,
					rearranged,
					// list_permutation(m₀, cons(p₀, r₀)) ⇒ list_product(m₀) = list_product(cons(p₀, r₀))
					list.PermutationListProduct.At(m, front),
					list.ListProductClauses))

			restProduct := a.Have(
				"p₀·k₀ is p₀ times the product of r₀, and p₀, not 0, cancels",
				"list_product(r) = k",
				ByArith(
					prime,
					PrimeAtLeastTwo.At(p),
					frontProduct,
					products,
					// p₀ * list_product(r₀) = p₀ * k₀ ⇔ p₀ = 0 ∨ list_product(r₀) = k₀
					nat_arith.MulEqLCancel.At(p, a.TermAs[Nat]("list_product(r)"), k)))

			restPrime := a.Have(
				"a member of r₀ is a member of cons(p₀, r₀), hence of m₀, hence prime",
				"∀q:num. list_member(q, r) ⇒ nat_prime(q)",
				// The member is fixed so that the rearrangement's membership
				// law is cited at it.
				Derive(func(b *Argument) {
					q := b.FixAs[Nat]()
					inRest := b.Assume()
					b.Show(
						"list_member's clause at cons puts it in cons(p₀, "+
							"r₀), and the rearrangement m₀ has the same members",
						By(
							inRest,
							rearranged,
							primeMembers.At(q),
							// list_permutation(m₀, cons(p₀, r₀)) ⇒ (list_member(q₀, m₀) ⇔ list_member(q₀, cons(p₀, r₀)))
							list.PermutationMember.At(q, m, front),
							list.ListMemberDef.Inst[Nat]()))
				}))

			a.Take(r)
			a.Show(
				"r₀ is the rest: m₀ is a rearrangement of p₀ in front "+
					"of it, its members are primes, and its product is k₀",
				By(rearranged, restPrime, restProduct))
		}),
})}

// FactorizationUnique — by induction on l, for every m at once.
//
//	base  the product of m is the empty product, 1, so m is nil: a head
//	      in front would be a prime whose product with the rest's is 1,
//	      making it 1 itself, and a prime is at least 2. nil is a
//	      permutation of itself.
//	step  at cons(p, t) the product is p times that of t; that is the
//	      product of m, so the prime p cancels from m, leaving a rest r
//	      of primes with the product of t. The hypothesis, held for
//	      every list, is used at r: t is a permutation of r. The common
//	      head p keeps cons(p, t) one of cons(p, r), and that is m
//	      rearranged.
var FactorizationUnique = factorizationUniqueThm{family.Add(registry.ProofEntry{
	Name: "FactorizationUnique",
	Key:  "prop_cbd0708a94922ca6",
	Build: family.Theorem(
		Statement{
			Binders: "∀l m:list(num).",
			Hypotheses: []string{
				"∀q:num. list_member(q, l) ⇒ nat_prime(q)",
				"∀q:num. list_member(q, m) ⇒ nat_prime(q)",
				"list_product(l) = list_product(m)",
			},
			Conclusion: "list_permutation(l, m)",
		},
		func(a *Argument, l *Expr[list.List[Nat]]) {
			membership := list.ListMemberDef.Inst[Nat]()

			a.Induct(l)
			a.Base(
				"l = nil: a list of primes with product 1 is nil",
				func(b *Argument) {
					m := b.FixAs[list.List[Nat]]()
					given := b.Assume()
					primes := b.Have(
						"every member of m₀ is prime",
						"∀q:num. list_member(q, m) ⇒ nat_prime(q)",
						By(given))

					notNil := b.Unless(
						b.Term("m = nil"),
						"m₀ = nil: the empty list is a permutation of itself",
						Given(func(c *Argument, empty Fact) {
							c.Show(
								"the empty pair is a permutation",
								By(empty, list.PermutationNil))
						}))

					head, _, shape := b.Obtain2(
						"a list other than nil is a head h₀ in front of a tail t₀",
						"∃h:num. ∃t:list(num). m = cons(h, t)",
						By(notNil, list.Cases.At(m))) // m₀ = nil ∨ ∃h t. m₀ = cons(h, t)
					h := ext.As[Nat](head)

					headPrime := b.Have(
						"h₀ is a member of m₀, hence prime",
						"nat_prime(h)",
						By(shape, primes.At(h), membership))
					factored := b.Have(
						"h₀ times the product of t₀ is the product of m₀, which is 1",
						"h * list_product(t) = 1",
						By(Normalized, shape, given, list.ListProductClauses))

					b.Show(
						"a factor of 1 is 1 and the prime h₀ is at least 2, which cannot both hold",
						ByArith(
							headPrime,
							factored,
							// h₀ * list_product(t₀) = 1 ⇔ h₀ = 1 ∧ list_product(t₀) = 1
							nat_arith.MulEqOne.At(h, b.TermAs[Nat]("list_product(t)")),
							PrimeAtLeastTwo.At(h))) // nat_prime(h₀) ⇒ 2 ≤ h₀
				})
			a.Step(
				"l = cons(p, t): the head p cancels from m₀, and the hypothesis matches t with what is left",
				func(b *Argument, ih Fact) {
					parts := b.StepArgs("p", "t")
					p, t := ext.As[Nat](parts[0]), ext.As[list.List[Nat]](parts[1])
					whole := b.TermAs[list.List[Nat]]("cons(p, t)")
					m := b.FixAs[list.List[Nat]]()
					given := b.Assume()

					consPrimes := b.Have(
						"every member of cons(p₀, t₀) is prime",
						"∀q:num. list_member(q, cons(p, t)) ⇒ nat_prime(q)",
						By(given))
					mPrimes := b.Have(
						"so is every member of m₀",
						"∀q:num. list_member(q, m) ⇒ nat_prime(q)",
						By(given))
					factored := b.Have(
						"the product of cons(p₀, t₀), p₀ times that of t₀, is the product of m₀",
						"p * list_product(t) = list_product(m)",
						By(Normalized, given, list.ListProductClauses))
					headPrime := b.Have(
						"the head p₀ is prime",
						"nat_prime(p)",
						By(consPrimes.At(p), membership))
					tailPrimes := b.Have(
						"and so is every member of t₀, a member of cons(p₀, t₀) too",
						"∀q:num. list_member(q, t) ⇒ nat_prime(q)",
						By(consPrimes, membership))

					r, cancellation := b.ObtainAs[list.List[Nat]](
						"the prime p₀ times the product of t₀ is the product "+
							"of m₀, so p₀ cancels from m₀ against a rest r₀",
						"∃r:list(num). "+
							"    list_permutation(m, cons(p, r)) ∧ "+
							"    (∀q:num. list_member(q, r) ⇒ nat_prime(q)) ∧ "+
							"    list_product(r) = list_product(t)",
						By(
							headPrime,
							mPrimes,
							factored,
							// the cancellation at p₀, k := list_product(t₀), m₀
							ListProductCancelPrime.At(p, b.TermAs[Nat]("list_product(t)"), m)))
					front := b.TermAs[list.List[Nat]]("cons(p, r)")

					restPrimes := b.Have(
						"the members of r₀ are primes",
						"∀q:num. list_member(q, r) ⇒ nat_prime(q)",
						By(cancellation))

					tails := b.Have(
						"the hypothesis at r₀: t₀ and r₀ are lists of primes with one product",
						"list_permutation(t, r)",
						By(ih.At(r), tailPrimes, restPrimes, cancellation))
					heads := b.Have(
						"the common head p₀ keeps them a permutation",
						"list_permutation(cons(p, t), cons(p, r))",
						By(
							tails,
							// list_permutation(t₀, r₀) ⇒ list_permutation(cons(p₀, t₀), cons(p₀, r₀))
							list.PermutationCons.At(p, t, r)))
					back := b.Have(
						"the rearrangement of m₀, read backwards",
						"list_permutation(cons(p, r), m)",
						By(
							cancellation,
							// list_permutation(m₀, cons(p₀, r₀)) ⇒ list_permutation(cons(p₀, r₀), m₀)
							list.PermutationSym.At(m, front)))

					b.Show(
						"the two compose: cons(p₀, t₀) to cons(p₀, r₀) to m₀",
						By(
							heads,
							back,
							list.PermutationTrans.At(whole, front, m))) // … ∧ … ⇒ list_permutation(cons(p₀, t₀), m₀)
				})
		}),
})}
