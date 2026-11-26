// fermat.go — Fermat's little theorem: a prime p divides aᵖ - a.
//
// Two parts, marked by banners:
//
// - The p-th power is additive modulo p
// - Fermat's little theorem

package nat_prime

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/binomial"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_gcd"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The p-th power is additive modulo p
// ---------------------------------------------------------------------------
//
// Expanded by the binomial theorem, (a + b)ᵖ is aᵖ + bᵖ plus the terms
// strictly inside row p, and a prime divides every coefficient strictly
// inside its row: p divides p! = k!·(p - k)!·binomial(p, k), and neither
// factorial below p has p among its factors. The same count, at
// (2m + 1)! = m!·(m + 1)!·binomial(2m + 1, m), puts every prime of
// ⟬m + 1, 2m + 1⟧ in binomial(2m + 1, m).

// PrimeDividesBinomial — a prime divides every entry strictly inside its
// row of the triangle. p divides p!, which the factorial formula splits
// as k!·(p - k)!·binomial(p, k); by Euclid's lemma p divides one of the
// three factors, and it divides no factorial of a number below it.
var PrimeDividesBinomial = primeDividesBinomialThm{family.Add(registry.ProofEntry{
	Name: "PrimeDividesBinomial",
	Key:  "prop_334f73f62c2e51f6",
	Build: family.Theorem(Statement{
		Binders: "∀p k:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"0 < k",
			"k < p",
		},
		Conclusion: "p ∣ binomial(p, k)",
	},
		func(a *Argument, p, k *Expr[Nat], hyp Fact) {
			rest := a.TermAs[Nat]("p - k")
			within := a.Have(
				"the column lies within the row",
				"k ≤ p",
				ByArith(hyp))
			formula := a.Have(
				"p! is k!·(p - k)!·binomial(p, k)",
				"factorial(k) * factorial(p - k) * binomial(p, k) = factorial(p)",
				By(within, binomial.FactorialFormula.At(p, k)))
			whole := a.Have(
				"p divides p!",
				"p ∣ factorial(p)",
				By(hyp, nat_order.LessEqRefl.At(p), PrimeDividesFactorial.At(p, p)))
			pastK := a.Have(
				"k lies below p",
				"¬(p ≤ k)",
				ByArith(hyp))
			low := a.Have(
				"so p does not divide k!",
				"¬(p ∣ factorial(k))",
				By(hyp, pastK, PrimeDividesFactorial.At(p, k)))
			pastRest := a.Have(
				"and, k being past 0, neither does p - k",
				"¬(p ≤ p - k)",
				ByArith(hyp))
			high := a.Have(
				"so p does not divide (p - k)! either",
				"¬(p ∣ factorial(p - k))",
				By(hyp, pastRest, PrimeDividesFactorial.At(p, rest)))
			factorials := a.Have(
				"so, by Euclid's lemma, p does not divide k!·(p - k)!",
				"¬(p ∣ factorial(k) * factorial(p - k))",
				By(
					hyp,
					low,
					high,
					EuclidLemma.At(p, a.TermAs[Nat]("factorial(k)"), a.TermAs[Nat]("factorial(p - k)"))))
			a.Show(
				"and, by Euclid's lemma again, divides binomial(p, k)",
				By(
					hyp,
					formula,
					whole,
					factorials,
					EuclidLemma.At(
						p, a.TermAs[Nat]("factorial(k) * factorial(p - k)"), a.TermAs[Nat]("binomial(p, k)"))))
		}),
})}

// PrimesBetweenDivideBinomial — a prime p with m + 1 < p ≤ 2m + 1 divides
// binomial(2m + 1, m): it divides (2m + 1)! = m!·(m + 1)!·binomial(2m + 1, m)
// but neither m! nor (m + 1)!, every factor of those being smaller than p.
var PrimesBetweenDivideBinomial = primesBetweenDivideBinomialThm{family.Add(registry.ProofEntry{
	Name: "PrimesBetweenDivideBinomial",
	Key:  "prop_95ecf87abd99fb5b",
	Build: family.Theorem(Statement{
		Binders: "∀m p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"m + 1 < p",
			"p ≤ 2 * m + 1",
		},
		Conclusion: "p ∣ binomial(2 * m + 1, m)",
	},
		func(a *Argument, m, p *Expr[Nat], prime, above, below Fact) {
			top := a.TermAs[Nat]("2 * m + 1")
			mFactorial := a.TermAs[Nat]("factorial(m)")
			nextFactorial := a.TermAs[Nat]("factorial(m + 1)")
			factorials := a.Have(
				"the binomial coefficient times m!·(m + 1)! is (2m + 1)!",
				"factorial(m) * factorial(m + 1) * binomial(2 * m + 1, m) = factorial(2 * m + 1)",
				ByArith(binomial.FactorialFormula.At(top, m)))
			avoids := a.Have(
				"p exceeds m + 1, so it divides neither m! nor (m + 1)!, nor their product",
				"¬(p ∣ factorial(m) * factorial(m + 1))",
				ByArith(
					prime,
					above,
					PrimeDividesFactorial.At(p, m),
					PrimeDividesFactorial.At(p, a.TermAs[Nat]("m + 1")),
					EuclidLemma.At(p, mFactorial, nextFactorial)))
			a.Show(
				"p ≤ 2m + 1 divides (2m + 1)!, so it divides the binomial factor",
				By(
					prime,
					avoids,
					below,
					factorials,
					PrimeDividesFactorial.At(p, top),
					EuclidLemma.At(
						p,
						a.TermAs[Nat]("factorial(m) * factorial(m + 1)"),
						a.TermAs[Nat]("binomial(2 * m + 1, m)"))))
		}),
})}

// PowPrimeAdditive — raising to a prime power p is additive modulo p. The
// binomial theorem writes (a + b)ᵖ as its first term bᵖ, its last term
// aᵖ, and the terms strictly between, which p divides one by one and so
// all together.
var PowPrimeAdditive = powPrimeAdditiveThm{family.Add(registry.ProofEntry{
	Name: "PowPrimeAdditive",
	Key:  "prop_6c8217d6823027be",
	Build: family.Theorem(
		Statement{
			Binders: "∀p a b:num.",
			Hypotheses: []string{
				"nat_prime(p)",
			},
			Conclusion: "nat_pow(a + b, p) ≡ nat_pow(a, p) + nat_pow(b, p) (mod p)",
			Abbrev: Abbrev{
				{Name: "expansionTerms", Text: "λk:num. binomial(p, k) * nat_pow(a, k) * nat_pow(b, p - k)"},
			},
		},
		func(arg *Argument, p, a, b *Expr[Nat], prime Fact) {
			zero, one := arg.Ctx().Nat(0), arg.Ctx().Nat(1)
			terms := arg.TermAs[Fun[Nat, Nat]]("«expansionTerms»")
			inner := arg.TermAs[Set[Nat]]("1 .. p - 1")
			atLeastTwo := arg.Have(
				"a prime is at least 2",
				"2 ≤ p",
				By(prime, PrimeAtLeastTwo.At(p)))

			expansion := arg.Have(
				"the binomial theorem at row p",
				"nat_pow(a + b, p) = sum(0 .. p, «expansionTerms»)",
				By(binomial.Expansion.At(p, a, b)))
			first := arg.Have(
				"its first term comes off the front, leaving the terms from column 1",
				"sum(0 .. p, «expansionTerms») = "+
					"binomial(p, 0) * nat_pow(a, 0) * nat_pow(b, p - 0) + sum(1 .. p, «expansionTerms»)",
				By(nat_sum.PeelLeft.At(zero, p, terms), nat_order.ZeroLessEq.At(p)))
			pastOne := arg.Have(
				"the row reaches past column 1",
				"0 < p ∧ 1 ≤ p",
				ByArith(atLeastTwo))
			last := arg.Have(
				"and its last term off the back",
				"sum(1 .. p, «expansionTerms») = "+
					"sum(1 .. p - 1, «expansionTerms») + binomial(p, p) * nat_pow(a, p) * nat_pow(b, p - p)",
				By(pastOne, nat_sum.PeelRight.At(p, one, terms)))
			firstIs := arg.Have(
				"the first term is bᵖ",
				"binomial(p, 0) * nat_pow(a, 0) * nat_pow(b, p - 0) = nat_pow(b, p)",
				Derive(func(c *Argument) {
					corner := c.Have(
						"column 0 holds 1",
						"binomial(p, 0) = 1",
						By(binomial.Clauses))
					empty := c.Have(
						"the empty power is 1",
						"nat_pow(a, 0) = 1",
						By(nat_arith.NatPow))
					whole := c.Have(
						"and b keeps all p factors",
						"p - 0 = p",
						By(nat_monus.Sub))
					c.Do(corner.Rw(), empty.Rw(), whole.Rw())
					c.Show(
						"1 · 1 · bᵖ",
						ByArith())
				}))
			lastIs := arg.Have(
				"the last term is aᵖ",
				"binomial(p, p) * nat_pow(a, p) * nat_pow(b, p - p) = nat_pow(a, p)",
				Derive(func(c *Argument) {
					corner := c.Have(
						"the diagonal holds 1",
						"binomial(p, p) = 1",
						By(binomial.Diagonal.At(p)))
					none := c.Have(
						"b keeps no factor",
						"p - p = 0",
						By(nat_monus.SubRefl.At(p)))
					c.Do(corner.Rw(), none.Rw())
					empty := c.Have(
						"the empty power is 1",
						"nat_pow(b, 0) = 1",
						By(nat_arith.NatPow))
					c.Do(empty.Rw())
					c.Show(
						"1 · aᵖ · 1",
						ByArith())
				}))

			termwise := arg.Have(
				"p divides every term strictly inside the row",
				"∀k:num. k ∈ 1 .. p - 1 ⇒ p ∣ binomial(p, k) * nat_pow(a, k) * nat_pow(b, p - k)",
				Derive(func(c *Argument) {
					k := c.FixAs[Nat]("k")
					inside := c.Assume()
					column := c.Have(
						"k runs from 1 to p - 1",
						"1 ≤ k ∧ k ≤ p - 1",
						By(inside))
					bounds := c.Have(
						"so it lies strictly between 0 and p",
						"0 < k ∧ k < p",
						ByArith(atLeastTwo, column))
					coefficient := c.Have(
						"so p divides its coefficient",
						"p ∣ binomial(p, k)",
						By(prime, bounds, PrimeDividesBinomial.At(p, k)))
					c.Show(
						"and every multiple of it, the whole term among them",
						By(
							coefficient,
							nat_divides.DividesMul.At(p, c.TermAs[Nat]("binomial(p, k)"), c.TermAs[Nat]("nat_pow(a, k)")),
							nat_divides.DividesMul.At(
								p, c.TermAs[Nat]("binomial(p, k) * nat_pow(a, k)"), c.TermAs[Nat]("nat_pow(b, p - k)"))))
				}))
			middle := arg.Have(
				"so p divides the terms strictly inside, all together",
				"p ∣ sum(1 .. p - 1, «expansionTerms»)",
				By(termwise, nat_sum.DividesSum.At(p, terms, inner)))

			ends := arg.TermAs[Nat]("nat_pow(a, p) + nat_pow(b, p)")
			between := arg.TermAs[Nat]("sum(1 .. p - 1, «expansionTerms»)")
			both := arg.TermAs[Nat]("nat_pow(a, p) + nat_pow(b, p) + sum(1 .. p - 1, «expansionTerms»)")
			total := arg.Have(
				"(a + b)ᵖ is aᵖ + bᵖ and the terms between",
				"nat_pow(a + b, p) = nat_pow(a, p) + nat_pow(b, p) + sum(1 .. p - 1, «expansionTerms»)",
				ByArith(expansion, first, last, firstIs, lastIs))
			arg.Do(total.Rw())
			arg.Show(
				"so it lies a multiple of p from aᵖ + bᵖ",
				By(
					middle,
					nat_congruence.DistIffDivides.At(both, ends, p),
					nat_monus.DistLeftAdd.At(ends, between)))
		}),
})}

// ---------------------------------------------------------------------------
// Fermat's little theorem
// ---------------------------------------------------------------------------

// FermatLittle — for a prime p, aᵖ is congruent to a modulo p. By
// induction on a. 0ᵖ is 0, p being past 0. And (a + 1)ᵖ is aᵖ + 1ᵖ modulo
// p, the p-th power being additive there, which the induction hypothesis
// makes a + 1.
var FermatLittle = fermatLittleThm{family.Add(registry.ProofEntry{
	Name: "FermatLittle",
	Key:  "prop_6ca6f3ace99e95fc",
	Build: family.Theorem(Statement{
		Binders: "∀p a:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "nat_pow(a, p) ≡ a (mod p)",
	},
		func(arg *Argument) {
			p := arg.FixAs[Nat]("p")
			a := arg.Binder("a")

			arg.Induct(a)
			arg.Base(
				"a = 0: 0ᵖ is 0, p being past 0",
				func(b *Argument) {
					prime := b.Assume()
					nonzero := b.Have(
						"a prime is at least 2, so it is past 0",
						"p ≠ 0",
						ByArith(prime, PrimeAtLeastTwo.At(p)))
					vanishes := b.Have(
						"so 0ᵖ is 0",
						"nat_pow(0, p) = 0",
						By(nonzero, nat_arith.ZeroPow.At(p)))
					b.Do(vanishes.Rw())
					b.Show(
						"and 0 is congruent to itself",
						Derive(func(c *Argument) {
							c.Do(Unfold(nat_congruence.CongDef))
						}))
				})
			arg.Step(
				"a → suc(a)",
				func(b *Argument, ih Fact) {
					prime := b.Assume()
					a, one := b.TermAs[Nat]("a"), b.Ctx().Nat(1)
					successor := b.Have(
						"the successor is a + 1",
						"suc(a) = a + 1",
						By(nat_arith.Add1.At(a)))
					b.Do(successor.Rw())
					additive := b.Have(
						"the p-th power is additive modulo p",
						"nat_pow(a + 1, p) ≡ nat_pow(a, p) + nat_pow(1, p) (mod p)",
						By(prime, PowPrimeAdditive.At(p, a, one)))
					previous := b.Have(
						"the induction hypothesis",
						"nat_pow(a, p) ≡ a (mod p)",
						By(prime, ih))
					same := b.Have(
						"1 is congruent to itself",
						"1 ≡ 1 (mod p)",
						Derive(func(c *Argument) {
							c.Do(Unfold(nat_congruence.CongDef))
						}))
					shifted := b.Have(
						"so aᵖ + 1 is congruent to a + 1",
						"nat_pow(a, p) + 1 ≡ a + 1 (mod p)",
						By(previous, same, nat_congruence.AddCongruent.At(b.TermAs[Nat]("nat_pow(a, p)"), a, one, one, p)))
					b.Show(
						"so (a + 1)ᵖ ≡ aᵖ + 1ᵖ = aᵖ + 1 ≡ a + 1: read as remainders, the equations chain",
						By(additive, nat_arith.OnePow.At(p), shifted, b.Ctx().ConstDefNormalized("nat_cong")))
				})
		}),
})}

// FermatLittleCoprime — for a prime p not dividing a, aᵖ⁻¹ is congruent
// to 1 modulo p. aᵖ is a·aᵖ⁻¹ and a is a·1, so Fermat's little theorem
// says a·aᵖ⁻¹ ≡ a·1; and a, not a multiple of the prime p, is coprime to
// it, so it cancels.
var FermatLittleCoprime = fermatLittleCoprimeThm{family.Add(registry.ProofEntry{
	Name: "FermatLittleCoprime",
	Key:  "prop_53bdb7d4ef7519ea",
	Build: family.Theorem(Statement{
		Binders: "∀p a:num.",
		Hypotheses: []string{
			"nat_prime(p)",
			"¬(p ∣ a)",
		},
		Conclusion: "nat_pow(a, p - 1) ≡ 1 (mod p)",
	},
		func(arg *Argument, p, a *Expr[Nat], hyp Fact) {
			one := arg.Ctx().Nat(1)
			primeCoprime := arg.Have(
				"a prime is coprime to what it does not divide",
				"nat_coprime(p, a)",
				By(Normalized, hyp, PrimeCoprimeIffNotDivides.At(p)))
			nonzero := arg.Have(
				"a prime is at least 2, so it is past 0",
				"p ≠ 0",
				ByArith(hyp, PrimeAtLeastTwo.At(p)))
			power := arg.Have(
				"p is one more than p - 1, so aᵖ is a·aᵖ⁻¹",
				"nat_pow(a, p) = a * nat_pow(a, p - 1)",
				By(nonzero, nat_monus.SucOfSubOne.At(p), nat_arith.NatPow))
			scaled := arg.Have(
				"Fermat's little theorem, with a written a·1",
				"a * nat_pow(a, p - 1) ≡ a * 1 (mod p)",
				By(hyp, power, nat_arith.MulOne.At(a), FermatLittle.At(p, a)))
			arg.Show(
				"and a, coprime to p, cancels",
				By(
					scaled,
					primeCoprime,
					nat_gcd.CoprimeSym.At(p, a),
					nat_congruence.MulCancel.At(a, arg.TermAs[Nat]("nat_pow(a, p - 1)"), one, p)))
		}),
})}
