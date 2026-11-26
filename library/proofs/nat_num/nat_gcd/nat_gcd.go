// nat_gcd.go — the chapter: the greatest common divisor, defined in ℕ.
//
// Four parts, marked by banners:
//
// - That a greatest common divisor exists at all
// - What the two constants SAY
// - Coprimality depends only on a residue
// - Cancelling a coprime factor

package nat_gcd

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// That a greatest common divisor exists at all
// ---------------------------------------------------------------------------
//
// `nat_gcd` is a Hilbert choice, so the constant is well formed whatever
// is true; what has to be earned is that the thing it chooses from is
// non-empty. That is this file.
//
// The argument is Euclid's algorithm, run as an induction rather than as
// a recursion. The step passes from (a, b) to the SWAPPED pair
// (nat_mod(b, a), a): the swap is what puts the remainder — the one thing
// that shrank — into the first slot, so course-of-values induction on
// that slot carries the algorithm; and the move leaves the pair's
// common divisors untouched, which is dividesResidue (the fact
// the residue reduction already needs). The base case is a = 0, where every
// natural divides a and the pair's gcd is therefore b.
//
// Nothing here leaves ℕ, which is the point: maximality is stated by
// DIVISIBILITY (vocab.go), and the gcd of that specification is the one
// Euclid's algorithm computes. The BÉZOUT reading — the gcd as a
// ℤ-combination — is a strictly stronger statement about the same
// number, and it was the reason an earlier version of this file
// descended into ℤ: the combination's coefficients are the thing ℕ does
// not have. Nothing in the chapter above ever used them.
//
// The statement binds `a` and `b`, which the corpus-wide Argument
// receiver `a` would shadow, so the receiver is `arg`.

// ---------------------------------------------------------------------------
// gcdExists — the chapter's ε-fodder
// ---------------------------------------------------------------------------

// gcdExists is what makes `nat_gcd` mean anything: some natural is a
// common divisor of a and b that every common divisor divides. The specification
// hands this statement to the choice operator, and the chapter's
// theorems are read off the specification from there on.
//
// The induction is at the predicate "a has a gcd with EVERY b" — the b
// is quantified inside the predicate because the step recurses at the
// swapped pair (nat_mod(b, a), a): its second slot is a itself, a value the
// goal's own b never names, so the hypothesis must arrive with its ∀b
// intact.
//
// Internal: existence is scaffolding for the definition, not a fact the
// chapter's readers have any use for.
var gcdExists = gcdExistsThm{family.Add(registry.ProofEntry{
	Name: "gcdExists",
	Key:  "prop_9e9b0f1bba8a481",
	Build: family.Theorem(
		"∀a b:num. ∃d:num. d ∣ a ∧ d ∣ b ∧ (∀e:num. e ∣ a ∧ e ∣ b ⇒ e ∣ d)",
		func(arg *Argument) {
			// No binder is fixed: the headline IS the principle's
			// conclusion ∀a. P(a), so the principle is cited bare and P is
			// read off it, and the whole statement closes at once.
			// ByInduction installs the principle as its file states it, so
			// its ⇒ survives the install and one elimination closes (README
			// §"Reading the proofs" carries the mechanism).
			arg.Show(
				"course-of-values induction on the first argument, with Euclid's algorithm as the step",
				ByInduction(nat_order.StrongInduction,
					Case(
						"granted a gcd for every pair with smaller first argument, "+
							"one turn of Euclid's algorithm produces one for (a, b)",
						Derive(func(c *Argument) {
							// The principle spells the point n — read (n₀, b₀)
							// below for the headline's (a, b).
							n := c.Fix()        // the step's own point
							below := c.Assume() // gcds exist below n₀
							b := c.Fix()        // the second argument, arbitrary
							v := nops(c.Ctx())
							zero := c.Ctx().Numeral(0)

							nonzero := c.Unless(
								n.Eq(zero),
								"at n₀ = 0 the common divisors of the pair are b₀'s own divisors, so b₀ is the greatest of them",
								Given(func(c *Argument, isZero Fact) {
									c.Take(b) // the witness d := b₀

									// The maximality conjunct asks nothing: every
									// common divisor of the pair divides b₀ already.
									c.Show(
										"b₀ divides 0 — a remainder that vanishes — and divides itself",
										By(
											isZero,
											At(nat_divides.DividesMod, b, zero), // b₀ ∣ 0 ⇔ nat_mod(0, b₀) = 0
											At(nat_div_mod.ZeroMod, b),          // nat_mod(0, b₀) = 0
											At(nat_divides.DividesRefl, b)))     // b₀ ∣ b₀
								}))

							rem := v.Mod.Apply(b, n) // nat_mod(b₀, n₀) — b₀'s residue

							smaller := c.Have(
								"division by a non-zero number leaves a strictly smaller "+
									"remainder — the measure the algorithm descends on",
								"rem(b, n) < n",
								By(nonzero, At(nat_div_mod.Division, b, n)))

							// Euclid's step: solve for the pair (nat_mod(b₀, n₀), n₀).
							d, lower := c.Obtain(
								"so the induction hypothesis supplies a gcd one turn of the algorithm down",
								"∃d:num. d ∣ rem(b, n) ∧ d ∣ n ∧ (∀e:num. e ∣ rem(b, n) ∧ e ∣ n ⇒ e ∣ d)",
								By(smaller, below.At(rem)))

							c.Take(d)

							// dividesResidue is cited WHOLE: it is wanted at d₀
							// for the divisibility conjunct and at the goal's own
							// bound e for maximality, and its quantifier is what
							// supplies both.
							c.Show(
								"a divisor of n₀ cannot tell b₀ from its residue, so that gcd "+
									"of (rem(b₀, n₀), n₀) is one of (n₀, b₀) — maximality included",
								By(lower, dividesResidue))
						}))))
		}),
})}

// ---------------------------------------------------------------------------
// What the two constants SAY
// ---------------------------------------------------------------------------
//
// Below this file `nat_gcd` and `nat_coprime` are two Hilbert choices
// and an equation, which is a definition and not a meaning. These
// members supply the meaning: gcd's universal property — it is a common
// divisor, and every common divisor divides it — and coprimality as the
// condition that 1 is the only common divisor, which does not care about
// the order of the pair. Above this file the definitions are never
// unfolded again.
//
// The members bind `a` and `b`, which the corpus-wide Argument receiver
// `a` would shadow, so the receiver is `arg`.

// ---------------------------------------------------------------------------
// Gcd — the universal property
// ---------------------------------------------------------------------------

// Gcd is what makes "greatest" the right word, and the order in which
// it is greatest is DIVISIBILITY, not ≤: every common divisor of a and
// b divides nat_gcd(a, b), which is strictly stronger than being no
// larger than it.
//
// There is nothing to prove beyond existence. The specification IS the
// definition — nat_gcd(a, b) is the ε of exactly this property — so
// once something satisfies it, the choice does, and gcdExists is that
// something.
var Gcd = gcdThm{family.Add(registry.ProofEntry{
	Name: "Gcd",
	Key:  "prop_23eff85c8166f44a",
	Build: family.Theorem(
		"∀a b:num. nat_gcd(a, b) ∣ a ∧ nat_gcd(a, b) ∣ b ∧ (∀e:num. e ∣ a ∧ e ∣ b ⇒ e ∣ nat_gcd(a, b))",
		func(arg *Argument, a, b Term) {
			// ↦ the same statement, about the ε-term nat_gcd(a₀, b₀) abbreviates
			// — which makes it that ε's own defining property.
			arg.Do(Unfold(GcdDef))

			arg.Show(
				"a choice satisfies its own defining property as soon as anything does",
				By(gcdExists))
		}),
})}

// ---------------------------------------------------------------------------
// Coprime — coprimality as a statement about divisors
// ---------------------------------------------------------------------------

// Coprime says what nat_coprime means where a reader expects to meet
// it: a and b are coprime exactly when 1 is their only common divisor.
// Every member above this file works through this characterization and
// none of them ever names a gcd again.
//
// Unfolded, the claim is that nat_gcd(a, b) = 1 and "1 is the only
// common divisor" are the same condition, and each direction is one
// half of Gcd:
//
//	⇐ the hypothesis holds of EVERY common divisor, and Gcd's first
//	 half says the gcd is one — so the hypothesis reads off gcd = 1;
//	⇒ Gcd's maximality puts an arbitrary common divisor under the gcd,
//	 which the hypothesis makes 1, and 1's only divisor is 1.
var Coprime = coprimeThm{family.Add(registry.ProofEntry{
	Name: "Coprime",
	Key:  "prop_cdee21d45cf72109",
	Build: family.Theorem(
		"∀a b:num. nat_coprime(a, b) ⇔ ∀d:num. d ∣ a ∧ d ∣ b ⇒ d = 1",
		func(arg *Argument, a, b Term) {
			// ↦ nat_gcd(a₀, b₀) = 1 ⇔ ∀d. …
			arg.Do(Unfold(CoprimeDef))

			// nat_gcd(a₀, b₀) as a Go term: the ⇐ arm grounds its hypothesis
			// there. `a₀`/`b₀` are the resident spellings of this section's
			// own binders.
			gcdAB := arg.Ctx().TermText("nat_gcd(a₀, b₀)")

			arg.Iff()
			arg.Forward(
				"a common divisor divides the gcd, and a gcd of 1 leaves it dividing 1",
				func(c *Argument, unit Fact) {
					d := c.Fix()         // let d₀ be arbitrary
					common := c.Assume() // …and assume d₀ divides both
					c.Show(
						"Gcd's maximality puts d₀ under the gcd, which the hypothesis makes 1 — and 1's only divisor is 1",
						By(Normalized, unit, common, At(Gcd, a, b), At(nat_divides.DividesOne, d))) // d₀ ∣ 1 ⇔ d₀ = 1
				})
			arg.Backward(
				"the hypothesis holds of every common divisor, so in particular of the gcd",
				func(c *Argument, only Fact) {
					c.Show(
						"the gcd is itself a common divisor of a₀ and b₀, so the hypothesis there pins it to 1",
						By(
							only.At(gcdAB), // the hypothesis at d := nat_gcd(a₀, b₀)
							At(Gcd, a, b)))
				})
		}),
})}

// CoprimeSym — coprimality does not depend on the order of the pair:
// read through Coprime, a common divisor of a and b is a common divisor
// of b and a.
var CoprimeSym = coprimeSymThm{family.Add(registry.ProofEntry{
	Name: "CoprimeSym",
	Key:  "prop_1bd581bf01d0df5e",
	Build: family.Theorem("∀a b:num. nat_coprime(a, b) ⇔ nat_coprime(b, a)",
		func(arg *Argument, a, b *Expr[Nat]) {
			arg.Iff()
			arg.Forward(
				"a common divisor of b and a is one of a and b",
				func(c *Argument, coprime Fact) {
					c.Show(
						"so it is 1",
						By(coprime, Coprime.At(a, b), Coprime.At(b, a)))
				})
			arg.Backward(
				"and the other way round",
				func(c *Argument, coprime Fact) {
					c.Show(
						"so it is 1",
						By(coprime, Coprime.At(a, b), Coprime.At(b, a)))
				})
		}),
})}

// OneCoprime — 1 is coprime to every number: a common divisor of 1 and n
// divides 1, and 1's only divisor is 1.
var OneCoprime = oneCoprimeThm{family.Add(registry.ProofEntry{
	Name: "OneCoprime",
	Key:  "prop_ad7d7956cb0cd9b7",
	Build: family.Theorem("∀n:num. nat_coprime(1, n)",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"a common divisor of 1 and n divides 1, so it is 1",
				By(Coprime.At(a.Ctx().Nat(1), n), nat_divides.DividesOne))
		}),
})}

// ---------------------------------------------------------------------------
// Coprimality depends only on a residue
// ---------------------------------------------------------------------------
//
// The file's shape is one lemma about DIVISORS and two one-sentence
// consequences about coprimality. That split is the whole recast: read
// through the specification's Coprime, a coprimality is a statement about a
// pair's common divisors, so a member that replaces one argument by its
// remainder has nothing to say about coprimality and everything to say
// about which numbers divide which. The argument stays in ℕ throughout.

// natOps is ℕ's arithmetic as term BUILDERS — the text DSL parses these
// operators without handing back a Go value for them, and the ground
// cites below are taken at terms this file assembles.
type natOps struct{ Mul, Div, Mod *TermWrapper }

func nops(ctx *proof.Script) *natOps {
	binOp := MakeFun(NumType, NumType, NumType)
	return &natOps{
		Mul: ctx.Const("*", binOp),
		Div: ctx.Const("nat_div", binOp),
		Mod: ctx.Const("nat_mod", binOp),
	}
}

// ---------------------------------------------------------------------------
// dividesResidue — a divisor of the modulus cannot tell a number from
// its remainder
// ---------------------------------------------------------------------------

// dividesResidue is the file's one piece of arithmetic: a divisor of n
// divides a exactly when it divides nat_mod(a, n).
//
// Division writes a as a whole number of n's plus its remainder, and a
// divisor of n counts those n's too — so as far as d can see, a and
// nat_mod(a, n) differ by nothing. Making that precise is one substitution
// (each n is a whole number of d's, so the block of n's is a block of
// d's) and then nat_div_mod.ModEq, which says a shift by whole copies of the
// divisor leaves a remainder alone. nat_divides.DividesMod is what
// carries the two divisibilities into and out of that language.
//
// A zero MODULUS splits off first, for the reason it always does in
// this sub-chapter: at n = 0 there is no division equation to appeal
// to. Nothing is lost there — nat_mod(a, 0) is a, so the two sides of the
// ⇔ are the same statement.
//
// Chapter machinery. Its consumers are this file's two
// reductions and the existence proof's Euclid step, for which "cannot tell a
// number from its remainder" is the whole invariance argument.
var dividesResidue = dividesResidueThm{family.Add(registry.ProofEntry{
	Name: "dividesResidue",
	Key:  "prop_a61db99550d149c1",
	Build: family.Theorem(
		Statement{
			Binders: "∀d n a:num.",
			Hypotheses: []string{
				"d ∣ n",
			},
			Conclusion: "d ∣ rem(a, n) ⇔ d ∣ a",
		},
		func(arg *Argument, d Term, n *TermWrapper, a Term, divN Fact) {
			v := nops(arg.Ctx())
			zero := arg.Ctx().Numeral(0)

			nonzero := arg.Unless(
				n.Eq(zero),
				"at n₀ = 0 there is no division to do — rem(a₀, 0) is a₀, so the two sides are one statement",
				Given(func(c *Argument, isZero Fact) {
					c.Show(
						"the remainder by 0 is the number itself",
						By(isZero, At(nat_div_mod.ModZero, a))) // nat_mod(a₀, 0) = a₀
				}))

			// The divisibility names a cofactor: n₀ is q₀ copies of d₀.
			q, factor := arg.Obtain(
				"a vanishing remainder is a multiple, so n is a whole number of d₀'s",
				"∃q:num. n = q * d",
				By(
					divN,
					At(nat_divides.DividesMod, d, n), // d₀ ∣ n₀ ⇔ nat_mod(n₀, d₀) = 0
					nat_div_mod.ModEqZero))

			quot := v.Div.Apply(a, n)      // nat_div(a₀, n₀) — the copies of n₀ inside a₀
			rem := v.Mod.Apply(a, n)       // nat_mod(a₀, n₀) — what a₀ leaves over
			block := v.Mul.Apply(quot, n)  // the part of a₀ those copies fill
			copies := v.Mul.Apply(quot, q) // the same part, counted in d₀'s

			shifted := arg.Have(
				"so a is its own remainder plus a whole number of d₀'s",
				"a = rem(a, n) + div(a, n) * q * d",
				By(
					Normalized,
					nonzero,
					factor,
					At(nat_div_mod.Division, a, n),     // a₀ = nat_div(a₀,n₀)·n₀ + nat_mod(a₀,n₀)
					At(nat_arith.MulAssoc, quot, q, d), // nat_div(a₀,n₀)·(q₀·d₀) = (nat_div(a₀,n₀)·q₀)·d₀
					// nat_div(a₀,n₀)·n₀ + nat_mod(a₀,n₀) = nat_mod(a₀,n₀) + nat_div(a₀,n₀)·n₀
					At(nat_arith.AddSym, block, rem)))

			arg.Show(
				"a₀ and its remainder therefore leave the same remainder on "+
					"division by d₀ — and a vanishing remainder IS divisibility by d₀",
				By(
					Normalized,
					shifted,
					// ModEq at (dividend, representative, divisor, multiplier).
					At(nat_div_mod.ModEq, a, rem, d, copies),
					At(nat_divides.DividesMod, d, a),
					At(nat_divides.DividesMod, d, rem)))
		}),
})}

// ---------------------------------------------------------------------------
// CoprimeLMod · CoprimeRMod — reducing one argument of the pair
// ---------------------------------------------------------------------------

// CoprimeLMod carries coprimality down to a residue in the first slot.
// Coprimality is a statement about the pair's common divisors, and
// dividesResidue says the pair (nat_mod(a, n), n) has exactly the ones
// (a, n) has: everything here divides n, so nothing here can tell a
// from its remainder.
var CoprimeLMod = coprimeLModThm{family.Add(registry.ProofEntry{
	Name: "CoprimeLMod",
	Key:  "prop_bd9c7d080f5a72a2",
	Build: family.Theorem(
		"∀a n:num. nat_coprime(rem(a, n), n) ⇔ nat_coprime(a, n)",
		func(arg *Argument, a, n Term) {
			res := nops(arg.Ctx()).Mod.Apply(a, n)

			arg.Show(
				"both sides say 1 is the only common divisor, of pairs whose common divisors coincide",
				// dividesResidue is cited WHOLE: the quantifier over divisors
				// is what the argument runs over, and the pair it is wanted at
				// is already fixed by the two Coprime instances.
				By(At(Coprime, res, n), At(Coprime, a, n), dividesResidue))
		}),
})}

// CoprimeRMod is CoprimeLMod with the pair's slots exchanged. It is not
// derived from it: the common-divisor reading of coprimality does not
// distinguish the slots, so the same three facts close this headline
// too, and going through a symmetry lemma would be the longer road.
var CoprimeRMod = coprimeRModThm{family.Add(registry.ProofEntry{
	Name: "CoprimeRMod",
	Key:  "prop_5d583ea75589d166",
	Build: family.Theorem(
		"∀a n:num. nat_coprime(n, rem(a, n)) ⇔ nat_coprime(n, a)",
		func(arg *Argument, a, n Term) {
			res := nops(arg.Ctx()).Mod.Apply(a, n)

			arg.Show(
				"the same coincidence of common divisors, read on the other slot",
				By(At(Coprime, n, res), At(Coprime, n, a), dividesResidue))
		}),
})}

// ---------------------------------------------------------------------------
// Cancelling a coprime factor
// ---------------------------------------------------------------------------
//
// A number coprime to b can be cancelled against b from a divisibility
// of a product — and so two coprime divisors of a number divide it
// together, a product is coprime to n exactly when each factor is, and a
// number coprime to b is coprime to every power of b. The gcd's universal
// property is enough to cancel; no Bézout coefficient is written down.

// CoprimeCancel — a divisor coprime to b divides a whenever it divides a·b.
// It divides gcd(a·p, a·b), which is a·gcd(p, b) = a.
var CoprimeCancel = coprimeCancelThm{family.Add(registry.ProofEntry{
	Name: "CoprimeCancel",
	Key:  "prop_cc5cfff589a8b43c",
	Build: family.Theorem(
		Statement{
			Binders: "∀p a b:num.",
			Hypotheses: []string{
				"nat_coprime(p, b)",
				"p ∣ a * b",
			},
			Conclusion: "p ∣ a",
		},
		func(arg *Argument, p, a, b *Expr[Nat], hyp Fact) {
			aP, aB := arg.TermAs[Nat]("a * p"), arg.TermAs[Nat]("a * b")
			pUnder := arg.Have(
				"p divides both a·p and a·b, so it divides their gcd",
				"p ∣ nat_gcd(a * p, a * b)",
				By(hyp, Gcd.At(aP, aB), nat_divides.DividesOwnMultiple.At(p, a)))
			arg.Show(
				"the gcd is a·gcd(p, b) = a",
				By(Normalized, hyp, pUnder, GcdMulLeft.At(a, p, b), CoprimeDef.At(p, b), nat_arith.MulOne.At(a)))
		}),
})}

// CoprimeProductDivides — two coprime divisors of n divide n together. n
// is a taken some number of times, e; b divides a·e and shares nothing
// with a, so it divides e; and then n is a·b taken the rest.
var CoprimeProductDivides = coprimeProductDividesThm{family.Add(registry.ProofEntry{
	Name: "CoprimeProductDivides",
	Key:  "prop_ba9a0c17f74e0f4f",
	Build: family.Theorem(Statement{
		Binders: "∀a b n:num.",
		Hypotheses: []string{
			"nat_coprime(a, b)",
			"a ∣ n",
			"b ∣ n",
		},
		Conclusion: "a * b ∣ n",
	},
		func(arg *Argument, a, b, n *Expr[Nat], hyp Fact) {
			e, byA := arg.ObtainAs[Nat](
				"n is a taken e times",
				"∃e:num. n = a * e",
				By(hyp, nat_divides.DividesFactor.At(a, n)))
			flipped := arg.Have(
				"b shares nothing with a",
				"nat_coprime(b, a)",
				By(hyp, CoprimeSym.At(a, b)))
			bDividesE := arg.Have(
				"b divides a·e and is coprime to a, so it divides e",
				"b ∣ e",
				By(Normalized, hyp, byA, flipped, nat_arith.MulSym.At(a, e), CoprimeCancel.At(b, e, a)))
			f, byB := arg.ObtainAs[Nat](
				"e is b taken f times",
				"∃f:num. e = b * f",
				By(bDividesE, nat_divides.DividesFactor.At(b, e)))
			arg.Show(
				"so n is a·b taken f times",
				By(
					Normalized,
					byA,
					byB,
					nat_arith.MulAssoc.At(a, b, f),
					nat_divides.DividesFactor.At(arg.TermAs[Nat]("a * b"), n)))
		}),
})}

// DivisorProductFactors — a divisor of a product splits into divisors of its
// factors. Remove gcd(d, m) from d and m; the remaining cofactors are coprime,
// so the cofactor of d divides n by coprime cancellation.
var DivisorProductFactors = divisorProductFactorsThm{family.Add(registry.ProofEntry{
	Name: "DivisorProductFactors",
	Key:  "prop_f2f2f81ad91a434f",
	Build: family.Theorem(Statement{
		Binders: "∀d m n:num.",
		Hypotheses: []string{
			"d ∣ m * n",
		},
		Conclusion: "∃a b:num. d = a * b ∧ a ∣ m ∧ b ∣ n",
	},
		func(a *Argument, d, m, n *Expr[Nat], divides Fact) {
			nonzeroD := a.Unless(
				Equal(d, a.TermAs[Nat]("0")),
				"when d is zero, m and n themselves are the required factors",
				Given(func(b *Argument, zero Fact) {
					b.Take(m)
					b.Take(n)
					b.Show(
						"zero divides only zero, so d equals m·n",
						By(zero, divides, nat_divides.ZeroDivides.At(b.TermAs[Nat]("m * n")), nat_divides.DividesRefl))
				}))
			g, gDef := a.LetAs[Nat]("g", "nat_gcd(d, m)")
			common := a.Have(
				"g divides both d and m",
				"g ∣ d ∧ g ∣ m",
				By(Normalized, gDef, Gcd.At(d, m)))
			q, qEq := a.ObtainAs[Nat](
				"write d = g·q",
				"∃q:num. d = g * q",
				By(common, nat_divides.DividesFactor.At(g, d)))
			r, rEq := a.ObtainAs[Nat](
				"write m = g·r",
				"∃r:num. m = g * r",
				By(common, nat_divides.DividesFactor.At(g, m)))
			nonzeroG := a.Have(
				"g is nonzero since it divides nonzero d",
				"g ≠ 0",
				By(nonzeroD, common, nat_divides.ZeroDivides.At(d)))
			cofactorGcd := a.Have(
				"factoring g out of gcd(d, m) gives g·gcd(q, r) = g",
				"g * nat_gcd(q, r) = g * 1",
				Simp(Rev(GcdMulLeft), Rev(qEq), Rev(rEq), Rev(gDef), Fwd(nat_arith.MulOne)),
				Refl())
			coprime := a.Have(
				"cancelling g gives coprimality of q and r",
				"nat_coprime(q, r)",
				By(
					nonzeroG,
					cofactorGcd,
					nat_arith.MulEqLCancel.At(g, a.TermAs[Nat]("nat_gcd(q, r)"), a.TermAs[Nat]("1")),
					CoprimeDef.At(q, r)))
			reduced := a.Have(
				"cancelling g from d ∣ m·n leaves q ∣ n·r",
				"q ∣ n * r",
				By(
					Normalized,
					nonzeroG,
					qEq,
					rEq,
					divides,
					nat_arith.MulAssoc.At(g, r, n),
					nat_divides.MulDividesLCancel.At(g, q, a.TermAs[Nat]("r * n")),
					nat_arith.MulSym.At(n, r)))
			a.Take(g)
			a.Take(q)
			a.Show(
				"coprime cancellation gives q ∣ n, so g and q split d as required",
				By(qEq, coprime, reduced, common, CoprimeCancel.At(q, n, r)))
		}),
})}

// CoprimeMul — a product is coprime to n exactly when each factor is. A
// divisor of a factor divides the product, which gives one direction. For
// the other, a common divisor d of a·b and n shares no divisor with a, since
// such a divisor would divide n as well; so d cancels a from d ∣ b·a
// (CoprimeCancel) and divides b, and a common divisor of b and n is 1.
var CoprimeMul = coprimeMulThm{family.Add(registry.ProofEntry{
	Name: "CoprimeMul",
	Key:  "prop_741fde94c849daf",
	Build: family.Theorem("∀a b n:num. nat_coprime(a * b, n) ⇔ nat_coprime(a, n) ∧ nat_coprime(b, n)",
		func(arg *Argument, a, b, n *Expr[Nat]) {
			product := arg.TermAs[Nat]("a * b")
			arg.Iff()
			arg.Forward(
				"a divisor of either factor divides the product",
				func(c *Argument, coprime Fact) {
					c.Show(
						"so a common divisor of a factor and n is one of a·b and n, and is 1",
						By(
							coprime,
							Coprime.At(product, n),
							Coprime.At(a, n),
							Coprime.At(b, n),
							nat_divides.DividesMul,
							nat_arith.MulSym))
				})
			arg.Backward(
				"a common divisor of a·b and n cancels a and divides b",
				func(c *Argument, both Fact) {
					coprime := c.Conjuncts(
						both,
						"a is coprime to n",
						"b is coprime to n")
					onlyOne := c.Have(
						"every common divisor of a·b and n is 1",
						"∀d:num. d ∣ a * b ∧ d ∣ n ⇒ d = 1",
						Derive(func(e *Argument) {
							d := e.FixAs[Nat]("d")
							divides := e.Conjuncts(
								e.Assume(),
								"d divides a·b",
								"d divides n")
							withA := e.Have(
								"d shares no divisor with a: such a divisor would divide n as well",
								"nat_coprime(d, a)",
								By(coprime[0], divides[1], Coprime.At(d, a), Coprime.At(a, n), nat_divides.DividesTrans))
							e.Show(
								"so d cancels a from d ∣ b·a and divides b, and a common divisor of b and n is 1",
								By(
									withA,
									divides[0],
									divides[1],
									coprime[1],
									CoprimeCancel.At(d, b, a),
									nat_arith.MulSym.At(a, b),
									Coprime.At(b, n)))
						}))
					c.Show(
						"which is what a·b coprime to n means",
						By(onlyOne, Coprime.At(product, n)))
				})
		}),
})}

// CoprimePowRight — a number coprime to b is coprime to every power of b.
// The zeroth power is 1; multiplication preserves coprimality at each step.
var CoprimePowRight = coprimePowRightThm{family.Add(registry.ProofEntry{
	Name: "CoprimePowRight",
	Key:  "prop_75c5ef0cea4ec96b",
	Build: family.Theorem(Statement{
		Binders: "∀a b k:num.",
		Hypotheses: []string{
			"nat_coprime(a, b)",
		},
		Conclusion: "nat_coprime(a, b ^ k)",
	}, func(arg *Argument, a, b, k *Expr[Nat], coprime Fact) {
		arg.Induct(k)
		arg.Base(
			"b^0 = 1, whose only divisor is 1",
			By(nat_arith.NatPow, Coprime.At(a, arg.TermAs[Nat]("1")), nat_divides.DividesOne))
		arg.Step(
			"both b and b^k are coprime to a, so their product is too",
			func(step *Argument, ih Fact) {
				power := step.TermAs[Nat]("b ^ k")
				step.Show(
					"b^suc(k) = b·b^k is coprime to a",
					By(
						Normalized,
						coprime,
						ih,
						CoprimeSym.At(a, b),
						CoprimeSym.At(a, power),
						CoprimeMul.At(b, power, a),
						nat_arith.NatPow,
						CoprimeSym.At(a, step.TermAs[Nat]("b ^ suc(k)"))))
			})
	}),
})}

// GcdFromCommonMultiples — e is d / nat_gcd(d, r) as soon as d divides r·e and
// r·e divides every positive common multiple of d and r. Write d = g·u and
// r = g·v: the multiple u·r gives e ∣ u, and d ∣ r·e gives u ∣ v·e, hence u ∣ e
// since u and v are coprime.
var GcdFromCommonMultiples = gcdFromCommonMultiplesThm{family.Add(registry.ProofEntry{
	Name: "GcdFromCommonMultiples",
	Key:  "prop_521459767fb86c1c",
	Build: family.Theorem(Statement{
		Binders: "∀d r e:num.",
		Hypotheses: []string{
			"0 < d",
			"0 < r",
			"d ∣ r * e",
			"∀L:num. 0 < L ∧ d ∣ L ∧ r ∣ L ⇒ r * e ∣ L",
		},
		Conclusion: "e * nat_gcd(d, r) = d",
	},
		func(a *Argument, d, r, e *Expr[Nat], positiveD, positiveR, divides, least Fact) {
			g, gDef := a.LetAs[Nat]("g", "nat_gcd(d, r)")
			gcd := a.Have(
				"g divides d and r, and every common divisor divides g",
				"g ∣ d ∧ g ∣ r ∧ (∀c:num. c ∣ d ∧ c ∣ r ⇒ c ∣ g)",
				By(Normalized, gDef, Gcd.At(d, r)))
			u, uEq := a.ObtainAs[Nat](
				"write d = g·u",
				"∃u:num. d = g * u",
				By(gcd, nat_divides.DividesFactor.At(g, d)))
			v, vEq := a.ObtainAs[Nat](
				"write r = g·v",
				"∃v:num. r = g * v",
				By(gcd, nat_divides.DividesFactor.At(g, r)))
			positiveGU := a.Have(
				"g and u are positive, since their product d is",
				"0 < g ∧ 0 < u",
				ByArith(positiveD, uEq, nat_arith.MulEqZero.At(g, u)))
			positive := a.Have(
				"and so is v, since g·v is r",
				"0 < g ∧ 0 < u ∧ 0 < v",
				ByArith(positiveGU, positiveR, vEq, nat_arith.MulEqZero.At(g, v)))
			nonzero := a.Have(
				"so g and r are not zero",
				"g ≠ 0 ∧ r ≠ 0",
				ByArith(positive, positiveR))
			multiple := a.Have(
				"u·r is the multiple d·v",
				"d * v = u * r",
				By(Normalized, uEq, vEq, nat_arith.MulAssoc.At(u, g, v), nat_arith.MulSym.At(u, g)))
			positiveMultiple := a.Have(
				"u·r is positive",
				"0 < u * r",
				ByArith(positive, positiveR, nat_arith.MulEqZero.At(u, r)))
			commonD := a.Have(
				"d divides u·r",
				"d ∣ u * r",
				By(Normalized, multiple, nat_divides.DividesOwnMultiple.At(d, v)))
			atMultiple := a.Have(
				"r·e divides u·r, a positive common multiple of d and r",
				"r * e ∣ r * u",
				By(
					Normalized,
					least.At(a.TermAs[Nat]("u * r")),
					positiveMultiple,
					commonD,
					nat_divides.DividesOwnMultiple.At(r, u),
					nat_arith.MulSym.At(r, u)))
			eDividesU := a.Have(
				"cancelling r, e divides u",
				"e ∣ u",
				By(nonzero, atMultiple, nat_divides.MulDividesLCancel.At(r, e, u)))
			cancelled := a.Have(
				"d ∣ r·e reads g·u ∣ g·(v·e)",
				"g * u ∣ g * (v * e)",
				By(Normalized, uEq, vEq, divides, nat_arith.MulAssoc.At(g, v, e)))
			uDividesVE := a.Have(
				"cancelling g, u divides v·e",
				"u ∣ e * v",
				By(
					Normalized,
					nonzero,
					cancelled,
					nat_divides.MulDividesLCancel.At(g, u, a.TermAs[Nat]("v * e")),
					nat_arith.MulSym.At(e, v)))
			cofactorGcd := a.Have(
				"factoring g out of gcd(d, r) gives g·gcd(u, v) = g",
				"g * nat_gcd(u, v) = g * 1",
				By(Normalized, gDef, uEq, vEq, GcdMulLeft.At(g, u, v), nat_arith.MulOne.At(g)))
			coprime := a.Have(
				"cancelling nonzero g gives gcd(u, v) = 1, so u and v are coprime",
				"nat_coprime(u, v)",
				By(
					nonzero,
					cofactorGcd,
					nat_arith.MulEqLCancel.At(g, a.TermAs[Nat]("nat_gcd(u, v)"), a.TermAs[Nat]("1")),
					CoprimeDef.At(u, v)))
			same := a.Have(
				"u divides e by coprimality, and e divides u, so they are equal",
				"e = u",
				By(eDividesU, coprime, uDividesVE, CoprimeCancel.At(u, e, v), nat_divides.DividesAntisym.At(e, u)))
			a.Show(
				"so e·g is u·g, which is d",
				By(uEq, same, nat_arith.MulSym.At(e, g)))
		}),
})}

// GcdMulLeft — a common factor comes out of a gcd. c·gcd(a, b) divides c·a
// and c·b, so it divides their gcd. Conversely c divides both, so their gcd
// is c·h for some h; cancelling c from c·h ∣ c·a and c·h ∣ c·b leaves h a
// common divisor of a and b, so h divides gcd(a, b) and the gcd divides
// c·gcd(a, b). At c = 0 both sides are 0.
var GcdMulLeft = gcdMulLeftThm{family.Add(registry.ProofEntry{
	Name: "GcdMulLeft",
	Key:  "prop_48b2b69bd3b4800d",
	Build: family.Theorem(
		"∀c a b:num. nat_gcd(c * a, c * b) = c * nat_gcd(a, b)",
		func(arg *Argument, c, a, b *Expr[Nat]) {
			ca, cb := arg.TermAs[Nat]("c * a"), arg.TermAs[Nat]("c * b")
			g := arg.TermAs[Nat]("nat_gcd(a, b)")
			gcd := arg.TermAs[Nat]("nat_gcd(c * a, c * b)")

			lower := arg.Have(
				"c·gcd(a, b) divides c·a and c·b, so it divides their gcd",
				"c * nat_gcd(a, b) ∣ nat_gcd(c * a, c * b)",
				By(
					Gcd.At(a, b),
					Gcd.At(ca, cb),
					nat_divides.MulDividesMulLeft.At(c, g, a),
					nat_divides.MulDividesMulLeft.At(c, g, b)))

			nonzero := arg.Unless(
				Equal(c, arg.TermAs[Nat]("0")),
				"at c = 0 the gcd is divisible by 0, so it is 0, as is 0·gcd(a, b)",
				Given(func(zeroCase *Argument, isZero Fact) {
					zeroCase.Show(
						"0 divides only 0",
						By(isZero, lower, nat_divides.ZeroDivides.At(gcd), nat_arith.MulLeftZeroClause.At(g)))
				}))

			h, cofactor := arg.ObtainAs[Nat](
				"c divides c·a and c·b, so it divides their gcd, which is c·h for some h",
				"∃h:num. nat_gcd(c * a, c * b) = c * h",
				By(
					Gcd.At(ca, cb),
					nat_divides.DividesOwnMultiple.At(c, a),
					nat_divides.DividesOwnMultiple.At(c, b),
					nat_divides.DividesFactor.At(c, gcd)))

			common := arg.Have(
				"cancelling c from c·h ∣ c·a and c·h ∣ c·b, h is a "+
					"common divisor of a and b, so it divides gcd(a, b)",
				"h ∣ nat_gcd(a, b)",
				By(
					nonzero,
					cofactor,
					Gcd.At(ca, cb),
					Gcd.At(a, b),
					nat_divides.MulDividesLCancel.At(c, h, a),
					nat_divides.MulDividesLCancel.At(c, h, b)))

			arg.Show(
				"so the gcd c·h divides c·gcd(a, b), and the two divide each other",
				By(
					cofactor,
					common,
					lower,
					nat_divides.MulDividesMulLeft.At(c, h, g),
					nat_divides.DividesAntisym.At(gcd, arg.TermAs[Nat]("c * nat_gcd(a, b)"))))
		}),
})}
