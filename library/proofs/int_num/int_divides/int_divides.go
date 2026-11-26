// int_divides.go — the chapter: divisibility on ℤ.
//
// Two parts, marked by banners:
//
// - The elementary laws of `∣`
// - What the ℤ greatest common divisor IS

package int_divides

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The elementary laws of `∣`
// ---------------------------------------------------------------------------
//
// the elementary laws of `∣`: how far a divisor can reach, what a
// divisibility does not notice, and what carries it to a new dividend.
//
// All four are proved the same way, because `∣` IS the existence of a
// cofactor. Expanding it turns the hypothesis into the cofactor it
// hands over and the goal into the one it asks for, and the argument is
// then always the same shape: name the second in terms of the first. A
// sign on either side is absorbed by negating the cofactor; an extra
// factor on the dividend, by multiplying it in. The bound is the one
// that cannot do this — it is what happens when the cofactor is pinned
// away from &0 instead.
//
// The two absolute-value laws are that sentence twice, once on each
// side of the relation, and what differs between them is which factor
// of the defining product the sign lands on — and, because the two
// products it leaves behind chain differently, whether the close needs
// shaping.

// DivisorBoundedByDividend — a divisor is no larger than what it
// divides, once what it divides is not &0.
//
// The zero exclusion is not a technicality: &0 is divided by every
// integer, so without it the statement would claim every integer is
// smaller than &0.
//
// The argument is one chain. Divisibility hands over a cofactor; the
// dividend being nonzero makes that cofactor nonzero, since a product
// with a zero factor vanishes; a nonzero integer has size at least &1,
// which is the discreteness step and the only ℤ-specific one; and a
// size scaled by something at least &1 does not go down.
//
// The ℝ statement is FALSE — every nonzero real divides every real —
// so that third step is not a convenience but the whole content.
var DivisorBoundedByDividend = divisorBoundedByDividendThm{family.Add(registry.ProofEntry{
	Name: "DivisorBoundedByDividend",
	Key:  "prop_5464ee8bce55f32d",
	Build: family.Theorem(Statement{
		Binders: "∀x y:int.",
		Hypotheses: []string{
			"x ∣ y",
			"y ≠ &0",
		},
		Conclusion: "|x| ≤ |y|",
	},
		func(a *Argument, x, y Term, dividesNonzero Fact) {
			v := ops(a.Ctx())
			absX, absY := v.Abs.Apply(x), v.Abs.Apply(y)

			multiple := a.Have(
				"unfold the divisibility to the multiple it is defined to be",
				"∃k:int. y = x * k",
				Unfold(IntDividesDef))
			k, decomposes := a.Unpack(multiple) // y = x * k
			absK := v.Abs.Apply(k)

			nonzero := a.Have(
				"so the cofactor is nonzero, a vanishing factor being enough to vanish the product",
				MakeProp(k.Neq(v.Zero)),
				// Normalized — the hypothesis arrives as the statement's whole
				// antecedent and has to be taken apart before the premises
				// meet the closer; engine shaping, not part of the argument.
				By(
					Normalized,
					dividesNonzero,
					decomposes,
					At(int_real_lift.MulEqZero, x, k))) // x * k = &0 ⇔ x = &0 ∨ k = &0

			atLeastOne := a.Have(
				"and a nonzero integer has a size of at least &1, there being no integer between",
				MakeProp(v.Le.Apply(v.One, absK)),
				By(
					nonzero,
					At(int_real_lift.AbsPosIffNonzero, k), // k ≠ &0 ⇔ &0 < |k|
					At(int_embed.Discrete, v.Zero, absK),  // &0 < |k| ⇔ &0 + &1 ≤ |k|
					int_real_lift.AddLeftIdentity))

			factored := a.Have(
				"the dividend's size is the two sizes multiplied",
				MakeProp(absY.Eq(v.Mul.Apply(absX, absK))),
				By(decomposes, int_real_lift.AbsMul))

			a.Show(
				"and scaling the divisor's size by a factor of at least &1 cannot bring it down",
				By(
					factored,
					atLeastOne,
					At(int_real_lift.AbsNonneg, x), // &0 ≤ |x|
					// &0 ≤ |x| ∧ &1 ≤ |k| ⇒ |x| * &1 ≤ |x| * |k|
					At(int_real_lift.LessEqMulLeft, absX, v.One, absK),
					int_real_lift.MulRightIdentity))
		}),
})}

// AbsDividend — a divisor does not see the sign of what it divides, so
// taking the dividend's absolute value changes nothing.
//
// One sentence, proved once and applied twice. Negating a dividend
// preserves divisibility, because the cofactor negates with it. An
// absolute value is either the integer itself, where there is nothing
// to prove, or its negation, where that sentence gives the forward
// direction outright and the backward one applied a second time —
// at the negation, whose own negation is the integer again.
var AbsDividend = absDividendThm{family.Add(registry.ProofEntry{
	Name: "AbsDividend",
	Key:  "prop_19749aac2ab2bdec",
	Build: family.Sections("∀d n:int. d ∣ n ⇔ d ∣ |n|",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			negate := ctx.Lemma(Statement{
				Binders: "∀d n:int.",
				Hypotheses: []string{
					"d ∣ n",
				},
				Conclusion: "d ∣ int_neg(n)",
			},
				func(a *Argument, d, n Term, _ Fact) {
					// The cofactor construction, as in the file header.
					a.Do(Unfold(IntDividesDef))
					k, decomposes := a.Unpack(a.Hyp("∃k:int. n = d * k"))
					a.Take(v.Neg.Apply(k))
					a.Show(
						"negating the cofactor negates the product, which is the cofactor -n asks for",
						// Normalized — the sign has to travel from the product
						// to the factor, so the two product equations chain
						// through each other rather than meeting the closer
						// directly. AbsDivisor's mirror needs no such step:
						// there the cited law rewrites the goal's product onto
						// the hypothesis's in one move.
						By(Normalized, decomposes, At(int_real_lift.MulRightNeg, d, k))) // d * -k = -(d * k)
				})

			return ctx.Theorem(headline, func(a *Argument, d, n Term) {
				// AbsBySign is int_abs's CHARACTERIZATION, not its
				// definition: unfolding the constant drops into the ℝ
				// term it is built from
				// (`int_of_real(real_abs(real_of_int(n)))`), and it is
				// the characterization that carries the sign case split.
				a.Show(
					"|n| is n or -n, and the sign law crosses the second in both directions",
					By(
						At(negate, d, n),                  // d ∣ n ⇒ d ∣ -n
						At(negate, d, v.Neg.Apply(n)),     // d ∣ -n ⇒ d ∣ -(-n)
						At(int_construction.AbsBySign, n), // int_abs(n) = COND(&0 ≤ n, n, -n)
						At(int_real_lift.NegNeg, n)))      // -(-n) = n
			})
		}),
})}

// AbsDivisor — nor does the sign of the divisor matter, so taking ITS
// absolute value changes nothing either.
//
// AbsDividend's proof with the sign moved to the other factor of the
// defining product. There the cofactor's sign had nothing to meet and
// so survived onto the product; here it meets the divisor's, and the
// two cancel.
var AbsDivisor = absDivisorThm{family.Add(registry.ProofEntry{
	Name: "AbsDivisor",
	Key:  "prop_40a3635cee261e43",
	Build: family.Sections("∀d n:int. d ∣ n ⇔ |d| ∣ n",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			negate := ctx.Lemma(Statement{
				Binders: "∀d n:int.",
				Hypotheses: []string{
					"d ∣ n",
				},
				Conclusion: "int_neg(d) ∣ n",
			},
				func(a *Argument, d, n Term, _ Fact) {
					// The same construction again. MulNegNeg — that
					// negating BOTH factors leaves the product alone — is
					// the one place the two proofs part, standing where
					// AbsDividend cites int_real_lift.MulRightNeg.
					a.Do(Unfold(IntDividesDef))
					k, decomposes := a.Unpack(a.Hyp("∃k:int. n = d * k"))
					a.Take(v.Neg.Apply(k))
					a.Show(
						"negating the cofactor as well restores the product, so the negated divisor still divides",
						By(decomposes, int_real_lift.MulNegNeg))
				})

			return ctx.Theorem(headline, func(a *Argument, d, n Term) {
				// AbsBySign, as in AbsDividend.
				a.Show(
					"|d| is d or -d, and the sign law crosses the second in both directions",
					By(
						At(negate, d, n),                  // d ∣ n ⇒ -d ∣ n
						At(negate, v.Neg.Apply(d), n),     // -d ∣ n ⇒ -(-d) ∣ n
						At(int_construction.AbsBySign, d), // int_abs(d) = COND(&0 ≤ d, d, -d)
						At(int_real_lift.NegNeg, d)))      // -(-d) = d
			})
		}),
})}

// DividesProduct — whatever divides one factor divides the product.
//
// The cofactor absorbs the other factor: if `m` is `d` times `k`, then
// `m * n` is `d` times `k * n`, and re-associating is all there is to
// it.
var DividesProduct = dividesProductThm{family.Add(registry.ProofEntry{
	Name: "DividesProduct",
	Key:  "prop_15d0393da9774110",
	Build: family.Theorem(Statement{
		Binders: "∀d m n:int.",
		Hypotheses: []string{
			"d ∣ m",
		},
		Conclusion: "d ∣ m * n",
	},
		func(a *Argument, d, m, n Term, _ Fact) {
			v := ops(a.Ctx())

			// The same construction once more.
			a.Do(Unfold(IntDividesDef))
			k, decomposes := a.Unpack(a.Hyp("∃k:int. m = d * k"))
			a.Take(v.Mul.Apply(k, n))
			a.Show(
				"the cofactor takes the extra factor with it, which is one re-association",
				// Normalized — the two product equations chain through
				// each other, as in AbsDividend.
				By(Normalized, decomposes, At(int_real_lift.MulAssoc, d, k, n))) // d * (k * n) = d * k * n
		}),
})}

// DividesOwnMultiple — every integer divides its own multiples.
//
// Nothing is proved here either: for `c · d` the cofactor `∣` asks for
// is the other factor, so unfolding and exhibiting it is the whole
// argument, with one commutation to write the product the way the
// definition does.
//
// It is `DividesProduct` with the divisibility already discharged —
// `d ∣ d` needing no cofactor but itself — and it is a member rather
// than a line repeated inline because its consumers reach it at a
// cofactor they have just built, where a named law arrives as a ground
// instance.
//
// Exported because its consumers are in `int_num/int_div_rem`, one
// chapter up.
var DividesOwnMultiple = dividesOwnMultipleThm{family.Add(registry.ProofEntry{
	Name: "DividesOwnMultiple",
	Key:  "prop_ac5a048fca1af38a",
	Build: family.Theorem("∀d c:int. d ∣ c * d",
		func(a *Argument, d, c Term) {

			a.Do(
				Unfold(IntDividesDef),      // d ∣ c * d ↦ ∃k. c * d = d * k
				Witness(c),                 // and the cofactor asked for is the other factor
				Cite(int_real_lift.MulSym), // ↦ c * d = c * d
			)
		}),
})}

// ---------------------------------------------------------------------------
// ℕ's divisibility, read in ℤ
// ---------------------------------------------------------------------------
//
// ℕ has its own divisibility, defined inside ℕ as the existence of a
// natural cofactor (nat_num/nat_divides), and the embedding carries it to
// this chapter's relation. The clause belongs to the sentence "& is an
// embedding of ordered semirings" that int_embed states operation by
// operation; it sits here rather than at the boundary because the ℤ side
// of the clause is this chapter's relation, and the boundary chapter is
// below it — as congruence's clause sits in int_congruence and the
// power's in int_pow.

// OfNumDivides — `&` carries divisibility across: d divides n in ℕ
// exactly when &d divides &n in ℤ. Both directions are one question —
// does a factorization survive &(·): ℕ ↪ ℤ? — asked the two ways, and
// each sub-lemma answers by naming the witness the other side needs.
// Going up is free, because & is multiplicative. Coming down is the
// content: a ℤ factor need not be a natural, but its absolute value is,
// and taking absolute values leaves the equation intact because &n and
// &d are already nonnegative.
//
// ℕ's divisibility is nat_num/nat_divides's constant and ℤ's is
// int_divides; each side unfolds to its own factorization, and the two
// lemmas carry a witness between them.
var OfNumDivides = ofNumDividesThm{family.Add(registry.ProofEntry{
	Name: "OfNumDivides",
	Key:  "prop_78851fe044548b78",
	// The two transport lemmas are Go locals; the headline cites them by
	// closure capture, one per direction of the ⇔.
	Build: family.Sections(
		"∀d n:num. d ∣ n ⇔ d ∣ int_of_num(n)",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// descend — a ℤ factorization of &n yields an ℕ one, witness
			// num_of_int|z₀|.
			//
			// (The ℤ factor is `z` and the ℕ factor of `lift` below is `x`:
			// proof-level free names carry one type per file.)
			descend := ctx.Lemma(
				Statement{
					Binders: "∀n d:num. ∀z:int.",
					Hypotheses: []string{
						"&n = &d * z",
					},
					Conclusion: "∃y:num. n = d * y",
				},
				// The ℤ equation is consumed as a resident hyp — the two Have
				// claims below read it, and nothing addresses it by name.
				func(a *Argument, n, d, z Term, _ Fact) {
					absZ := v.Abs.Apply(z) // |z₀|
					a.Take(v.NumOfInt.Apply(absZ))

					a.Have(
						"&(num_of_int|z|) = |z| — num_of_int is a section of & on "+
							"the nonnegatives, and |z| ≥ 0 discharges the side condition",
						"&num_of_int(|z|) = |z|",
						By(
							At(int_real_lift.AbsNonneg, z),       // &0 ≤ |z₀|
							At(int_embed.NumOfIntSection, absZ))) // the section at |z₀|, whose side condition that is

					// &n₀ = |&d₀·z₀| = &d₀·|z₀|, one waypoint per leg.
					a.Have(
						"&n = &d·|z| — pass to absolute values; &n and &d are their own absolute values",
						"&n = &d * |z|",
						Cite(int_embed.OfNumAbs, n),
						Cite(int_embed.OfNumAbs, d),
						Cite(int_real_lift.AbsMul, v.IntOfNum.Apply(d), z),
						CalcEq(
							Leg(
								v.Abs.Apply(v.Mul.Apply(v.IntOfNum.Apply(d), z)),
								"|·| fixes &n₀, and the hypothesis rewrites its argument",
								Basic()),
							FinalLeg(
								"|·| splits the product; |&d₀| = &d₀ leaves the left factor alone",
								Basic()),
						))

					// Both sides are now embedded naturals, so & can be cancelled.
					a.Show(
						"n₀ = d₀·num_of_int|z₀| — the two claims give the equation under &, which is injective",
						// ↦ &(d₀·num_of_int|z₀|) = &d₀·&(num_of_int|z₀|), the form
						// the two claims above have already established.
						Cite(int_embed.OfNumMul, d, v.NumOfInt.Apply(absZ)),
						// ↦ rewrites the ℕ goal to that ℤ equation, closing it.
						Cite(int_embed.OfNumEq))
				})

			// lift — an ℕ factorization embeds. Free: & is multiplicative, so
			// &x₀ is the witness and one rewrite closes.
			lift := ctx.Lemma(
				Statement{
					Binders: "∀n d x:num.",
					Hypotheses: []string{
						"n = d * x",
					},
					Conclusion: "∃y:int. &n = &d * y",
				},
				func(a *Argument, n, d, x Term, _ Fact) {
					a.Take(v.IntOfNum.Apply(x))
					// ↦ &n₀ = &(d₀·x₀), which is the hypothesis under &.
					a.Do(Cite(int_embed.OfNumMul))
				})

			return ctx.Theorem(headline,
				func(a *Argument, d, n Term) {
					// Each direction unfolds both divisibilities to their
					// factorizations and transports the witness the matching
					// way.
					//
					// Both arms cite their sibling with CiteNode rather than
					// Cite: the sibling is a ∀-implication that must be APPLIED
					// to the resident hypothesis, and Cite's IsStronger test
					// fails before instantiation, so it installs and leaves the
					// arm open.
					//
					// Each arm's first unfold moves the antecedent into the
					// hypotheses (the unfold's trivial simplify does that), so
					// the sibling meets a resident ∃ and Skolemizes it itself.
					a.Iff()
					a.Forward(
						"the ℕ witness lifts to ℤ, which is what int_divides asks for",
						// ↦ ∃x. n₀ = d₀·x ⊢ ∃y:int. &n₀ = &d₀·y
						Unfold(nat_divides.DividesFactor),
						Unfold(IntDividesDef),
						CiteNode(lift))
					a.Backward(
						"int_divides supplies a ℤ witness; descend turns it into an ℕ one",
						// ↦ ∃z:int. &n₀ = &d₀·z ⊢ ∃x. n₀ = d₀·x
						Unfold(nat_divides.DividesFactor),
						Unfold(IntDividesDef),
						CiteNode(descend))
				})
		}),
})}

// UnitPlusMinusOne — the units of ℤ are plus and minus one: a factor r of
// one divides one, so its size, a natural number, divides one in ℕ and is
// one, and r is the integer of size one with its sign.
var UnitPlusMinusOne = unitPlusMinusOneThm{family.Add(registry.ProofEntry{
	Name: "UnitPlusMinusOne",
	Key:  "prop_a8e28bfac8ef7602",
	Build: family.Theorem(Statement{
		Binders: "∀r s:int.",
		Hypotheses: []string{
			"r * s = &1",
		},
		Conclusion: "r = &1 ∨ r = -&1",
	},
		func(a *Argument, r, s *Expr[Int], product Fact) {
			dividesOne := a.Have(
				"r divides one",
				"r ∣ &1",
				Simp(Fwd(IntDividesDef)),
				Witness(s),
				By(product))
			d, magnitude := a.ObtainAs[Nat](
				"write the size of r as a natural number",
				"∃d:num. |r| = &d",
				By(int_real_lift.AbsNonneg.At(r), int_embed.OfNumExists.At(a.TermAs[Int]("|r|"))))
			magnitudeDivides := a.Have(
				"that natural number divides one",
				"d ∣ 1",
				By(
					Normalized,
					magnitude,
					dividesOne,
					AbsDivisor.At(r, a.TermAs[Int]("&1")),
					OfNumDivides.At(d, a.TermAs[Nat]("1"))))
			magnitudeOne := a.Have(
				"a natural divisor of one is one",
				"d = 1",
				By(magnitudeDivides, nat_divides.DividesOne.At(d)))
			a.Show(
				"so r, of size one, is plus or minus one",
				ByArith(magnitude, magnitudeOne, int_construction.AbsBySign.At(r)))
		}),
})}

// ---------------------------------------------------------------------------
// What the ℤ greatest common divisor IS
// ---------------------------------------------------------------------------
//
// `int_gcd` arrives by CHOICE rather than by construction: every pair
// HAS a nonnegative common divisor reachable by Bézout, and the
// constant names one. This file carries both sentences — the existence
// pair (`Bezout` proves the reachable common divisor, `BezoutNonneg`
// takes its absolute value) and the mint that turns the existence
// statement into a fact about the constant the choice defines.
//
// `By(Normalized, …)` is this file's usual close, and where it stands
// the token is load-bearing, not decoration: it runs Basic between the
// installs and the close, which is what lets an assembly leaf settle
// without reaching the refuter. A bare `By` here is a leaf the
// conditioning settles on its own, with no key either. Only a handful
// of leaves genuinely refute; they are the file's recorded keys.

// Coprime is what the ℤ predicate int_coprime IS: a and b are coprime
// when some ℤ-combination of them reaches &1 — Bézout's identity taken
// as the definition. It heads the gcd part because it is the part's
// other definitional face: IntGcdSpec below says what int_gcd is, this
// says what int_coprime is, and the two meet where the gcd is &1.
//
// The proof is the definition read on a pair: unfolding int_coprime
// leaves its body over the pair's projections fst((a, b)) and
// snd((a, b)), which collapse to a and b, and the two sides of the ⇔
// are then one statement.
var Coprime = coprimeThm{family.Add(registry.ProofEntry{
	Name: "Coprime",
	Key:  "prop_ca8c17e04b58fae6",
	Build: family.Theorem("∀a b:int. int_coprime((a, b)) ⇔ ∃x y:int. a * x + b * y = &1",
		func(arg *Argument, a, b Term) {
			arg.Show(
				"unfolding int_coprime leaves the Bézout combination "+
					"over the pair's projections, which collapse to a and b",
				// ↦ (∃x y. fst((a, b)) * x + snd((a, b)) * y = &1) ⇔ ∃x y. a * x + b * y = &1
				Unfold(IntCoprimeDef),
				// ↦ the same combination on both sides of the ⇔
				pairs.Collapse(arg.Ctx()),
				// one statement written twice normalizes to ⊤
				TrivialNormalized())
		}),
})}

// IntGcdSpec is what the ℤ constant int_gcd IS. Of a pair's common
// divisors it names one that is nonnegative and that Bézout's identity
// reaches — a ℤ-combination of the two arguments. Maximality is absent
// on purpose: every consumer so far needs the nonnegativity, the two
// divisibilities and the combination, and nothing needs more.
//
// The constant arrives through the define door's spec shape: the
// author's surfaces are the specification and the pointwise existence
// it rests on (BezoutNonneg, one cite — same-file, below). The
// ε-choice over the pair, the projection computation fst((a,b))↦a /
// snd((a,b))↦b, and the name-tag conditioning run inside the
// composite; the projection rows it consumes are the typed deps on
// the pairs chapter, whose ServesAs binds them under the
// fst/snd names the compiler reads.
var IntGcdSpec = intGcdSpecThm{family.DefineSpec(registry.SpecEntry{
	Name: "IntGcdSpec",
	Key:  "prop_9b5a198c25da3e4b",
	Consts: []registry.SpecConst{
		{Const: "int_gcd", Type: "prod(int, int) → int"},
	},
	// `x`/`y` are Bézout's coefficients, in the notation the
	// specification already uses for them.
	Spec: "∀a b:int. &0 ≤ int_gcd((a, b)) ∧ int_gcd((a, b)) ∣ a ∧ " +
		"int_gcd((a, b)) ∣ b ∧ (∃x y:int. int_gcd((a, b)) = a * x + b * y)",
	Deps: []registry.EntryLike{BezoutNonneg, pairs.Fst, pairs.Snd},
	// The obligation IS BezoutNonneg's statement.
	Existence: []Action{Cite(BezoutNonneg)},
})}

// Bezout — every pair of integers has a common divisor that is an
// integer linear combination of the pair.
//
// For nonnegative arguments, subtract the smaller positive argument
// from the larger. The sum of their sizes decreases, and the divisor
// and coefficients lift back through subtraction. Symmetry supplies
// the other order. Finally, apply this descent to the absolute values
// and absorb each argument's sign into its coefficient.
var Bezout = bezoutThm{family.Add(registry.ProofEntry{
	Name: "Bezout",
	Key:  "prop_9dd62302fef06643",
	Build: family.Sections(
		"∀a b:int. ∃d:int. d ∣ a ∧ d ∣ b ∧ (∃x y:int. d = a * x + b * y)",
		func(ctx *Script, headline string) *GoalStackNode {
			subtractionShrinks := ctx.Lemma(Statement{
				Binders:    "∀a b:int.",
				Hypotheses: []string{"&0 ≤ a", "&0 < b", "b ≤ a"},
				Conclusion: "|a - b| < |a|",
			}, func(g *Argument, a, b *Expr[Int], ordered Fact) {
				g.Show(
					"subtracting a positive part strictly decreases the size",
					By(
						Normalized,
						ordered,
						int_real_lift.AbsFixedIffNonneg.At(a),
						int_real_lift.SubNonneg.At(a, b),
						int_real_lift.AbsFixedIffNonneg.At(g.TermAs[Int]("a - b")),
						int_real_lift.LessThanSubAddRight.At(a, b, a),
						int_real_lift.LessThanSelfAddRight.At(a, b)))
			})

			zeroPair := ctx.Lemma("∀a:int. ∃d:int. d ∣ a ∧ d ∣ &0 ∧ (∃x y:int. d = a * x + &0 * y)",
				func(g *Argument, a *Expr[Int]) {
					g.Take(a)
					g.Do(Unfold(IntDividesDef))
					g.Show(
						"a divides itself and zero and remains their linear combination",
						By(
							Normalized,
							int_real_lift.MulRightIdentity.At(a),
							int_real_lift.MulRightZero.At(a),
							int_real_lift.MulLeftZero,
							int_real_lift.AddRightIdentity))
				})

			swap := ctx.Lemma(Statement{
				Binders: "∀a b:int.",
				Hypotheses: []string{
					"∃d:int. d ∣ a ∧ d ∣ b ∧ (∃x y:int. d = a * x + b * y)",
				},
				Conclusion: "∃d:int. d ∣ b ∧ d ∣ a ∧ (∃x y:int. d = b * x + a * y)",
			}, func(g *Argument, a, b *Expr[Int], has Fact) {
				d, triple := g.UnpackAs[Int](has, "d")
				g.Take(d)
				g.Show(
					"the divisor stays fixed and the two coefficients exchange places",
					By(triple, int_real_lift.AddSym))
			})

			subtract := ctx.Lemma(Statement{
				Binders: "∀a b:int.",
				Hypotheses: []string{
					"∃d:int. d ∣ a - b ∧ d ∣ b ∧ (∃x y:int. d = (a - b) * x + b * y)",
				},
				Conclusion: "∃d:int. d ∣ a ∧ d ∣ b ∧ (∃x y:int. d = a * x + b * y)",
			}, func(g *Argument, a, b *Expr[Int], has Fact) {
				d, triple := g.UnpackAs[Int](has, "d")
				parts := g.Conjuncts(
					triple,
					"divides the difference",
					"divides the second argument",
					"linear combination")
				x, y, combination := g.Unpack2As[Int, Int](parts[2], "x", "y")
				dividesA := g.Have(
					"adding the cofactors reconstructs a",
					"d ∣ a",
					Derive(func(c *Argument) {
						k, difference := c.UnpackAs[Int](c.Unfolded(parts[0], IntDividesDef), "k")
						l, second := c.UnpackAs[Int](c.Unfolded(parts[1], IntDividesDef), "l")
						c.Do(Unfold(IntDividesDef))
						c.Take(c.TermAs[Int]("k + l"))
						c.Show(
							"a is d times the sum of the two cofactors",
							By(
								Normalized,
								difference,
								second,
								int_real_lift.EqSubRightAdd.At(a, b, c.TermAs[Int]("d * k")),
								int_real_lift.LeftDistrib.At(d, k, l)))
					}))
				transported := g.Have(
					"the second coefficient absorbs the subtraction",
					"d = a * x + b * (y - x)",
					By(
						combination,
						int_real_lift.SubRightDistrib.At(a, b, x),
						int_real_lift.SubLeftDistrib.At(b, y, x),
						int_real_lift.SubAddLeft.At(g.TermAs[Int]("b * y"), g.TermAs[Int]("b * x")),
						int_real_lift.AddAssoc.At(
							g.TermAs[Int]("a * x - b * x"), g.TermAs[Int]("b * x"), g.TermAs[Int]("b * y - b * x")),
						int_real_lift.SubAddRight))
				g.Take(d)
				g.Show(
					"the divisor and its transformed combination lift to the original pair",
					By(Normalized, dividesA, parts[1], transported))
			})

			descent := ctx.Lemma(Statement{
				Binders: "∀a b:int.",
				Hypotheses: []string{
					"∀u v:int. " +
						"    |u| + |v| < |a| + |b| ⇒ " +
						"    (&0 ≤ u ∧ &0 ≤ v ⇒ ∃d:int. d ∣ u ∧ d ∣ v ∧ (∃x y:int. d = u * x + v * y))",
					"&0 ≤ a",
					"&0 ≤ b",
				},
				Conclusion: "∃d:int. d ∣ a ∧ d ∣ b ∧ (∃x y:int. d = a * x + b * y)",
			}, func(g *Argument, a, b *Expr[Int], ih, aNonneg, bNonneg Fact) {
				nzB := g.Unless(
					g.Term("b = &0"),
					"a zero second argument gives the boundary pair",
					Given(func(c *Argument, bZero Fact) {
						c.Show(
							"the boundary pair supplies the divisor",
							By(Normalized, bZero, At(zeroPair, a)))
					}))
				nzA := g.Unless(
					g.Term("a = &0"),
					"a zero first argument gives the swapped boundary pair",
					Given(func(c *Argument, aZero Fact) {
						c.Show(
							"swap the boundary pair",
							By(Normalized, aZero, At(zeroPair, b), At(swap, b, c.TermAs[Int]("&0"))))
					}))
				g.Cases(g.Term("b ≤ a"))
				g.When(
					"subtract b from the larger a",
					func(c *Argument, ordered Fact) {
						drop := c.Have(
							"the first coordinate decreases",
							"|a - b| < |a|",
							By(
								nzB,
								ordered,
								aNonneg,
								bNonneg,
								int_real_lift.LessThanSplit.At(c.TermAs[Int]("&0"), b),
								At(subtractionShrinks, a, b)))
						smaller := c.Have(
							"the pair's summed size decreases",
							"|a - b| + |b| < |a| + |b|",
							By(
								drop,
								int_real_lift.LessThanAddLeft.At(
									c.TermAs[Int]("|b|"), c.TermAs[Int]("|a - b|"), c.TermAs[Int]("|a|")),
								int_real_lift.AddSym.At(c.TermAs[Int]("|a - b|"), c.TermAs[Int]("|b|")),
								int_real_lift.AddSym.At(c.TermAs[Int]("|a|"), c.TermAs[Int]("|b|"))))
						previous := c.Have(
							"the smaller nonnegative pair has its divisor",
							"∃d:int. d ∣ a - b ∧ d ∣ b ∧ (∃x y:int. d = (a - b) * x + b * y)",
							By(smaller, ordered, bNonneg, ih.At(c.TermAs[Int]("a - b"), b), int_real_lift.SubNonneg.At(a, b)))
						c.Show(
							"lift its combination through subtraction",
							By(previous, At(subtract, a, b)))
					})
				g.Otherwise(
					"subtract a from the larger b and swap back",
					func(c *Argument, notOrdered Fact) {
						ordered := c.Have(
							"a fits inside b",
							"a ≤ b",
							By(notOrdered, int_real_lift.NotLessThan.At(a, b), int_real_lift.LessEqOfLessThan.At(a, b)))
						drop := c.Have(
							"the larger coordinate decreases",
							"|b - a| < |b|",
							By(
								nzA,
								ordered,
								aNonneg,
								bNonneg,
								int_real_lift.LessThanSplit.At(c.TermAs[Int]("&0"), a),
								At(subtractionShrinks, b, a)))
						smaller := c.Have(
							"the swapped smaller pair has smaller summed size",
							"|b - a| + |a| < |a| + |b|",
							By(
								Normalized,
								drop,
								int_real_lift.LessThanAddLeft.At(
									c.TermAs[Int]("|a|"), c.TermAs[Int]("|b - a|"), c.TermAs[Int]("|b|")),
								int_real_lift.AddSym.At(c.TermAs[Int]("|b - a|"), c.TermAs[Int]("|a|"))))
						previous := c.Have(
							"the smaller nonnegative pair has its divisor",
							"∃d:int. d ∣ b - a ∧ d ∣ a ∧ (∃x y:int. d = (b - a) * x + a * y)",
							By(smaller, ordered, aNonneg, ih.At(c.TermAs[Int]("b - a"), a), int_real_lift.SubNonneg.At(b, a)))
						c.Show(
							"lift through subtraction and exchange the coefficients",
							By(previous, At(subtract, b, a), At(swap, b, a)))
					})
			})

			measureNonneg := ctx.Lemma("∀u v:int. &0 ≤ |u| + |v|", func(g *Argument, u, v *Expr[Int]) {
				g.Show(
					"both absolute values are nonnegative",
					By(
						int_real_lift.AbsNonneg.At(u),
						int_real_lift.AbsNonneg.At(v),
						int_real_lift.LessEqSelfAddRight.At(g.TermAs[Int]("|u|"), g.TermAs[Int]("|v|")),
						int_real_lift.LessEqTrans.At(
							g.TermAs[Int]("&0"), g.TermAs[Int]("|u|"), g.TermAs[Int]("|u| + |v|"))))
			})
			nonnegative := ctx.Lemma(Statement{
				Binders:    "∀a b:int.",
				Hypotheses: []string{"&0 ≤ a", "&0 ≤ b"},
				Conclusion: "∃d:int. d ∣ a ∧ d ∣ b ∧ (∃x y:int. d = a * x + b * y)",
			}, func(g *Argument, a, b *Expr[Int], aNonneg, bNonneg Fact) {
				g.Do(Cite(measureNonneg))
				measure := g.TermAs[Op[Int]]("λa:int. λb:int. |a| + |b|")
				property := g.TermAs[Fun2[Int, Int, Bool]](
					"λa:int. λb:int. &0 ≤ a ∧ &0 ≤ b ⇒ ∃d:int. d ∣ a ∧ d ∣ b ∧ (∃x y:int. d = a * x + b * y)")
				// The induction door reads the raw implication, with the predicate
				// and measure in their stated binder order.
				g.Show(
					"induct on the summed sizes of the pair",
					ByInduction(At(ctx.AtTypeVars(ctx.Dep(int_embed.PairMeasureInduction),
						TypeBinder.BindA[Int](), TypeBinder.BindB[Int]()), property, measure),
						g.Hyp("∀u v:int. &0 ≤ |u| + |v|"), aNonneg, bNonneg,
						Case(
							"subtraction supplies the descent obligation",
							By(descent))))
			})

			return ctx.Theorem(headline, func(g *Argument, a, b *Expr[Int]) {
				d, triple := g.ObtainAs[Int](
					"apply nonnegative Bézout to the two magnitudes",
					"∃d:int. d ∣ |a| ∧ d ∣ |b| ∧ (∃x y:int. d = |a| * x + |b| * y)",
					By(
						int_real_lift.AbsNonneg.At(a),
						int_real_lift.AbsNonneg.At(b),
						At(nonnegative, g.TermAs[Int]("|a|"), g.TermAs[Int]("|b|"))))
				parts := g.Conjuncts(
					triple,
					"divides the first magnitude",
					"divides the second magnitude",
					"magnitude combination")
				x, y, combination := g.Unpack2As[Int, Int](parts[2], "x", "y")
				transported := g.Have(
					"absorb each sign into its coefficient",
					"d₀ = a * (sgn(a) * x) + b * (sgn(b) * y)",
					By(
						Normalized,
						combination,
						int_real_lift.SgnMulSelfIsAbs.At(a),
						int_real_lift.SgnMulSelfIsAbs.At(b),
						int_real_lift.MulSym.At(g.TermAs[Int]("sgn(a)"), a),
						int_real_lift.MulSym.At(g.TermAs[Int]("sgn(b)"), b),
						int_real_lift.MulAssoc.At(a, g.TermAs[Int]("sgn(a)"), x),
						int_real_lift.MulAssoc.At(b, g.TermAs[Int]("sgn(b)"), y)))
				g.Take(d)
				g.Show(
					"divisibility forgets the signs and the adjusted coefficients give the original combination",
					By(Normalized, transported, parts[0], parts[1], AbsDividend.At(d, a), AbsDividend.At(d, b)))
			})
		}),
})}

// BezoutNonneg — the reachable common divisor can be taken
// nonnegative: pass Bézout's d to its absolute value. The size divides
// whatever d divides, it is nonnegative outright, and the combination
// survives the sign change with its coefficients negated.
//
// Only the negative arm touches the size at all — splitting on
// &0 ≤ d directly is what makes the first arm free.
var BezoutNonneg = bezoutNonnegThm{family.Add(registry.ProofEntry{
	Name: "BezoutNonneg",
	Key:  "prop_6d3c06a7a0d82da2",
	Build: family.Theorem(
		"∀a b:int. ∃d:int. &0 ≤ d ∧ d ∣ a ∧ d ∣ b ∧ (∃x y:int. d = a * x + b * y)",
		func(g *Argument, a, b Term) {
			v := ops(g.Ctx())
			zero := v.Zero
			neg := func(t Term) Term { return v.Neg.Apply(t) }
			mul := func(s, t Term) Term { return v.Mul.Apply(s, t) }
			add := func(s, t Term) Term { return v.Add.Apply(s, t) }

			d, triple := g.Unpack(g.Have(
				"Bézout's triple at the pair — the sibling theorem",
				// bare: the claim IS the theorem at (a, b)
				"∃d:int. d ∣ a ∧ d ∣ b ∧ (∃x y:int. d = a * x + b * y)",
				Cite(Bezout)))
			x, y, comb := g.Unpack2(g.Have(
				"its combination, Skolemized",
				"∃x y:int. d₀ = a * x + b * y",
				By(triple)))

			g.Cases(v.Le.Apply(zero, d))
			g.When(
				"&0 ≤ d₀: the triple already qualifies as it stands",
				func(c *Argument, nonneg Fact) {
					c.Take(d)
					c.Show(
						"d₀ itself, with its own combination",
						By(nonneg, triple, comb))
				})
			g.Otherwise(
				"d₀ < &0: pass to the size, negating the coefficients",
				func(c *Argument, notNonneg Fact) {
					size := c.Have(
						"the size is the negation",
						"|d₀| = int_neg(d₀)",
						By(
							notNonneg,
							At(int_real_lift.NotLessThan, d, zero),
							At(int_real_lift.LessEqOfLessThan, d, zero),
							At(int_real_lift.NegNonneg, d),
							At(int_real_lift.AbsFixedIffNonneg, neg(d)),
							int_real_lift.AbsEven))
					divA := c.Have(
						"the size divides a — divisibility does not see the divisor's sign",
						"|d₀| ∣ a",
						By(triple, AbsDivisor))
					divB := c.Have(
						"and b likewise",
						"|d₀| ∣ b",
						By(triple, AbsDivisor))
					negComb := c.Have(
						"negating the combination negates its coefficients",
						"int_neg(d₀) = a * int_neg(x₀) + b * int_neg(y₀)",
						By(
							Normalized,
							comb,
							// −(ax + by) = (&0 + &0) − (ax + by) = (&0 − ax) + (&0 − by)
							At(int_real_lift.SubAddPairwise, zero, zero, mul(a, x), mul(b, y)),
							At(int_real_lift.AddLeftIdentity, zero),
							At(int_real_lift.SubLeftZero, add(mul(a, x), mul(b, y))),
							At(int_real_lift.SubLeftZero, mul(a, x)),
							At(int_real_lift.SubLeftZero, mul(b, y)),
							// and a · −x₀ / b · −y₀ absorb the signs
							At(int_real_lift.MulRightNeg, a, x),
							At(int_real_lift.MulRightNeg, b, y)))
					joined := c.Have(
						"so the size is that combination outright",
						"|d₀| = a * int_neg(x₀) + b * int_neg(y₀)",
						By(size, negComb))
					c.Take(v.Abs.Apply(d))
					c.Show(
						"the size: nonnegative, dividing both, with the negated coefficients",
						By(joined, divA, divB, int_real_lift.AbsNonneg))
				})
		}),
})}
