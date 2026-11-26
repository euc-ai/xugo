// nat_parity.go — the chapter: even and odd.
//
// Five parts, marked by banners:
//
// - The defining equations of nat_even and nat_odd
// - nat_even and nat_odd are complementary
// - Parity is a homomorphism onto the two-element algebra
// - Parity, turned back into arithmetic
// - Parity, read off a remainder

package nat_parity

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_divides"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The defining equations of nat_even and nat_odd
// ---------------------------------------------------------------------------
//
// Both predicates are primitive recursions over `num` that flip at every
// successor and differ only in where they start, and both are DEFINED
// by those clauses (`family.Define`, compiled against peano.Recursion
// at the result type bool — the principle is polymorphic in the result
// type, so a bool-valued recursion needs no new principle).
//
// What the two equations come out AS is what every later file in this
// chapter cites them by, so the chapter's standing rule on bare cites is
// stated here, at their source. Each is a CLAUSE PACK — a conjunction
// whose ∀ lives inside one conjunct, `nat_even(0) ∧ (∀n. …)` — so there is
// no outer binder for a witness to land on and `term_specialize` is
// rejected outright. Cites of NatEven and NatOdd are therefore bare, and that
// is forced rather than chosen; the same holds for every recursion
// equation this chapter borrows from nat_arith. Two other kinds of cite are
// bare for their own reasons, stated where they stand: a ground equation
// has no binder at all (the numeral bridges), and a cite that fires as a
// goal REWRITE installs no hypothesis to ground (peano.SucNotZero).
// Every remaining cite in the chapter carries its instance.

// ---------------------------------------------------------------------------
// NatEven — the recursion equations of nat_even
// ---------------------------------------------------------------------------

// NatEven — nat_even defined: zero is even, and every successor disagrees
// with its predecessor.
var NatEven = natEvenThm{family.Define(registry.DefEntry{
	Name:      "NatEven",
	Key:       "prop_a103059e97199eb7",
	Const:     "nat_even",
	Type:      "num → bool",
	Equations: []string{"nat_even(0) ⇔ ⊤", "∀n:num. nat_even(suc(n)) ⇔ ¬nat_even(n)"},
})}

// ---------------------------------------------------------------------------
// NatOdd — the recursion equations of nat_odd
// ---------------------------------------------------------------------------

// NatOdd — nat_odd defined: zero is not odd, and every successor disagrees
// with its predecessor.
var NatOdd = natOddThm{family.Define(registry.DefEntry{
	Name:      "NatOdd",
	Key:       "prop_d68b2714d15e1b98",
	Const:     "nat_odd",
	Type:      "num → bool",
	Equations: []string{"nat_odd(0) ⇔ ⊥", "∀n:num. nat_odd(suc(n)) ⇔ ¬nat_odd(n)"},
})}

// ---------------------------------------------------------------------------
// nat_even and nat_odd are complementary
// ---------------------------------------------------------------------------
//
// Only OddIffNotEven carries an argument. The converse biconditional,
// "not both" and "at least one" are the same sentence rearranged, so
// each is one ground instance of it and no more — separate members
// because they are separate readings, not separate facts, and a
// consumer holding nat_even(m) and owing ¬nat_odd(m) cannot reach for the
// wrong one.

// ---------------------------------------------------------------------------
// OddIffNotEven — the hinge
// ---------------------------------------------------------------------------

// OddIffNotEven — odd is the negation of even, and the hinge everything
// else in the chapter turns on. Induction on n: the two recursions start
// apart, and each successor negates both of them, so an equivalence once
// established survives every step.
var OddIffNotEven = oddIffNotEvenThm{family.Add(registry.ProofEntry{
	Name: "OddIffNotEven",
	Key:  "prop_b599417f7501d02f",
	Build: family.Theorem("∀n:num. nat_odd(n) ⇔ ¬nat_even(n)",
		func(a *Argument) {
			a.Induct("n")
			a.Base(
				"at 0 both sides are false — zero is not odd, and zero is even",
				By(NatOdd, NatEven))
			a.Step(
				"at suc(n): one successor negates each predicate exactly once",
				func(b *Argument, ih Fact) { // nat_odd(n) ⇔ ¬nat_even(n)
					b.Show(
						"so the successor goal is that same equivalence with both sides negated",
						By(Normalized, ih, NatOdd, NatEven))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The three propositional readings
// ---------------------------------------------------------------------------

// EvenIffNotOdd — the same fact read from the other side: even is
// exactly failing to be odd. This is the reading an argument reaches for
// when what it holds is about evenness and what it owes denies oddness.
var EvenIffNotOdd = evenIffNotOddThm{family.Add(registry.ProofEntry{
	Name: "EvenIffNotOdd",
	Key:  "prop_d989ddccc7a3b243",
	Build: family.Theorem("∀n:num. nat_even(n) ⇔ ¬nat_odd(n)",
		func(a *Argument, n Term) {
			// Normalized is load-bearing, and not because a premise is
			// missing: the double negation cancels under Basic(), so with
			// the shaping the leaf settles there and mints no CNF key.
			// Drop it and the same premise list reaches the refuter.
			a.Show(
				"negate both sides of the equivalence at n₀ and cancel the double negation",
				By(Normalized, At(OddIffNotEven, n))) // nat_odd(n₀) ⇔ ¬nat_even(n₀)
		}),
})}

// NotEvenAndOdd — at most one of the two holds: the reading wanted when
// a case analysis has produced both and needs the contradiction.
var NotEvenAndOdd = notEvenAndOddThm{family.Add(registry.ProofEntry{
	Name: "NotEvenAndOdd",
	Key:  "prop_69f465d5afb30973",
	Build: family.Theorem("∀n:num. ¬(nat_even(n) ∧ nat_odd(n))",
		func(a *Argument, n Term) {
			a.Show(
				"being odd already denies being even, so the two cannot hold together at n₀",
				By(At(OddIffNotEven, n))) // nat_odd(n₀) ⇔ ¬nat_even(n₀)
		}),
})}

// EvenOrOdd — at least one of the two holds: the reading wanted when an
// argument splits on parity and needs the split to be exhaustive.
var EvenOrOdd = evenOrOddThm{family.Add(registry.ProofEntry{
	Name: "EvenOrOdd",
	Key:  "prop_e444ad9d06f4d195",
	Build: family.Theorem("∀n:num. nat_even(n) ∨ nat_odd(n)",
		func(a *Argument, n Term) {
			a.Show(
				"failing to be even is what being odd means, so n₀ cannot escape both",
				By(OddIffNotEven))
		}),
})}

// ---------------------------------------------------------------------------
// Parity is a homomorphism onto the two-element algebra
// ---------------------------------------------------------------------------
//
// Forget everything about a natural number except whether it is even,
// and ℕ's arithmetic survives the forgetting: `+` becomes `⇔`, `*`
// becomes `∨`, and exponentiation is the multiplicative law iterated.
// The three members here are exactly the statements that it does.
//
// All three are one induction on the operand the defining recursion
// moves, and all three have the same two-branch shape. At zero the
// operation collapses — the sum is the other summand, the product and
// the power are constants — and the base predicate decides the branch
// outright. At a successor the recursion clause peels one step off that
// operand, and the previous law reads the parity of what is left. What
// the peeling exposes differs: `*` and `nat_pow` shed a copy of the other
// operand, while `+` carries the successor outward and sheds nothing,
// which is why EvenAdd's step is a cancellation where the other two are
// absorptions. So EvenMul leans on EvenAdd and EvenPow leans on EvenMul,
// and the file reads downward in exactly that order.
//
// Cites of NatEven and of the three recursion equations are BARE, for the
// chapter's standing reason — they are clause packs with no outer binder
// to ground at (the defining equations above state it at their source). The two
// further bare cites here are marked where they stand.

// ---------------------------------------------------------------------------
// EvenAdd — addition becomes equivalence
// ---------------------------------------------------------------------------

// EvenAdd — a sum is even exactly when its two summands have the same
// parity. Induction on the left summand: the successor clause of +
// carries one successor out of the sum, which negates the left side of
// the goal, while on the right suc(m) negates nat_even(m). Negating one side
// of an equivalence negates the equivalence, so the two negations cancel
// and what is left standing is the hypothesis.
var EvenAdd = evenAddThm{family.Add(registry.ProofEntry{
	Name: "EvenAdd",
	Key:  "prop_b2f9d24fd73a502e",
	Build: family.Theorem("∀m n:num. nat_even(m + n) ⇔ (nat_even(m) ⇔ nat_even(n))",
		func(a *Argument) {
			a.Induct("m")
			a.Base(
				"at 0: the sum is n itself, and zero is even, so both sides read nat_even(n)",
				By(Normalized, NatEven, nat_arith.Add))
			a.Step(
				"at suc(m): one negation appears on each side of the goal",
				func(b *Argument, ih Fact) { // ∀n. nat_even(m + n) ⇔ (nat_even(m) ⇔ nat_even(n))
					b.Show(
						"the successor comes out of the sum to negate the left side, and "+
							"negates nat_even(m) on the right — one each, so the hypothesis stands",
						By(ih, NatEven, nat_arith.Add))
				})
		}),
})}

// ---------------------------------------------------------------------------
// EvenMul — multiplication becomes disjunction
// ---------------------------------------------------------------------------

// EvenMul — a product is even exactly when at least one factor is.
// Induction on the left factor: the successor clause of * takes one copy
// of the right factor out of the product and leaves it behind as a
// summand, so the step is a question about a sum — and EvenAdd answers
// that by comparing the parities of the two summands.
var EvenMul = evenMulThm{family.Add(registry.ProofEntry{
	Name: "EvenMul",
	Key:  "prop_ab2322650e004184",
	Build: family.Theorem("∀m n:num. nat_even(m * n) ⇔ nat_even(m) ∨ nat_even(n)",
		func(a *Argument) {
			v := ops(a.Ctx())
			m := a.Binder("m")

			a.Induct(m)
			a.Base(
				"at 0: the product is 0, which is even — and the "+
					"disjunct nat_even(0) holds too, so both sides are true",
				By(Normalized, NatEven, nat_arith.Mul))
			a.Step(
				"at suc(m): the product sheds one copy of the other factor "+
					"as a summand, and suc(m) is even exactly when m is not",
				func(b *Argument, ih Fact) {
					n := b.Fix()        // n₀
					prod := v.Mul(m, n) // the smaller product, which the shed copy joins as a summand

					b.Show(
						"so both sides say that nat_even(m) forces nat_even(n₀) — the "+
							"left because a sum is even exactly when its two summands agree",
						By(
							Normalized,
							ih.At(n), // nat_even(m * n₀) ⇔ (nat_even(m) ∨ nat_even(n₀))
							NatEven,
							nat_arith.Mul,
							At(EvenAdd, prod, n), // nat_even(m*n₀ + n₀) ⇔ (nat_even(m*n₀) ⇔ nat_even(n₀))
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// EvenPow — exponentiation, and the exponent it has to exclude
// ---------------------------------------------------------------------------

// EvenPow — a power is even exactly when its base is even and the
// exponent is not zero. Induction on the exponent, and each branch
// supplies one half of the statement: the empty product is 1, which is
// odd whatever the base was, and that is why a zero exponent has to be
// excluded; while every further factor of the base lets the base's own
// parity decide alone, and that is why no larger exponent needs
// excluding.
var EvenPow = evenPowThm{family.Add(registry.ProofEntry{
	Name: "EvenPow",
	Key:  "prop_8fbd6f6c0b05d76b",
	Build: family.Theorem("∀m n:num. nat_even(nat_pow(m, n)) ⇔ nat_even(m) ∧ n ≠ 0",
		func(a *Argument) {
			v := ops(a.Ctx())
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"at 0: the power is 1, that is suc(0), which is odd for every base — and on the right 0 ≠ 0 fails",
				By(
					NatEven,
					nat_arith.NatPow,
					nat_arith.OneIsSucZero /* 1 = suc(0) */))
			a.Step(
				"at suc(n): the power sheds one factor of the base, and "+
					"a product is even exactly when one of its two factors is",
				func(b *Argument, ih Fact) {
					m := b.Fix()       // m₀
					pow := v.Exp(m, n) // the smaller power, which the shed factor multiplies

					b.Show(
						"that shed factor's own parity absorbs the hypothesis's conjunction, "+
							"and suc(n) ≠ 0 discharges the side condition the successor brings",
						By(
							Normalized,
							ih.At(m), // nat_even(nat_pow(m₀, n)) ⇔ (nat_even(m₀) ∧ n ≠ 0)
							nat_arith.NatPow,
							// Fires as a goal rewrite: the suc(n) ≠ 0 conjunct
							// collapses rather than installing, so there is no
							// hypothesis to ground and the cite takes no witness.
							peano.SucNotZero,
							At(EvenMul, m, pow), // nat_even(m₀ * nat_pow(m₀, n)) ⇔ nat_even(m₀) ∨ nat_even(nat_pow(m₀, n))
						))
				})
		}),
})}

// ---------------------------------------------------------------------------
// Parity, turned back into arithmetic
// ---------------------------------------------------------------------------
//
// Everything above this file treats nat_even and nat_odd as predicates. Here
// they become shapes: an even number IS a double and an odd one IS the
// successor of a double, so a parity hypothesis can be spent on an
// equation rather than on a case analysis.
//
// One lemma carries the file. Every natural number is 2m or suc(2m),
// and which of the two it is, is exactly its parity — that is
// doubleOrSucDouble, and the only member here that argues. Its
// induction turns on the fact that a successor swaps the two shapes and
// moves the witness with them: an odd n = suc(2m) has the even
// successor suc(suc(2m)) = 2·suc(m), where the witness climbs by one,
// while an even n = 2m has the odd successor suc(2m), where it does
// not. The two characterisations below it are that lemma read once in
// each direction, the converse of each supplied by EvenDouble or
// OddSucDouble — the two members that say the shapes really do carry
// the parity claimed.
//
// The numeral 2 is opaque to the recursion nat_even runs on: nothing about
// suc reaches inside a binary literal. EvenDouble and the shape lemma
// are the two members that have to look inside it, and both pay
// nat_arith.Two and nat_arith.OneIsSucZero for the privilege.
//
// Cites of NatEven, NatOdd and the recursion equations of + are bare for the
// chapter's standing reason — clause packs with no outer binder, stated
// in the defining equations above. The two numeral bridges are bare for the other
// standing reason: a ground equation has no binder at all.

// ---------------------------------------------------------------------------
// EvenDouble · OddSucDouble — the two shapes have the parities claimed
// ---------------------------------------------------------------------------

// EvenDouble — every double is even. The product law reduces the
// question to the two factors separately, and one of them is the
// numeral 2: unfolding it to suc(suc(0)) lets nat_even flip twice from zero
// and settle the left disjunct, after which the other factor is free.
var EvenDouble = evenDoubleThm{family.Add(registry.ProofEntry{
	Name: "EvenDouble",
	Key:  "prop_fde1922ae4407aec",
	Build: family.Theorem("∀n:num. nat_even(2 * n)",
		func(a *Argument, n Term) {
			two := a.Ctx().Numeral(2)

			a.Show(
				"2 is even — two flips from zero — so a product with it is even however the other factor falls",
				By(
					At(EvenMul, two, n), // nat_even(2 · n₀) ⇔ nat_even(2) ∨ nat_even(n₀)
					NatEven,
					nat_arith.Two,          // 2 = suc(1)
					nat_arith.OneIsSucZero, // 1 = suc(0)
				))
		}),
})}

// OddSucDouble — one more than a double is odd. EvenDouble settles the
// double itself, complementarity reads that as "not odd", and a single
// successor of nat_odd's recursion flips it back.
var OddSucDouble = oddSucDoubleThm{family.Add(registry.ProofEntry{
	Name: "OddSucDouble",
	Key:  "prop_7dfc571a9cfe9ccd",
	Build: family.Theorem("∀n:num. nat_odd(suc(2 * n))",
		func(a *Argument, n Term) {
			v := ops(a.Ctx())
			double := v.Mul(a.Ctx().Numeral(2), n) // 2 · n₀

			a.Show(
				"the double is even, hence not odd, and its successor disagrees with it",
				By(
					At(EvenDouble, n),         // nat_even(2 · n₀)
					At(OddIffNotEven, double), // nat_odd(2 · n₀) ⇔ ¬nat_even(2 · n₀)
					NatOdd,
				))
		}),
})}

// ---------------------------------------------------------------------------
// doubleOrSucDouble — every number has one of the two shapes
// ---------------------------------------------------------------------------

// doubleOrSucDouble — every natural number is a double or the successor
// of one, and its parity says which. Induction on n. Zero is even and
// is its own double. At a successor the two shapes exchange places, so
// the step splits on n's parity rather than on suc(n)'s: an even n is
// 2m and suc(n) = suc(2m) needs no new witness, while an odd n is
// suc(2m) and suc(n) = suc(suc(2m)) is twice suc(m) — the only place in
// the file where the witness has to be built rather than carried, and
// the only place that has to know what 2 is.
//
// Unexported, and not because its fan-in is small: the two members
// below it already SAY it. EvenOrOdd and the hinge split any n by
// parity, and the two characterisations then supply the matching shape,
// so a reader with the chapter's public surface can recover this
// statement in one propositional step. That is what makes it chapter
// implementation rather than API — the API is not missing anything.
var doubleOrSucDouble = doubleOrSucDoubleThm{family.Add(registry.ProofEntry{
	Name: "doubleOrSucDouble",
	Key:  "prop_d15783c583912ade",
	Build: family.Theorem(
		"∀n:num. (nat_even(n) ⇒ ∃m:num. n = 2 * m) ∧ (¬nat_even(n) ⇒ ∃m:num. n = suc(2 * m))",
		func(a *Argument) {
			ctx := a.Ctx()
			v := ops(ctx)
			two := ctx.Numeral(2)
			n := a.Binder("n")

			// Where a leaf below carries Normalized, that is load-bearing and
			// not a premise gap: the list is complete but does not meet the
			// closer in clause form, and without the shaping the same list
			// reaches the refuter and mints a key the argument has no use for.
			a.Induct(n)
			a.Base(
				"at 0: zero is even, which empties the odd branch, and it is its own double",
				By(Normalized, NatEven, At(nat_arith.MulZero, two))) // 2 · 0 = 0
			a.Step(
				"at suc(n): a successor exchanges the two shapes, so n's parity decides which one suc(n) has",
				func(b *Argument, ih Fact) { // n is a double, or the successor of one
					b.Cases(v.Even(n))
					b.When(
						"n even: suc(n) is the odd one, and n's own half serves it unchanged",
						func(c *Argument, isEven Fact) {
							// The half is never named: the goal's own ∃ takes the
							// same one, so only the equation is carried forward.
							_, isDouble := c.Obtain(
								"being even is what puts n in the first shape",
								"∃m:num. n = 2 * m",
								By(isEven, ih)) // n = 2 · m₀

							c.Show(
								"so suc(n) = suc(2 · m₀) is the odd shape at that same half, and suc(n) cannot also be even",
								By(isDouble, isEven, NatEven))
						})
					b.Otherwise(
						"n odd: suc(n) is the even one, and its half is one more than n's",
						func(c *Argument, notEven Fact) {
							m, isSucDouble := c.Obtain(
								"failing to be even is what puts n in the second shape",
								"∃m:num. n = suc(2 * m)",
								By(notEven, ih)) // n = suc(2 · m₀)

							doubled := c.Have(
								"twice suc(m₀) is 2 + 2 · m₀, and unfolding 2 to suc(suc(0)) "+
									"turns that sum into the two successors suc(n) carries",
								MakeProp(v.Suc(n).Eq(v.Mul(two, v.Suc(m)))),
								By(
									isSucDouble,
									At(nat_arith.MulSuc, two, m), // 2 · suc(m₀) = 2 + 2 · m₀
									nat_arith.Two,                // 2 = suc(1)
									nat_arith.OneIsSucZero,       // 1 = suc(0)
									nat_arith.Add,
								))

							c.Show(
								"so suc(n) is a double — and it is even because n is not, which empties the odd branch",
								By(Normalized, notEven, doubled, NatEven))
						})
				})
		}),
})}

// ---------------------------------------------------------------------------
// EvenIffDouble · OddIffSucDouble — the two characterisations
// ---------------------------------------------------------------------------

// EvenIffDouble — a number is even exactly when it is a double. The
// file's shape lemma — every number is 2m or suc(2m), according to its
// parity — supplies the forward reading at n directly; the converse is
// EvenDouble, which says nothing about n and everything about doubles.
var EvenIffDouble = evenIffDoubleThm{family.Add(registry.ProofEntry{
	Name: "EvenIffDouble",
	Key:  "prop_c27adf97dcca40ec",
	Build: family.Theorem("∀n:num. nat_even(n) ⇔ ∃m:num. n = 2 * m",
		func(a *Argument, n Term) {
			a.Show(
				"forwards, evenness picks the shape lemma's first branch; backwards, every double is even",
				By(
					// (nat_even(n₀) ⇒ ∃m. n₀ = 2m) ∧ (¬nat_even(n₀) ⇒ ∃m. n₀ = suc(2m))
					At(doubleOrSucDouble, n),
					// Bare: the instance wanted is at the half, which enters only
					// as the witness of the goal's own ∃.
					EvenDouble,
				))
		}),
})}

// OddIffSucDouble — a number is odd exactly when it is one more than a
// double. The same lemma read through its other branch, which
// complementarity reaches: being odd is failing to be even, and that is
// the branch's antecedent. The converse is OddSucDouble.
var OddIffSucDouble = oddIffSucDoubleThm{family.Add(registry.ProofEntry{
	Name: "OddIffSucDouble",
	Key:  "prop_ee008c69574fb461",
	Build: family.Theorem("∀n:num. nat_odd(n) ⇔ ∃m:num. n = suc(2 * m)",
		func(a *Argument, n Term) {
			a.Show(
				"odd is not even, which is the shape lemma's second "+
					"branch; backwards, every successor of a double is odd",
				By(
					At(OddIffNotEven, n), // nat_odd(n₀) ⇔ ¬nat_even(n₀)
					// (nat_even(n₀) ⇒ ∃m. n₀ = 2m) ∧ (¬nat_even(n₀) ⇒ ∃m. n₀ = suc(2m))
					At(doubleOrSucDouble, n),
					// Bare, for EvenDouble's reason above.
					OddSucDouble,
				))
		}),
})}

// ---------------------------------------------------------------------------
// Parity, read off a remainder
// ---------------------------------------------------------------------------
//
// Dividing by 2 destroys everything about a number except its parity,
// so `nat_even n` and `nat_mod(n, 2)` are the same information twice. The first
// two members say exactly that, one residue each: even is remainder 0,
// odd is remainder 1. The last two ask what survives at other moduli —
// an even divisor leaves oddness alone, and a power of 2 is an even
// divisor precisely when the exponent is not 0.
//
// Three of the four turn on one sentence, nat_div_mod's division
// equation m = nat_div(m, n)·n + nat_mod(m, n). It does two jobs here: it bounds
// a residue below its divisor, which is what pins the residue mod 2 down
// to 0 or 1; and it exhibits m as a multiple of n plus its remainder,
// over which parity is additive — so an even divisor contributes an even
// multiple and the remainder carries the whole answer. The odd one out
// is the first member, where both sides are already existentials and
// nothing has to be divided.
//
// The one thing the refuter will not do here is tell numerals apart: it
// sees 0, 1 and 2 as opaque atoms. Two idioms answer that, and this file
// is mostly made of them. To discharge a divisor guard n ≠ 0, unfold the
// numeral one rung to a successor and apply peano.SucNotZero — that is
// nat_arith.Two + SucNotZero for a divisor of 2, nat_arith.OneIsSucZero +
// SucNotZero for 1, and the same pair is what supplies 1 ≠ 0 where a
// residue has to be told apart from 0. To let nat_even's recursion move at
// all, unfold the numeral all the way down — nat_arith.Two AND
// nat_arith.OneIsSucZero, since 2 = suc(1) leaves a 1 that must itself reach
// suc(0) — after which nat_even flips its way to an answer. Each step is
// cheap and there are many of them.
//
// Cites of NatEven, NatOdd and nat_arith.NatPow are bare for the chapter's standing
// reason — clause packs with no outer binder, stated in the defining
// equations above. peano.SucNotZero is bare for the second standing reason (it
// fires as a goal rewrite and installs nothing), and nat_arith.Two /
// nat_arith.OneIsSucZero for the third (ground equations, no binder at all).
// The remaining bare cites are marked where they stand.
//
// One leaf carries Normalized, for the chapter's usual reason: the
// premise list is complete but does not meet the closer in clause form,
// so without the shaping the same list reaches the refuter and mints a
// key the argument has no use for.

// ---------------------------------------------------------------------------
// EvenIffModTwoZero · OddIffModTwoOne — parity IS the residue mod 2
// ---------------------------------------------------------------------------

// EvenIffModTwoZero — a number is even exactly when 2 goes into it
// evenly. Neither side has to be unfolded: the shape characterisation
// already reads evenness as an existential, and nat_div_mod reads a zero
// remainder as one too. The two differ only in which side of the product
// the 2 stands on, so commutativity is the entire bridge.
var EvenIffModTwoZero = evenIffModTwoZeroThm{family.Add(registry.ProofEntry{
	Name: "EvenIffModTwoZero",
	Key:  "prop_1117188be4316186",
	Build: family.Theorem("∀n:num. nat_even(n) ⇔ rem(n, 2) = 0",
		func(a *Argument, n Term) {
			two := a.Ctx().Numeral(2)

			a.Show(
				"both sides say n₀ is a multiple of 2, and they "+
					"disagree only on which side of the product the 2 stands",
				By(
					At(EvenIffDouble, n),              // nat_even(n₀) ⇔ ∃m. n₀ = 2 · m
					At(nat_div_mod.ModEqZero, n, two), // nat_mod(n₀, 2) = 0 ⇔ ∃q. n₀ = q · 2
					// Bare: the instance wanted is at the two ∃-bound
					// witnesses, which neither statement names.
					nat_arith.MulSym,
				))
		}),
})}

// OddIffModTwoOne — a number is odd exactly when 2 goes into it leaving
// 1. Complementarity turns the goal into "not even", the member above
// turns that into "the residue is not 0", and what remains is that a
// residue mod 2 has nowhere else to be: it is below 2, hence 0 or 1.
//
// The dichotomy is the whole proof, and the two directions do not cost
// the same. Forwards nothing more is needed — a residue that is not 0 is
// 1 by the dichotomy. Backwards one has to know that the residue 1 is
// not the residue 0, which is the last two premises of the close.
var OddIffModTwoOne = oddIffModTwoOneThm{family.Add(registry.ProofEntry{
	Name: "OddIffModTwoOne",
	Key:  "prop_d3216af0fba9ea6b",
	Build: family.Theorem("∀n:num. nat_odd(n) ⇔ rem(n, 2) = 1",
		func(a *Argument, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			zero, one, two := ctx.Numeral(0), ctx.Numeral(1), ctx.Numeral(2)
			mod := v.Mod(n, two) // nat_mod(n₀, 2) — the residue the theorem is about

			bound := a.Have(
				"division by 2 leaves a remainder below 2",
				MakeProp(v.LessThan(mod, two)),
				By(
					// 2 ≠ 0 ⇒ n₀ = nat_div(n₀,2)·2 + nat_mod(n₀,2) ∧ nat_mod(n₀,2) < 2
					At(nat_div_mod.Division, n, two),
					nat_arith.Two,    // 2 = suc(1), a successor …
					peano.SucNotZero, // … and no successor is 0, which discharges the divisor guard
				))

			dichotomy := a.Have(
				"and below 2 there is only 0 and 1",
				MakeProp(mod.Eq(zero).Or(mod.Eq(one))),
				By(
					bound,
					// Bare: the ladder crosses suc twice — nat_mod(n₀,2) < suc(1)
					// gives nat_mod(n₀,2) ≤ 1, and nat_mod(n₀,2) < suc(0) gives
					// nat_mod(n₀,2) ≤ 0 — so two instances are wanted.
					nat_order.LessThanSucIffLessEq,
					At(nat_order.LessEqSplit, mod, one), // nat_mod(n₀,2) ≤ 1 ⇔ nat_mod(n₀,2) < 1 ∨ nat_mod(n₀,2) = 1
					nat_arith.Two,                       // 2 = suc(1)
					nat_arith.OneIsSucZero,              // 1 = suc(0)
					At(nat_order.LessEqZeroClause, mod), // nat_mod(n₀,2) ≤ 0 ⇔ nat_mod(n₀,2) = 0
				))

			a.Show(
				"odd is not even, not even is a nonzero residue, and "+
					"of the only two residues 1 is the one that is not 0",
				By(
					dichotomy,
					At(OddIffNotEven, n),     // nat_odd(n₀) ⇔ ¬nat_even(n₀)
					At(EvenIffModTwoZero, n), // nat_even(n₀) ⇔ nat_mod(n₀, 2) = 0
					nat_arith.OneNotZero,     // 1 ≠ 0 — what the ⇐ direction needs, and nothing the refuter knows
				))
		}),
})}

// ---------------------------------------------------------------------------
// DoubleOrSucDoubleBelow — the two shapes, with the half bounded
// ---------------------------------------------------------------------------

// DoubleOrSucDoubleBelow — a number at most 2k is a double 2i with i ≤ k,
// or one more than a double, 2i + 1 with i < k: its parity picks the shape
// (EvenIffDouble, OddIffSucDouble), and the bound on the number bounds the
// half. It is registered after EvenIffModTwoZero because its bounds close
// by the arithmetic closer, whose parity layer reads that member.
var DoubleOrSucDoubleBelow = doubleOrSucDoubleBelowThm{family.Add(registry.ProofEntry{
	Name: "DoubleOrSucDoubleBelow",
	Key:  "prop_df18bdcd1bb30b5e",
	Build: family.Theorem(Statement{
		Binders: "∀k j:num.",
		Hypotheses: []string{
			"j ≤ 2 * k",
		},
		Conclusion: "(∃i:num. i ≤ k ∧ j = 2 * i) ∨ (∃i:num. i < k ∧ j = 2 * i + 1)",
	}, func(a *Argument, k, j *Expr[Nat], bound Fact) {
		a.Cases(a.TermAs[Bool]("nat_even(j)"))
		a.When(
			"an even j is twice a half that is at most k",
			func(b *Argument, even Fact) {
				i, half := b.ObtainAs[Nat](
					"j is twice some i",
					"∃i:num. j = 2 * i",
					By(even, EvenIffDouble))
				b.Do(Left())
				b.Take(i)
				b.Show(
					"2i ≤ 2k bounds i by k",
					ByArith(bound, half))
			})
		a.Otherwise(
			"an odd j is one more than twice a half that is below k",
			func(b *Argument, odd Fact) {
				i, half := b.ObtainAs[Nat](
					"j is one more than twice some i",
					"∃i:num. j = suc(2 * i)",
					By(odd, OddIffNotEven.At(j), OddIffSucDouble.At(j)))
				b.Do(Right())
				b.Take(i)
				b.Show(
					"2i + 1 ≤ 2k bounds i below k",
					ByArith(bound, half))
			})
	}),
})}

// ---------------------------------------------------------------------------
// OddModEven · OddModPowTwo — reducing modulo something else
// ---------------------------------------------------------------------------

// OddModEven — reducing modulo an even number does not disturb oddness.
// Division splits m into the part it takes out and the part it leaves,
// m = nat_div(m,n)·n + nat_mod(m,n); parity is additive over that sum, and an
// even n makes the extracted part even however the quotient falls. So
// the sum's parity is the remainder's parity, which is the claim.
//
// No case split on n = 0 is needed. Division carries its own n ≠ 0
// guard and nat_div_mod.ModZero says
// nat_mod(m, 0) = m — where the equation above holds trivially — so the two
// cases are two halves of a single premise list and one refutation
// settles both.
var OddModEven = oddModEvenThm{family.Add(registry.ProofEntry{
	Name: "OddModEven",
	Key:  "prop_984ee4e8e7412468",
	Build: family.Theorem(Statement{
		Binders: "∀m n:num.",
		Hypotheses: []string{
			"nat_even(n)",
		},
		Conclusion: "nat_odd(rem(m, n)) ⇔ nat_odd(m)",
	},
		func(a *Argument, m, n Term, isEven Fact) {
			v := ops(a.Ctx())
			quot := v.Div(m, n)     // nat_div(m₀, n₀)
			taken := v.Mul(quot, n) // nat_div(m₀,n₀) · n₀ — what division takes out of m₀
			rest := v.Mod(m, n)     // nat_mod(m₀, n₀)   — what it leaves behind

			a.Show(
				"m₀ is a multiple of n₀ plus its remainder; an even n₀ makes "+
					"that multiple even, so the parity of the sum is the remainder's",
				By(
					isEven,
					// n₀ ≠ 0 ⇒ m₀ = nat_div(m₀,n₀)·n₀ + nat_mod(m₀,n₀) ∧ nat_mod(m₀,n₀) < n₀
					At(nat_div_mod.Division, m, n),
					// nat_mod(m₀, 0) = m₀ — the divisor-zero case, where the split is trivial
					At(nat_div_mod.ModZero, m),
					// nat_even(nat_div(m₀,n₀)·n₀ + nat_mod(m₀,n₀)) ⇔ (nat_even(nat_div(m₀,n₀)·n₀) ⇔ nat_even(nat_mod(m₀,n₀)))
					At(EvenAdd, taken, rest),
					// nat_even(nat_div(m₀,n₀)·n₀) ⇔ nat_even(nat_div(m₀,n₀)) ∨ nat_even(n₀)
					At(EvenMul, quot, n),
					// Bare: both sides of the goal's ⇔ want it, one at
					// nat_mod(m₀,n₀) and one at m₀.
					OddIffNotEven,
				))
		}),
})}

// OddModPowTwo — reducing modulo 2ᵏ preserves oddness exactly when
// k ≠ 0. Over the member above it this is one step: 2 is even, so by the
// exponent law 2ᵏ is even whenever k ≠ 0, and an even modulus leaves
// oddness alone. The exponent law's side condition and this statement's
// are the same condition, met once.
//
// The degenerate exponent is what the statement's k ≠ 0 is for. At
// k = 0 the modulus is 2⁰ = 1, every residue mod 1 is 0, and 0 is not
// odd — so the left side is false while nat_odd(n) may not be, and both
// sides are rescued by the conjunct.
//
// nat_mod(n, 1) = 0 is a theorem in its own right, and stays an
// internal fact here rather than becoming a member: it is one step from
// division's remainder bound — below 1 is 0 — so naming it would buy a
// reader nothing this proof does not already show.
var OddModPowTwo = oddModPowTwoThm{family.Add(registry.ProofEntry{
	Name: "OddModPowTwo",
	Key:  "prop_bed790ed6a000c7b",
	Build: family.Theorem("∀n k:num. nat_odd(rem(n, nat_pow(2, k))) ⇔ nat_odd(n) ∧ k ≠ 0",
		func(a *Argument, n Term, k *TermWrapper) {
			ctx := a.Ctx()
			v := ops(ctx)
			zero, one, two := ctx.Numeral(0), ctx.Numeral(1), ctx.Numeral(2)
			pow := v.Exp(two, k)  // 2ᵏ⁰ — the modulus
			unit := v.Mod(n, one) // nat_mod(n₀, 1) — the modulus at the degenerate exponent

			trivial := a.Have(
				"modulo 1 nothing is left over: the remainder is below 1, and below 1 there is only 0",
				MakeProp(unit.Eq(zero)),
				By(
					// 1 ≠ 0 ⇒ n₀ = nat_div(n₀,1)·1 + nat_mod(n₀,1) ∧ nat_mod(n₀,1) < 1
					At(nat_div_mod.Division, n, one),
					nat_arith.OneIsSucZero, // 1 = suc(0), a successor …
					// … and no successor is 0, which discharges the divisor guard
					peano.SucNotZero,
					At(nat_order.LessThanSucIffLessEq, unit, zero), // nat_mod(n₀,1) < suc(0) ⇔ nat_mod(n₀,1) ≤ 0
					At(nat_order.LessEqZeroClause, unit),           // nat_mod(n₀,1) ≤ 0 ⇔ nat_mod(n₀,1) = 0
				))

			evenTwo := a.Have(
				"2 is even: unfolding it to suc(suc(0)) lets nat_even flip twice from zero",
				MakeProp(v.Even(two)),
				By(
					NatEven,
					nat_arith.Two,          // 2 = suc(1)
					nat_arith.OneIsSucZero, // 1 = suc(0)
				))

			evenPow := a.Have(
				"so a power of 2 is even exactly when the exponent is "+
					"not 0 — the exponent law with its base condition settled",
				MakeProp(v.Even(pow).Eq(k.Neq(zero))),
				By(
					Normalized,
					evenTwo,
					At(EvenPow, two, k), // nat_even(2ᵏ⁰) ⇔ nat_even(2) ∧ k₀ ≠ 0
				))

			a.Show(
				"an even modulus keeps oddness, and at exponent 0 the "+
					"modulus is 1, where every residue is 0 and nothing is odd",
				By(
					trivial,
					evenPow,
					At(OddModEven, n, pow), // nat_even(2ᵏ⁰) ⇒ (nat_odd(nat_mod(n₀, 2ᵏ⁰)) ⇔ nat_odd(n₀))
					nat_arith.NatPow,       // nat_pow(m, 0) = 1 — the modulus at the degenerate exponent
					NatOdd,                 // ¬nat_odd(0)
				))
		}),
})}

// ---------------------------------------------------------------------------
// SquareModFour · OddSquareModEight · UpperHalfCountEven — residues mod 4 and 8
// ---------------------------------------------------------------------------

// SquareModFour — the square of an even number is a multiple of 4, and the
// square of an odd number leaves remainder 1 on division by 4:
// (2s)² = 4s² and (2s + 1)² = 4(s² + s) + 1.
var SquareModFour = squareModFourThm{family.Add(registry.ProofEntry{
	Name: "SquareModFour",
	Key:  "prop_76953b0875c1f8d6",
	Build: family.Theorem(
		"∀a:num. (nat_even(a) ⇒ rem(a * a, 4) = 0) ∧ (nat_odd(a) ⇒ rem(a * a, 4) = 1)",
		func(arg *Argument, a *Expr[Nat]) {
			square, four := arg.TermAs[Nat]("a * a"), arg.Ctx().Nat(4)
			arg.Do(SplitConj(
				Case(
					"an even a = 2s squares to 4s², a multiple of 4",
					Derive(func(b *Argument) {
						even := b.Assume()
						s, half := b.ObtainAs[Nat](
							"a = 2s",
							"∃s:num. a = 2 * s",
							By(even, EvenIffDouble.At(a)))
						b.Show(
							"a² = 4s² leaves remainder 0",
							ByArith(
								Scaled(a, half),
								Scaled(s, half),
								nat_div_mod.ModUniq.At(square, four, b.TermAs[Nat]("s * s"), b.Ctx().Nat(0))))
					})),
				Case(
					"an odd a = 2s + 1 squares to 4(s² + s) + 1",
					Derive(func(b *Argument) {
						odd := b.Assume()
						s, half := b.ObtainAs[Nat](
							"a = 2s + 1",
							"∃s:num. a = 2 * s + 1",
							By(odd, OddIffSucDouble.At(a), nat_arith.Add1))
						b.Show(
							"a² = 4(s² + s) + 1 leaves remainder 1",
							ByArith(
								Scaled(a, half),
								Scaled(s, half),
								nat_div_mod.ModUniq.At(square, four, b.TermAs[Nat]("s * s + s"), b.Ctx().Nat(1))))
					}))))
		}),
})}

// OddSquareModEight — an odd square is one more than a multiple of 8.
// Writing m = 2i + 1, m² = 4·i(i + 1) + 1, and i(i + 1) is even, one of two
// consecutive numbers being even; so i(i + 1) = 2c makes m² = 8c + 1.
var OddSquareModEight = oddSquareModEightThm{family.Add(registry.ProofEntry{
	Name: "OddSquareModEight",
	Key:  "prop_d97fe5b2489318c4",
	Build: family.Theorem(Statement{
		Binders: "∀m:num.",
		Hypotheses: []string{
			"nat_odd(m)",
		},
		Conclusion: "∃a:num. m * m = 8 * a + 1",
	}, func(arg *Argument, m *Expr[Nat], odd Fact) {
		i, mIs := arg.ObtainAs[Nat](
			"m is odd: m = 2i + 1",
			"∃i:num. m = suc(2 * i)",
			By(odd, OddIffSucDouble.At(m)))
		c, consecutive := arg.ObtainAs[Nat](
			"i(i + 1) is even, one of two consecutive numbers being even",
			"∃c:num. i * suc(i) = 2 * c",
			By(
				EvenMul.At(i, arg.TermAs[Nat]("suc(i)")),
				NatEven,
				EvenIffDouble.At(arg.TermAs[Nat]("i * suc(i)"))))
		arg.Take(c)
		arg.Show(
			"so m² = 4·i(i + 1) + 1 = 8c + 1",
			ByArith(mIs, consecutive))
	}),
})}

// UpperHalfCountEven — h − ⌊h/2⌋ is even exactly when 2h + 1 ≡ ±1 (mod 8):
// by h mod 4. Writing h = 4q + j, the count is 2q, 2q + 1, 2q + 1, 2q + 2 and
// 2h + 1 leaves 1, 3, 5, 7 mod 8 for j = 0, 1, 2, 3.
var UpperHalfCountEven = upperHalfCountEvenThm{family.Add(registry.ProofEntry{
	Name: "UpperHalfCountEven",
	Key:  "prop_cde9bada6d80aeea",
	Build: family.Theorem("∀h:num. "+
		"    nat_even(h - div(h, 2)) ⇔ rem(2 * h + 1, 8) = 1 ∨ rem(2 * h + 1, 8) = 7",
		func(arg *Argument, h *Expr[Nat]) {
			two, eight := arg.TermAs[Nat]("2"), arg.TermAs[Nat]("8")
			count := arg.TermAs[Nat]("h - div(h, 2)")
			odd := arg.TermAs[Nat]("2 * h + 1")
			quarter := arg.TermAs[Nat]("div(h, 4)")
			quarters := arg.Have(
				"h = 4q + j with j = h mod 4 below 4",
				"h = div(h, 4) * 4 + rem(h, 4) ∧ rem(h, 4) < 4",
				By(nat_div_mod.Division.At(h, arg.TermAs[Nat]("4"))))
			residues := arg.Have(
				"so j is 0, 1, 2 or 3",
				"rem(h, 4) = 0 ∨ rem(h, 4) = 1 ∨ rem(h, 4) = 2 ∨ rem(h, 4) = 3",
				ByArith(quarters))
			countEven := EvenIffModTwoZero.At(count)
			zero := arg.Have(
				"j = 0: the count is 2q and 2h + 1 = 8q + 1",
				"rem(h, 4) = 0 ⇒ (nat_even(h - div(h, 2)) ⇔ rem(2 * h + 1, 8) = 1 ∨ rem(2 * h + 1, 8) = 7)",
				ByArith(
					quarters,
					nat_div_mod.DivUniq.At(h, two, arg.TermAs[Nat]("2 * div(h, 4)"), arg.TermAs[Nat]("0")),
					nat_div_mod.ModUniq.At(odd, eight, quarter, arg.TermAs[Nat]("1")),
					nat_div_mod.ModUniq.At(count, two, quarter, arg.TermAs[Nat]("0")),
					countEven))
			one := arg.Have(
				"j = 1: the count is 2q + 1 and 2h + 1 = 8q + 3",
				"rem(h, 4) = 1 ⇒ (nat_even(h - div(h, 2)) ⇔ rem(2 * h + 1, 8) = 1 ∨ rem(2 * h + 1, 8) = 7)",
				ByArith(
					quarters,
					nat_div_mod.DivUniq.At(h, two, arg.TermAs[Nat]("2 * div(h, 4)"), arg.TermAs[Nat]("1")),
					nat_div_mod.ModUniq.At(odd, eight, quarter, arg.TermAs[Nat]("3")),
					nat_div_mod.ModUniq.At(count, two, quarter, arg.TermAs[Nat]("1")),
					countEven))
			twoCase := arg.Have(
				"j = 2: the count is 2q + 1 and 2h + 1 = 8q + 5",
				"rem(h, 4) = 2 ⇒ (nat_even(h - div(h, 2)) ⇔ rem(2 * h + 1, 8) = 1 ∨ rem(2 * h + 1, 8) = 7)",
				ByArith(
					quarters,
					nat_div_mod.DivUniq.At(h, two, arg.TermAs[Nat]("2 * div(h, 4) + 1"), arg.TermAs[Nat]("0")),
					nat_div_mod.ModUniq.At(odd, eight, quarter, arg.TermAs[Nat]("5")),
					nat_div_mod.ModUniq.At(count, two, quarter, arg.TermAs[Nat]("1")),
					countEven))
			three := arg.Have(
				"j = 3: the count is 2q + 2 and 2h + 1 = 8q + 7",
				"rem(h, 4) = 3 ⇒ (nat_even(h - div(h, 2)) ⇔ rem(2 * h + 1, 8) = 1 ∨ rem(2 * h + 1, 8) = 7)",
				ByArith(
					quarters,
					nat_div_mod.DivUniq.At(h, two, arg.TermAs[Nat]("2 * div(h, 4) + 1"), arg.TermAs[Nat]("1")),
					nat_div_mod.ModUniq.At(odd, eight, quarter, arg.TermAs[Nat]("7")),
					nat_div_mod.ModUniq.At(count, two, arg.TermAs[Nat]("div(h, 4) + 1"), arg.TermAs[Nat]("0")),
					countEven))
			arg.Show(
				"one of the four cases holds",
				By(residues, zero, one, twoCase, three))
		}),
})}

// OddSquareEighthEven — for odd n, (n² − 1)/8 is even exactly when
// n ≡ ±1 (mod 8). Write n = 8t + r: the remainder r is 1, 3, 5 or 7, n being
// odd, and for these four (n² − 1)/8 is 8t² + 2t, 8t² + 6t + 1,
// 8t² + 10t + 3 and 8t² + 14t + 6, even for r = 1 and r = 7 and odd for
// r = 3 and r = 5.
var OddSquareEighthEven = oddSquareEighthEvenThm{family.Add(registry.ProofEntry{
	Name: "OddSquareEighthEven",
	Key:  "prop_9d364c0615c921de",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"nat_odd(n)",
		},
		Conclusion: "nat_even(div(n * n - 1, 8)) ⇔ rem(n, 8) = 1 ∨ rem(n, 8) = 7",
	}, func(arg *Argument, n *Expr[Nat], odd Fact) {
		zero, one, two, four, eight :=
			arg.Ctx().Nat(0), arg.Ctx().Nat(1), arg.Ctx().Nat(2), arg.Ctx().Nat(4), arg.Ctx().Nat(8)
		quotient := arg.Have(
			"divide n by 8: n = 8·⌊n/8⌋ + (n mod 8), the remainder below 8",
			"n = div(n, 8) * 8 + rem(n, 8) ∧ rem(n, 8) < 8",
			By(nat_div_mod.Division.At(n, eight)))
		arg.Let("t", arg.TermAs[Nat]("div(n, 8)"))
		remainder := arg.Let("r", arg.TermAs[Nat]("rem(n, 8)"))
		square := arg.Have(
			"n = 8t + r, so n² = (8t + r)²",
			"n * n = (t * 8 + r) * (t * 8 + r)",
			By(Normalized, quotient))
		i, nIs := arg.ObtainAs[Nat](
			"n is odd: n = 2i + 1",
			"∃i:num. n = suc(2 * i)",
			By(odd, OddIffSucDouble.At(n)))
		residue := arg.Have(
			"i = 4q + j with j below 4 makes n = 8q + 2j + 1, so r = 2j + 1",
			"r = 2 * rem(i, 4) + 1 ∧ rem(i, 4) < 4",
			ByArith(
				nIs,
				remainder,
				nat_div_mod.Division.At(i, four),
				nat_div_mod.ModUniq.At(
					n, eight, arg.TermAs[Nat]("div(i, 4)"), arg.TermAs[Nat]("2 * rem(i, 4) + 1"))))
		residues := arg.Have(
			"so r is 1, 3, 5 or 7",
			"r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7",
			ByArith(residue))
		reduced := arg.TermAs[Nat]("n * n - 1")
		exponent := arg.TermAs[Nat]("div(n * n - 1, 8)")
		atOne := arg.Have(
			"r = 1: (n² − 1)/8 = 8t² + 2t, which is even",
			"r = 1 ⇒ nat_even(div(n * n - 1, 8))",
			ByArith(
				square,
				nat_div_mod.DivUniq.At(reduced, eight, arg.TermAs[Nat]("8 * (t * t) + 2 * t"), zero),
				nat_div_mod.ModUniq.At(exponent, two, arg.TermAs[Nat]("4 * (t * t) + t"), zero)))
		atThree := arg.Have(
			"r = 3: (n² − 1)/8 = 8t² + 6t + 1, which is odd",
			"r = 3 ⇒ ¬nat_even(div(n * n - 1, 8))",
			ByArith(
				square,
				nat_div_mod.DivUniq.At(reduced, eight, arg.TermAs[Nat]("8 * (t * t) + 6 * t + 1"), zero),
				nat_div_mod.ModUniq.At(exponent, two, arg.TermAs[Nat]("4 * (t * t) + 3 * t"), one)))
		atFive := arg.Have(
			"r = 5: (n² − 1)/8 = 8t² + 10t + 3, which is odd",
			"r = 5 ⇒ ¬nat_even(div(n * n - 1, 8))",
			ByArith(
				square,
				nat_div_mod.DivUniq.At(reduced, eight, arg.TermAs[Nat]("8 * (t * t) + 10 * t + 3"), zero),
				nat_div_mod.ModUniq.At(exponent, two, arg.TermAs[Nat]("4 * (t * t) + 5 * t + 1"), one)))
		atSeven := arg.Have(
			"r = 7: (n² − 1)/8 = 8t² + 14t + 6, which is even",
			"r = 7 ⇒ nat_even(div(n * n - 1, 8))",
			ByArith(
				square,
				nat_div_mod.DivUniq.At(reduced, eight, arg.TermAs[Nat]("8 * (t * t) + 14 * t + 6"), zero),
				nat_div_mod.ModUniq.At(exponent, two, arg.TermAs[Nat]("4 * (t * t) + 7 * t + 3"), zero)))
		arg.Show(
			"one of the four residues holds, and the exponent is even exactly at r = 1 and r = 7",
			By(remainder, residues, atOne, atThree, atFive, atSeven))
	}),
})}

// ---------------------------------------------------------------------------
// TwoNotDividesOdd — parity as divisibility by 2
// ---------------------------------------------------------------------------

// TwoNotDividesOdd — an odd number is not divisible by 2: a multiple of 2 is
// even.
var TwoNotDividesOdd = twoNotDividesOddThm{family.Add(registry.ProofEntry{
	Name: "TwoNotDividesOdd",
	Key:  "prop_a7d2db923f4d3451",
	Build: family.Theorem(Statement{
		Binders: "∀n:num.",
		Hypotheses: []string{
			"nat_odd(n)",
		},
		Conclusion: "¬(2 ∣ n)",
	}, func(a *Argument, n *Expr[Nat], odd Fact) {
		a.Show(
			"n = 2·x would make n even",
			By(odd, OddIffNotEven.At(n), EvenIffDouble.At(n), nat_divides.DividesFactor.At(a.Ctx().Nat(2), n)))
	}),
})}
