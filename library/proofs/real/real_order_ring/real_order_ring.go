// real_order_ring.go — the chapter: ℝ as an ordered ring.
//
// Eight parts, marked by banners:
//
// - The ≤/< bridge
// - Translation invariance and its consequences
// - Moving a negation or a subtracted term across a comparison
// - The negation laws read at &0, where they become statements about
// sign
// - The order across the ℕ embedding
// - Scaling a comparison by a non-negative factor, and the sign of a
// product
// - Cancelling a positive factor without dividing by it
// - A common radius for finitely many

package real_order_ring

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The ≤/< bridge
// ---------------------------------------------------------------------------
//
// the ≤/< bridge: what the two order relations say about themselves and
// about each other.
//
// README §"The one idea the chapter runs on".

// LessEqRefl — reflexivity is the degenerate case of totality.
//
// The tower hands down its order axioms without this one, which is why
// the chapter opens here rather than at the ≤/< bridge: every later
// tier dismisses an equal-case branch by citing it.
var LessEqRefl = lessEqReflThm{family.Add(registry.ProofEntry{
	Name: "LessEqRefl",
	Key:  "prop_ba788040e376e841",
	Build: family.Theorem("∀x:real. x ≤ x",
		func(a *Argument, x Term) {
			// Totality at (x, x) is `x ≤ x ∨ x ≤ x`; either disjunct is the
			// goal.
			a.Do(By(At(real_construction.LessEqTotal, x, x)))
		}),
})}

// NotLessEq — the negation of ≤ IS the flipped strict order, and that
// IS the definition of `<`: the tower delivers `real_le`, and the
// strict order is its negation the other way round. NotLessThan is the
// same equation with both sides negated.
var NotLessEq = notLessEqThm{family.Define(registry.DefEntry{
	Name:      "NotLessEq",
	Key:       "prop_64b5152bd6c6d703",
	Const:     "real_lt",
	Type:      "real → real → bool",
	Equations: []string{"∀x y:real. real_lt(x, y) ⇔ ¬(y ≤ x)"},
})}

// NotLessThan — `<` is not a second primitive. It is DEFINED as the
// negation of the reversed `≤`, and this member is that definition
// stated the way the rest of the chapter uses it: one unfold, nothing
// else, no dep.
//
// Every later member that mixes the two relations goes through this
// equation, usually by unfolding `real_lt` in its own statement rather
// than by citing here.
var NotLessThan = notLessThanThm{family.Add(registry.ProofEntry{
	Name: "NotLessThan",
	Key:  "prop_6833d3c658cfb4c5",
	Build: family.Theorem("∀x y:real. ¬(x < y) ⇔ y ≤ x",
		func(a *Argument) {
			// real_lt's defining equation IS the statement: unfolding the
			// left side leaves `y ≤ x ⇔ y ≤ x`, which the unfold discharges.
			a.Do(Unfold(NotLessEq))
		}),
})}

// LessThanIrrefl — irreflexivity of `<` is reflexivity of `≤`, read
// through the definition: `¬(x < x)` unfolds to `¬¬(x ≤ x)`, and the
// two negations cancel in the same step.
var LessThanIrrefl = lessThanIrreflThm{family.Add(registry.ProofEntry{
	Name: "LessThanIrrefl",
	Key:  "prop_664ca5b2ae67f106",
	Build: family.Theorem("∀x:real. ¬(x < x)",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x. x ≤ x
				Unfold(NotLessEq),
				Cite(LessEqRefl),
			)
		}),
})}

// LessEqSplit — the decomposition every later case analysis runs on:
// a non-strict comparison is a strict one or an equality, and never
// both.
//
// Unfolded, the claim is `x ≤ y ⇔ ¬(y ≤ x) ∨ x = y`, and each
// direction is one axiom. Left to right is ANTISYMMETRY: the only way
// `x ≤ y` can fail to give `¬(y ≤ x)` is for both comparisons to hold,
// and that is the case antisymmetry identifies as equality. Right to
// left is TOTALITY: where `y ≤ x` fails, totality's disjunction leaves
// `x ≤ y` standing, and the equal arm closes by reflexivity — which is
// totality again, at (x, x).
var LessEqSplit = lessEqSplitThm{family.Add(registry.ProofEntry{
	Name: "LessEqSplit",
	Key:  "prop_34e924744abd3bf5",
	Build: family.Theorem("∀x y:real. x ≤ y ⇔ x < y ∨ x = y",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y. x ≤ y ⇔ ¬(y ≤ x) ∨ x = y
				Unfold(NotLessEq),
				By(Normalized, real_construction.LessEqAntisym, real_construction.LessEqTotal),
			)
		}),
})}

// LessThanSplit — LessEqSplit read from the strict side. Unfolded, the claim
// is `¬(y ≤ x) ⇔ x ≤ y ∧ x ≠ y`: totality supplies `x ≤ y` in every
// case where `y ≤ x` fails, and antisymmetry is what identifies the
// one case it does not cover — both comparisons holding — with the
// equality the right side excludes. The equal case needs `x ≤ x`,
// which is totality read at (x, x).
var LessThanSplit = lessThanSplitThm{family.Add(registry.ProofEntry{
	Name: "LessThanSplit",
	Key:  "prop_7c492d07bc4180e7",
	Build: family.Theorem("∀x y:real. x < y ⇔ x ≤ y ∧ x ≠ y",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y. ¬(y ≤ x) ⇔ x ≤ y ∧ x ≠ y
				Unfold(NotLessEq),
				By(Normalized, real_construction.LessEqAntisym, real_construction.LessEqTotal),
			)
		}),
})}

// LessThanTrichotomy — that ℝ is linearly ordered, in the form the
// later tiers case-split on.
//
// It is antisymmetry alone, which is not obvious until the strict
// comparisons are unfolded: the claim becomes
// `x = y ∨ ¬(y ≤ x) ∨ ¬(x ≤ y)`, i.e. that two reals comparing both
// ways are equal. Totality is not needed — the disjunction already
// covers the case where neither comparison holds, vacuously.
var LessThanTrichotomy = lessThanTrichotomyThm{family.Add(registry.ProofEntry{
	Name: "LessThanTrichotomy",
	Key:  "prop_dd0a7c3bb7d5deb3",
	Build: family.Theorem("∀x y:real. x = y ∨ x < y ∨ y < x",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y. x = y ∨ ¬(y ≤ x) ∨ ¬(x ≤ y)
				Unfold(NotLessEq),
				By(real_construction.LessEqAntisym),
			)
		}),
})}

// LessThanAsym — asymmetry of the strict order, and it needs neither
// transitivity nor irreflexivity to get there. Both comparisons unfold
// to negations, and forbidding their conjunction is asserting the
// disjunction of what they negate: `y ≤ x ∨ x ≤ y`, which is totality.
var LessThanAsym = lessThanAsymThm{family.Add(registry.ProofEntry{
	Name: "LessThanAsym",
	Key:  "prop_698ce3b39c296521",
	Build: family.Theorem("∀x y:real. ¬(x < y ∧ y < x)",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y. y ≤ x ∨ x ≤ y
				Unfold(NotLessEq),
				Cite(real_construction.LessEqTotal),
			)
		}),
})}

// lessThanLessEqAsym — mixed asymmetry, and like lessEqOrLessThan it is propositional
// rather than order-theoretic: `x < y` unfolds to `¬(y ≤ x)`, so the
// forbidden conjunction is a formula and its own negation. No dep.
var lessThanLessEqAsym = lessThanLessEqAsymThm{family.Add(registry.ProofEntry{
	Name: "lessThanLessEqAsym",
	Key:  "prop_cf55db42d0908d15",
	Build: family.Theorem("∀x y:real. ¬(x < y ∧ y ≤ x)",
		func(a *Argument) {
			// ↦ ∀x y. ¬(¬(y ≤ x) ∧ y ≤ x) — the unfold discharges it.
			a.Do(Unfold(NotLessEq))
		}),
})}

// lessEqOrLessThan — mixed totality, and it says nothing about the order at all:
// the right disjunct IS the negation of the left, so unfolding real_lt
// leaves an instance of excluded middle. Hence no dep, not even the
// totality axiom the name suggests.
var lessEqOrLessThan = lessEqOrLessThanThm{family.Add(registry.ProofEntry{
	Name: "lessEqOrLessThan",
	Key:  "prop_10d6632f8db50acf",
	Build: family.Theorem("∀x y:real. x ≤ y ∨ y < x",
		func(a *Argument) {
			// ↦ ∀x y. x ≤ y ∨ ¬(x ≤ y) — the unfold discharges it.
			a.Do(Unfold(NotLessEq))
		}),
})}

// LessEqOfLessThan — the implication both later transitivity members
// use to weaken a strict step. Unfolded it stops being an implication
// at all: the antecedent is a negation, so the claim reads
// `y ≤ x ∨ x ≤ y` — totality, verbatim.
var LessEqOfLessThan = lessEqOfLessThanThm{family.Add(registry.ProofEntry{
	Name: "LessEqOfLessThan",
	Key:  "prop_624eda3dce7565b7",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"x < y",
		},
		Conclusion: "x ≤ y",
	},
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y. ¬(y ≤ x) ⇒ x ≤ y — an implication, not yet the
				// disjunction the doc reads it as: the unfold does not
				// classically re-express ⇒.
				Unfold(NotLessEq),
				Cite(real_construction.LessEqTotal),
			)
		}),
})}

// LessEqOfEq — reflexivity with one side renamed. Nothing unfolds here
// (the statement names no strict comparison): the hypothesis is an
// equality, and an equality is what carries a fact about y onto x.
var LessEqOfEq = lessEqOfEqThm{family.Add(registry.ProofEntry{
	Name: "LessEqOfEq",
	Key:  "prop_5b77013d870f97da",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"x = y",
		},
		Conclusion: "x ≤ y",
	},
		func(a *Argument, x, y Term, eq Fact) { // x, y bound to reach eq
			// The equality is APPLIED, not listed as a premise: a By over
			// facts the context already holds installs nothing, so no
			// eq-simplify runs and the leaf falls through to the refuter
			// (measured — it costs a CNF key for a pure substitution).
			a.Do(
				eq.Rw(),          // x₀ ≤ y₀ ↦ y₀ ≤ y₀
				Cite(LessEqRefl), // the rewritten goal IS reflexivity's instance
			)
		}),
})}

// NotEqualOfLessThan — the corollary of irreflexivity. Nothing unfolds
// here, because the argument is about `<` as such: LessThanIrrefl is
// the member where the unfold to `≤` already happened, and citing it
// is how that work is reused rather than repeated.
var NotEqualOfLessThan = notEqualOfLessThanThm{family.Add(registry.ProofEntry{
	Name: "NotEqualOfLessThan",
	Key:  "prop_1b6f40fd2b429f17",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"x < y",
		},
		Conclusion: "x ≠ y",
	},
		func(a *Argument, x, y Term, lt Fact) { // x, y bound to reach lt
			a.Show(
				"x₀ ≠ y₀ — under x₀ = y₀ the hypothesis becomes y₀ < y₀",
				By(lt, At(LessThanIrrefl, y)))
		}),
})}

// NonzeroOfPositive — the chapter's first statement to spell an embedded
// literal: an x both above &0 and equal to it would put &0 strictly
// below itself, which is what irreflexivity refuses.
//
// It is NotEqualOfLessThan's argument at a fixed lower endpoint, but the
// body is shorter rather than parallel — see below.
var NonzeroOfPositive = nonzeroOfPositiveThm{family.Add(registry.ProofEntry{
	Name: "NonzeroOfPositive",
	Key:  "prop_aee2a57a0befa982",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "x ≠ &0",
	},
		func(a *Argument, x Term) {
			// Binding x is what makes the leaf ground, and against a ground
			// leaf the cite closes outright rather than installing a
			// premise — so unlike NotEqualOfLessThan this needs no By and no
			// witness. (Left ∀-closed, the same cite installs instead.)
			a.Do(Cite(LessThanIrrefl))
		}),
})}

// LessEqLessThanTrans — mixed transitivity, and unfolded it stops being
// mixed. `x ≤ y ∧ ¬(z ≤ y) ⇒ ¬(z ≤ x)` is the contrapositive of
// `z ≤ x ∧ x ≤ y ⇒ z ≤ y`: transitivity's own statement, read with z,
// x and y in its three slots.
var LessEqLessThanTrans = lessEqLessThanTransThm{family.Add(registry.ProofEntry{
	Name: "LessEqLessThanTrans",
	Key:  "prop_925216a2eb566d3b",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"x ≤ y",
			"y < z",
		},
		Conclusion: "x < z",
	},
		// ↦ ∀x y z. (x ≤ y ∧ ¬(z ≤ y)) ⇒ ¬(z ≤ x)
		Opening(Unfold(NotLessEq), func(a *Argument, x, y, z *Expr[Real], steps Fact) {
			a.Show(
				"¬(z₀ ≤ x₀): z₀ ≤ x₀ would carry z₀ under y₀, which the strict step denies",
				By(steps, At(real_construction.LessEqTrans, z, x, y))) // z₀ ≤ x₀ ∧ x₀ ≤ y₀ ⇒ z₀ ≤ y₀
		})),
})}

// LessThanLessEqTrans — the other mixed transitivity, and the same
// observation carries it: unfolded, `¬(y ≤ x) ∧ y ≤ z ⇒ ¬(z ≤ x)` is
// the contrapositive of `z ≤ x ∧ y ≤ z ⇒ y ≤ x`, which is transitivity
// with y, z, x in its three slots. Here the unfolded form is already
// the axiom's, so the cite lands on the ∀-closed goal.
var LessThanLessEqTrans = lessThanLessEqTransThm{family.Add(registry.ProofEntry{
	Name: "LessThanLessEqTrans",
	Key:  "prop_9f7eb758d17d08c5",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"x < y",
			"y ≤ z",
		},
		Conclusion: "x < z",
	},
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y z. (¬(y ≤ x) ∧ y ≤ z) ⇒ ¬(z ≤ x)
				Unfold(NotLessEq),
				Cite(real_construction.LessEqTrans),
			)
		}),
})}

// LessThanTrans — nothing unfolds here, and the mixed members say why.
// LessEqLessThanTrans and LessThanLessEqTrans each unfold to
// transitivity's own clause; this one unfolds to
// `¬(y ≤ x) ∧ ¬(z ≤ y) ⇒ ¬(z ≤ x)`, whose clause carries TWO positive
// literals where transitivity carries one — one negative literal short
// of the axiom, so no instance of it is the goal. Read at the level of
// `<` instead, the second step weakens to `y ≤ z` and the mixed
// transitivity already proved finishes.
var LessThanTrans = lessThanTransThm{family.Add(registry.ProofEntry{
	Name: "LessThanTrans",
	Key:  "prop_53c36997b91301d0",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"x < y",
			"y < z",
		},
		Conclusion: "x < z",
	},
		func(a *Argument, x, y, z Term, steps Fact) {
			a.Show(
				"x₀ < z₀ — weaken the second step, then run the mixed transitivity",
				By(
					steps,
					At(LessEqOfLessThan, y, z),        // y₀ < z₀ ⇒ y₀ ≤ z₀
					At(LessThanLessEqTrans, x, y, z))) // x₀ < y₀ ∧ y₀ ≤ z₀ ⇒ x₀ < z₀
		}),
})}

// ---------------------------------------------------------------------------
// Translation invariance and its consequences
// ---------------------------------------------------------------------------
//
// translation invariance and its consequences: what addition does to a
// comparison.
//
// README §"What addition does to the order".

// LessEqAddLeft — translation invariance, as an equivalence, and the
// tier's real content: every later additive law is this one moved
// around by commutativity or read through the `<` unfold.
//
// The axiom LessEqAddLeftImp gives ⇐ outright. It also gives ⇒, used a
// second time in the opposite direction: translating x + y ≤ x + z by
// -x yields -x + (x + y) ≤ -x + (x + z), and each side collapses back
// to its own summand. That collapse is the file's one lemma, and it is
// where associativity, the left inverse and the left identity are
// spent.
var LessEqAddLeft = lessEqAddLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddLeft",
	Key:  "prop_81fdd92e433ef6a5",
	Build: family.Sections("∀x y z:real. x + y ≤ x + z ⇔ y ≤ z",
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)

			// shiftCancel — adding -x undoes adding x. The three axioms are
			// brought in as equations over the goal's own terms, in the
			// order the left-hand side is read; the last one closes.
			shiftCancel := ctx.Lemma("∀x y:real. -x + (x + y) = y",
				func(a *Argument, x, y Term) {
					a.Do(
						Cite(real_construction.AddAssoc, v.Negate(x), x, y), // -x₀ + (x₀ + y₀) = (-x₀ + x₀) + y₀
						Cite(real_construction.AddLeftInv, x),               // -x₀ + x₀ = &0
						Cite(real_construction.AddLeftId),                   // &0 + y₀ = y₀, and the goal is gone
					)
				})

			return ctx.Theorem(headline, func(a *Argument, x, y, z Term) {
				a.Iff()
				a.Forward(
					"the axiom again, translating the hypothesis by -x₀",
					// x₀ + y₀ ≤ x₀ + z₀ ⇒ -x₀ + (x₀ + y₀) ≤ -x₀ + (x₀ + z₀)
					Cite(real_construction.LessEqAddLeftImp, v.Negate(x), v.Add(x, y), v.Add(x, z)),
					// both shifts cancel, and the translated inequality
					// becomes the goal.
					Cite(shiftCancel))
				a.Backward(
					"the axiom, translating y₀ ≤ z₀ by x₀",
					func(b *Argument, le Fact) {
						b.Show(
							"x₀ + y₀ ≤ x₀ + z₀",
							By(le, At(real_construction.LessEqAddLeftImp, x, y, z)))
					})
			})
		}),
})}

// LessEqAddRight — translation invariance on the other side, which
// addition's commutativity reduces to the side already done. Commuting
// each sum puts the shared summand on the left, where LessEqAddLeft
// already lives; the two rewrites below show the goal arriving there.
var LessEqAddRight = lessEqAddRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqAddRight",
	Key:  "prop_bc10e4d04b9aea6c",
	Build: family.Theorem("∀x y z:real. x + z ≤ y + z ⇔ x ≤ y",
		func(a *Argument, x, y, z Term) {
			// Each claim IS commutativity's instance, so the cite closes it
			// and takes no witnesses.
			swapX := a.Have(
				"commute the left-hand sum",
				"x + z = z + x",
				Cite(real_construction.AddSym))
			swapY := a.Have(
				"commute the right-hand sum",
				"y + z = z + y",
				Cite(real_construction.AddSym))
			a.Do(
				// ↦ (z₀ + x₀ ≤ y₀ + z₀) ⇔ x₀ ≤ y₀
				swapX.Rw(),
				// ↦ (z₀ + x₀ ≤ z₀ + y₀) ⇔ x₀ ≤ y₀
				swapY.Rw(),
				Cite(LessEqAddLeft),
			)
		}),
})}

// LessThanAddLeft — the strict form of translation invariance, and the
// unfold makes it the non-strict one. Both sides of the equivalence are
// negations, and `¬A ⇔ ¬B` is `A ⇔ B`, so the unfold cancels both at
// once and leaves LessEqAddLeft with its compared pair reversed.
var LessThanAddLeft = lessThanAddLeftThm{family.Add(registry.ProofEntry{
	Name: "LessThanAddLeft",
	Key:  "prop_cd44ed71dc5d6467",
	Build: family.Theorem("∀x y z:real. x + y < x + z ⇔ y < z",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y z. x + z ≤ x + y ⇔ z ≤ y
				Unfold(NotLessEq),
				Cite(LessEqAddLeft),
			)
		}),
})}

// LessThanAddRight — the strict form on the right, and the unfold makes
// it the non-strict one exactly as on the left: both sides are
// negations, they cancel together, and what is left is LessEqAddRight
// with its compared pair reversed. Commutativity is not spent a second
// time — LessEqAddRight paid for it once, and the unfold inherits it.
var LessThanAddRight = lessThanAddRightThm{family.Add(registry.ProofEntry{
	Name: "LessThanAddRight",
	Key:  "prop_c6f74c3b74a45f29",
	Build: family.Theorem("∀x y z:real. x + z < y + z ⇔ x < y",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y z. y + z ≤ x + z ⇔ y ≤ x
				Unfold(NotLessEq),
				Cite(LessEqAddRight),
			)
		}),
})}

// LessThanAddLeftImp — the strict counterpart of the translation axiom.
// Its statement is the ⇐ half of LessThanAddLeft, which sits in the
// same tier and is proved the same way; it is a member of its own
// because the corpus cites the one-way form directly.
//
// Unfolded the claim is `¬(z ≤ y) ⇒ ¬(x + z ≤ x + y)`, which is the
// contrapositive of LessEqAddLeft's ⇒ direction with the compared pair
// reversed — so the equivalence already proved covers it whole, and one
// cite is the proof. The associativity, inverse and identity laws that
// translation invariance costs were spent there, once.
var LessThanAddLeftImp = lessThanAddLeftImpThm{family.Add(registry.ProofEntry{
	Name: "LessThanAddLeftImp",
	Key:  "prop_c9c21b4400811516",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"y < z",
		},
		Conclusion: "x + y < x + z",
	},
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y z. ¬(z ≤ y) ⇒ ¬(x + z ≤ x + y)
				Unfold(NotLessEq),
				Cite(LessEqAddLeft),
			)
		}),
})}

// LessEqAdd2 — adding two comparisons, and the argument is that one
// summand moves at a time. Raising w to x with y held fixed, then y to
// z with x held fixed, passes through the mixed sum x + y; that term
// is the whole content of the proof, and transitivity joins the two
// halves across it.
var LessEqAdd2 = lessEqAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqAdd2",
	Key:  "prop_fe8ab54cea944ab8",
	Build: family.Theorem(Statement{
		Binders: "∀w x y z:real.",
		Hypotheses: []string{
			"w ≤ x",
			"y ≤ z",
		},
		Conclusion: "w + y ≤ x + z",
	},
		func(a *Argument, w, x, y, z Term, bounds Fact) {
			v := ops(a.Ctx())
			lower := a.Have(
				"raise the left summand, holding y",
				"w + y ≤ x + y",
				By(bounds, LessEqAddRight))
			upper := a.Have(
				"raise the right summand, holding x",
				"x + y ≤ x + z",
				By(bounds, LessEqAddLeft))
			a.Show(
				"join the two halves at x₀ + y₀",
				By(lower, upper, At(real_construction.LessEqTrans, v.Add(w, y), v.Add(x, y), v.Add(x, z))))
		}),
})}

// LessThanAdd2 — LessEqAdd2 with every comparison strict, and the same
// one-summand-at-a-time argument carries it: the two halves meet at
// x + y, and strict transitivity joins them there.
var LessThanAdd2 = lessThanAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessThanAdd2",
	Key:  "prop_a1363356b15b9ac9",
	Build: family.Theorem(Statement{
		Binders: "∀w x y z:real.",
		Hypotheses: []string{
			"w < x",
			"y < z",
		},
		Conclusion: "w + y < x + z",
	},
		func(a *Argument, w, x, y, z Term, bounds Fact) {
			v := ops(a.Ctx())
			lower := a.Have(
				"raise the left summand, holding y",
				"w + y < x + y",
				By(bounds, LessThanAddRight))
			upper := a.Have(
				"raise the right summand, holding x",
				"x + y < x + z",
				By(bounds, LessThanAddLeft))
			a.Show(
				"join the two halves at x₀ + y₀",
				By(lower, upper, At(LessThanTrans, v.Add(w, y), v.Add(x, y), v.Add(x, z))))
		}),
})}

// LessEqLessThanAdd2 — the mixed sum, strict on the right. The halves
// are as in LessEqAdd2, but only the second one is strict, so the join
// at x + y is the mixed transitivity rather than either pure one.
var LessEqLessThanAdd2 = lessEqLessThanAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqLessThanAdd2",
	Key:  "prop_fbbbf03d9b425946",
	Build: family.Theorem(Statement{
		Binders: "∀w x y z:real.",
		Hypotheses: []string{
			"w ≤ x",
			"y < z",
		},
		Conclusion: "w + y < x + z",
	},
		func(a *Argument, w, x, y, z Term, bounds Fact) {
			v := ops(a.Ctx())
			lower := a.Have(
				"raise the left summand, holding y",
				"w + y ≤ x + y",
				By(bounds, LessEqAddRight))
			upper := a.Have(
				"raise the right summand, holding x",
				"x + y < x + z",
				By(bounds, LessThanAddLeft))
			a.Show(
				"join the two halves at x₀ + y₀",
				By(lower, upper, At(LessEqLessThanTrans, v.Add(w, y), v.Add(x, y), v.Add(x, z))))
		}),
})}

// LessThanLessEqAdd2 — the mixed sum with the strict half first. It is
// LessEqLessThanAdd2 with the strictness moved from the second
// comparison to the first, and the same waypoint x + y still serves
// because both members raise the LEFT summand first; what changes is
// which of the two translations is strict, and hence which mixed
// transitivity joins them.
var LessThanLessEqAdd2 = lessThanLessEqAdd2Thm{family.Add(registry.ProofEntry{
	Name: "LessThanLessEqAdd2",
	Key:  "prop_2b28e8e53d747fe6",
	Build: family.Theorem(Statement{
		Binders: "∀w x y z:real.",
		Hypotheses: []string{
			"w < x",
			"y ≤ z",
		},
		Conclusion: "w + y < x + z",
	},
		func(a *Argument, w, x, y, z Term, bounds Fact) {
			v := ops(a.Ctx())
			lower := a.Have(
				"raise the left summand, holding y",
				"w + y < x + y",
				By(bounds, LessThanAddRight))
			upper := a.Have(
				"raise the right summand, holding x",
				"x + y ≤ x + z",
				By(bounds, LessEqAddLeft))
			a.Show(
				"join the two halves at x₀ + y₀",
				By(lower, upper, At(LessThanLessEqTrans, v.Add(w, y), v.Add(x, y), v.Add(x, z))))
		}),
})}

// AddNonneg — a sum of non-negative reals is non-negative: LessEqAdd2
// read with both lower bounds at &0. The two comparisons add to
// `&0 + &0 ≤ x + y`, and the left side is &0 by the additive identity.
var AddNonneg = addNonnegThm{family.Add(registry.ProofEntry{
	Name: "AddNonneg",
	Key:  "prop_a560f52181024b7d",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"&0 ≤ y",
		},
		Conclusion: "&0 ≤ x + y",
	},
		func(a *Argument, x, y Term, nonneg Fact) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			// Normalized — engine shaping, not part of the argument.
			a.Show(
				"add the two bounds; the sum of the two zeros is &0",
				By(
					Normalized,
					nonneg,
					At(LessEqAdd2, zero, x, zero, y),      // &0 ≤ x₀ ∧ &0 ≤ y₀ ⇒ &0 + &0 ≤ x₀ + y₀
					At(real_construction.AddLeftId, zero), // &0 + &0 = &0
				))
		}),
})}

// LessEqSelfAddRight — a summand's sign decides whether the sum beats the
// other summand, and translation invariance already says so once both
// sides are sums: x is x + &0, so comparing x with x + y is comparing
// &0 with y under a common left summand. The whole content is supplying
// the missing &0.
var LessEqSelfAddRight = lessEqSelfAddRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqSelfAddRight",
	Key:  "prop_53a252fdabbf14e9",
	Build: family.Theorem("∀x y:real. x ≤ x + y ⇔ &0 ≤ y",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				Cite(real_ring.AddRightId),          // x + &0 = x, brought in unground
				Cite(LessEqAddLeft, x, v.Lit(0), y), // x₀ + &0 ≤ x₀ + y₀ ⇔ &0 ≤ y₀
				Basic(),                             // reading x₀ + &0 as x₀, that IS the goal
			)
		}),
})}

// LessEqSelfAddLeft — LessEqSelfAddRight with the summands exchanged, and the
// mirror runs all the way through the proof: y is &0 + y, so comparing
// y with x + y is comparing &0 with x under a common RIGHT summand.
// Where the other member spends the right identity and the left
// translation law, this one spends the left identity and the right one.
var LessEqSelfAddLeft = lessEqSelfAddLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqSelfAddLeft",
	Key:  "prop_2093df3107ddfb3b",
	Build: family.Theorem("∀x y:real. y ≤ x + y ⇔ &0 ≤ x",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				Cite(real_construction.AddLeftId),    // &0 + x = x, brought in unground
				Cite(LessEqAddRight, v.Lit(0), x, y), // &0 + y₀ ≤ x₀ + y₀ ⇔ &0 ≤ x₀
				Basic(),                              // reading &0 + y₀ as y₀, that IS the goal
			)
		}),
})}

// LessThanSelfAddRight — LessEqSelfAddRight with both comparisons strict. It
// takes that member's route rather than the chapter's usual unfold:
// unfolding gives `x + y ≤ x ⇔ y ≤ &0`, which no member here states,
// whereas supplying the missing &0 puts the goal under the strict
// translation law already proved.
var LessThanSelfAddRight = lessThanSelfAddRightThm{family.Add(registry.ProofEntry{
	Name: "LessThanSelfAddRight",
	Key:  "prop_979d7e54278445e9",
	Build: family.Theorem("∀x y:real. x < x + y ⇔ &0 < y",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				Cite(real_ring.AddRightId),            // x + &0 = x, brought in unground
				Cite(LessThanAddLeft, x, v.Lit(0), y), // x₀ + &0 < x₀ + y₀ ⇔ &0 < y₀
				Basic(),                               // reading x₀ + &0 as x₀, that IS the goal
			)
		}),
})}

// ---------------------------------------------------------------------------
// Moving a negation or a subtracted term across a comparison
// ---------------------------------------------------------------------------
//
// README §"Negation and subtraction".

// lessEqLeftNeg — a negation on the left of a comparison is the same as
// a comparison of &0 with a sum, and the move is to translate both
// sides by x: that is exactly what sends -x to zero and y to the sum.
// Translation invariance is an equivalence, so nothing is lost either
// way.
//
// The LEFT translation law is what the target sum asks for: `x + y`
// spells x first, so the translator is prepended, and the pair that
// then collapses is `x + -x` — real_ring's right-inverse theorem. Its
// mirror lessEqRightNeg appends its translator instead, collapses
// `-y + y`, and so reaches for the construction's left-inverse AXIOM.
// Same argument, and the two inverse laws sit in different packages
// only because one is derived from the other.
var lessEqLeftNeg = lessEqLeftNegThm{family.Add(registry.ProofEntry{
	Name: "lessEqLeftNeg",
	Key:  "prop_7040831f28b650f9",
	Build: family.Theorem("∀x y:real. -x ≤ y ⇔ &0 ≤ x + y",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				// -x₀ ≤ y₀ ⇔ x₀ + -x₀ ≤ x₀ + y₀ — translation by x₀.
				Cite(LessEqAddLeft, x, v.Negate(x), y),
				// x₀ + -x₀ is &0, which rewrites the installed equivalence into the goal.
				Cite(real_ring.AddRightInv),
			)
		}),
})}

// lessEqRightNeg — lessEqLeftNeg's mirror, and the mirror runs through
// the translation as well: it is the negated term that has to be sent
// to zero, and which translation law does that is decided by where the
// translator has to land in the target sum. Here the target is `x + y`
// with y appended, so the RIGHT law applies it on the right; at
// lessEqLeftNeg the target is the same sum with x prepended, so the
// LEFT law. Both are translation by the un-negated term.
//
// The two also reach for different inverse laws, and the asymmetry is
// the tower's rather than this chapter's: `-y + y = &0` is an AXIOM of
// the construction, while `y + -y = &0` is real_ring's theorem derived
// from it. Whichever side the translator lands on picks the one that
// matches.
var lessEqRightNeg = lessEqRightNegThm{family.Add(registry.ProofEntry{
	Name: "lessEqRightNeg",
	Key:  "prop_519b8b732d9126ac",
	Build: family.Theorem("∀x y:real. x ≤ -y ⇔ x + y ≤ &0",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				// x₀ ≤ -y₀ ⇔ x₀ + y₀ ≤ -y₀ + y₀ — translation by y₀.
				Cite(LessEqAddRight, x, v.Negate(y), y),
				// -y₀ + y₀ is &0, which rewrites the installed equivalence into the goal.
				Cite(real_construction.AddLeftInv),
			)
		}),
})}

// lessThanLeftNeg — lessEqLeftNeg with both comparisons strict, and the
// unfold is what makes them the same theorem: each `<` becomes the
// reversed `≤`, both negations cancel across the equivalence, and the
// residue is a non-strict statement that the same translation by x
// settles.
//
// Note which translation law that is. The statement is about `<`, but
// the goal reaching the cite is not, and the law it wants is the
// NON-strict LessEqAddLeft. Choosing the dep from the headline would
// pick LessThanAddLeft, which this proof never needs.
var lessThanLeftNeg = lessThanLeftNegThm{family.Add(registry.ProofEntry{
	Name: "lessThanLeftNeg",
	Key:  "prop_9646779151517761",
	Build: family.Theorem("∀x y:real. -x < y ⇔ &0 < x + y",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				// ↦ (y₀ ≤ -x₀) ⇔ (x₀ + y₀ ≤ &0)
				Unfold(NotLessEq),
				// y₀ ≤ -x₀ ⇔ x₀ + y₀ ≤ x₀ + -x₀ — translation by x₀.
				Cite(LessEqAddLeft, x, y, v.Negate(x)),
				// x₀ + -x₀ is &0, which rewrites the installed equivalence into the goal.
				Cite(real_ring.AddRightInv),
			)
		}),
})}

// lessThanRightNeg — lessEqRightNeg with both comparisons strict. The
// unfold reverses each side and the same right translation by y sends
// the negated term to zero. As at lessThanLeftNeg, the law the cite
// wants is the NON-strict LessEqAddRight: by then no `<` is left in the
// goal.
var lessThanRightNeg = lessThanRightNegThm{family.Add(registry.ProofEntry{
	Name: "lessThanRightNeg",
	Key:  "prop_dce04d265ad58021",
	Build: family.Theorem("∀x y:real. x < -y ⇔ x + y < &0",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				// ↦ (-y₀ ≤ x₀) ⇔ (&0 ≤ x₀ + y₀)
				Unfold(NotLessEq),
				// -y₀ ≤ x₀ ⇔ -y₀ + y₀ ≤ x₀ + y₀ — translation by y₀.
				Cite(LessEqAddRight, v.Negate(y), x, y),
				// -y₀ + y₀ is &0, which rewrites the installed equivalence into the goal.
				Cite(real_construction.AddLeftInv),
			)
		}),
})}

// LessEqNeg2 — negating both sides reverses the comparison, and the two
// sides meet at one and the same statement: &0 ≤ -y + x. Each reaches
// it by a single translation chosen so that its left-hand side becomes
// an inverse pair — the negated comparison translates by x on the
// right, giving -x + x; the plain one by -y on the left, giving
// -y + y. Note the asymmetry: on the negated side the translation
// cancels a negation already present, while on the plain side it
// introduces the -y that makes the pair. Both translations are
// equivalences, so the two comparisons are the same statement about
// -y + x, and the one inverse law settles both.
var LessEqNeg2 = lessEqNeg2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqNeg2",
	Key:  "prop_ec57de5fcbe6be4b",
	Build: family.Theorem("∀x y:real. -x ≤ -y ⇔ y ≤ x",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			negX, negY := v.Negate(x), v.Negate(y)
			a.Do(
				// -x₀ ≤ -y₀ ⇔ -x₀ + x₀ ≤ -y₀ + x₀ — translation by x₀.
				Cite(LessEqAddRight, negX, negY, x),
				// y₀ ≤ x₀ ⇔ -y₀ + y₀ ≤ -y₀ + x₀ — translation by -y₀.
				Cite(LessEqAddLeft, negY, y, x),
				// -x₀ + x₀ and -y₀ + y₀ are both &0, so the two instances
				// become the same comparison and the goal is gone.
				Cite(real_construction.AddLeftInv),
			)
		}),
})}

// LessThanNeg2 — LessEqNeg2 read through the `<` unfold, which swaps
// each comparison's two operands (`a < b` is `¬(b ≤ a)`). Elsewhere in
// this tier that swap sends a member to a DIFFERENT law —
// NegNegativeIffPositive and NegPositiveIffNegative take each other's
// non-strict twin — but here it sends the
// member to its OWN, and this is the tier's one such case: the
// statement already reverses x and y, so the operand swap is undone by
// renaming the two binders. The unfolded goal is LessEqNeg2 verbatim.
var LessThanNeg2 = lessThanNeg2Thm{family.Add(registry.ProofEntry{
	Name: "LessThanNeg2",
	Key:  "prop_8a0b06ad55b286e4",
	Build: family.Theorem("∀x y:real. -x < -y ⇔ y < x",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y. (-y ≤ -x) ⇔ (x ≤ y)
				Unfold(NotLessEq),
				// which is LessEqNeg2 itself.
				Cite(LessEqNeg2),
			)
		}),
})}

// LessEqSubAddLeft — taking z off one side and putting it on the other
// says the same thing, because translating the comparison by z is
// reversible: adding z back is what turns the difference into the plain
// term. Nothing about subtraction beyond that cancellation is used,
// which is why the only algebra here is real_ring.SubAddRight.
//
// This law and its mirror are how the chapter reads `−` at all. `x - y`
// stays an opaque term, and every later member that meets one comes
// through here rather than through the ring's definition of it.
var LessEqSubAddLeft = lessEqSubAddLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqSubAddLeft",
	Key:  "prop_8058daeb5305ae29",
	Build: family.Theorem("∀x y z:real. x ≤ y - z ⇔ x + z ≤ y",
		func(a *Argument, x, y, z Term) {
			v := ops(a.Ctx())
			a.Do(
				// x₀ ≤ y₀ - z₀ ⇔ x₀ + z₀ ≤ (y₀ - z₀) + z₀ — translation by z₀.
				Cite(LessEqAddRight, x, v.Sub(y, z), z),
				// (y₀ - z₀) + z₀ is y₀, which rewrites the installed equivalence into the goal.
				Cite(real_ring.SubAddRight),
			)
		}),
})}

// LessEqSubAddRight — LessEqSubAddLeft with the difference on the other
// side of the comparison. The same translation settles it, and it is
// still a translation by the subtracted term: adding y back cancels the
// difference and lands on the other side as a sum.
var LessEqSubAddRight = lessEqSubAddRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqSubAddRight",
	Key:  "prop_c7feb35c98d0cfc2",
	Build: family.Theorem("∀x y z:real. x - y ≤ z ⇔ x ≤ z + y",
		func(a *Argument, x, y, z Term) {
			v := ops(a.Ctx())
			a.Do(
				// x₀ - y₀ ≤ z₀ ⇔ (x₀ - y₀) + y₀ ≤ z₀ + y₀ — translation by y₀.
				Cite(LessEqAddRight, v.Sub(x, y), z, y),
				// (x₀ - y₀) + y₀ is x₀, which rewrites the installed equivalence into the goal.
				Cite(real_ring.SubAddRight),
			)
		}),
})}

// LessThanSubAddLeft — the strict form is the non-strict one already
// proved, read in the other direction. `a < b` is `¬(b ≤ a)`, so
// unfolding swaps each comparison's two operands, which carries the
// difference from the right-hand side of its comparison to the left —
// and a difference on the LEFT is what LessEqSubAddRight is about. So
// the strict Left law is the non-strict RIGHT law, and nothing else is
// needed: no translation, no ring equation.
var LessThanSubAddLeft = lessThanSubAddLeftThm{family.Add(registry.ProofEntry{
	Name: "LessThanSubAddLeft",
	Key:  "prop_d4794526e0309451",
	Build: family.Theorem("∀x y z:real. x + z < y ⇔ x < y - z",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y z. (y ≤ x + z) ⇔ (y - z ≤ x)
				Unfold(NotLessEq),
				// which is LessEqSubAddRight itself, up to binder names.
				Cite(LessEqSubAddRight),
			)
		}),
})}

// LessThanSubAddRight — the mirror of LessThanSubAddLeft, and it
// mirrors the cross-pairing too: unfolding swaps each comparison's two
// operands, carrying the difference from the left of its comparison to
// the right, so the strict Right law is the non-strict LEFT law.
// One unfold and one cite.
var LessThanSubAddRight = lessThanSubAddRightThm{family.Add(registry.ProofEntry{
	Name: "LessThanSubAddRight",
	Key:  "prop_c5017336c14a9b0b",
	Build: family.Theorem("∀x y z:real. x - y < z ⇔ x < z + y",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x y z. (z ≤ x - y) ⇔ (z + y ≤ x)
				Unfold(NotLessEq),
				// which is LessEqSubAddLeft itself, up to binder names.
				Cite(LessEqSubAddLeft),
			)
		}),
})}

// SubNonneg — the sign of a difference IS the comparison of its two
// terms. It is LessEqSubAddLeft read at the one instance where the term
// compared against the difference is &0; the identity law then clears
// the zero the transported comparison is left carrying.
var SubNonneg = subNonnegThm{family.Add(registry.ProofEntry{
	Name: "SubNonneg",
	Key:  "prop_5ab1afc9d3c0984b",
	Build: family.Theorem("∀x y:real. &0 ≤ x - y ⇔ y ≤ x",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				// &0 ≤ x₀ - y₀ ⇔ &0 + y₀ ≤ x₀ — the subtraction law at &0.
				Cite(LessEqSubAddLeft, v.Lit(0), x, y),
				// &0 + y₀ is y₀, which rewrites the installed equivalence into the goal.
				Cite(real_construction.AddLeftId),
			)
		}),
})}

// SubPos — SubNonneg with both comparisons strict, and the unfold is
// what decides which subtraction law it wants: reversing the sides puts
// the difference on the LEFT, so the instance needed is the mirror
// law's, not SubNonneg's. The identity law then clears the zero, as it
// does there.
var SubPos = subPosThm{family.Add(registry.ProofEntry{
	Name: "SubPos",
	Key:  "prop_e27ff0404f300435",
	Build: family.Theorem("∀x y:real. &0 < x - y ⇔ y < x",
		func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			a.Do(
				// ↦ (x₀ - y₀ ≤ &0) ⇔ (x₀ ≤ y₀)
				Unfold(NotLessEq),
				// x₀ - y₀ ≤ &0 ⇔ x₀ ≤ &0 + y₀ — the subtraction law at &0.
				Cite(LessEqSubAddRight, x, y, v.Lit(0)),
				// &0 + y₀ is y₀, which rewrites the installed equivalence into the goal.
				Cite(real_construction.AddLeftId),
			)
		}),
})}

// ---------------------------------------------------------------------------
// The negation laws read at &0, where they become statements about sign
// ---------------------------------------------------------------------------
//
// README §"What the order says about a sign".

// NegNonnegativeIffNonpositive — the first of the sign laws, and it is one
// instance of the transport tier: lessEqRightNeg moves a negated right-hand
// side across the comparison, and this is that law read where the left-hand
// side is already &0. Transporting then leaves the zero standing in front
// of x, and real_construction.AddLeftId clears it.
//
// It and its mirror NegNonpositiveIffNonnegative are where the transport
// laws stop: every remaining sign-at-zero member — the two strict versions,
// the two totality laws, both directions of lessEqSelfNeg — cites this pair
// rather than the transport law the pair came from.
var NegNonnegativeIffNonpositive = negNonnegativeIffNonpositiveThm{family.Add(registry.ProofEntry{
	Name: "NegNonnegativeIffNonpositive",
	Key:  "prop_600aa54eaa67debb",
	Build: family.Theorem("∀x:real. &0 ≤ -x ⇔ x ≤ &0",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			a.Do(
				// &0 ≤ -x₀ ⇔ &0 + x₀ ≤ &0 — the transport law with &0 on
				// the left.
				Cite(lessEqRightNeg, v.Lit(0), x),
				// &0 + x₀ is x₀, which rewrites the installed equivalence
				// into the goal.
				Cite(real_construction.AddLeftId),
			)
		}),
})}

// NegNonpositiveIffNonnegative — NegNonnegativeIffNonpositive's mirror, and
// it is proved by the mirrored route rather than out of
// NegNonnegativeIffNonpositive: the negation now stands on the LEFT of the
// comparison, so the law that transports it is lessEqLeftNeg, and the zero
// it leaves behind is appended rather than prepended, so
// real_ring.AddRightId clears it where NegNonnegativeIffNonpositive spends
// real_construction.AddLeftId. Same argument, both halves reflected.
var NegNonpositiveIffNonnegative = negNonpositiveIffNonnegativeThm{family.Add(registry.ProofEntry{
	Name: "NegNonpositiveIffNonnegative",
	Key:  "prop_71b4e48d6d590962",
	Build: family.Theorem("∀x:real. -x ≤ &0 ⇔ &0 ≤ x",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			a.Do(
				// -x₀ ≤ &0 ⇔ &0 ≤ x₀ + &0 — the transport law with &0 on
				// the right.
				Cite(lessEqLeftNeg, x, v.Lit(0)),
				// x₀ + &0 is x₀, which rewrites the installed equivalence
				// into the goal.
				Cite(real_ring.AddRightId),
			)
		}),
})}

// NegPositiveIffNegative — NegNonpositiveIffNonnegative with both
// comparisons strict, and the same crossing as at NegNegativeIffPositive:
// `a < b` is `¬(b ≤ a)`, so unfolding swaps each comparison's two operands,
// and `&0 < -x` — that -x is positive — becomes a claim about `-x ≤ &0`,
// which is what NegNonpositiveIffNonnegative is about. Reading the dep off
// the strict headline picks the other law every time.
var NegPositiveIffNegative = negPositiveIffNegativeThm{family.Add(registry.ProofEntry{
	Name: "NegPositiveIffNegative",
	Key:  "prop_5a131286804b4373",
	Build: family.Theorem("∀x:real. &0 < -x ⇔ x < &0",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x. (-x ≤ &0) ⇔ (&0 ≤ x)
				Unfold(NotLessEq),
				// which is NegNonpositiveIffNonnegative itself.
				Cite(NegNonpositiveIffNonnegative),
			)
		}),
})}

// NegNegativeIffPositive — NegNonnegativeIffNonpositive with both
// comparisons strict, and the pairing CROSSES, which is what makes the dep
// look like a typo and is not one. `a < b` is `¬(b ≤ a)`, so unfolding
// swaps the two OPERANDS of each comparison while leaving the ⇔'s own sides
// where they are; the two negations then cancel across the ⇔. So `-x < &0`,
// a claim that -x is negative, becomes a claim about `&0 ≤ -x` — and the
// law about `&0 ≤ -x` is NegNonnegativeIffNonpositive. Its mirror
// NegPositiveIffNegative crosses the other way, for the same reason.
var NegNegativeIffPositive = negNegativeIffPositiveThm{family.Add(registry.ProofEntry{
	Name: "NegNegativeIffPositive",
	Key:  "prop_1689d98c3cc0a559",
	Build: family.Theorem("∀x:real. -x < &0 ⇔ &0 < x",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x. (&0 ≤ -x) ⇔ (x ≤ &0)
				Unfold(NotLessEq),
				// which is NegNonnegativeIffNonpositive itself.
				Cite(NegNonnegativeIffNonpositive),
			)
		}),
})}

// LessEqNegTotal — totality of the order, said about x and its negation:
// NegNonnegativeIffNonpositive turns "-x is non-negative" into "x is
// non-positive", and the two disjuncts then compare x with &0 in both
// directions, which is what totality asserts. No case analysis: the
// statement is one instance of the axiom once the second disjunct is read
// on the other side.
var LessEqNegTotal = lessEqNegTotalThm{family.Add(registry.ProofEntry{
	Name: "LessEqNegTotal",
	Key:  "prop_dbf4cbe54013ad09",
	Build: family.Theorem("∀x:real. &0 ≤ x ∨ &0 ≤ -x",
		func(a *Argument) {
			a.Do(
				// ↦ ∀x. (&0 ≤ x) ∨ (x ≤ &0)
				Cite(NegNonnegativeIffNonpositive),
				// which is totality at &0 and x.
				Cite(real_construction.LessEqTotal),
			)
		}),
})}

// LessThanNegTotal — LessEqNegTotal's statement with both comparisons made
// strict, which is why it carries a third disjunct: sharpening ≤ to < has
// to let x be &0 outright. And it is not proved from LessEqNegTotal —
// sharpening a disjunction of ≤'s is not something totality does — but from
// antisymmetry, which the unfold reveals.
//
// Unfolding `<` makes the two strict disjuncts NEGATIVE, so what is left to
// prove is: if x is not positive and -x is not positive, then x = &0. Those
// two failures read x ≤ &0 and -x ≤ &0; NegNonpositiveIffNonnegative turns
// the second into &0 ≤ x, and a real caught between &0 on both sides IS &0.
var LessThanNegTotal = lessThanNegTotalThm{family.Add(registry.ProofEntry{
	Name: "LessThanNegTotal",
	Key:  "prop_7d0b8934f639108c",
	Build: family.Theorem("∀x:real. x = &0 ∨ &0 < x ∨ &0 < -x",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			a.Do(
				// ↦ ∀x. ((x = &0) ∨ ¬(x ≤ &0)) ∨ ¬(-x ≤ &0)
				Unfold(NotLessEq),
				// x₀ = &0 ⇔ x₀ ≤ &0 ∧ &0 ≤ x₀ — the two negated disjuncts
				// become the hypotheses x₀ ≤ &0 and -x₀ ≤ &0, and x₀ = &0
				// is what is left to prove.
				Cite(real_construction.LessEqAntisym, x, v.Lit(0)),
				// -x₀ ≤ &0 is &0 ≤ x₀, the second half antisymmetry wants.
				Cite(NegNonpositiveIffNonnegative),
			)
		}),
})}

// lessEqSelfNeg — the tier's one member with two directions to argue, and
// both go through &0 rather than comparing x with -x directly. The direct
// route transports x ≤ -x by x and arrives at x + x ≤ &0, which then needs
// "a sum of a real with itself is non-positive exactly when the real is".
// That is a true ordered-group fact, and the chapter could prove it from
// LessEqAdd2 — it simply does not STATE it, so reaching for it here would
// mean adding a member. Zero is the waypoint that avoids the question, and
// both directions then need the two sign laws, transitivity, and — in the ⇒
// direction — totality.
//
// - ⇐ x ≤ &0 gives &0 ≤ -x by NegNonnegativeIffNonpositive, so x ≤ &0 ≤ -x.
// - ⇒ totality compares x with &0. One case IS the goal; in the
// other, &0 ≤ x gives -x ≤ &0 by NegNonpositiveIffNonnegative, and the
// hypothesis chains x ≤ -x ≤ &0.
//
// Both arms name their premises to a `By` rather than closing at a cite,
// and both carry `Normalized` — engine shaping, not part of the argument.
// The two cases are fused into one `By` per
// arm rather than split with `a.Cases` — every premise is ground, so the
// split would add a branch without adding a name.
var lessEqSelfNeg = lessEqSelfNegThm{family.Add(registry.ProofEntry{
	Name: "lessEqSelfNeg",
	Key:  "prop_6018210ee957c676",
	Build: family.Theorem("∀x:real. x ≤ -x ⇔ x ≤ &0",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			zero, negX := v.Lit(0), v.Negate(x)
			a.Iff()
			a.Forward(
				"totality against zero settles both its cases",
				func(b *Argument, belowNeg Fact) {
					b.Show(
						"&0 ≤ x₀ gives x₀ ≤ -x₀ ≤ &0; totality's other case is the goal itself",
						// totality at (&0, x₀) — its second disjunct IS the
						// goal.
						By(
							belowNeg,
							At(real_construction.LessEqTrans, x, negX, zero),
							At(NegNonpositiveIffNonnegative, x),
							At(real_construction.LessEqTotal, zero, x)))
				})
			a.Backward(
				"from below zero, over zero, to the negation",
				func(b *Argument, belowZero Fact) {
					b.Show(
						"x₀ ≤ &0 ≤ -x₀",
						By(
							belowZero,
							At(NegNonnegativeIffNonpositive, x),
							At(real_construction.LessEqTrans, x, zero, negX)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The order across the ℕ embedding
// ---------------------------------------------------------------------------
//
// the order across the ℕ embedding, and the two facts about the unit that
// only ℕ can supply.
//
// README §"The order across the ℕ embedding".

// OfNumLessThan — the embedding agrees with the strict order because
// it agrees with the non-strict one, and because in both ℕ and ℝ the
// strict order is the negation of the flipped non-strict one. The two
// domains hold that duality on different terms: at ℝ it is the
// DEFINITION of `<`, so it is unfolded, while at ℕ each order is given
// by its own clauses and the duality has to be proved. Between the
// two, the order agreement takes the embedding off.
var OfNumLessThan = ofNumLessThanThm{family.Add(registry.ProofEntry{
	Name: "OfNumLessThan",
	Key:  "prop_62bc2a4506d50326",
	Build: family.Theorem("∀m n:num. &m < &n ⇔ m < n",
		func(a *Argument) {
			a.Do(
				// ↦ ∀m n. ¬(&n ≤ &m) ⇔ m < n
				Unfold(NotLessEq),
				// ↦ ∀n m. ¬(n ≤ m) ⇔ m < n — one rewrite takes the embedding
				// off both operands of the ℝ comparison; the right-hand side
				// was already at ℕ. The binder prefix comes back reordered,
				// which is why this marker reads ∀n m where the one above
				// reads ∀m n — a cite re-derives the prefix, an unfold does
				// not.
				Cite(real_construction.OfNumLessEq),
				// and that residual IS ℕ's own duality, with its two binders
				// renamed — the cite closes the section.
				Cite(nat_order.NotLessEq),
			)
		}),
})}

// ofNumGreaterThan — OfNumLessThan read from the larger end. Neither
// `>` is a relation of its own: ℝ and ℕ each DEFINE theirs as their
// own strict order with the arguments swapped. So unfolding both
// leaves the same swap on either side of the equivalence, and what is
// left is OfNumLessThan. The chapter unfolds a definitional bridge
// rather than citing it; here that habit runs on both sides of an
// embedding at once.
//
// The headline says `real_gt(&m, &n)` in prefix and `m > n` in infix
// because only ℕ's `>` is declared as notation here — ℝ's is spelled
// out, which also keeps the two sides visibly different relations.
var ofNumGreaterThan = ofNumGreaterThanThm{family.Add(registry.ProofEntry{
	Name: "ofNumGreaterThan",
	Key:  "prop_2056036e8df1fb37",
	Build: family.Theorem("∀m n:num. real_gt(&m, &n) ⇔ m > n",
		func(a *Argument) {
			a.Do(
				// ↦ ∀m n. (&n < &m) ⇔ m > n
				Unfold(RealGtDef),
				// ↦ ∀m n. (&n < &m) ⇔ (n < m)
				Unfold(nat_order.GtDef),
				// the swap is now common to both sides, so renaming the two
				// binders recovers OfNumLessThan — the cite closes the section.
				Cite(OfNumLessThan),
			)
		}),
})}

// NumNonneg — ℝ's copy of ℕ has no negative element, and the reason
// is entirely on the ℕ side: zero is ℕ's bottom element, and the
// embedding preserves order, so it carries that up unchanged.
var NumNonneg = numNonnegThm{family.Add(registry.ProofEntry{
	Name: "NumNonneg",
	Key:  "prop_f9451cf38cb1d307",
	Build: family.Theorem("∀n:num. &0 ≤ &n",
		func(a *Argument) {
			a.Do(
				// ↦ ∀n. 0 ≤ n — the order agreement moves the comparison to ℕ.
				Cite(real_construction.OfNumLessEq),
				// where zero is the bottom element — the cite closes it.
				Cite(nat_order.ZeroLessEq),
			)
		}),
})}

// ZeroLessEqOne — the unit is non-negative, because it is an embedded
// number and no embedded number is negative. The non-strict companion
// of ZeroLessThanOne, and stated on its own because the chapters that
// want the unit's sign want it at `&1` rather than at "some numeral".
var ZeroLessEqOne = zeroLessEqOneThm{family.Add(registry.ProofEntry{
	Name: "ZeroLessEqOne",
	Key:  "prop_f3fc8fd1c20a2ce7",
	Build: family.Theorem("&0 ≤ &1",
		func(a *Argument) {
			// The goal is the ∀-instance of NumNonneg at n = 1, so the cite
			// closes the section outright.
			a.Do(Cite(NumNonneg))
		}),
})}

// ZeroLessThanOne — the unit is strictly positive, and the chapter
// gets it from the embedding rather than from its own order laws.
// Carried down to ℕ the claim is that `1` is positive, which on ℕ is
// the same fact as `1 ≤ 1` — structural, with no ring reasoning in it
// at all.
var ZeroLessThanOne = zeroLessThanOneThm{family.Add(registry.ProofEntry{
	Name: "ZeroLessThanOne",
	Key:  "prop_713acc2961720c72",
	Build: family.Theorem("&0 < &1",
		func(a *Argument) {
			one := a.Ctx().Numeral(1)
			a.Do(
				// ↦ 0 < 1 — the whole comparison moves to ℕ.
				Cite(OfNumLessThan),
				// where positivity and a bound by 1 are the same fact.
				// ↦ 1 ≤ 1 ⇔ 0 < 1
				Cite(nat_order.OneLessEqIffPos, one),
				// which reflexivity settles — the cite closes the section.
				Cite(nat_order.LessEqRefl),
			)
		}),
})}

// LessThanAddOne — adding the unit to a bound makes it a strict one.
// The additive laws say only that the step from y to y + &1 is strict
// exactly when &1 is above zero, so all the strength of the statement
// sits in that one comparison — which is not an additive fact at all,
// but what the ℕ embedding contributes. Mixed transitivity then hands
// the strictness down to anything at or below y.
var LessThanAddOne = lessThanAddOneThm{family.Add(registry.ProofEntry{
	Name: "LessThanAddOne",
	Key:  "prop_1e3c22e3ba23a7a1",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"x ≤ y",
		},
		Conclusion: "x < y + &1",
	},
		func(a *Argument, x, y Term, below Fact) {
			v := ops(a.Ctx())
			one := v.Lit(1)

			step := a.Have(
				"the step up by one is strict, because the unit is positive",
				"y < y + &1",
				// ↦ &0 < &1 — consumed as a goal rewrite, so it takes no
				// witnesses: the claim already spells the instance.
				Cite(LessThanSelfAddRight),
				Cite(ZeroLessThanOne),
			)

			a.Show(
				"carry the strictness down to x₀ across the bound",
				By(below, step, At(LessEqLessThanTrans, x, y, v.Add(y, one))))
		}),
})}

// ---------------------------------------------------------------------------
// Scaling a comparison by a non-negative factor, and the sign of a product
// ---------------------------------------------------------------------------
//
// README §"What the order says about multiplication".

// LessEqMulLeft — scaling a comparison by a non-negative factor, and
// its whole argument is that a comparison IS the sign of a difference.
// Read that
// way the hypothesis says z - y is non-negative; the construction's one
// multiplicative order axiom says a product of non-negatives is
// non-negative, so x·(z - y) is non-negative too; and distributing that
// product gives x·z - x·y, whose sign read back the other way is the
// comparison asked for.
var LessEqMulLeft = lessEqMulLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulLeft",
	Key:  "prop_c0e8ff143320b121",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 ≤ x",
			"y ≤ z",
		},
		Conclusion: "x * y ≤ x * z",
	},
		func(a *Argument, x, y, z Term, bounds Fact) {
			v := ops(a.Ctx())
			// SubNonneg is bare here: it rewrites the claim into y₀ ≤ z₀,
			// which bounds already carries.
			gap := a.Have(
				"the comparison y ≤ z, restated as a sign",
				"&0 ≤ z - y",
				By(bounds, SubNonneg))
			scaled := a.Have(
				"the non-negative x scales a non-negative difference",
				"&0 ≤ x * (z - y)",
				By(bounds, gap, At(real_construction.LessEqMul, x, v.Sub(z, y))))
			// Normalized — engine shaping, not part of the argument.
			a.Show(
				"distribute, then read the sign of x₀·z₀ - x₀·y₀ back as the comparison",
				By(
					Normalized,
					scaled,
					// x₀ * (z₀ - y₀) = x₀ * z₀ - x₀ * y₀
					At(real_ring.SubLeftDistrib, x, z, y),
					// &0 ≤ x₀ * z₀ - x₀ * y₀ ⇔ x₀ * y₀ ≤ x₀ * z₀
					At(SubNonneg, v.Mul(x, z), v.Mul(x, y))))
		}),
})}

// LessEqMulRight — LessEqMulLeft said of the other factor, and
// commutativity is the entire distance between the two. Both products
// are turned round, which puts the scaling factor on the left of each,
// and the goal is then the left law at that factor.
var LessEqMulRight = lessEqMulRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulRight",
	Key:  "prop_7be766471443362d",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"x ≤ y",
			"&0 ≤ z",
		},
		Conclusion: "x * z ≤ y * z",
	},
		func(a *Argument, x, y, z Term, bounds Fact) {
			// Both equations are stated at their instance and applied as
			// rewrites rather than listed as premises: an equation relating
			// two nonlinear products cannot close a leaf, since the closer
			// meets the two products as distinct opaque atoms.
			// The cites below are bare because each
			// discharges its own stated claim; cited AGAINST THE GOAL
			// commutativity would not rewrite at all — it permutes rather
			// than shrinks, so the rewrite path declines it and installs a
			// ∀-hypothesis.
			lower := a.Have(
				"turn the smaller product round",
				"x * z = z * x",
				Cite(real_construction.MulSym))
			upper := a.Have(
				"turn the larger product round",
				"y * z = z * y",
				Cite(real_construction.MulSym))
			a.Do(
				// ↦ z₀ * x₀ ≤ y₀ * z₀
				lower.Rw(),
				// ↦ z₀ * x₀ ≤ z₀ * y₀
				upper.Rw(),
			)
			a.Show(
				"z₀ now scales from the left, which is the left law",
				By(bounds, At(LessEqMulLeft, z, x, y)))
		}),
})}

// MulPos — positivity splits into two independent claims, being
// non-negative and being non-zero, and the product inherits each of
// them from a different law: real_construction.LessEqMul gives the first, and
// real_ring.MulEqZero — a product vanishes only if a factor does —
// gives the second. The splitting itself is LessThanSplit, applied at
// each factor and then once more, backwards, to reassemble the two
// halves at the product.
var MulPos = mulPosThm{family.Add(registry.ProofEntry{
	Name: "MulPos",
	Key:  "prop_711796c7c61d7a36",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 < x",
			"&0 < y",
		},
		Conclusion: "&0 < x * y",
	},
		func(a *Argument, x, y Term, pos Fact) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			nonneg := a.Have(
				"neither factor is negative, so the product is not",
				"&0 ≤ x * y",
				By(
					pos,
					// &0 < x₀ ⇔ &0 ≤ x₀ ∧ &0 ≠ x₀
					At(LessThanSplit, zero, x),
					// &0 < y₀ ⇔ &0 ≤ y₀ ∧ &0 ≠ y₀
					At(LessThanSplit, zero, y),
					// &0 ≤ x₀ ∧ &0 ≤ y₀ ⇒ &0 ≤ x₀ * y₀
					At(real_construction.LessEqMul, x, y)))
			nonzero := a.Have(
				"neither factor is &0, and only a zero factor makes a zero product",
				"x * y ≠ &0",
				By(
					pos,
					// the same two splits, now for their other half
					At(LessThanSplit, zero, x),
					At(LessThanSplit, zero, y),
					// x₀ * y₀ = &0 ⇔ x₀ = &0 ∨ y₀ = &0
					At(real_ring.MulEqZero, x, y)))
			a.Show(
				"non-negative together with non-zero is positive — the split, read backwards",
				By(nonneg, nonzero, At(LessThanSplit, zero, v.Mul(x, y))))
		}),
})}

// LessThanMulLeft — LessEqMulLeft with every comparison strict, and
// the argument survives the change unaltered: a strict comparison is a
// positive difference, a positive factor times a positive difference is
// positive, and distributing gives back the strict comparison of the
// two products.
//
// It does not unfold `<`, which is the chapter's default. Unfolded the
// statement reads `¬(x ≤ &0) ∧ ¬(z ≤ y) ⇒ ¬(x·z ≤ x·y)` — the
// cancellation direction, which this chapter does not state at ≤. Kept
// strict, the argument is about strict order as such: the difference
// has to be positive, not merely non-negative, for the conclusion to be
// strict, and the two laws that say so — SubPos and MulPos — are
// already stated here.
var LessThanMulLeft = lessThanMulLeftThm{family.Add(registry.ProofEntry{
	Name: "LessThanMulLeft",
	Key:  "prop_2eef4379359952a6",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < x",
			"y < z",
		},
		Conclusion: "x * y < x * z",
	},
		func(a *Argument, x, y, z Term, bounds Fact) {
			v := ops(a.Ctx())
			// SubPos is bare here: it rewrites the claim into y₀ < z₀,
			// which bounds already carries.
			gap := a.Have(
				"the comparison y < z, restated as a sign",
				"&0 < z - y",
				By(bounds, SubPos))
			scaled := a.Have(
				"the positive x scales a positive difference",
				"&0 < x * (z - y)",
				By(bounds, gap, At(MulPos, x, v.Sub(z, y))))
			// Normalized — engine shaping, not part of the argument.
			a.Show(
				"distribute, then read the sign of x₀·z₀ - x₀·y₀ back as the comparison",
				By(
					Normalized,
					scaled,
					// x₀ * (z₀ - y₀) = x₀ * z₀ - x₀ * y₀
					At(real_ring.SubLeftDistrib, x, z, y),
					// &0 < x₀ * z₀ - x₀ * y₀ ⇔ x₀ * y₀ < x₀ * z₀
					At(SubPos, v.Mul(x, z), v.Mul(x, y))))
		}),
})}

// LessThanMulRight — LessThanMulLeft said of the other factor. As in
// the non-strict pair, commutativity is the entire distance between the
// two: turning both products round puts the scaling factor on the left,
// and the goal becomes the left law at that factor.
var LessThanMulRight = lessThanMulRightThm{family.Add(registry.ProofEntry{
	Name: "LessThanMulRight",
	Key:  "prop_403cfbf672a7c401",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"x < y",
			"&0 < z",
		},
		Conclusion: "x * z < y * z",
	},
		func(a *Argument, x, y, z Term, bounds Fact) {
			// Stated at their instance and applied as rewrites, for the reason
			// LessEqMulRight records: commutativity permutes rather than
			// shrinks, so a bare cite installs instead of rewriting.
			lower := a.Have(
				"turn the smaller product round",
				"x * z = z * x",
				Cite(real_construction.MulSym))
			upper := a.Have(
				"turn the larger product round",
				"y * z = z * y",
				Cite(real_construction.MulSym))
			a.Do(
				// ↦ z₀ * x₀ < y₀ * z₀
				lower.Rw(),
				// ↦ z₀ * x₀ < z₀ * y₀
				upper.Rw(),
			)
			a.Show(
				"z₀ now scales from the left, which is the strict left law",
				By(bounds, At(LessThanMulLeft, z, x, y)))
		}),
})}

// SquareNonneg — argues by cases, and the case distinction is
// forced: the construction's multiplicative
// order axiom speaks only about non-negative factors, while x is
// arbitrary. LessEqNegTotal supplies the missing side — one of x and -x
// is always non-negative — so either the axiom applies to x directly,
// or it applies to -x and the ring identifies (-x)·(-x) with x·x.
var SquareNonneg = squareNonnegThm{family.Add(registry.ProofEntry{
	Name: "SquareNonneg",
	Key:  "prop_a6f0aee1773f26b9",
	Build: family.Theorem("∀x:real. &0 ≤ x * x",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			negX := v.Negate(x)
			sign := a.Have(
				"one of x and -x is non-negative",
				"&0 ≤ x ∨ &0 ≤ -x",
				Cite(LessEqNegTotal))
			a.Do(sign.SplitDisj(
				LeftHolds(
					"x₀ non-negative: the square already has two non-negative factors",
					Given(func(b *Argument, nonneg Fact) {
						b.Show(
							"the axiom at (x₀, x₀)",
							By(nonneg, At(real_construction.LessEqMul, x, x)))
					})),
				RightHolds(
					"-x₀ non-negative: the axiom applies to -x₀, whose square is the same number",
					Given(func(b *Argument, nonneg Fact) {
						same := b.Have(
							"the two sign changes cancel",
							"-x₀ * -x₀ = x₀ * x₀",
							CalcEq(
								Leg(
									v.Negate(v.Mul(x, negX)),
									"take the left factor's sign out",
									Cite(real_ring.MulLeftNeg)),
								// Congr strips the sign the previous leg pulled out,
								// leaving the right factor's own sign to move.
								Leg(
									v.Negate(v.Negate(v.Mul(x, x))),
									"take the right factor's sign out too",
									Congr(),
									Cite(real_ring.MulRightNeg)),
								FinalLeg(
									"a doubled sign change is none",
									Cite(real_ring.NegNeg)),
							))
						// ↦ &0 ≤ -x₀ * -x₀
						b.Do(same.RwRev())
						b.Show(
							"the axiom at (-x₀, -x₀)",
							By(nonneg, At(real_construction.LessEqMul, negX, negX)))
					})),
			))
		}),
})}

// SquarePos — SquareNonneg is what makes this an equivalence rather
// than an implication. Positivity is non-negativity together with being
// non-zero; for a square the first half is free, so all that is left of
// positivity is that the square does not vanish — and a product
// vanishes only when a factor does, which for x·x is x itself.
var SquarePos = squarePosThm{family.Add(registry.ProofEntry{
	Name: "SquarePos",
	Key:  "prop_9436f410dd521be5",
	Build: family.Theorem("∀x:real. &0 < x * x ⇔ x ≠ &0",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			// Normalized — engine shaping, not part of the argument.
			a.Show(
				"the square's non-negativity is free, so positivity is exactly non-vanishing",
				By(
					Normalized,
					// &0 < x₀ * x₀ ⇔ &0 ≤ x₀ * x₀ ∧ &0 ≠ x₀ * x₀
					At(LessThanSplit, v.Lit(0), v.Mul(x, x)),
					// &0 ≤ x₀ * x₀
					At(SquareNonneg, x),
					// x₀ * x₀ = &0 ⇔ x₀ = &0 ∨ x₀ = &0
					At(real_ring.MulEqZero, x, x)))
		}),
})}

// SumSquaresEqZero — a sum of two squares vanishes only when both
// bases do. Neither square is negative, so neither can cancel the
// other: a zero sum leaves both squares zero, and a square is zero only
// at zero (SquarePos).
var SumSquaresEqZero = sumSquaresEqZeroThm{family.Add(registry.ProofEntry{
	Name: "SumSquaresEqZero",
	Key:  "prop_69f16dfa9b576f86",
	Build: family.Theorem("∀x y:real. x * x + y * y = &0 ⇔ x = &0 ∧ y = &0",
		func(a *Argument, x, y Term) {
			a.Iff()
			a.Forward(
				"neither square is negative, so a zero sum makes each zero, and a zero square has a zero root",
				func(b *Argument, sumZero Fact) {
					b.Show(
						"both roots are zero",
						ByArith(sumZero, At(SquareNonneg, x), At(SquareNonneg, y), At(SquarePos, x), At(SquarePos, y)))
				})
			a.Backward(
				"at zero both squares vanish",
				func(b *Argument, zeros Fact) {
					both := b.Conjuncts(
						zeros,
						"x is zero",
						"y is zero")
					b.Show(
						"so the sum is zero",
						both[0].Rw(),
						both[1].Rw(),
						ByArith())
				})
		}),
})}

// ---------------------------------------------------------------------------
// Cancelling a positive factor without dividing by it
// ---------------------------------------------------------------------------
//
// cancelling a positive factor without dividing by it, and the pairwise
// laws that run the same transitivity.
//
// README §"Cancelling a positive factor, without dividing by it".

// LessThanCancelMulLeft — the converse of scaling, and unfolded it is
// not a new argument but LessEqMulLeft read backwards: if z were at or
// below y, scaling by x would put x·z at or below x·y, and that is
// precisely what the hypothesis denies. Totality supplies the one thing
// scaling needs and the statement does not give — x itself
// non-negative, which is all that is left once x is known not to sit
// at or below &0.
//
// The seed cancels by multiplying through by x's inverse. That is
// search residue: nothing in this argument mentions real_inv, and the
// chapter's boundary stops short of it.
var LessThanCancelMulLeft = lessThanCancelMulLeftThm{family.Add(registry.ProofEntry{
	Name: "LessThanCancelMulLeft",
	Key:  "prop_6aac38b8412f44f7",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < x",
			"x * y < x * z",
		},
		Conclusion: "y < z",
	},
		// ↦ ∀x y z. (¬(x ≤ &0) ∧ ¬(x * z ≤ x * y)) ⇒ ¬(z ≤ y)
		Opening(Unfold(NotLessEq), func(a *Argument, x, y, z *Expr[Real], hyps Fact) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			nonneg := a.Have(
				"x₀ fails to sit at or below &0, and totality leaves only the other side",
				"&0 ≤ x₀",
				By(hyps, At(real_construction.LessEqTotal, x, zero))) // x₀ ≤ &0 ∨ &0 ≤ x₀
			a.Show(
				"z₀ ≤ y₀ would scale up to x₀ * z₀ ≤ x₀ * y₀, which the second hypothesis denies",
				By(
					hyps,
					nonneg,
					// &0 ≤ x₀ ∧ z₀ ≤ y₀ ⇒ x₀ * z₀ ≤ x₀ * y₀
					At(LessEqMulLeft, x, z, y)))
		})),
})}

// LessThanCancelMulRight — LessThanCancelMulLeft said of the other
// factor, and as in the scaling pair commutativity is the entire
// distance between the two: turning both products round puts the
// cancelled factor on the left, and what is left is the left law.
//
// It does not unfold `<`. Nothing here is about what `<` means — the
// two products are turned round and the left law carries the relation
// across untouched, so unfolding would only spell the same comparisons
// a longer way.
var LessThanCancelMulRight = lessThanCancelMulRightThm{family.Add(registry.ProofEntry{
	Name: "LessThanCancelMulRight",
	Key:  "prop_481968041f16efd5",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < z",
			"x * z < y * z",
		},
		Conclusion: "x < y",
	},
		func(a *Argument, x, y, z Term, bounds Fact) {
			// Stated at their instance and applied as rewrites, for the reason
			// LessEqMulRight records: commutativity permutes rather than
			// shrinks, so a bare cite installs instead of rewriting. Here the
			// products they move sit in the hypothesis rather than the goal,
			// which costs nothing — a rewrite runs across every hypothesis as
			// well as the conclusion.
			lower := a.Have(
				"turn the smaller product round",
				"x * z = z * x",
				Cite(real_construction.MulSym))
			upper := a.Have(
				"turn the larger product round",
				"y * z = z * y",
				Cite(real_construction.MulSym))
			a.Do(
				// bounds ↦ &0 < z₀ ∧ z₀ * x₀ < y₀ * z₀
				lower.Rw(),
				// bounds ↦ &0 < z₀ ∧ z₀ * x₀ < z₀ * y₀
				upper.Rw(),
			)
			a.Show(
				"z₀ is now the left factor of both products, which is the strict left cancellation law",
				By(bounds, At(LessThanCancelMulLeft, z, x, y)))
		}),
})}

// LessEqCancelMulLeft — the same contraposition as its strict sibling,
// and like it, cancelling a positive factor without ever dividing by
// one; LessThanCancelMulLeft states why an ordered ring needs no
// inverse here. With the two relations exchanged: were z strictly
// below y, the positive x would carry x·z strictly below x·y, and the
// hypothesis says it does not. So the argument is about `<` even though the
// statement is about `≤`, and each of the two comparisons it names has
// to be crossed from one relation to the other.
//
// The chapter's default is to cross by unfolding, and here that does
// not work: an unfold fires on the goal as it then stands, while the
// LessThanMulLeft this member installs keeps its own `&0 < x` — unfolded, the hypothesis is
// spelled `¬(x ≤ &0)` and the two stop meeting. NotLessThan is the same
// equation applied on the dep's side instead, once at each comparison,
// which is when a member cites that law rather than unfolding.
//
// It does not reduce to its strict sibling, which is the natural first
// guess: contraposing a `≤` statement produces a `<` one, so what the
// argument reaches for is the strict SCALING law, not the strict
// cancellation.
var LessEqCancelMulLeft = lessEqCancelMulLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqCancelMulLeft",
	Key:  "prop_dc8bcdc752c6ad86",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < x",
			"x * y ≤ x * z",
		},
		Conclusion: "y ≤ z",
	},
		func(a *Argument, x, y, z Term, bounds Fact) {
			v := ops(a.Ctx())
			a.Show(
				"z₀ strictly below y₀ would carry x₀ * z₀ strictly below x₀ * y₀, against the hypothesis",
				By(
					bounds,
					// &0 < x₀ ∧ z₀ < y₀ ⇒ x₀ * z₀ < x₀ * y₀
					At(LessThanMulLeft, x, z, y),
					// ¬(z₀ < y₀) ⇔ y₀ ≤ z₀ — the goal, crossed
					At(NotLessThan, z, y),
					// ¬(x₀ * z₀ < x₀ * y₀) ⇔ x₀ * y₀ ≤ x₀ * z₀ — the hypothesis, crossed
					At(NotLessThan, v.Mul(x, z), v.Mul(x, y))))
		}),
})}

// LessEqCancelMulRight — LessEqCancelMulLeft said of the other factor.
// Commutativity is the whole distance between them, as it is for the
// strict pair and for the two scaling laws: turning both products round
// puts the cancelled factor on the left, and the left law finishes.
var LessEqCancelMulRight = lessEqCancelMulRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqCancelMulRight",
	Key:  "prop_a8b88503413a39e2",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < z",
			"x * z ≤ y * z",
		},
		Conclusion: "x ≤ y",
	},
		func(a *Argument, x, y, z Term, bounds Fact) {
			// Stated at their instance and applied as rewrites, for the reason
			// LessEqMulRight records: commutativity permutes rather than
			// shrinks, so a bare cite installs instead of rewriting. The
			// products they move sit in the hypothesis, which a rewrite
			// reaches — see LessThanCancelMulRight, which does the same.
			lower := a.Have(
				"turn the smaller product round",
				"x * z = z * x",
				Cite(real_construction.MulSym))
			upper := a.Have(
				"turn the larger product round",
				"y * z = z * y",
				Cite(real_construction.MulSym))
			a.Do(
				// bounds ↦ &0 < z₀ ∧ z₀ * x₀ ≤ y₀ * z₀
				lower.Rw(),
				// bounds ↦ &0 < z₀ ∧ z₀ * x₀ ≤ z₀ * y₀
				upper.Rw(),
			)
			a.Show(
				"z₀ is now the left factor of both products, which is the left cancellation law",
				By(bounds, At(LessEqCancelMulLeft, z, x, y)))
		}),
})}

// LessEqMulRightEq — right-hand scaling and its converse, stated once
// as the equivalence they amount to. Each direction is one of them:
// scaling by a non-negative factor carries a comparison forward, and
// cancelling a positive one carries it back. Positivity is what makes
// the pair fit — the forward direction only needs the factor
// non-negative, so it is the hypothesis weakened, while the backward
// direction needs the whole of it.
var LessEqMulRightEq = lessEqMulRightEqThm{family.Add(registry.ProofEntry{
	Name: "LessEqMulRightEq",
	Key:  "prop_7e83862071958720",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < z",
		},
		Conclusion: "x * z ≤ y * z ⇔ x ≤ y",
	},
		func(a *Argument, x, y, z Term, pos Fact) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			a.Iff()
			a.Forward(
				"cancelling carries it back, which is where the whole of the positivity is spent",
				func(b *Argument, scaled Fact) {
					b.Show(
						"drop z₀ from the right of both products",
						By(pos, scaled, At(LessEqCancelMulRight, x, y, z)))
				})
			a.Backward(
				"scaling carries the comparison forward, and only asks that z₀ be non-negative",
				func(b *Argument, ordered Fact) {
					nonneg := b.Have(
						"weaken the positivity to what scaling asks",
						"&0 ≤ z₀",
						By(pos, At(LessEqOfLessThan, zero, z)))
					b.Show(
						"multiply both sides on the right by z₀",
						By(ordered, nonneg, At(LessEqMulRight, x, y, z)))
				})
		}),
})}

// LessThanMulRightEq — LessEqMulRightEq seen from the other end of each
// comparison. A strict comparison is the failure of the reversed
// non-strict one, so both sides of this equivalence are sides of that
// one with their operands exchanged, and the non-strict law read at the
// exchanged instance already relates them. Nothing else is needed: the
// mirror is the argument.
//
// It does not unfold `<`, for LessEqCancelMulLeft's reason, stated
// there. What is specific here is which dep would stop meeting the
// goal: LessEqMulRightEq carries its own `&0 < z`. So NotLessThan
// applies the equation on the dep's side instead, once at each of the
// equivalence's two comparisons.
var LessThanMulRightEq = lessThanMulRightEqThm{family.Add(registry.ProofEntry{
	Name: "LessThanMulRightEq",
	Key:  "prop_873153f7145c6f7b",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < z",
		},
		Conclusion: "x * z < y * z ⇔ x < y",
	},
		func(a *Argument, x, y, z Term, pos Fact) {
			v := ops(a.Ctx())
			// Normalized — engine shaping, not part of the argument.
			a.Show(
				"read both comparisons backwards and the non-strict "+
					"law at the exchanged instance is the equivalence",
				By(
					Normalized,
					pos,
					// &0 < z₀ ⇒ (y₀ * z₀ ≤ x₀ * z₀ ⇔ y₀ ≤ x₀)
					At(LessEqMulRightEq, y, x, z),
					// ¬(x₀ * z₀ < y₀ * z₀) ⇔ y₀ * z₀ ≤ x₀ * z₀ — the left side, exchanged
					At(NotLessThan, v.Mul(x, z), v.Mul(y, z)),
					// ¬(x₀ < y₀) ⇔ y₀ ≤ x₀ — the right side, exchanged
					At(NotLessThan, x, y)))
		}),
})}

// LessEqMul2 — multiplying two comparisons, and as with adding them the
// argument is that one factor moves at a time. Raising w to x with y
// held fixed, then y to z with x held fixed, passes through the mixed
// product x·y; that term is the whole content of the proof.
//
// Transitivity appears twice, for two different reasons. Once to reach
// the fact the statement does not give and the second scaling needs —
// x is non-negative, sitting as it does above the non-negative w — and
// once to join the two halves across the mixed product.
var LessEqMul2 = lessEqMul2Thm{family.Add(registry.ProofEntry{
	Name: "LessEqMul2",
	Key:  "prop_872337dbe360cb3a",
	Build: family.Theorem(Statement{
		Binders: "∀w x y z:real.",
		Hypotheses: []string{
			"&0 ≤ w",
			"w ≤ x",
			"&0 ≤ y",
			"y ≤ z",
		},
		Conclusion: "w * y ≤ x * z",
	},
		func(a *Argument, w, x, y, z Term, bounds Fact) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			lower := a.Have(
				"raise the left factor, holding y",
				"w * y ≤ x * y",
				By(bounds, At(LessEqMulRight, w, x, y)))
			nonneg := a.Have(
				"x is non-negative too, sitting above the non-negative w₀",
				"&0 ≤ x",
				By(bounds, At(real_construction.LessEqTrans, zero, w, x)))
			upper := a.Have(
				"raise the right factor, holding x",
				"x * y ≤ x * z",
				By(bounds, nonneg, At(LessEqMulLeft, x, y, z)))
			a.Show(
				"join the two halves at x₀ * y₀",
				By(lower, upper, At(real_construction.LessEqTrans, v.Mul(w, y), v.Mul(x, y), v.Mul(x, z))))
		}),
})}

// LessThanMul2 — LessEqMul2's argument with the two comparisons made
// strict, keeping the same mixed product x·y as its waypoint and the
// same division of labour between the two factors.
//
// What changes is that the two halves are no longer the same kind of
// step. The first only needs w at or below x, so the strict hypothesis
// is weakened and the non-strict scaling law does it; the second is
// where the strictness is spent, because x is now strictly positive and
// carries y < z up to x·y < x·z. Non-strict followed by strict is
// strict, which is what joins them — and the same mixed transitivity
// is what makes x positive in the first place, w being non-negative and
// strictly below it.
var LessThanMul2 = lessThanMul2Thm{family.Add(registry.ProofEntry{
	Name: "LessThanMul2",
	Key:  "prop_8a07c2cde12ac598",
	Build: family.Theorem(Statement{
		Binders: "∀w x y z:real.",
		Hypotheses: []string{
			"&0 ≤ w",
			"w < x",
			"&0 ≤ y",
			"y < z",
		},
		Conclusion: "w * y < x * z",
	},
		func(a *Argument, w, x, y, z Term, bounds Fact) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			weak := a.Have(
				"the left step, weakened: raising the left factor needs no more than this",
				"w ≤ x",
				By(bounds, At(LessEqOfLessThan, w, x)))
			lower := a.Have(
				"raise the left factor, holding y",
				"w * y ≤ x * y",
				By(bounds, weak, At(LessEqMulRight, w, x, y)))
			pos := a.Have(
				"x is positive, sitting strictly above the non-negative w₀",
				"&0 < x",
				By(bounds, At(LessEqLessThanTrans, zero, w, x)))
			upper := a.Have(
				"raise the right factor, holding x — this is where the strictness is spent",
				"x * y < x * z",
				By(bounds, pos, At(LessThanMulLeft, x, y, z)))
			a.Show(
				"join the two halves at x₀ * y₀: non-strict then strict is strict",
				By(lower, upper, At(LessEqLessThanTrans, v.Mul(w, y), v.Mul(x, y), v.Mul(x, z))))
		}),
})}

// ---------------------------------------------------------------------------
// A common radius for finitely many
// ---------------------------------------------------------------------------

// CommonRadius — finitely many radii have a common one: when each i below k
// has a radius δ > 0 within which R(i, y) holds, one δ > 0 serves every i
// below k at once. By induction on k, the smaller of a common radius for the
// first k and the radius for k itself serves the first k + 1.
var CommonRadius = commonRadiusThm{family.Add(registry.ProofEntry{
	Name: "CommonRadius",
	Key:  "prop_6619506ae9515e7a",
	Build: family.Theorem(Statement{
		Binders: "∀k:num. ∀d:(A → real). ∀R:(num → A → bool).",
		Hypotheses: []string{
			"∀i:num. i < k ⇒ ∃δ:real. &0 < δ ∧ (∀y:A. d(y) < δ ⇒ R(i, y))",
		},
		Conclusion: "∃δ:real. &0 < δ ∧ (∀y:A. d(y) < δ ⇒ (∀i:num. i < k ⇒ R(i, y)))",
	}, func(a *Argument) {
		a.Induct("k")
		a.Base(
			"with no index any radius serves",
			func(b *Argument) {
				b.FixAs[Fun[A, Real]]("d")
				b.FixAs[Fun2[Nat, A, Bool]]("R")
				b.Assume()
				b.Take(b.TermAs[Real]("&1"))
				b.Show(
					"δ = 1",
					ByArith())
			})
		a.Step(
			"the smaller of two radii serves both",
			func(b *Argument, ih Fact) {
				d := b.FixAs[Fun[A, Real]]("d")
				R := b.FixAs[Fun2[Nat, A, Bool]]("R")
				radii := b.Assume()
				below := b.Have(
					"the indices below k have their radii",
					"∀i:num. i < k ⇒ ∃δ:real. &0 < δ ∧ (∀y:A. d(y) < δ ⇒ R(i, y))",
					By(radii, nat_order.LessThanSucClause))
				first, firstRadius := b.ObtainAs[Real](
					"a common radius for the indices below k",
					"∃δ₁:real. &0 < δ₁ ∧ (∀y:A. d(y) < δ₁ ⇒ (∀i:num. i < k ⇒ R(i, y)))",
					By(ih.At(d, R), below))
				last, lastRadius := b.ObtainAs[Real](
					"a radius for k itself",
					"∃δ₂:real. &0 < δ₂ ∧ (∀y:A. d(y) < δ₂ ⇒ R(k, y))",
					By(radii.At(b.TermAs[Nat]("k")), nat_order.LessThanSucClause))
				b.Cases(b.Term("δ₁ ≤ δ₂"))
				b.When(
					"δ₁ is the smaller",
					func(c *Argument, smaller Fact) {
						c.Take(first)
						c.Show(
							"within δ₁ both radii hold",
							By(smaller, firstRadius, lastRadius, nat_order.LessThanSucClause, LessThanLessEqTrans))
					})
				b.Otherwise(
					"δ₂ is the smaller",
					func(c *Argument, smaller Fact) {
						c.Take(last)
						c.Show(
							"within δ₂ both radii hold",
							By(smaller, firstRadius, lastRadius, nat_order.LessThanSucClause, LessThanTrans, NotLessEq))
					})
			})
	}),
})}
