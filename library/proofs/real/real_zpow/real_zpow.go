// real_zpow.go — the chapter: ℝ's integer powers.
//
// Six parts, marked by banners:
//
// - The ℤ-indexed power, and its bridge back to the ℕ-indexed one
// - The evaluations
// - The negative half of the reading, and the pair packaged
// - The ℤ-indexed algebra
// - The zero base
// - The exponent's law

package real_zpow

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The ℤ-indexed power
// ---------------------------------------------------------------------------
//
// the ℤ-indexed power: the two bridges back to the ℕ-indexed one, and the
// evaluations those bridges immediately give.
//
// `real_zpow` is defined by cases on the sign of its exponent — at a
// nonnegative exponent it is `real_pow` at the natural that exponent
// names, at a negative one the inverse of that. So the chapter's
// constant carries no content of its own: every ℤ-indexed law is a
// ℕ-indexed law read through the sign split. The two bridges
//
// 	x zpow &n = xⁿ x zpow (−n) = (x zpow n)⁻¹
//
// are that reading written out — the first at an exponent whose sign is
// settled in advance, the second saying what changing the sign does —
// and between them they are the only members here that unfold the
// definition and argue about its guard. They argue in opposite ways.
// ZpowOfNum settles the guard outright, an exponent in the image of ℕ
// never being negative, and discards the other branch unexamined;
// ZpowNeg cannot settle it at all, its exponent being an arbitrary
// integer, and so meets every way the two sides' guards can stand.
//
// The three evaluations after ZpowOfNum are that bridge composed with
// real_pow's own evaluations: pinning the exponent at &0, &1
// or &2 turns each of them into a ℕ-indexed statement already proved, so
// none of the three has an argument of its own. OneZpow is the odd one
// out, because it pins the BASE and leaves the exponent an arbitrary
// integer — the sign split cannot be avoided there, only made
// irrelevant.
//
// ZpowNeg is read last of the bridges rather than beside ZpowOfNum
// because it consumes one of those evaluations: the exponent &0 has to
// be settled before the sign analysis, and settling it is ZpowZero.
// ZpowClauses then names the two bridges together, and that closes the
// reading.
//
// What follows the bridges is real_pow's algebra restated at a ℤ
// exponent. Those laws vary the BASE and leave the exponent alone, so
// unlike ZpowNeg they never compare a power at n with one at −n: every
// real_zpow in such a statement guards on the same sign of the same
// exponent, and the sign analysis collapses to two branches that prove
// the same ℕ-indexed law twice.
//
// ZeroZpow is neither of those things. It pins the BASE as OneZpow
// does, but where &1's two branches agree and leave the guard nothing
// to decide, &0's do not — and the statement carries a second guard of
// its own besides, whether the exponent is &0. Two different questions
// asked of one exponent make the split the full 2×2 rather than a
// collapse, so four leaves there is the honest shape and not a failure
// to simplify.
//
// The last two members close the file, and they are the first laws here
// that vary the EXPONENT rather than the base. That is why they need a
// hypothesis on the base where nothing above them did, and why ZpowAdd
// is the only member that decomposes an integer: three different
// exponents mean three independent sign guards, so the shared-guard
// collapse the base laws enjoy is unavailable and the exponents have to
// be presented in a form the ℕ-indexed laws can read. Writing each as a
// DIFFERENCE of naturals is that form, and it makes the law's four sign
// cases one computation. ZpowSub is then that law read once more, at an
// exponent turned round, and it decomposes nothing.
//
// Every statement here is written zpow-first, as real_pow writes its
// own subject first: the left-hand side is the ℤ-indexed power and
// the right-hand side is what it turns out to be.

// ---------------------------------------------------------------------------
// ZpowOfNum — the bridge
// ---------------------------------------------------------------------------

// ZpowOfNum — an exponent in the image of ℕ is nonnegative, so the sign
// guard is settled before it is ever asked about a particular base, and
// what the definition leaves is the ℕ-indexed power at an exponent the
// embedding has been undone on.
//
// Two facts, one per obstacle. int_embed.EmbedNonneg discharges the
// guard — the whole of the sign analysis this movement ever performs,
// and the reason the negative branch is dropped unexamined rather than
// refuted. int_embed.OfNumRetract then cancels the num_of_int the
// definition applies to the exponent before handing it on, leaving the
// two sides the same power.
var ZpowOfNum = zpowOfNumThm{family.Add(registry.ProofEntry{
	Name: "ZpowOfNum",
	Key:  "prop_517606036c2014a3",
	Build: family.Theorem("∀x:real. ∀n:num. real_zpow(x, &n) = real_pow(x, n)",
		func(a *Argument, x, n Term) {
			a.Show(
				"with the guard settled the definition keeps its ℕ "+
					"branch, and the embedding cancels out of the exponent",
				// The definition, opened once for the whole movement: a COND
				// on &0 ≤ &n₀ between real_pow(x₀, num_of_int(&n₀)) and the
				// inverse of the power at the negated exponent.
				Unfold(RealZpowDef),
				// The guard holds of every embedded natural, which is what
				// selects the first branch. ↦ real_pow(x₀, num_of_int(&n₀)) =
				// real_pow(x₀, n₀).
				Cite(int_embed.EmbedNonneg),
				// num_of_int(&n₀) ↦ n₀, and the two powers coincide.
				Cite(int_embed.OfNumRetract),
			)
		}),
})}

// ===========================================================================
// The evaluations — the exponent pinned, and the bridge read at it
// ===========================================================================

// ---------------------------------------------------------------------------
// ZpowZero — the empty product, at an integer exponent
// ---------------------------------------------------------------------------

// ZpowZero — the exponent is an embedded natural, so the bridge sends
// the statement to the ℕ-indexed one, where it is real_pow.Pow's zero clause.
var ZpowZero = zpowZeroThm{family.Add(registry.ProofEntry{
	Name: "ZpowZero",
	Key:  "prop_3c28897b01172670",
	Build: family.Theorem("∀x:real. real_zpow(x, &0) = &1",
		func(a *Argument, x Term) {
			a.Show(
				"the bridge crosses to the ℕ-indexed power, and there the exponent 0 is Pow's own zero clause",
				Cite(ZpowOfNum), // ↦ real_pow(x₀, 0) = &1
				Cite(real_pow.PowExpZeroClause),
			)
		}),
})}

// ---------------------------------------------------------------------------
// ZpowOne — the first power
// ---------------------------------------------------------------------------

// ZpowOne — the same crossing, landing on the ℕ-indexed evaluation that
// says a first power is its base.
var ZpowOne = zpowOneThm{family.Add(registry.ProofEntry{
	Name: "ZpowOne",
	Key:  "prop_835a85e8c4e409ae",
	Build: family.Theorem("∀x:real. real_zpow(x, &1) = x",
		func(a *Argument, x Term) {
			a.Show(
				"the bridge crosses to the ℕ-indexed power, where a first power is its own base",
				Cite(ZpowOfNum), // ↦ real_pow(x₀, 1) = x₀
				Cite(real_pow.PowOne),
			)
		}),
})}

// ---------------------------------------------------------------------------
// ZpowTwo — the square
// ---------------------------------------------------------------------------

// ZpowTwo — the crossing one rung higher, landing on the ℕ-indexed
// square.
var ZpowTwo = zpowTwoThm{family.Add(registry.ProofEntry{
	Name: "ZpowTwo",
	Key:  "prop_292a9dad45782128",
	Build: family.Theorem("∀x:real. real_zpow(x, &2) = x * x",
		func(a *Argument, x Term) {
			a.Show(
				"the bridge crosses to the ℕ-indexed power, where a square is the base times itself",
				Cite(ZpowOfNum), // ↦ real_pow(x₀, 2) = x₀ * x₀
				Cite(real_pow.PowTwo),
			)
		}),
})}

// ---------------------------------------------------------------------------
// OneZpow — the base pinned instead, at an arbitrary integer exponent
// ---------------------------------------------------------------------------

// OneZpow — the one member of the movement the bridge does not reach:
// its exponent is an arbitrary integer, so the definition has to be
// opened and both branches met.
//
// Meeting them costs nothing, because they agree. Every ℕ-indexed power
// of &1 is &1, which evaluates the nonnegative branch and, inside the
// inverse, the negative one; field.InvOne.Read(real_field.Field) then says &1 is its own
// inverse, and the two branches having become the same term the sign
// guard is left with nothing to decide. So the proof never asks whether
// the exponent is negative — which is exactly why this law needs no
// case analysis while its ℤ-exponent siblings would.
var OneZpow = oneZpowThm{family.Add(registry.ProofEntry{
	Name: "OneZpow",
	Key:  "prop_6140f41781b144c9",
	Build: family.Theorem("∀n:int. real_zpow(&1, n) = &1",
		func(a *Argument, n Term) {
			a.Show(
				"both branches of the sign split evaluate to &1, so the guard decides nothing",
				// A COND on &0 ≤ n₀ between the two powers of &1.
				Unfold(RealZpowDef),
				// ↦ COND(&0 ≤ n₀, &1, real_inv(&1)) = &1 — one cite reaches
				// both branches, the bare power and the one standing under
				// the inverse.
				Cite(real_pow.OnePow),
				// And that inverse goes too, leaving the two branches equal.
				Cite(field.InvOne.Read(real_field.Field)),
			)
		}),
})}

// ===========================================================================
// The negative half of the reading, and the pair packaged
// ===========================================================================

// ---------------------------------------------------------------------------
// ZpowNeg — changing the sign of the exponent
// ---------------------------------------------------------------------------

// ZpowNeg — the reading's other half, and the one member of the chapter
// whose exponent has a sign nobody knows.
//
// Negating an exponent exchanges the two branches of the definition, and
// each branch absorbs the exchange through an involution of its own: on
// the value side inverting twice is doing nothing, on the exponent side
// negating twice is doing nothing. That is the whole content of the law
// — one involution per sign of n, and neither of them says anything
// about powers.
//
// The exponent &0 is peeled off before any of that, because it is the
// only integer nonnegative on both sides of the negation. There no
// branch is exchanged, both sides take the ℕ-indexed one, and what is
// left to say is that the empty product is its own inverse. Removing it
// is also what leaves the sign analysis below with two LIVE cases: the
// fan is still four, but with n ≠ &0 standing the two guards can no
// longer agree, so the two like-signed leaves are discharged as
// impossible and only the two involutions carry an argument.
var ZpowNeg = zpowNegThm{family.Add(registry.ProofEntry{
	Name: "ZpowNeg",
	Key:  "prop_e31a366c48d12949",
	Build: family.Theorem("∀x:real. ∀n:int. real_zpow(x, -n) = real_inv(real_zpow(x, n))",
		func(a *Argument, x, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			zero := v.IntOfNum.Apply(ctx.Numeral(0)) // &0, the exponent taken out of the way first
			negN := ctx.TermText("-n₀")              // −n₀, the negated exponent
			atZero := ctx.TermText("n₀ = 0")         // the case peeled off below

			nonzero := a.Unless(
				atZero,
				"n = &0: the one exponent nonnegative both ways, where "+
					"nothing is exchanged and &1 has to invert to itself",
				Given(func(b *Argument, isZero Fact) {
					b.Show(
						"−&0 is &0 too, so each side is the empty product, and that is its own inverse",
						// The exponent, on both sides: n₀ ↦ &0.
						isZero.Rw(),
						// The one on the left is still negated, and that sign has
						// to come off by a rewrite whose direction is named:
						// cited as an ordinary premise the equation installs
						// without ever firing.
						Expect(LeanRw(ctx.Dep(int_real_lift.NegZero)),
							Case(
								"−&0 is &0",
								Cite(int_real_lift.NegZero)),
							Case(
								"so the two sides read the same power, which is the empty product",
								// ↦ &1 = real_inv(&1), both occurrences at once.
								Cite(ZpowZero),
								Cite(field.InvOne.Read(real_field.Field)))),
					)
				}))

			a.Show(
				"with the sign of n unknown, both CONDs are opened and every way their guards can stand is met",
				// Each side is a COND on the sign of its own exponent, and the
				// two guards are independent of one another.
				Unfold(RealZpowDef),
				// ↦ one implication tree over the four ways the pair can stand,
				CondRewrite(),
				// which Basic() fans into its four leaves, each carrying its own
				// guard pair as hypotheses.
				Expect(Basic(),
					Case(
						"n and −n both nonnegative: that happens at &0 alone, which this branch is past",
						Derive(func(b *Argument) {
							nonpos := b.Have(
								"a nonnegative negation is a nonpositive integer",
								"n₀ ≤ 0",
								By(b.Hyp("0 ≤ -n₀"), int_real_lift.NegNonneg))
							b.Show(
								"bounded by &0 on both sides, n₀ IS &0 — the exponent this branch has already left behind",
								By(
									nonpos,
									b.Hyp("0 ≤ n₀"),
									nonzero,
									At(int_real_lift.LessEqAntisym, n, zero))) // n₀ = &0 ⇔ n₀ ≤ &0 ∧ &0 ≤ n₀
						})),
					Case(
						"n negative: both sides read the power at −n, the right one under two inversions",
						// ↦ the two inversions cancel and the sides coincide.
						Cite(field.InvInv.Read(real_field.Field))),
					Case(
						"n positive: both sides invert the power at n, the left one after negating the exponent twice",
						// ↦ the two negations cancel and the sides coincide.
						Cite(int_real_lift.NegNeg)),
					Case(
						"neither n nor −n nonnegative: impossible, a nonzero integer lying strictly on one side of &0",
						Derive(func(b *Argument) {
							b.Show(
								"trichotomy offers &0, positive and negative, and this branch has denied all three",
								By(
									b.Hyp("¬(0 ≤ n₀)"),
									b.Hyp("¬(0 ≤ -n₀)"),
									nonzero,
									At(int_real_lift.LessThanNegTotal, n),           // n₀ = &0 ∨ &0 < n₀ ∨ &0 < −n₀
									At(int_real_lift.LessEqOfLessThan, zero, n),     // &0 < n₀ ⇒ &0 ≤ n₀
									At(int_real_lift.LessEqOfLessThan, zero, negN))) // &0 < −n₀ ⇒ &0 ≤ −n₀
						})),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// ZpowClauses — the two bridges packaged together
// ---------------------------------------------------------------------------

// ZpowClauses — the two bridges named together as one conjunction.
//
// It is the pair as a single statement, and a statement only: a
// conjunction installs as a conjunction and rewrites nothing, so a proof
// that wants either bridge as a rewriting equation cites ZpowOfNum or
// ZpowNeg instead, and nothing in the chapter cites this. Both halves
// being proved already, it has no argument of its own — the nonnegative
// one IS ZpowOfNum, and the negative one is the two composed: the sign
// comes off the exponent, and the bridge is then crossed on what is
// left.
var ZpowClauses = zpowClausesThm{family.Add(registry.ProofEntry{
	Name: "ZpowClauses",
	Key:  "prop_efac7162b5138c94",
	Build: family.Theorem("(∀x:real. ∀n:num. real_zpow(x, &n) = real_pow(x, n)) ∧ "+
		"(∀x:real. ∀n:num. real_zpow(x, -&n) = real_inv(real_pow(x, n)))",
		func(a *Argument) {
			v := ops(a.Ctx())
			// A conjunction has no Argument verb of its own; the two halves
			// are proved independently and neither reads the other.
			a.Do(SplitConj(
				Case(
					"the nonnegative half IS the bridge",
					Cite(ZpowOfNum)),
				Case(
					"the negative half is that bridge with the sign taken off the exponent first",
					Derive(func(b *Argument) {
						x := b.Fix()
						n := b.Fix()
						b.Show(
							"negating the exponent inverts, and what is left inside the "+
								"inverse is an embedded natural the bridge carries across",
							By(
								At(ZpowNeg, x, v.IntOfNum.Apply(n)), // x₀ zpow (−&n₀) = (x₀ zpow &n₀)⁻¹
								ZpowOfNum))
					})),
			))
		}),
})}

// ===========================================================================
// The ℤ-indexed algebra — the base's laws, read through the sign split
// ===========================================================================

// The members below are real_pow's ℝ-base laws — a power of a
// product, of an inverse, of a quotient — restated at a ℤ exponent.
// None of them has an argument of its own. The first two carry a sign
// split, and it is cheaper than ZpowNeg's; the third carries none, its
// quotient opening into the other two before any guard is reached.
//
// The split is cheap because the exponent occurs once and is never
// touched. ZpowNeg compares the power at n against the power at −n, so
// its two sides carry independent guards and every way the pair can
// stand has to be met. These vary the base instead, so every real_zpow
// in the statement guards on the one condition &0 ≤ n: unfolding turns
// the whole statement into CONDs over a single guard, CondRewrite() into
// a single implication pair, and Basic() into two leaves, not four.
//
// The two leaves then say the same thing twice. Whichever way the guard
// falls, what is left is the ℕ-indexed law at the natural that branch
// names — the one n names when the guard holds, the one −n names when it
// does not — the negative branch differing only by standing under an
// inverse. Neither branch consults the guard it was handed: choosing the
// natural was the guard's whole job, and which natural it chose is
// something the ℕ-indexed law does not ask.

// ---------------------------------------------------------------------------
// MulZpowDistrib — a ℤ-indexed power of a product
// ---------------------------------------------------------------------------

// MulZpowDistrib — real_pow.MulPowDistrib at a ℤ exponent, and the one member
// here whose negative branch costs a fact of its own.
//
// It costs one because the two sides are not shaped alike there. The
// left is a single inverse, of the power of the product; the right is a
// PRODUCT of two inverses, one per factor. field.InvMul.Read(real_field.Field) read from
// right to left gathers those two into one, and with both sides a single
// inverse the ℕ-indexed law reaches under it and distributes the power
// exactly as it did on the other branch.
var MulZpowDistrib = mulZpowDistribThm{family.Add(registry.ProofEntry{
	Name: "MulZpowDistrib",
	Key:  "prop_4e2bf03efc9048c5",
	Build: family.Theorem("∀x y:real. ∀n:int. real_zpow(x * y, n) = real_zpow(x, n) * real_zpow(y, n)",
		func(a *Argument, x, y, n Term) {
			a.Show(
				"all three powers guard on the same sign of n, so the "+
					"definition opens into two branches and each is the ℕ-indexed law",
				// Each of the three becomes a COND on the one guard &0 ≤ n₀.
				Unfold(RealZpowDef),
				// ↦ one implication pair over the two ways that guard can stand,
				CondRewrite(),
				// which Basic() fans into its two leaves, each carrying the guard
				// as a hypothesis neither of them reads.
				Expect(Basic(),
					Case(
						"n nonnegative: the powers are ℕ-indexed at the "+
							"natural n₀ names, and the law there is MulPowDistrib",
						Cite(real_pow.MulPowDistrib)),
					Case(
						"n negative: that same law under an inverse, once "+
							"the right side's two inverses are gathered into one",
						// ↦ inv((x₀·y₀)ᵐ) = inv(x₀ᵐ · y₀ᵐ), where m is the natural
						// −n₀ names: multiplicativity of the inverse, read from
						// right to left.
						Cite(field.InvMul.Read(real_field.Field)),
						// And the distribution law reaches under that inverse.
						Cite(real_pow.MulPowDistrib)),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// InvZpow — a ℤ-indexed power of an inverse
// ---------------------------------------------------------------------------

// InvZpow — real_pow.InvPow at a ℤ exponent, and the cheapest of the three,
// because its two branches are literally the same goal.
//
// On the negative branch each side is a single inverse: the left inverts
// a power of x⁻¹, the right inverts an inverse of a power of x. Congr()
// strips that common inverse, and what it uncovers is the nonnegative
// branch's goal read at the natural −n names rather than the one n
// names. So the member cites one thing twice, and the collapse is its
// content — the law is the same law at whichever natural the guard
// picks.
//
// Where MulZpowDistrib needs multiplicativity of the inverse to bring
// its branches together, this one needs nothing: it varies a single
// factor, so no side of any branch ever carries more than one inverse.
var InvZpow = invZpowThm{family.Add(registry.ProofEntry{
	Name: "InvZpow",
	Key:  "prop_9d0bf14adbfe0f7b",
	Build: family.Theorem("∀x:real. ∀n:int. real_zpow(real_inv(x), n) = real_inv(real_zpow(x, n))",
		func(a *Argument, x, n Term) {
			a.Show(
				"both powers guard on the same sign of n, and either way "+
					"what is left is InvPow at the natural that branch names",
				Unfold(RealZpowDef),
				CondRewrite(),
				Expect(Basic(),
					Case(
						"n nonnegative: the ℕ-indexed law at the natural n₀ names, and nothing stands over it",
						Cite(real_pow.InvPow)),
					Case(
						"n negative: each side is a single inverse, and under "+
							"it stands the branch above at the natural −n₀ names",
						// ↦ (x₀⁻¹)ᵐ = inv(x₀ᵐ), which is that branch's goal.
						Congr(),
						Cite(real_pow.InvPow)),
				),
			)
		}),
})}

// ---------------------------------------------------------------------------
// DivZpow — a ℤ-indexed power of a quotient
// ---------------------------------------------------------------------------

// DivZpow — real_pow.DivPow at a ℤ exponent, and it repeats that member's
// argument rather than the two above it. A quotient is a product with an
// inverse, so opening it leaves the two laws immediately above and
// nothing to split on:
//
//	(x/y) zpow n = (x·y⁻¹) zpow n = (x zpow n) · ((y⁻¹) zpow n)
//	 = (x zpow n) · ((y zpow n)⁻¹) = (x zpow n)/(y zpow n)
//
// the second equality being MulZpowDistrib and the third InvZpow. The
// outer two are that abbreviation read in its two directions, and they
// cost nothing: one unfold opens the quotients on both sides of the goal
// at once, so the chain the proof runs is the middle two links.
//
// The member performs no sign analysis. It does not avoid one — it
// inherits two, one from each law it cites, and neither is visible here.
var DivZpow = divZpowThm{family.Add(registry.ProofEntry{
	Name: "DivZpow",
	Key:  "prop_f241d04cd2a1d748",
	Build: family.Theorem("∀x y:real. ∀n:int. real_zpow(x / y, n) = real_zpow(x, n) / real_zpow(y, n)",
		func(a *Argument, x, y, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			// The chapter states real_zpow and never builds it through its ops
			// handle; the two powers this chain names are read back out of the
			// leaf's own scope.
			// x₀ zpow n₀ — the factor that rides through untouched
			zpowX := ctx.TermText("real_zpow(x₀, n₀)")
			// (y₀⁻¹) zpow n₀ — the power the last leg turns inside out
			zpowInvY := ctx.TermText("real_zpow(real_inv(y₀), n₀)")

			a.Do(
				// x / y ↦ x · y⁻¹, on both sides of the equation at once, and
				// neither quotient is rebuilt afterwards.
				Unfold(real_field.RealDivDef),
				CalcEq(
					Leg(
						v.Mul.Apply(zpowX, zpowInvY),
						"the ℤ-indexed power distributes over the product the quotient has become",
						Cite(MulZpowDistrib)),
					FinalLeg(
						"and the inversion in the second factor moves out from under its power",
						Cite(InvZpow)),
				),
			)
		}),
})}

// ===========================================================================
// The zero base — the two guards that do not collapse
// ===========================================================================

// ---------------------------------------------------------------------------
// ZeroZpow — a zero base at an integer exponent
// ---------------------------------------------------------------------------

// ZeroZpow — real_pow.ZeroPow read at a ℤ exponent. The zero base is the one
// base whose power depends on nothing about the base and everything
// about whether the exponent vanishes.
//
// What the ℤ exponent adds is that a negative one cannot rescue it.
// There the definition asks for the INVERSE of a power of &0, at the
// natural −n names; that natural is nonzero because n is, so the power
// is &0, and &0 inverts to itself. The last step is a convention rather
// than a computation — real_construction.InvZero fixes it — and it is the only
// thing this member says that the ℕ-indexed law did not.
//
// Everything before it is bookkeeping about which natural the exponent
// names: OfNumRetract when the exponent is literally &0, NumOfIntSection
// when it is merely known nonnegative, and on the negative branch a
// trichotomy step to learn that −n is nonnegative at all.
var ZeroZpow = zeroZpowThm{family.Add(registry.ProofEntry{
	Name: "ZeroZpow",
	Key:  "prop_e92e84caed49a78a",
	Build: family.Theorem("∀n:int. real_zpow(&0, n) = COND(n = &0, &1, &0)",
		func(a *Argument, n Term) {
			ctx := a.Ctx()
			v := ops(ctx)
			zero := v.IntOfNum.Apply(ctx.Numeral(0)) // &0, the integer the trichotomy compares against
			negN := ctx.TermText("-n₀")              // −n₀, the exponent the negative branch reads
			expZero := ctx.Numeral(0)                // 0, the natural &0 names

			// The two guards, as the hypotheses the four leaves carry: the
			// statement's own n₀ = &0 and the definition's &0 ≤ n₀. Where the
			// first holds, the second arrives already rewritten through it,
			// which is why one of the pair below is a bare irreflexivity.
			atZero := ctx.MakePropText("n₀ = 0")
			nonzero := ctx.MakePropText("n₀ ≠ 0")
			nonneg := ctx.MakePropText("0 ≤ n₀")
			negative := ctx.MakePropText("¬(0 ≤ n₀)")
			irreflexive := ctx.MakePropText("¬(n₀ ≤ n₀)")

			a.Show(
				"the definition's guard is opened against the statement's "+
					"own, and all four ways the pair can stand are met",
				// A COND on &0 ≤ n₀ between the power at the natural n₀ names
				// and the inverse of the power at the natural −n₀ names.
				Unfold(RealZpowDef),
				// ↦ one implication tree over that guard and the statement's
				// n₀ = &0,
				CondRewrite(),
				// which Basic() fans into four leaves, each carrying one way
				// the pair can stand.
				Expect(Basic(),
					Case(
						"n = &0, nonnegative: the exponent names the natural 0, and the empty product is &1",
						// Both cited instances are ground, so simplification
						// alone settles the leaf: Normalized runs it, and the
						// refuter is never asked.
						By(
							Normalized,
							ResidentHyp(atZero),
							At(int_embed.OfNumRetract, expZero), // num_of_int(&0) = 0
							At(real_pow.ZeroPow, expZero))),     // 0⁰ = COND(0 = 0, &1, &0)
					Case(
						"n nonnegative but not &0: the natural it names is "+
							"nonzero too, so the product carries a factor of &0",
						// real_pow.ZeroPow is named as a rewrite here, where the leaf
						// above cites it as a ground premise. Its equation
						// grows left to right, so eqSimplify's size guard
						// declines to orient the ∀-form, and a plain cite
						// would leave it standing as a ∀-hypothesis for the
						// refuter to instantiate.
						Expect(LeanRw(ctx.Dep(real_pow.ZeroPow)),
							Case(
								"a power of &0 is settled by its exponent alone",
								Cite(real_pow.ZeroPow)),
							Case(
								"and this exponent is not 0, the integer it undoes not being &0",
								By(
									ResidentHyp(nonzero),
									ResidentHyp(nonneg),
									At(int_embed.NumOfIntSection, n))))), // &0 ≤ n₀ ⇒ &(num_of_int(n₀)) = n₀
					Case(
						"n = &0 yet not nonnegative: impossible, the guard having been rewritten to n ≰ n",
						By(ResidentHyp(irreflexive), int_real_lift.LessEqRefl)),
					Case(
						"n negative: −n names a nonzero natural, so the power "+
							"under the inverse is &0, and &0 inverts to itself",
						Derive(func(b *Argument) {
							// The three trichotomy instances ZpowNeg's fourth
							// case installs, used to reach its third disjunct
							// here rather than to refute all three.
							positive := b.Have(
								"negating a negative integer lands on a nonnegative one, n ≠ &0 killing the zero disjunct",
								"0 ≤ -n₀",
								By(
									ResidentHyp(nonzero),
									ResidentHyp(negative),
									At(int_real_lift.LessThanNegTotal, n),           // n₀ = &0 ∨ &0 < n₀ ∨ &0 < −n₀
									At(int_real_lift.LessEqOfLessThan, zero, n),     // &0 < n₀ ⇒ &0 ≤ n₀
									At(int_real_lift.LessEqOfLessThan, zero, negN))) // &0 < −n₀ ⇒ &0 ≤ −n₀
							nonzeroNeg := b.Have(
								"and it is not &0 either, negation being an involution that fixes &0",
								"-n₀ ≠ 0",
								By(
									ResidentHyp(nonzero),
									At(int_real_lift.NegNeg, n), // −(−n₀) = n₀
									int_real_lift.NegZero))      // −&0 = &0
							b.Show(
								"so the power under the inverse is &0, and &0 is its own inverse",
								Expect(LeanRw(ctx.Dep(real_pow.ZeroPow)),
									Case(
										"a power of &0 is settled by its exponent alone",
										Cite(real_pow.ZeroPow)),
									Case(
										"this exponent is not 0 either, so the power is &0, which inverts to itself",
										By(
											nonzeroNeg,
											positive,
											At(int_embed.NumOfIntSection, negN), // &0 ≤ −n₀ ⇒ &(num_of_int(−n₀)) = −n₀
											real_construction.InvZero))))        // (&0)⁻¹ = &0
						})),
				),
			)
		}),
})}

// ===========================================================================
// The exponent's law — adding exponents multiplies powers, over all of ℤ
// ===========================================================================

// ZpowAdd — real_pow.PowAdd at a ℤ exponent: the map n ↦ xⁿ still carries
// addition to multiplication when n is allowed to be negative.
//
// The base has to be nonzero now, and that is not bookkeeping. At x = &0
// the left side of x⁻¹·x¹ = x⁰ is &0·&0 by the inv 0 = 0 convention
// while the right side is &1, so the law is simply false there; the
// hypothesis is what buys the cancellation the negative exponents need.
//
// The proof rests on ℤ being the differences of ℕ. Once each exponent is
// written as &a − &b the ℤ-indexed power is a quotient of two ℕ-indexed
// ones,
//
//	x^(&a − &b) = xᵃ · (xᵇ)⁻¹
//
// and adding exponents becomes adding the numerators' and the
// denominators' separately — which is real_pow.PowAdd twice, with the two
// denominators gathered under one inverse. That is the whole argument,
// and it replaces the four-way sign analysis (+/+, −/−, −/+, +/−) the
// statement invites: the signs are absorbed once, into the difference
// form, rather than met four times over.
//
// Five sections. `asDifference` is the presentation — every integer is
// &a − &b, one of the two slots empty. `gap` is the ℤ arithmetic the
// difference form needs: one identity, read forwards in one order case
// and negated in the other. `cancel` is the only place inversion is
// used as more than notation: xᵏ·(xᵏ)⁻¹ = &1, proved without induction
// by pushing the inverse through the power and collapsing x·x⁻¹ under
// it. `diffPow` is the quotient reading above, and it is where the two
// order cases live, because which of a and b is larger decides which
// side of &0 the difference falls on. `merge` is the law for two
// exponents already in difference form, which leaves the headline
// nothing to do but present them that way.
var ZpowAdd = zpowAddThm{family.Add(registry.ProofEntry{
	Name: "ZpowAdd",
	Key:  "prop_de3bde85b2613f4f",
	Build: family.Sections(Statement{
		Binders: "∀x:real. ∀m n:int.",
		Hypotheses: []string{
			"x ≠ &0",
		},
		Conclusion: "real_zpow(x, m + n) = real_zpow(x, m) * real_zpow(x, n)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			v := ops(ctx)
			zeroNat := ctx.Numeral(0)            // 0, the natural
			zeroInt := v.IntOfNum.Apply(zeroNat) // &0, the integer it names

			// ℤ as the differences of ℕ. Either sign is already a
			// difference — one with nothing on the left, one with nothing
			// on the right — so the two branches differ only in which slot
			// the natural takes.
			asDifference := ctx.Lemma("∀m:int. ∃a b:num. m = &a - &b",
				func(a *Argument, m Term) {
					// One natural serves both signs, so it is named once and
					// the case analysis is over the sign alone.
					c, sign := a.Obtain(
						"m is plus or minus an embedded natural",
						"∃c:num. m = -&c ∨ m = &c",
						By(int_embed.Image))
					embedC := v.IntOfNum.Apply(c)

					a.Do(sign.SplitDisj(
						LeftHolds(
							"m = −&c: the natural goes on the right, and negating IS subtracting from &0",
							Given(func(a *Argument, isNeg Fact) {
								a.Take(zeroNat)
								a.Take(c)
								a.Show(
									"−&c is &0 − &c",
									By(isNeg, int_real_lift.SubLeftZero))
							})),
						RightHolds(
							"m = &c: the natural goes on the left, and taking &0 back off changes nothing",
							Given(func(a *Argument, isPos Fact) {
								a.Take(c)
								a.Take(zeroNat)
								a.Show(
									"&c is &c − &0",
									By(
										isPos,
										At(int_real_lift.EqSubRightAdd, embedC, zeroInt, embedC), // &c − &0 = &c ⇔ &c = &c + &0
										int_real_lift.AddRightIdentity))
							})),
					))
				})

			// The one piece of ℤ arithmetic the proof needs, and it is
			// needed in both directions: taking a summand back off an
			// embedded sum leaves the other summand. The order case where
			// the difference comes out NEGATIVE reads the same identity
			// under a negation, which is why there is one lemma here and
			// not two.
			gap := ctx.Lemma("∀k d:num. k + d - &k = int_of_num(d)",
				func(a *Argument, k, d Term) {
					embedK, embedD := v.IntOfNum.Apply(k), v.IntOfNum.Apply(d)
					split := a.Term("(k + int_of_num(d)) - int_of_num(k)")
					commuted := a.Term("(int_of_num(d) + k) - int_of_num(k)")
					dThenK := a.Term("int_of_num(d) + k")

					// One law per link, each read at the instance the link
					// needs — and the instances are the point, because the
					// difficulty here is entirely the ORDER of the two
					// summands: the subtraction law wants the subtrahend
					// written last and & hands it over written first, so the
					// middle leg is a permutation and nothing else.
					// A permutation is also what no rewrite discharges, which
					// is why that leg alone declares Normalized: its ground
					// commutation and the goal meet under Basic() but not in
					// the clause form the refuter would see. The other two legs
					// close at the install and need no shaping.
					a.Do(CalcEq(
						Leg(
							split,
							"& is additive, so the embedded sum splits into two",
							Cite(int_embed.OfNumAdd)),
						Leg(
							commuted,
							"and the two summands commute, moving the one that is taken back off to the end",
							By(Normalized, At(int_real_lift.AddSym, embedK, embedD))), // &k + &d = &d + &k
						FinalLeg(
							"where taking it off is what adding it undoes",
							// (&d + &k) − &k = &d ⇔ &d + &k = &d + &k
							By(At(int_real_lift.EqSubRightAdd, dThenK, embedK, embedD))),
					))
				})

			// The cancellation the negative exponents live on, and the one
			// fact in the movement that is about inversion rather than
			// about powers. No induction: inversion passes through a power
			// (real_pow.InvPow), two powers at one exponent are the power of the
			// product (real_pow.MulPowDistrib), and what is left under the exponent
			// is x against its own inverse.
			//
			// Nothing here asks whether xᵏ is nonzero — the hypothesis is
			// consumed at x, before the power is ever formed, which is what
			// keeps a nonvanishing-power lemma out of the dependency set.
			cancel := ctx.Lemma(Statement{
				Binders: "∀x:real. ∀k:num.",
				Hypotheses: []string{
					"x ≠ &0",
				},
				Conclusion: "real_pow(x, k) * real_inv(real_pow(x, k)) = &1",
			},
				func(a *Argument, x, k Term, nonzero Fact) {
					invX := v.Inv.Apply(x) // x⁻¹ — the base the second factor turns out to be a power of

					a.Do(CalcEq(
						Leg(
							v.Mul.Apply(v.Pow.Apply(x, k), v.Pow.Apply(invX, k)),
							"the inverted power is a power of the inverted base",
							Cite(real_pow.InvPow)),
						Leg(
							v.Pow.Apply(v.Mul.Apply(x, invX), k),
							"and two powers at one exponent are the power of the product",
							Cite(real_pow.MulPowDistrib)),
						Leg(
							v.Pow.Apply(v.Lit(1), k),
							"that product being x against its own inverse, which x ≠ &0 makes &1",
							// The premises are complete; what they need is the
							// guard discharged before the closer sees them, the
							// invertibility law arriving with its own x = &0
							// disjunct still attached.
							By(
								Normalized,
								nonzero,
								At(field.MulRightInverse.Read(real_field.Field), x))), // x ≠ &0 ⇒ x · x⁻¹ = &1
						FinalLeg(
							"and every power of &1 is &1",
							Cite(real_pow.OnePow)),
					))
				})

			// The quotient reading of a ℤ-indexed power, and the only
			// place the sign of the exponent is argued about. Which of the
			// two naturals is larger decides it: ℕ's order IS the
			// existence of a gap, so one of them is the other plus d, and
			// the difference of their images is ±&d accordingly. Either
			// way the surviving power is the gap's, and `cancel` is what
			// removes the common part.
			diffPow := ctx.Lemma(Statement{
				Binders: "∀x:real. ∀a b:num.",
				Hypotheses: []string{
					"x ≠ &0",
				},
				Conclusion: "real_zpow(x, &a - &b) = real_pow(x, a) * real_inv(real_pow(x, b))",
			},
				func(arg *Argument, x, a, b Term, nonzero Fact) {
					powA, powB := v.Pow.Apply(x, a), v.Pow.Apply(x, b)
					invPowA, invPowB := v.Inv.Apply(powA), v.Inv.Apply(powB)

					arg.Do(At(nat_order.LessEqTotal, a, b).SplitDisj(
						LeftHolds(
							"a ≤ b: the exponent is negative, and what survives is the gap's power, inverted",
							Given(func(arg *Argument, le Fact) {
								d, split := arg.Obtain(
									"b is a plus a gap",
									"∃d:num. b = a + d",
									By(le, nat_order.LessEqExists))
								invPowD := v.Inv.Apply(v.Pow.Apply(x, d))

								negGap := arg.Have(
									"read the other way round the difference is the gap, so this way it is minus the gap",
									"a - &(a + d) = -int_of_num(d)",
									CalcEq(
										Leg(
											arg.Term("-(a + d - int_of_num(a))"),
											"reading a difference backwards negates it",
											Cite(int_real_lift.NegSub)), // −(y − z) = z − y
										FinalLeg(
											"and read that way round it is the gap",
											Congr(),
											By(gap)),
									))

								arg.Show(
									"xᵃ meets its own inverse inside x^b, leaving the gap's inverse alone",
									split.Rw(),  // b ↦ a + d, in the goal and beside it
									negGap.Rw(), // and the exponent that leaves ↦ −&d
									CalcEq(
										Leg(
											arg.Term("real_inv(real_zpow(x, &d))"),
											"a negated exponent inverts",
											Cite(ZpowNeg)),
										Leg(
											invPowD,
											"and under that inverse the bridge crosses at the gap",
											Cite(ZpowOfNum)),
										Leg(
											v.Mul.Apply(v.Mul.Apply(powA, invPowA), invPowD),
											"put the unit back as xᵃ against its own inverse",
											By(nonzero, At(cancel, x, a), real_construction.MulLeftId)),
										Leg(
											v.Mul.Apply(powA, v.Mul.Apply(invPowA, invPowD)),
											"reassociate so the two inverses stand side by side",
											Cite(real_construction.MulAssoc)),
										FinalLeg(
											"and they gather into the inverse of the power at a + d",
											By(field.InvMul.Read(real_field.Field), real_pow.PowAdd)),
									))
							})),
						RightHolds(
							"b ≤ a: the exponent is the gap itself, and x^b divides out of x^a",
							Given(func(arg *Argument, ge Fact) {
								d, split := arg.Obtain(
									"a is b plus a gap",
									"∃d:num. a = b + d",
									By(ge, nat_order.LessEqExists))
								powD := v.Pow.Apply(x, d)

								gapInst := arg.Have(
									"the difference of &(b + d) and &b is the gap",
									"b + d - &b = int_of_num(d)",
									By(gap))

								arg.Show(
									"x^b meets its own inverse, leaving the gap's power alone",
									split.Rw(),   // a ↦ b + d
									gapInst.Rw(), // and the exponent that leaves ↦ &d
									CalcEq(
										Leg(
											powD,
											"the bridge crosses at the gap",
											Cite(ZpowOfNum)),
										Leg(
											v.Mul.Apply(powD, v.Mul.Apply(powB, invPowB)),
											"put the unit back as x^b against its own inverse",
											By(nonzero, At(cancel, x, b), real_ring.MulRightId)),
										Leg(
											v.Mul.Apply(v.Mul.Apply(powB, powD), invPowB),
											"regroup so the two powers of x stand side by side",
											ACRegroupWith(real_construction.MulAC(ctx))),
										FinalLeg(
											"and their exponents merge into b + d",
											Cite(real_pow.PowAdd)),
									))
							})),
					))
				})

			// The law itself, for exponents already presented as
			// differences — which is where all the work is, the top below
			// being nothing but the presentation. Two differences add
			// coordinatewise, so the merged exponent's quotient has the
			// two numerators multiplied and the two denominators
			// multiplied; real_pow.PowAdd splits both back apart and the inverses
			// gather, leaving each numerator standing over its own
			// denominator.
			merge := ctx.Lemma(Statement{
				Binders: "∀x:real. ∀p q r s:num.",
				Hypotheses: []string{
					"x ≠ &0",
				},
				Conclusion: "real_zpow(x, &p - &q + (&r - &s)) = real_zpow(x, &p - &q) * real_zpow(x, &r - &s)",
			},
				func(a *Argument, x, p, q, r, s Term, nonzero Fact) {
					sumP, sumQ := a.Term("p + r"), a.Term("q + s") // the merged numerator and denominator exponents
					powP, powR := v.Pow.Apply(x, p), v.Pow.Apply(x, r)
					invQ, invS := v.Inv.Apply(v.Pow.Apply(x, q)), v.Inv.Apply(v.Pow.Apply(x, s))

					// The exponents merge in ℤ before anything is said about
					// powers. Additivity of the difference is size-neutral, so
					// nothing orients it on its own and the direction is named;
					// & then gathers each of the two ℕ sums.
					expMerge := a.Have(
						"two differences add coordinatewise, and & carries each ℕ sum",
						"&p - q + (int_of_num(r) - int_of_num(s)) = p + r - int_of_num(q + s)",
						Expect(LeanRw(ctx.Dep(int_real_lift.SubAddPairwise)),
							Case(
								"the numerators gather against the denominators",
								Cite(int_real_lift.SubAddPairwise)),
							Case(
								"and each gathered ℕ sum comes back inside &",
								Cite(int_embed.OfNumAdd))))

					a.Show(
						"with the exponent merged, what is left is the ℕ-indexed law over numerator and denominator",
						expMerge.Rw(), // the exponent ↦ &(p + r) − &(q + s)
						CalcEq(
							Leg(
								v.Mul.Apply(v.Pow.Apply(x, sumP), v.Inv.Apply(v.Pow.Apply(x, sumQ))),
								"the merged difference reads as one ℕ-power over another",
								By(nonzero, diffPow)),
							Leg(
								v.Mul.Apply(v.Mul.Apply(powP, powR),
									v.Inv.Apply(v.Mul.Apply(v.Pow.Apply(x, q), v.Pow.Apply(x, s)))),
								"and both merged exponents split apart again",
								Cite(real_pow.PowAdd)),
							Leg(
								v.Mul.Apply(v.Mul.Apply(powP, powR), v.Mul.Apply(invQ, invS)),
								"the inverse of the denominators' product being the product of their inverses",
								Cite(field.InvMul.Read(real_field.Field))),
							Leg(
								v.Mul.Apply(v.Mul.Apply(powP, invQ), v.Mul.Apply(powR, invS)),
								"regroup so each numerator stands over its own denominator",
								ACRegroupWith(real_construction.MulAC(ctx))),
							Leg(
								v.Mul.Apply(a.Term("real_zpow(x, &p - &q)"), v.Mul.Apply(powR, invS)),
								"the first pair is the ℤ-indexed power at its own difference",
								By(nonzero, diffPow)),
							FinalLeg(
								"and so is the second",
								By(nonzero, diffPow)),
						))
				})

			return ctx.Theorem(headline, func(a *Argument, x, m, n Term, nonzero Fact) {
				_, _, mDiff := a.Unpack2(At(asDifference, m))
				_, _, nDiff := a.Unpack2(At(asDifference, n))

				a.Show(
					"with both exponents written as differences of naturals, the law is the one above",
					mDiff.Rw(), // m ↦ &p − &q
					nDiff.Rw(), // n ↦ &r − &s
					By(nonzero, merge))
			})
		}),
})}

// ---------------------------------------------------------------------------
// ZpowSub — subtracting exponents divides powers
// ---------------------------------------------------------------------------

// ZpowSub — the law above read at an exponent turned round, which is all
// that subtracting one is.
//
// A difference of integers is a sum with the subtrahend negated, and
// once the exponent is written that way the two ℤ-indexed laws already
// here finish it:
//
//	x^(m−n) = x^(m+(−n)) = xᵐ · x^(−n) = xᵐ · (xⁿ)⁻¹
//
// the middle equality being ZpowAdd and the last ZpowNeg. The quotient
// the statement asks for is opened before any of that and never rebuilt,
// exactly as DivZpow opens its own two, so what the chain lands on is
// the product on the right.
//
// The base has to be nonzero for exactly the reason ZpowAdd does, and
// this member adds nothing to the demand: the hypothesis is passed
// straight to that law and consumed only there. In particular nothing
// here asks whether xⁿ is nonzero, which is what dividing by it would
// otherwise seem to require — the division is notation for a product
// with an inverse, and ZpowAdd has already paid for the inverse.
var ZpowSub = zpowSubThm{family.Add(registry.ProofEntry{
	Name: "ZpowSub",
	Key:  "prop_a59414051f7e24e2",
	Build: family.Theorem(Statement{
		Binders: "∀x:real. ∀m n:int.",
		Hypotheses: []string{
			"x ≠ &0",
		},
		Conclusion: "real_zpow(x, m - n) = real_zpow(x, m) / real_zpow(x, n)",
	},
		func(a *Argument, x, m, n Term, nonzero Fact) {
			ctx := a.Ctx()
			v := ops(ctx)
			// The chapter states real_zpow and never builds it, so the
			// powers this chain names are read back out of the leaf's own
			// scope, as DivZpow reads its two.
			negN := ctx.TermText("-n₀") // −n₀ — the exponent ZpowAdd is read at
			// x^(m + (−n)) — the difference, re-presented as a sum
			sumExp := ctx.TermText("real_zpow(x₀, m₀ + -n₀)")
			powM := ctx.TermText("real_zpow(x₀, m₀)")     // xᵐ — the factor that rides through untouched
			powNegN := ctx.TermText("real_zpow(x₀, -n₀)") // x^(−n) — the factor the last leg inverts

			a.Do(
				// x / y ↦ x · y⁻¹, and nothing below rebuilds the quotient.
				Unfold(real_field.RealDivDef),
				CalcEq(
					Leg(
						sumExp,
						"a difference of integers is a sum with the subtrahend negated",
						By(
							At(int_real_lift.SubRightNeg, m, negN), // m₀ − −(−n₀) = m₀ + (−n₀)
							int_real_lift.NegNeg)),
					Leg(
						v.Mul.Apply(powM, powNegN),
						"and at a sum the exponent law splits the power, which "+
							"is the one place the base's nonvanishing is asked for",
						By(nonzero, At(ZpowAdd, x, m, negN))),
					FinalLeg(
						"a negated exponent inverts, and that inverse is the quotient the statement wrote",
						Cite(ZpowNeg)),
				),
			)
		}),
})}
