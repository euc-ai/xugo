// real_sgn_abs.go — the chapter: ℝ's sign–absolute-value pair.
//
// Six parts, marked by banners:
//
// - The two bounds the absolute value satisfies with no hypothesis at
// all
// - The absolute value as an equation
// - The absolute value is multiplicative
// - README movement 7
// - README movement 4
// - README movements 5 and 6

package real_sgn_abs

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The two bounds the absolute value satisfies with no hypothesis at all
// ---------------------------------------------------------------------------
//
// the two bounds the absolute value satisfies with no hypothesis at all:
// it is never below &0, and never below its own argument.
//
// Both unfold the case definition and split on its guard `&0 ≤ x`, and
// stating them together is what makes the second one cheap. AbsNonneg has
// to do the sign reasoning on both branches, because `|x|` is a
// different term on each. AbsDominates then reuses it rather than
// repeating it: below the guard, `x ≤ &0` and AbsNonneg's `&0 ≤ |x|` meet
// at &0, so that branch never has to name `-x` at all.

// AbsNonneg — a size is never negative. This is what lets every later
// member treat `|x|` as living in ℝ's nonnegative half without
// carrying a hypothesis for it.
var AbsNonneg = absNonnegThm{family.Add(registry.ProofEntry{
	Name: "AbsNonneg",
	Key:  "prop_f7cee4966976fafc",
	Build: family.Theorem("∀x:real. &0 ≤ |x|", func(a *Argument, x Term) {
		v := ops(a.Ctx())

		// Both branches need to know which of the two values `|x|` is,
		// so the definition is unfolded once, before the split.
		a.Do(Unfold(RealAbsDef))
		a.Cases(v.Nonneg(x))
		a.When(
			"x is already nonnegative, so |x| is x",
			func(b *Argument, xNonneg Fact) {
				b.Show(
					"&0 ≤ x, which is the claim once the COND collapses",
					By(xNonneg))
			})
		a.Otherwise(
			"x is negative, so |x| is -x, and one of the two is always nonnegative",
			func(b *Argument, xNegative Fact) {
				// The COND collapses on the failed guard before any
				// order reasoning starts; what is left is `&0 ≤ -x`.
				b.Do(TrivialSimplify())
				b.Show(
					"the guard ruled out the first alternative, so the second holds",
					// &0 ≤ x ∨ &0 ≤ -x — a value and its negation
					// cannot both be below &0, and this is the whole
					// of the negative branch at every member of the
					// chapter.
					By(xNegative, At(real_order_ring.LessEqNegTotal, x)))
			})
	}),
})}

// AbsDominates — nothing exceeds its own size. Where AbsNonneg bounds `|x|`
// below by a constant, this bounds it below by the argument, and that
// is the form arguments by contradiction reach for: a quantity forced
// strictly above its own size has nowhere to be.
var AbsDominates = absDominatesThm{family.Add(registry.ProofEntry{
	Name: "AbsDominates",
	Key:  "prop_dfb02b60cdd63dde",
	Build: family.Theorem("∀x:real. x ≤ |x|", func(a *Argument, x Term) {
		v := ops(a.Ctx())
		zero := v.Lit(0)

		// Split BEFORE unfolding, which is the difference from AbsNonneg
		// above: only the nonnegative branch needs to know what `|x|`
		// is, and the negative one is shorter for being left with the
		// absolute value intact.
		a.Cases(v.Nonneg(x))
		a.When(
			"x is already nonnegative, so |x| is x and the claim is reflexivity",
			func(b *Argument, xNonneg Fact) {
				b.Do(Unfold(RealAbsDef))
				b.Show(
					"x is at or below itself",
					By(xNonneg, real_order_ring.LessEqRefl))
			})
		a.Otherwise(
			"x is negative, so it is at or below &0, which AbsNonneg puts at or below |x|",
			func(b *Argument, xNegative Fact) {
				b.Show(
					"&0 lies between x and its size",
					By(
						xNegative,
						// x ≤ &0 ∨ &0 ≤ x — the left leg, whose second
						// alternative the failed guard ruled out. This
						// is why the branch never mentions -x at all.
						At(real_construction.LessEqTotal, zero, x),
						// &0 ≤ |x| — the right leg
						At(AbsNonneg, x),
						// the two legs meet at &0
						At(real_construction.LessEqTrans, x, zero, v.Size(x))))
			})
	}),
})}

// ---------------------------------------------------------------------------
// The absolute value as an equation
// ---------------------------------------------------------------------------
//
// the absolute value as an equation: which arguments it leaves alone,
// which it flips, and which single argument it sends to &0.
//
// The chapter's two characterizations open the file. `AbsFixedIffNonneg`
// says when the size leaves its argument alone and `AbsEven` says the size
// forgets the sign; everything after them is one of the two read at a
// particular value — `|x|` itself, an embedded natural, `&1`, `&0` —
// or, in `AbsVanishes` and `AbsPosIffNonzero`, the one place the size
// collapses and what that means for the strict order.
//
// `AbsEven` and `AbsVanishes` are the file's two case analyses, both
// splitting on the size's own guard `&0 ≤ x`. `AbsEven` is the only member in the chapter whose split is not
// binary, and the more instructive of the two. Its two sides are guarded by
// `&0 ≤ -x` and `&0 ≤ x`, and those two guards are OVERLAPPING (both
// hold at &0, which is why there is a leaf for that point) but also
// EXHAUSTIVE (a value and its negation are never both below &0, which
// is why there is no fourth). The exhaustiveness is
// `real_order_ring.LessEqNegTotal`, and the negative leaf cites it
// rather than arguing it.

// AbsEven — the absolute value forgets the sign. Stated in the direction
// that reads as a rewrite of the negated argument, which is how every
// consumer meets it: a `-x` appears and the size is unchanged.
var AbsEven = absEvenThm{family.Add(registry.ProofEntry{
	Name: "AbsEven",
	Key:  "prop_bf73d41d87887d6",
	Build: family.Theorem("∀x:real. |-x| = |x|", func(a *Argument, x Term) {
		v := ops(a.Ctx())
		zero, negX := v.Lit(0), v.Negate(x)

		// Both sides are guarded CONDs, so both definitions are
		// unfolded before either guard is decided.
		a.Do(Unfold(RealAbsDef))
		a.Cases(v.Nonneg(x))
		a.When(
			"x is nonnegative, so the right side is x; which value the LEFT takes still depends on -x's sign",
			func(b *Argument, xNonneg Fact) {
				b.Cases(v.Nonneg(negX))
				b.When(
					"both x and -x are nonnegative, which pins x at &0 — and "+
						"there the two sides agree because negating &0 changes nothing",
					func(c *Argument, negXNonneg Fact) {
						// The CONDs stay standing on this leaf:
						// both guards hold, so the claim follows
						// by substituting x = &0 rather than by
						// collapsing either side first.
						pinned := c.Have(
							"nothing can be strictly on both sides of &0",
							"x₀ = &0",
							By(
								xNonneg,
								negXNonneg,
								// &0 ≤ -x ⇔ x ≤ &0, the second
								// half of the squeeze
								At(real_order_ring.NegNonnegativeIffNonpositive, x),
								// x = &0 ⇔ x ≤ &0 ∧ &0 ≤ x
								At(real_construction.LessEqAntisym, x, zero)))
						c.Show(
							"and at &0 the two sides are the same value",
							// -&0 = &0. Bare: the row binds
							// nothing, so there is no instance
							// to pick.
							By(pinned, real_ring.NegZero))
					})
				b.Otherwise(
					"x is nonnegative and -x is not, so the left side is --x",
					func(c *Argument, negXNegative Fact) {
						// Both guards are decided here, so both
						// CONDs collapse and the claim is the
						// double negation alone.
						c.Do(TrivialSimplify())
						c.Show(
							"negating twice returns x, which is the right side",
							By(real_ring.NegNeg))
					})
			})
		a.Otherwise(
			"x is negative, so the right side is -x and the left side's guard holds",
			func(b *Argument, xNegative Fact) {
				// The right side's COND collapses on the failed
				// guard; the left side's is decided by the premise.
				b.Do(TrivialSimplify())
				b.Show(
					"the guard ruled out the first alternative, so -x is nonnegative and the left side is -x too",
					By(xNegative, At(real_order_ring.LessEqNegTotal, x)))
			})
	}),
})}

// AbsFixedIffNonneg — the absolute value leaves its argument alone
// exactly on the nonnegative half. This is the chapter's converse
// direction: `AbsNonneg` and `Dominates` say what `|x|` is bounded by,
// and this says when it is nothing new at all.
var AbsFixedIffNonneg = absFixedIffNonnegThm{family.Add(registry.ProofEntry{
	Name: "AbsFixedIffNonneg",
	Key:  "prop_ec93e210cd6c0a2f",
	Build: family.Theorem("∀x:real. |x| = x ⇔ &0 ≤ x", func(a *Argument, x Term) {

		// No case split. Right to left the guard IS the hypothesis and
		// the COND collapses; left to right the proof is by
		// contraposition — a failed guard makes the equation say
		// `-x = x` while `&0 ≤ -x` holds, and that forces the guard
		// after all.
		a.Do(Unfold(RealAbsDef))
		a.Show(
			"the equation holds exactly when the definition's guard does",
			// Normalized: the premise is complete, but the COND has to
			// be reduced against the guard before it meets the closer.
			By(Normalized, At(real_order_ring.LessEqNegTotal, x)))
	}),
})}

// AbsNegatedIffNonpos — and the absolute value flips its argument's sign
// exactly on the nonpositive half. The dual of AbsFixedIffNonneg: that
// one says when the size is nothing new, this says when it is a
// reflection, and between them they cover the line.
//
// They OVERLAP at &0, and reconciling the overlap is this member's whole
// content — a value that is both nonnegative and nonpositive is fixed
// and reflected at once, which is consistent only because `-&0 = &0`.
// That is why it is worth stating rather than rebuilding: the four
// premises below are about the overlap, not about whatever the citing
// member happens to be proving.
//
// Three members cite it (AbsMul, SgnMulSelfIsAbs, SgnEqSelfDivAbs).
var AbsNegatedIffNonpos = absNegatedIffNonposThm{family.Add(registry.ProofEntry{
	Name: "AbsNegatedIffNonpos",
	Key:  "prop_6930e641b485888a",
	Build: family.Theorem("∀x:real. |x| = -x ⇔ x ≤ &0", func(a *Argument, x Term) {
		v := ops(a.Ctx())

		// The COND is left standing: both directions are about which
		// branch it takes, so neither guard is decided in advance.
		a.Do(Unfold(RealAbsDef))
		a.Show(
			"the size flips the sign exactly on the nonpositive half, the two halves agreeing at &0",
			By(
				Normalized,
				// &0 ≤ x ∨ &0 ≤ -x
				At(real_order_ring.LessEqNegTotal, x),
				// x ≤ &0 ⇔ &0 ≤ -x
				At(real_order_ring.NegNonnegativeIffNonpositive, x),
				// x = &0 ⇔ x ≤ &0 ∧ &0 ≤ x — the overlap …
				At(real_construction.LessEqAntisym, x, v.Lit(0)),
				// … and -&0 = &0, which is why the two readings agree there
				real_ring.NegZero))
	}),
})}

// AbsOfZero — &0 is its own size. It is AbsFixedIffNonneg read at the one
// point where the definition's two branches agree, so it is proved
// that way rather than by unfolding again: the characterization needs
// `&0 ≤ &0`, and that is reflexivity.
var AbsOfZero = absOfZeroThm{family.Add(registry.ProofEntry{
	Name: "AbsOfZero",
	Key:  "prop_ce5b5010931ae606",
	Build: family.Theorem("|&0| = &0", func(a *Argument) {
		v := ops(a.Ctx())
		zero := v.Lit(0)

		a.Show(
			"&0 is nonnegative, so it is fixed",
			By(
				// |&0| = &0 ⇔ &0 ≤ &0
				At(AbsFixedIffNonneg, zero),
				real_order_ring.LessEqRefl))
	}),
})}

// AbsIdempotent — taking the size of a size adds nothing. It is
// `AbsFixedIffNonneg` applied to `|x|`, which `AbsNonneg` has already put in
// the nonnegative half, so the case definition is never reopened.
var AbsIdempotent = absIdempotentThm{family.Add(registry.ProofEntry{
	Name: "AbsIdempotent",
	Key:  "prop_faef945c60848e30",
	Build: family.Theorem("∀x:real. ||x|| = |x|", func(a *Argument, x Term) {
		a.Show(
			"|x| is nonnegative, so it is one of the values the size fixes",
			By(
				// bare: fires as a goal rewrite, ↦ `&0 ≤ |x|`
				AbsFixedIffNonneg,
				AbsNonneg))
	}),
})}

// AbsOfNum — the embedded naturals are all fixed, ℕ having no negative
// part for the size to fold away. Same shape as AbsIdempotent: the
// characterization plus a nonnegativity fact, this one from the
// embedding rather than from this chapter.
var AbsOfNum = absOfNumThm{family.Add(registry.ProofEntry{
	Name: "AbsOfNum",
	Key:  "prop_85571dde5e313dd6",
	Build: family.Theorem("∀n:num. |&n| = &n", func(a *Argument, n Term) {
		v := ops(a.Ctx())

		a.Show(
			"an embedded natural is nonnegative, so it is fixed",
			By(
				// Ground at `&n`, unlike AbsIdempotent's bare cite above:
				// there the rewrite target IS the goal's own subject and
				// the cite fires as a rewrite, here it would install as
				// a wide ∀-hypothesis and the leaf would fall through to
				// a refutation.
				At(AbsFixedIffNonneg, v.Embed(n)),
				real_order_ring.NumNonneg))
	}),
})}

// AbsOfOne — `&1` is fixed, which is AbsOfNum read at 1. Stated separately
// because the unit is what later members carry into multiplicative
// arguments, where reaching it through a ∀-instantiation costs a step
// at every site.
var AbsOfOne = absOfOneThm{family.Add(registry.ProofEntry{
	Name: "AbsOfOne",
	Key:  "prop_f6f510ac94f9d6e6",
	Build: family.Theorem("|&1| = &1", func(a *Argument) {
		a.Show(
			"the unit is an embedded natural",
			By(AbsOfNum))
	}),
})}

// AbsVanishes — &0 is the only argument whose size is &0. This is the
// chapter's separation fact: everything above it that needs "these two
// are different" reaches for it through AbsPosIffNonzero below.
var AbsVanishes = absVanishesThm{family.Add(registry.ProofEntry{
	Name: "AbsVanishes",
	Key:  "prop_146fa6a3214673f1",
	Build: family.Theorem("∀x:real. |x| = &0 ⇔ x = &0", func(a *Argument, x Term) {
		v := ops(a.Ctx())

		// Unlike the fixed-point members above, this one does reopen
		// the definition: the claim is about BOTH branches, and neither
		// is known in advance to be the one taken.
		a.Do(Unfold(RealAbsDef))
		a.Cases(v.Nonneg(x))
		a.When(
			"x is nonnegative, so its size is x and the two sides are the same equation",
			func(b *Argument, xNonneg Fact) {
				b.Show(
					"nothing to prove once the COND collapses",
					By(xNonneg))
			})
		a.Otherwise(
			"x is negative, so its size is -x, and a negation vanishes exactly with its argument",
			func(b *Argument, xNegative Fact) {
				b.Do(TrivialSimplify())
				b.Show(
					"-x = &0 says the same as x = &0",
					By(real_ring.NegEqZero))
			})
	}),
})}

// AbsPosIffNonzero — away from &0 the size is strictly positive. This is
// `AbsVanishes` with the order put back in: `AbsNonneg` already places `|x|`
// at or above &0, so ruling out equality is the whole of strictness,
// and AbsVanishes says when equality holds.
var AbsPosIffNonzero = absPosIffNonzeroThm{family.Add(registry.ProofEntry{
	Name: "AbsPosIffNonzero",
	Key:  "prop_2a9931176b2c3e61",
	Build: family.Theorem("∀x:real. &0 < |x| ⇔ x ≠ &0", func(a *Argument, x Term) {
		ctx := a.Ctx()
		v := ops(ctx)
		size := v.Size(x)

		a.Show(
			"|x| sits at or above &0, so it is strictly above exactly when it is not equal",
			// Normalized: the premises are complete, but strictness has
			// to be unfolded into a negated comparison before they meet
			// the closer.
			By(
				Normalized,
				// |x| = &0 ⇔ x = &0
				At(AbsVanishes, x),
				// &0 ≤ |x| — the half that makes "not equal" enough
				At(AbsNonneg, x),
				// |x| = &0 ⇔ |x| ≤ &0 ∧ &0 ≤ |x|
				At(real_construction.LessEqAntisym, size, v.Lit(0)),
				// ¬(|x| ≤ &0) ⇔ &0 < |x| — real_lt's definition, at the
				// witness pair that fills the negated comparison in
				// reading order
				At(MakeFact(ctx.ConstDefNormalized("real_lt")), size, v.Lit(0))))
	}),
})}

// ---------------------------------------------------------------------------
// The absolute value is multiplicative
// ---------------------------------------------------------------------------
//
// This is the chapter's first argument about two arguments, and its
// case analysis is correspondingly the first that is genuinely
// two-dimensional: each of x and y is split on its own sign, and the
// four leaves are the four sign combinations. The product's OWN sign is
// not split on — it is derived in each leaf from the two that were.
//
// Nothing here unfolds the case definition. Each leaf establishes the
// sign of x, of y, and of the product, and then `AbsFixedIffNonneg` and
// `AbsNegatedIffNonpos` rewrite all three absolute values from those
// signs — so no COND ever reaches a closer, and every intermediate the
// argument names is a `Have` on the page.
//
// Every leaf and every `Have` here closes `By(Normalized, …)`, and the
// shaping is doing one job throughout: the premises arrive as ∀-laws
// and the goal as a product of three rewritten sizes, so a `Basic`
// pass between the installs is what lets the rewrites meet. It is
// stated once here rather than at each of the eight sites.
//
// The two characterizations it rewrites with are a pair, and the second
// of them lives with the equations above beside the first rather than here:
// the difficulty it settles — that they OVERLAP at &0, where a value is
// fixed and reflected at once — is not about products, and two other
// members outside this file need it settled too.

// AbsMul — sizes multiply. Every later estimate that turns a product into
// a product of bounds passes through this.
var AbsMul = absMulThm{family.Add(registry.ProofEntry{
	Name: "AbsMul",
	Key:  "prop_6915fc6f411034d4",
	Build: family.Sections("∀x y:real. |x * y| = |x| * |y|", func(
		ctx *Script,
		headline string,
	) *GoalStackNode {
		return ctx.Theorem(headline, func(a *Argument, x, y Term) {
			v := ops(a.Ctx())
			zero := v.Lit(0)
			negX, negY := v.Negate(x), v.Negate(y)
			product := v.Product(x, y)

			// Nothing is unfolded here. Each leaf knows the sign of x, of
			// y, and — once it derives it — of the product, and the two
			// characterizations rewrite all three absolute values from
			// those signs. No COND ever appears.
			a.Cases(v.Nonneg(x))
			a.When(
				"x is nonnegative",
				func(b *Argument, xNonneg Fact) {
					b.Cases(v.Nonneg(y))
					b.When(
						"and so is y, so all three sizes are their own arguments",
						func(c *Argument, yNonneg Fact) {
							c.Show(
								"a product of nonnegatives is nonnegative, so every size is fixed and the claim is an identity",
								By(
									Normalized,
									xNonneg,
									yNonneg,
									At(real_construction.LessEqMul, x, y), // &0 ≤ x·y
									At(AbsFixedIffNonneg, x),
									At(AbsFixedIffNonneg, y),
									At(AbsFixedIffNonneg, product)))
						})
					b.Otherwise(
						"y is negative, so its size flips and so does the product's",
						func(c *Argument, yNegative Fact) {
							nonposY := c.Have(
								"y is at or below &0",
								"y₀ ≤ &0",
								By(
									yNegative,
									// y ≤ &0 ∨ &0 ≤ y, whose second
									// alternative the failed guard
									// ruled out
									At(real_construction.LessEqTotal, zero, y)))
							nonposProduct := c.Have(
								"and so is the product",
								"x₀ * y₀ ≤ &0",
								By(
									Normalized,
									xNonneg,
									nonposY,
									// y ≤ &0 ⇔ &0 ≤ -y, read back
									// the way LessEqMul needs it
									At(real_order_ring.NegNonnegativeIffNonpositive, y),
									// &0 ≤ x·(-y)
									At(real_construction.LessEqMul, x, negY),
									// x·(-y) = -(x·y), which carries
									// that bound onto the product
									At(real_ring.MulRightNeg, x, y),
									At(real_order_ring.NegNonnegativeIffNonpositive, product)))
							c.Show(
								"so both flipped sizes are negations, and the two negations are the same term",
								By(
									Normalized,
									xNonneg,
									nonposY,
									nonposProduct,
									At(AbsFixedIffNonneg, x),
									At(AbsNegatedIffNonpos, y),
									At(AbsNegatedIffNonpos, product),
									At(real_ring.MulRightNeg, x, y)))
						})
				})
			a.Otherwise(
				"x is negative",
				func(b *Argument, xNegative Fact) {
					nonposX := b.Have(
						"x is at or below &0",
						"x₀ ≤ &0",
						By(xNegative, At(real_construction.LessEqTotal, zero, x)))
					b.Cases(v.Nonneg(y))
					b.When(
						"y is nonnegative, so the product flips — the mirror "+
							"of the leaf above, with the negation on the left",
						func(c *Argument, yNonneg Fact) {
							nonposProduct := c.Have(
								"the product is at or below &0",
								"x₀ * y₀ ≤ &0",
								By(
									Normalized,
									nonposX,
									yNonneg,
									At(real_order_ring.NegNonnegativeIffNonpositive, x), // &0 ≤ -x
									At(real_construction.LessEqMul, negX, y),            // &0 ≤ (-x)·y
									At(real_ring.MulLeftNeg, x, y),                      // (-x)·y = -(x·y)
									At(real_order_ring.NegNonnegativeIffNonpositive, product)))
							c.Show(
								"so both flipped sizes are negations, and the two negations are the same term",
								By(
									Normalized,
									nonposX,
									yNonneg,
									nonposProduct,
									At(AbsNegatedIffNonpos, x),
									At(AbsFixedIffNonneg, y),
									At(AbsNegatedIffNonpos, product),
									At(real_ring.MulLeftNeg, x, y)))
						})
					b.Otherwise(
						"y is negative too, so both sizes flip and the product's does not",
						func(c *Argument, yNegative Fact) {
							nonposY := c.Have(
								"y is at or below &0",
								"y₀ ≤ &0",
								By(yNegative, At(real_construction.LessEqTotal, zero, y)))
							nonnegProduct := c.Have(
								"but their product is at or above it",
								"&0 ≤ x₀ * y₀",
								By(
									Normalized,
									nonposX,
									nonposY,
									At(real_order_ring.NegNonnegativeIffNonpositive, x),
									At(real_order_ring.NegNonnegativeIffNonpositive, y),
									// &0 ≤ (-x)·(-y) …
									At(real_construction.LessEqMul, negX, negY),
									// … which is x·y, the two
									// negations cancelling
									At(real_ring.MulLeftNeg, x, negY),
									At(real_ring.MulRightNeg, x, y),
									At(real_ring.NegNeg, product)))
							c.Show(
								"so the two flipped sizes multiply to the product, which is its own size",
								By(
									Normalized,
									nonposX,
									nonposY,
									nonnegProduct,
									At(AbsNegatedIffNonpos, x),
									At(AbsNegatedIffNonpos, y),
									At(AbsFixedIffNonneg, product),
									At(real_ring.MulLeftNeg, x, negY),
									At(real_ring.MulRightNeg, x, y),
									At(real_ring.NegNeg, product)))
						})
				})
		})
	}),
})}

// ---------------------------------------------------------------------------
// README movement 7
// ---------------------------------------------------------------------------
//
// README movement 7: a bound on a size, read as a two-sided bound on the
// value. Movement 1's unconditional one-sided bounds stand above;
// the two equivalences here turn a size bound into an interval and back,
// and the triangle inequality — this movement's summit — is what
// `AbsBounds` is for: it is the first member to need both of that
// equivalence's directions in one argument.
//
// The two equivalences are the same argument at two strengths. What
// separates them is only the algebra between the bound as stated and
// the bound the size argument produces: `AbsBounds` crosses a negation,
// `AbsBetween` crosses a negation and a subtraction. No member here
// splits on the case definition's guard: the equivalences settle it
// once, and `AbsTriangle`, built on them, never reaches the definition.
//
// The equivalences' four leaves close with `By(Normalized, …)`; the
// rewrite ladders below them close with a bare `Cite`, having already
// put their goal in the cited law's shape. The premise lists are
// complete without the shaping — what it adds is the clause reduction
// that lets `Basic` settle the leaf, and without it those leaves fall
// through to the refuter and mint a key the argument does not need.
// The triangle inequality asks for no shaping at any of its leaves.

// AbsBounds — a size bound is a two-sided bound. This is the form
// every estimate above this chapter reaches for: an argument that has
// produced `|x| ≤ k` wants the two inequalities separately, and an
// argument that has bracketed x wants the single size statement back.
//
// The proof is the same pair of bounds read in both directions.
// `|x| ≤ k` says exactly that k bounds both x and -x — forwards because
// the size dominates each of them, backwards because the size IS one of
// them — and the statement's lower bound `-k ≤ x` is the second of
// those two with the negation moved to the other side.
var AbsBounds = absBoundsThm{family.Add(registry.ProofEntry{
	Name: "AbsBounds",
	Key:  "prop_dbbdf068de32dd43",
	Build: family.Theorem("∀x k:real. |x| ≤ k ⇔ -k ≤ x ∧ x ≤ k", func(a *Argument, x, k Term) {
		v := ops(a.Ctx())
		negX, negK, size := v.Negate(x), v.Negate(k), v.Size(x)

		// Both directions cross between the statement's lower bound and
		// the bound the size argument produces, so the crossing is
		// stated once, before the split.
		flip := a.Have(
			"the lower bound on x is an upper bound on -x",
			"-x₀ ≤ k₀ ⇔ -k₀ ≤ x₀",
			By(
				// -x ≤ --k ⇔ -k ≤ x
				At(real_order_ring.LessEqNeg2, x, negK),
				real_ring.NegNeg))

		a.Iff()
		a.Forward(
			"the size dominates x and -x alike, so k bounds both",
			func(b *Argument, sizeBound Fact) {
				above := b.Have(
					"x never exceeds its own size, which k bounds",
					"x₀ ≤ k₀",
					By(
						sizeBound,
						At(AbsDominates, x), // x ≤ |x|
						At(real_construction.LessEqTrans, x, size, k))) // x ≤ |x| ≤ k
				below := b.Have(
					"neither does -x, whose size is the same one",
					"-x₀ ≤ k₀",
					By(
						Normalized,
						sizeBound,
						At(AbsDominates, negX), // -x ≤ |-x|
						At(AbsEven, x),         // |-x| = |x|
						At(real_construction.LessEqTrans, negX, size, k))) // -x ≤ |x| ≤ k
				b.Show(
					"and the bound on -x is the statement's lower bound",
					By(flip, above, below))
			})
		a.Backward(
			"k bounds x and -x, and the size is one of them",
			func(b *Argument, bounds Fact) {
				above := b.Have(
					"k bounds x — the right-hand conjunct as it stands",
					"x₀ ≤ k₀",
					By(bounds))
				below := b.Have(
					"and it bounds -x, which is the left-hand conjunct flipped",
					"-x₀ ≤ k₀",
					By(bounds, flip))
				// With both values bounded the guard is irrelevant:
				// the COND takes one of them whichever way it goes.
				b.Do(Unfold(RealAbsDef))
				b.Show(
					"|x| is x or -x, and k is above both",
					By(above, below))
			})
	}),
})}

// AbsBetween — y lies within d of x exactly when it lies in the open
// interval of radius d around x. This is the same statement as
// AbsBounds one order relation over and applied to a difference, which
// is the shape every metric estimate is actually stated in, and the
// reason `&0 < d` rides along on the right: it is free (a size is never
// negative, so a size strictly below d puts &0 there too) and a
// consumer that has the interval usually needs it.
//
// It re-runs AbsBounds' argument rather than citing it: the layer below
// carries nothing that transports a non-strict equivalence across to the
// strict order, so the sibling's ⇔ is unusable here even though the two
// proofs are the same shape. That shape is — the size dominates the gap
// `y - x` and its reflection, and is one of them — so what is left is
// the translation between a bound on the gap and the interval's two
// ends. The right end is that bound with `real_order_ring.LessThanSubAddRight`
// applied and its sum commuted; the left end is the same law once the
// reflection has been read backwards through `real_ring.NegSub`. Those
// two translations, stated first, are the member's only algebra.
var AbsBetween = absBetweenThm{family.Add(registry.ProofEntry{
	Name: "AbsBetween",
	Key:  "prop_32dfa722cba30d3f",
	Build: family.Theorem("∀x y d:real. |y - x| < d ⇔ x - d < y ∧ y < x + d ∧ &0 < d", func(
		a *Argument,
		x, y, d Term,
	) {
		v := ops(a.Ctx())
		gap := v.Diff(y, x)     // y - x
		negGap := v.Negate(gap) // -(y - x)
		size := v.Size(gap)     // |y - x|

		// The two translations. Each is proved by REWRITING its claim
		// into the shape of `LessThanSubAddRight`, whose bare cite then
		// closes it; handing the rewriting equations to a closer instead
		// makes each commutation a paramodulation step, which is the
		// one thing in either member that costs a recorded CNF key.
		// They are declared inside the translation that uses them
		// rather than at this level: hoisted, they are in scope when
		// the definition is unfolded below, where `-(y - x) = x - y`
		// also matches the argument's own facts and rewrites several
		// hypotheses at once — which replay rejects outright.
		rightEnd := a.Have(
			"the right end says the gap is below d",
			"y₀ - x₀ < d₀ ⇔ y₀ < x₀ + d₀",
			Derive(func(c *Argument) {
				comm := c.Have(
					"the right end's sum, the other way round",
					"x₀ + d₀ = d₀ + x₀",
					Cite(real_construction.AddSym))
				c.Show(
					"which leaves the sub-add law",
					comm.Rw(), // ↦ … ⇔ y₀ < d₀ + x₀
					Cite(real_order_ring.LessThanSubAddRight))
			}))
		leftEnd := a.Have(
			"the left end says the gap's reflection is below d",
			"-(y₀ - x₀) < d₀ ⇔ x₀ - d₀ < y₀",
			Derive(func(c *Argument) {
				reflected := c.Have(
					"the reflection is the gap read backwards",
					"-(y₀ - x₀) = x₀ - y₀",
					Cite(real_ring.NegSub))
				asBoundOnX := c.Have(
					"the left end, as a bound on x alone",
					"x₀ - d₀ < y₀ ⇔ x₀ < y₀ + d₀",
					Cite(real_order_ring.LessThanSubAddRight))
				comm := c.Have(
					"the left end's sum, the other way round",
					"y₀ + d₀ = d₀ + y₀",
					Cite(real_construction.AddSym))
				c.Show(
					"which leaves the same law",
					reflected.Rw(),  // ↦ x₀ - y₀ < d₀ ⇔ …
					asBoundOnX.Rw(), // ↦ … ⇔ x₀ < y₀ + d₀
					comm.Rw(),       // ↦ … ⇔ x₀ < d₀ + y₀
					Cite(real_order_ring.LessThanSubAddRight))
			}))

		a.Iff()
		a.Forward(
			"the size dominates the gap, its reflection and &0",
			func(b *Argument, sizeBound Fact) {
				above := b.Have(
					"the gap never exceeds its own size, which is below d",
					"y₀ - x₀ < d₀",
					By(
						sizeBound,
						At(AbsDominates, gap), // y - x ≤ |y - x|
						At(real_order_ring.LessEqLessThanTrans, gap, size, d)))
				below := b.Have(
					"neither does its reflection, whose size is the same one",
					"-(y₀ - x₀) < d₀",
					By(
						Normalized,
						sizeBound,
						At(AbsDominates, negGap), // -(y - x) ≤ |-(y - x)|
						At(AbsEven, gap),         // |-(y - x)| = |y - x|
						At(real_order_ring.LessEqLessThanTrans, negGap, size, d)))
				radius := b.Have(
					"and &0 is below the size, so d is positive",
					"&0 < d₀",
					By(
						sizeBound,
						At(AbsNonneg, gap), // &0 ≤ |y - x|
						At(real_order_ring.LessEqLessThanTrans, v.Lit(0), size, d)))
				b.Show(
					"the two gap bounds are the interval's ends, and d's positivity rides along",
					By(rightEnd, leftEnd, above, below, radius))
			})
		a.Backward(
			"d bounds the gap and its reflection, and the size is one of them",
			func(b *Argument, interval Fact) {
				above := b.Have(
					"the right end, as a bound on the gap",
					"y₀ - x₀ < d₀",
					By(interval, rightEnd))
				below := b.Have(
					"the left end, as a bound on its reflection",
					"-(y₀ - x₀) < d₀",
					By(interval, leftEnd))
				// Same as above: both values are bounded, so the COND
				// takes one of them whichever way the guard goes.
				b.Do(Unfold(RealAbsDef))
				b.Show(
					"|y - x| is one of the two, and d is above both",
					By(above, below))
			})
	}),
})}

// NonzeroNear — a real closer to a than |a| is not 0. By AbsBetween, b
// lies in the window of radius |a| about a, which is (0, 2a) when a is
// nonnegative and (2a, 0) when it is negative; neither holds 0.
var NonzeroNear = nonzeroNearThm{family.Add(registry.ProofEntry{
	Name: "NonzeroNear",
	Key:  "prop_39e508ae5853bb79",
	Build: family.Theorem(Statement{
		Binders: "∀a b:real.",
		Hypotheses: []string{
			"|a - b| < |a|",
		},
		Conclusion: "b ≠ &0",
	}, func(arg *Argument, a, b *Expr[Real], closer Fact) {
		window := AbsBetween.At(b, a, arg.TermAs[Real]("|a|"))
		arg.Cases(arg.Term("&0 ≤ a"))
		arg.When(
			"for a ≥ 0 the window about a is (0, 2a)",
			func(c *Argument, nonneg Fact) {
				c.Show(
					"so b > 0",
					ByArith(nonneg, closer, window, AbsFixedIffNonneg.At(a)))
			})
		arg.Otherwise(
			"for a < 0 the window about a is (2a, 0)",
			func(c *Argument, negative Fact) {
				nonpos := c.Have(
					"a is at most 0",
					"a ≤ &0",
					ByArith(negative))
				c.Show(
					"so b < 0",
					ByArith(negative, nonpos, closer, window, AbsNegatedIffNonpos.At(a)))
			})
	}),
})}

// AbsTriangle — the size of a sum is at most the sum of the sizes. This
// is the estimate every later analytic argument is assembled from: it
// is what lets a quantity be broken into pieces and bounded piece by
// piece.
//
// The proof is `AbsBounds` read in both of its directions, which is the
// return on having stated that equivalence as one theorem. Read forwards
// at a value and its OWN size, it says that |t| brackets t — and the
// bound it asks for in order to say so, |t| ≤ |t|, is reflexivity, so a
// size brackets its own value for nothing. Two such brackets then add
// end by end, leaving x + y bracketed by ±(|x| + |y|); only the lower
// end costs any algebra, the negation having to be distributed over the
// sum before the bracket's two ends are built from the same term. Read
// backwards, a bracket by ±(|x| + |y|) IS a size bound on x + y, and
// that is the statement.
var AbsTriangle = absTriangleThm{family.Add(registry.ProofEntry{
	Name: "AbsTriangle",
	Key:  "prop_517c5f843ae2b9d0",
	Build: family.Theorem("∀x y:real. |x + y| ≤ |x| + |y|", func(a *Argument, x, y Term) {
		v := ops(a.Ctx())
		sizeX, sizeY := v.Size(x), v.Size(y) // |x|, |y|
		sum := v.Sum(x, y)                   // x + y
		sizeSum := v.Sum(sizeX, sizeY)       // |x| + |y|

		bracketX := a.Have(
			"|x| brackets x, the bound it asks for being |x| ≤ |x|",
			"-|x₀| ≤ x₀ ∧ x₀ ≤ |x₀|",
			By(
				At(AbsBounds, x, sizeX), // |x| ≤ |x| ⇔ -|x| ≤ x ∧ x ≤ |x|
				real_order_ring.LessEqRefl))
		bracketY := a.Have(
			"and |y| brackets y for the same reason",
			"-|y₀| ≤ y₀ ∧ y₀ ≤ |y₀|",
			By(At(AbsBounds, y, sizeY), real_order_ring.LessEqRefl))

		// Two lower ends add to -|x| + -|y|, while the end the claim
		// wants is the negation of the sum, so the two have to be put in
		// the same terms first. That is a REWRITE: as a premise the same
		// equation reaches the closer only as a paramodulation step, and
		// costs a recorded key. (Member level is safe here, unlike
		// AbsBetween's translations above: nothing in this proof unfolds,
		// so the equation has no argument facts to catch.)
		distributed := a.Have(
			"the sum of sizes, negated one summand at a time",
			"-(|x₀| + |y₀|) = -|x₀| + -|y₀|",
			Cite(real_ring.NegAdd))
		lower := a.Have(
			"with both ends in the same terms, the lower ones add",
			"-(|x₀| + |y₀|) ≤ x₀ + y₀",
			distributed.Rw(), // ↦ -|x| + -|y| ≤ x + y
			By(
				bracketX,
				bracketY,
				// -|x| ≤ x ∧ -|y| ≤ y ⇒ -|x| + -|y| ≤ x + y
				At(real_order_ring.LessEqAdd2, v.Negate(sizeX), x, v.Negate(sizeY), y)))
		upper := a.Have(
			"the upper ends add with nothing in the way",
			"x₀ + y₀ ≤ |x₀| + |y₀|",
			By(
				bracketX,
				bracketY,
				// x ≤ |x| ∧ y ≤ |y| ⇒ x + y ≤ |x| + |y|
				At(real_order_ring.LessEqAdd2, x, sizeX, y, sizeY)))

		a.Show(
			"and a bracket by ±(|x| + |y|) is a size bound on the sum",
			By(
				lower,
				upper,
				// |x + y| ≤ |x| + |y| ⇔ -(|x| + |y|) ≤ x + y ∧ x + y ≤ |x| + |y|
				At(AbsBounds, sum, sizeSum)))
	}),
})}

// AbsReverseTriangle — sizes differ by at most the size of the
// difference. The triangle inequality at x = (x − y) + y and at
// y = (y − x) + x, with |y − x| = |x − y|, bounds |x| − |y| above and
// below by |x − y|, and that bracket is the size bound.
var AbsReverseTriangle = absReverseTriangleThm{family.Add(registry.ProofEntry{
	Name: "AbsReverseTriangle",
	Key:  "prop_6862648c9a7fdea5",
	Build: family.Theorem("∀x y:real. ||x| - |y|| ≤ |x - y|", func(a *Argument, x, y *Expr[Real]) {
		both := a.Have(
			"the triangle inequality at x = (x − y) + y and at y = (y − x) + x",
			"|x| ≤ |x - y| + |y| ∧ |y| ≤ |x - y| + |x|",
			ByArith(
				AbsTriangle.At(a.TermAs[Real]("x - y"), y),
				AbsTriangle.At(a.TermAs[Real]("y - x"), x),
				AbsEven.At(a.TermAs[Real]("x - y"))))
		a.Show(
			"so |x| − |y| lies between −|x − y| and |x − y|",
			ByArith(both, AbsBounds.At(a.TermAs[Real]("|x| - |y|"), a.TermAs[Real]("|x - y|"))))
	}),
})}

// AbsTriangleSub — the triangle inequality for a difference: x − y is
// x + (−y), and |−y| = |y|.
var AbsTriangleSub = absTriangleSubThm{family.Add(registry.ProofEntry{
	Name: "AbsTriangleSub",
	Key:  "prop_284990e75b4df05f",
	Build: family.Theorem("∀x y:real. |x - y| ≤ |x| + |y|", func(a *Argument, x, y *Expr[Real]) {
		a.Show(
			"x − y is x + (−y), and |−y| = |y|",
			By(
				Normalized,
				real_ring.RealSubDef.At(x, y),
				AbsTriangle.At(x, a.TermAs[Real]("-y")),
				AbsEven.At(y)),
		)
	}),
})}

// AbsSubComm — the distance between two reals reads the same both ways:
// x − y is the negative of y − x, and |·| forgets the sign.
var AbsSubComm = absSubCommThm{family.Add(registry.ProofEntry{
	Name: "AbsSubComm",
	Key:  "prop_635e607f34cfed63",
	Build: family.Theorem("∀x y:real. |x - y| = |y - x|", func(a *Argument, x, y *Expr[Real]) {
		negated := a.Have(
			"x − y is the negative of y − x",
			"x - y = -(y - x)",
			ByArith(Raw),
		)
		a.Show(
			"and |·| forgets the sign",
			By(Normalized, negated, AbsEven.At(a.TermAs[Real]("y - x"))),
		)
	}),
})}

// AbsQuadraticBound — one plus the square bounds the size: the squares of
// x + 1 and x − 1 are nonnegative, so 1 + x·x lies above x and −x.
var AbsQuadraticBound = absQuadraticBoundThm{family.Add(registry.ProofEntry{
	Name: "AbsQuadraticBound",
	Key:  "prop_c8d30b6af218bf56",
	Build: family.Theorem("∀x:real. |x| ≤ &1 + x * x", func(a *Argument, x *Expr[Real]) {
		square := real_order_ring.SquareNonneg.At(x)
		lower := a.Have(
			"1 + x·x lies above −x, as (x + 1)·(x + 1) ≥ 0",
			"-(&1 + x * x) ≤ x",
			ByArith(square, real_order_ring.SquareNonneg.At(a.TermAs[Real]("x + &1"))))
		upper := a.Have(
			"and above x, as (x − 1)·(x − 1) ≥ 0",
			"x ≤ &1 + x * x",
			ByArith(square, real_order_ring.SquareNonneg.At(a.TermAs[Real]("x - &1"))))
		a.Show(
			"a two-sided bound is a size bound",
			By(lower, upper, AbsBounds.At(x, a.TermAs[Real]("&1 + x * x"))))
	}),
})}

// ---------------------------------------------------------------------------
// README movement 4
// ---------------------------------------------------------------------------
//
// README movement 4: the sign on its own, before it is paired with the
// size. Its definition `sgn x = COND(&0 < x, &1, COND(x < &0, -&1, &0))`
// is two nested guards on the strict order, and these three members are
// everything those guards say when nothing else is assumed — which values
// they can produce, what they produce at &0, and what negating the
// argument does to them.
//
// None of the three splits into cases, which is worth saying because
// the shape invites it, and each avoids it differently: the range law
// reads off what the reduced guards already offer, without deciding
// either; the value at &0 decides both at once, the two guards asking
// the same comparison there; and oddness rewrites the guards until the
// two sides of the equation test the same conditions. A statement
// ABOUT a pair of guards need not be a case analysis OF them.

// SgnTrichotomy — the sign takes three values and no others. It lets a
// consumer treat the sign as a three-valued quantity, and reason by
// cases on which value it is, without reopening the definition.
//
// Nothing outside the definition is needed, and nothing has to be
// decided. Reduced, the guards offer `&1`, `-&1` and `&0` on their
// three branches, and those are exactly the three values the statement
// lists — so the whole proof is the reduction, with no order fact to
// supply and no branch to prefer.
var SgnTrichotomy = sgnTrichotomyThm{family.Add(registry.ProofEntry{
	Name: "SgnTrichotomy",
	Key:  "prop_b4278a85cc7d58ed",
	// The point is never named — the reason is the same at every one —
	// but it must still be fixed, since the closer works inside no
	// quantifier.
	Build: family.Theorem("∀x:real. sgn(x) = -&1 ∨ sgn(x) = &0 ∨ sgn(x) = &1", func(
		a *Argument,
		x Term,
	) {
		a.Do(Unfold(RealSgnDef))
		a.Show(
			"each branch the guards can take is one of the three values listed",
			// The guards are not decided, only replaced by the
			// implications they name.
			CondRewrite(),
			Basic())
	}),
})}

// SgnOfZero — &0 has the sign the definition keeps for the arguments
// neither guard claims.
//
// One order fact settles it, and the reason is that at this argument
// the two nested guards are the SAME test: the outer asks whether &0 is
// strictly below itself, and the inner — `x < &0` read at `x = &0` — is
// that same comparison again. Failing it once therefore sends both
// CONDs to their last branch together. That is why the value is taken
// directly from the definition rather than by eliminating the other two
// from SgnTrichotomy: ruling out `&1` and `-&1` separately is more work
// than deciding the one comparison both guards turn on.
var SgnOfZero = sgnOfZeroThm{family.Add(registry.ProofEntry{
	Name: "SgnOfZero",
	Key:  "prop_5c9517ac1a31e51d",
	Build: family.Theorem("sgn(&0) = &0", func(a *Argument) {
		a.Do(Unfold(RealSgnDef))
		a.Show(
			"the comparison both guards ask is &0 < &0, which fails",
			By(real_order_ring.LessThanIrrefl))
	}),
})}

// SgnOdd — the sign is odd, the mirror of the size being even. Between
// them the pair says what negation does to the polar decomposition: it
// leaves the magnitude alone and reverses the direction.
//
// No case analysis, because the guards can be made to agree. The left
// side's are `&0 < -x` and `-x < &0`; the two sign transfers restate
// them as `x < &0` and `&0 < x`, which are the right side's own guards
// with their roles exchanged. Both sides then turn on the same pair of
// conditions, and on three of the four combinations their values agree
// outright or after one identity: with `x < &0` alone the left takes
// `&1` and the right `--&1`; with `&0 < x` alone both give `-&1`; with
// neither, the left takes `&0` and the right `-&0`.
//
// The exchange of roles is what makes asymmetry necessary, and it is
// the whole of what asymmetry does here. The fourth combination — both
// conditions at once — is the one the two sides would disagree on, and
// it is also the one the order forbids; excluding it is the last thing
// the equation needs.
var SgnOdd = sgnOddThm{family.Add(registry.ProofEntry{
	Name: "SgnOdd",
	Key:  "prop_fc500d8861c2554c",
	Build: family.Theorem("∀x:real. sgn(-x) = -sgn(x)", func(a *Argument, x Term) {
		v := ops(a.Ctx())
		zero, one := v.Lit(0), v.Lit(1)

		a.Do(
			Unfold(RealSgnDef),
			// ↦ the negated argument's guards, restated at x: `&0 < -x`
			// becomes `x < &0`, and `-x < &0` becomes `&0 < x`.
			Simp(Fwd(real_order_ring.NegPositiveIffNegative), Fwd(real_order_ring.NegNegativeIffPositive)),
		)
		a.Show(
			"both sides now turn on the same two conditions, and "+
				"branch by branch their values are negatives of each other",
			By(
				// ¬(&0 < x ∧ x < &0) — the two conditions exclude each
				// other, which is the branch neither side can take.
				At(real_order_ring.LessThanAsym, zero, x),
				At(real_ring.NegNeg, one), // --&1 = &1
				real_ring.NegZero,         // -&0 = &0
			))
	}),
})}

// ---------------------------------------------------------------------------
// README movements 5 and 6
// ---------------------------------------------------------------------------
//
// README movements 5 and 6: the polar decomposition, and what
// multiplication, inversion and division do to the pair.
//
// The two movements share a file because they share an argument. The
// sign is fixed by two questions about its argument, `&0 < x` and
// `x < &0`, so any goal still mentioning a sign is a goal about which
// region its argument falls in — and the only way past that is to say,
// once, what the sign IS in terms of the size. Saying it is what the
// two polar members do, and they say the same thing twice:
// `SgnMulSelfIsAbs` as a product, `SgnEqSelfDivAbs` as a quotient.
//
// So exactly those two decide regions and nothing else here does. They
// have to: the size asks one nonstrict question and the sign two nested
// strict ones, and no rewriting aligns a nonstrict guard with a strict
// pair. Both peel the three regions in the order the definition nests
// its guards, letting the failed guards accumulate as named facts so
// the last case can say what it is — the region left over when neither
// question is answered yes. Read them as one proof told twice; the
// second is the first divided through by the size.
//
// Everything else is a calculation, and is one BECAUSE those two
// exist. `SgnMul` and `SgnDiv` restate every sign as a value over its
// size and are then left rearranging a single product; `AbsInv`,
// `AbsDiv` and `SgnPreservedByInv` never involve a sign and a size at
// once, so no region ever has to be decided in them.
//
// A marker convention the file uses throughout, stated here once. A
// `Simp` rule carries `Fwd` or `Flipped` naming the direction against
// the law's CANONICAL orientation, which is not always the reading of
// its headline; a set can therefore look mixed while firing one way,
// and one law can carry opposite markers at two sites that rewrite in
// opposite directions. Each site below says only which markers are
// forced there and how a wrong one shows up.

// AbsInv — inversion commutes with the size.
//
// To learn what the inverse of `|x|` is, exhibit something that
// multiplies it to &1. `|x⁻¹|` does: multiplied against `|x|` it is the
// size of `x · x⁻¹` — which is the size of &1 — and uniqueness then has
// no room to name anything else.
//
// The exhibition needs x ≠ &0, and that is the only reason for the
// degenerate branch. There nothing is exhibited and nothing is
// computed: real_inv and real_abs each fix &0, so the two sides reach
// &0 by taking the same two steps in opposite orders.
//
// The split is not what makes the member PROVABLE — handing all six
// laws to a single `By` on the unstripped goal closes too, because the
// refuter runs the same case analysis inside its clause space. It costs
// a refute key there and none here, and it hides the exhibition, which
// is the only idea in the proof, inside a six-premise list.
var AbsInv = absInvThm{family.Add(registry.ProofEntry{
	Name: "AbsInv",
	Key:  "prop_4d6eb33962e5c88e",
	Build: family.Theorem("∀x:real. |real_inv(x)| = real_inv(|x|)", func(a *Argument, x *TermWrapper) {
		v := ops(a.Ctx())
		sizeX, sizeInvX := v.Size(x), v.Size(v.Invert(x))

		nonzero := a.Unless(
			x.Eq(v.Lit(0)),
			"x = &0 is degenerate: both functions fix &0, so both sides of the equation land there",
			Given(func(b *Argument, isZero Fact) {
				b.Show(
					"inverting &0 and sizing it commute because neither moves it",
					By(
						isZero,
						real_construction.InvZero, // real_inv(&0) = &0; the row binds nothing to ground
						AbsOfZero))                // |&0| = &0, likewise
			}))

		unit := a.Have(
			"the two sizes multiply to &1, being the size of a product that is &1",
			MakeProp(v.Product(sizeX, sizeInvX).Eq(v.Lit(1))),
			By(
				nonzero,
				// Bare: a size law fires as a rewrite here rather than
				// installing, so there is no instance for it to pick.
				AbsMul,
				// x ≠ &0 ⇒ x · x⁻¹ = &1, which is what that size is of
				At(field.MulRightInverse.Read(real_field.Field), x),
				AbsOfOne)) // |&1| = &1; the row binds nothing to ground

		a.Show(
			"and only one real multiplies |x| to &1, so uniqueness names |x⁻¹| as the inverse of |x|",
			// |x| · |x⁻¹| = &1 ⇒ real_inv(|x|) = |x⁻¹|
			By(unit, At(field.InvRightUnique.Read(real_field.Field), sizeX, sizeInvX)))
	}),
})}

// AbsDiv — division commutes with the size, which once the quotient is
// spelled out is AbsMul and AbsInv applied in turn.
//
// Both sides mention a quotient, so unfolding acts on both at once and
// leaves the size of a product against a product with an inverse.
// AbsMul splits the first, AbsInv rewrites what is left of it, and the
// two sides are then the same term — nothing is decided and no
// hypothesis is carried.
//
// So the two laws enter as RULES rather than as premises: when a
// member's whole argument is that one side rewrites into the other, the
// laws it rewrites with are rules. The premise spelling closes here
// too, and costs a refute key the rule set does not.
//
// Only AbsMul's marker is forced — reversed, it stops the set dead,
// since nothing else matches the unfolded goal. AbsInv closes either
// way, the two sides meeting at `|x| · |y|⁻¹` forward and at
// `|x| · |y⁻¹|` reversed; forward is written because it is the
// direction this argument reads in.
var AbsDiv = absDivThm{family.Add(registry.ProofEntry{
	Name: "AbsDiv",
	Key:  "prop_636ef8ca192df01a",
	// No binder parameter: `Simp` rewrites the goal under its
	// quantifiers, so a member whose whole body is a rule set never needs
	// its statement stripped. `SgnPreservedByInv` below is the same
	// shape. (A member closing on `Basic()` does need the strip — see
	// SgnTrichotomy above.)
	Build: family.Theorem("∀x y:real. |x / y| = |x| / |y|", func(a *Argument) {
		// ↦ the size of `x · y⁻¹` against `|x| · |y|⁻¹`. The chapter builds
		// no quotients, so `real_div` is unfolded by name — see vocab.go.
		a.Do(Unfold(real_field.RealDivDef))

		a.Show(
			"the size of the product splits, and the size of the "+
				"inverse inverts — which is what the other side already says",
			Simp(Fwd(AbsMul), Fwd(AbsInv)),
			TrivialNormalized())
	}),
})}

// SgnPreservedByInv — inverting a real leaves its direction untouched.
// A reciprocal points the way the number it inverts points. Unlike most
// laws about `x⁻¹` the statement carries no nonzero hypothesis, and the
// proof needs none: it never decides whether x is zero, because what it
// transfers is an equivalence between guards that holds at every real.
//
// No case analysis, because the two sides can be made to ask the same
// questions. Both are the same COND at different arguments, so it is
// enough to carry the left side's guards over to the right's, and three
// rewrites do it. The strict-BELOW question goes first, at both
// arguments at once — `t < &0` restated as `&0 < -t` — so that
// afterwards every guard in sight is a strict-above one. What is left
// on the left is then two readings of the same inverse law: `&0 < x⁻¹`
// becomes `&0 < x` outright, and `&0 < -(x⁻¹)` becomes `&0 < (-x)⁻¹`
// first, because inversion is odd, and then `&0 < -x`. Both land on the
// right side's own guards, and the two CONDs are one term.
//
// This member needs no law for the inner guard `x⁻¹ < &0 ⇔ x < &0`:
// routing that question through the negation is
// exactly what lets the strict-above law serve both of them.
//
// All three markers are forced, unlike AbsDiv's pair, but they do not
// announce a reversal the same way. Reversing either of the two
// ⇔-shaped rules leaves the set with no redex and it says so; reversing
// the equation rewrites the goal somewhere else instead, and the run
// then dies in the TrivialNormalized below — a step that is not the
// faulty one. Measured by reverting each in turn. (`InvNeg` carries the
// opposite marker in SgnEqSelfDivAbs, where the rewrite runs the other
// way; the law is the same and the sites are not.)
var SgnPreservedByInv = sgnPreservedByInvThm{family.Add(registry.ProofEntry{
	Name: "SgnPreservedByInv",
	Key:  "prop_99cf9e865d90579",
	// No binder parameter, as in AbsDiv: the rule set rewrites under the
	// statement's own quantifier, so the point is never named.
	Build: family.Theorem("∀x:real. sgn(real_inv(x)) = sgn(x)", func(a *Argument) {
		a.Do(Unfold(RealSgnDef))
		a.Show(
			"both sides now ask the same two questions of x, so the two CONDs are one term",
			// ↦ every `t < &0` restated as `&0 < -t`; then, on the left,
			// `&0 < -(x⁻¹)` ↦ `&0 < (-x)⁻¹` ↦ `&0 < -x`, and
			// `&0 < x⁻¹` ↦ `&0 < x`.
			Simp(
				Rev(real_order_ring.NegPositiveIffNegative),
				Rev(field.InvNeg.Read(real_field.Field)),
				Fwd(real_order_field.InvPos)),
			// What is left is an equation between two copies of one term.
			TrivialNormalized())
	}),
})}

// SgnMulSelfIsAbs — direction times magnitude is magnitude. Restoring
// the sign to the size recovers nothing new, because the sign is
// exactly what the size threw away.
//
// The three cases are the definition's own, and each pairs a value the
// sign takes with a face the size shows. Above &0 the sign is &1 and
// the size is the argument itself, so the product is an identity.
// Below &0 the sign is -&1 and the size is the reflected argument, so
// the product is the reflection — which is what `AbsNegatedIffNonpos`
// says outright, being the nonpositive half's characterization. At the
// one point neither guard claims, the sign is &0 and both sides
// vanish.
//
// Three regions against two faces is why the last case is the
// interesting one: it is the region the sign distinguishes and the size
// does not, where the size shows the same face as it does above &0 and
// only the sign has anything left to say.
//
// The correlation between the sign's value and the argument's position
// is the whole content, which is why the definition is unfolded rather
// than the range law cited: knowing that the sign is one of three
// values says nothing about which one goes with which face of the size.
// It is also why the argument is not shorter than it looks — the two
// functions are guarded by different tests, so the regions have to be
// decided rather than matched.
var SgnMulSelfIsAbs = sgnMulSelfIsAbsThm{family.Add(registry.ProofEntry{
	Name: "SgnMulSelfIsAbs",
	Key:  "prop_1425f46594799c9b",
	Build: family.Theorem("∀x:real. sgn(x) * x = |x|", func(a *Argument, x Term) {
		v := ops(a.Ctx())
		zero := v.Lit(0)

		a.Do(Unfold(RealSgnDef))

		notPositive := a.Unless(
			v.Positive(x),
			"above &0 the sign is &1",
			Given(func(b *Argument, positive Fact) {
				b.Show(
					"so the product is x itself, and x is one of the arguments the size fixes",
					By(
						positive,
						// |x| = x ⇔ &0 ≤ x
						At(AbsFixedIffNonneg, x),
						// &0 < x ⇒ &0 ≤ x — the guard weakened to the
						// characterization's own comparison
						At(real_order_ring.LessEqOfLessThan, zero, x),
						// Bare: `&1 * x` reduces on its own, so this law
						// fires as a rewrite and has no instance to pick.
						real_construction.MulLeftId))
			}))

		// The failed guard collapses the outer COND, leaving the sign's
		// second question standing.
		a.Do(TrivialSimplify())

		notNegative := a.Unless(
			v.Negative(x),
			"below &0 the sign is -&1",
			Given(func(b *Argument, negative Fact) {
				b.Show(
					"so the product is -x, which is the size on this half of the line",
					By(
						negative,
						// Bare, for the same reason as MulLeftId above.
						// ↦ -x.
						real_ring.NegMinusOne,
						// Bare: its subject |x| IS the goal's, so it fires as
						// a rewrite carrying |x| to -x rather than installing.
						AbsNegatedIffNonpos,
						// x < &0 ⇒ x ≤ &0, which is the side the guard gives
						At(real_order_ring.LessEqOfLessThan, x, zero)))
			}))

		// Both guards have now failed, so both CONDs are spent and the
		// sign has taken its last value.
		a.Do(TrivialSimplify())

		pinned := a.Have(
			"both questions were answered no, and trichotomy leaves nowhere else for x to be",
			"x = &0",
			By(
				notPositive,
				notNegative,
				// x = &0 ∨ x < &0 ∨ &0 < x — the two failed guards are two
				// of the three alternatives, so the first is what is left
				At(real_order_ring.LessThanTrichotomy, x, zero)))
		a.Show(
			"the sign there is &0, so the product vanishes — "+
				"and &0 is the one argument the size sends to &0 too",
			By(
				pinned,
				// Bare: `&0 * x` reduces on its own. ↦ &0.
				real_ring.MulLeftZero,
				AbsOfZero)) // |&0| = &0; the row binds nothing to ground
	}),
})}

// SgnEqSelfDivAbs — dividing by the size is what taking the sign IS.
// The quotient throws the magnitude away and keeps the direction, which
// is the polar decomposition read as a formula for the sign rather than
// as a factorization of the argument.
//
// It holds at &0 too, and for a reason that is not the general one:
// there the division never happens. The numerator annihilates the
// product before the size's inverse is looked at, so no fact about
// inverting &0 is used — the sign's own last branch is &0, and so is
// the quotient.
//
// Three regions, peeled in the order the sign's definition nests its
// guards, so the two failed guards accumulate as named facts and the
// last case can say what it is. Each region first names the face the
// size shows there and then collapses the quotient: above &0 the size
// is the argument, so the quotient is x over itself; below &0 it is the
// reflection, so the quotient carries a sign out of the inverse; at
// neither, x is pinned to &0 and the product vanishes.
//
// The case analysis is forced for the same reason it is in
// `SgnMulSelfIsAbs` above, whose peel this repeats step for step: the
// size asks one nonstrict question and the sign two nested strict ones,
// and no rewriting aligns them. The two are the same proof — this one
// divided through by the size.
var SgnEqSelfDivAbs = sgnEqSelfDivAbsThm{family.Add(registry.ProofEntry{
	Name: "SgnEqSelfDivAbs",
	Key:  "prop_d0e677633118af82",
	Build: family.Theorem("∀x:real. sgn(x) = x / |x|", func(a *Argument, x Term) {
		v := ops(a.Ctx())
		zero := v.Lit(0)

		// Both definitions open at once; the chapter builds no quotients,
		// so `real_div` is unfolded by name — see vocab.go.
		a.Do(Unfold(RealSgnDef), Unfold(real_field.RealDivDef))

		notPositive := a.Unless(
			v.Positive(x),
			"above &0 the sign is &1",
			Given(func(b *Argument, positive Fact) {
				fixed := b.Have(
					"above &0 the size is the argument itself",
					"|x| = x",
					By(
						positive,
						// |x| = x ⇔ &0 ≤ x
						At(AbsFixedIffNonneg, x),
						// &0 < x ⇒ &0 ≤ x, which is the side the guard gives
						At(real_order_ring.LessEqOfLessThan, zero, x)))
				b.Show(
					"so the quotient is x over itself, and an x strictly above &0 is invertible",
					fixed.Rw(), // ↦ x · x⁻¹
					By(
						positive,
						// &0 < x ⇒ x ≠ &0
						At(real_order_ring.NonzeroOfPositive, x),
						// x ≠ &0 ⇒ x · x⁻¹ = &1
						At(field.MulRightInverse.Read(real_field.Field), x)))
			}))

		// The failed guard collapses the outer COND, leaving the sign's
		// second question standing.
		a.Do(TrivialSimplify())

		notNegative := a.Unless(
			v.Negative(x),
			"below &0 the sign is -&1",
			Given(func(b *Argument, negative Fact) {
				reflected := b.Have(
					"below &0 the size is the reflection",
					"|x| = -x",
					By(
						negative,
						// Bare: the claim IS this characterization's left
						// side at x, so it fires onto the goal rather than
						// installing as a hypothesis.
						AbsNegatedIffNonpos,
						// x < &0 ⇒ x ≤ &0, which is the side the guard gives
						At(real_order_ring.LessEqOfLessThan, x, zero)))
				recip := b.Have(
					"an x strictly below &0 is invertible as well",
					"x * real_inv(x) = &1",
					By(
						negative,
						// x < &0 ⇒ x ≠ &0
						At(real_order_ring.NotEqualOfLessThan, x, zero),
						// x ≠ &0 ⇒ x · x⁻¹ = &1
						At(field.MulRightInverse.Read(real_field.Field), x)))
				b.Show(
					"so the quotient is x over its reflection, and the reflection's inverse hands the sign back out",
					reflected.Rw(), // ↦ x · (-x)⁻¹
					// ↦ x · -(x⁻¹), and then ↦ -(x · x⁻¹) — the negation
					// walked out past the inverse and then past the product.
					// This site rewrites InvNeg the opposite way to
					// SgnPreservedByInv's, hence the opposite marker.
					Simp(Fwd(field.InvNeg.Read(real_field.Field)), Fwd(real_ring.MulRightNeg)),
					recip.Rw(), // ↦ -&1
					By(negative))
			}))

		// Both guards have now failed, so both CONDs are spent and the
		// sign has taken its last value.
		a.Do(TrivialSimplify())

		pinned := a.Have(
			"both questions were answered no, and trichotomy leaves nowhere else for x to be",
			"x = &0",
			// x = &0 ∨ x < &0 ∨ &0 < x — the two failed guards are two of
			// the three alternatives, so the first is what is left.
			By(notPositive, notNegative, At(real_order_ring.LessThanTrichotomy, x, zero)))
		a.Show(
			"the quotient vanishes with x: the leading &0 annihilates "+
				"the product before the size's inverse is looked at",
			By(
				pinned,
				// Bare: `&0 * t` reduces on its own. ↦ &0.
				real_ring.MulLeftZero))
	}),
})}

// SgnMul — the direction of a product is the product of the directions.
//
// Nothing is decided here and nothing needs to be, because the member
// above has already restated the sign as something the ordinary algebra
// of ℝ can compute with. That restatement is used three times — once on
// the left and once on each factor of the right, at the two ends of the
// calculation below — and what it leaves is an equation between two
// products. Two further laws then distribute over those products, one
// for each thing a quotient is made of: the size of a product is the
// product of the sizes, and the inverse of a product is the product of
// the inverses. After both, the two sides hold the SAME four factors,
// `x`, `y`, `|x|⁻¹` and `|y|⁻¹`, grouped differently, and rearranging
// them is the only step in the member with any content.
//
// The calculation below is that sentence with its midpoints written as
// terms rather than left to prose: the product over the product of the
// sizes, then the four factors flat, then the same four paired off so
// each real stands beside its own reciprocal size — which is where each
// pair becomes a sign again.
//
// The rearrangement goes through the AC KIT rather than through a cite
// of ℝ's associativity and commutativity. `field.InvMul.Read(real_field.Field)` regroups
// the identical four-factor shape and gives the reason at its own leg;
// the same reason applies here unchanged.
var SgnMul = sgnMulThm{family.Add(registry.ProofEntry{
	Name: "SgnMul",
	Key:  "prop_1554d77779930500",
	Build: family.Theorem("∀x y:real. sgn(x * y) = sgn(x) * sgn(y)", func(a *Argument, x, y Term) {
		ctx := a.Ctx()
		v := ops(ctx)
		sizeX, sizeY := v.Size(x), v.Size(y)
		prod := v.Product(x, y)

		// The calculation's three midpoints, in the order it passes them:
		overSize := v.Product(prod, v.Invert(v.Product(sizeX, sizeY)))
		flat := v.Product(prod, v.Product(v.Invert(sizeX), v.Invert(sizeY)))
		paired := v.Product(v.Product(x, v.Invert(sizeX)), v.Product(y, v.Invert(sizeY)))

		// The chapter builds no quotients, so `real_div` is unfolded by name —
		// see vocab.go.
		openDivisions := Unfold(real_field.RealDivDef)

		a.Do(CalcEq(
			Leg(
				overSize,
				"the sign is its argument over its size, the size of a product "+
					"is the product of the sizes, and every division is then opened",
				Simp(Fwd(SgnEqSelfDivAbs), Fwd(AbsMul)),
				openDivisions),
			Leg(
				flat,
				"the inverse distributes over that product as well, so no inverse is left standing on a product",
				Simp(Fwd(field.InvMul.Read(real_field.Field))),
				TrivialNormalized()),
			Leg(
				paired,
				"the same four factors, regrouped so each value stands beside its own size",
				ACRegroupWith(real_construction.MulAC(ctx))),
			FinalLeg(
				"and a value over its own size is its sign, so the pairs are the two signs the claim multiplies",
				Simp(Fwd(SgnEqSelfDivAbs)),
				openDivisions),
		))
	}),
})}

// SgnDiv — and the direction of a quotient is the quotient of the
// directions. `SgnMul`'s calculation again, with one extra rung, and the
// extra rung is what dividing by a quotient costs.
//
// Here BOTH sides divide by something that is itself a quotient — the
// left by `|x|/|y|`, the right by `sgn y` — so opening every division
// leaves an inverse standing on an inverse. Distributing the outer one
// and then taking the inner one off is what puts a side into the flat
// four-factor form the rearrangement needs, and the calculation has to
// come back UP the same way afterwards, because the kit works on products
// while a sign is a quotient. That is why the ladder below descends,
// regroups once, and climbs again rather than going straight across.
//
// The four factors it regroups are `x`, `y⁻¹`, `|x|⁻¹` and `|y|`. The
// pairing it starts from puts the two values together and the two sizes
// together; the pairing it ends at puts each value beside a size, which
// is what makes each half a sign.
//
// `InvInv`'s marker is forced, and it fails in the visible way. A marker
// names the law's canonical orientation, which for `InvInv` puts the bare
// `x` on the left, so `Fwd` asks to rewrite EVERY real into its own
// double inverse; the set declines a rule with a bare variable on the
// left, and the `real_inv(real_inv(…))` the goal actually holds simply
// survives into the next step, where it is visible. `InvMul` beside it is
// forward, so the pair carries mixed markers out of necessity rather than
// by oversight.
//
// There IS a route that never mentions the size at all: `sgn(x/y)` is
// `sgn(x · y⁻¹)`, which `SgnMul` and `SgnPreservedByInv` reduce to
// `sgn x · sgn y`, leaving only the fact that a sign is its own
// inverse. That fact is a theorem in its own right,
// in this chapter's boundary and not yet built — so the shorter route
// is really the longer one with a member missing from the middle of it.
// Measured against the route below and rejected: proving it inline
// argues from the three values a sign takes, which is a case analysis
// where the calculation below has none.
var SgnDiv = sgnDivThm{family.Add(registry.ProofEntry{
	Name: "SgnDiv",
	Key:  "prop_53a5226071c2ad23",
	Build: family.Theorem("∀x y:real. sgn(x / y) = sgn(x) / sgn(y)", func(a *Argument, x, y Term) {
		ctx := a.Ctx()
		v := ops(ctx)
		sizeX, sizeY := v.Size(x), v.Size(y)

		// The calculation's four midpoints: each side of the claim with its
		// divisions opened, and each side again with the resulting inverted
		// quotient flattened. The regrouping runs between the two flat ones.
		leftOpened := v.Product(v.Product(x, v.Invert(y)), v.Invert(v.Product(sizeX, v.Invert(sizeY))))
		leftFlat := v.Product(v.Product(x, v.Invert(y)), v.Product(v.Invert(sizeX), sizeY))
		rightFlat := v.Product(v.Product(x, v.Invert(sizeX)), v.Product(v.Invert(y), sizeY))
		rightOpened := v.Product(v.Product(x, v.Invert(sizeX)), v.Invert(v.Product(y, v.Invert(sizeY))))

		// One rule pair does the flattening in both places: the outer inverse
		// distributes, and the inverse it leaves standing on an inverse comes
		// off. The rules run the same way in the second leg and the fourth —
		// what changes is which side of that leg carries the inverted
		// quotient, which is why the fourth reads as climbing back up.
		flatten := Chain(Simp(
			Fwd(field.InvMul.Read(real_field.Field)),
			Fwd(field.InvInv.Read(real_field.Field))), TrivialNormalized())
		// The chapter builds no quotients, so `real_div` is unfolded by name —
		// see vocab.go.
		openDivisions := Unfold(real_field.RealDivDef)

		a.Do(CalcEq(
			Leg(
				leftOpened,
				"the sign is its argument over its size, the size of a quotient "+
					"is the quotient of the sizes, and every division is then opened",
				Simp(Fwd(SgnEqSelfDivAbs), Fwd(AbsDiv)),
				openDivisions),
			Leg(
				leftFlat,
				"the outer inverse distributes over the size quotient, "+
					"and the inverse it leaves standing on |y| comes back off",
				flatten),
			Leg(
				rightFlat,
				"the same four factors, regrouped so each value stands beside the size it is measured against",
				ACRegroupWith(real_construction.MulAC(ctx))),
			Leg(
				rightOpened,
				"and back up: y's pair is the reciprocal of y over its "+
					"size, which is the shape a division by a sign asks for",
				flatten),
			FinalLeg(
				"leaving one value over its size divided by the other, which is one sign divided by the other",
				Simp(Fwd(SgnEqSelfDivAbs)),
				openDivisions),
		))
	}),
})}
