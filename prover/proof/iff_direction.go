/** File: iff_direction.go
 *
 * The named halves of an ⇔ split.
 *
 * An ⇔ splits two ways, and neither split's halves are interchangeable:
 *
 *   ⊢ L ⇔ R          (the GOAL split)  →  R ⊢ L   and   L ⊢ R
 *   L ⇔ R ⊢ C        (the HYP split)   →  L, R ⊢ C  and  ¬L, ¬R ⊢ C
 *
 * The tactics hand those children back in a fixed order — for the goal
 * split the BACKWARD direction comes first, which is the reverse of the
 * order a reader expects — so a surface taking `cases ...Case` makes the
 * author remember an arbitrary convention and then say in prose which
 * half they meant. The prose is unchecked, so it drifts: before this
 * surface existed the corpus had two sites whose arrow contradicted the
 * branch it labeled, eleven with no arrow at all, and emit's own label
 * generator had the two directions the wrong way round.
 *
 * So each half gets a name and its own TYPE. `Forward` and `Backward`
 * cannot be passed in each other's slot, `BothHold` and `NeitherHolds`
 * likewise, and the verb — not the author — places each where the
 * tactic wants it and writes the arrow into the label. A swapped pair
 * is a compile error, not a misleading label.
 *
 * The positional forms survive one layer down (SplitIffCases,
 * SplitHypIffCases, SplitHypIffAtCases) because emit renders a split
 * whose children did not become a Case block as a bare caseless step.
 * A chapter body never authors them — TestLintNoPositionalIffCases.
 */

package proof

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

// ---------------------------------------------------------------------------
// The goal split: ⊢ L ⇔ R
// ---------------------------------------------------------------------------

// IffForward carries the ⇒ half of an ⇔ goal — assume L, prove R.
// It is a distinct type from IffBackward so the two cannot be swapped.
type IffForward struct{ c Case }

// IffBackward carries the ⇐ half of an ⇔ goal — assume R, prove L.
type IffBackward struct{ c Case }

// Forward is the ⇒ half of an ⇔ goal: the left side is resident and the
// right side is the claim. label says what carries that implication, in
// mathematics — the arrow is written by this constructor, so it states
// the direction the verb actually runs the body on and cannot drift
// from it.
func Forward(label string, body ...Action) IffForward {
	return IffForward{c: MakeCase("⇒ "+label, body...)}
}

// Backward is the ⇐ half: the right side is resident and the left side
// is the claim. This is the half the tactic produces FIRST; the verb
// knows that, and the author does not have to.
func Backward(label string, body ...Action) IffBackward {
	return IffBackward{c: MakeCase("⇐ "+label, body...)}
}

// ---------------------------------------------------------------------------
// The hyp split: L ⇔ R ⊢ C
// ---------------------------------------------------------------------------

// IffBothHold carries the branch on which both sides of an ⇔ HYPOTHESIS
// are resident.
type IffBothHold struct{ c Case }

// IffNeitherHolds carries the branch on which both sides are negated.
type IffNeitherHolds struct{ c Case }

// BothHold is the branch where the ⇔-hypothesis's two sides are both
// true and both resident. An ⇔ in the HYPOTHESES does not split into
// directions — it splits into the two ways an equivalence can be
// satisfied — which is why this pair is named for truth and not for an
// arrow.
func BothHold(label string, body ...Action) IffBothHold {
	return IffBothHold{c: MakeCase("both: "+label, body...)}
}

// NeitherHolds is the branch where both sides are false, so both
// negations are resident.
func NeitherHolds(label string, body ...Action) IffNeitherHolds {
	return IffNeitherHolds{c: MakeCase("neither: "+label, body...)}
}

// ---------------------------------------------------------------------------
// The order tripwires
// ---------------------------------------------------------------------------
//
// Every Forward / Backward / BothHold / NeitherHolds in the corpus
// means what it says only because the tactic orders its children the
// way these checks assert. Nothing else observes that order — a change
// to it would leave every landed label quietly lying and every proof
// still green — so the steps check it on the way past, once per split,
// and a mismatch is a logical inconsistency: it panics.

// namedIffSplit is what a named ⇔ split commits: sg as the tactic made
// it, its two children in the order the halves assume (order checks
// that), or nil — the step declines — where the constructor merged the
// two into one because one subsumes the other (tactic.makeSubGoalsAt:
// `L ⊢ L ⇔ ⊥` on the goal side, `p ⇔ q, p, q ⊢ R` on the hypothesis
// side). The halves are claimed by name, and a one-child split has no
// half to give a name to; the author simplifies instead, and the
// session's `split_iff` / `split_hyp_iff` report the decline.
func namedIffSplit(sg *tactic.SubGoals, order func(*tactic.SubGoals)) *tactic.SubGoals {
	if sg == nil || sg.Size() == 1 {
		return nil
	}
	order(sg)
	return sg
}

// assertIffGoalChildOrder pins ConclIffTactic's children: child 0 is the
// ⇐ half (R ⊢ L) and child 1 is the ⇒ half (L ⊢ R).
func assertIffGoalChildOrder(p Prop, sg *tactic.SubGoals) {
	l, r, ok := ext.MatchesIFF(p.Conclusion())
	if !ok || sg.Size() != 2 {
		panic("SplitIff: expected an ⇔ conclusion split into 2 children, got " +
			prop.PrintProp(p))
	}
	back, fwd := sg.ChildGoal(0), sg.ChildGoal(1)
	if !back.Conclusion().AlphaEquals(l) || !fwd.Conclusion().AlphaEquals(r) {
		panic("SplitIff: ConclIffTactic no longer yields (⇐, ⇒) in that order — " +
			"Backward/Forward, and every label the corpus wrote through them, " +
			"name the wrong branch now.\n  goal:     " + prop.PrintProp(p) +
			"\n  child 0:  " + prop.PrintProp(back) +
			"\n  child 1:  " + prop.PrintProp(fwd))
	}
}

// assertIffHypChildOrder pins HypIffTacticAt's children for the
// ⇔-hypothesis at i: child 0 carries both sides of the split ⇔, child 1
// carries both denials.
//
// The denial is the tactic's own: it CONTRACTS a side that is already
// ¬-headed rather than stacking a second ¬, so a `¬A ⇔ ¬B` hypothesis
// puts the plain A and B on the neither-branch. Counting ¬s would
// therefore read that split backwards (eudoxus_slope.ArchMult is the corpus's
// instance), which is why this checks the sides themselves.
func assertIffHypChildOrder(p Prop, sg *tactic.SubGoals, i int) {
	if sg.Size() != 2 {
		panic("SplitHypIff: expected an ⇔ hypothesis split into 2 children, got " +
			prop.PrintProp(p))
	}
	// The tactic split the hypothesis at i as an ⇔ with distinct sides.
	left, right, ok := ext.MatchesIFF(p.Hyp(i))
	Assert(ok && !left.AlphaEquals(right))
	both, neither := sg.ChildGoal(0), sg.ChildGoal(1)
	bad := !both.HasHyp(left) || !both.HasHyp(right) ||
		!neither.HasHyp(denied(left)) || !neither.HasHyp(denied(right))
	if bad {
		panic("SplitHypIff: HypIffTactic no longer yields (both, neither) in that " +
			"order — BothHold/NeitherHolds name the wrong branch now.\n  goal:     " +
			prop.PrintProp(p) +
			"\n  child 0:  " + prop.PrintProp(both) +
			"\n  child 1:  " + prop.PrintProp(neither))
	}
}

// denied is the tactic's negation of one ⇔ side: the term under a
// leading ¬, or the term under a fresh one.
func denied(t core.Term) core.Term {
	if inner := ext.MatchesNOT(t); inner != nil {
		return inner
	}
	return ext.Not(t)
}
