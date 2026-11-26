package proof

// closed_leaf.go — what a step refused for want of an open leaf says: the
// step that closed the last leaf, where the author wrote it when the step
// knows, and the leaf it closed. An Unfold whose tidy closes its leaf on
// contact is the common case: the step after it has nothing to act on,
// and the refusal names the Unfold rather than leaving the author to
// find the close.

import (
	"fmt"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

// lastClosedLeaf is the leaf under n a step closed last: the end of the
// rightmost path, the order in which a proof's steps close its leaves.
// nil when nothing under n was expanded.
func lastClosedLeaf(n *GoalStackNode) *GoalStackNode {
	if n == nil || n.miniStep == nil {
		return nil
	}
	for len(n.children) > 0 {
		n = n.children[len(n.children)-1]
		if n.miniStep == nil {
			return nil
		}
	}
	return n
}

// closedLeafNote is the text a "no unsolved leaves remaining" refusal on
// root appends: the step that closed the last leaf under root (with the
// step it closed an obligation of, where that step is a cite of a known
// theorem), what an Unfold's tidy found, and the leaf. Empty when root
// has no closed leaf to name.
func closedLeafNote(root *GoalStackNode) string {
	leaf := lastClosedLeaf(root)
	if leaf == nil || !leaf.Proved() {
		return ""
	}
	closer := stepSpelling(leaf)
	if _, known := leaf.miniStep.(_KnownThmStep); known && leaf.parent != nil && leaf.parent.miniStep != nil {
		closer += ", closing a leaf of " + stepSpelling(leaf.parent)
	}
	if unfold, ok := leaf.miniStep.(_DefExpandStep); ok {
		if why := unfoldClosingReason(unfold.constTerm, leaf.Goal, libraryRead(leaf.proofScope)); why != "" {
			closer += " — " + why
		}
	}
	return fmt.Sprintf("\n  the step that closed the last leaf: %s\n  the leaf it closed: %s\n"+
		"  Nothing is left for this step: drop it and the steps after it on that leaf, "+
		"or state the goal so that it is still open there.", closer, prop.PrintProp(leaf.Goal))
}

// unfoldClosingReason says how the def-expand composite closed goal on
// c: the definition's own theorem states it, the rewrite by the
// definition discharged it, or the tidy found the opened goal an
// identity — ⊤, an equation of equal sides, a conclusion a hypothesis
// states, or another identity tactic.UnfoldTidyTactic closes. Empty when
// the step no longer reproduces on goal.
func unfoldClosingReason(c ConstTerm, goal Prop, read tactic.LibraryRead) string {
	defThm := getDefThm(c)
	if defThm.IsZero() {
		return ""
	}
	if IsStronger(defThm, goal) {
		return "the definition's own theorem states the goal"
	}
	inner, _ := dispatchDefExpandRewrite(defThm, goal, read)
	if inner == nil {
		return ""
	}
	if inner.Size() < 2 {
		return "the rewrite by the definition discharged the goal"
	}
	opened := inner.ChildGoal(1)
	concl := opened.Conclusion()
	switch l, r, isEquation := ext.MatchesEQ(concl); {
	case concl.Equals(T):
		return "the opened conclusion is ⊤"
	case isEquation && l.AlphaEquals(r):
		return fmt.Sprintf("the opened conclusion %s is an equation of equal sides", ext.PrintTerm(concl))
	case opened.HasHyp(concl):
		return fmt.Sprintf("its tidy found the opened conclusion %s stated by a hypothesis", ext.PrintTerm(concl))
	}
	return fmt.Sprintf("its tidy closed the opened conclusion %s: after an unfold the tidy closes a leaf whose "+
		"conclusion is ⊤ once the basic rewrites and the connective simplification have run, whose conclusion a "+
		"hypothesis states modulo that normalization, or whose hypotheses contradict", ext.PrintTerm(concl))
}
