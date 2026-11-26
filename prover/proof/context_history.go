package proof

// context_history.go — where a fact the context no longer holds went.
//
// A refusal that says the context does not hold a fact — a guard a fact
// in hand still carries, a premise's antecedent the rung could not
// supply, an equation with nothing left to rewrite — is read as "the
// fact was never there" unless the refusal says otherwise. Often it was
// there: an earlier step rewrote the hypothesis that held it (a Simp at
// the hypothesis, an Unfold whose tidy substituted a resident equation
// into it), and the step that did so stands in the proof tree above the
// leaf. The notes here read it off the tree and name the step.

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/tactic"
)

// rewrittenAwayNote names the step at which the context last held want:
// the nearest ancestor of leaf whose goal holds a hypothesis equal to
// want in the rung's reading while its child does not, with what the
// hypothesis became there. "" when no ancestor held it, so the refusal
// says only that the context does not hold it.
func rewrittenAwayNote(leaf *GoalStackNode, want core.Term) string {
	if leaf == nil {
		return ""
	}
	same := readerOf(leaf.proofScope).resident(want)
	for child := leaf; child.parent != nil; child = child.parent {
		parent := child.parent
		idx := -1
		for i := range parent.Goal.NumHyps() {
			if same(parent.Goal.Hyp(i)) {
				idx = i
				break
			}
		}
		if idx < 0 || child.Goal.AnyHyp(same) {
			continue
		}
		became := "the step dropped it, or split it into several"
		if succ := parent.hypSuccessors(child); succ != nil {
			if succ[idx] != tactic.NoSuccessor {
				became = "it became " + ext.PrintTerm(child.Goal.Hyp(succ[idx]))
			}
		} else if added := hypsAdded(parent.Goal, child.Goal); len(added) == 1 {
			became = "it became " + ext.PrintTerm(added[0])
		}
		return fmt.Sprintf("\n  %s stood in the context until step %s rewrote it: %s",
			ext.PrintTerm(parent.Goal.Hyp(idx)), stepSpelling(parent), became)
	}
	return ""
}

// lastOccurrenceNote names the step past which t occurs nowhere in the
// goal: the nearest ancestor of leaf whose goal spells t — in its
// conclusion or in a hypothesis other than except — while its child
// does not. A rewrite that substituted a term everywhere leaves an
// equation standing with nothing left to rewrite, and this is what says
// so. "" when no ancestor spelled it.
func lastOccurrenceNote(leaf *GoalStackNode, t core.Term, except func(core.Term) bool) string {
	if leaf == nil {
		return ""
	}
	spells := func(g Prop) bool {
		if occursIn(g.Conclusion(), t) {
			return true
		}
		for i := range g.NumHyps() {
			if h := g.Hyp(i); !except(h) && occursIn(h, t) {
				return true
			}
		}
		return false
	}
	for child := leaf; child.parent != nil; child = child.parent {
		if spells(child.Goal) {
			return ""
		}
		if spells(child.parent.Goal) {
			return fmt.Sprintf("\n  %s last stood in the goal before step %s, which rewrote it away",
				ext.PrintTerm(t), stepSpelling(child.parent))
		}
	}
	return ""
}

// stepSpelling is a step as a refusal names it: the author's spelling
// where the ministep has one (an Unfold), the step's own description
// otherwise.
func stepSpelling(n *GoalStackNode) string {
	if unfold, ok := n.miniStep.(_DefExpandStep); ok {
		if unfold.site != "" {
			return fmt.Sprintf("the Unfold of %s at %s", unfold.constTerm.Name(), unfold.site)
		}
		return fmt.Sprintf("the Unfold of %s", unfold.constTerm.Name())
	}
	if simp, ok := n.miniStep.(_SimpWithStep); ok && simp.atHyp > 0 {
		return fmt.Sprintf("%q (a Simp at the hypothesis: fact.Simp or a.Simplified)", n.StepDescription())
	}
	return fmt.Sprintf("%q", n.StepDescription())
}

// hypsAdded lists the hypotheses of after that before does not hold.
func hypsAdded(before, after Prop) []core.Term {
	var added []core.Term
	for i := range after.NumHyps() {
		if h := after.Hyp(i); !goalHasHypAlpha(before, h) {
			added = append(added, h)
		}
	}
	return added
}

// occursIn reports whether sub occurs in t, up to α.
func occursIn(t, sub core.Term) bool {
	if t.AlphaEquals(sub) {
		return true
	}
	if app, ok := t.AsAppliedTerm(); ok {
		return occursIn(app.Fun(), sub) || occursIn(app.Arg(), sub)
	}
	if abs, ok := t.AsAbsTerm(); ok {
		return occursIn(abs.Body(), sub)
	}
	return false
}
