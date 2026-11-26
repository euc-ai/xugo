package proof

import (
	"fmt"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
)

// ApplyResident closes the focus as an instance of a resident
// hypothesis: the apply rung (apply_close.go, Lean's `apply h;
// assumption`) reads the context alone — no named premise, no closer, no
// CNF key; the steps it commits are the kernel's. A resident conjunction
// is split first, so each of its conjuncts is a head. The rung is tried
// on the goal as it stands and again after each leading ∀ is fixed and
// each leading antecedent assumed (and split), so a goal that is the law
// at fresh terms and a goal the section has opened alike meet the law's
// own telescope.
// A door whose proof makes a law resident and leaves the goal that law
// (a structure's Axiom, a definition's Conjunct: the predicate unfolded
// at the hypothesis) closes with it. It panics, naming the nearest miss,
// when no resident hypothesis applies.
func ApplyResident() Action { return _applyResidentAction{} }

type _applyResidentAction struct{}

func (_applyResidentAction) applyAction(s *Script, root *GoalStackNode) {
	leaf := root.unsolvedLeaf(0)
	if leaf == nil {
		panic("ApplyResident: no unsolved leaf remains" + closedLeafNote(root))
	}
	for {
		for leaf.runStep(_SplitHypConj{}) {
			leaf = root.unsolvedLeaf(0)
		}
		closed, diag := applyClose(root, new([]*GoalStackNode), nil, rungOpts{depth: antecedentApplies, plain: true})
		if closed {
			return
		}
		concl := leaf.Goal.Conclusion()
		switch {
		case !ext.MatchesFORALL(concl).IsZero():
			s.Do(leaf, StripQuant())
		case isImplication(concl):
			s.Do(leaf, StripImp())
		default:
			if diag == "" {
				diag = "no resident hypothesis concludes the goal"
			}
			panic(fmt.Sprintf("ApplyResident: %s\n  leaf: %s", diag, prop.PrintProp(leaf.Goal)))
		}
		leaf = root.unsolvedLeaf(0)
	}
}

// isImplication reports whether t is an implication, its antecedent and
// consequent apart.
func isImplication(t core.Term) bool {
	ante, concl, ok := ext.MatchesIMPLY(t)
	return ok && !ante.AlphaEquals(concl)
}
