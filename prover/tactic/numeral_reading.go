package tactic

import (
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/solver/omega"
)

// NumeralReadTactic reads a goal at its numerals (omega.NumeralReading)
// under policy, the conclusion and every hypothesis through the kernel's
// equation — the apply rung's numeral reading of a leaf whose context
// holds a statement up to it (the NumeralRead step in prover/proof). A
// goal whose conclusion reads ⊤, or one of whose hypotheses reads ⊥, is
// closed by the reading; otherwise one child, the goal read; nil where
// the goal spells nothing the reading reads.
func NumeralReadTactic(policy omega.ArithPolicy) Tactic {
	read := omega.NumeralReading(policy)
	return func(goal Prop) *SubGoals {
		if w := read(goal.Conclusion()); w != nil && prop.Rhs(w).Equals(T) {
			return MakeEmptySubGoals(goal, w.EqSym().EqMP(prop.DerivesTrue))
		}
		for h := range goal.HypIter() {
			if w := read(h); w != nil && prop.Rhs(w).Equals(F) {
				return MakeEmptySubGoals(goal, w.EqMP(prop.Assume(h)))
			}
		}
		return rewritePropWith(goal, read)
	}
}
