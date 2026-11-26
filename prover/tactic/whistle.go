// whistle.go — a divergence-whistle cut as the author of the step reads
// it. The drivers report a cut as a skeleton.WhistleEvent; the recorder's
// refusal, the replay harness's whistle-free failure and a session's
// `by` response all describe it through here, so the three say the same
// thing in the same words.

package tactic

import (
	"fmt"
	"strings"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
)

// WhistleCutAdvice says what a cut means for the step it cut and what
// the author changes. It follows a listing of cuts.
const WhistleCutAdvice = "A cut is a function of the goal it was made at, so every replay of the step meets it again; " +
	"the step closed on what its search had left. Give the step less to split or to rewrite: name fewer " +
	"premises, ground a quantified premise at the terms the goal needs, or prove the intermediate fact in a step of its own."

// whistleStatementRunes bounds a statement in a cut's description. A
// refused case analysis is read at the goal it was entered with, a leaf
// of the author's own step; the goal of a branch cut as divergent has
// grown by construction, and nothing bounds it.
const whistleStatementRunes = 4000

// whistleCutsListed is how many distinct cuts a listing spells out.
const whistleCutsListed = 5

// WhistleCutStatement is the statement a cut is read at, printed: the
// goal a refused case analysis was entered with, the goal a cut branch
// had reached, or the term a cut rewrite was called on.
func WhistleCutStatement(ev skeleton.WhistleEvent) string {
	switch {
	case ev.Open > 0 && ev.Entry != nil:
		return prop.PrintProp(ev.Entry)
	case ev.Goal != nil:
		return prop.PrintProp(ev.Goal)
	case ev.Term != nil:
		return ext.PrintTerm(ev.Term)
	}
	return ""
}

// clippedStatement cuts a statement at whistleStatementRunes, on a rune:
// a description travels in a session's JSON response.
func clippedStatement(statement string) string {
	runes := []rune(statement)
	if len(runes) <= whistleStatementRunes {
		return statement
	}
	return fmt.Sprintf("%s … (%d more characters)", string(runes[:whistleStatementRunes]), len(runes)-whistleStatementRunes)
}

// DescribeWhistleCut renders one cut: the step that was running, where
// the event names one (skeleton.WhistleEvent.Step), what the driver
// refused, and the statement it refused it at (WhistleCutStatement, cut
// at whistleStatementRunes), indented under the line.
func DescribeWhistleCut(ev skeleton.WhistleEvent) string {
	var what string
	switch {
	case ev.Open > 0:
		what = fmt.Sprintf("a case analysis reached %d open leaves, its breadth backstop, and was refused whole "+
			"(%s, depth %d) — the goal it was entered with:", ev.Open, ev.Driver, ev.Depth)
	case ev.Goal != nil:
		what = fmt.Sprintf("a simplification branch was cut at depth %d, past the backstop of %d, where its goal "+
			"re-contains one it came from (%s) — the goal at the cut:", ev.Depth, ev.Budget, ev.Driver)
	case ev.Driver == "DeepRewriteWhistled":
		what = fmt.Sprintf("a rewrite by a rule set was cut as divergent at its firing %d "+
			"(%s, budget %d) — the term it was called on:", ev.Depth, ev.Driver, ev.Budget)
	case ev.Term != nil:
		what = fmt.Sprintf("a rewrite chain was cut after %d step(s), past the backstop of %d, where its result "+
			"re-contains an earlier one (%s) — the term at the cut:", ev.Depth, ev.Budget, ev.Driver)
	default:
		what = fmt.Sprintf("a search was cut at depth %d, budget %d (%s)", ev.Depth, ev.Budget, ev.Driver)
	}
	if ev.Step != "" {
		what = "in " + ev.Step + ": " + what
	}
	statement := clippedStatement(WhistleCutStatement(ev))
	if statement == "" {
		return what
	}
	return what + "\n      " + strings.ReplaceAll(statement, "\n", "\n      ")
}

// ListWhistleCuts numbers described cuts on lines of their own under the
// sentence that introduces them: one entry for each distinct
// description, in order of first report, with the number of times it
// was reported when that is more than one — a ladder's probe and its
// closing rung report the same cut — and the first whistleCutsListed
// entries only, the rest counted.
func ListWhistleCuts(described []string) string {
	var distinct []string
	times := map[string]int{}
	for _, cut := range described {
		if times[cut] == 0 {
			distinct = append(distinct, cut)
		}
		times[cut]++
	}
	var b strings.Builder
	for i, cut := range distinct {
		if i == whistleCutsListed {
			fmt.Fprintf(&b, "\n  and %d more cut(s) elsewhere, not listed", len(distinct)-whistleCutsListed)
			break
		}
		fmt.Fprintf(&b, "\n  %d. ", i+1)
		if n := times[cut]; n > 1 {
			fmt.Fprintf(&b, "(%d times) ", n)
		}
		b.WriteString(cut)
	}
	return b.String()
}
