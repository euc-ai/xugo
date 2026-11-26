// whistle_gate_test.go — the whistle-free check of a replay: no stored
// proof may meet a divergence-whistle backstop (ext/skeleton,
// prover/tactic openLeafBackstop). A cut does not stop a search, which
// goes on with what is left and may close, so a member can record its
// rows past one; a replay is held to none, by the recorder at the write
// (verifyRecordedMember) and by TestReplayAll.

package gates

import (
	"fmt"
	"strings"
	"testing"

	"github.com/stretchr/testify/require"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve/testenv"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
)

// _WhistleGate collects the cuts fired while it is open, each described
// where it fired. One is open at a time: it installs the process's
// whistle hook and restores the one it found.
type _WhistleGate struct {
	fires0 int64
	prev   func(skeleton.WhistleEvent)
	cuts   []string
}

// openWhistleGate opens the gate. A cut is described by its driver's
// refusal and the statement it was made at (tactic.DescribeWhistleCut),
// under the By that was running where one was (the event's Step: the
// By's premises and its file:line), and with the chapter line that was
// running — the hook runs on the goroutine that reported the cut, whose
// stack holds the member's build, so the verb that applied the step is
// named for a step of any kind.
func openWhistleGate() *_WhistleGate {
	g := &_WhistleGate{fires0: skeleton.WhistleFires(), prev: skeleton.OnWhistleFire}
	skeleton.OnWhistleFire = func(ev skeleton.WhistleEvent) {
		cut := tactic.DescribeWhistleCut(ev)
		if site := registry.ChapterSite(); site != "" {
			cut += "\n     chapter line: " + site
		}
		g.cuts = append(g.cuts, cut)
	}
	return g
}

// close restores the hook the gate found.
func (g *_WhistleGate) close() { skeleton.OnWhistleFire = g.prev }

// fired is the number of cuts since the gate opened and, when there
// were any, their listing with what an author does about them — text
// that follows "… fired N time(s):" and ends its line.
func (g *_WhistleGate) fired() (int64, string) {
	n := skeleton.WhistleFires() - g.fires0
	if n == 0 {
		return 0, ""
	}
	return n, tactic.ListWhistleCuts(g.cuts) + "\n  " + tactic.WhistleCutAdvice + "\n"
}

// nineEquivalences is `(P0(x) ∨ … ∨ P8(x)) ⇒ (Q0(x) ∨ … ∨ Q8(x))` under
// the nine hypotheses Pᵢ(x) ⇔ Qᵢ(x) over distinct predicate variables:
// nine case splits no rule decides, 2⁹ = 512 open leaves under Basic's
// case analysis — the breadth backstop.
func nineEquivalences() (core.Prop, []core.Term) {
	pred := core.MakeFun(core.TypeA(), core.TypeBool())
	x := ext.Var("x", core.TypeA())
	var hyps []core.Term
	var ps, qs *ext.TermWrapper
	for i := range 9 {
		p := ext.Var(core.TermName(fmt.Sprintf("P%d", i)), pred).Apply(x)
		q := ext.Var(core.TermName(fmt.Sprintf("Q%d", i)), pred).Apply(x)
		hyps = append(hyps, ext.Apply(core.IFF(), p.Core(), q.Core()))
		if i == 0 {
			ps, qs = p, q
			continue
		}
		ps, qs = ps.Or(p), qs.Or(q)
	}
	return prop.MakeProp(ps.Imply(qs).Core(), hyps...), hyps
}

// TestWhistleGate_NamesTheByAndTheGoal: a By that fires the whistle and
// closes all the same is refused in words an author can act on — the By
// and the file:line it was written at, the statement of the goal whose
// case analysis was refused, the chapter line that was applying the
// step, and what to change. The goal is the leaf as the ladder's first
// rung conditioned it: the implication's antecedent stands among the
// hypotheses and its consequent is the conclusion.
func TestWhistleGate_NamesTheByAndTheGoal(t *testing.T) {
	goal, hyps := nineEquivalences()
	sec := proof.NewScript(testenv.MakeT(t)).Section(goal)

	whistle := openWhistleGate()
	defer whistle.close()
	sec.Do(proof.Derive(func(a *proof.Argument) { showAcrossEquivalences(a, hyps) }))
	require.True(t, sec.Proved(), "the By closes: the cut costs it a case analysis, not the close")

	n, cuts := whistle.fired()
	require.EqualValues(t, 1, n, "nine equivalences reach the breadth backstop once")
	require.Contains(t, cuts, ") at /checkout/library/proofs/fixture/whistle.go:12: a case analysis reached 512 open leaves",
		"the refusal names the By by its call site")
	_, statement, stated := strings.Cut(cuts, "the goal it was entered with:")
	require.True(t, stated, cuts)
	require.Contains(t, statement, "P8(x) ⇔ Q8(x)", "the statement is the goal the case analysis was entered with")
	require.Contains(t, statement, "(((((((P0(x) ∨ P1(x))", "with the antecedent the rung stripped")
	require.Contains(t, statement, "⊢ (((((((Q0(x) ∨ Q1(x))", "and its conclusion")
	require.Contains(t, cuts, "\n     chapter line: library/proofs/fixture/whistle.go:11\n",
		"the refusal names the chapter line that was applying the step")
	require.Contains(t, cuts, tactic.WhistleCutAdvice)
}

// showAcrossEquivalences closes the goal of nineEquivalences by a By
// over its hypotheses, shaped by Basic(). It compiles as lines of a
// chapter file — a //line directive names the file and line of the line
// after it — so the By's call site and the chapter line are the
// fixture's: the Show at line 11, the By at line 12.
//
//line /checkout/library/proofs/fixture/whistle.go:6
func showAcrossEquivalences(a *proof.Argument, hyps []core.Term) {
	premises := []any{proof.Normalized}
	for _, h := range hyps {
		premises = append(premises, a.Hyp(h))
	}
	a.Show("each disjunct crosses its own equivalence",
		proof.By(premises...))
}
