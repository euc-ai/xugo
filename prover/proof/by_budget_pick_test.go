package proof

import (
	"context"
	"testing"
	"time"

	"github.com/stretchr/testify/require"
)

// The ladder's budget pick: a conditioned rung whose refutation ran to
// the refuter budget, and a bare retry that then closed, record a bare
// key where the conditioned rung, given the time, records a conditioned
// key and a plan row. tryCNFRefute tells the ladder state its context
// carries that the search ended at the budget, and the closing rung
// reports it through the recorder's audit sink and the call's own.

// TestNoteRefuteCutOff_TheBudgetsDeadlineNotTheCallers: a search whose
// context expired while the caller's is alive ran to the refuter's
// budget, and the ladder state the caller's context carries records it;
// a search the caller's deadline ended, a search that finished inside
// its context, a budget of 0 (the replay sentinel) and a context without
// a ladder state record nothing.
func TestNoteRefuteCutOff_TheBudgetsDeadlineNotTheCallers(t *testing.T) {
	budget := 500 * time.Millisecond
	withLadder := func() (context.Context, *byLadderState) {
		st := &byLadderState{}
		return context.WithValue(context.Background(), byLadderStateKey{}, st), st
	}
	expired := func(parent context.Context) context.Context {
		ctx, cancel := context.WithCancel(parent)
		cancel()
		return ctx
	}

	parent, st := withLadder()
	noteRefuteCutOff(parent, expired(parent), budget)
	require.Equal(t, "a refutation ran to its 500ms budget", st.cutOff)

	parent, st = withLadder()
	noteRefuteCutOff(parent, parent, budget)
	require.Empty(t, st.cutOff, "a search that finished inside its context was not cut off")

	parent, st = withLadder()
	noteRefuteCutOff(parent, expired(parent), 0)
	require.Empty(t, st.cutOff, "a budget of 0 is the replay sentinel: no live search ran")

	parent, st = withLadder()
	gone := expired(parent)
	noteRefuteCutOff(gone, expired(gone), budget)
	require.Empty(t, st.cutOff, "the caller's deadline is not the refuter's budget")

	plain := context.Background()
	noteRefuteCutOff(plain, expired(plain), budget) // no ladder state: nowhere to record, and no panic
}

// TestLadderState_KeepsTheFirstCutOff: the first refutation to run to
// budget describes the rung; later ones change nothing.
func TestLadderState_KeepsTheFirstCutOff(t *testing.T) {
	st := &byLadderState{}
	st.noteCutOff(500 * time.Millisecond)
	st.noteCutOff(5 * time.Second)
	require.Equal(t, "a refutation ran to its 500ms budget", st.cutOff)
	require.Nil(t, ladderStateOf(context.Background()))
	require.Same(t, st, ladderStateOf(context.WithValue(context.Background(), byLadderStateKey{}, st)))
}

// TestRanToBudget_TheCeilingIsNinetyPercentOfTheBudget: the terminal
// close's measurement behind byBudgetAdvice, with its three refusals — a
// closer other than the refuter, the replay sentinel, a close well under
// the ceiling.
func TestRanToBudget_TheCeilingIsNinetyPercentOfTheBudget(t *testing.T) {
	budget := 5 * time.Second
	require.True(t, ranToBudget(true, budget, 4500*time.Millisecond), "nine tenths of the budget is the ceiling")
	require.True(t, ranToBudget(true, budget, 5084*time.Millisecond), "an overshoot ran to the budget")
	require.False(t, ranToBudget(true, budget, 4499*time.Millisecond), "under the ceiling the search finished")
	require.False(t, ranToBudget(false, budget, budget), "an arith or settac close has no refuter budget")
	require.False(t, ranToBudget(true, 0, budget), "a budget of 0 is the replay sentinel: no live search ran")
	require.Empty(t, byBudgetAdvice(true, budget, 4499*time.Millisecond))
	require.Contains(t, byBudgetAdvice(true, budget, 5084*time.Millisecond), "ran 5.084s against a 5s search budget")
}

// TestReportBudgetPick_SaysWhichRowsTheBudgetPicked: given the
// conditioned rung's cut-off, the report names the By, the budget and
// the rows each rung records, and reaches both sinks; given none,
// nothing is reported.
func TestReportBudgetPick_SaysWhichRowsTheBudgetPicked(t *testing.T) {
	var audit, leaf []string
	env := &ProverEnv{ByAuditReport: func(f string) { audit = append(audit, f) }}
	step := _ByStep{
		env:        env,
		site:       "member.go:12",
		leafReport: func(f string) { leaf = append(leaf, f) },
	}
	st := &byLadderState{}
	st.noteCutOff(5 * time.Second)
	step.reportBudgetPick(st.cutOff, byRetryPick)
	require.Len(t, audit, 1)
	require.Equal(t, audit, leaf, "the call's own sink hears the same finding")
	finding := audit[0]
	require.Contains(t, finding, "By() at member.go:12: in the conditioned rung a refutation ran to its 5s budget and was cut off")
	require.Contains(t, finding, "the rows recorded here are a bare key and no plan")
	require.Contains(t, finding, "records a conditioned key and a plan row")
	require.Contains(t, finding, "the machine's load, not the spelling")

	step.reportBudgetPick("", byRetryPick)
	require.Len(t, audit, 1, "no cut-off, no finding")

	step.reportBudgetPick(st.cutOff, byPrunedRunPick)
	require.Len(t, audit, 2)
	pruned := audit[1]
	require.Contains(t, pruned, "By() at member.go:12: in the conditioned rung a refutation ran to its 5s budget and was cut off")
	require.Contains(t, pruned, "run again on the pruned leaf, the rung closed it")
	require.Contains(t, pruned, "the plan recorded here replaces.")
	require.Contains(t, pruned, "records a plan that replaces nothing")
	require.Contains(t, pruned, "the machine's load, not the spelling")
	require.NotContains(t, pruned, "bare key")
}

// TestCutsARetryReplaySkips: which whistle cuts a close at the bare retry
// reports. A conditioned rung that failed on its own leaves a recording
// that replays the retry's path alone, so every earlier cut is skipped;
// one cut off at the refuter's budget leaves either recording possible,
// so none is.
func TestCutsARetryReplaySkips(t *testing.T) {
	require.Equal(t, 3, cutsARetryReplaySkips(3, ""), "the conditioned rung failed on its own: a replay runs the retry's path")
	require.Equal(t, 0, cutsARetryReplaySkips(3, "a refutation ran to its 500ms budget"),
		"the conditioned rung was cut off: a recording given the time closes there, and its replay runs that rung")
	require.Equal(t, 0, cutsARetryReplaySkips(0, ""))
}

// TestCutsAPrunedRunReplaySkips: which whistle cuts a close at the
// conditioned rung's run on the pruned leaf reports. A run on the whole
// leaf that failed on its own leaves a recording whose replay runs the
// probes and the pruned run's plan: the whole run's cuts, those between
// the two counts, are skipped and the probes' are not. One cut off at
// the refuter's budget leaves either recording possible, so none is.
func TestCutsAPrunedRunReplaySkips(t *testing.T) {
	from, to := cutsAPrunedRunReplaySkips(2, 5, "")
	require.Equal(t, []int{2, 5}, []int{from, to}, "the run on the whole leaf failed on its own: its three cuts are skipped")
	from, to = cutsAPrunedRunReplaySkips(2, 5, "a refutation ran to its 500ms budget")
	require.Equal(t, []int{0, 0}, []int{from, to}, "the run on the whole leaf was cut off: a recording given the time closes there")
	from, to = cutsAPrunedRunReplaySkips(2, 2, "")
	require.Equal(t, from, to, "a run that fired no cut leaves none to skip")
}
