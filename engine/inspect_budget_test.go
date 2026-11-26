package engine

import (
	"context"
	"fmt"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// selfFeedingRw is a goal one of whose rw probes does not end in any
// time a test waits. Hypothesis 0 is f(m) = g((λn. f(n))(m)): its right
// side holds its left side once the redex is reduced, so each pass of
// rw rewrites f(m), the pass's cleanup reduces the redex, and f(m)
// stands in the target again. The passes run to the goal's size, which
// hypothesis 1, a thousand applications deep, puts in the thousands,
// and a pass costs more as the target grows: minutes in all. Every
// other probe of the goal answers in milliseconds; the conclusion is a
// conjunction, so split_conj is one of them.
func selfFeedingRw() string {
	wide := "m"
	for range 1000 {
		wide = "g(" + wide + ")"
	}
	return "f:A→A, g:A→A, m:A, P:A→bool, Q:A→bool, f(m) = g((λn:A. f(n))(m)), P(" + wide + ") ⊢ Q(f(m)) ∧ Q(m)"
}

// selfFeedingRwSession is a session of e holding selfFeedingRw, with the
// index of the equation among the goal's hypotheses.
func selfFeedingRwSession(t *testing.T, e *Engine) (sid, gid string, eq int) {
	t.Helper()
	info, err := e.CreateSession(t.Context())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropText(selfFeedingRw())
	require.Empty(t, parsed.Errors)
	s.mu.Lock()
	gid = s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	eq = -1
	for i := range parsed.Prop.NumHyps() {
		if _, _, isEq := ext.MatchesEQ(parsed.Prop.Hyp(i)); isEq {
			eq = i
		}
	}
	require.GreaterOrEqual(t, eq, 0, "fixture: the equation is a hypothesis")
	return info.ID, gid, eq
}

// answersWithin runs call and fails the test if it has not returned
// limit after it started (the call then goes on in the background,
// holding its session, which no other test uses).
func answersWithin(t *testing.T, limit time.Duration, call func()) time.Duration {
	t.Helper()
	done := make(chan struct{})
	start := time.Now()
	go func() {
		defer close(done)
		call()
	}()
	select {
	case <-done:
		return time.Since(start)
	case <-time.After(limit):
		t.Fatalf("no answer %v after the call started", limit)
		return 0
	}
}

// TestInspect_AProbeThatDoesNotEndIsCutOffAndMarkedUnverified: inspect
// runs each of its clocked probes under the probe budget, so a goal one
// of whose probes does not end is answered at the budget, the session
// released. The cut probe's fact is in the answer, marked unverified
// with the budget it was cut at; every other fact stands.
func TestInspect_AProbeThatDoesNotEndIsCutOffAndMarkedUnverified(t *testing.T) {
	e := newEngine(testEnv())
	sid, gid, eq := selfFeedingRwSession(t, e)
	// One pass of the rw is milliseconds at the deadline; the slack is
	// for a loaded machine. An inspect with no budget fails on it.
	const slack = 15 * time.Second

	rwFact := func(res *InspectResult) StructuralFact {
		t.Helper()
		for _, fact := range res.StructuralFacts {
			if fact.Kind == "rw" && fact.Params["hyp_index"] == fmt.Sprint(eq) {
				return fact
			}
		}
		t.Fatalf("the rw fact of hypothesis %d is left out: %+v", eq, res.StructuralFacts)
		return StructuralFact{}
	}

	t.Run("at the request's budget_ms", func(t *testing.T) {
		const budget = 300 * time.Millisecond
		var res *InspectResult
		var err error
		elapsed := answersWithin(t, budget+slack, func() {
			res, err = e.Inspect(t.Context(), sid, &InspectRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds())})
		})
		require.NoError(t, err)
		fact := rwFact(res)
		assert.Contains(t, fact.Unverified, "cut off at inspect's 300 ms probe budget")
		assert.Contains(t, fact.Unverified, "neither verified nor ruled out")
		assert.Equal(t, "false", fact.Params["flip"], "the direction that was cut off")
		assert.GreaterOrEqual(t, elapsed, budget, "the probe ran to its budget")
		var verified []string
		for _, f := range res.StructuralFacts {
			if f.Unverified == "" {
				verified = append(verified, f.Kind)
			}
		}
		assert.Contains(t, verified, "split_conj", "the facts whose probes answered stand: %v", verified)
		assert.Len(t, res.Goals, 1, "the goal is served with the facts")
	})

	t.Run("at the default probe budget", func(t *testing.T) {
		var res *InspectResult
		var err error
		answersWithin(t, time.Duration(ProbeDefaultBudgetMs)*time.Millisecond+slack, func() {
			res, err = e.Inspect(t.Context(), sid, &InspectRequest{GoalID: gid})
		})
		require.NoError(t, err)
		assert.Contains(t, rwFact(res).Unverified, fmt.Sprintf("cut off at inspect's %d ms probe budget", ProbeDefaultBudgetMs))
	})

	t.Run("a request that goes away cuts the probe off", func(t *testing.T) {
		ctx, cancel := context.WithCancel(t.Context())
		time.AfterFunc(200*time.Millisecond, cancel)
		var res *InspectResult
		var err error
		answersWithin(t, slack, func() {
			res, err = e.Inspect(ctx, sid, &InspectRequest{GoalID: gid, BudgetMs: 600_000})
		})
		require.NoError(t, err)
		assert.Contains(t, rwFact(res).Unverified, "the request's context is done")
	})

	t.Run("the session takes its next command", func(t *testing.T) {
		res, err := e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, Tactic: TacticReq{Type: "clear", HypIndex: &eq}})
		require.NoError(t, err)
		assert.NotEqual(t, ProbeUnknown, res.Outcome, "diagnostic: %s", res.Diagnostic)
	})
}

// TestRw_ARunThatDoesNotEndIsCutOffNotFailed: a `probe` and an `apply`
// of an rw that does not end in its budget answer that it was cut off.
// The probe is unknown(timeout), where a tactic that did not apply is
// fail; the apply fails with the cut-off and no repair hint, commits
// nothing, records no fault and leaves the session taking moves.
func TestRw_ARunThatDoesNotEndIsCutOffNotFailed(t *testing.T) {
	store := t.TempDir()
	e := newEngine(testEnv(), WithFaultStore(filepath.Join(store, "faults")))
	sid, gid, eq := selfFeedingRwSession(t, e)
	const budget = 300 * time.Millisecond
	const slack = 15 * time.Second
	rw := TacticReq{Type: "rw", HypIndex: &eq}

	var probed *ProbeResult
	var err error
	answersWithin(t, budget+slack, func() {
		probed, err = e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds()), Tactic: rw})
	})
	require.NoError(t, err)
	assert.Equal(t, ProbeUnknown, probed.Outcome, "diagnostic: %s", probed.Diagnostic)
	assert.Equal(t, ProbeReasonTimeout, probed.Reason)
	assert.Contains(t, probed.Diagnostic, "rw was cut off inside rw")
	assert.Nil(t, probed.EngineFault)

	var applied *StepResult
	answersWithin(t, budget+slack, func() {
		applied, err = e.ApplyStep(t.Context(), sid, &ApplyStepRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds()), Tactic: rw})
	})
	require.NoError(t, err)
	require.False(t, applied.Success)
	require.Len(t, applied.Diagnostics, 1)
	assert.Contains(t, applied.Diagnostics[0].Message, "rw was cut off inside rw")
	assert.Contains(t, applied.Diagnostics[0].Message, "no evidence that the tactic does not apply")
	assert.Empty(t, applied.Diagnostics[0].RepairHints, "a cut-off run has nothing to repair")
	assert.Nil(t, applied.EngineFault)

	state, err := e.InspectState(t.Context(), sid)
	require.NoError(t, err)
	require.Len(t, state.Goals, 1)
	assert.Equal(t, gid, state.Goals[0].ID, "the goal is as it was")
	records, err := ListFaults(filepath.Join(store, "faults"))
	require.NoError(t, err)
	assert.Empty(t, records, "a cut-off at its budget is no fault and no overrun")
}

// TestOverrun_ARunThatEndsWellPastItsDeadlineIsRecorded: a run that
// ends later than overrunRecordAfter past its deadline is written to
// the fault store as an overrun, with the request and the goal, and
// `faults` lists it open. The session is not locked. The threshold is
// lowered to nothing here, so the instant a cut takes past its deadline
// stands in for the seconds a unit that reads no clock would take.
func TestOverrun_ARunThatEndsWellPastItsDeadlineIsRecorded(t *testing.T) {
	kept := overrunRecordAfter
	overrunRecordAfter = 0
	t.Cleanup(func() { overrunRecordAfter = kept })
	var observed []*FaultRecord
	overrunObserver = func(record *FaultRecord) { observed = append(observed, record) }
	t.Cleanup(func() { overrunObserver = nil })

	store := filepath.Join(t.TempDir(), "faults")
	e := newEngine(testEnv(), WithFaultStore(store))
	sid, gid, eq := selfFeedingRwSession(t, e)
	const budget = 200 * time.Millisecond

	var err error
	answersWithin(t, budget+15*time.Second, func() {
		_, err = e.Inspect(t.Context(), sid, &InspectRequest{GoalID: gid, BudgetMs: int(budget.Milliseconds())})
	})
	require.NoError(t, err)
	require.NotEmpty(t, observed, "the cut probe ended past its deadline")

	view, err := ViewFaults(store, false)
	require.NoError(t, err)
	require.Equal(t, len(observed), view.Open)
	var row *FaultRow
	for i := range view.Faults {
		if strings.Contains(view.Faults[i].Panic, fmt.Sprintf("the rw probe by hypothesis %d of inspect", eq)) {
			row = &view.Faults[i]
		}
	}
	require.NotNil(t, row, "the listing names the probe: %+v", view.Faults)
	assert.Equal(t, "inspect", row.Command)
	assert.Equal(t, sid, row.Session)
	assert.Equal(t, gid, row.GoalID)
	assert.Positive(t, row.OverrunMs)

	record, err := ReadFault(store, row.ID)
	require.NoError(t, err)
	require.NotNil(t, record.Overrun)
	assert.True(t, record.Overrun.CutOff)
	assert.Equal(t, int(budget.Milliseconds()), record.Overrun.BudgetMs)
	assert.Contains(t, record.Stack, "rwFixpoint", "the stack is the cut's")
	require.NotNil(t, record.Goal)
	assert.NotEmpty(t, record.Goal.Blob, "the goal is on record for a test to rebuild")

	res, err := e.Probe(t.Context(), sid, &ProbeRequest{GoalID: gid, Tactic: TacticReq{Type: "clear", HypIndex: &eq}})
	require.NoError(t, err, "an overrun locks no session")
	assert.NotEqual(t, ProbeUnknown, res.Outcome)
}
