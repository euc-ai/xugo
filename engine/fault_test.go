package engine

import (
	"context"
	"encoding/json"
	"os"
	"path/filepath"
	"sync/atomic"
	"testing"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/euc-ai/xugo/utils"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// _BreakingCNFStore fails an assertion at its first read of a proof and
// holds nothing: a tactic whose close reaches the store breaks an engine
// invariant on the request's own goroutine, once, and the same tactic
// run again refutes its leaf live.
type _BreakingCNFStore struct {
	proof.CNFStore
	reads *atomic.Int32
}

func (s _BreakingCNFStore) ReadProof(core.PropKey) *refuter.CNFRefuteProofProto {
	if s.reads.Add(1) == 1 {
		utils.Assert(false)
	}
	return nil
}

func breakingStore() proof.CNFStore {
	return _BreakingCNFStore{proof.NewMemoryCNFStore(), &atomic.Int32{}}
}

// _FaultFixture is an engine whose CNF store breaks once, over a session
// store and a fault store under dir, with one session holding the goal
// "a chain of three equations gives the fourth" and the `by` that
// closes it from its three hypotheses.
type _FaultFixture struct {
	e      *Engine
	faults string
	sid    string
	gid    string
	goal   core.Prop
	by     TacticReq
}

func newFaultFixture(t *testing.T, dir string) _FaultFixture {
	t.Helper()
	env := testEnv()
	env.ProofService.CNFStore = breakingStore()
	faults := ""
	opts := []EngineOption{}
	if dir != "" {
		faults = filepath.Join(dir, "faults")
		opts = append(opts, WithSessionStore(filepath.Join(dir, "sessions")), WithFaultStore(faults))
	}
	e := newEngine(env, opts...)
	info, err := e.CreateSession(context.Background())
	require.NoError(t, err)
	s, err := e.getSession(info.ID)
	require.NoError(t, err)
	parsed := dsl.ParsePropText("f:num→num, g:num→num, h:num→num, k:num→num, a:num, b:num, c:num, d:num, " +
		"f(a) = g(b), g(b) = h(c), h(c) = k(d) ⊢ f(a) = k(d)")
	require.Empty(t, parsed.Errors)
	s.mu.Lock()
	gid := s.AddGoal(parsed.Prop)
	s.mu.Unlock()
	zero, one, two := 0, 1, 2
	return _FaultFixture{e: e, faults: faults, sid: info.ID, gid: gid, goal: parsed.Prop,
		by: TacticReq{Type: "by", ByHyps: []ByHypSpec{{HypIndex: &zero}, {HypIndex: &one}, {HypIndex: &two}}}}
}

func (f _FaultFixture) apply(t *testing.T) *StepResult {
	t.Helper()
	out, err := f.e.ApplyStep(context.Background(), f.sid, &ApplyStepRequest{GoalID: f.gid, Tactic: f.by, BudgetMs: 3000})
	require.NoError(t, err)
	return out
}

// TestApply_AnEngineFaultIsMarkedRecordedAndLocksTheSession: a `by`
// whose close breaks an assertion is no tactic that did not apply. The
// response carries the fault's mark and an engine_fault diagnostic with
// no repair hint; the record is on disk with the request and the goal in
// a form a test rebuilds; the fault is an event of the session's
// lineage; and the session answers reads and refuses moves, naming the
// record, until the record is acknowledged.
func TestApply_AnEngineFaultIsMarkedRecordedAndLocksTheSession(t *testing.T) {
	expectFaults(t)
	f := newFaultFixture(t, t.TempDir())
	ctx := context.Background()
	lineageBefore, err := f.e.SessionLineage(f.sid)
	require.NoError(t, err)

	out := f.apply(t)
	require.False(t, out.Success)
	require.NotNil(t, out.EngineFault, "the response carries the fault's mark: %+v", out.Diagnostics)
	fault := out.EngineFault
	assert.Contains(t, fault.Panic, utils.AssertionFailed)
	assert.Contains(t, fault.Site, "fault_test.go:")
	require.Len(t, out.Diagnostics, 1)
	assert.Equal(t, DiagEngineFault, out.Diagnostics[0].Type, "not a tactic_failure")
	assert.Empty(t, out.Diagnostics[0].RepairHints, "no repair is offered around a fault")
	assert.Contains(t, out.Diagnostics[0].Message, fault.ID)
	wire, err := json.Marshal(out)
	require.NoError(t, err)
	assert.Contains(t, string(wire), `"engine_fault":{"id":"`+fault.ID+`"`)

	// The record.
	require.Equal(t, filepath.Join(f.faults, fault.ID+".json"), fault.Record)
	records, err := ListFaults(f.faults)
	require.NoError(t, err)
	require.Len(t, records, 1)
	record := records[0]
	assert.Equal(t, fault.ID, record.ID)
	assert.Equal(t, "apply", record.Command)
	assert.Equal(t, f.sid, record.Session)
	assert.Equal(t, len(lineageBefore.Events), record.LineageSeq, "the session's state when the request arrived")
	assert.Equal(t, 3000, record.BudgetMs)
	assert.Equal(t, "request", record.Goroutine)
	assert.Contains(t, record.Panic, utils.AssertionFailed)
	assert.Contains(t, record.Stack, "ReadProof", "the stack reaches the break")
	assert.Contains(t, record.Stack, "ApplyByStep", "and shows the request's way to it")
	assert.Nil(t, record.Ack)
	require.NotNil(t, record.Goal)
	assert.Equal(t, f.gid, record.Goal.GoalID)
	rebuilt, _, err := ext.UnmarshalPropBlob(record.Goal.Blob, f.e.env.ProofService.LoadConstMeta)
	require.NoError(t, err)
	assert.True(t, f.goal.AlphaEquals(rebuilt), "the blob rebuilds the sequent the tactic ran on")
	closed := dsl.ParsePropText(record.Goal.Closed)
	require.Empty(t, closed.Errors, "the closed spelling reads as a goal text: %s", record.Goal.Closed)
	assert.Zero(t, closed.Prop.NumHyps())
	require.NotNil(t, record.Tactic)
	replayed, err := record.Tactic.tacticReq(f.e.env.ProofService.LoadConstMeta)
	require.NoError(t, err)
	assert.Equal(t, f.by, replayed, "the tactic decodes to the request")

	// The session: reads answer, moves are refused naming the record.
	_, err = f.e.Inspect(ctx, f.sid, &InspectRequest{})
	assert.NoError(t, err, "inspect still answers")
	lineage, err := f.e.SessionLineage(f.sid)
	require.NoError(t, err)
	require.Len(t, lineage.Events, len(lineageBefore.Events)+1)
	assert.Equal(t, kindFault, lineage.Events[len(lineage.Events)-1].Kind)
	assert.Contains(t, lineage.Events[len(lineage.Events)-1].Summary, fault.ID)
	for name, move := range map[string]func() error{
		"apply": func() error {
			_, err := f.e.ApplyStep(ctx, f.sid, &ApplyStepRequest{GoalID: f.gid, Tactic: f.by})
			return err
		},
		"probe": func() error {
			_, err := f.e.Probe(ctx, f.sid, &ProbeRequest{GoalID: f.gid, Tactic: f.by})
			return err
		},
		"batch-apply": func() error {
			_, err := f.e.BatchApply(ctx, f.sid, &BatchApplyRequest{GoalID: f.gid, Tactics: []TacticReq{f.by}, Mode: FirstSuccess})
			return err
		},
		"checkpoint": func() error { _, err := f.e.Checkpoint(ctx, f.sid, "after"); return err },
		"add-goal":   func() error { s, _ := f.e.getSession(f.sid); return s.FaultRefusal() },
	} {
		err := move()
		require.Error(t, err, "%s is refused", name)
		assert.Contains(t, err.Error(), fault.ID, "%s's refusal names the fault", name)
		assert.Contains(t, err.Error(), fault.Record, "%s's refusal names the record", name)
	}

	// Acknowledged, the session takes moves again; the same `by` closes.
	_, err = AcknowledgeFault(f.faults, fault.ID, "")
	require.Error(t, err, "an acknowledgment says what was done")
	acked, err := AcknowledgeFault(f.faults, fault.ID, "reproduced; fixed at its source")
	require.NoError(t, err)
	require.NotNil(t, acked.Ack)
	out = f.apply(t)
	require.True(t, out.Success, "%+v", out.Diagnostics)
	assert.Nil(t, out.EngineFault)
	records, err = ListFaults(f.faults)
	require.NoError(t, err)
	require.Len(t, records, 1, "the acknowledged record stays on file")
	assert.Equal(t, "reproduced; fixed at its source", records[0].Ack.Note)
}

// TestProbe_AnEngineFaultAnswersPanicRecoveredWithTheMark: a probe of
// the same `by` answers unknown(panic_recovered), not the fail a `by`
// that did not close answers, carries the mark, and leaves the same
// record and the same lock as an apply.
func TestProbe_AnEngineFaultAnswersPanicRecoveredWithTheMark(t *testing.T) {
	expectFaults(t)
	f := newFaultFixture(t, t.TempDir())
	ctx := context.Background()
	res, err := f.e.Probe(ctx, f.sid, &ProbeRequest{GoalID: f.gid, Tactic: f.by})
	require.NoError(t, err)
	assert.Equal(t, ProbeUnknown, res.Outcome)
	assert.Equal(t, ProbeReasonPanicRecovered, res.Reason)
	require.NotNil(t, res.EngineFault)
	assert.Contains(t, res.Diagnostic, res.EngineFault.ID)

	records, err := ListFaults(f.faults)
	require.NoError(t, err)
	require.Len(t, records, 1)
	assert.Equal(t, "probe", records[0].Command)
	assert.Equal(t, f.gid, records[0].Goal.GoalID)
	require.NotNil(t, records[0].Tactic)
	assert.Equal(t, "by", records[0].Tactic.Type)

	_, err = f.e.Probe(ctx, f.sid, &ProbeRequest{GoalID: f.gid, Tactic: f.by})
	require.Error(t, err, "the session takes no further probe")
	assert.Contains(t, err.Error(), res.EngineFault.ID)
}

// TestBatchApply_EndsAtAnEngineFault: the tactic that met the fault
// carries its mark and the tactics after it are not run, where a
// first_success batch would otherwise commit the next one that closes.
func TestBatchApply_EndsAtAnEngineFault(t *testing.T) {
	expectFaults(t)
	f := newFaultFixture(t, t.TempDir())
	res, err := f.e.BatchApply(context.Background(), f.sid, &BatchApplyRequest{
		GoalID: f.gid, Tactics: []TacticReq{f.by, f.by}, Mode: FirstSuccess})
	require.NoError(t, err)
	assert.Equal(t, -1, res.WinnerIndex)
	require.Len(t, res.Results, 2)
	require.NotNil(t, res.Results[0].EngineFault)
	assert.False(t, res.Results[1].Success)
	assert.Nil(t, res.Results[1].EngineFault)
	require.Len(t, res.Results[1].Diagnostics, 1)
	assert.Contains(t, res.Results[1].Diagnostics[0].Message, "not run")
	assert.Contains(t, res.Results[1].Diagnostics[0].Message, res.Results[0].EngineFault.ID)
	s, _ := f.e.getSession(f.sid)
	assert.False(t, s.sections[0].root.Proved(), "nothing was committed")
}

// TestApply_AFaultWithNoStoreStillMarksAndLocks: an engine with no fault
// store writes no file; the response is marked all the same and the
// session takes no further move.
func TestApply_AFaultWithNoStoreStillMarksAndLocks(t *testing.T) {
	expectFaults(t)
	f := newFaultFixture(t, "")
	out := f.apply(t)
	require.NotNil(t, out.EngineFault)
	assert.Empty(t, out.EngineFault.Record)
	_, err := f.e.ApplyStep(context.Background(), f.sid, &ApplyStepRequest{GoalID: f.gid, Tactic: f.by})
	require.Error(t, err)
	assert.Contains(t, err.Error(), out.EngineFault.ID)
	assert.Contains(t, err.Error(), "no fault store")
}

// TestResume_AFaultedSessionStaysLockedUntilAcknowledged: the fault is
// in the lineage, so a session resumed by a later engine over the same
// stores is locked as the one that met the fault was, and is unlocked
// by the same acknowledgment.
func TestResume_AFaultedSessionStaysLockedUntilAcknowledged(t *testing.T) {
	expectFaults(t)
	dir := t.TempDir()
	f := newFaultFixture(t, dir)
	fault := f.apply(t).EngineFault
	require.NotNil(t, fault)

	env := testEnv()
	env.ProofService.CNFStore = proof.NewMemoryCNFStore()
	later := newEngine(env, WithSessionStore(filepath.Join(dir, "sessions")), WithFaultStore(f.faults))
	ctx := context.Background()
	resumed, err := later.ResumeSession(ctx, f.sid)
	require.NoError(t, err)
	require.Nil(t, resumed.Diverged, "the fault event replays: %+v", resumed.Diverged)

	_, err = later.ApplyStep(ctx, f.sid, &ApplyStepRequest{GoalID: f.gid, Tactic: f.by})
	require.Error(t, err, "the resumed session is locked")
	assert.Contains(t, err.Error(), fault.ID)

	_, err = AcknowledgeFault(f.faults, fault.ID, "fixed at its source")
	require.NoError(t, err)
	out, err := later.ApplyStep(ctx, f.sid, &ApplyStepRequest{GoalID: f.gid, Tactic: f.by})
	require.NoError(t, err)
	assert.True(t, out.Success, "%+v", out.Diagnostics)
}

// TestFaultRecord_OfASearchFaultNamesTheWorkerAndTheSequentRefuted: a
// fault a search raised from another goroutine is recorded with that
// goroutine's stack, where on the request's goroutine it was raised,
// and the sequent the refutation ran on.
func TestFaultRecord_OfASearchFaultNamesTheWorkerAndTheSequentRefuted(t *testing.T) {
	f := newFaultFixture(t, t.TempDir())
	s, _ := f.e.getSession(f.sid)
	search := refuter.SearchFault{
		Fault: utils.Fault{
			Value: utils.AssertionFailed + " (at deduce.go:250 in clause.contradictsFromSubst)",
			Site:  "deduce.go:250 in clause.contradictsFromSubst",
			Stack: "goroutine 7 [running]:\nrefuter.(*_RefuteState).findContradicts.func2()\n",
		},
		Goal: f.goal,
	}
	scope := faultScope(context.Background(), s, "apply").onGoal(f.gid, s.goalIndex[f.gid], f.by, 0)
	record := scope.record(search, "goroutine 3 [running]:\nengine.(*Engine).runTactic.func2()\n")
	assert.Equal(t, "worker", record.Goroutine)
	assert.Equal(t, search.Site, record.Site)
	assert.Contains(t, record.Stack, "findContradicts.func2")
	assert.Contains(t, record.RaisedAt, "runTactic")
	require.NotNil(t, record.Refuted)
	rebuilt, _, err := ext.UnmarshalPropBlob(record.Refuted.Blob, f.e.env.ProofService.LoadConstMeta)
	require.NoError(t, err)
	assert.True(t, f.goal.AlphaEquals(rebuilt))

	onRequest := scope.record(search, "goroutine 7 [running]:\nengine.(*Engine).runTactic.func2()\n")
	assert.Equal(t, "request", onRequest.Goroutine, "a search's panic on the asking goroutine is the request's")
	assert.Empty(t, onRequest.RaisedAt)
}

// TestLateFault_IsRecordedAndLocksTheSession: a fault a search met after
// answering has no response to mark. It is recorded against the request
// that started the search, as late, and the session is locked from then
// on.
func TestLateFault_IsRecordedAndLocksTheSession(t *testing.T) {
	expectFaults(t)
	f := newFaultFixture(t, t.TempDir())
	s, _ := f.e.getSession(f.sid)
	scope := faultScope(context.Background(), s, "apply").onGoal(f.gid, s.goalIndex[f.gid], f.by, 0)
	f.e.lateFault(scope, refuter.SearchFault{
		Fault: utils.Fault{Value: "a check still running broke", Site: "deduce.go:1 in clause.rule", Stack: "goroutine 9 [running]:\n"},
		Goal:  f.goal,
	})
	records, err := ListFaults(f.faults)
	require.NoError(t, err)
	require.Len(t, records, 1)
	assert.True(t, records[0].Late)
	assert.Equal(t, "worker", records[0].Goroutine)
	_, err = f.e.ApplyStep(context.Background(), f.sid, &ApplyStepRequest{GoalID: f.gid, Tactic: f.by})
	require.Error(t, err)
	assert.Contains(t, err.Error(), records[0].ID)
}

// TestRecordCommandFault_RecordsAPanicThatLeftACommand: the /rpc
// handler's reading of a panic out of a command that is no tactic run.
// The record holds the request body as it came, and the session the
// body names is the one that met the fault.
func TestRecordCommandFault_RecordsAPanicThatLeftACommand(t *testing.T) {
	expectFaults(t)
	f := newFaultFixture(t, t.TempDir())
	body := []byte(`{"cmd":"emit-section","session_id":"` + f.sid + `","section":0}`)
	var fault *EngineFault
	func() {
		defer func() {
			if r := recover(); r != nil {
				fault = f.e.RecordCommandFault("emit-section", body, r)
			}
		}()
		var none *Session
		_ = none.ID // a nil dereference inside a command
	}()
	require.NotNil(t, fault)
	assert.Contains(t, fault.Panic, "nil pointer dereference")
	assert.Contains(t, fault.Site, "fault_test.go:")
	record, err := readFaultRecord(fault.Record)
	require.NoError(t, err)
	assert.Equal(t, "emit-section", record.Command)
	assert.JSONEq(t, string(body), string(record.RPCBody))
	assert.Equal(t, f.sid, record.Session)
	assert.Nil(t, record.Goal)
	_, err = f.e.ApplyStep(context.Background(), f.sid, &ApplyStepRequest{GoalID: f.gid, Tactic: f.by})
	require.Error(t, err, "the named session is locked")

	stateless := f.e.RecordCommandFault("check", []byte(`{"cmd":"check"}`), "a panic with no session")
	require.NotNil(t, stateless)
	record, err = readFaultRecord(stateless.Record)
	require.NoError(t, err)
	assert.Empty(t, record.Session)
}

// TestListFaults_OfAStoreThatDoesNotExistIsEmpty: no fault has been
// recorded where no store was made.
func TestListFaults_OfAStoreThatDoesNotExistIsEmpty(t *testing.T) {
	records, err := ListFaults(filepath.Join(t.TempDir(), "faults"))
	require.NoError(t, err)
	assert.Empty(t, records)

	dir := t.TempDir()
	require.NoError(t, os.WriteFile(filepath.Join(dir, "notes.json"), []byte("{}"), 0o644))
	records, err = ListFaults(dir)
	require.NoError(t, err)
	assert.Empty(t, records, "a file that is no record is not read as one")

	_, err = AcknowledgeFault(dir, "../sessions/x", "a note")
	require.Error(t, err, "an id is checked before it names a path")
	_, err = AcknowledgeFault(dir, "20261112T000000Z-0123abcd", "a note")
	require.Error(t, err, "no such record")
}
