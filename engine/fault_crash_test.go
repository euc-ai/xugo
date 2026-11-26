package engine

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"testing"
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// _WatchingCNFStore calls watch at each read of a proof: a look at the
// world from inside a tactic that is running.
type _WatchingCNFStore struct {
	proof.CNFStore
	watch func()
}

func (s _WatchingCNFStore) ReadProof(core.PropKey) *refuter.CNFRefuteProofProto {
	s.watch()
	return nil
}

// TestInFlight_ARequestIsOnDiskWhileItsTacticRuns: from the start of a
// tactic run to its answer the request is a file of the fault store,
// naming the session, the goal and the tactic; once the run has
// answered the file is gone.
func TestInFlight_ARequestIsOnDiskWhileItsTacticRuns(t *testing.T) {
	f := newFaultFixture(t, t.TempDir())
	pattern := filepath.Join(f.faults, fmt.Sprintf("serve-%d-*.inflight", os.Getpid()))
	var during []FaultInFlight
	f.e.env.ProofService.CNFStore = _WatchingCNFStore{proof.NewMemoryCNFStore(), func() {
		files, _ := filepath.Glob(pattern)
		for _, file := range files {
			data, err := os.ReadFile(file)
			require.NoError(t, err)
			var running FaultInFlight
			require.NoError(t, json.Unmarshal(data, &running))
			during = append(during, running)
		}
	}}

	out := f.apply(t)
	require.True(t, out.Success, "%+v", out.Diagnostics)
	require.NotEmpty(t, during, "fixture: the close reads the store")
	assert.Equal(t, "apply", during[0].Command)
	assert.Equal(t, f.sid, during[0].Session)
	assert.Equal(t, f.gid, during[0].GoalID)
	require.NotNil(t, during[0].Tactic)
	assert.Equal(t, "by", during[0].Tactic.Type)
	after, _ := filepath.Glob(pattern)
	assert.Empty(t, after, "an answered request is in flight no longer")
}

// inFlightFiles reads the in-flight files this process has under store.
func inFlightFiles(t *testing.T, store string) []FaultInFlight {
	t.Helper()
	files, err := filepath.Glob(filepath.Join(store, fmt.Sprintf("serve-%d-*.inflight", os.Getpid())))
	require.NoError(t, err)
	var running []FaultInFlight
	for _, file := range files {
		data, err := os.ReadFile(file)
		require.NoError(t, err)
		var one FaultInFlight
		require.NoError(t, json.Unmarshal(data, &one))
		running = append(running, one)
	}
	return running
}

// shortInFlightAfter sets InFlightAfter for the test, which may set it
// again; the value it had comes back when the test ends.
func setInFlightAfter(t *testing.T, after time.Duration) {
	t.Helper()
	kept := InFlightAfter
	InFlightAfter = after
	t.Cleanup(func() { InFlightAfter = kept })
}

// TestKeepInFlight_ACommandThatIsNoTacticRunIsOnDiskOnceItHasRun: a
// request kept in flight is a file of the fault store from the time its
// command has run InFlightAfter until it answers, whatever the command:
// the file names the command, the session and the goal the body named,
// the session's position, and holds the body. A command that answers
// sooner writes nothing.
func TestKeepInFlight_ACommandThatIsNoTacticRunIsOnDiskOnceItHasRun(t *testing.T) {
	f := newFaultFixture(t, t.TempDir())
	body := []byte(fmt.Sprintf(`{"cmd":"inspect","session_id":%q,"goal_id":%q}`, f.sid, f.gid))
	lineage, err := f.e.SessionLineage(f.sid)
	require.NoError(t, err)

	// A command that answers before InFlightAfter, here an hour.
	setInFlightAfter(t, time.Hour)
	_, answered := f.e.KeepInFlight(context.Background(), "inspect", body)
	assert.Empty(t, inFlightFiles(t, f.faults), "nothing is written before the command has run InFlightAfter")
	answered()
	assert.Empty(t, inFlightFiles(t, f.faults), "a command that answered before InFlightAfter leaves nothing")

	InFlightAfter = 50 * time.Millisecond
	_, answered = f.e.KeepInFlight(context.Background(), "inspect", body)
	require.Eventually(t, func() bool { return len(inFlightFiles(t, f.faults)) == 1 },
		5*time.Second, 5*time.Millisecond, "the request is on disk once the command has run InFlightAfter")
	running := inFlightFiles(t, f.faults)[0]
	assert.Equal(t, "inspect", running.Command)
	assert.Equal(t, f.sid, running.Session)
	assert.Equal(t, f.gid, running.GoalID)
	assert.Equal(t, len(lineage.Events), running.LineageSeq)
	assert.JSONEq(t, string(body), string(running.RPCBody))
	assert.Nil(t, running.Tactic)
	answered()
	assert.Empty(t, inFlightFiles(t, f.faults), "an answered request is in flight no longer")
}

// TestKeepInFlight_ATacticRunJoinsItsRequestsFile: a tactic run of a
// kept request is on disk from its start, in the request's own file, so
// one request is one file; when the run answers before the request is
// InFlightAfter old the file goes, and when the request is older it
// stays without the tactic until the request answers.
func TestKeepInFlight_ATacticRunJoinsItsRequestsFile(t *testing.T) {
	f := newFaultFixture(t, t.TempDir())
	// during is the files on disk at each look from inside the run.
	var during [][]FaultInFlight
	f.e.env.ProofService.CNFStore = _WatchingCNFStore{proof.NewMemoryCNFStore(), func() {
		during = append(during, inFlightFiles(t, f.faults))
	}}
	apply := func(ctx context.Context) {
		out, err := f.e.ApplyStep(ctx, f.sid, &ApplyStepRequest{GoalID: f.gid, Tactic: f.by, BudgetMs: 3000})
		require.NoError(t, err)
		require.True(t, out.Success, "%+v", out.Diagnostics)
	}

	// A request younger than InFlightAfter, here an hour, for its whole run.
	setInFlightAfter(t, time.Hour)
	ctx, answered := f.e.KeepInFlight(context.Background(), "apply", []byte(`{"cmd":"apply"}`))
	checkpoint, err := f.e.Checkpoint(context.Background(), f.sid, "before")
	require.NoError(t, err)
	apply(ctx)
	require.NotEmpty(t, during, "fixture: the close reads the store")
	for _, files := range during {
		require.Len(t, files, 1, "one request, one file, while the tactic runs")
	}
	running := during[0][0]
	assert.Equal(t, "apply", running.Command)
	assert.Equal(t, f.sid, running.Session)
	assert.Equal(t, f.gid, running.GoalID)
	require.NotNil(t, running.Tactic)
	assert.Equal(t, "by", running.Tactic.Type)
	assert.Empty(t, inFlightFiles(t, f.faults), "the run answered inside InFlightAfter: the file is gone")
	answered()

	// The same run in a request already InFlightAfter old.
	require.NoError(t, f.e.Restore(context.Background(), f.sid, checkpoint))
	InFlightAfter = 20 * time.Millisecond
	during = nil
	ctx, answered = f.e.KeepInFlight(context.Background(), "apply", []byte(`{"cmd":"apply"}`))
	require.Eventually(t, func() bool { return len(inFlightFiles(t, f.faults)) == 1 }, 5*time.Second, 5*time.Millisecond)
	apply(ctx)
	require.NotEmpty(t, during)
	for _, files := range during {
		require.Len(t, files, 1)
		require.NotNil(t, files[0].Tactic)
	}
	after := inFlightFiles(t, f.faults)
	require.Len(t, after, 1, "the request has not answered: its file stays")
	assert.Nil(t, after[0].Tactic, "and names no tactic once the run has answered")
	answered()
	assert.Empty(t, inFlightFiles(t, f.faults))
}

// TestCollectCrashes_AServeStoppedDuringACommandThatIsNoTacticRun: a
// serve stopped while an inspect had not answered leaves the request
// behind, and the listing names it by its command, its session and its
// goal.
func TestCollectCrashes_AServeStoppedDuringACommandThatIsNoTacticRun(t *testing.T) {
	setInFlightAfter(t, 20*time.Millisecond)
	f := newFaultFixture(t, t.TempDir())
	body := []byte(fmt.Sprintf(`{"cmd":"inspect","session_id":%q,"goal_id":%q}`, f.sid, f.gid))
	_, answered := f.e.KeepInFlight(context.Background(), "inspect", body)
	defer answered()
	require.Eventually(t, func() bool { return len(inFlightFiles(t, f.faults)) == 1 }, 5*time.Second, 5*time.Millisecond)

	// The serve is stopped: its files are a dead process's from here on.
	files, err := filepath.Glob(filepath.Join(f.faults, fmt.Sprintf("serve-%d-*.inflight", os.Getpid())))
	require.NoError(t, err)
	require.Len(t, files, 1)
	stopped := deadProcess(t)
	require.NoError(t, os.Rename(files[0], filepath.Join(f.faults, fmt.Sprintf("serve-%d-1.inflight", stopped))))

	view, err := ViewFaults(f.faults, false)
	require.NoError(t, err)
	require.Equal(t, 1, view.Open)
	row := view.Faults[0]
	assert.Equal(t, "serve", row.Command)
	assert.Contains(t, row.Panic, "ended with no report while 1 request(s) were in flight")
	require.Len(t, row.InFlight, 1)
	assert.Equal(t, FaultRowInFlight{Command: "inspect", Session: f.sid, GoalID: f.gid}, row.InFlight[0])
	record, err := ReadFault(f.faults, row.ID)
	require.NoError(t, err)
	require.Len(t, record.InFlight, 1)
	assert.JSONEq(t, string(body), string(record.InFlight[0].RPCBody), "the request is on record to be sent again")
}

// deadProcess is the id of a process that has ended: `true`, which
// starts and ends at once. This binary run again would do, at the cost
// of loading the corpus each time.
func deadProcess(t *testing.T) int {
	t.Helper()
	child := exec.Command("true")
	require.NoError(t, child.Run())
	return child.ProcessState.Pid()
}

// TestCollectCrashes_AProcessThatIsGoneLeavesAFaultRecord: the crash
// report and the in-flight requests a dead serve left become one open
// fault record naming its build, and its files are removed. A process
// that left neither ended in order and leaves no record; the files of a
// process that still runs are not touched.
func TestCollectCrashes_AProcessThatIsGoneLeavesAFaultRecord(t *testing.T) {
	store := t.TempDir()
	write := func(name, content string) {
		require.NoError(t, os.WriteFile(filepath.Join(store, name), []byte(content), 0o644))
	}
	crashed, ended, running := deadProcess(t), deadProcess(t), os.Getpid()
	write(fmt.Sprintf("serve-%d.json", crashed), `{"pid":1,"binary":{"revision":"87bd750ae","registry_fingerprint":"abc"}}`)
	write(fmt.Sprintf("serve-%d.crash", crashed),
		"fatal error: concurrent map writes\n\ngoroutine 41 [running]:\nruntime.fatal(...)\n")
	write(fmt.Sprintf("serve-%d-7.inflight", crashed),
		`{"at":"2026-11-12T08:00:00Z","command":"apply","session":"a-session","lineage_seq":29,"goal_id":"s0_g","tactic":{"type":"by"}}`)
	write(fmt.Sprintf("serve-%d.json", ended), `{"pid":2}`)
	write(fmt.Sprintf("serve-%d.crash", ended), "")
	write(fmt.Sprintf("serve-%d.json", running), `{"pid":3}`)
	write(fmt.Sprintf("serve-%d.crash", running), "")
	write(fmt.Sprintf("serve-%d-1.inflight", running), `{"command":"probe"}`)

	require.NoError(t, CollectCrashes(store))
	records, err := ListFaults(store)
	require.NoError(t, err)
	require.Len(t, records, 1, "one record: the process that crashed")
	record := records[0]
	assert.Equal(t, "serve", record.Command)
	assert.Equal(t, "process", record.Goroutine)
	assert.Equal(t, "fatal error: concurrent map writes", record.Panic)
	assert.Contains(t, record.Stack, "goroutine 41")
	assert.Equal(t, "87bd750ae", record.Binary.Revision)
	assert.Nil(t, record.Ack, "the record is open")
	require.Len(t, record.InFlight, 1)
	assert.Equal(t, "a-session", record.InFlight[0].Session)
	assert.Equal(t, 29, record.InFlight[0].LineageSeq)
	assert.Equal(t, "by", record.InFlight[0].Tactic.Type)

	left, err := os.ReadDir(store)
	require.NoError(t, err)
	var names []string
	for _, entry := range left {
		names = append(names, entry.Name())
	}
	assert.ElementsMatch(t, []string{
		record.ID + ".json",
		fmt.Sprintf("serve-%d.json", running),
		fmt.Sprintf("serve-%d.crash", running),
		fmt.Sprintf("serve-%d-1.inflight", running),
	}, names, "the dead processes' files are gone, the running one's stay")

	require.NoError(t, CollectCrashes(store), "collecting again finds nothing new")
	records, err = ListFaults(store)
	require.NoError(t, err)
	assert.Len(t, records, 1)
}

// TestCollectCrashes_AKilledProcessIsNamedByItsInFlightRequests: a
// process that ended with no report, with a request in flight, was
// killed; the record says so and holds the request.
func TestCollectCrashes_AKilledProcessIsNamedByItsInFlightRequests(t *testing.T) {
	store := t.TempDir()
	killed := deadProcess(t)
	require.NoError(t, os.WriteFile(filepath.Join(store, fmt.Sprintf("serve-%d.crash", killed)), nil, 0o644))
	require.NoError(t, os.WriteFile(filepath.Join(store, fmt.Sprintf("serve-%d-3.inflight", killed)),
		[]byte(`{"command":"probe","session":"a-session"}`), 0o644))
	require.NoError(t, CollectCrashes(store))
	records, err := ListFaults(store)
	require.NoError(t, err)
	require.Len(t, records, 1)
	assert.Contains(t, records[0].Panic, "ended with no report while 1 request(s) were in flight")
	require.Len(t, records[0].InFlight, 1)
	assert.Equal(t, "probe", records[0].InFlight[0].Command)
}
