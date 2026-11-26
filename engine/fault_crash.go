// fault_crash.go — what a serve leaves in the fault store for the death
// no recover reads: a runtime fatal error, a panic on a goroutine
// nothing guards, a kill. While it runs, a serve keeps three kinds of
// file under the store, named by its process id:
//
//   - serve-<pid>.json: the build it runs;
//   - serve-<pid>.crash: the runtime's own report of the unrecovered
//     panic or fatal error that ends the process
//     (debug.SetCrashOutput), empty until then;
//   - serve-<pid>-<n>.inflight: one request it has not answered,
//     whatever the command: written when a tactic run of the request
//     starts, or once the request has run InFlightAfter, whichever
//     comes first, and removed when the request answers.
//
// CollectCrashes, run when a serve starts and by `xugo faults`, turns
// what a process that is gone left there into a fault record: the
// report and the requests that were in flight when it ended.

package engine

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"runtime/debug"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
	"uuid"
)

// FaultInFlight is one request a serve had not answered: the request as
// a fault record holds it, without the goal, which the session's
// lineage at LineageSeq rebuilds. Tactic and BudgetMs are set while a
// tactic run of the request is going; a command that is no tactic run
// (inspect, add-goal, session-create, emit-section) is named by
// Command, Session and the GoalID its body names.
type FaultInFlight struct {
	At         time.Time       `json:"at"`
	Command    string          `json:"command"`
	Session    string          `json:"session,omitempty"`
	LineageSeq int             `json:"lineage_seq,omitempty"`
	GoalID     string          `json:"goal_id,omitempty"`
	RPCBody    json.RawMessage `json:"rpc_body,omitempty"`
	Tactic     *lineageTactic  `json:"tactic,omitempty"`
	BudgetMs   int             `json:"budget_ms,omitempty"`
}

// _ServeMark is serve-<pid>.json: the build a serve runs.
type _ServeMark struct {
	PID     int         `json:"pid"`
	Started time.Time   `json:"started"`
	Binary  FaultBinary `json:"binary"`
}

var (
	serveFile    = regexp.MustCompile(`^serve-(\d+)\.(json|crash)$`)
	inFlightFile = regexp.MustCompile(`^serve-(\d+)-\d+\.inflight$`)
)

// OpenCrashReport makes this process a serve of the fault store: its
// build is marked there and the runtime's report of an unrecovered
// panic or a fatal error goes to a file there as well as to stderr. The
// returned function ends the marking for an exit that is none of those.
func OpenCrashReport(store string) (func(), error) {
	if err := os.MkdirAll(store, 0o755); err != nil {
		return nil, err
	}
	stem := filepath.Join(store, fmt.Sprintf("serve-%d", os.Getpid()))
	mark, err := json.Marshal(_ServeMark{PID: os.Getpid(), Started: time.Now().UTC(), Binary: faultBinary()})
	if err != nil {
		return nil, err
	}
	if err := os.WriteFile(stem+".json", mark, 0o644); err != nil {
		return nil, err
	}
	report, err := os.Create(stem + ".crash")
	if err != nil {
		return nil, err
	}
	if err := debug.SetCrashOutput(report, debug.CrashOptions{}); err != nil {
		report.Close()
		return nil, err
	}
	return func() {
		_ = debug.SetCrashOutput(nil, debug.CrashOptions{})
		report.Close()
		os.Remove(stem + ".crash")
		os.Remove(stem + ".json")
	}, nil
}

// inFlightSeq numbers this process's in-flight files.
var inFlightSeq atomic.Int64

// InFlightAfter is how long a request runs before the fault store
// keeps it in flight. A request that answers sooner writes nothing,
// unless it runs a tactic, which is kept from its start. A variable so
// that a test can shorten it.
var InFlightAfter = 2 * time.Second

// _InFlightRequest is one request the fault store keeps while its
// command runs: one file, written at most once per change, removed when
// the request answers.
type _InFlightRequest struct {
	store string
	path  string

	mu      sync.Mutex
	running FaultInFlight
	// due: the request has run InFlightAfter, so its file stays until
	// it answers. written: the file is on disk. answered: the request
	// is over and nothing more is written.
	due, written, answered bool
	// lineageSeq reads the session's position where no tactic run has
	// set it; nil for a request that names no live session.
	lineageSeq func() int
}

// _InFlightKey is the context key of the request KeepInFlight keeps.
type _InFlightKey struct{}

// KeepInFlight keeps the request of command, called over /rpc with
// body, in the fault store from the time it has run InFlightAfter until
// it answers, so that a serve stopped while the command runs leaves the
// request behind whatever the command is. It returns the context the
// command runs under, through which a tactic run joins the same file,
// and what ends the keeping when the command has answered. An engine
// with no fault store keeps nothing.
func (e *Engine) KeepInFlight(ctx context.Context, command string, body []byte) (context.Context, func()) {
	if e.faultStore == "" {
		return ctx, func() {}
	}
	var named struct {
		SessionID string `json:"session_id"`
		GoalID    string `json:"goal_id"`
	}
	_ = json.Unmarshal(body, &named)
	request := &_InFlightRequest{
		store: e.faultStore,
		path:  filepath.Join(e.faultStore, fmt.Sprintf("serve-%d-%d.inflight", os.Getpid(), inFlightSeq.Add(1))),
		running: FaultInFlight{
			At:      time.Now().UTC(),
			Command: command,
			Session: named.SessionID,
			GoalID:  named.GoalID,
		},
	}
	if json.Valid(body) {
		request.running.RPCBody = json.RawMessage(body)
	}
	// The command holds the session lock while it runs, so the position
	// is read off the session's own count of its lineage, which no lock
	// guards.
	request.lineageSeq = func() int {
		e.mu.Lock()
		s := e.sessions[named.SessionID]
		e.mu.Unlock()
		if s == nil {
			return 0
		}
		return int(s.lineageLen.Load())
	}
	timer := time.AfterFunc(InFlightAfter, func() {
		request.mu.Lock()
		defer request.mu.Unlock()
		if request.answered {
			return
		}
		request.due = true
		if request.running.LineageSeq == 0 {
			request.running.LineageSeq = request.lineageSeq()
		}
		request.write()
	})
	return context.WithValue(ctx, _InFlightKey{}, request), func() {
		timer.Stop()
		request.mu.Lock()
		defer request.mu.Unlock()
		request.answered = true
		request.remove()
	}
}

// write puts the request on disk as it stands. The lock is held.
func (r *_InFlightRequest) write() {
	data, err := json.Marshal(r.running)
	if err == nil {
		if err = os.MkdirAll(r.store, 0o755); err == nil {
			err = os.WriteFile(r.path, data, 0o644)
		}
	}
	if err != nil {
		fmt.Fprintf(os.Stderr, "[fault] the in-flight request was not written: %v\n", err)
		return
	}
	r.written = true
}

// remove takes the request's file off disk. The lock is held.
func (r *_InFlightRequest) remove() {
	if r.written {
		os.Remove(r.path)
		r.written = false
	}
}

// tacticRun marks the request as running the scope's tactic, on disk at
// once, and returns what ends the mark when the run has answered: the
// file then goes if the request is not yet InFlightAfter old, and
// otherwise stays without the tactic.
func (r *_InFlightRequest) tacticRun(scope *_FaultScope) (answered func()) {
	r.mu.Lock()
	defer r.mu.Unlock()
	if r.answered {
		return func() {}
	}
	r.running.Command = scope.command
	r.running.LineageSeq = scope.lineageSeq
	r.running.GoalID = scope.goalID
	r.running.BudgetMs = scope.budgetMs
	if scope.session != nil {
		r.running.Session = scope.session.ID
	}
	if scope.tactic != nil {
		if tactic, err := lineageTacticOf(*scope.tactic); err == nil {
			r.running.Tactic = &tactic
		}
	}
	r.write()
	return func() {
		r.mu.Lock()
		defer r.mu.Unlock()
		if r.answered {
			return
		}
		r.running.Tactic, r.running.BudgetMs = nil, 0
		if r.due {
			r.write()
		} else {
			r.remove()
		}
	}
}

// inFlight keeps the scope's request in the fault store while its
// tactic runs, and returns what ends that when the run has answered. A
// request KeepInFlight keeps (one called over /rpc) is marked in its own
// file; a tactic run outside one gets a file for the run. An engine
// with no fault store keeps nothing.
func (e *Engine) inFlight(ctx context.Context, scope *_FaultScope) (answered func()) {
	if e.faultStore == "" {
		return func() {}
	}
	if request, ok := ctx.Value(_InFlightKey{}).(*_InFlightRequest); ok {
		return request.tacticRun(scope)
	}
	run := &_InFlightRequest{
		store:   e.faultStore,
		path:    filepath.Join(e.faultStore, fmt.Sprintf("serve-%d-%d.inflight", os.Getpid(), inFlightSeq.Add(1))),
		running: FaultInFlight{At: time.Now().UTC()},
	}
	if json.Valid(scope.rpcBody) {
		run.running.RPCBody = json.RawMessage(scope.rpcBody)
	}
	run.tacticRun(scope)
	return func() {
		run.mu.Lock()
		defer run.mu.Unlock()
		run.answered = true
		run.remove()
	}
}

// CollectCrashes turns what the serves that are gone left under store
// into fault records, one per process: the runtime's report, when the
// process wrote one, and the requests it had not answered. A process
// that left neither ended in order, and its files are removed. The
// files of a process that is still running, this one included, are left
// alone.
func CollectCrashes(store string) error {
	entries, err := os.ReadDir(store)
	if errors.Is(err, os.ErrNotExist) {
		return nil
	}
	if err != nil {
		return err
	}
	left := map[int][]string{}
	for _, entry := range entries {
		m := serveFile.FindStringSubmatch(entry.Name())
		if m == nil {
			m = inFlightFile.FindStringSubmatch(entry.Name())
		}
		if m == nil {
			continue
		}
		pid, _ := strconv.Atoi(m[1])
		left[pid] = append(left[pid], entry.Name())
	}
	for pid, names := range left {
		if pid == os.Getpid() || processRuns(pid) {
			continue
		}
		record := FaultRecord{Command: "serve", Goroutine: "process"}
		var newest time.Time
		for _, name := range names {
			path := filepath.Join(store, name)
			if info, err := os.Stat(path); err == nil && info.ModTime().After(newest) {
				newest = info.ModTime()
			}
			data, err := os.ReadFile(path)
			if err != nil {
				return err
			}
			switch {
			case strings.HasSuffix(name, ".json"):
				var mark _ServeMark
				if json.Unmarshal(data, &mark) == nil {
					record.Binary = mark.Binary
				}
			case strings.HasSuffix(name, ".crash"):
				record.Stack = string(data)
			default:
				var running FaultInFlight
				if err := json.Unmarshal(data, &running); err != nil {
					return fmt.Errorf("%s does not parse: %w", path, err)
				}
				record.InFlight = append(record.InFlight, running)
			}
		}
		if record.Stack != "" || len(record.InFlight) > 0 {
			record.At = newest.UTC()
			record.ID = record.At.Format("20060102T150405Z") + "-" + uuid.New().String()[:8]
			record.Panic = crashHeadline(record.Stack)
			if record.Panic == "" {
				record.Panic = fmt.Sprintf("the serve process %d ended with no report while %d request(s) were in flight",
					pid, len(record.InFlight))
			}
			if err := writeFaultRecord(faultRecordPath(store, record.ID), &record); err != nil {
				return err
			}
		}
		for _, name := range names {
			os.Remove(filepath.Join(store, name))
		}
	}
	return nil
}

// crashHeadline is the line of a runtime crash report that says what
// ended the process: its "panic: …" or "fatal error: …" line, else its
// first line.
func crashHeadline(report string) string {
	lines := strings.Split(strings.TrimSpace(report), "\n")
	for _, line := range lines {
		if strings.HasPrefix(line, "panic: ") || strings.HasPrefix(line, "fatal error: ") {
			return line
		}
	}
	return lines[0]
}

// processRuns reports whether a process with this id exists.
func processRuns(pid int) bool {
	process, err := os.FindProcess(pid)
	if err != nil {
		return false
	}
	err = process.Signal(syscall.Signal(0))
	return err == nil || errors.Is(err, syscall.EPERM)
}
