// fault.go — an engine fault: a panic that marks a defect of the engine
// rather than a failure of the move that met it. The engine writes one
// record per fault under its fault store, marks the response of the
// command that met it, and the session that met it takes no further
// move until the record is acknowledged.
//
// What is a fault. A panic that leaves a command — a tactic run by
// apply, probe or batch-apply; any other command, at the /rpc handler —
// is one, whatever its value: a command reports a failure by an error.
// Inside a tactic whose failures are panics (by, by_induction, the
// kits) a fault is a panic carried off another goroutine (utils.Fault,
// refuter.SearchFault), a failed assertion or an error of the Go
// runtime, and the recover that turns the tactic's panics into its
// error lets those pass (utils.Failure).
//
// The record does not depend on who reads the response: it is written
// before the response is, to a store that outlives the process, and
// `xugo faults` lists the ones nobody has acknowledged.

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
	"slices"
	"strings"
	"sync"
	"time"
	"uuid"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	extprop "github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/euc-ai/xugo/utils"
)

// WithFaultStore points the engine at the directory fault records are
// written under, one file per fault (the serve points it at
// <data-dir>/faults). Empty = no file: a fault still marks its response
// and its session, and its stack goes to stderr.
func WithFaultStore(dir string) EngineOption {
	return func(e *Engine) { e.faultStore = dir }
}

// EngineFault is the mark a response carries when its command met an
// engine fault: the record's id, where the engine broke and with what,
// and the record's file (empty when the engine has no fault store).
type EngineFault struct {
	ID     string `json:"id"`
	Site   string `json:"site"`
	Panic  string `json:"panic"`
	Record string `json:"record,omitempty"`
}

// FaultRecord is one engine fault as the engine wrote it down: the
// request that met it, the goal it ran on, and the panic.
type FaultRecord struct {
	ID string    `json:"id"`
	At time.Time `json:"at"`
	// Binary names the engine that broke, so a reader can tell a fault
	// of a build since replaced from one the tree still has.
	Binary FaultBinary `json:"binary"`

	// Command is the command that met the fault. RPCBody is its request
	// body as /rpc received it, to be sent again as it is; absent for a
	// command run outside the serve.
	Command string          `json:"command"`
	RPCBody json.RawMessage `json:"rpc_body,omitempty"`

	// Session is the session the command ran in, with its family
	// binding; LineageSeq is how many events its lineage held when the
	// command arrived, which is the state a resume of a copy of the
	// session reaches.
	Session    string   `json:"session,omitempty"`
	Family     string   `json:"family,omitempty"`
	Imports    []string `json:"imports,omitempty"`
	LineageSeq int      `json:"lineage_seq,omitempty"`

	// Goal is the sequent the tactic ran on, and Tactic the tactic in
	// the lineage's form (inline props as blobs), under BudgetMs.
	Goal     *FaultGoal     `json:"goal,omitempty"`
	Tactic   *lineageTactic `json:"tactic,omitempty"`
	BudgetMs int            `json:"budget_ms,omitempty"`

	// Panic is the value panicked with and Site where; Stack is the
	// stack of the goroutine that panicked. Goroutine says whether that
	// was the request's own ("request") or one a search or a fan-out
	// started ("worker"); for a worker RaisedAt is the request
	// goroutine's stack where the fault was raised on it.
	Panic     string `json:"panic"`
	Site      string `json:"site,omitempty"`
	Goroutine string `json:"goroutine"`
	Stack     string `json:"stack"`
	RaisedAt  string `json:"raised_at,omitempty"`
	// Refuted is the sequent the refutation ran on, for a fault of a
	// search: what a test of the refuter starts from.
	Refuted *FaultSequent `json:"refuted,omitempty"`
	// Late: the fault was met after its request had answered (a
	// contradiction check its search did not wait for), so no response
	// carries its mark.
	Late bool `json:"late,omitempty"`
	// InFlight, on the record of a serve whose process ended
	// (fault_crash.go; Command "serve", Goroutine "process", Stack the
	// runtime's report): the tactic runs it had not answered.
	InFlight []FaultInFlight `json:"in_flight,omitempty"`
	// Overrun, on the record of a run that ended well past its deadline
	// (overrun.go): Panic says so in a line, Stack is the stack of the
	// cut that ended the run, and no session is locked.
	Overrun *FaultOverrun `json:"overrun,omitempty"`

	// Ack is the acknowledgment: who handled the fault says what was
	// done. A record without one is open.
	Ack *FaultAck `json:"ack,omitempty"`
}

// FaultBinary identifies a build: the commit it was built from (Dirty
// when the tree had changes) and the fingerprint of the registry it
// linked (registry.Fingerprint).
type FaultBinary struct {
	Revision            string `json:"revision,omitempty"`
	Dirty               bool   `json:"dirty,omitempty"`
	RegistryFingerprint string `json:"registry_fingerprint"`
}

// FaultGoal is the goal a faulting tactic ran on. Blob is the pooled
// prop (ext.MarshalPropBlob), exact: ext.UnmarshalPropBlob rebuilds the
// sequent in a test. Closed is the sequent's closed reading as parser
// text, which `add-goal` takes; Statement is the display form.
type FaultGoal struct {
	GoalID    string `json:"goal_id"`
	Section   int    `json:"section"`
	Statement string `json:"statement"`
	Closed    string `json:"closed,omitempty"`
	Blob      []byte `json:"blob,omitempty"`
}

// FaultSequent is a sequent by its display form and its pooled blob.
type FaultSequent struct {
	Statement string `json:"statement"`
	Blob      []byte `json:"blob,omitempty"`
}

// FaultAck acknowledges a fault: Note says what was done about it.
type FaultAck struct {
	At   time.Time `json:"at"`
	Note string    `json:"note"`
}

// _FaultScope is what a command knows of the request it runs, kept for
// the record of a fault met in it.
type _FaultScope struct {
	command    string
	rpcBody    []byte
	session    *Session
	lineageSeq int
	goalID     string
	section    int
	goal       core.Prop
	tactic     *TacticReq
	budgetMs   int
}

// _RPCRequestKey is the context key of WithRPCRequest.
type _RPCRequestKey struct{}

// WithRPCRequest marks ctx with the request body a command was called
// with over /rpc, for the record of a fault met in it.
func WithRPCRequest(ctx context.Context, body []byte) context.Context {
	return context.WithValue(ctx, _RPCRequestKey{}, body)
}

// faultScope is the scope of a command of session s (nil for a
// command that names none), read when the command starts.
func faultScope(ctx context.Context, s *Session, command string) *_FaultScope {
	scope := &_FaultScope{command: command, session: s}
	scope.rpcBody, _ = ctx.Value(_RPCRequestKey{}).([]byte)
	if s != nil && s.lineage != nil {
		scope.lineageSeq = len(s.lineage.Events)
	}
	return scope
}

// onGoal adds the goal a tactic runs on to the scope.
func (scope *_FaultScope) onGoal(goalID string, entry *goalEntry, tactic TacticReq, budgetMs int) *_FaultScope {
	scope.goalID, scope.section, scope.goal = goalID, entry.sectionID, entry.node.Goal
	scope.tactic, scope.budgetMs = &tactic, budgetMs
	return scope
}

// runTactic is runTacticOnClone on the goal of entry, read at the
// command's boundary: a panic out of the tactic is an engine fault,
// recorded and returned in place of the clone and the error. A search
// the tactic starts hands a fault it meets after answering to the same
// record (refuter.WithLateFaultReport). The session lock is held.
//
// While the tactic runs the request is kept in the fault store
// (inFlight), for the death of the process no recover reads; a request
// called over /rpc is kept there for as long as its command runs,
// tactic or not (KeepInFlight).
//
// A session replaying its lineage runs under the cache-only context,
// where a certificate the store lacks surfaces as a panic the resume
// reads as the divergence; there only what is a fault by its value is
// one, and every other panic goes up.
//
// A run its context ended inside a unit of work (a utils.Cut) is no
// fault: it is returned as the error _CutOffError, and nothing is
// recorded.
func (e *Engine) runTactic(ctx context.Context, scope *_FaultScope) (clone *proof.GoalStackNode, fault *EngineFault, err error) {
	s := scope.session
	ctx = refuter.WithLateFaultReport(ctx, func(late refuter.SearchFault) { e.lateFault(scope, late) })
	defer func() {
		r := recover()
		if r == nil {
			return
		}
		if cut, ok := utils.AsCut(r); ok {
			clone, fault, err = nil, nil, _CutOffError{tactic: scope.tactic.Type, cut: cut, stack: string(debug.Stack())}
			return
		}
		if s.replaying && !utils.IsFault(r) {
			panic(r)
		}
		clone, err = nil, nil
		fault = e.fileFault(s, scope.record(r, string(debug.Stack())))
	}()
	defer e.inFlight(ctx, scope)()
	clone, err = e.runTacticOnClone(ctx, s, scope.goal, *scope.tactic)
	return clone, nil, err
}

// lateFault records a fault a search of the scope's request met after
// the search had answered: on a goroutine of the search's contradiction
// pool, with the request gone or going on. It takes the session lock.
func (e *Engine) lateFault(scope *_FaultScope, late refuter.SearchFault) {
	record := scope.record(late, "")
	record.Late = true
	scope.session.mu.Lock()
	defer scope.session.mu.Unlock()
	e.fileFault(scope.session, record)
}

// RecordCommandFault records the panic r as an engine fault of command,
// called with the request body: the /rpc handler's reading of a panic
// that left a command. The session the body names, when it names a live
// one, is the session that met the fault. It is called from the
// deferred function that recovered r.
func (e *Engine) RecordCommandFault(command string, body []byte, r any) *EngineFault {
	var named struct {
		SessionID string `json:"session_id"`
	}
	_ = json.Unmarshal(body, &named)
	e.mu.Lock()
	s := e.sessions[named.SessionID]
	e.mu.Unlock()
	scope := faultScope(WithRPCRequest(context.Background(), body), nil, command)
	stack := string(debug.Stack())
	if s == nil {
		return e.fileFault(nil, scope.record(r, stack))
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	scope.session = s
	if s.lineage != nil {
		scope.lineageSeq = len(s.lineage.Events)
	}
	return e.fileFault(s, scope.record(r, stack))
}

// record is the record of the recovered panic value r for the scope's
// request. stack is the stack of the goroutine that recovered r, taken
// in the deferred function that did; "" for a fault no request
// goroutine recovered.
func (scope *_FaultScope) record(r any, stack string) FaultRecord {
	now := time.Now().UTC()
	record := FaultRecord{
		ID:         now.Format("20060102T150405Z") + "-" + uuid.New().String()[:8],
		At:         now,
		Binary:     faultBinary(),
		Command:    scope.command,
		LineageSeq: scope.lineageSeq,
		BudgetMs:   scope.budgetMs,
	}
	if json.Valid(scope.rpcBody) {
		record.RPCBody = json.RawMessage(scope.rpcBody)
	}
	if s := scope.session; s != nil {
		record.Session = s.ID
		record.Family, record.Imports = s.familyNames()
	}
	if scope.goal != nil {
		record.Goal = &FaultGoal{
			GoalID:    scope.goalID,
			Section:   scope.section,
			Statement: printed(func() string { return scope.session.Spelling().Prop(scope.goal) }),
			Closed:    printed(func() string { return proof.ClosedSpelling(scope.goal) }),
		}
		record.Goal.Blob, _ = ext.MarshalPropBlob(scope.goal)
	}
	if scope.tactic != nil {
		if tactic, err := lineageTacticOf(*scope.tactic); err == nil {
			record.Tactic = &tactic
		}
	}

	if carried, ok := utils.AsFault(r); ok {
		record.Panic, record.Site, record.Stack = fmt.Sprint(carried.Value), carried.Site, carried.Stack
		record.Goroutine = "worker"
		if stack != "" && goroutineOf(stack) == goroutineOf(carried.Stack) {
			record.Goroutine = "request"
		} else {
			record.RaisedAt = stack
		}
	} else {
		record.Panic, record.Site, record.Stack = fmt.Sprint(r), utils.PanicSite(), stack
		record.Goroutine = "request"
	}
	var search refuter.SearchFault
	if err, ok := r.(error); ok && errors.As(err, &search) && search.Goal != nil {
		record.Refuted = &FaultSequent{Statement: printed(func() string { return extprop.PrintProp(search.Goal) })}
		record.Refuted.Blob, _ = ext.MarshalPropBlob(search.Goal)
	}
	return record
}

// printed is a statement's text for a fault record. A printer that
// panics on the statement does not cost the record: the field says so.
func printed(print func() string) (text string) {
	defer func() {
		if r := recover(); r != nil {
			text = fmt.Sprintf("(the statement did not print: %v)", r)
		}
	}()
	return print()
}

// goroutineHeader is the first line of a stack: "goroutine 12 [running]:".
var goroutineHeader = regexp.MustCompile(`^goroutine (\d+) `)

// goroutineOf is the id of the goroutine a stack is of, "" when the
// text opens with no header.
func goroutineOf(stack string) string {
	if m := goroutineHeader.FindStringSubmatch(stack); m != nil {
		return m[1]
	}
	return ""
}

// faultBinary identifies this process's build.
var faultBinary = sync.OnceValue(func() FaultBinary {
	binary := FaultBinary{}
	_, binary.RegistryFingerprint = registry.Fingerprint()
	if info, ok := debug.ReadBuildInfo(); ok {
		for _, setting := range info.Settings {
			switch setting.Key {
			case "vcs.revision":
				binary.Revision = setting.Value
			case "vcs.modified":
				binary.Dirty = setting.Value == "true"
			}
		}
	}
	return binary
})

// faultObserver, when set, is handed every record fileFault files. A
// command answers a fault as a failed move, which a test asserting a
// refusal reads as the refusal: the engine's test binary sets the
// observer to fail a run in which a test met a fault it did not expect.
var faultObserver func(*FaultRecord)

// fileFault writes record to the fault store, says so on stderr with
// the stack, and marks the session that met the fault (nil for none),
// whose lock is held: the fault joins its lineage and the session takes
// no further move until the record is acknowledged. It returns the mark
// for the response.
func (e *Engine) fileFault(s *Session, record FaultRecord) *EngineFault {
	if faultObserver != nil {
		faultObserver(&record)
	}
	mark := &EngineFault{ID: record.ID, Site: record.Site, Panic: record.Panic}
	if e.faultStore != "" {
		path := faultRecordPath(e.faultStore, record.ID)
		if err := writeFaultRecord(path, &record); err != nil {
			fmt.Fprintf(os.Stderr, "[fault] %s: the record was not written: %v\n", record.ID, err)
		} else {
			mark.Record = path
		}
	}
	fmt.Fprintf(os.Stderr, "[fault] engine fault %s in %s at %s: %s\n%s\n",
		record.ID, record.Command, record.Site, record.Panic, record.Stack)
	if s != nil {
		s.faults = append(s.faults, record.ID)
		s.recordFault(record.ID, record.Command, record.Site)
	}
	return mark
}

// message is the mark as a diagnostic's text.
func (f *EngineFault) message(what string) string {
	text := fmt.Sprintf("engine fault %s: %s broke an engine invariant at %s: %s\n"+
		"This is a defect of the engine, not a failure of the move: report ENGINE-FAULT with the id. "+
		"The session takes no further move until the fault is acknowledged.",
		f.ID, what, f.Site, f.Panic)
	if f.Record != "" {
		text += "\nThe record (the request, the goal, the stack): " + f.Record
	}
	return text
}

// faultRefusal is why the session takes no move: it met an engine fault
// whose record is not acknowledged. nil when it met none, or every one
// is acknowledged. A session replaying its lineage re-issues the moves
// it took, and is not refused. The session lock is held.
func (s *Session) faultRefusal() error {
	if s.replaying {
		return nil
	}
	s.faults = slices.DeleteFunc(s.faults, func(id string) bool {
		return faultAcknowledged(s.faultStore, id)
	})
	if len(s.faults) == 0 {
		return nil
	}
	id := s.faults[0]
	if s.faultStore == "" {
		return fmt.Errorf("session %s met engine fault %s and takes no further move: report ENGINE-FAULT with that id. "+
			"This engine keeps no fault store (no --data-dir), so nothing acknowledges the fault and the refusal stands; "+
			"inspect, session-lineage, list-checkpoints, dump-section, emit-section and retrieve still answer", s.ID, id)
	}
	return fmt.Errorf("session %s met engine fault %s and takes no further move until it is acknowledged: "+
		"report ENGINE-FAULT with that id and stop. The record is %s; `xugo --data-dir <dir> faults ack %s --note \"…\"`, "+
		"run by whoever handled the fault, lifts the refusal. "+
		"inspect, session-lineage, list-checkpoints, dump-section, emit-section and retrieve still answer",
		s.ID, id, faultRecordPath(s.faultStore, id), id)
}

// FaultRefusal is faultRefusal for a caller that does not hold the
// session lock: the add-goal door.
func (s *Session) FaultRefusal() error {
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.faultRefusal()
}

// --- the fault store ---

// isFaultID reports whether id has the form the engine mints, so an id
// a caller supplies is checked before it is joined into a path.
var isFaultID = regexp.MustCompile(`^\d{8}T\d{6}Z-[0-9a-f]{8}$`).MatchString

func faultRecordPath(store, id string) string { return filepath.Join(store, id+".json") }

// writeFaultRecord writes the record atomically (temp + rename).
func writeFaultRecord(path string, record *FaultRecord) error {
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		return err
	}
	data, err := json.MarshalIndent(record, "", " ")
	if err != nil {
		return err
	}
	tmp := path + ".tmp"
	if err := os.WriteFile(tmp, data, 0o644); err != nil {
		return err
	}
	return os.Rename(tmp, path)
}

func readFaultRecord(path string) (*FaultRecord, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var record FaultRecord
	if err := json.Unmarshal(data, &record); err != nil {
		return nil, fmt.Errorf("%s does not parse: %w", path, err)
	}
	return &record, nil
}

// faultAcknowledged reports whether the record of fault id under store
// carries an acknowledgment. A record that cannot be read is not
// acknowledged.
func faultAcknowledged(store, id string) bool {
	if store == "" {
		return false
	}
	record, err := readFaultRecord(faultRecordPath(store, id))
	return err == nil && record.Ack != nil
}

// ListFaults reads the fault records under store, newest first. A store
// that does not exist holds none.
func ListFaults(store string) ([]FaultRecord, error) {
	entries, err := os.ReadDir(store)
	if errors.Is(err, os.ErrNotExist) {
		return nil, nil
	}
	if err != nil {
		return nil, err
	}
	var records []FaultRecord
	for _, entry := range entries {
		id, isRecord := strings.CutSuffix(entry.Name(), ".json")
		if entry.IsDir() || !isRecord || !isFaultID(id) {
			continue
		}
		record, err := readFaultRecord(filepath.Join(store, entry.Name()))
		if err != nil {
			return nil, err
		}
		records = append(records, *record)
	}
	slices.SortFunc(records, func(a, b FaultRecord) int { return strings.Compare(b.ID, a.ID) })
	return records, nil
}

// AcknowledgeFault writes the acknowledgment of fault id under store:
// note says what was done about the fault. A session locked by the
// fault takes moves again from its next request.
func AcknowledgeFault(store, id, note string) (*FaultRecord, error) {
	if !isFaultID(id) {
		return nil, fmt.Errorf("%q is not a fault id", id)
	}
	if strings.TrimSpace(note) == "" {
		return nil, errors.New("an acknowledgment says what was done about the fault: reproduced and fixed in <commit>, or put to the user")
	}
	path := faultRecordPath(store, id)
	record, err := readFaultRecord(path)
	if errors.Is(err, os.ErrNotExist) {
		return nil, fmt.Errorf("no fault %s is on record under %s", id, store)
	}
	if err != nil {
		return nil, err
	}
	record.Ack = &FaultAck{At: time.Now().UTC(), Note: strings.TrimSpace(note)}
	return record, writeFaultRecord(path, record)
}

// FaultsView is the fault store as `xugo faults` prints it: how many
// records are open and how many acknowledged, and one row per listed
// record, newest first.
type FaultsView struct {
	Open         int        `json:"open"`
	Acknowledged int        `json:"acknowledged"`
	Faults       []FaultRow `json:"faults"`
}

// FaultRow is one fault record in the listing: what tells a reader
// which fault it is, and the file that holds the rest.
type FaultRow struct {
	ID        string    `json:"id"`
	At        time.Time `json:"at"`
	Command   string    `json:"command"`
	Session   string    `json:"session,omitempty"`
	GoalID    string    `json:"goal_id,omitempty"`
	Tactic    string    `json:"tactic,omitempty"`
	Site      string    `json:"site,omitempty"`
	Panic     string    `json:"panic"`
	Goroutine string    `json:"goroutine"`
	Late      bool      `json:"late,omitempty"`
	// InFlight are the requests a serve had not answered when its
	// process ended.
	InFlight []FaultRowInFlight `json:"in_flight,omitempty"`
	// OverrunMs is set on the record of a run that ended well past its
	// deadline (overrun.go): how many milliseconds past. Such a record
	// locks no session.
	OverrunMs int       `json:"overrun_ms,omitzero"`
	Record    string    `json:"record"`
	Ack       *FaultAck `json:"ack,omitempty"`
}

// FaultRowInFlight names one request in flight in the listing: its
// command, its session, the goal its body named, and the tactic it was
// running, if it was running one.
type FaultRowInFlight struct {
	Command string `json:"command"`
	Session string `json:"session,omitempty"`
	GoalID  string `json:"goal_id,omitempty"`
	Tactic  string `json:"tactic,omitempty"`
}

// ViewFaults reads the fault store for the listing, after turning what
// dead serves left there into records (CollectCrashes). The rows are
// the open records, and the acknowledged ones too when all is set.
func ViewFaults(store string, all bool) (*FaultsView, error) {
	if err := CollectCrashes(store); err != nil {
		return nil, err
	}
	records, err := ListFaults(store)
	if err != nil {
		return nil, err
	}
	view := &FaultsView{Faults: []FaultRow{}}
	for _, record := range records {
		if record.Ack != nil {
			view.Acknowledged++
			if !all {
				continue
			}
		} else {
			view.Open++
		}
		row := FaultRow{
			ID: record.ID, At: record.At, Command: record.Command, Session: record.Session,
			Site: record.Site, Panic: clipRunes(record.Panic, 300), Goroutine: record.Goroutine,
			Late: record.Late, Record: faultRecordPath(store, record.ID), Ack: record.Ack,
		}
		if record.Goal != nil {
			row.GoalID = record.Goal.GoalID
		}
		if record.Tactic != nil {
			row.Tactic = record.Tactic.Type
		}
		for _, running := range record.InFlight {
			in := FaultRowInFlight{Command: running.Command, Session: running.Session, GoalID: running.GoalID}
			if running.Tactic != nil {
				in.Tactic = running.Tactic.Type
			}
			row.InFlight = append(row.InFlight, in)
		}
		if record.Overrun != nil {
			row.OverrunMs = record.Overrun.LateMs
		}
		view.Faults = append(view.Faults, row)
	}
	return view, nil
}

// ReadFault is the record of fault id under store, whole.
func ReadFault(store, id string) (*FaultRecord, error) {
	if !isFaultID(id) {
		return nil, fmt.Errorf("%q is not a fault id", id)
	}
	record, err := readFaultRecord(faultRecordPath(store, id))
	if errors.Is(err, os.ErrNotExist) {
		return nil, fmt.Errorf("no fault %s is on record under %s", id, store)
	}
	return record, err
}
