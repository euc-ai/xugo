// lineage.go — a session's LINEAGE: the ordered record of every move
// that changed its state, persisted as it happens and replayable into
// a fresh engine. This is the persistence the prove/curate merger
// stands on: the seed dissolves into session persistence
// (the editable environment). Two streams:
//
//   - The TRANSCRIPT (lineage.json): what the author did — mode,
//     defines, goals, applies, checkpoints, restores — recorded at the
//     engine API boundary in the form the engine received. Resume
//     re-issues it in order under a cache-only context (CNF refutes
//     replay from the store and never search), with no deadline and
//     past a caller that hangs up, and stops at the FIRST event that
//     no longer applies: the divergence is reported by sequence number
//     and the session stays live at that point, so an unfinished proof
//     is exactly as recoverable as a finished one.
//   - The RECORDS (section_<k>.pb): each proved section's step tree as
//     DetailedProofProto — the same bytes emit renders Go from. Written
//     when a section proves; compared on resume (record_matches), so a
//     re-proof that took a different route is visible rather than
//     silent.
//
// Not persisted, by design: in-memory checkpoints (their creation and
// every restore are events, so a resume rebuilds them, ids mapped);
// session-minted constants (process-global by ruling — replaying the
// define events re-mints them, and a resume into a process that
// already holds the name fails at that event: there is no "same
// definition, reuse" rule, name identity being the editing problem
// rather than this file's).
//
// Recording is always on (the lineage is in memory for every session;
// `session-lineage` reads it); files are written only when the engine
// has a session store (WithSessionStore — the serve points it at
// <data-dir>/sessions).

package engine

import (
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"runtime/debug"
	"slices"
	"strings"
	"time"
	"uuid"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
	"google.golang.org/protobuf/proto"
)

// WithSessionStore points the engine at the directory session lineages
// persist under (one subdirectory per session id). Empty = in-memory
// only (no files, no resume).
func WithSessionStore(dir string) EngineOption {
	return func(e *Engine) { e.sessionStore = dir }
}

// LineageKind names one kind of recorded move.
type LineageKind string

const (
	kindFamily     LineageKind = "family"
	kindDefine     LineageKind = "define"
	kindAddGoal    LineageKind = "add_goal"
	kindApply      LineageKind = "apply"
	kindCheckpoint LineageKind = "checkpoint"
	kindRestore    LineageKind = "restore"
	kindDefer      LineageKind = "defer"
	kindFault      LineageKind = "fault"
)

// LineageEvent is one recorded move. Exactly one payload is set, by
// Kind.
type LineageEvent struct {
	Seq  int         `json:"seq"`
	Kind LineageKind `json:"kind"`
	At   time.Time   `json:"at"`

	Family     *LineageFamily     `json:"family,omitempty"`
	Define     *DefineRequest     `json:"define,omitempty"`
	Goal       *LineageGoal       `json:"goal,omitempty"`
	Apply      *LineageApply      `json:"apply,omitempty"`
	Checkpoint *LineageCheckpoint `json:"checkpoint,omitempty"`
	Restore    *LineageRestore    `json:"restore,omitempty"`
	Defer      *LineageDefer      `json:"defer,omitempty"`
	Fault      *LineageFault      `json:"fault,omitempty"`
}

// LineageFault records an engine fault the session met (fault.go): the
// id of its record, the command that met it and where the engine
// broke. It changes no proof state. A resume reads it as the session
// reads the fault when it happens: no move until the record is
// acknowledged.
type LineageFault struct {
	ID      string `json:"id"`
	Command string `json:"command"`
	Site    string `json:"site"`
}

// LineageDefer records a `defer` (defer.go): the open leaf that became
// a card and a premise of its section. Key is the card's identity (the
// closed statement's normalized key); Statement its printed form.
// Replay re-issues the defer and checks the key it produces.
type LineageDefer struct {
	GoalID  string `json:"goal_id"`
	Section int    `json:"section"`
	Name    string `json:"name"`
	// Entry is the registered name the card lands under — the cite
	// spelling, <family>.<Name>.
	Entry string `json:"entry,omitempty"`
	Note  string `json:"note,omitempty"`
	// Deps are the registered names this defer said the card stands
	// on; replay re-issues them, and the card stands on every defer's.
	Deps      []string `json:"deps,omitempty"`
	Key       string   `json:"key"`
	Statement string   `json:"statement"`
	// StatementTyped is the card's parse-faithful spelling (see
	// FormatStatementTyped), recorded so that `cards` can hand it to
	// the prover attacking the card after the session is gone.
	StatementTyped string `json:"statement_typed,omitempty"`
}

// LineageFamily records the family binding (SetSessionFamily): the
// chapter the session works and the families it imports.
type LineageFamily struct {
	Name    string   `json:"name"`
	Imports []string `json:"imports,omitempty"`
}

// LineageGoal records an add-goal by its statement: the pooled prop
// blob (exact, parse-scope-proof); the printed text is for readers.
type LineageGoal struct {
	Statement string `json:"statement"`
	Blob      []byte `json:"blob,omitempty"`
	Section   int    `json:"section"`
	GoalID    string `json:"goal_id"`
	// NormKey is the goal statement's normalized key — the section's
	// identity in the card index (cards.go): a lineage whose target
	// states a card is that card's attacker, and a section is landed
	// once an entry states its target.
	NormKey string `json:"norm_key,omitempty"`
	// Abbreviations is the table the goal was added with
	// (sectionState.abbreviations), replayed with it: the section's
	// texts are read under it.
	Abbreviations dsl.Abbrev `json:"abbreviations,omitempty"`
}

// LineageApply records a committed tactic: an `apply`, or the winner
// a batch-apply / commit-plan committed (Winner — replayed through the
// batch path, whose post-commit pipeline it went through).
type LineageApply struct {
	GoalID  string        `json:"goal_id"`
	Section int           `json:"section"`
	Tactic  lineageTactic `json:"tactic"`
	// BudgetMs is the budget_ms the apply ran under, for readers:
	// replay runs without it (replayEvent).
	BudgetMs int    `json:"budget_ms,omitempty"`
	Winner   bool   `json:"batch_winner,omitempty"`
	Effect   string `json:"effect,omitempty"`
	// AutoCheckpoint is the id of the auto-checkpoint this apply
	// created (empty when auto-checkpointing is off) — a later restore
	// may name it, so resume maps the recorded id to the new one.
	AutoCheckpoint string `json:"auto_checkpoint,omitempty"`
	// PreCheckpoint is the snapshot holding a direct apply's pre-state,
	// including one a failed attempt created; empty with auto-checkpointing off.
	PreCheckpoint string `json:"pre_checkpoint,omitempty"`
}

// LineageCheckpoint records an explicit checkpoint (its id, so a
// later restore event resolves).
type LineageCheckpoint struct {
	ID   string `json:"id"`
	Name string `json:"name,omitempty"`
}

// LineageRestore records a restore by checkpoint id (explicit or auto).
type LineageRestore struct {
	CheckpointID string `json:"checkpoint_id"`
}

// lineageTactic is TacticReq on the wire: the two inline-Prop fields
// (Lemma / Claim — the back-compat inline forms) travel as pooled
// prop blobs; the outer fields shadow the embedded ones for JSON.
type lineageTactic struct {
	TacticReq
	LemmaBlob []byte `json:"lemma,omitempty"`
	ClaimBlob []byte `json:"claim,omitempty"`
}

func lineageTacticOf(req TacticReq) (lineageTactic, error) {
	lt := lineageTactic{TacticReq: req}
	lt.TacticReq.Lemma, lt.TacticReq.Claim = nil, nil
	var err error
	if req.Lemma != nil {
		if lt.LemmaBlob, err = ext.MarshalPropBlob(req.Lemma); err != nil {
			return lt, fmt.Errorf("lineage: marshal inline lemma: %w", err)
		}
	}
	if req.Claim != nil {
		if lt.ClaimBlob, err = ext.MarshalPropBlob(req.Claim); err != nil {
			return lt, fmt.Errorf("lineage: marshal inline claim: %w", err)
		}
	}
	return lt, nil
}

func (lt lineageTactic) tacticReq(load ext.LoadConstMeta) (TacticReq, error) {
	req := lt.TacticReq
	if len(lt.LemmaBlob) > 0 {
		p, _, err := ext.UnmarshalPropBlob(lt.LemmaBlob, load)
		if err != nil || p == nil {
			return req, fmt.Errorf("lineage: inline lemma does not decode (%v)", err)
		}
		req.Lemma = p
	}
	if len(lt.ClaimBlob) > 0 {
		p, _, err := ext.UnmarshalPropBlob(lt.ClaimBlob, load)
		if err != nil || p == nil {
			return req, fmt.Errorf("lineage: inline claim does not decode (%v)", err)
		}
		req.Claim = p
	}
	return req, nil
}

// sessionLineage is the persisted form.
type sessionLineage struct {
	ID        string         `json:"id"`
	CreatedAt time.Time      `json:"created_at"`
	Events    []LineageEvent `json:"events"`
}

const lineageFileName = "lineage.json"

func lineageDir(store, id string) string { return filepath.Join(store, id) }

// isSessionID reports whether id has the form the engine mints
// (CreateSession): a UUID in lowercase hex and dashes. A session's id
// is its directory's name under the session store, so an id a caller
// supplies is checked before it is joined into a path.
func isSessionID(id string) bool {
	u, err := uuid.Parse(id)
	return err == nil && u.String() == id
}

func sectionRecordPath(store, id string, section int) string {
	return filepath.Join(lineageDir(store, id), fmt.Sprintf("section_%d.pb", section))
}

// record appends one event to the session's lineage and persists it.
// A no-op while the session is replaying its own lineage (the loaded
// events are the truth). Persistence failures are loud on stderr and
// otherwise ignored: the move already happened, and a failed write is
// not a reason to report the apply as failed.
func (s *Session) record(ev LineageEvent) {
	if s.replaying || s.recordingSuppressed > 0 || s.lineage == nil {
		return
	}
	ev.Seq = len(s.lineage.Events) + 1
	ev.At = time.Now()
	s.lineage.Events = append(s.lineage.Events, ev)
	s.lineageLen.Store(int64(len(s.lineage.Events)))
	s.saveLineage()
}

// saveLineage writes lineage.json atomically (temp + rename).
func (s *Session) saveLineage() {
	if s.lineageStore == "" || s.lineage == nil {
		return
	}
	dir := lineageDir(s.lineageStore, s.ID)
	if err := os.MkdirAll(dir, 0o755); err != nil {
		fmt.Fprintf(os.Stderr, "[lineage] session %s: %v\n", s.ID, err)
		return
	}
	data, err := json.MarshalIndent(s.lineage, "", " ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "[lineage] session %s: marshal: %v\n", s.ID, err)
		return
	}
	tmp := filepath.Join(dir, lineageFileName+".tmp")
	if err := os.WriteFile(tmp, data, 0o644); err != nil {
		fmt.Fprintf(os.Stderr, "[lineage] session %s: write: %v\n", s.ID, err)
		return
	}
	if err := os.Rename(tmp, filepath.Join(dir, lineageFileName)); err != nil {
		fmt.Fprintf(os.Stderr, "[lineage] session %s: rename: %v\n", s.ID, err)
	}
}

// recordProvedSections writes the record of every section that has
// proved since the last sweep (a section proves once; a restore that
// rolls it back replaces its sectionState, so a re-proof records
// again). Called after every move that can close a section.
func (s *Session) recordProvedSections() {
	for i, sec := range s.sections {
		if sec.recorded || !sec.root.Proved() {
			continue
		}
		sec.recorded = true
		if s.lineageStore == "" || s.replaying {
			continue
		}
		detailed := sec.root.DetailedProofProto()
		if detailed == nil {
			continue
		}
		data, err := proto.Marshal(detailed)
		if err != nil {
			fmt.Fprintf(os.Stderr, "[lineage] session %s section %d: marshal record: %v\n", s.ID, i, err)
			continue
		}
		if err := os.MkdirAll(lineageDir(s.lineageStore, s.ID), 0o755); err != nil {
			fmt.Fprintf(os.Stderr, "[lineage] session %s: %v\n", s.ID, err)
			continue
		}
		if err := os.WriteFile(sectionRecordPath(s.lineageStore, s.ID, i), data, 0o644); err != nil {
			fmt.Fprintf(os.Stderr, "[lineage] session %s section %d: write record: %v\n", s.ID, i, err)
		}
	}
}

// --- recording hooks (called by the mutating engine paths) ---

func (s *Session) recordFamily(name string, imports []string) {
	s.record(LineageEvent{Kind: kindFamily, Family: &LineageFamily{Name: name, Imports: slices.Clone(imports)}})
}

// familyNames is the session's binding as SessionInfo reports it.
func (s *Session) familyNames() (family string, imports []string) {
	if s.family == nil {
		return "", nil
	}
	for _, f := range s.imports {
		imports = append(imports, f.Name)
	}
	return s.family.Name, imports
}

func (s *Session) recordDefine(req *DefineRequest) {
	copied := *req
	copied.SessionID = ""
	s.record(LineageEvent{Kind: kindDefine, Define: &copied})
}

// recordGoal records a goal added by statement.
func (s *Session) recordGoal(goal core.Prop, section int, goalID string, abbreviations *dsl.AbbreviationTable) {
	if s.replaying || s.lineage == nil {
		return
	}
	blob, err := ext.MarshalPropBlob(goal)
	if err != nil {
		fmt.Fprintf(os.Stderr, "[lineage] session %s: marshal goal: %v\n", s.ID, err)
		return
	}
	s.record(LineageEvent{Kind: kindAddGoal, Goal: &LineageGoal{
		Statement:     s.Spelling().Prop(goal),
		Blob:          blob,
		Section:       section,
		GoalID:        goalID,
		NormKey:       string(statementKey(goal)),
		Abbreviations: abbreviations.Entries(),
	}})
}

// recordDefer records a defer of card at the leaf goalID of section,
// naming deps. The card's own name, entry and note are recorded, which
// are the first defer's: a replay re-issued under them finds the card
// a second defer of the same lemma found.
func (s *Session) recordDefer(goalID string, section int, card *sessionCard, deps []string) {
	typed, _ := s.Spelling().Typed(card.statement)
	s.record(LineageEvent{Kind: kindDefer, Defer: &LineageDefer{
		GoalID:         goalID,
		Section:        section,
		Name:           card.name,
		Entry:          card.entry,
		Note:           card.note,
		Deps:           slices.Clone(deps),
		Key:            string(card.key),
		Statement:      s.Spelling().Prop(card.statement),
		StatementTyped: typed,
	}})
}

func (s *Session) recordApply(req *ApplyStepRequest, section int, effect string, winner bool, autoCheckpoint, preCheckpoint string) {
	if s.replaying || s.lineage == nil {
		return
	}
	lt, err := lineageTacticOf(req.Tactic)
	if err != nil {
		fmt.Fprintf(os.Stderr, "[lineage] session %s: %v\n", s.ID, err)
		return
	}
	if recorded := s.checkpointLineageIDs[preCheckpoint]; recorded != "" {
		preCheckpoint = recorded
	}
	s.record(LineageEvent{Kind: kindApply, Apply: &LineageApply{
		GoalID:         req.GoalID,
		Section:        section,
		Tactic:         lt,
		BudgetMs:       req.BudgetMs,
		Winner:         winner,
		Effect:         effect,
		AutoCheckpoint: autoCheckpoint,
		PreCheckpoint:  preCheckpoint,
	}})
}

func (s *Session) recordCheckpoint(id, name string) {
	s.record(LineageEvent{Kind: kindCheckpoint, Checkpoint: &LineageCheckpoint{ID: id, Name: name}})
}

func (s *Session) recordRestore(checkpointID string) {
	if recorded := s.checkpointLineageIDs[checkpointID]; recorded != "" {
		checkpointID = recorded
	}
	s.record(LineageEvent{Kind: kindRestore, Restore: &LineageRestore{CheckpointID: checkpointID}})
}

// rememberReplayCheckpoint keeps the replay lookup and the identity a
// later restore records. Several recorded ids may share one recreated
// snapshot; its first recorded identity remains a valid restore target.
func (s *Session) rememberReplayCheckpoint(ids map[string]string, recorded, recreated string) {
	ids[recorded] = recreated
	if s.checkpointLineageIDs == nil {
		s.checkpointLineageIDs = make(map[string]string)
	}
	if s.checkpointLineageIDs[recreated] == "" {
		s.checkpointLineageIDs[recreated] = recorded
	}
}

// recordFault records an engine fault. It is recorded inside a move
// that records itself too: the fault is no part of that move.
func (s *Session) recordFault(id, command, site string) {
	suppressed := s.recordingSuppressed
	s.recordingSuppressed = 0
	defer func() { s.recordingSuppressed = suppressed }()
	s.record(LineageEvent{Kind: kindFault, Fault: &LineageFault{ID: id, Command: command, Site: site}})
}

// --- the lineage view (`session-lineage`) ---

// LineageView is the readable form of a session's lineage.
type LineageView struct {
	ID        string             `json:"id"`
	CreatedAt time.Time          `json:"created_at"`
	Persisted bool               `json:"persisted"`
	Events    []LineageEventView `json:"events"`
}

// LineageEventView is one event, summarized.
type LineageEventView struct {
	Seq     int         `json:"seq"`
	Kind    LineageKind `json:"kind"`
	Section int         `json:"section,omitempty"`
	GoalID  string      `json:"goal_id,omitempty"`
	Summary string      `json:"summary"`
}

// SessionLineage returns the session's lineage, summarized.
func (e *Engine) SessionLineage(sessionID string) (*LineageView, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	view := &LineageView{ID: s.ID, CreatedAt: s.CreatedAt, Persisted: s.lineageStore != ""}
	if s.lineage == nil {
		return view, nil
	}
	for _, ev := range s.lineage.Events {
		v := LineageEventView{Seq: ev.Seq, Kind: ev.Kind}
		switch ev.Kind {
		case kindFamily:
			v.Summary = "family " + ev.Family.Name
			if len(ev.Family.Imports) > 0 {
				v.Summary += " imports " + strings.Join(ev.Family.Imports, ", ")
			}
		case kindDefine:
			v.Summary = "define " + defineRequestName(ev.Define)
		case kindAddGoal:
			v.Section, v.GoalID = ev.Goal.Section, ev.Goal.GoalID
			v.Summary = "add-goal " + clipRunes(ev.Goal.Statement, 80)
		case kindApply:
			v.Section, v.GoalID = ev.Apply.Section, ev.Apply.GoalID
			v.Summary = ev.Apply.Tactic.Type
			if ev.Apply.Effect != "" {
				v.Summary += " → " + ev.Apply.Effect
			}
		case kindCheckpoint:
			v.Summary = "checkpoint " + ev.Checkpoint.Name
		case kindRestore:
			v.Summary = "restore " + ev.Restore.CheckpointID
		case kindDefer:
			v.Section, v.GoalID = ev.Defer.Section, ev.Defer.GoalID
			v.Summary = "defer " + ev.Defer.Name + ": " + clipRunes(ev.Defer.Statement, 80)
		case kindFault:
			v.Summary = "engine fault " + ev.Fault.ID + " in " + ev.Fault.Command + " at " + ev.Fault.Site
		}
		view.Events = append(view.Events, v)
	}
	return view, nil
}

func defineRequestName(req *DefineRequest) string {
	switch {
	case req == nil:
		return "?"
	case req.Recursive != nil:
		return req.Recursive.Name
	case req.Data != nil:
		return req.Data.Name
	case req.Typedef != nil:
		return req.Typedef.Type
	case req.Inductive != nil:
		return req.Inductive.Name
	case req.Quotient != nil:
		return req.Quotient.Type
	case req.Spec != nil:
		names := make([]string, len(req.Spec.Consts))
		for i, c := range req.Spec.Consts {
			names[i] = c.Name
		}
		return fmt.Sprint(names)
	}
	return "?"
}

// clipRunes shortens s to at most max runes (rune-safe; these strings
// travel in RPC responses).
func clipRunes(s string, max int) string {
	r := []rune(s)
	if len(r) <= max {
		return s
	}
	return string(r[:max-1]) + "…"
}

// --- resume ---

// ResumeResult reports a resume: how far the transcript replayed,
// where it diverged, and every section's state afterwards.
type ResumeResult struct {
	Session  SessionInfo       `json:"session"`
	Events   int               `json:"events"`
	Replayed int               `json:"replayed"`
	Diverged *ResumeDivergence `json:"diverged,omitempty"`
	Sections []ResumeSection   `json:"sections"`
}

// ResumeDivergence names the first event that did not replay. The
// session is live at the state the events before it produced; the
// events from it on are set aside (lineage.diverged-<time>.json) and
// the live lineage is truncated to what replayed.
type ResumeDivergence struct {
	Seq   int         `json:"seq"`
	Kind  LineageKind `json:"kind"`
	Error string      `json:"error"`
}

// ResumeSection is one section after resume. RecordMatches compares
// the re-proved section's record to the persisted one (nil when the
// section is open or was never recorded).
type ResumeSection struct {
	Section       int    `json:"section"`
	Statement     string `json:"statement"`
	Proved        bool   `json:"proved"`
	RecordMatches *bool  `json:"record_matches,omitempty"`
	// Cards lists the cards the section's leaves closed by (defer.go).
	Cards []DeferredCard `json:"cards,omitempty"`
}

// ResumeSession rebuilds a persisted session under its own id by
// replaying its lineage: defines re-mint, goals re-add, applies re-run
// under a cache-only context (a CNF refute that is not in the store is
// a divergence, never a live search) and without the budget_ms they
// recorded, checkpoints and restores replay with their ids mapped.
// Stops at the first divergence and leaves the session live there.
//
// The replay outlives its caller: ctx's cancellation does not reach it,
// so a client that hangs up mid-resume costs only the response, never a
// divergence and the truncated lineage that follows. A resume of an id
// whose replay is running waits for that replay and returns its result;
// it starts no replay of its own, which would re-mint the session's
// defines into an engine that already holds them. Every other call that
// names the id is refused until the replay ends and the session is live.
func (e *Engine) ResumeSession(ctx context.Context, sessionID string) (*ResumeResult, error) {
	if !isSessionID(sessionID) {
		return nil, fmt.Errorf("resume: %q is not a session id — resume takes the id session-create returned, a UUID in lowercase", sessionID)
	}
	if e.sessionStore == "" {
		return nil, errors.New("resume: this engine has no session store")
	}
	e.mu.Lock()
	if f, running := e.resumes[sessionID]; running {
		e.mu.Unlock()
		return f.wait(ctx, sessionID)
	}
	if _, live := e.sessions[sessionID]; live {
		e.mu.Unlock()
		return nil, fmt.Errorf("resume: session %s is live in this engine: work on it as it stands", sessionID)
	}
	f := &_ResumeFlight{done: make(chan struct{})}
	e.resumes[sessionID] = f
	e.mu.Unlock()
	defer e.endResume(sessionID, f)
	f.result, f.err = e.replayLineage(context.WithoutCancel(ctx), sessionID)
	return f.result, f.err
}

// _ResumeFlight is a resume whose replay is running. done closes when
// the replay returns, with what it returned or the panic it raised.
type _ResumeFlight struct {
	done     chan struct{}
	result   *ResumeResult
	err      error
	panicked any
}

// wait is a second resume of the flight's session: it returns what the
// running replay returns, or an error if ctx is done first — the replay
// goes on either way.
func (f *_ResumeFlight) wait(ctx context.Context, sessionID string) (*ResumeResult, error) {
	select {
	case <-f.done:
		if f.panicked != nil {
			panic(f.panicked)
		}
		return f.result, f.err
	case <-ctx.Done():
		return nil, fmt.Errorf("resume: session %s is still replaying for an earlier resume; resume it again to wait for that replay", sessionID)
	}
}

// endResume takes a finished flight off the engine and wakes the
// resumes waiting on it; a panic in the replay reaches them as it
// reaches the resume that ran it.
func (e *Engine) endResume(sessionID string, f *_ResumeFlight) {
	f.panicked = recover()
	e.mu.Lock()
	delete(e.resumes, sessionID)
	e.mu.Unlock()
	close(f.done)
	if f.panicked != nil {
		panic(f.panicked)
	}
}

// replayLineage is ResumeSession's replay of the persisted lineage.
// The session joins the engine's live sessions when its replay ends:
// until then every call that names it is refused (getSession), so no
// move lands between two replayed events and no read sees a state
// halfway through.
func (e *Engine) replayLineage(ctx context.Context, sessionID string) (*ResumeResult, error) {
	data, err := os.ReadFile(filepath.Join(lineageDir(e.sessionStore, sessionID), lineageFileName))
	if err != nil {
		return nil, fmt.Errorf("resume: %w", err)
	}
	var lineage sessionLineage
	if err := json.Unmarshal(data, &lineage); err != nil {
		return nil, fmt.Errorf("resume: lineage of %s does not parse: %w", sessionID, err)
	}
	if lineage.ID != sessionID {
		return nil, fmt.Errorf("resume: lineage file names session %s, not %s", lineage.ID, sessionID)
	}

	s := e.newSession(sessionID, lineage.CreatedAt)
	s.lineage = &lineage
	s.replaying = true

	// CNF refutes replay from the store: a MISS is a divergence.
	ctx = proof.CNFCacheOnlyContext(ctx)
	checkpointIDs := map[string]string{}
	result := &ResumeResult{
		Session: SessionInfo{ID: s.ID, CreatedAt: s.CreatedAt},
		Events:  len(lineage.Events),
	}
	for i, ev := range lineage.Events {
		s.mu.Lock()
		err := e.replayEvent(ctx, s, ev, checkpointIDs)
		s.mu.Unlock()
		if err != nil {
			result.Diverged = &ResumeDivergence{Seq: ev.Seq, Kind: ev.Kind, Error: err.Error()}
			// Set the full transcript aside, then keep only what replayed.
			stash := filepath.Join(lineageDir(e.sessionStore, sessionID),
				fmt.Sprintf("lineage.diverged-%s.json", time.Now().UTC().Format("20060102T150405")))
			if werr := os.WriteFile(stash, data, 0o644); werr != nil {
				fmt.Fprintf(os.Stderr, "[lineage] session %s: stash diverged transcript: %v\n", sessionID, werr)
			}
			s.mu.Lock()
			s.lineage.Events = append([]LineageEvent(nil), lineage.Events[:i]...)
			s.mu.Unlock()
			break
		}
		result.Replayed = i + 1
	}

	s.mu.Lock()
	s.replaying = false
	result.Session.Family, result.Session.Imports = s.familyNames()
	for i, sec := range s.sections {
		rs := ResumeSection{Section: i, Statement: s.Spelling().Prop(sec.root.Goal), Proved: sec.root.Proved()}
		rs.Cards = sec.status(i, s.Spelling()).Cards
		if rs.Proved {
			sec.recorded = true
			if want, rerr := os.ReadFile(sectionRecordPath(e.sessionStore, sessionID, i)); rerr == nil {
				matches := false
				if detailed := sec.root.DetailedProofProto(); detailed != nil {
					if got, merr := proto.Marshal(detailed); merr == nil {
						matches = string(got) == string(want)
					}
				}
				rs.RecordMatches = &matches
			}
		}
		result.Sections = append(result.Sections, rs)
	}
	s.saveLineage()
	s.lineageLen.Store(int64(len(s.lineage.Events)))
	s.mu.Unlock()
	e.mu.Lock()
	e.sessions[sessionID] = s
	e.mu.Unlock()
	return result, nil
}

// replayEvent re-issues one recorded move through the engine's own
// moves, under the session lock: each entry point's Locked form, which
// takes the session itself, since a replaying session is not yet one
// an id names. A panic inside a replayed move (a cache-only MISS
// surfaces as one) is a divergence, not a crash; one that is a fault by
// its value is recorded as the session's (fault.go), and the divergence
// names the record.
func (e *Engine) replayEvent(ctx context.Context, s *Session, ev LineageEvent, checkpointIDs map[string]string) (err error) {
	defer func() {
		if r := recover(); r != nil {
			err = fmt.Errorf("%v", r)
			if utils.IsFault(r) {
				scope := faultScope(ctx, s, "session-create (resume, event "+fmt.Sprint(ev.Seq)+" "+string(ev.Kind)+")")
				fault := e.fileFault(s, scope.record(r, string(debug.Stack())))
				err = errors.New(fault.message("the replayed " + string(ev.Kind)))
			}
		}
	}()
	switch ev.Kind {
	case kindFamily:
		if ev.Family == nil {
			return errors.New("family event without a payload")
		}
		_, err := e.setSessionFamilyLocked(s, ev.Family.Name, ev.Family.Imports)
		return err

	case kindDefine:
		if ev.Define == nil {
			return errors.New("define event without a payload")
		}
		req := *ev.Define
		req.SessionID = s.ID
		if err := checkDefinePayload(&req); err != nil {
			return err
		}
		_, err := e.defineMoveLocked(s, &req)
		return err

	case kindAddGoal:
		g := ev.Goal
		if g == nil {
			return errors.New("add-goal event without a payload")
		}
		if len(g.Blob) == 0 {
			return errors.New("add-goal event carries no statement: a session states its goals " +
				"by text, and replay re-adds the recorded statement")
		}
		p, _, perr := ext.UnmarshalPropBlob(g.Blob, s.env.ProofService.LoadConstMeta)
		if perr != nil || p == nil {
			return fmt.Errorf("goal statement does not decode (%v)", perr)
		}
		table, terr := dsl.ParseAbbreviations(g.Abbreviations)
		if terr != nil {
			return fmt.Errorf("the goal's abbreviations do not read: %v", terr)
		}
		goalID, aerr := s.AddGoalWith(p, table)
		if aerr != nil {
			return aerr
		}
		if goalID != g.GoalID {
			return fmt.Errorf("goal id drifted: recorded %s, replay produced %s", g.GoalID, goalID)
		}
		return nil

	case kindApply:
		a := ev.Apply
		if a == nil {
			return errors.New("apply event without a payload")
		}
		tactic, terr := a.Tactic.tacticReq(s.env.ProofService.LoadConstMeta)
		if terr != nil {
			return terr
		}
		if a.Winner {
			res, berr := e.batchApplyLocked(ctx, s, &BatchApplyRequest{
				GoalID: a.GoalID, Tactics: []TacticReq{tactic}, Mode: FirstSuccess})
			if berr != nil {
				return berr
			}
			if res.WinnerIndex != 0 {
				return fmt.Errorf("the committed tactic %s no longer applies: %s", tactic.Type, firstDiagnostic(res.Results))
			}
			return nil
		}
		// Without the recorded budget_ms: it bounded the apply's search,
		// and replay re-runs a move that succeeded, its CNF refutes read
		// from the store — a deadline would only make a slower run a
		// divergence. With no deadline the unifier runs in its
		// deterministic mode (ext/unify), as the chapter Go's replay does.
		res, aerr := e.applyStepLocked(ctx, s, &ApplyStepRequest{GoalID: a.GoalID, Tactic: tactic})
		if aerr != nil {
			return aerr
		}
		if !res.Success {
			return fmt.Errorf("tactic %s no longer applies: %s", tactic.Type, firstDiagnostic([]StepResult{*res}))
		}
		if a.AutoCheckpoint != "" {
			if s.lastAutoCheckpointID == "" {
				return errors.New("the apply created no auto-checkpoint on replay (auto-checkpointing off?)")
			}
			s.rememberReplayCheckpoint(checkpointIDs, a.AutoCheckpoint, s.lastAutoCheckpointID)
		}
		if a.PreCheckpoint != "" {
			// On replay an earlier auto-checkpoint may already hold
			// the recorded apply's pre-state
			// (the replay's checkpoints are re-created in event order,
			// not the original's), and a restore to the recorded id is
			// a restore to whichever holds it now.
			if s.preApplyCheckpointID == "" {
				return errors.New("no auto-checkpoint holds the pre-apply state on replay (auto-checkpointing off?), and the recorded apply names one")
			}
			s.rememberReplayCheckpoint(checkpointIDs, a.PreCheckpoint, s.preApplyCheckpointID)
		}
		return nil

	case kindCheckpoint:
		if ev.Checkpoint == nil {
			return errors.New("checkpoint event without a payload")
		}
		s.rememberReplayCheckpoint(checkpointIDs, ev.Checkpoint.ID, e.checkpointLocked(s, ev.Checkpoint.Name))
		return nil

	case kindRestore:
		if ev.Restore == nil {
			return errors.New("restore event without a payload")
		}
		id, ok := checkpointIDs[ev.Restore.CheckpointID]
		if !ok {
			return fmt.Errorf("restore names checkpoint %s, which no replayed event created", ev.Restore.CheckpointID)
		}
		return e.restoreCheckpointLocked(s, id)

	case kindDefer:
		// Re-mints the card as recorded whether or not an entry states
		// it since (deferLocked skips that check while replaying), its
		// recorded deps held to what a dep may be as the live defer held
		// them — a lineage recorded without deps names none; the
		// recorded cite that follows re-closes the leaf.
		d := ev.Defer
		if d == nil {
			return errors.New("defer event without a payload")
		}
		res, derr := e.deferLocked(ctx, s, d.GoalID, d.Name, d.Note, d.Deps, false)
		if derr != nil {
			return derr
		}
		if res.Card.Key != d.Key {
			return fmt.Errorf("defer of %s produced card %s, recorded %s", d.Name, res.Card.Key, d.Key)
		}
		return nil

	case kindFault:
		if ev.Fault == nil {
			return errors.New("fault event without a payload")
		}
		s.faults = append(s.faults, ev.Fault.ID)
		return nil
	}
	return fmt.Errorf("unknown lineage event kind %q", ev.Kind)
}

func firstDiagnostic(results []StepResult) string {
	for _, r := range results {
		for _, d := range r.Diagnostics {
			if d.Type == DiagTacticFailure {
				return d.Message
			}
		}
		for _, d := range r.Diagnostics {
			return d.Message
		}
	}
	return "no diagnostic"
}
