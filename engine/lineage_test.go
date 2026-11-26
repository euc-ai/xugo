package engine

import (
	"context"
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"
	"uuid"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/solver/refuter"
	"github.com/stretchr/testify/assert"
	"github.com/stretchr/testify/require"
)

// lineageEngine builds an engine over a FRESH test env (its own
// const-meta map — what a new process holds) sharing the given CNF
// store (what the production session store persists across serves) and
// the given session store directory.
// lineageFamily is the family buildLineageSession binds. What the test
// needs of it is that binding installs NO definition rules: the session
// is replayed into a fresh env holding its own const-meta map, and a
// rule mentioning a constant that map does not carry cannot be decoded.
// A chapter of the corpus cannot promise that — whether it defines
// constants is its own business and changes as it grows — so the family
// is declared here and left empty.
const lineageFamily = "zz_engine_lineage"

var _ = registry.NewFamily(lineageFamily, nil)

func lineageEngine(store proof.CNFStore, dir string) *Engine {
	env := testEnv()
	env.ProofService.CNFStore = store
	return newEngine(env, WithSessionStore(dir))
}

func lineageText(t *testing.T, s *Session, text string) string {
	t.Helper()
	parsed := dsl.ParsePropTextInScope(text, &dsl.ParseScope{
		ConstResolver:      envConstResolver(s.env),
		StrictResolution:   true,
		FreshenMetaLetters: true,
	})
	require.Empty(t, parsed.Errors, "parse %q: %v", text, parsed.Errors)
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.AddGoal(parsed.Prop)
}

func lineageApply(t *testing.T, e *Engine, sid, gid, tactic string) *StepResult {
	t.Helper()
	res, err := e.ApplyStep(context.Background(), sid, &ApplyStepRequest{GoalID: gid, Tactic: TacticReq{Type: tactic}})
	require.NoError(t, err)
	require.True(t, res.Success, "%s on %s: %+v", tactic, gid, res.Diagnostics)
	return res
}

func openGoalTexts(s *Session) []string {
	s.mu.Lock()
	defer s.mu.Unlock()
	var out []string
	for _, g := range s.buildStateView().Goals {
		out = append(out, prop.PrintProp(g.Statement))
	}
	return out
}

// buildLineageSession writes the session this file's tests resume: a
// direct define, a section proved through the define's simp rule, a
// section `auto` closes in the CNF prelude (no certificate), an
// UNFINISHED section left after a checkpoint / apply /
// restore round trip, and one more apply on it.
func buildLineageSession(t *testing.T, e *Engine) (sid string, open []string) {
	t.Helper()
	ctx := context.Background()
	info, err := e.CreateSession(ctx)
	require.NoError(t, err)
	sid = info.ID
	// A family with no registered definitions: the binding records and
	// replays, nothing installs (the install itself is family_session_test).
	_, err = e.SetSessionFamily(sid, lineageFamily, nil)
	require.NoError(t, err)
	s, err := e.getSession(sid)
	require.NoError(t, err)

	// A definition: re-minted on resume.
	_, err = e.Define(&DefineRequest{SessionID: sid, Recursive: &DefineRecursive{
		Name: "zz_lin_xor", Type: "bool → bool → bool",
		Equations: []string{"∀p q:bool. zz_lin_xor(p, q) ⇔ (p ∨ q) ∧ ¬(p ∧ q)"},
	}})
	require.NoError(t, err)

	// A section proved by the define's simp rule + the reflexivity finisher.
	g1 := lineageText(t, s, "∀p:bool. zz_lin_xor(p, p) ⇔ (p ∨ p) ∧ ¬(p ∧ p)")
	r1 := lineageApply(t, e, sid, g1, "simp")
	require.Len(t, r1.Produced, 1)
	lineageApply(t, e, sid, r1.Produced[0].GoalID, "simplify")

	// A section `auto` closes: the clausified hyps refute outright, so
	// no certificate is written (addStoredRefute writes one).
	g2 := lineageText(t, s, "p:bool, q:bool, p ⊢ p ∨ q")
	require.Equal(t, "close", lineageApply(t, e, sid, g2, "auto").Effect)

	// An unfinished section with a checkpoint / restore in its history.
	g3 := lineageText(t, s, "∀x:num. ∀y:num. x = y ⇒ y = x")
	r3 := lineageApply(t, e, sid, g3, "strip_quant")
	require.Len(t, r3.Produced, 1)
	cp, err := e.Checkpoint(ctx, sid, "after-strip")
	require.NoError(t, err)
	r3b := lineageApply(t, e, sid, r3.Produced[0].GoalID, "strip_imp")
	require.Len(t, r3b.Produced, 1)
	require.NoError(t, e.Restore(ctx, sid, cp))
	// After the restore the strip_imp is undone; do it again — the
	// transcript now carries checkpoint, an apply, a restore, an apply.
	lineageApply(t, e, sid, r3.Produced[0].GoalID, "strip_imp")

	return sid, openGoalTexts(s)
}

func TestLineage_ResumeRebuildsProvedAndUnfinishedSections(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()

	a := lineageEngine(store, dir)
	sid, openBefore := buildLineageSession(t, a)
	require.Len(t, openBefore, 1, "one unfinished section")

	// The transcript and the records are on disk.
	lineagePath := filepath.Join(dir, sid, lineageFileName)
	data, err := os.ReadFile(lineagePath)
	require.NoError(t, err)
	var saved sessionLineage
	require.NoError(t, json.Unmarshal(data, &saved))
	require.Equal(t, sid, saved.ID)
	kinds := map[LineageKind]int{}
	for _, ev := range saved.Events {
		kinds[ev.Kind]++
	}
	assert.Equal(t, 1, kinds[kindFamily])
	assert.Equal(t, 1, kinds[kindDefine])
	assert.Equal(t, 3, kinds[kindAddGoal])
	assert.Equal(t, 6, kinds[kindApply])
	assert.Equal(t, 1, kinds[kindCheckpoint])
	assert.Equal(t, 1, kinds[kindRestore])
	for _, sec := range []int{0, 1, 2} {
		_, err := os.Stat(sectionRecordPath(dir, sid, sec))
		assert.NoError(t, err, "proved section %d has a record", sec)
	}
	_, err = os.Stat(sectionRecordPath(dir, sid, 3))
	assert.True(t, os.IsNotExist(err), "the unfinished section has no record")

	// A fresh engine — a new process's const metas — resumes it.
	b := lineageEngine(store, dir)
	res, err := b.ResumeSession(context.Background(), sid)
	require.NoError(t, err)
	if res.Diverged != nil {
		t.Fatalf("resume diverged at event %d (%s): %s", res.Diverged.Seq, res.Diverged.Kind, res.Diverged.Error)
	}
	assert.Equal(t, res.Events, res.Replayed)
	assert.Equal(t, sid, res.Session.ID)
	assert.Equal(t, lineageFamily, res.Session.Family)
	require.Len(t, res.Sections, 4)
	for _, sec := range res.Sections[:3] {
		assert.True(t, sec.Proved, "section %d re-proves", sec.Section)
		if assert.NotNil(t, sec.RecordMatches, "section %d compares to its record", sec.Section) {
			assert.True(t, *sec.RecordMatches, "section %d re-proves along the recorded steps", sec.Section)
		}
	}
	assert.False(t, res.Sections[3].Proved)

	sb, err := b.getSession(sid)
	require.NoError(t, err)
	assert.Equal(t, openBefore, openGoalTexts(sb), "the unfinished section resumes at the same open leaf")

	// The resumed session keeps recording: a further apply extends the
	// same lineage on disk.
	openIDs := func() []string {
		sb.mu.Lock()
		defer sb.mu.Unlock()
		var ids []string
		for id := range sb.goalIndex {
			ids = append(ids, id)
		}
		return ids
	}()
	require.Len(t, openIDs, 1)
	lineageApply(t, b, sid, openIDs[0], "simplify")
	data, err = os.ReadFile(lineagePath)
	require.NoError(t, err)
	var after sessionLineage
	require.NoError(t, json.Unmarshal(data, &after))
	assert.Len(t, after.Events, len(saved.Events)+1)
}

func TestLineage_DivergenceStopsAtTheFirstFailedEvent(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(store, dir)
	sid, _ := buildLineageSession(t, a)

	// Tamper: make the refute-closed section's `auto` an `assumption`
	// (which cannot close p ⊢ p ∨ q).
	lineagePath := filepath.Join(dir, sid, lineageFileName)
	data, err := os.ReadFile(lineagePath)
	require.NoError(t, err)
	var saved sessionLineage
	require.NoError(t, json.Unmarshal(data, &saved))
	tampered := 0
	for i := range saved.Events {
		if saved.Events[i].Kind == kindApply && saved.Events[i].Apply.Tactic.Type == "auto" {
			saved.Events[i].Apply.Tactic.Type = "assumption"
			tampered = saved.Events[i].Seq
		}
	}
	require.NotZero(t, tampered)
	data, err = json.Marshal(saved)
	require.NoError(t, err)
	require.NoError(t, os.WriteFile(lineagePath, data, 0o644))

	b := lineageEngine(store, dir)
	res, err := b.ResumeSession(context.Background(), sid)
	require.NoError(t, err)
	require.NotNil(t, res.Diverged, "the tampered event must not replay")
	assert.Equal(t, tampered, res.Diverged.Seq)
	assert.Equal(t, kindApply, res.Diverged.Kind)
	assert.Equal(t, tampered-1, res.Replayed)
	// Live at the state before the divergence: the define section and
	// the simp-proved section stand, the refute section is open, the
	// later sections were never added.
	require.Len(t, res.Sections, 3)
	assert.True(t, res.Sections[0].Proved)
	assert.True(t, res.Sections[1].Proved)
	assert.False(t, res.Sections[2].Proved)
	// The full transcript is set aside; the live lineage holds what
	// replayed.
	stashes, _ := filepath.Glob(filepath.Join(dir, sid, "lineage.diverged-*.json"))
	assert.Len(t, stashes, 1)
	data, err = os.ReadFile(lineagePath)
	require.NoError(t, err)
	var live sessionLineage
	require.NoError(t, json.Unmarshal(data, &live))
	assert.Len(t, live.Events, tampered-1)
}

// _HeldCNFStore is a CNF store whose ReadProof runs hold first: a
// replay's refute waits there for as long as a test needs.
type _HeldCNFStore struct {
	proof.CNFStore
	hold func()
}

func (s *_HeldCNFStore) ReadProof(key core.PropKey) *refuter.CNFRefuteProofProto {
	s.hold()
	return s.CNFStore.ReadProof(key)
}

// _AskedContext is a context that reports the first time a caller
// selects on its Done channel.
type _AskedContext struct {
	context.Context
	once  sync.Once
	asked chan struct{}
}

func (c *_AskedContext) Done() <-chan struct{} {
	c.once.Do(func() { close(c.asked) })
	return c.Context.Done()
}

// addStoredRefute adds to the session a section `auto` closes by a CNF
// refute that resolution finds — its certificate written to the store,
// so a replay of the apply reads it back from there.
func addStoredRefute(t *testing.T, e *Engine, sid string, store *proof.MemoryCNFStore) {
	t.Helper()
	s, err := e.getSession(sid)
	require.NoError(t, err)
	held := store.Len()
	g := lineageText(t, s, "P:num → bool, Q:num → bool, a:num, ∀x:num. P(x) ⇒ Q(x), P(a) ⊢ Q(a)")
	require.Equal(t, "close", lineageApply(t, e, sid, g, "auto").Effect)
	require.Equal(t, held+1, store.Len(), "the refute's certificate is in the store")
}

// A resume whose caller has hung up — its context done before the
// first event that polls it — replays the whole transcript: the
// cancellation is no divergence, and the lineage on disk keeps every
// event.
func TestLineage_ResumeOutlivesItsCaller(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	sid, _ := buildLineageSession(t, lineageEngine(store, dir))
	lineagePath := filepath.Join(dir, sid, lineageFileName)
	before, err := os.ReadFile(lineagePath)
	require.NoError(t, err)

	hungUp, cancel := context.WithCancel(context.Background())
	cancel()
	res, err := lineageEngine(store, dir).ResumeSession(hungUp, sid)
	require.NoError(t, err)
	if res.Diverged != nil {
		t.Fatalf("resume diverged at event %d (%s): %s", res.Diverged.Seq, res.Diverged.Kind, res.Diverged.Error)
	}
	assert.Equal(t, res.Events, res.Replayed)
	stashes, _ := filepath.Glob(filepath.Join(dir, sid, "lineage.diverged-*.json"))
	assert.Empty(t, stashes, "nothing is set aside")
	after, err := os.ReadFile(lineagePath)
	require.NoError(t, err)
	assert.Equal(t, string(before), string(after), "the lineage on disk is the one resume read")
}

// A resume of an id whose replay is running — the retry of a caller
// that hung up — starts no replay of its own (which would re-mint the
// session's defines): it waits for the running one and returns its
// result. A waiter whose own caller hangs up returns, and the replay
// goes on.
func TestLineage_ASecondResumeJoinsTheRunningReplay(t *testing.T) {
	memory := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(memory, dir)
	sid, _ := buildLineageSession(t, a)
	addStoredRefute(t, a, sid, memory)

	// The replay's first refute is held until release closes.
	reached, release := make(chan struct{}), make(chan struct{})
	releaseHeld := sync.OnceFunc(func() { close(release) })
	t.Cleanup(releaseHeld)
	var once sync.Once
	b := lineageEngine(&_HeldCNFStore{CNFStore: memory, hold: func() {
		once.Do(func() { close(reached); <-release })
	}}, dir)

	type outcome struct {
		res *ResumeResult
		err error
	}
	resume := func(ctx context.Context) <-chan outcome {
		out := make(chan outcome, 1)
		go func() {
			res, err := b.ResumeSession(ctx, sid)
			out <- outcome{res, err}
		}()
		return out
	}
	first := resume(context.Background())
	select {
	case <-reached:
	case o := <-first:
		t.Fatalf("the resume returned before its replay reached the refute: %+v, %v", o.res, o.err)
	}

	hungUp, cancel := context.WithCancel(context.Background())
	cancel()
	_, err := b.ResumeSession(hungUp, sid)
	if assert.Error(t, err, "a waiter whose caller hung up returns") {
		assert.Contains(t, err.Error(), "still replaying")
	}

	waiting := &_AskedContext{Context: context.Background(), asked: make(chan struct{})}
	second := resume(waiting)
	select {
	case <-waiting.asked:
	case o := <-second:
		t.Fatalf("the second resume returned while the first was replaying: %+v, %v", o.res, o.err)
	}
	releaseHeld()
	ran, joined := <-first, <-second
	require.NoError(t, ran.err)
	require.NoError(t, joined.err)
	assert.Same(t, ran.res, joined.res, "the second resume returns the running replay's result")
	if ran.res.Diverged != nil {
		t.Fatalf("resume diverged at event %d (%s): %s", ran.res.Diverged.Seq, ran.res.Diverged.Kind, ran.res.Diverged.Error)
	}
	assert.Equal(t, ran.res.Events, ran.res.Replayed)

	_, err = b.ResumeSession(context.Background(), sid)
	if assert.Error(t, err, "once the replay is done the session is live") {
		assert.Contains(t, err.Error(), "is live")
	}
}

// While its resume replays, a session takes no other call: a move
// would land unrecorded between two replayed events, a read would see
// a state halfway through the transcript. Each call is refused, naming
// the resume that waits for the replay; once the replay is done the
// session answers.
func TestLineage_ASessionBeingResumedRefusesOtherCalls(t *testing.T) {
	memory := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(memory, dir)
	sid, _ := buildLineageSession(t, a)
	addStoredRefute(t, a, sid, memory)

	// The replay's first refute is held until release closes.
	reached, release := make(chan struct{}), make(chan struct{})
	releaseHeld := sync.OnceFunc(func() { close(release) })
	t.Cleanup(releaseHeld)
	var once sync.Once
	b := lineageEngine(&_HeldCNFStore{CNFStore: memory, hold: func() {
		once.Do(func() { close(reached); <-release })
	}}, dir)
	resumed := make(chan error, 1)
	go func() {
		_, err := b.ResumeSession(context.Background(), sid)
		resumed <- err
	}()
	select {
	case <-reached:
	case err := <-resumed:
		t.Fatalf("the resume returned before its replay reached the refute: %v", err)
	}

	ctx := context.Background()
	for _, c := range []struct {
		name string
		call func() error
	}{
		{"inspect", func() error { _, err := b.InspectState(ctx, sid); return err }},
		{"apply", func() error {
			_, err := b.ApplyStep(ctx, sid, &ApplyStepRequest{GoalID: "s0_gprop_0", Tactic: TacticReq{Type: "simplify"}})
			return err
		}},
		{"lineage", func() error { _, err := b.SessionLineage(sid); return err }},
		{"close", func() error { return b.CloseSession(ctx, sid) }},
	} {
		returned := make(chan error, 1)
		go func() { returned <- c.call() }()
		select {
		case err := <-returned:
			if assert.Error(t, err, "%s during the replay", c.name) {
				assert.Contains(t, err.Error(), "being resumed", c.name)
			}
		case <-time.After(10 * time.Second):
			t.Errorf("%s reached the session: it is still waiting on the replay's lock", c.name)
		}
	}

	releaseHeld()
	require.NoError(t, <-resumed)
	_, err := b.InspectState(ctx, sid)
	assert.NoError(t, err, "once the replay is done the session answers")
}

// An apply's budget_ms bounded the live search it ran; replay runs
// none (its CNF refutes read the store), so it imposes no deadline. A
// replay slower than the original — here the stored refute is read
// 20 ms into a 1 ms budget — is no divergence.
func TestLineage_ReplayRunsWithoutTheRecordedBudget(t *testing.T) {
	memory := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(memory, dir)
	sid, _ := buildLineageSession(t, a)
	addStoredRefute(t, a, sid, memory)

	lineagePath := filepath.Join(dir, sid, lineageFileName)
	data, err := os.ReadFile(lineagePath)
	require.NoError(t, err)
	var saved sessionLineage
	require.NoError(t, json.Unmarshal(data, &saved))
	// The last apply is addStoredRefute's `auto`.
	last := &saved.Events[len(saved.Events)-1]
	require.Equal(t, kindApply, last.Kind)
	require.Equal(t, "auto", last.Apply.Tactic.Type)
	last.Apply.BudgetMs = 1
	data, err = json.Marshal(saved)
	require.NoError(t, err)
	require.NoError(t, os.WriteFile(lineagePath, data, 0o644))

	slow := &_HeldCNFStore{CNFStore: memory, hold: func() { time.Sleep(20 * time.Millisecond) }}
	res, err := lineageEngine(slow, dir).ResumeSession(context.Background(), sid)
	require.NoError(t, err)
	if res.Diverged != nil {
		t.Fatalf("resume diverged at event %d (%s): %s", res.Diverged.Seq, res.Diverged.Kind, res.Diverged.Error)
	}
	assert.Equal(t, res.Events, res.Replayed)
}

func TestLineage_ResumeRefusals(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	dir := t.TempDir()
	a := lineageEngine(store, dir)
	sid, _ := buildLineageSession(t, a)

	t.Run("live in this engine", func(t *testing.T) {
		_, err := a.ResumeSession(context.Background(), sid)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "is live")
	})
	t.Run("no session store", func(t *testing.T) {
		env := testEnv()
		env.ProofService.CNFStore = store
		bare := newEngine(env)
		_, err := bare.ResumeSession(context.Background(), sid)
		require.Error(t, err)
		assert.Contains(t, err.Error(), "no session store")
	})
	t.Run("unknown id", func(t *testing.T) {
		_, err := lineageEngine(store, dir).ResumeSession(context.Background(), uuid.New().String())
		require.Error(t, err)
		assert.NotContains(t, err.Error(), "not a session id", "a well-formed id with no lineage is refused for the lineage it lacks")
	})
	t.Run("a re-mint into a process that holds the name diverges at the define", func(t *testing.T) {
		// The SAME engine (same const metas) after closing the session:
		// the define event collides — by ruling there is no reuse rule.
		require.NoError(t, a.CloseSession(context.Background(), sid))
		res, err := a.ResumeSession(context.Background(), sid)
		require.NoError(t, err)
		require.NotNil(t, res.Diverged)
		assert.Equal(t, kindDefine, res.Diverged.Kind)
		assert.Contains(t, res.Diverged.Error, "already names a constant")
	})
}

// TestLineage_ResumeTakesOnlyASessionID pins the one place a caller's
// string becomes a path: a session's id names its directory under the
// session store, and resume reads there. An id that is not one the
// engine mints is refused before the store is touched. The first case
// is the one the refusal exists for: a lineage OUTSIDE the store, at
// the path a traversing id reaches and naming that id as its own, so
// that the read's check of the file against the id passes.
func TestLineage_ResumeTakesOnlyASessionID(t *testing.T) {
	base := t.TempDir()
	dir := filepath.Join(base, "store")
	require.NoError(t, os.MkdirAll(dir, 0o755))
	e := lineageEngine(proof.NewMemoryCNFStore(), dir)

	const traversing = "../outside"
	outside := filepath.Join(base, "outside")
	require.NoError(t, os.MkdirAll(outside, 0o755))
	planted, err := json.Marshal(sessionLineage{ID: traversing, CreatedAt: time.Now()})
	require.NoError(t, err)
	require.NoError(t, os.WriteFile(filepath.Join(outside, lineageFileName), planted, 0o644))

	minted := uuid.New().String()
	for _, id := range []string{
		traversing,
		outside,
		"",
		".",
		"..",
		"a/b",
		strings.ToUpper(minted),
		"{" + minted + "}",
		"urn:uuid:" + minted,
		strings.ReplaceAll(minted, "-", ""),
	} {
		_, err := e.ResumeSession(context.Background(), id)
		if assert.Error(t, err, "resume %q", id) {
			assert.Contains(t, err.Error(), "not a session id", "resume %q", id)
		}
		_, err = e.getSession(id)
		assert.Error(t, err, "resume %q opened a session", id)
	}
	left, err := os.ReadDir(outside)
	require.NoError(t, err)
	assert.Len(t, left, 1, "the directory outside the store holds what was planted and nothing more")
}

func TestLineage_ViewSummarizesTheTranscript(t *testing.T) {
	store := proof.NewMemoryCNFStore()
	a := lineageEngine(store, t.TempDir())
	sid, _ := buildLineageSession(t, a)
	view, err := a.SessionLineage(sid)
	require.NoError(t, err)
	assert.True(t, view.Persisted)
	assert.Equal(t, sid, view.ID)
	require.NotEmpty(t, view.Events)
	assert.Equal(t, "family "+lineageFamily, view.Events[0].Summary)
	assert.Equal(t, "define zz_lin_xor", view.Events[1].Summary)
	var applies, closes int
	for _, ev := range view.Events {
		if ev.Kind == kindApply {
			applies++
			if strings.HasSuffix(ev.Summary, "→ close") {
				closes++
			}
		}
	}
	assert.Equal(t, 6, applies)
	assert.Equal(t, 2, closes, "the simplify finisher and the refute close a section each")

	// In-memory only: an engine without a store still records.
	env := testEnv()
	env.ProofService.CNFStore = store
	bare := newEngine(env)
	info, err := bare.CreateSession(context.Background())
	require.NoError(t, err)
	bs, _ := bare.getSession(info.ID)
	lineageText(t, bs, "p:bool ⊢ p ∨ ¬p")
	v2, err := bare.SessionLineage(info.ID)
	require.NoError(t, err)
	assert.False(t, v2.Persisted)
	require.Len(t, v2.Events, 1)
	assert.Equal(t, kindAddGoal, v2.Events[0].Kind)
}
