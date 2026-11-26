package engine

import (
	"cmp"
	"context"
	"errors"
	"fmt"
	"slices"
	"strings"
	"sync"
	"sync/atomic"
	"time"
	"uuid"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/library/emit"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// confDefAction is the repair hints' confidence in a definition
// expansion or an induction: useful, but neither closes a goal by itself.
const confDefAction = 0.7

// Engine owns the proof sessions of one process and the
// closed-derivation pool they share. Its methods are the package's
// API: the stateless checks (CheckDerivation, CheckConsistency, …)
// and the session moves (CreateSession, Inspect, ApplyStep, Probe,
// Checkpoint, Restore, …).
type Engine struct {
	env            *proof.ProverEnv
	domainRegistry *DomainRegistry // nil = no registered domains (logic domain is implicit)

	mu       sync.Mutex
	sessions map[string]*Session
	// resumes holds the resumes whose replay is running, by session id
	// (lineage.go): a second resume of the id joins the running one, and
	// every other call naming the id is refused (sessionMissingLocked).
	resumes map[string]*_ResumeFlight

	// derivPool is the engine-global closed-derivation pool enabling
	// cross-session proof grafting via cite-node. Always non-nil (set by
	// NewEngine); see derivation_pool.go for scope/soundness rationale.
	derivPool *DerivationPool

	// autoCheckpointCap governs the automatic per-apply checkpoint feature
	// (see WithAutoCheckpoint). 0 disables the feature; > 0 enables it and
	// caps the number of retained auto_* checkpoints (LRU eviction).
	// User-named checkpoints are never evicted by the LRU pass.
	autoCheckpointCap int

	// constDefIdx is the reverse index from a constant's definitional
	// theorem to the constant (registry.BuildConstDefIndex over the
	// process's constants), built once for emit's leaf resolution.
	constDefIdx     registry.ConstDefIndex
	constDefIdxOnce sync.Once

	// inductionTemplates memoizes parsed induction principles by type
	// key. Populated lazily by lookupInductionTemplate. LibraryThms is
	// immutable per session, so this cache is set-once per type.
	inductionTemplates map[core.TypeKey]*tactic.InductionTemplate

	// sessionStore is the directory session lineages persist under
	// (lineage.go); empty = in-memory lineages only, no resume.
	sessionStore string

	// faultStore is the directory engine-fault records are written
	// under (fault.go); empty = no record files.
	faultStore string
}

// EngineOption configures optional Engine features.
type EngineOption func(*Engine)

// WithDerivationPoolCap overrides the closed-derivation pool's max entry
// count (default DefaultDerivationPoolCap). n <= 0 selects the default.
func WithDerivationPoolCap(n int) EngineOption {
	return func(e *Engine) { e.derivPool = NewDerivationPool(n) }
}

// DefaultAutoCheckpointCap is the default LRU cap for automatic per-apply
// checkpoints. See WithAutoCheckpoint.
const DefaultAutoCheckpointCap = 500

// WithAutoCheckpoint configures the automatic per-apply checkpoint feature.
// After every successful ApplyStep (RPC-boundary apply, not BatchApply inner
// iterations), the engine clones the session state into an "auto_<n>"
// checkpoint. Motivation: recover session progress cleanly when a sub-agent
// dies to an API infrastructure error mid-proof.
//
// cap > 0 enables auto-checkpointing with an LRU eviction cap (only auto_*
// checkpoints are evicted — user-named checkpoints are sticky). cap == 0
// disables the feature. cap < 0 is treated as 0.
//
// Default (when this option is not passed): ON with DefaultAutoCheckpointCap.
func WithAutoCheckpoint(cap int) EngineOption {
	if cap < 0 {
		cap = 0
	}
	return func(e *Engine) { e.autoCheckpointCap = cap }
}

// WithAutoCheckpointOff disables the automatic per-apply checkpoint feature.
// Equivalent to WithAutoCheckpoint(0).
func WithAutoCheckpointOff() EngineOption {
	return func(e *Engine) { e.autoCheckpointCap = 0 }
}

// autoCheckpointNamePrefix is the prefix marking engine-created auto
// checkpoints. Names starting with this prefix are subject to LRU
// eviction; any other checkpoint name is sticky.
const autoCheckpointNamePrefix = "auto_"

// DerivationPoolStats reports the engine-global closed-derivation pool's
// counters (entries / published / hits / misses / evictions).
func (e *Engine) DerivationPoolStats() DerivationPoolStats {
	return e.derivPool.Stats()
}

func NewEngine(env *proof.ProverEnv, opts ...EngineOption) *Engine {
	e := newEngine(env, opts...)
	// The corpus's statements are read here, once per process, so the
	// first request that scans them (retrieve's corpus groups) pays no
	// elaboration, and a member whose statement does not read under its
	// family vocabulary fails at construction, not mid-session. Keys are
	// computed on ask (registry.Statement.Key): a hit's, never the
	// corpus's. The laws readable through the corpus's projections
	// (retrieve's readings group) are derived from those statements in
	// the background from here: a request reads the view once it is
	// there and never waits for it.
	registry.ReadStatements()
	registry.WarmReadables()
	return e
}

// newEngine allocates independent session state. Corpus preparation belongs
// to NewEngine; tests of session mechanics use this constructor directly.
func newEngine(env *proof.ProverEnv, opts ...EngineOption) *Engine {
	e := &Engine{
		env:               env,
		sessions:          make(map[string]*Session),
		resumes:           make(map[string]*_ResumeFlight),
		derivPool:         NewDerivationPool(DefaultDerivationPoolCap),
		autoCheckpointCap: DefaultAutoCheckpointCap,
	}
	for _, opt := range opts {
		opt(e)
	}
	return e
}

// ---------------------------------------------------------------------------
// Session
// ---------------------------------------------------------------------------

// Session holds the proof state for one agent interaction.
type Session struct {
	// mu serializes all public RPC handlers touching per-session state
	// (goalIndex, sections, checkpoints, pendingPlans, env, auto-match
	// fields). Acquired by handler entry points AFTER getSession returned
	// this Session pointer; the engine-level e.mu is released before mu is
	// taken. Without this, concurrent `inspect` + long-running `apply`/
	// `probe`/`auto_with` goroutines race on goalIndex/sections and can
	// wedge the session: inspect hangs indefinitely after a restore
	// while a stale probe goroutine keeps mutating state.
	mu sync.Mutex

	ID        string
	CreatedAt time.Time
	env       *proof.ProverEnv

	// lineageLen is the number of events the lineage holds, kept beside
	// it for a reader that cannot take mu: the fault store's record of
	// a request in flight, written while the request's command holds
	// the lock.
	lineageLen atomic.Int64

	// derivPool is the owning engine's closed-derivation pool (shared by
	// every session of this engine; see derivation_pool.go). Publish side:
	// rebuildGoalIndex → publishClosedSubtrees. Consume side: the
	// cite-node dispatch's pool fallback. nil disables both (defensive —
	// CreateSession always sets it).
	derivPool *DerivationPool

	// family is the family this session works (nil for a bare
	// session); imports the further families whose definitions it
	// started with. Bound once, before any goal, by SetSessionFamily —
	// which installs every bound family's registered definitions as
	// use rules.
	family  *registry.Family
	imports []*registry.Family

	// Each section is an independent proof goal added via AddGoal.
	sections []*sectionState

	// simpRules is the session's installed simp set (the manual's R4): one
	// entry per `define` — the definition's characterizing theorem,
	// installed WHOLE (a conjunction is a valid simp_with rule), with the
	// definition section's promise as the closing cert for the rule child
	// the driver surfaces. The bare `simp` tactic rewrites with these;
	// checkpoints snapshot the list alongside the sections.
	simpRules []sessionSimpRule

	// defineTexts keeps, per session-defined constant, the author's own
	// spelling of its definition as the `define` RPC received it — the
	// type, equations, measure and spec texts — so emit-section renders
	// the family.Define / family.DefineSpec literal the author wrote
	// rather than the printer's form (emit.EmitOptions.DefinitionText).
	// Keyed by constant name; monotone (a mint is process-global and
	// exclusive), so checkpoints need no snapshot.
	defineTexts map[string]emit.DefinitionText

	// dataDefines tracks the session's datatype definition moves (the
	// `define` RPC's `data:` payload) — the emit layer's session-define
	// leaf tier resolves INJ/DISTINCT simp fires and induction-
	// principle deps against these records. Entries are immutable;
	// checkpoints snapshot the slice like simpRules.
	dataDefines []sessionDataDefine

	// typedefDefines tracks the session's type-definition moves (the
	// `define` RPC's `typedef:` payload) — the emit layer's
	// session-define leaf tier names their future entries against
	// these records. Entries are immutable; checkpoints snapshot the
	// slice like simpRules.
	typedefDefines []sessionTypedefDefine

	// inductiveDefines tracks the session's inductive definition moves
	// (the `define` RPC's `inductive:` payload) — the emit layer's
	// session-define leaf tier names their three future entries
	// against these records. Entries are immutable; checkpoints
	// snapshot the slice like simpRules.
	inductiveDefines []sessionInductiveDefine

	// cards are the cards this session minted with `defer`
	// (defer.go), by registered name: each a lemma stated without a
	// proof, served to the session as its axiom and cited by that
	// name, rendered as a card entry beside the member by
	// emit-section. Monotone (a mint is a statement, never undone by
	// a restore — a card nothing cites any more is rendered nowhere),
	// so checkpoints need no snapshot.
	cards map[string]*sessionCard

	// quotientDefines tracks the session's quotient definition moves
	// (the `define` RPC's `quotient:` payload) — the emit layer's
	// session-define leaf tier names their seven future entries and
	// the equivalence against these records. Entries are immutable;
	// checkpoints snapshot the slice like simpRules.
	quotientDefines []sessionQuotientDefine

	// obligationDefines records the authored-obligation definition
	// sections (WF, spec) that have COMPLETED: the emit layer's
	// session-define leaf tier names a cite of their characterizing
	// theorem, which the simp set does not carry (a specification
	// installs nothing; WF installs derived readings). Entries are
	// immutable; checkpoints snapshot the slice like simpRules.
	obligationDefines []sessionObligationDefine

	// pendingDefines tracks definition sections whose obligation the
	// AUTHOR still owes (the WF shape: the termination obligation is
	// the section's one open child). The apply path sweeps the list —
	// when a pending section proves, its R4 installation runs (the
	// derived guarded readings join the simp set) and the completion
	// is reported on that apply's response (transcript D's "on close").
	// Checkpoints snapshot the slice like simpRules.
	pendingDefines []pendingDefine

	// goalIndex maps stable goal IDs to their GoalStackNode.
	// Rebuilt after any mutation.
	goalIndex map[string]*goalEntry

	// checkpoints stores cloned snapshots of the session state.
	checkpoints map[string]*sessionCheckpoint

	// autoCheckpointSeq is the monotonic per-session counter used to name
	// auto-checkpoints ("auto_1", "auto_2", ...). Incremented under s.mu
	// after each successful RPC-boundary ApplyStep. See maybeAutoCheckpointLocked.
	autoCheckpointSeq int

	// pendingPlans stores deferred expansion plans from CompareAll mode.
	// Keyed by plan ref (UUID). Cleared on session mutation.
	pendingPlans map[string]*pendingPlan

	// lineage is the session's recorded transcript (lineage.go): every
	// mode / define / add-goal / apply / checkpoint / restore, in order.
	// lineageStore is the engine's session store directory (empty =
	// in-memory only). replaying suppresses recording while
	// ResumeSession re-issues the loaded events. lastAutoCheckpointID
	// is the id the most recent apply's auto-checkpoint got — recorded
	// with the apply so a later restore of it resolves on resume.
	lineage      *sessionLineage
	lineageStore string
	replaying    bool
	// checkpointLineageIDs maps recreated checkpoint ids to the ids
	// their creating events recorded, so later restores stay replayable.
	checkpointLineageIDs map[string]string
	// recordingSuppressed > 0 while a move that records ITSELF (a
	// define, whose sections are its own) runs the paths that would
	// otherwise record their parts.
	recordingSuppressed int
	// faults are the ids of the engine faults this session met whose
	// records it has not seen acknowledged (fault.go): while one is
	// open the session takes no move. faultStore is the engine's fault
	// store directory (empty = no record files).
	faults               []string
	faultStore           string
	lastAutoCheckpointID string
	// preApplyCheckpointID is the id of the auto-checkpoint holding the
	// state the most recent apply started from — the snapshot that
	// apply took, or the earlier one that still held it
	// (ensurePreApplyCheckpointLocked); "" with auto-checkpointing off.
	// A direct apply records the snapshot's id on its lineage event,
	// and a resume maps that id here.
	preApplyCheckpointID string

	// pendingApplyDiagnostics / pendingAutoMatched carry informational
	// results produced INSIDE runTacticOnClone's dispatch out to the RPC
	// boundary — currently simp_with's multi-instance polymorphic-rule
	// expansion notes and the rule children it auto-closes on the clone
	// (invisible to the post-commit runAutoPipeline because they close
	// pre-commit). Cleared at the top of every runTacticOnClone, drained
	// by ApplyStep into StepResult.Diagnostics / .AutoMatched. Guarded by
	// s.mu like all other per-session state; probe/batch callers that
	// don't drain simply leave them to be cleared by the next dispatch.
	pendingApplyDiagnostics []Diagnostic
	pendingAutoMatched      []AutoMatchedGoal

	// autoMatchCache is a per-session ThmCache used to inject trusted Thms
	// for auto-matched subgoals. Separate from env.ThmCache to avoid
	// cross-session pollution.
	autoMatchCache *proof.ThmCache
}

type sectionState struct {
	root *proof.GoalStackNode
	// recorded marks a proved section whose record (its
	// DetailedProofProto) the lineage store holds — see
	// Session.recordProvedSections.
	recorded bool
	// deferred lists the cards the section's leaves closed by
	// (defer.go), in defer order. Snapshotted with the root by
	// checkpoints.
	deferred []*sessionCard
	// abbreviations is the statement's table (dsl.Statement.Abbrev): the
	// names the section's goal was added spelling as «Name» — the
	// goal's own entries under the chapter's, self-contained — which
	// every claim and term text of the session reads under and the
	// output door folds a printed term back into. nil for a goal added
	// with none. Immutable; a checkpoint shares it.
	abbreviations *dsl.AbbreviationTable
}

type goalEntry struct {
	node      *proof.GoalStackNode
	sectionID int // index into sections
	depth     int
}

type sessionCheckpoint struct {
	// Clone-based: each section root is a Clone() of the original at checkpoint time.
	// Restoring clones the checkpoint's sections again (so checkpoint stays reusable).
	sections []*sectionState
	// simpRules snapshots the session's installed simp set — a restore
	// must not keep rules whose defining sections it rolled away (their
	// certs stay valid kernel objects, but the session state should
	// mirror what the restored tree can show). Entries are immutable;
	// the slice is copied.
	simpRules []sessionSimpRule
	// dataDefines snapshots the session's datatype-define records —
	// same rationale as simpRules.
	dataDefines []sessionDataDefine
	// typedefDefines snapshots the session's type-definition records —
	// same rationale as simpRules.
	typedefDefines []sessionTypedefDefine
	// inductiveDefines snapshots the session's inductive-define records.
	inductiveDefines []sessionInductiveDefine
	// quotientDefines snapshots the session's quotient-define records.
	quotientDefines []sessionQuotientDefine
	// obligationDefines snapshots the completed WF/spec records — same
	// rationale as simpRules.
	obligationDefines []sessionObligationDefine
	// pendingDefines snapshots the authored-obligation define sections
	// awaiting close — same rationale as simpRules.
	pendingDefines []pendingDefine
	name           string    // user-supplied label (may be empty)
	createdAt      time.Time // when Checkpoint() was called
}

// sessionObligationDefine is one completed WF or spec definition's
// session record: the constant whose exported spelling names the
// future entry (a spec group's first constant) and the characterizing
// statement — what the emit layer needs to name a cite of it.
type sessionObligationDefine struct {
	constName      string
	characterizing core.Prop
}

// pendingDefine is one authored-obligation definition section awaiting
// its close (see Session.pendingDefines).
type pendingDefine struct {
	// name is the minted constant's name (a spec's joined name list);
	// section its section index.
	name    string
	section int
	// node is the definition section's root.
	node *proof.GoalStackNode
	// key is the characterizing statement's normalized key.
	key string
	// shape is the served shape (WF, spec or lift — the three whose
	// section closes on the author's obligation); its completion
	// installs what proof.DefinitionSimpRules says the shape installs:
	// the WF shape's guarded readings, nothing for a specification, a
	// lift's computation rule whole. consts is the spec's constant
	// group.
	shape  proof.DefinitionShape
	consts []string
}

// sweepPendingDefines completes every pending definition section that
// has proved since the last sweep: the shape's default rules (the WF
// shape's guarded readings — the COND ruling's R4 half; none for the
// spec shape, a specification not being a directed rewrite) join the
// session simp set, backed by the section's own promise. Returns one
// completion report per closed define.
func (s *Session) sweepPendingDefines() []DefineCompletion {
	if len(s.pendingDefines) == 0 {
		return nil
	}
	var out []DefineCompletion
	kept := s.pendingDefines[:0]
	for _, pd := range s.pendingDefines {
		if !pd.node.Proved() {
			kept = append(kept, pd)
			continue
		}
		rules := s.installDefinitionRules(pd.name, pd.shape, pd.node.PromisedThm(), nil)
		constName := pd.name
		if len(pd.consts) > 0 {
			constName = pd.consts[0]
		}
		s.obligationDefines = append(s.obligationDefines, sessionObligationDefine{
			constName:      constName,
			characterizing: core.MakeProp(pd.node.Goal.Conclusion()),
		})
		done := DefineCompletion{
			Defined:       pd.name,
			Consts:        pd.consts,
			SimpInstalled: len(rules),
			Section:       pd.section,
			Key:           pd.key,
		}
		switch pd.shape {
		case proof.DefinitionWF:
			done.Schema = "wellfounded_recursion (measure)"
		case proof.DefinitionSpec:
			done.Schema = "specification"
		case proof.DefinitionLift:
			done.Schema = "quotient_lift"
		default:
			panic(fmt.Sprintf("define %s: a pending definition of shape %s — only the "+
				"WF, spec and lift shapes close on an obligation (engine fault)", pd.name, pd.shape))
		}
		out = append(out, done)
	}
	s.pendingDefines = kept
	return out
}

// sessionSimpRule is one installed simp-set entry: the rule statement
// (a definition's characterizing theorem — possibly a conjunction — or
// a reading derived from it) and the proved backing that closes the
// rule child simp_with surfaces. entry is the registered definition
// the rule was imported from (SetSessionFamily); nil for a rule this
// session's own `define` installed.
type sessionSimpRule struct {
	rule  core.Prop
	cert  core.Thm
	entry *registry.ProofEntry
}

// installDefinitionRules installs a served definition's default rules
// (proof.DefinitionSimpRules — the ONE dispatch every define door and
// the family import share) into the session simp set, backed by the
// definition's promise — the section's for a session define, the
// entry's replay promise for an import — and returns them. A
// derivation failure is an engine fault — the characterizing statement
// is machine-made by the door that served the shape — so it panics
// rather than degrading.
func (s *Session) installDefinitionRules(name string, shape proof.DefinitionShape, characterizing core.Thm, entry *registry.ProofEntry) []proof.DefinitionRule {
	rules, err := proof.DefinitionSimpRules(shape, characterizing)
	if err != nil {
		panic(fmt.Sprintf("define %s: %v — engine fault", name, err))
	}
	for _, r := range rules {
		s.simpRules = append(s.simpRules, sessionSimpRule{rule: r.Rule, cert: r.Cert, entry: entry})
	}
	return rules
}

// sessionDataDefine is one datatype definition move's session record:
// the type name plus the INJ/DISTINCT statements (nil when the shape
// has none) — what the emit layer needs to name the future
// entries (`<fam>.<ExportedType>Inj` / …Distinct / …Induct).
type sessionDataDefine struct {
	typeName string
	inj      core.Prop
	distinct core.Prop
}

// CheckpointInfo is the public metadata for one stored checkpoint within a
// session. Enumerated via ListCheckpoints — load-bearing for the proving
// loop's resume mode (.claude/agents/xugo-prover.md §"Resume mode"): a
// fresh agent inheriting a session needs to see what restore points the
// prior attempt left so it can roll back to a good state instead of being
// forced to either continue blindly or discard.
type CheckpointInfo struct {
	ID            string    `json:"id"`
	Name          string    `json:"name,omitempty"`
	CreatedAt     time.Time `json:"created_at"`
	NumOpenLeaves int       `json:"num_open_leaves"`
	NumSections   int       `json:"num_sections"`
}

type pendingPlan struct {
	plan *proof.ExpansionPlan
	// tactic is the request the plan came from — what the lineage
	// records when CommitPlan lands it.
	tactic    TacticReq
	goalID    string
	sectionID int
	nodePath  []int // path from section root to target node
}

// CreateSession starts a new proof session with its own proof state and theorem cache.
func (e *Engine) CreateSession(ctx context.Context) (*SessionInfo, error) {
	s := e.newSession(uuid.New().String(), time.Now())
	e.mu.Lock()
	e.sessions[s.ID] = s
	e.mu.Unlock()
	return &SessionInfo{ID: s.ID, CreatedAt: s.CreatedAt}, nil
}

// newSession builds an empty session under the given identity, its
// lineage opened (lineage.go). Not yet registered with the engine.
func (e *Engine) newSession(id string, createdAt time.Time) *Session {
	return &Session{
		ID:             id,
		CreatedAt:      createdAt,
		env:            e.env,
		derivPool:      e.derivPool,
		goalIndex:      make(map[string]*goalEntry),
		defineTexts:    map[string]emit.DefinitionText{},
		cards:          map[string]*sessionCard{},
		checkpoints:    make(map[string]*sessionCheckpoint),
		pendingPlans:   make(map[string]*pendingPlan),
		autoMatchCache: &proof.ThmCache{},
		lineage:        &sessionLineage{ID: id, CreatedAt: createdAt},
		lineageStore:   e.sessionStore,
		faultStore:     e.faultStore,
	}
}

// CloseSession ends a session and frees resources.
func (e *Engine) CloseSession(ctx context.Context, sessionID string) error {
	e.mu.Lock()
	defer e.mu.Unlock()
	if _, ok := e.sessions[sessionID]; !ok {
		return e.sessionMissingLocked(sessionID)
	}
	delete(e.sessions, sessionID)
	return nil
}

func (e *Engine) getSession(sessionID string) (*Session, error) {
	e.mu.Lock()
	defer e.mu.Unlock()
	s, ok := e.sessions[sessionID]
	if !ok {
		return nil, e.sessionMissingLocked(sessionID)
	}
	return s, nil
}

// sessionMissingLocked is the refusal for an id that names no live
// session: a session whose resume is replaying (lineage.go) joins the
// live sessions when its replay ends, and until then every call on it
// is refused for that reason. e.mu is held.
func (e *Engine) sessionMissingLocked(sessionID string) error {
	if _, resuming := e.resumes[sessionID]; resuming {
		return fmt.Errorf("session %s is being resumed: session-create {\"resume\":\"%s\"} waits for its replay and returns the result", sessionID, sessionID)
	}
	return fmt.Errorf("session %s not found", sessionID)
}

// GetSession returns a session by ID. Exported for CLI use.
func (e *Engine) GetSession(sessionID string) (*Session, error) {
	return e.getSession(sessionID)
}

// SetSessionFamily binds a fresh session to a family — the
// chapter it works — and to the further families it imports. The
// session starts with every bound family's registered definitions
// installed as use rules, exactly as if it had `define`d them:
// proof.DefinitionSimpRules over each entry's served shape
// (registry.ProofEntry.Definition, a value computed at registration)
// and its replay promise (serve.EntryThm) — the ONE dispatch the
// define door and this import share, so the two sides cannot drift and
// nothing re-analyzes the equations. A simp fire on an imported rule
// records a cite of the entry (emit renders the typed dep).
//
// Must be called before any goal is added — the installed set is the
// session's starting state, not a mid-proof change. A session bound
// to no family has the same semantics with nothing installed.
func (e *Engine) SetSessionFamily(sessionID, family string, imports []string) (*FamilyBinding, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if err := s.faultRefusal(); err != nil {
		return nil, err
	}
	return e.setSessionFamilyLocked(s, family, imports)
}

// setSessionFamilyLocked is SetSessionFamily under the session lock.
func (e *Engine) setSessionFamilyLocked(s *Session, family string, imports []string) (*FamilyBinding, error) {
	if len(s.sections) > 0 {
		return nil, fmt.Errorf("session %s already has %d goal(s) — the family must be bound before any add-goal",
			s.ID, len(s.sections))
	}
	if s.family != nil {
		return nil, fmt.Errorf("session %s is already bound to family %s", s.ID, s.family.Name)
	}
	lookup := func(name string) (*registry.Family, error) {
		f, ok := registry.FamilyByName(name)
		if !ok {
			return nil, fmt.Errorf("family %q is not registered (the registry links %d families; "+
				"a family landed after this serve was built also misses — rebuild and restart)",
				name, len(registry.Families()))
		}
		return f, nil
	}
	fam, err := lookup(family)
	if err != nil {
		return nil, err
	}
	bound := []*registry.Family{fam}
	for _, name := range imports {
		f, err := lookup(name)
		if err != nil {
			return nil, err
		}
		if slices.Contains(bound, f) {
			return nil, fmt.Errorf("family %s is imported twice", f.Name)
		}
		bound = append(bound, f)
	}
	binding := &FamilyBinding{Family: fam.Name, Imports: imports}
	door := familySpelling(fam)
	for _, f := range bound {
		for _, entry := range f.Entries() {
			if entry.Simp {
				// The chapter's simp set (registry.ProofEntry.Simp): the
				// theorem as stated, backed by its replay promise.
				cert := serve.EntryThm(s.env, entry)
				s.simpRules = append(s.simpRules, sessionSimpRule{rule: cert, cert: cert, entry: entry})
				binding.Installed = append(binding.Installed, InstalledRule{
					Entry: entry.Name, Shape: "simp", Rule: door.Prop(cert)})
				continue
			}
			if entry.Definition == proof.NotADefinition {
				continue
			}
			rules := s.installDefinitionRules(entry.Name, entry.Definition, serve.EntryThm(s.env, entry), entry)
			for _, r := range rules {
				binding.Installed = append(binding.Installed, InstalledRule{
					Entry: entry.Name, Shape: entry.Definition.String(), Rule: door.Prop(r.Rule)})
			}
		}
	}
	s.family = fam
	s.imports = bound[1:]
	s.recordFamily(family, imports)
	return binding, nil
}

// AddGoal adds a new proof goal to the session as a new section and
// returns its goal ID.
func (s *Session) AddGoal(goal core.Prop) string {
	return s.addGoalNode(proof.CreateGoalStack(goal), nil)
}

// AddGoalWith is AddGoal for a goal stated with an abbreviation table
// (sectionState.abbreviations): the texts of the section's proof
// spell the table's names, and its emitted member declares them. The
// session's names are one table (abbreviationTable), so a goal whose
// table declares a name an earlier section declares with another text
// is refused, the error naming the clash.
func (s *Session) AddGoalWith(goal core.Prop, abbreviations *dsl.AbbreviationTable) (string, error) {
	if err := s.abbreviationClash(abbreviations); err != nil {
		return "", err
	}
	return s.addGoalNode(proof.CreateGoalStack(goal), abbreviations), nil
}

// abbreviationClash is why table cannot join the session's: an entry
// whose name an earlier section declares with another text — one name,
// one meaning, in a session as in a chapter. nil when every name it
// shares with a section is declared alike.
func (s *Session) abbreviationClash(table *dsl.AbbreviationTable) error {
	for _, a := range table.Entries() {
		for i, sec := range s.sections {
			for _, b := range sec.abbreviations.Entries() {
				if b.Name == a.Name && b.Text != a.Text {
					return fmt.Errorf("abbreviation «%s» is declared by section %d as `%s` and by this goal as `%s` — "+
						"one name, one meaning: a session's sections spell one table, the member's. "+
						"Rename the entry in one of the two, or prove this goal in a session of its own",
						a.Name, i, b.Text, a.Text)
				}
			}
		}
	}
	return nil
}

// addGoalNode adds node as a new section's root, indexes it and
// records the goal in the lineage.
func (s *Session) addGoalNode(node *proof.GoalStackNode, abbreviations *dsl.AbbreviationTable) string {
	sec := &sectionState{root: node, abbreviations: abbreviations}
	s.sections = append(s.sections, sec)
	s.rebuildGoalIndex()
	for id, entry := range s.goalIndex {
		if entry.node == node {
			s.recordGoal(node.Goal, len(s.sections)-1, id, abbreviations)
			return id
		}
	}
	panic("unreachable: just-added goal not in index")
}

// abbreviationTable is the session's abbreviations as one table: the
// chapter's (registry.Family.WithAbbrev) for a session bound to a
// family, then every section's, in section order, a name two sections
// declare — alike, AddGoalWith refusing a second text — one entry. The
// texts of a session are read under it, and the output door folds a
// printed term back into it. nil when neither the family nor any
// section declares any.
func (s *Session) abbreviationTable() *dsl.AbbreviationTable {
	return s.abbreviationTableOf(s.sections)
}

// abbreviationTableOf is the one table of the given sections under the
// session's family's, as abbreviationTable merges a session's.
func (s *Session) abbreviationTableOf(sections []*sectionState) *dsl.AbbreviationTable {
	var family *dsl.AbbreviationTable
	if s.family != nil {
		family = s.family.AbbrevTable()
	}
	return abbreviationTableUnder(family, sections)
}

// abbreviationTableUnder is the one table of the given sections under
// family (nil for none): family's entries first, then each section's
// in order, a name declared again one entry. A name declared with two
// texts is the inconsistency AddGoalWith refuses, so it panics here.
func abbreviationTableUnder(family *dsl.AbbreviationTable, sections []*sectionState) *dsl.AbbreviationTable {
	var tables []*dsl.AbbreviationTable
	if family != nil {
		tables = append(tables, family)
	}
	for _, sec := range sections {
		if sec.abbreviations != nil {
			tables = append(tables, sec.abbreviations)
		}
	}
	switch len(tables) {
	case 0:
		return nil
	case 1:
		return tables[0]
	}
	var entries dsl.Abbrev
	declared := map[string]int{}
	for _, t := range tables {
		for _, a := range t.Entries() {
			if i, seen := declared[a.Name]; seen {
				if entries[i].Text != a.Text {
					panic(fmt.Sprintf("abbreviation «%s» is declared as `%s` and as `%s` in one session", a.Name, entries[i].Text, a.Text))
				}
				continue
			}
			declared[a.Name] = len(entries)
			entries = append(entries, a)
		}
	}
	// Each table parsed on its own, and a name declared again is
	// declared alike, so every entry a text spells stands before it in
	// the union as it did in its own table.
	table, err := dsl.ParseAbbreviations(entries)
	if err != nil {
		panic(fmt.Sprintf("the session's abbreviation tables do not read as one: %v", err))
	}
	return table
}

// runAutoMatch walks every open leaf in every section and closes the ones
// a PROVED sibling section states (applyAutoMatchOnRoots). The automatic
// pipeline never cites the library: a registry entry closes a leaf only
// when the author asks — `known`, a premise listed in by / auto_with /
// simp_with, a `lemma` cite. Returns the list of closed subgoals.
func (s *Session) runAutoMatch() []AutoMatchedGoal {
	roots := make([]*proof.GoalStackNode, len(s.sections))
	for i, sec := range s.sections {
		roots[i] = sec.root
	}
	return s.applyAutoMatchOnRoots(roots, s.autoMatchCache)
}

// corpusBackedInjection returns the (goal-shaped, normalized) Props to inject
// into a known-thm cache to close a leaf against the registry entry whose
// own key is `key`: PromiseByKey returns the entry's real, FORCEABLE
// promise (serve.RegisterAll registered it at startup). The normalized
// promise is α-gated to the corpus proof; the goal-shaped one is that
// promise reconstructed back to goal shape (`reconstruct`, the EndoFunc
// PreCNFCache.Normalize returns). At replay the promise forces to a real
// kernel cert via the entry's Build.
//
// An env that serves no builder for the key (an engine test's mock env,
// which links the registry but never runs serve.RegisterAll) gets a
// promise whose builder PANICS at force time: session-time semantics
// are unchanged, and a replay that reaches the cite fails loudly and
// attributably. No path fabricates a certificate. A key that names no
// registry entry, no card of this session and no served builder is a
// programming error and panics here: a leaf closed on such a promise
// would complete a section on a statement nothing proves (a rule given
// by text once reached this door under a key computed from its own
// statement).
func (s *Session) corpusBackedInjection(
	key core.PropKey, normalized core.Prop,
	reconstruct func(core.Prop) core.Prop,
) (raw, norm core.Prop) {
	// A card this session minted (defer.go) is served as its axiom: a
	// promise at the normalized form, settled by bridging the axiom
	// to it — session-scoped, registered in no env, so another
	// session never closes on it.
	if card := s.cardFor(string(key)); card != nil {
		axiom := card.axiom
		normProm := core.Promise(normalized, func(f core.Forcer) core.ThmCert {
			if axiom.AlphaEquals(normalized) {
				return axiom
			}
			bridged := prop.BridgeNormalize(normalized, prop.WrapProp(axiom))
			if bridged == nil {
				panic(fmt.Sprintf("card %s: its axiom does not normalize-coincide with the cited form %s",
					card.entry, normalized.AlphaKey()))
			}
			return f.Force(core.AsThm(bridged))
		})
		return reconstruct(normProm), normProm
	}
	if s.env != nil {
		if normProm := s.env.PromiseByKey(key, normalized); normProm != nil {
			return reconstruct(normProm), normProm
		}
	}
	if _, ok := registryEntry(string(key)); !ok {
		panic(fmt.Sprintf("corpus-backed injection under %q: the key names no registry entry, "+
			"no card of this session and no served builder — nothing backs a promise at %s",
			key, prop.PrintProp(normalized)))
	}
	failingProm := core.Promise(normalized, func(f core.Forcer) core.ThmCert {
		panic(fmt.Sprintf(
			"registry entry %q has no registered builder in this env — "+
				"serve.RegisterAll registers every entry under its own key at "+
				"startup; this cite cannot be forced here",
			key))
	})
	return reconstruct(failingProm), failingProm
}

// applyAutoMatchOnRoots is the per-leaf auto-match core, factored out so
// probe can run the same prediction non-destructively against a clone.
// Walks each given root's unsolved leaves; a leaf a PROVED sibling
// section states closes on the section's promise (injected into `cache`,
// then ApplyKnown).
// Mutates the leaves of the given roots and the given cache; does NOT
// touch s.sections directly.
//
// Loops until a full pass produces no matches, because closing one leaf
// can promote internal nodes and expose new leaves (though in practice the
// tree shape is already fixed by whatever tactic just ran — this is just a
// safety measure).
func (s *Session) applyAutoMatchOnRoots(roots []*proof.GoalStackNode, cache *proof.ThmCache) []AutoMatchedGoal {
	normalizeCache := &prop.PreCNFCache{}
	var matched []AutoMatchedGoal
	for {
		changedThisPass := false
		for _, root := range roots {
			for _, leaf := range root.UnsolvedLeaves() {
				if leaf.Proved() {
					continue
				}
				normalized, _ := normalizeCache.Normalize(leaf.Goal)
				if normalized.Conclusion().Equals(ext.T) {
					continue
				}
				// A PROVED sibling section whose goal α-matches the leaf
				// acts as an in-session lemma — the chapter's `Use(lemmaK)`
				// semantics. Self-reference is impossible by construction:
				// only PROVED roots are candidates, and a section with an
				// open leaf is by definition unproved.
				secThm, secIdx := s.curateSiblingThm(leaf, normalized.AlphaKey(), normalizeCache)
				if secThm == nil {
					continue
				}
				goalText := s.Spelling().Prop(leaf.Goal)
				secNorm, _ := prop.Normalize(secThm)
				cache.SaveThm(secThm, secNorm)
				if proof.ApplyKnown(leaf, cache) {
					idx := secIdx
					matched = append(matched, AutoMatchedGoal{
						GoalStatement:  goalText,
						MatchedSection: &idx,
					})
					changedThisPass = true
					// Restart the leaves iteration for this root — the tree
					// may have promoted internal nodes.
					break
				}
			}
		}
		if !changedThisPass {
			break
		}
	}
	return matched
}

// curateSiblingThm scans the session's sections for a PROVED root whose
// goal's normalized form α-matches normKey, returning its thm
// (promise-preserving, via PromisedThm) and 0-based section index — the
// curate-mode in-session lemma source (the the chapter's `Use(lemmaK)`
// semantics). Returns (nil, -1) on no match.
//
// Self-reference is impossible: only PROVED roots are candidates, and a
// section that still has an open leaf is by definition unproved — so a
// leaf can never close against its own containing section. In-session
// cycles are likewise impossible by construction (a section can only be
// cited AFTER it is fully proved; citing can't re-open it).
//
// The leaf param is unused for exclusion (per the above) but kept for
// the call-site read ("which leaf is this lookup for") and any future
// diagnostics.
func (s *Session) curateSiblingThm(leaf *proof.GoalStackNode, normKey core.PropKey, normalizeCache *prop.PreCNFCache) (core.Prop, int) {
	_ = leaf
	for i, sec := range s.sections {
		if !sec.root.Proved() {
			continue
		}
		secNorm, _ := normalizeCache.Normalize(sec.root.Goal)
		if secNorm.AlphaKey() != normKey {
			continue
		}
		return sec.root.PromisedThm(), i
	}
	return nil, -1
}

// ProvedSectionStating returns the index of a PROVED section whose root
// states goal — the normalized α-identity the sibling auto-match closes
// on — or -1. A fresh section stating exactly what a proved sibling
// states closes on that sibling at its first step and proves nothing
// of its own; the add-goal door refuses one unless told otherwise, and
// names the section it found here.
func (s *Session) ProvedSectionStating(goal core.Prop) int {
	normalizeCache := &prop.PreCNFCache{}
	normalized, _ := normalizeCache.Normalize(goal)
	_, idx := s.curateSiblingThm(nil, normalized.AlphaKey(), normalizeCache)
	return idx
}

// applyKnownFallback is the agent-facing dispatch for the `known`
// tactic. It closes `clone`'s goal via _KnownThmStep against the
// available knowledge stores, in order of locality:
//
//  1. s.autoMatchCache — trusted Thms injected by prior auto-match in
//     this session.
//  2. s.env.ThmCache — engine-wide kernel cache populated by replayed
//     proofs / preloaded deps.
//  3. A constant's own defining equation (_AxiomDefStep).
//  4. A PROVED sibling section stating the goal.
//  5. A registry entry stating the goal that the session's family can
//     cite (Session.citeRefusal) — the member's promise
//     (corpusBackedInjection) in a scratch cache, closed via ApplyKnown,
//     the same close auto-match would make on the same goal.
//
// Trivial-true goals are not handled here — FindProvedThm refuses to
// match them by design (see ApplyKnown's doc comment).
//
// The scratch caches used by (4) and (5) are discarded after the call,
// so probe/apply stay symmetric (probe doesn't pollute session state).
//
// Returns true iff the goal was closed.
func (s *Session) applyKnownFallback(clone *proof.GoalStackNode) bool {
	if proof.ApplyKnown(clone, s.autoMatchCache) {
		return true
	}
	if proof.ApplyKnown(clone, &s.env.ThmCache) {
		return true
	}
	// Const-definition fallback: the goal may BE a constant's own defining
	// equation (`∀x. c(x) = <def>(x)`) — a const-def is an "already-known
	// fact" that lives in const-meta, not the registry. Closes via
	// _AxiomDefStep (Type-1: no dep; Type-2: DefSource), the same path
	// def_expand records — so no new record/replay surface. A const's
	// defining axiom is a DAG leaf and cannot form a cycle.
	if proof.TryCloseByConstDef(clone) {
		return true
	}
	normalizeCache := &prop.PreCNFCache{}
	// A PROVED sibling section is an "already-known fact" (the
	// Use(lemmaK) semantics). Tried before the registry, mirroring
	// applyAutoMatchOnRoots' order.
	sibNormalized, _ := normalizeCache.Normalize(clone.Goal)
	if !sibNormalized.Conclusion().Equals(ext.T) {
		if secThm, _ := s.curateSiblingThm(clone, sibNormalized.AlphaKey(), normalizeCache); secThm != nil {
			secNorm, _ := prop.Normalize(secThm)
			scratch := &proof.ThmCache{}
			scratch.SaveThm(secThm, secNorm)
			if proof.ApplyKnown(clone, scratch) {
				return true
			}
		}
	}
	normalized, reconstruct := normalizeCache.Normalize(clone.Goal)
	if normalized.Conclusion().Equals(ext.T) {
		return false
	}
	entry, ok := entryByKey(string(normalized.AlphaKey()))
	if !ok || s.citeRefusal(entry) != nil {
		return false
	}
	entryKey := core.PropKey(entry.Key)
	fakeThm, normFakeThm := s.corpusBackedInjection(entryKey, normalized, reconstruct)
	scratch := &proof.ThmCache{}
	scratch.SaveThm(fakeThm, normFakeThm)
	return proof.ApplyKnownWithKey(clone, scratch, entryKey)
}

// tryCloseAsTypeVariantOfEntry is the fallback the agent-facing
// `lemma` / `lean_rw` dispatch runs when the primary tactic apply
// returns false AND the agent supplied a `LemmaKey`. It targets the
// "goal IS the lemma modulo type-variable renaming" wall: the
// type-adapter brings the lemma to α-equal-with-goal, then
// LemmaTactic's α-circular guard returns nil because the tactic
// framework forbids child goals α-equal to the parent. The agent sees
// "lemma did not apply to a goal that IS the lemma" (the wall reported
// by the live-session probe: the goal `⊢ ∀y. ∀x. y = snd(,(x, y))`
// failing `apply lemma` despite printing character-identical to the
// member).
//
// Mechanism: drive the existing `applyAutoMatchTypeInstanceOnRoots`
// against the clone with the entry's statement as source. Its
// identical-α-key branch injects a trusted Thm for the goal and
// ApplyKnown closes it; its NormalizedPropTypeMatch branch handles the
// type-instance / type-variant case where the goal carries different
// type-var names than the entry.
//
// Only fires when the lemma is a registry entry (`tactic.LemmaKey`
// resolves): an ad-hoc inline `lemma({lemma:...})` has no key for dep
// recording, and falling through to the failure path avoids
// corrupting the dep tracking. Reuses the session's auto-match cache
// so the recorded close is visible to subsequent steps.
//
// Returns true iff the fallback closed the clone's leaf.
func (e *Engine) tryCloseAsTypeVariantOfEntry(s *Session, clone *proof.GoalStackNode, tactic TacticReq) bool {
	if tactic.LemmaKey == "" {
		return false
	}
	var sourceKey core.PropKey
	var source core.Prop
	var name string
	if entry, ok := registryEntry(tactic.LemmaKey); ok {
		sourceKey, source, name = core.PropKey(entry.Key), entry.Statement().Prop, entry.Name
	} else if card := s.cardFor(tactic.LemmaKey); card != nil {
		sourceKey, source, name = card.key, card.statement, card.entry
	} else {
		return false
	}
	matched := s.applyAutoMatchTypeInstanceOnRoots(
		[]*proof.GoalStackNode{clone}, sourceKey, source, []string{name}, s.autoMatchCache)
	return len(matched) > 0
}

// goalIsEntryModuloNormalize reports whether a hyp-free goal and the
// entry or card `tactic.LemmaKey` names are one proposition modulo
// Normalize and the names of its type variables: equal normal-form
// keys, or normal forms one of which renames the other's type variables
// one to one. The test Go's `Cite` makes before it installs; a type
// instance of the entry that is no variant is the install's to adapt.
func (e *Engine) goalIsEntryModuloNormalize(s *Session, goal core.Prop, tactic TacticReq) bool {
	if tactic.LemmaKey == "" || goal.NumHyps() != 0 {
		return false
	}
	var source core.Prop
	if entry, ok := registryEntry(tactic.LemmaKey); ok {
		source = entry.Statement().Prop
	} else if card := s.cardFor(tactic.LemmaKey); card != nil {
		source = card.statement
	} else {
		return false
	}
	if source.NumHyps() != 0 {
		return false
	}
	normGoal, _ := prop.Normalize(goal)
	normSource, _ := prop.Normalize(source)
	if normGoal.AlphaKey() == normSource.AlphaKey() {
		return true
	}
	_, variant := prop.IsTypeVariantOf(normSource, normGoal)
	return variant
}

// runAutoMatchTypeInstance closes open leaves that are type-instantiations of
// a just-applied entry. This handles lemma reproduction subgoals whose
// printed normalized form matches the entry's statement, but whose AlphaKey
// differs because lemma type adaptation renamed type variables to the
// goal-side names.
//
// Also closes leaves whose normalized form alpha-equals the source's normalized
// form (no type renaming needed) — typically the lemma's own reproduction
// subgoal. That case is the agent-driven `lemma({key:K})` pattern: the
// residual is K's own statement, and we already know the source key K
// explicitly, so we close it precisely against K.
func (s *Session) runAutoMatchTypeInstance(sourceKey core.PropKey, source core.Prop, names []string) []AutoMatchedGoal {
	roots := make([]*proof.GoalStackNode, len(s.sections))
	for i, sec := range s.sections {
		roots[i] = sec.root
	}
	return s.applyAutoMatchTypeInstanceOnRoots(roots, sourceKey, source, names, s.autoMatchCache)
}

// applyAutoMatchTypeInstanceOnRoots is the per-leaf type-instance core,
// factored out so probe can run the same prediction non-destructively
// against a clone. Mutates the leaves of the given roots; does NOT touch
// s.sections directly. See runAutoMatchTypeInstance for semantics.
//
// `cache` receives trusted Thms for the identical-alpha-key close path (the
// "lemma's own reproduction subgoal" case). Apply callers pass
// s.autoMatchCache so the trusted thm persists; probe callers pass a
// scratch cache so prediction stays non-destructive.
func (s *Session) applyAutoMatchTypeInstanceOnRoots(roots []*proof.GoalStackNode, sourceKey core.PropKey, source core.Prop, names []string, cache *proof.ThmCache) []AutoMatchedGoal {
	if source == nil {
		return nil
	}
	normalizeCache := &prop.PreCNFCache{}
	normalizedSource, reconstructSource := normalizeCache.Normalize(source)
	if normalizedSource.NumHyps() != 0 {
		return nil
	}
	// Promise-back a bare source ONCE, up front. A source read off a
	// registry entry is a statement, not a certificate; the type-instance closes
	// below (_TypeInstStep via proof.ApplyTypeInst) thread the source into
	// the session's cert graph, so it must be an honest Thm — a real corpus
	// promise (a forceable entry Build) or a fail-at-force promise that surfaces a
	// missing build loudly at replay. Same mechanism, same key, as the
	// identical-alpha-key branch's injection; the raw shape is the normalized
	// promise reconstructed back through Normalize's functor, so both applySource
	// candidates below (normalized and raw) stay statement-identical to the
	// pre-promise forms. ApplyTypeInst asserts this contract (the former
	// core.TestThm lift there is gone).
	if !source.Proved() && !core.IsPromised(source) {
		source, normalizedSource = s.corpusBackedInjection(
			sourceKey, normalizedSource, reconstructSource)
	}

	var matched []AutoMatchedGoal
	for {
		changedThisPass := false
		for _, root := range roots {
			leaves := root.UnsolvedLeaves()
			for _, leaf := range leaves {
				if leaf.Proved() {
					continue
				}
				if leaf.Goal.NumHyps() != 0 {
					continue
				}
				normalizedLeaf, _ := normalizeCache.Normalize(leaf.Goal)
				if normalizedLeaf.NumHyps() != 0 {
					continue
				}

				// Identical-alpha-key branch: the leaf is the lemma's own
				// reproduction subgoal (typical of `lemma({key:K})` whose
				// residual is K's statement). We know the source's
				// identity is sourceKey by construction — close via
				// trusted-Thm injection + ApplyKnown, recording sourceKey
				// as MatchedKey. This is precise: no candidate guessing.
				// NormalizedPropTypeMatch refuses this
				// case by design (line 160-162 in prover/proof/try.go), so we
				// can't reuse the type-substitution path below.
				if normalizedLeaf.AlphaKey() == normalizedSource.AlphaKey() {
					if cache == nil {
						continue
					}
					// The source is its own certificate — a reading's
					// derived theorem, an installed definition's promise,
					// or the corpus-backed promise the block above gave a
					// registry entry — and the leaf closes on it.
					cache.SaveThm(source, normalizedSource)
					goalText := s.Spelling().Prop(leaf.Goal)
					// sourceKey is stamped onto the recorded step: the key
					// we know by construction here is what emit must
					// resolve through.
					if !proof.ApplyKnownWithKey(leaf, cache, sourceKey) {
						continue
					}
					matched = append(matched, AutoMatchedGoal{
						GoalStatement: goalText,
						MatchedKey:    string(sourceKey),
						MatchedNames:  names,
					})
					changedThisPass = true
					break
				}

				// The canonical forms match in the common case. Every other
				// form of the source a leaf can be an instance of — a raw
				// image, a by premise's install form or its telescope at a
				// tuple, an instance whose Normalize diverged from the
				// source's — is the step's to read, so the raw source goes
				// to the step when the step says it closes the leaf; it
				// carries sourceKey, and Normalize(raw).AlphaKey is the
				// source's own key besides.
				applySource := normalizedSource
				if _, ok := proof.NormalizedPropTypeMatch(normalizedSource, normalizedLeaf); !ok {
					if !proof.TypeInstCloses(source, leaf.Goal) {
						continue
					}
					applySource = source
				}
				goalText := s.Spelling().Prop(leaf.Goal)
				if !proof.ApplyTypeInstWithKey(leaf, applySource, sourceKey) {
					continue
				}
				matched = append(matched, AutoMatchedGoal{
					GoalStatement: goalText,
					MatchedKey:    string(sourceKey),
					MatchedNames:  names,
				})
				changedThisPass = true
				break
			}
		}
		if !changedThisPass {
			break
		}
	}
	return matched
}

func (s *Session) rebuildGoalIndex() {
	s.goalIndex = make(map[string]*goalEntry)
	for secIdx, sec := range s.sections {
		s.indexNode(sec.root, secIdx, 0)
	}
	// rebuildGoalIndex is the single post-mutation choke point, so this is
	// also where newly-CLOSED sub-derivations get published to the
	// engine-global pool for cross-session cite-node grafting.
	s.publishClosedSubtrees()
}

func (s *Session) indexNode(n *proof.GoalStackNode, secIdx, depth int) {
	if n.Proved() {
		return // proved nodes don't need IDs
	}
	if n.NumUnsolvedLeaves() == 0 {
		return
	}
	// Leaf node: unsolved, no expansion yet.
	leaves := n.UnsolvedLeaves()
	if len(leaves) == 1 && leaves[0] == n {
		// This is an actual unsolved leaf.
		s.indexOpenLeaf(n, secIdx, depth)
		return
	}
	// Internal node with unsolved children: index each child.
	for _, leaf := range leaves {
		s.indexOpenLeaf(leaf, secIdx, depth+1)
	}
}

// indexOpenLeaf inserts one open leaf into the goalIndex under its
// content-addressed id. Ids derive from the goal's alpha-key, so two
// DISTINCT open leaves with α-equal goals (e.g. the rule-reproduction
// children that both induction cases' auto-rewrites leave behind) would
// collide: a map overwrite would silently drop one of them, making
// `num_open` under-count the real tree and the shadowed leaf
// unaddressable (inspect reporting 1 open while the tree holds 2).
// A deterministic "#<n>" ordinal in tree-walk order disambiguates:
// the first occurrence keeps the bare id, later ones get
// "#2", "#3", …. Lookups are exact map hits either way.
func (s *Session) indexOpenLeaf(leaf *proof.GoalStackNode, secIdx, depth int) {
	baseID := fmt.Sprintf("s%d_g%s", secIdx, shortKey(leaf.Goal))
	id := baseID
	for ord := 2; ; ord++ {
		if _, taken := s.goalIndex[id]; !taken {
			break
		}
		id = fmt.Sprintf("%s#%d", baseID, ord)
	}
	s.goalIndex[id] = &goalEntry{node: leaf, sectionID: secIdx, depth: depth}
}

// openLeafID resolves the goalIndex id for an open leaf by node
// identity, so response builders report the SAME id (including any
// "#<n>" collision ordinal) that a follow-up apply/probe lookup will
// resolve. Falls back to the bare content-addressed id when the leaf
// isn't indexed (clone trees in probe paths).
func (s *Session) openLeafID(leaf *proof.GoalStackNode, secIdx int) string {
	for id, e := range s.goalIndex {
		if e.node == leaf {
			return id
		}
	}
	return fmt.Sprintf("s%d_g%s", secIdx, shortKey(leaf.Goal))
}

// shortKey returns a short stable ID derived from a prop's alpha key.
func shortKey(p core.Prop) string {
	k := string(p.AlphaKey())
	if len(k) > 16 {
		k = k[:16]
	}
	return k
}

// closedNodeID returns the stable ID format for a closed (proved) node,
// distinct from the open-leaf "g" prefix used by indexNode. The "c" prefix
// makes inspect output unambiguous: an ID starting with `s<N>_c…` is a
// citable closed sub-derivation; `s<N>_g…` is an open subgoal.
//
// Collision policy: first-walked wins. Two closed nodes whose Goal has the
// same α-key prove the same statement (modulo the hyp context); citing
// either is correct, so collapsing them is OK for v1. Tracked at the
// walker layer (walkClosedSubtrees), not here.
func closedNodeID(secIdx int, p core.Prop) string {
	return fmt.Sprintf("s%d_c%s", secIdx, shortKey(p))
}

// walkClosedSubtrees visits every TOP-LEVEL closed sub-derivation in the
// session's section trees and invokes `visit` per node. Top-level = a
// proved node whose ancestors are not all themselves proved (concretely:
// we don't descend into a closed subtree because its descendants ARE the
// proof of the top-level closed node, not separately citable).
//
// Order: section-index ascending, then DFS within each section. Bounded
// only by the size of the open frontier above closed nodes — once we hit
// a proved node we stop.
func (s *Session) walkClosedSubtrees(visit func(id string, secIdx, depth int, n *proof.GoalStackNode)) {
	var walk func(n *proof.GoalStackNode, secIdx, depth int)
	walk = func(n *proof.GoalStackNode, secIdx, depth int) {
		if n == nil {
			return
		}
		if n.Proved() {
			visit(closedNodeID(secIdx, n.Goal), secIdx, depth, n)
			return
		}
		for _, c := range n.Children() {
			walk(c, secIdx, depth+1)
		}
	}
	for secIdx, sec := range s.sections {
		walk(sec.root, secIdx, 0)
	}
}

// lookupClosedNode finds a closed sub-derivation by the ID format
// closedNodeID emits. Returns (node, sectionID, true) on hit; nil on miss.
// O(N) over the open-frontier interior nodes per section; rare enough that
// a persistent index is overkill for v1.
func (s *Session) lookupClosedNode(nodeID string) (*proof.GoalStackNode, int, bool) {
	var found *proof.GoalStackNode
	var foundSecIdx int
	s.walkClosedSubtrees(func(id string, secIdx, depth int, n *proof.GoalStackNode) {
		if found == nil && id == nodeID {
			found = n
			foundSecIdx = secIdx
		}
	})
	if found != nil {
		return found, foundSecIdx, true
	}
	return nil, 0, false
}

func (s *Session) buildStateView() *StateView {
	var goals []GoalView
	for id, entry := range s.goalIndex {
		goals = append(goals, goalView(id, entry))
	}
	numOpen := len(goals)
	complete := numOpen == 0 && len(s.sections) > 0
	return &StateView{Goals: goals, NumOpen: numOpen, Complete: complete, Spelling: s.Spelling()}
}

// goalView is one open goal as the state views list it.
func goalView(id string, entry *goalEntry) GoalView {
	return GoalView{
		ID:           id,
		Statement:    entry.node.Goal,
		Hypotheses:   entry.node.Goal.Hyps(),
		Depth:        entry.depth,
		SurfaceNames: surfaceNamesView(entry.node.Goal),
	}
}

// buildStateViewFromRoot builds a StateView from a standalone section root,
// used for CompareAll previews without mutating the session's goalIndex.
func (s *Session) buildStateViewFromRoot(root *proof.GoalStackNode) *StateView {
	leaves := root.UnsolvedLeaves()
	goals := make([]GoalView, len(leaves))
	for i, leaf := range leaves {
		goals[i] = GoalView{
			ID:         fmt.Sprintf("preview_%d", i),
			Statement:  leaf.Goal,
			Hypotheses: leaf.Goal.Hyps(),
		}
	}
	complete := len(leaves) == 0
	return &StateView{Goals: goals, NumOpen: len(leaves), Complete: complete, Spelling: s.Spelling()}
}

// ---------------------------------------------------------------------------
// Stateless checks
// ---------------------------------------------------------------------------

// CheckDerivation checks whether conclusion follows from premises.
// No session required. Returns structured diagnostics on failure.
func (e *Engine) CheckDerivation(ctx context.Context, req *CheckDerivationRequest) (*CheckDerivationResult, error) {
	timeout := time.Duration(req.TimeoutMs) * time.Millisecond
	if timeout == 0 {
		timeout = 200 * time.Millisecond
	}
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	// Classify goal for capability boundary detection.
	goalClass, unsupportedConsts := classifyGoal(req.Conclusion, e.domainRegistry)

	// For unsupported domains, return unknown immediately (don't waste time on proof search).
	// Skip this check when SkipDomainChk is set (library reconstruction — we have
	// known-correct premises and want to attempt verification regardless of domain).
	if goalClass == GoalUnsupported && !req.SkipDomainChk {
		return &CheckDerivationResult{
			Result: ResultUnknown,
			CapabilityHint: &CapabilityHint{
				Reason:            "unsupported_domain",
				UnsupportedConsts: unsupportedConsts,
			},
			Diagnostics: []Diagnostic{{
				Type:    DiagMissingPremise,
				Message: fmt.Sprintf("goal contains constants not in any registered domain: %v", unsupportedConsts),
			}},
		}, nil
	}

	// Build a goal node for the conclusion.
	node := proof.CreateGoalStack(req.Conclusion)

	// Strategy 1: Try AutoExpand directly (handles tautologies + equality reasoning).
	autoAction := e.env.AutoExpandWithCtx(ctx)
	if autoAction.Apply(node) {
		if node.Proved() {
			return &CheckDerivationResult{Result: ResultValid}, nil
		}
	}

	// Strategy 2: Try each premise as a lemma, collecting per-premise results.
	type premiseResult struct {
		matched  bool      // TryLemmaTactic succeeded
		residual core.Prop // non-nil if matched but left unclosed residual
	}
	premiseResults := make([]premiseResult, len(req.Premises))

	for i, premise := range req.Premises {
		select {
		case <-ctx.Done():
			return derivationTimedOut(), nil
		default:
		}

		children, lemmaOk := proof.TryLemmaTactic(req.Conclusion, premise)
		if !lemmaOk {
			premiseResults[i] = premiseResult{matched: false}
			continue
		}

		// Lemma applies. Check if it directly proves the goal.
		if len(children) == 1 {
			return &CheckDerivationResult{Result: ResultValid}, nil
		}

		// There's a residual. Try AutoExpand on it.
		if len(children) == 2 {
			residual := children[1]
			residualNode := proof.CreateGoalStack(residual)
			if autoAction.Apply(residualNode) && residualNode.Proved() {
				return &CheckDerivationResult{Result: ResultValid}, nil
			}
			premiseResults[i] = premiseResult{matched: true, residual: residual}
		} else {
			premiseResults[i] = premiseResult{matched: true}
		}
	}

	// A search the timeout cut short is not a failed one: the failure
	// classification below would read it as invalid.
	if ctx.Err() != nil {
		return derivationTimedOut(), nil
	}

	// Build differentiated failure diagnostics.
	var diags []Diagnostic

	if len(req.Premises) == 0 {
		hyps := req.Conclusion.Hyps()
		if len(hyps) > 0 {
			diags = analyzeHypothesisChain(ctx, req.Conclusion.Conclusion(), hyps, autoAction)
		} else {
			diags = append(diags, Diagnostic{
				Type:    DiagMissingPremise,
				Message: "goal is not a tautology",
			})
		}
	} else {
		for i, pr := range premiseResults {
			if pr.matched && pr.residual != nil {
				d := Diagnostic{
					Type:    DiagPremisePartial,
					Message: fmt.Sprintf("premise %d applies but leaves residual: %s", i, prop.PrintProp(pr.residual)),
				}
				d.RepairHints = structuralRepairHints(pr.residual, req.Premises)
				diags = append(diags, d)
			} else if !pr.matched {
				diags = append(diags, Diagnostic{
					Type:    DiagPremiseNoMatch,
					Message: fmt.Sprintf("premise %d does not match goal structure", i),
				})
			}
		}
		diags = append(diags, Diagnostic{
			Type:    DiagMissingPremise,
			Message: "could not derive conclusion from given premises",
		})
	}

	// Repair hints: the moves that apply to the conclusion
	// (collectRecommendations), not just raw def_expand for every
	// definable constant in the goal.
	if len(diags) > 0 {
		recs := e.collectRecommendations(ctx, req.Conclusion, 10)
		diags[len(diags)-1].RepairHints = append(diags[len(diags)-1].RepairHints, recommendationsToHints(recs, "", 5)...)
	}

	// Determine result based on goal class.
	result := e.classifyFailure(ctx, req, goalClass, unsupportedConsts, autoAction)
	result.Diagnostics = diags
	return result, nil
}

// derivationTimedOut is CheckDerivation's answer when the deadline cut the
// search short.
func derivationTimedOut() *CheckDerivationResult {
	return &CheckDerivationResult{
		Result:         ResultUnknown,
		CapabilityHint: &CapabilityHint{Reason: "timeout"},
		Diagnostics:    []Diagnostic{{Type: DiagTimeout, Message: "timeout during derivation check"}},
	}
}

// classifyFailure determines the three-state result when proof search fails.
func (e *Engine) classifyFailure(ctx context.Context, req *CheckDerivationRequest, goalClass GoalClass, unsupportedConsts []string, autoAction proof.Macro) *CheckDerivationResult {
	switch goalClass {
	case GoalPropositional:
		// CNF refutation is complete for propositional logic.
		// Failure to prove means the goal is genuinely invalid.
		return &CheckDerivationResult{Result: ResultInvalid}

	case GoalPureFOL:
		// CNF refutation is incomplete for FOL. Try proving the negation
		// to get positive evidence of invalidity.
		if negResult := e.tryNegationProof(ctx, req, autoAction); negResult != nil {
			return negResult
		}
		return &CheckDerivationResult{
			Result:         ResultUnknown,
			CapabilityHint: &CapabilityHint{Reason: "proof_search_exhausted", Domain: "logic"},
		}

	case GoalPartiallySupported:
		return &CheckDerivationResult{
			Result: ResultUnknown,
			CapabilityHint: &CapabilityHint{
				Reason:            "partially_supported_domain",
				UnsupportedConsts: unsupportedConsts,
			},
		}

	case GoalSupported:
		// All constants in registered domains but proof failed.
		return &CheckDerivationResult{
			Result:         ResultUnknown,
			CapabilityHint: &CapabilityHint{Reason: "proof_search_exhausted"},
		}

	default: // GoalUnsupported — handled before proof attempt
		return &CheckDerivationResult{
			Result: ResultUnknown,
			CapabilityHint: &CapabilityHint{
				Reason:            "unsupported_domain",
				UnsupportedConsts: unsupportedConsts,
			},
		}
	}
}

// tryNegationProof attempts to prove the negation of the goal.
// For tautology checks (no premises): proves ¬goal.
// For derivations with premises: proves premises ⊢ ¬conclusion.
// Returns a ResultInvalid result if negation proves, nil otherwise.
func (e *Engine) tryNegationProof(ctx context.Context, req *CheckDerivationRequest, autoAction proof.Macro) *CheckDerivationResult {
	select {
	case <-ctx.Done():
		return nil // timeout, can't try negation
	default:
	}

	// Build ¬conclusion with same hypotheses.
	negConcl := ext.Not(req.Conclusion.Conclusion()).Core()
	negProp := core.MakeProp(negConcl, req.Conclusion.Hyps()...)

	negNode := proof.CreateGoalStack(negProp)
	if autoAction.Apply(negNode) && negNode.Proved() {
		return &CheckDerivationResult{Result: ResultInvalid}
	}

	// Also try with premises as lemmas on the negated goal.
	for _, premise := range req.Premises {
		children, ok := proof.TryLemmaTactic(negProp, premise)
		if !ok {
			continue
		}
		if len(children) == 1 {
			return &CheckDerivationResult{Result: ResultInvalid}
		}
		if len(children) == 2 {
			residualNode := proof.CreateGoalStack(children[1])
			if autoAction.Apply(residualNode) && residualNode.Proved() {
				return &CheckDerivationResult{Result: ResultInvalid}
			}
		}
	}

	return nil
}

// analyzeHypothesisChain decomposes a Prop's hypotheses and analyzes each one
// against the conclusion to provide per-hypothesis diagnostics. This runs only
// on failure (Strategy 1 already failed) and only when the Prop has hypotheses
// (text format "h1, h2 ⊢ conclusion").
//
// Uses structural pattern matching on terms (not TryLemmaTactic) because
// hypothesis variables are concrete boolean terms — HOL's higher-order
// unification would instantiate them freely, producing false matches.
func analyzeHypothesisChain(_ context.Context, conclusion core.Term, hyps []core.Term, _ proof.Macro) []Diagnostic {
	var diags []Diagnostic

	// Decompose the goal's top-level structure.
	goalA, goalC, goalIsImply := ext.MatchesIMPLY(conclusion)
	goalL, goalR, goalIsEq := core.MatchesEQ(conclusion)
	goalAndL, goalAndR, goalIsAnd := ext.MatchesAND(conclusion)

	// Classify each hypothesis by its structural relationship to the goal.
	type hypInfo struct {
		term           core.Term
		isImply        bool
		implyL, implyR core.Term
		isEq           bool
		eqL, eqR       core.Term
		directMatch    bool   // hypothesis alpha-equals conclusion
		relevance      string // human-readable relevance note
	}

	infos := make([]hypInfo, len(hyps))
	for i, h := range hyps {
		info := hypInfo{term: h}
		info.implyL, info.implyR, info.isImply = ext.MatchesIMPLY(h)
		info.eqL, info.eqR, info.isEq = core.MatchesEQ(h)
		info.directMatch = h.AlphaEquals(conclusion)
		infos[i] = info
	}

	// --- Implication chain analysis ---
	// For goal A ⇒ C: find hypotheses that form links in the chain A → ... → C.
	if goalIsImply {
		// Build a graph: for each implication hypothesis X ⇒ Y, record the edge.
		// Then trace reachable terms from A and backward-reachable from C.
		type edge struct {
			hypIdx   int
			from, to core.Term
		}
		var edges []edge
		for i, info := range infos {
			if info.isImply {
				edges = append(edges, edge{i, info.implyL, info.implyR})
			}
		}

		// Find which hypotheses connect to the antecedent or consequent.
		for i, info := range infos {
			if !info.isImply {
				continue
			}
			hypStr := ext.PrintTerm(hyps[i])

			if info.implyL.AlphaEquals(goalA) {
				// This hypothesis starts from A: A ⇒ Y. Need Y ⇒ C (or chain).
				if info.implyR.AlphaEquals(goalC) {
					// A ⇒ C directly — this should have been provable.
					infos[i].relevance = "directly matches goal"
				} else {
					// A ⇒ Y, need Y ⇒ C.
					// Check if any other hypothesis provides Y ⇒ C.
					gap := fmt.Sprintf("%s ⇒ %s", ext.PrintTerm(info.implyR), ext.PrintTerm(goalC))
					found := false
					for j, info2 := range infos {
						if j == i || !info2.isImply {
							continue
						}
						if info2.implyL.AlphaEquals(info.implyR) {
							found = true
							break
						}
					}
					if found {
						infos[i].relevance = fmt.Sprintf("provides %s, chain continues via another hypothesis", hypStr)
					} else {
						d := Diagnostic{
							Type: DiagPremisePartial,
							Message: fmt.Sprintf("hypothesis %d (%s) starts chain from %s but gap remains: need %s",
								i, hypStr, ext.PrintTerm(goalA), gap),
						}
						d.RepairHints = append(d.RepairHints, RepairHint{
							Description: fmt.Sprintf("have %s; need %s to complete implication chain to %s",
								hypStr, gap, ext.PrintTerm(goalC)),
						})
						diags = append(diags, d)
					}
				}
			} else if info.implyR.AlphaEquals(goalC) {
				// X ⇒ C: reaches the consequent. Need A ⇒ X.
				gap := fmt.Sprintf("%s ⇒ %s", ext.PrintTerm(goalA), ext.PrintTerm(info.implyL))
				found := false
				for j, info2 := range infos {
					if j == i || !info2.isImply {
						continue
					}
					if info2.implyR.AlphaEquals(info.implyL) {
						found = true
						break
					}
				}
				if found {
					infos[i].relevance = fmt.Sprintf("provides %s, chain connects via another hypothesis", hypStr)
				} else {
					d := Diagnostic{
						Type: DiagPremisePartial,
						Message: fmt.Sprintf("hypothesis %d (%s) reaches %s but gap remains: need %s",
							i, hypStr, ext.PrintTerm(goalC), gap),
					}
					d.RepairHints = append(d.RepairHints, RepairHint{
						Description: fmt.Sprintf("have %s; need %s to complete implication chain from %s",
							hypStr, gap, ext.PrintTerm(goalA)),
					})
					diags = append(diags, d)
				}
			}
		}

		// Trace the full chain: start from A, follow implication edges.
		// Report the longest reachable chain and where it breaks.
		reachable := map[string]bool{ext.PrintTerm(goalA): true}
		chainPath := []string{ext.PrintTerm(goalA)}
		changed := true
		for changed {
			changed = false
			for _, e := range edges {
				fromStr := ext.PrintTerm(e.from)
				toStr := ext.PrintTerm(e.to)
				if reachable[fromStr] && !reachable[toStr] {
					reachable[toStr] = true
					chainPath = append(chainPath, toStr)
					changed = true
				}
			}
		}

		goalCStr := ext.PrintTerm(goalC)
		if !reachable[goalCStr] && len(chainPath) > 1 {
			lastReachable := chainPath[len(chainPath)-1]
			diags = append(diags, Diagnostic{
				Type: DiagPremisePartial,
				Message: fmt.Sprintf("implication chain reaches %s but not %s; chain so far: %s",
					lastReachable, goalCStr, strings.Join(chainPath, " → ")),
				RepairHints: []RepairHint{{
					Description: fmt.Sprintf("need %s ⇒ %s to complete the chain", lastReachable, goalCStr),
				}},
			})
		}
	}

	// --- Equality chain analysis ---
	if goalIsEq {
		for i, info := range infos {
			if !info.isEq {
				continue
			}
			hypStr := ext.PrintTerm(hyps[i])
			// Check if this equality shares a term with the goal equality.
			if info.eqL.AlphaEquals(goalL) && !info.eqR.AlphaEquals(goalR) {
				diags = append(diags, Diagnostic{
					Type:    DiagPremisePartial,
					Message: fmt.Sprintf("hypothesis %d (%s) shares left term; need %s = %s", i, hypStr, ext.PrintTerm(info.eqR), ext.PrintTerm(goalR)),
				})
			} else if info.eqR.AlphaEquals(goalR) && !info.eqL.AlphaEquals(goalL) {
				diags = append(diags, Diagnostic{
					Type:    DiagPremisePartial,
					Message: fmt.Sprintf("hypothesis %d (%s) shares right term; need %s = %s", i, hypStr, ext.PrintTerm(goalL), ext.PrintTerm(info.eqL)),
				})
			} else if info.eqR.AlphaEquals(goalL) && !info.eqL.AlphaEquals(goalR) {
				diags = append(diags, Diagnostic{
					Type:    DiagPremisePartial,
					Message: fmt.Sprintf("hypothesis %d (%s) chains via symmetry; need %s = %s", i, hypStr, ext.PrintTerm(info.eqL), ext.PrintTerm(goalR)),
				})
			} else if info.eqL.AlphaEquals(goalR) && !info.eqR.AlphaEquals(goalL) {
				diags = append(diags, Diagnostic{
					Type:    DiagPremisePartial,
					Message: fmt.Sprintf("hypothesis %d (%s) chains via symmetry; need %s = %s", i, hypStr, ext.PrintTerm(goalL), ext.PrintTerm(info.eqR)),
				})
			}
		}
	}

	// --- Conjunction analysis ---
	if goalIsAnd {
		leftSupported := false
		rightSupported := false
		for _, info := range infos {
			if info.term.AlphaEquals(goalAndL) {
				leftSupported = true
			}
			if info.term.AlphaEquals(goalAndR) {
				rightSupported = true
			}
		}
		if !leftSupported || !rightSupported {
			var missing []string
			if !leftSupported {
				missing = append(missing, ext.PrintTerm(goalAndL))
			}
			if !rightSupported {
				missing = append(missing, ext.PrintTerm(goalAndR))
			}
			diags = append(diags, Diagnostic{
				Type:    DiagPremisePartial,
				Message: fmt.Sprintf("goal is a conjunction; missing support for: %s", strings.Join(missing, ", ")),
			})
		}
	}

	// Report hypotheses with no detected structural relationship to the goal.
	for i, info := range infos {
		if info.relevance != "" || info.directMatch {
			continue
		}
		hasStructuralDiag := false
		for _, d := range diags {
			if strings.Contains(d.Message, fmt.Sprintf("hypothesis %d ", i)) {
				hasStructuralDiag = true
				break
			}
		}
		if !hasStructuralDiag {
			diags = append(diags, Diagnostic{
				Type:    DiagPremiseNoMatch,
				Message: fmt.Sprintf("hypothesis %d (%s) has no direct structural relationship to goal %s", i, ext.PrintTerm(hyps[i]), ext.PrintTerm(conclusion)),
			})
		}
	}

	// Summary diagnostic.
	var hypStrs []string
	for _, h := range hyps {
		hypStrs = append(hypStrs, ext.PrintTerm(h))
	}
	diags = append(diags, Diagnostic{
		Type: DiagMissingPremise,
		Message: fmt.Sprintf("conclusion %s is not derivable from hypotheses [%s]",
			ext.PrintTerm(conclusion),
			strings.Join(hypStrs, ", ")),
	})

	return diags
}

// structuralRepairHints analyzes the residual left by a partial premise match
// and generates hints about what additional premise would close the gap.
func structuralRepairHints(residual core.Prop, premises []core.Prop) []RepairHint {
	concl := residual.Conclusion()
	var hints []RepairHint

	// Pattern 1: residual is an equality "a = c".
	// Look for premises of form "a = b" → suggest "b = c", or "b = c" → suggest "a = b".
	if l, r, ok := core.MatchesEQ(concl); ok {
		for _, p := range premises {
			pl, pr, pok := core.MatchesEQ(p.Conclusion())
			if !pok {
				continue
			}
			if pl.AlphaEquals(l) && !pr.AlphaEquals(r) {
				hints = append(hints, RepairHint{
					Description: fmt.Sprintf("have %s = %s; need premise %s = %s to complete equality chain",
						ext.PrintTerm(pl), ext.PrintTerm(pr),
						ext.PrintTerm(pr), ext.PrintTerm(r)),
				})
			}
			if pr.AlphaEquals(r) && !pl.AlphaEquals(l) {
				hints = append(hints, RepairHint{
					Description: fmt.Sprintf("have %s = %s; need premise %s = %s to complete equality chain",
						ext.PrintTerm(pl), ext.PrintTerm(pr),
						ext.PrintTerm(l), ext.PrintTerm(pl)),
				})
			}
			// Also check symmetric: premise "b = a" can chain via symmetry.
			if pr.AlphaEquals(l) && !pl.AlphaEquals(r) {
				hints = append(hints, RepairHint{
					Description: fmt.Sprintf("have %s = %s; need premise %s = %s to complete equality chain",
						ext.PrintTerm(pl), ext.PrintTerm(pr),
						ext.PrintTerm(pl), ext.PrintTerm(r)),
				})
			}
			if pl.AlphaEquals(r) && !pr.AlphaEquals(l) {
				hints = append(hints, RepairHint{
					Description: fmt.Sprintf("have %s = %s; need premise %s = %s to complete equality chain",
						ext.PrintTerm(pl), ext.PrintTerm(pr),
						ext.PrintTerm(l), ext.PrintTerm(pr)),
				})
			}
		}
		if len(hints) == 0 {
			hints = append(hints, RepairHint{
				Description: fmt.Sprintf("residual is %s = %s; need a premise connecting these terms",
					ext.PrintTerm(l), ext.PrintTerm(r)),
			})
		}
		return hints
	}

	// Pattern 2: residual is an implication "p ⇒ q".
	// Look for premises involving p or q to suggest the missing link.
	if l, r, ok := ext.MatchesIMPLY(concl); ok {
		for _, p := range premises {
			pl, pr, pok := ext.MatchesIMPLY(p.Conclusion())
			if !pok {
				continue
			}
			if pl.AlphaEquals(l) && !pr.AlphaEquals(r) {
				hints = append(hints, RepairHint{
					Description: fmt.Sprintf("have %s ⇒ %s; need premise %s ⇒ %s to complete implication chain",
						ext.PrintTerm(pl), ext.PrintTerm(pr),
						ext.PrintTerm(pr), ext.PrintTerm(r)),
				})
			}
			if pr.AlphaEquals(r) && !pl.AlphaEquals(l) {
				hints = append(hints, RepairHint{
					Description: fmt.Sprintf("have %s ⇒ %s; need premise %s ⇒ %s to complete implication chain",
						ext.PrintTerm(pl), ext.PrintTerm(pr),
						ext.PrintTerm(l), ext.PrintTerm(pl)),
				})
			}
		}
		if len(hints) == 0 {
			hints = append(hints, RepairHint{
				Description: fmt.Sprintf("residual is %s ⇒ %s; need a premise connecting these terms",
					ext.PrintTerm(l), ext.PrintTerm(r)),
			})
		}
		return hints
	}

	// Pattern 3: residual is a conjunction "p ∧ q".
	// Suggest providing each conjunct as a separate premise.
	if l, r, ok := ext.MatchesAND(concl); ok {
		hints = append(hints, RepairHint{
			Description: fmt.Sprintf("residual is %s ∧ %s; need both conjuncts as premises",
				ext.PrintTerm(l), ext.PrintTerm(r)),
		})
		return hints
	}

	return hints
}

// CheckConsistency checks whether a set of statements is free of contradictions.
// On inconsistency, returns a minimal conflicting subset.
func (e *Engine) CheckConsistency(ctx context.Context, req *CheckConsistencyRequest) (*CheckConsistencyResult, error) {
	if len(req.Statements) == 0 {
		return &CheckConsistencyResult{Result: ConsistencyConsistent}, nil
	}

	timeout := time.Duration(req.TimeoutMs) * time.Millisecond
	if timeout == 0 {
		timeout = 200 * time.Millisecond
	}
	ctx, cancel := context.WithTimeout(ctx, timeout)
	defer cancel()

	// Strategy: build a prop with all statements as hypotheses and F (false)
	// as conclusion. If CNF refutation succeeds, the statements are inconsistent.
	// Prop: stmt1, stmt2, ..., stmtN ⊢ ⊥
	hyps := make([]core.Term, len(req.Statements))
	for i, s := range req.Statements {
		hyps[i] = s.Conclusion()
	}
	goal := core.MakeProp(ext.F, hyps...)

	// Classify the combined goal to determine completeness.
	goalClass, _ := classifyGoal(goal, e.domainRegistry)

	// Try to refute.
	node := proof.CreateGoalStack(goal)
	autoAction := e.env.AutoExpandWithCtx(ctx)
	plan, ok := proof.TryExpandPlan(node, autoAction)
	if ok {
		node.Commit(plan)
		if node.Proved() {
			// Refutation succeeded — statements are inconsistent. The
			// certificate keeps only the hypotheses the refutation used,
			// so the conflict is the statements among them: not
			// necessarily a minimal subset, but one that is contradictory
			// on its own.
			refutation := node.PromisedThm()
			var conflict []int
			for i, s := range req.Statements {
				if refutation.HasHyp(s.Conclusion()) {
					conflict = append(conflict, i)
				}
			}
			return &CheckConsistencyResult{
				Result:         ConsistencyInconsistent,
				ConflictSubset: conflict,
				Diagnostics: []Diagnostic{{
					Type:    DiagMissingPremise,
					Message: "statements are mutually contradictory",
				}},
			}, nil
		}
	}

	// A refutation the timeout cut short shows nothing either way.
	if ctx.Err() != nil {
		return &CheckConsistencyResult{
			Result:         ConsistencyUnknown,
			CapabilityHint: &CapabilityHint{Reason: "timeout"},
			Diagnostics:    []Diagnostic{{Type: DiagTimeout, Message: "timeout during consistency check"}},
		}, nil
	}

	// Failure to find contradiction: for propositional goals, CNF is complete,
	// so the statements are genuinely consistent. For FOL/other, unknown.
	if goalClass == GoalPropositional {
		return &CheckConsistencyResult{Result: ConsistencyConsistent}, nil
	}
	return &CheckConsistencyResult{
		Result:         ConsistencyUnknown,
		CapabilityHint: &CapabilityHint{Reason: "proof_search_exhausted", Domain: "logic"},
	}, nil
}

// ---------------------------------------------------------------------------
// The session
// ---------------------------------------------------------------------------

// InspectState returns the open-goal state for a session. Lightweight: no
// structural-fact enumeration. Used internally by tests and by the
// /apply / /commit-plan response payloads where we already know the
// session and just need a fresh state snapshot.
func (e *Engine) InspectState(ctx context.Context, sessionID string) (*StateView, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	return s.buildStateView(), nil
}

// Inspect returns the session's open-goal state plus structural facts about
// the focused goal. The focused goal is determined by the request:
//
//   - GoalID set → use it (error if not in session), and Goals lists
//     that goal alone: the hypothesis indices read off goals[0] are the
//     named goal's, the ones a `by_hyps` or `instantiate` at it takes.
//     NumOpen stays the session's count.
//   - GoalID empty + 1 open goal → use that goal.
//   - GoalID empty + ≥2 open goals → return goal list only (FocusedGoalID
//     empty, StructuralFacts nil). The agent is expected to specify which
//     goal it wants facts for.
//   - GoalID empty + 0 open goals → return goal list only (Complete=true
//     when at least one section was added).
//
// Structural facts are deterministic, capped, and never carry score /
// priority / confidence. See enumerateStructuralFacts for the per-fact
// schema and cap discipline.
func (e *Engine) Inspect(ctx context.Context, sessionID string, req *InspectRequest) (*InspectResult, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	sv := s.buildStateView()
	res := &InspectResult{
		Goals:    sv.Goals,
		NumOpen:  sv.NumOpen,
		Complete: sv.Complete,
		Spelling: sv.Spelling,
	}

	// Decide which goal (if any) gets structural facts.
	var focused *goalEntry
	var focusedID string
	if req != nil && req.GoalID != "" {
		entry, ok := s.goalIndex[req.GoalID]
		if !ok {
			return nil, fmt.Errorf("goal %s not found", req.GoalID)
		}
		focused = entry
		focusedID = req.GoalID
		res.Goals = []GoalView{goalView(focusedID, entry)}
	} else if len(s.goalIndex) == 1 {
		for id, entry := range s.goalIndex {
			focused = entry
			focusedID = id
		}
	}
	if focused == nil {
		return res, nil
	}
	res.FocusedGoalID = focusedID
	// The probes that read a clock run each under the probe budget
	// (_ProbeBudget): the session lock is held for the whole pass, and
	// one probe that does not end would hold every later command of the
	// session with it.
	budgetMs := ProbeDefaultBudgetMs
	if req != nil && req.BudgetMs > 0 {
		budgetMs = req.BudgetMs
	}
	scope := faultScope(ctx, s, "inspect")
	scope.goalID, scope.section, scope.goal, scope.budgetMs = focusedID, focused.sectionID, focused.node.Goal, budgetMs
	budget := _ProbeBudget{
		ctx:    ctx,
		budget: time.Duration(budgetMs) * time.Millisecond,
		overran: func(what string, deadline time.Time, stack string) {
			e.noteOverrun(scope, what+" of inspect", deadline, stack)
		},
	}
	res.StructuralFacts, res.Truncated = enumerateStructuralFacts(budget, focused.node.Goal, e.env)

	// Populate ClosedSubtrees: citable closed sub-derivations in this
	// session. No cap — walkClosedSubtrees does NOT descend into proved
	// sub-trees (their descendants are part of the proof, not separately
	// citable), so the count is structurally bounded by the open-frontier
	// interior complexity. In practice this is single-digit-to-low-dozens
	// even for complex proofs; a defensive cap would be guarding against a
	// pathology that the walker's own shape rules out.
	s.walkClosedSubtrees(func(id string, secIdx, depth int, n *proof.GoalStackNode) {
		res.ClosedSubtrees = append(res.ClosedSubtrees, ClosedSubtreeView{
			NodeID:    id,
			Statement: sv.Spelling.Prop(n.Goal),
			HypCount:  n.Goal.NumHyps(),
			Depth:     depth,
			SectionID: secIdx,
		})
	})

	return res, nil
}

// tacticNoProgressDiagnostic returns a tactic-aware "no progress"
// diagnostic for the tactics whose failure mode is rarely "wrong shape":
// the search-y ones (expand, auto), whose failure is almost always
// "this isn't the right tool for this goal", simp_with and def_expand,
// and the named ⇔ splits, which decline where one branch subsumes the
// other. The diagnostic names the tactic's actual scope and points at
// the right alternative, replacing the generic "did not apply" /
// "exhausted without closing" wording that agents misread as a budget
// or state issue.
//
// Returns "" for tactic types that don't need the special-case message;
// callers fall through to their generic wording.
// substSizeGuardError is the `subst` refusal on an equality hypothesis
// whose rewrite does not shrink the goal — a TYPED error, because the
// apply failure path reads it: the repair the author needs is `rw` on
// the same hypothesis (the size-guard-free directed rewrite), and the
// generic hint list, which walks the goal's definable constants,
// cannot know that.
type substSizeGuardError struct{ hypIndex int }

func (e substSizeGuardError) Error() string {
	return fmt.Sprintf("subst on hyp %d had no effect (no rewrite reduced the goal size)", e.hypIndex)
}

func tacticNoProgressDiagnostic(tacticType string) string {
	switch tacticType {
	case "expand":
		return "expand made no progress on this goal. expand does single-step equational rewriting (size-shrinking only, fixpoint-safe), propositional simplification, structural splits (∧/⇔/⇒/∨), and deep hilbertRewrite ε-reduction. It does NOT chain transitivity (a=b, b=c ⊢ a=c) — each rewrite that doesn't strictly shrink is rejected by the size guard. It does NOT do congruence-under-unification across multiple hyps or CNF refutation. Those live inside `auto`. Retrying expand with a larger budget will not change this result — switch tactic."
	case "auto":
		return "auto did not close. auto's pipeline: arith fast-path → CondRewrite → BasicTactic (h⊢h, h+¬h⊢⊥, trivial-⊤ close-checks) → AutoDenote → CNF refutation on residual leaves. All stages ran to completion, and CNF has an empirical ~5s ceiling beyond which a larger budget does not help. Switch strategy: introduce a specific lemma, induction, case_split, or assert/trans with a named bridge term."
	case "simp_with":
		return "simp_with made no progress: no rule in the set fired on the selected target, and the session is unchanged. The target is the conclusion unless hyp_index selects a hypothesis. Conditional rewrites need a binder-closed redex whose match, together with side conditions matched against the other hypotheses and fact rules, pins every binder. Side conditions discharge through hypotheses, fact rules, unconditional rewrites, or descending closure rules in the set. Rules use their written direction; flip:true reverses an equation, including a conditional rule's equation. Unpinned polymorphic rules receive every distinct instance found by the finite anchor-pin enumeration, including instances exposed by rewrites; a rule the rewrite keeps exposing at new instances past the round bound is refused by name. Explicit type_specialize and read_at keep their chosen types. The set is the named rules alone; the bound families' installed definitions fire under the bare simp and simp_all. A conditional clause ending in an atom is a closure rule: it can discharge another rule's side condition, but does not itself rewrite the target."

	case "split_iff", "split_hyp_iff":
		return tacticType + " declined: the two branches of the split merge into one because one subsumes the other (`L ⊢ L ⇔ ⊥`; an ⇔-hypothesis both of whose sides are already resident), and a named ⇔ split has no branch to give its names to. Simplify the goal instead (`simplify`, `auto`), or name another ⇔-hypothesis with `hyp_index`."
	case "def_expand":
		return "def_expand did not apply — the const does appear in the goal, but no fast-path definitional rewrite fired. Three no-progress modes: (a) the fast-path walker (prover/tactic/def_expand.go) found the const but `constT.DefThm()` returned nil at that occurrence's polymorphic instance — typedef abs/rep constants have no Type-1 def thm; and for Type-1 consts like set_member, the per-occurrence PropTypeInst can bottom out on prod-type / function-type positions where the type substitution refuses (occurs-check). (b) The general LeanRw fallback DID find candidate rewrites but rejected them at unifyEq's projection-pattern ban (ext/prop/eq_rewrite.go) — patterns like λp.p or λx.λy.x match any target of their type vacuously via empty-substitution η-unification and would treadmill; the ban is universal. (c) The walk produced a rewrite but its result α-equals the input — already in normal form, or a β-cycle collapsed the change. Workaround: load the definitional lemma explicitly with top-level `type_specialize` at the required instance and `instantiate` its bound vars manually — `apply lemma({\"lemma\":{\"key\":\"<def-thm key>\"},\"type_specialize\":{\"A\":\"prod(var:A,var:B)\", ...}})`. Follow with `apply simplify` (deep β-reduce) if the goal still carries `(λp.body)(x)` residuals from a prior partial expansion."
	}
	return ""
}

// caseSplitNoProgressReason names which of ByCaseTactic's idempotence
// guards fired. Delegates to tactic.AnalyzeByCase — the SAME classifier
// ByCaseTactic itself consults to decide whether to return nil — so the
// agent-facing "why it failed" wording can never drift from the
// kernel-facing "why we refused" logic. The generic "did not apply to
// this goal" wording burned agent budget on retries because there is
// no wait-and-succeed here: the guard is deterministic given the goal,
// so the correct next move is always "pick a different term or a
// different tactic," and we should say which.
//
// `caseTerm` is the term as ByCaseTactic sees it (already resolved
// from the printed spec by resolveCaseTerm; leading-¬ normalization
// is handled inside AnalyzeByCase). `printed` is the raw
// agent-supplied string, echoed back so the agent can trace the
// message to its own call.
func caseSplitNoProgressReason(goal core.Prop, caseTerm core.Term, printed string) error {
	kind, pos, _ := tactic.AnalyzeByCase(goal, caseTerm)
	posStr := ext.PrintTerm(pos)
	switch kind {
	case tactic.ByCaseConclIsPositive:
		return fmt.Errorf(
			"case_split on %q: the (positive) term %s is already the goal's conclusion — the split is a no-op (branch 0 becomes Γ,φ ⊢ φ, branch 1 becomes Γ,¬φ ⊢ φ = the original goal). Run `auto` on the goal directly, or split on a sub-term whose truth-value the conclusion actually depends on",
			printed, posStr)
	case tactic.ByCaseConclIsNegative:
		return fmt.Errorf(
			"case_split on %q: the goal's conclusion is ¬%s — the split is a no-op for the same reason as the positive case (one branch reproduces the goal, the other closes trivially). Run `auto`, or split on a different sub-term",
			printed, posStr)
	case tactic.ByCaseHypIsPositive:
		return fmt.Errorf(
			"case_split on %q: %s is already a hypothesis — the true-branch would just restate it and the false-branch would contradict it. Use the existing hyp directly (e.g. `rewrite`, `cite`, `hyp_add`), or split on a term whose truth-value is still open in the current context",
			printed, posStr)
	case tactic.ByCaseHypIsNegative:
		return fmt.Errorf(
			"case_split on %q: ¬%s is already a hypothesis — the false-branch would just restate it and the true-branch would contradict it. Use the existing hyp, or split on a term whose truth-value is still open in the current context",
			printed, posStr)
	case tactic.ByCaseApplies:
		// ByCaseMacro.Apply returned false but AnalyzeByCase says the split
		// applies. The two must agree by construction (ByCaseTactic's only
		// no-op branch consults AnalyzeByCase) — hitting this means a
		// downstream _ByCaseStep guard rejected past the reasons we know,
		// or Apply's ExpansionPlan machinery aborted. Surface loudly rather
		// than emit a misleading "already a hyp" message.
		return fmt.Errorf(
			"case_split on %q: ByCaseMacro.Apply refused but tactic.AnalyzeByCase reports the split applies. Internal invariant broken — please report",
			printed)
	}
	return fmt.Errorf(
		"case_split on %q: unhandled ByCaseNoOpKind %d — please report",
		printed, int(kind))
}

// probeTimeoutDiagnostic returns advice for a probe that exhausted its
// budget without closing the goal. For the search-y tactics (expand,
// refute, auto) it reuses the tactic-aware "no progress" wording, which
// already names the ~5s CNF ceiling and the right alternatives; for any
// other tactic it returns a generic timeout note. A probe timeout
// returning ProbeReasonTimeout with an empty Diagnostic would give the
// agent no signal to switch tactic instead of retrying with a bigger
// budget.
func probeTimeoutDiagnostic(tacticType string, budgetMs int) string {
	if diag := tacticNoProgressDiagnostic(tacticType); diag != "" {
		return diag
	}
	return fmt.Sprintf("%s did not close within %dms (probe timeout). A larger budget is unlikely to help — switch strategy (lemma, induction, case_split, or assert/trans with a named bridge term).", tacticType, budgetMs)
}

// runTacticOnClone applies a tactic to a fresh GoalStack clone of the goal
// and returns the expanded clone. Error semantics:
//
//   - (clone, nil)  — the tactic applied; caller can read subgoals or commit.
//   - (nil, err)    — the tactic did not apply. Most cases are generic
//     ("tactic X did not apply to this goal"), but lemma
//     dispatch surfaces specific errors from resolveLemma
//     (a key that names no registry entry). The three
//     search-y tactics (expand, refute, auto) get a
//     tactic-aware message via tacticNoProgressDiagnostic.
//
// The shared evaluator backs both ApplyStep (commits the clone back into
// the session) and Probe (reads subgoals off the clone, then discards
// it). Probe and apply share an evaluator, not a strategy — same execution,
// different downstream wrapping.
// The error-vs-bool return lets each caller forward the specific reason
// to its own diagnostic channel (StepResult.Diagnostics for apply,
// ProbeResult.Diagnostic for probe).
func (e *Engine) runTacticOnClone(ctx context.Context, s *Session, goal core.Prop, tactic TacticReq) (*proof.GoalStackNode, error) {
	// The agent-facing surface has no bare `refute`; `auto` is its
	// CNF-refutation entry: arith fast-path + AutoExpand (CondRewrite +
	// BasicTactic + AutoDenote + CNFRefute per leaf). The BasicTactic
	// pass alone catches close cases a bare refute cannot (h⊢h, h+¬h⊢⊥
	// via simplestTrivialTactic's AlphaEquals check, trivial-⊤), and a
	// bare refute timing out on `H, ¬H ⊢ ⊥` reads as "the engine can't
	// close matched atoms". `_CNFRefute` is a proto-level ministep for
	// record/replay and is driven internally (set_tac ladder,
	// CloseByCNFRefute for stored Detailed steps) — this rejection
	// closes only the agent-facing dispatch (see ext/clause/cnf_test.go,
	// TestNegateGoalCNF_ExistsUnderLambdaAlphaDuplication).
	// `cnf_refute` joins the same guard rather than being aliased to
	// `auto`: it is the spelling of the Go Action (`CnfRefute()`), so an
	// author driving a proof session-first reaches for it by name and
	// gets "unknown tactic" plus a list of repair hints that say nothing
	// about the real mapping. An alias would be worse than the error —
	// `auto` also runs the arith fast-path, which a foundation-resident
	// target may not take, so the redirect has to be visible enough that
	// the caller knows to check for a recorded Arith().
	if tactic.Type == "refute" || tactic.Type == "cnf_refute" {
		return nil, fmt.Errorf("bare `%s` is retired from the agent surface — use `auto` (which runs the same CNF refuter after preprocessing that catches trivial-close cases refute alone misses, and skips CNF entirely when arith or trivial-simplify decides the goal). NOTE: because `auto` may close via the arith fast-path, check dump-section for a recorded Arith() when the target declares no capabilities", tactic.Type)
	}
	// Reset the RPC-boundary carry buffers (see Session field docs): this
	// is the single dispatch choke point, so stale entries from a probe /
	// batch caller that didn't drain can never leak into a later apply.
	if s != nil {
		s.pendingApplyDiagnostics = nil
		s.pendingAutoMatched = nil
	}
	clone := proof.CreateGoalStack(goal)
	var ok bool
	switch tactic.Type {
	case "expand":
		ok = proof.ApplySimplify(ctx, clone)
	case "apply_search":
		// Lean's `exact?`: the corpus searched for a member that CLOSES the
		// goal — exact by key, or applying by the apply rung's reading
		// (retrieve_corpus.go, the `retrieve goal` ranking) — each candidate
		// tried as a `lemma` on a clone of its own, and the first that closes
		// committed as that lemma step, so the record and the replay see a
		// cite and nothing of the search. The rest are reported. A candidate
		// that only rewrites or installs is not a close and is passed over.
		found, tried, serr := e.applySearch(ctx, s, goal)
		if serr != nil {
			return nil, serr
		}
		if found == nil {
			return nil, fmt.Errorf("apply_search: no member of the corpus closes the goal (%d candidate(s) tried: %s); name the premises and `by`, or `retrieve` for the members that apply with their open premises", len(tried), strings.Join(tried, ", "))
		}
		clone, ok = found, true
	case "lemma":
		if tactic.ReadAt != nil {
			// A structure law read at an instance (hypothesis_moves.go):
			// closes the goal it states, else installs as a resident
			// hypothesis.
			if err := e.applyLemmaReadingOnClone(s, clone, tactic); err != nil {
				return nil, err
			}
			ok = true
			break
		}
		lemmaProp, lerr := e.resolveLemma(s, tactic, goal)
		if lerr != nil {
			return nil, lerr
		}
		if lemmaProp == nil {
			return nil, fmt.Errorf("lemma tactic requires lemma_key or lemma field")
		}
		// The recorded ministep's source key. An unspecialized cite
		// records none: the loaded prop is the entry's own statement,
		// whose re-derived normalized key is the entry's own key, so
		// emit's leaf resolution finds the entry from the statement.
		//
		// Agent-supplied pre-install specializations follow. Two parallel
		// channels, applied in order: TYPE first (so binder types lose
		// their free type-vars before term-level β-substitution sees
		// them), then TERM. Each computes the lemma's pre-σ source
		// AlphaKey before mutating lemmaProp so the recorded
		// `polymorphicSourceKey` still points at the polymorphic entry
		// regardless of which σ fired.
		//
		// `type_specialize` is an explicit map (lemma's type-var name →
		// type expression); `term_specialize` is a parallel map (outer
		// ∀-binder name → witness term). For `term_specialize` the
		// witness's type is unified against the binder's type, so a
		// polymorphic binder gets pinned automatically — the agent
		// doesn't need to pre-supply a matching `type_specialize` for
		// the polymorphic binder's vars. See
		// engine/lemma_type_specialize.go +
		// engine/lemma_term_specialize.go.
		// A LemmaKey may be a registry NAME, not an entry's own
		// key — never recorded as the source; a specialization records
		// its polymorphic source below.
		var lemmaSourceKey core.PropKey
		// The letters an explicit σ read at the goal's own, held fixed
		// through the term pass (buildSpecializedLemma).
		var fixed core.VarTypePredicate = utils.EmptyPredicate[core.VarType]
		if len(tactic.TypeSpecialize) > 0 {
			specialized, goalLetters, sErr := buildSpecializedLemma(lemmaProp, tactic.TypeSpecialize, goal)
			if sErr != nil {
				return nil, sErr
			}
			if lemmaSourceKey == "" {
				lemmaSourceKey = proof.LemmaSourceKey(lemmaProp)
			}
			lemmaProp, fixed = specialized, goalLetters
		}
		// term_specialize pre-pass: resolve witnesses + compute σ_type
		// induced by binder/witness type unification. The σ_type applies
		// to the lemma BEFORE install so binder types become concrete;
		// the witnesses themselves are applied POST-install (via the
		// chain below) because LemmaTactic's hypMatching
		// auto-generalizes any goal-side free vars in the lemma's
		// concl before adding as a hyp — a pre-install β-substitute
		// would be undone by that generalization. The post-install
		// chain peels exactly those auto-generalized binders.
		var termSpecWitnesses []termSpecWitness
		if len(tactic.TermSpecialize) > 0 {
			ws, lemmaAfterTypeSig, _, sErr := e.resolveTermSpecializeWitnesses(lemmaProp, tactic.TermSpecialize, goal, s.familyScope(), fixed)
			if sErr != nil {
				return nil, sErr
			}
			if lemmaSourceKey == "" {
				lemmaSourceKey = proof.LemmaSourceKey(lemmaProp)
			}
			lemmaProp = lemmaAfterTypeSig
			termSpecWitnesses = ws
		}
		// Snapshot the focused goal's hyp set BEFORE install so the
		// post-install chain can identify the lemma's newly-added
		// ∀-headed hyp on the residual leaf.
		var origGoalHypKeys map[core.TermKey]struct{}
		if len(termSpecWitnesses) > 0 {
			origGoalHypKeys = make(map[core.TermKey]struct{}, goal.NumHyps())
			for _, h := range goal.Hyps() {
				origGoalHypKeys[h.AlphaKey()] = struct{}{}
			}
		}
		// Hypothesis-preserving install: a result that would rewrite/
		// drop a pre-existing hyp (LemmaTactic's simplifyNewGoal letting
		// a resident ∀-hyp absorb its own ground instances — the "lemma
		// load reverts my instantiate" complaint) is downgraded to a plain
		// add-as-hyp.
		// Search/macro/replay paths keep proof.ApplyLemma unchanged.
		//
		// Explicit-σ fork: when the agent has explicitly resolved the
		// lemma's type instantiation — via term_specialize's pre-pass
		// (resolveTermSpecializeWitnesses) OR an explicit type_specialize
		// map — route through the EXACT install entry point.
		// chooseTypeAdaptedStep's speculative tryAdaptLemmaTypes would
		// otherwise compute a competing σ against the goal context and
		// silently override the agent's choice whenever the σ target is
		// itself a type variable (`?27845` requested, the hyp installed
		// at `?27847`) — for term_specialize it additionally breaks the
		// post-install chain. Contract:
		// explicit σ is honored exactly or the tactic fails; only plain
		// lemma loads (no specialization) keep the adapt-enabled path so
		// polymorphic entry cites still benefit from automatic
		// type-pinning.
		switch {
		case len(termSpecWitnesses) > 0 || len(tactic.TypeSpecialize) > 0:
			ok = proof.ApplyLemmaPreserveExactWithSource(clone, lemmaProp, lemmaSourceKey)
		case e.goalIsEntryModuloNormalize(s, goal, tactic) && e.tryCloseAsTypeVariantOfEntry(s, clone, tactic):
			// The goal IS the cited entry modulo Normalize — its
			// contrapositive, its binders in another order, its type
			// variables under other names — so the cite closes it, as
			// Go's `Cite` does at its normalize tier
			// (citeNormalizedClose). Asked second, the install below
			// would succeed by adding the entry as a hypothesis beside a
			// goal it already proves.
			ok = true
		default:
			ok = proof.ApplyLemmaPreserveWithSource(clone, lemmaProp, lemmaSourceKey)
		}
		if !ok {
			ok = e.tryCloseAsTypeVariantOfEntry(s, clone, tactic)
		}
		if ok && len(termSpecWitnesses) > 0 {
			if cerr := e.applyLemmaTermSpecializeChain(clone, lemmaProp, termSpecWitnesses, origGoalHypKeys); cerr != nil {
				return nil, cerr
			}
		}
	case "type_inst":
		// A polymorphic registry entry read AT a type instance: closes the
		// focused goal when it is a type instantiation of the entry, with
		// σ recovered from the goal itself (_TypeInstStep's match
		// tiers) — the session counterpart of Go's `ctx.AtTypes(dep,
		// τ…)` / TypeInst(Thm). This is the tactic that discharges the
		// foreign-instance obligation a polymorphic `lemma` install
		// leaves open: a residual no other session tactic can close.
		src, terr := e.resolveLemmaThm(s, tactic, goal)
		if terr != nil {
			return nil, terr
		}
		ok = proof.ApplyTypeInst(clone, src)
		if !ok {
			return nil, fmt.Errorf("type_inst: the focused goal is not a type instance of %s\n  goal: %s",
				tactic.LemmaKey, prop.PrintProp(goal))
		}
	case "ac_regroup":
		// The AC kit's goal face as a session move (proof.ACRegroup /
		// ACRegroupWith): the focused goal must be the bare equation
		// `lhs = rhs` between two ⊕-sums over one leaf multiset; the
		// kit derives the rearrangement certificate from the assoc/sym
		// pair and closes (or installs) it. assoc/sym name registry
		// entries; the entries back the derivation as forceable promises —
		// the same trusted-injection channel every session cite uses.
		if tactic.Assoc == "" || tactic.Sym == "" {
			return nil, fmt.Errorf("ac_regroup requires assoc and sym — registry entries (own key or registered name) of the " +
				"⊕ associativity (∀m n p. (m⊕n)⊕p = m⊕(n⊕p)) and commutativity (∀m n. m⊕n = n⊕m) laws")
		}
		assocThm, aerr := e.resolveLemmaThm(s, TacticReq{Type: "ac_regroup", LemmaKey: tactic.Assoc}, goal)
		if aerr != nil {
			return nil, fmt.Errorf("ac_regroup assoc: %w", aerr)
		}
		symThm, serr := e.resolveLemmaThm(s, TacticReq{Type: "ac_regroup", LemmaKey: tactic.Sym}, goal)
		if serr != nil {
			return nil, fmt.Errorf("ac_regroup sym: %w", serr)
		}
		// The kit's contract violations (cert shape, sides not AC-equal,
		// non-equation goal) panic with their own diagnostics; recover
		// them into the RPC error channel — the agent reads the same
		// text an author would. A fault goes up (utils.Failure).
		var acErr error
		func() {
			defer func() {
				if r := utils.Failure(recover()); r != nil {
					acErr = fmt.Errorf("ac_regroup: %v", r)
				}
			}()
			ok = proof.ApplyACRegroup(clone, assocThm, symThm)
		}()
		if acErr != nil {
			return nil, acErr
		}
		if !ok {
			return nil, fmt.Errorf("ac_regroup did not apply")
		}
	case "def_expand":
		// Agent-facing dispatch routes through proof.ApplyDefExpand
		// (rewrite-only — no hypMatching fallback). See the comment on
		// DefAction.Apply in prover/proof/action.go for the agent-vs-search
		// split rationale.
		if tactic.Const == "" {
			return nil, fmt.Errorf("def_expand requires const")
		}
		c, err := e.lookupDefConst(tactic.Const)
		if err != nil {
			return nil, err
		}
		// A constant of the logic itself is opened by no proof: the
		// moves and the closers read it.
		if err := logicConstantUnfoldRefusal(c); err != nil {
			return nil, err
		}
		// An inductively defined relation's closure form is not a
		// proof surface: the refusal names its three theorems.
		if err := proof.InductiveUnfoldRefusal(c); err != nil {
			return nil, err
		}
		if tactic.HypIndex != nil {
			// The constant opened in ONE hypothesis, the unfolded
			// statement joining the hypotheses (hypothesis_moves.go).
			if err := e.applyUnfoldedHypOnClone(clone, c, *tactic.HypIndex); err != nil {
				return nil, err
			}
			ok = true
			break
		}
		ok = proof.ApplyDefExpand(clone, c)
	case "known":
		ok = s.applyKnownFallback(clone)
	case "case_split":
		// The BARE case split — what the chapter verb a.Cases records:
		// `φ ⊢ G` and `¬φ ⊢ G`, the second NOT pre-simplified (see
		// proof.ApplyByCase).
		caseTerm, err := e.resolveCaseTerm(tactic.Const, goal, s.familyScope())
		if err != nil {
			return nil, err
		}
		ok = proof.ApplyByCase(clone, caseTerm)
		if !ok {
			return nil, caseSplitNoProgressReason(goal, caseTerm, tactic.Const)
		}
	case "assert":
		// The claim arrives either pre-resolved (a programmatic caller
		// populating Claim directly) or as raw text-DSL
		// in ClaimText, which we parse here against the focused goal's scope
		// so a bare session free-var (n₀) resolves without an explicit
		// `n_0:num ⊢ …` type-declaration prefix.
		if tactic.Claim == nil && tactic.ClaimText != "" {
			claimP, perr := s.readStepText(tactic.ClaimText, goal, true)
			if perr != nil {
				return nil, fmt.Errorf("parse assert claim: %w", perr)
			}
			tactic.Claim = claimP
		}
		if tactic.Claim == nil {
			return nil, fmt.Errorf("assert tactic requires a 'claim' field with 'key' or 'text'")
		}
		if tactic.Claim.NumHyps() != 0 {
			return nil, fmt.Errorf(
				"assert claim must be hyp-free; got %d hyps (the asserted term is the conclusion)",
				tactic.Claim.NumHyps())
		}
		claimTerm := tactic.Claim.Conclusion()
		if !ext.IsBool(claimTerm) {
			return nil, fmt.Errorf(
				"assert claim must be boolean, got type %s",
				claimTerm.Type())
		}
		// Scope check: every free var of φ must already be in scope at the
		// current goal (i.e. appear free in concl or some hyp). Without
		// this, the agent could silently smuggle in a fresh free var via
		// the claim text; the resulting subgoals would be well-typed but
		// the new var would have no meaning relative to the surrounding
		// proof.
		for _, v := range claimTerm.Frees(nil) {
			if !goal.HasFreeName(v.Name()) {
				return nil, fmt.Errorf(
					"assert claim references unbound variable %q; "+
						"introduce it via strip_quant or declare it explicitly",
					string(v.Name()))
			}
		}
		ok = proof.ApplyAssert(clone, tactic.Claim)
		if !ok {
			return nil, fmt.Errorf(
				"assert: claim is already a hyp of the goal or matches the conclusion (the split would be a no-op)")
		}
	case "cite-node", "cite_node":
		// Both spellings: the tactic table is snake_case throughout and
		// this is its one hyphenated name, so the snake_case form is
		// accepted too (the CLI's alias table folds it the same way).
		// Session-internal lemma reuse: cite a proved node `target` whose
		// conclusion ψ we want as a hyp at the current focus, skipping the
		// re-search/re-expand path that `assert(ψ)` would otherwise force.
		// Materializes target's proof subtree into the assert's first
		// (claim) child — the stored proto is a regular assert with a
		// fully-proven first branch; no new step type / proto / replay path.
		if tactic.NodeID == "" {
			return nil, fmt.Errorf("cite-node requires 'node_id'")
		}
		target, _, found := s.lookupClosedNode(tactic.NodeID)
		if !found {
			// Cross-session graft: fall back to the engine-global
			// closed-derivation pool (see derivation_pool.go). A pool hit is
			// consumed through the exact same path as a local hit — the
			// hyp-subset soundness gate below and ApplyCiteNode's
			// materialize-into-assert both run unchanged, so the recorded
			// step structure (and hence replay) is identical to the
			// same-session case; the pool only changes WHERE the subtree
			// was found. Candidates are pre-filtered by the same gate here
			// solely to disambiguate 16-char key-prefix collisions: any
			// candidate passing the gate is a sound graft.
			candidates := s.derivPool.CandidatesForNodeID(tactic.NodeID)
			for _, cand := range candidates {
				if cand.Goal.AllHyp(goal.HasHyp) {
					target = cand
					found = true
					break
				}
			}
			if !found && len(candidates) > 0 {
				return nil, fmt.Errorf(
					"cite-node: node %q found in the cross-session derivation pool, but its hyp "+
						"context is not a subset of current focus's hyp context",
					tactic.NodeID)
			}
		}
		if !found {
			return nil, fmt.Errorf(
				"cite-node: closed node %q not found in session or in the cross-session "+
					"derivation pool — use `inspect` to enumerate available closed subtrees "+
					"in this session (the `closed_subtrees` field of the response)",
				tactic.NodeID)
		}
		// lookupClosedNode only returns Proved() nodes by construction, but
		// double-check defensively in case the walker's invariant ever
		// regresses (cheap; matches the assert-style validation pattern).
		if !target.Proved() {
			return nil, fmt.Errorf(
				"cite-node: node %q is not closed yet — cannot cite an unproved node",
				tactic.NodeID)
		}
		// Soundness gate: target's hyp context ⊆ current focus's hyp context.
		// AllHyp(HasHyp) checks every hyp of target is α-equiv to some hyp of
		// goal (the prover's existing hyp-subset primitive — see
		// ext/prop/utils.go IsStronger, which composes this same check with
		// a conclusion-equality check).
		if !target.Goal.AllHyp(goal.HasHyp) {
			return nil, fmt.Errorf(
				"cite-node: target's hyp context is not a subset of current focus's hyp context")
		}
		// term_specialize (optional): install cite-node's ∀-closed
		// conclusion already ground-instantiated at named witnesses,
		// reusing the exact machinery `lemma + term_specialize` uses
		// (resolveTermSpecializeWitnesses + applyLemmaTermSpecializeChain).
		// ApplyCiteNode installs target.Concl verbatim; the post-install
		// chain then peels its outer ∀-binders left-to-right — collapsing
		// what would otherwise be N separate `instantiate` round-trips
		// (each re-keying the goal + re-sorting hyp indices) into a single
		// call. The chain records as ordinary instantiate/clear ministeps,
		// so proto / emit / replay are unchanged — a term_specialize'd cite
		// serializes identically to a hand-written cite-node + instantiate×N
		// + clear (see engine/lemma_term_specialize.go).
		//
		// Witnesses resolve against the pre-cite focus scope; citeOrigHypKeys
		// snapshots that scope so the chain finds cite-node's newly-added
		// ∀-hyp on the residual (focus) leaf regardless of canonical hyp
		// reordering. The cited conclusion is assumed concrete (the Step-6.6
		// worker-cert case — its type vars are already pinned to the goal's);
		// a genuinely polymorphic cited node would need subtree-level type
		// instantiation, and surfaces here as the chain's defensive
		// binder/witness type-mismatch error rather than silent unsoundness.
		var citeTermSpecWitnesses []termSpecWitness
		var citeOrigHypKeys map[core.TermKey]struct{}
		var citePsi core.Prop
		if len(tactic.TermSpecialize) > 0 {
			citePsi = prop.MakeProp(target.Goal.Conclusion())
			ws, _, _, sErr := e.resolveTermSpecializeWitnesses(citePsi, tactic.TermSpecialize, goal, s.familyScope(), utils.EmptyPredicate[core.VarType])
			if sErr != nil {
				return nil, sErr
			}
			citeTermSpecWitnesses = ws
			citeOrigHypKeys = make(map[core.TermKey]struct{}, goal.NumHyps())
			for _, h := range goal.Hyps() {
				citeOrigHypKeys[h.AlphaKey()] = struct{}{}
			}
		}
		ok = proof.ApplyCiteNode(clone, target)
		if !ok {
			return nil, fmt.Errorf(
				"cite-node: target's conclusion is already a hyp of the goal or matches its conclusion (no-op)")
		}
		if len(citeTermSpecWitnesses) > 0 {
			if cerr := e.applyLemmaTermSpecializeChain(clone, citePsi, citeTermSpecWitnesses, citeOrigHypKeys); cerr != nil {
				return nil, cerr
			}
		}
	case "induction":
		// The BARE induction step — what the chapter verb a.Induct
		// records. The step case arrives as the principle states it
		// (`P(n) ⊢ P(suc n)`); a `≠` or `⇒` goal is NOT pre-shaped (no
		// contraposition, no antecedent moved into the hyps) — `by` takes
		// it as is, and an agent wanting the shaped form records it with
		// an explicit `simplify`, exactly as a Go author writes
		// `TrivialSimplify()`. See proof.ApplyInduction.
		inductVar, tmpl, err := e.resolveInduction(tactic.Const, goal)
		if err != nil {
			return nil, err
		}
		ok = proof.ApplyInduction(clone, inductVar, tmpl)
	case "witness":
		var expected core.HolType
		if abs := ext.MatchesEXISTS(goal.Conclusion()); !abs.IsZero() {
			expected = abs.Var().Type()
		} else if abs := ext.MatchesUNIQUE(goal.Conclusion()); !abs.IsZero() {
			expected = abs.Var().Type()
		}
		witness, err := e.resolveTermWithFallback(tactic.Const, goal, expected, s.familyScope())
		if err != nil {
			return nil, err
		}
		ok = proof.ApplyWitness(clone, witness)
	case "instantiate":
		// One unified path: every `instantiate` call grounds ONE ∀-hyp
		// (identified by hyp_index) at a witness list in ONE composite
		// `specialize` step.
		//   - Const + HypIndex    → hyp[index], 1 witness (source kept by
		//                           default; set `keep:false` to consume)
		//   - Terms + HypIndex    → hyp[index], N witnesses (multi-binder
		//                           peel; `keep` controls the source,
		//                           default consumed)
		// hyp_index is required — there is no "no-index, first-match"
		// sugar, so agents face ONE grounding action. Use `inspect` to
		// locate the target hyp's index. Records as `specialize` proto
		// tag.
		if len(tactic.Terms) > 0 && tactic.Const != "" {
			return nil, fmt.Errorf("instantiate: `terms` and `const` are mutually exclusive (use `terms` alone for the multi-witness form)")
		}
		if tactic.HypIndex == nil {
			return nil, fmt.Errorf("instantiate requires `hyp_index` (the 0-based index of the ∀-hyp to ground; use `inspect` to locate it)")
		}
		if tactic.Const == "" && len(tactic.Terms) == 0 {
			return nil, fmt.Errorf("instantiate requires `const` (single witness) or `terms` (multi-witness list)")
		}
		// Indexed form — always through ApplySpecialize. `Terms` is the
		// multi-witness list; a single `Const` is normalized to a
		// 1-element list. Binder types are pinned to the peeled ∀-chain
		// as the parser's expected type per rung.
		idx := *tactic.HypIndex
		if idx < 0 || idx >= goal.NumHyps() {
			return nil, fmt.Errorf("instantiate hyp_index %d out of range [0, %d)", idx, goal.NumHyps())
		}
		cur := goal.Hyp(idx)
		if nextStatedBinder(cur).IsZero() {
			return nil, fmt.Errorf("instantiate hyp_index %d (%s) is not ∀-headed and binds no ∀ behind an antecedent", idx, ext.PrintTerm(cur))
		}
		spellings := tactic.Terms
		singleConst := len(spellings) == 0
		if singleConst {
			spellings = []string{tactic.Const}
		}
		// Witness resolution with type adaptation: when a witness's type
		// doesn't equal its ∀-binder's but the binder type MATCHES it
		// under a substitution of the hyp's type vars (or the agent
		// passed an explicit `type_specialize`), `adapt` carries the
		// σ-specialized hyp
		// statement and the apply routes through the registry-backed
		// re-derivation chain. See engine/instantiate_type_adapt.go for
		// the mechanism and the soundness shape (there is no per-hyp
		// kernel type instantiation — the σ-instance is re-derived from
		// the hyp's backing registry entry).
		witnesses, adapt, werr := e.resolveInstantiateWitnesses(
			goal, cur, spellings, singleConst, tactic.TypeSpecialize, s.familyScope())
		if werr != nil {
			return nil, werr
		}
		// A single-witness + hyp_index instantiate keeps the source ∀ by
		// default (`Keep` governs `Terms`), so agent code that never sets
		// `keep` sees source-kept behavior.
		keep := tactic.Keep || singleConst
		if adapt != nil {
			if aerr := e.applyInstantiateTypeAdapted(s, clone, idx, cur, adapt, witnesses, keep); aerr != nil {
				return nil, aerr
			}
			ok = true
		} else {
			ok = proof.ApplySpecialize(clone,
				[]proof.SpecializeHyp{proof.InstHyp(idx, witnesses...)}, keep)
			if !ok {
				return nil, fmt.Errorf(
					"instantiate on hyp %d had no effect (the ground instance is already in scope)", idx)
			}
		}
	case "ematch":
		// E-matching ground pre-instantiation of resident ∀-hyps (see
		// ematch.go). Applies a bounded, deterministic chain of standard
		// instantiate steps; recorded exactly like agent-driven
		// instantiate moves, so replay needs nothing new.
		applied := applyEMatchGround(clone)
		if applied == 0 {
			return nil, fmt.Errorf("ematch found no NEW ground instantiations: no ∀-hyp trigger matches a ground goal subterm, or every match is already instantiated (load the relevant lemmas as hyps first, or the goal has no matching sites)")
		}
		ok = true
	case "subst":
		// Hyp-index dispatch: validate range + equality shape so the
		// agent gets a clear failure rather than a generic "did not
		// apply" when the index is wrong. The CLI layer guarantees
		// HypIndex is non-nil here (see tacticReqFromInput).
		if tactic.HypIndex == nil {
			return nil, fmt.Errorf("subst requires hyp_index")
		}
		idx := *tactic.HypIndex
		if idx < 0 || idx >= goal.NumHyps() {
			return nil, fmt.Errorf("subst hyp_index %d out of range [0, %d)", idx, goal.NumHyps())
		}
		hyp := goal.Hyp(idx)
		if _, _, isEq := ext.MatchesEQ(hyp); !isEq {
			return nil, fmt.Errorf("subst hyp_index %d (%s) is not an equality", idx, ext.PrintTerm(hyp))
		}
		ok = proof.ApplySubst(clone, idx)
		if !ok {
			return nil, substSizeGuardError{hypIndex: idx}
		}
	case "rw":
		// Directed rewrite-to-fixpoint with the equality hyp at idx:
		// rewrites the oriented LHS to the oriented RHS across the
		// conclusion and all other hyps (flip reverses the orientation).
		// Validate range + equality shape here so the agent gets a
		// precise failure instead of a generic "did not apply".
		if tactic.HypIndex == nil {
			return nil, fmt.Errorf("rw requires hyp_index (the equality hyp to rewrite with)")
		}
		idx := *tactic.HypIndex
		if idx < 0 || idx >= goal.NumHyps() {
			return nil, fmt.Errorf("rw hyp_index %d out of range [0, %d)", idx, goal.NumHyps())
		}
		hyp := goal.Hyp(idx)
		if _, _, isEq := ext.MatchesEQ(hyp); !isEq {
			return nil, fmt.Errorf("rw hyp_index %d (%s) is not an equality (a ∀-quantified equation must be instantiated to ground form first)", idx, ext.PrintTerm(hyp))
		}
		ok = proof.ApplyRw(ctx, clone, idx, tactic.Flip)
		if !ok {
			dir := "left-to-right"
			if tactic.Flip {
				dir = "right-to-left (flip)"
			}
			return nil, fmt.Errorf("rw on hyp %d had no effect: no %s occurrence of the rewrite side found in the conclusion or other hyps (a self-expanding equality — LHS occurring in RHS — is also refused)", idx, dir)
		}
	case "clear":
		// Drop one or more hypotheses from the goal.
		// Primary use: remove wide multi-quantifier ∀-lemmas before
		// `refute`/`auto` so the CNF refuter doesn't burn its ~5s ceiling
		// resolving an irrelevant bundle (refute-poisoning). Always sound — proving the goal under fewer
		// assumptions is stronger — so the only failures are bad indices.
		//
		// Single agent-facing form: `hyp_indices` is a SET of indices into
		// the goal's hyp list AS THE AGENT SEES IT (a single drop is just
		// `[i]`). All clears route through ApplyClearHyps and record ONE
		// `clear_hyps` ministep, so a recorded proof carries exactly one
		// clear shape.
		if len(tactic.HypIndices) == 0 {
			return nil, fmt.Errorf("clear requires hyp_indices (0-based hyp index/indices to drop; a single drop is [i])")
		}
		seen := make(map[int]bool, len(tactic.HypIndices))
		for _, idx := range tactic.HypIndices {
			if idx < 0 || idx >= goal.NumHyps() {
				return nil, fmt.Errorf("clear hyp_indices entry %d out of range [0, %d)", idx, goal.NumHyps())
			}
			if seen[idx] {
				return nil, fmt.Errorf("clear hyp_indices contains duplicate index %d", idx)
			}
			seen[idx] = true
		}
		ok = proof.ApplyClearHyps(clone, tactic.HypIndices)
		if !ok {
			return nil, fmt.Errorf("clear on hyps %v had no effect", tactic.HypIndices)
		}
	case "congr_arg":
		// Forward congruence on an equality hyp: hyp (a=b)@idx + a
		// function term f → adds hyp f(a)=f(b). Validate index + equality
		// shape + that f is a function whose domain matches the hyp's
		// side type, so the agent gets a precise error instead of a
		// generic "did not apply". (Lean congrArg.)
		if tactic.HypIndex == nil {
			return nil, fmt.Errorf("congr_arg requires hyp_index (the equality hyp to apply the function to)")
		}
		idx := *tactic.HypIndex
		if idx < 0 || idx >= goal.NumHyps() {
			return nil, fmt.Errorf("congr_arg hyp_index %d out of range [0, %d)", idx, goal.NumHyps())
		}
		hyp := goal.Hyp(idx)
		lhs, _, isEq := ext.MatchesEQ(hyp)
		if !isEq {
			return nil, fmt.Errorf("congr_arg hyp_index %d (%s) is not an equality", idx, ext.PrintTerm(hyp))
		}
		fn, err := e.resolveTermWithFallback(tactic.Const, goal, nil, s.familyScope())
		if err != nil {
			return nil, err
		}
		if !ext.IsFunType(fn.Type()) {
			return nil, fmt.Errorf("congr_arg function %s is not a function (type %s)", ext.PrintTerm(fn), fn.Type())
		}
		if dom := ext.MatchesFun(fn.Type())[0]; !dom.Equals(lhs.Type()) {
			return nil, fmt.Errorf("congr_arg function domain %s does not match equality side type %s", dom, lhs.Type())
		}
		ok = proof.ApplyCongrArg(clone, fn, idx)
		if !ok {
			return nil, fmt.Errorf("congr_arg on hyp %d had no effect (f(a)=f(b) already in scope)", idx)
		}
	case "congr_fun":
		// Dual of congr_arg: function-equality hyp (f=g)@idx + an argument
		// term x → adds hyp f(x)=g(x). (Lean congrFun.)
		if tactic.HypIndex == nil {
			return nil, fmt.Errorf("congr_fun requires hyp_index (the function-equality hyp to apply the argument to)")
		}
		idx := *tactic.HypIndex
		if idx < 0 || idx >= goal.NumHyps() {
			return nil, fmt.Errorf("congr_fun hyp_index %d out of range [0, %d)", idx, goal.NumHyps())
		}
		hyp := goal.Hyp(idx)
		lhs, _, isEq := ext.MatchesEQ(hyp)
		if !isEq {
			return nil, fmt.Errorf("congr_fun hyp_index %d (%s) is not an equality", idx, ext.PrintTerm(hyp))
		}
		if !ext.IsFunType(lhs.Type()) {
			return nil, fmt.Errorf("congr_fun hyp_index %d (%s): equated sides are not functions", idx, ext.PrintTerm(hyp))
		}
		expected := ext.MatchesFun(lhs.Type())[0]
		arg, err := e.resolveTermWithFallback(tactic.Const, goal, expected, s.familyScope())
		if err != nil {
			return nil, err
		}
		if !expected.Equals(arg.Type()) {
			return nil, fmt.Errorf("congr_fun argument type %s does not match function domain %s", arg.Type(), expected)
		}
		ok = proof.ApplyCongrFun(clone, arg, idx)
		if !ok {
			return nil, fmt.Errorf("congr_fun on hyp %d had no effect (f(x)=g(x) already in scope)", idx)
		}
	case "trans":
		// Expected middle type = type of the equality's sides, when the
		// goal is `a = c`. Lets the parser type-check a novel middle
		// term like `m * suc(n+p)` whose free vars are constrained
		// only by the surrounding equality, not by any operator in the
		// middle expression itself.
		var expected core.HolType
		if lhs, _, isEq := ext.MatchesEQ(goal.Conclusion()); isEq {
			expected = lhs.Type()
		}
		middle, err := e.resolveTermWithFallback(tactic.Const, goal, expected, s.familyScope())
		if err != nil {
			return nil, err
		}
		ok = proof.ApplyTrans(clone, middle)
	case "by_contra":
		// Per Decision 5: dispatched here, NOT in structuralTacticSpecs
		// (its shape predicate fires on every non-⊥ goal — too noisy
		// for inspect's structural_facts).
		if goal.Conclusion().Equals(ext.F) {
			return nil, fmt.Errorf("by_contra does not apply: conclusion is already ⊥")
		}
		ok = proof.ApplyByContra(clone)
	case "intro":
		// Smart dispatcher: ⇒ → strip_imp, ∀ → strip_quant.
		// Per Decision 2: dispatch here, not as a CLI alias, because
		// LEAN-style math goals lead with ∀ at least as often as with ⇒,
		// and we want one tactic name to cover the common-case
		// "introduce one outer thing".
		if proof.ApplyStripImp(clone) {
			ok = true
			break
		}
		// strip_imp may have mutated the clone partially before failing —
		// remake a fresh one.
		clone = proof.CreateGoalStack(goal)
		if proof.ApplyStripQuant(clone) {
			ok = true
			break
		}
		return nil, fmt.Errorf("intro: conclusion is neither A ⇒ B nor ∀x. P; use a different tactic")
	case "lean_rw":
		// LEAN-style `rw`: explicit equational rewrite. Resolves the
		// lemma the same way `lemma` does, gates on the lemma's
		// post-strip-∀ conclusion being an equality / iff, then
		// dispatches to ApplyLeanRw (rewrite-only path, size-decrease
		// guard bypassed, no fallback to conclusion or hypothesis matching).
		// Distinct from `lemma`: agents picking `lean_rw` want a
		// directional rewrite — when the rewrite path doesn't match,
		// they get clean failure rather than the lemma silently being
		// added as a hyp.
		lemmaProp, lerr := e.resolveLemma(s, tactic, goal)
		if lerr != nil {
			return nil, lerr
		}
		if lemmaProp == nil {
			return nil, fmt.Errorf("lean_rw requires lemma_key or lemma field")
		}
		// Agent-supplied pre-rewrite specializations — same recipe as
		// `lemma`'s branch above (TYPE first, then TERM). The pre-σ
		// source key is captured BEFORE either substitution replaces
		// lemmaProp, so the recorded source still points at the
		// polymorphic entry even after the equality check on the
		// post-σ form.
		var leanRwLemmaSourceKey core.PropKey
		if tactic.LemmaKey != "" {
			leanRwLemmaSourceKey = core.PropKey(tactic.LemmaKey)
		}
		var fixed core.VarTypePredicate = utils.EmptyPredicate[core.VarType]
		if len(tactic.TypeSpecialize) > 0 {
			specialized, goalLetters, sErr := buildSpecializedLemma(lemmaProp, tactic.TypeSpecialize, goal)
			if sErr != nil {
				return nil, sErr
			}
			if leanRwLemmaSourceKey == "" {
				leanRwLemmaSourceKey = proof.LemmaSourceKey(lemmaProp)
			}
			lemmaProp, fixed = specialized, goalLetters
		}
		if len(tactic.TermSpecialize) > 0 {
			specialized, sErr := e.buildTermSpecializedLemma(lemmaProp, tactic.TermSpecialize, goal, s.familyScope(), fixed)
			if sErr != nil {
				return nil, sErr
			}
			if leanRwLemmaSourceKey == "" {
				leanRwLemmaSourceKey = proof.LemmaSourceKey(lemmaProp)
			}
			lemmaProp = specialized
		}
		if !lemmaConclIsEquality(lemmaProp) {
			return nil, fmt.Errorf("lean_rw expects an equality lemma; got: %s", prop.PrintProp(lemmaProp))
		}
		// Explicit-σ fork: same skip-adapt rationale as `lemma`'s branch
		// above — the agent's explicit type-σ (term_specialize's induced
		// σ_type OR an explicit type_specialize map) must not be
		// overridden by the install path's tryAdaptLemmaTypes. Honored
		// exactly or clean failure.
		if len(tactic.TermSpecialize) > 0 || len(tactic.TypeSpecialize) > 0 {
			ok = proof.ApplyLeanRwExactWithSource(clone, lemmaProp, leanRwLemmaSourceKey)
		} else {
			ok = proof.ApplyLeanRwWithSource(clone, lemmaProp, leanRwLemmaSourceKey)
		}
		if !ok {
			ok = e.tryCloseAsTypeVariantOfEntry(s, clone, tactic)
		}
	case "auto":
		// Try the unified arith composite as a cheap fast-path, gated on
		// the SAME shape predicate the explicit `arith` tactic enforces
		// (goalHasArithContent). The gate is load-bearing for dep
		// recording, not just economy: _Arith's rewriter runs the generic
		// logic rewrites (β / hilbert / quantifier eta-expansion / …) in
		// the same fixpoint as the arith leaves, so on an arith-free goal
		// it can still "make progress" and record a StepProto_Arith —
		// an arith capability use (the ENTIRE bundle's foundation as the
		// member's capability edges) for a goal that needed none. Gate-false
		// goals lose nothing: the generic collapses are a subset of
		// AutoExpand's own basic-rewrite pass. Live-dispatch-only — a
		// recorded Arith step replays through the prover step driver
		// directly, so recorded proofs are untouched.
		//
		// The composite (ApplyArithSimplify) is SIMPLIFY-OR-CLOSE: a
		// fully-decidable goal closes via _Arith's deep rewrite to `⊢ ⊤`
		// collapsed by _TrivialSimplify; a partial decision
		// (`(a<a+1)∧Q → ⊤∧Q → Q`) advances the conclusion and AutoExpand
		// picks up the simpler residual. Every rewrite the composite makes
		// is an equivalence, but logical equivalence alone does NOT keep
		// AutoExpand's reach — its CNF stage is syntactic, and an arith
		// rewrite can consume exactly the syntax it needs (normalizing
		// `m*x ≠ 0*x` to `m*x ≠ 0` strands a refl-closable refutation;
		// dropping a ring-true hyp `0*x = 0` removes a paramodulation
		// bridge the refuter cannot re-derive). The no-hurt contract is
		// therefore enforced structurally inside the arith tactic: residuals
		// carry the consumed value-level equations as extra hyps
		// (emitArithBridges) and arith-redundant non-trivial hyps are
		// retained rather than dropped (the RETENTION rule) — see
		// prover/tactic/arith_tactics.go.
		// Crucially this stays at the engine dispatch layer — a member's
		// replay goes through CloseByAuto → env.AutoExpand().Apply
		// directly, never via this path, so the engine-side arith
		// integration cannot re-force a bundle promise mid-Build (no
		// deadlock).
		if goalHasArithContent(clone.Goal) {
			proof.ApplyArithSimplify(ctx, clone)
		}
		if clone.Proved() {
			ok = true
		} else {
			autoAction := s.env.AutoExpandWithCtx(ctx)
			ok = autoAction.Apply(clone)
		}
	case "auto_with":
		// Scoped lemma + focused auto in one atomic close-or-fail call.
		// Orchestrates (clear → lemma install ×N → arith → autoexpand)
		// on the clone via existing kernel paths; if the clone doesn't
		// .Proved() at the end, return an error so runTacticOnClone's
		// caller discards the clone — the session never absorbs the
		// scoped state without a close. See engine/auto_with.go.
		if err := e.applyAutoWithOnClone(ctx, s, clone, tactic); err != nil {
			return nil, err
		}
		ok = true
	case "by":
		// The math layer's premise-disciplined close as a session move —
		// auto_with's DECLARED sibling: THESE premises (by_hyps kept +
		// with_lemmas installed, ground where witnessed), the declared
		// by_shape, ONE refutation (or the gated arith closer with
		// {"arith":true}) — recorded as ONE `by` ministep
		// (StepProto_By), which is exactly the `By(...)` the Go
		// spells and replays. Close-or-fail; the closer never takes the
		// arith fast-path silently. See engine/by_tactic.go.
		if err := e.applyByOnClone(ctx, s, clone, tactic); err != nil {
			return nil, err
		}
		ok = true
	case "elementarity":
		// The elementarity step as a session move — Go's ByElementarity:
		// the goal read as a first-order formula, its bridge proved from
		// the reifier's plan, the formula carried over by elementary
		// equivalence from the source or along an elementary embedding —
		// recorded as ONE `elementarity` ministep (StepProto_Elementarity).
		// Close-or-fail. See engine/elementarity_tactic.go.
		if err := e.applyElementarityOnClone(ctx, s, clone, tactic); err != nil {
			return nil, err
		}
		ok = true
	case "by_induction":
		// Go's ByInduction as a session move: the principle's obligations
		// asserted one each and left open as the cases, the terminal By
		// closing the goal from them and the principle in its stated form.
		// Recorded as the asserts and the by the verb records. See
		// engine/by_induction.go.
		if err := e.applyByInductionOnClone(ctx, s, clone, tactic); err != nil {
			return nil, err
		}
		ok = true
	case "set_tac":
		// The set closer, recorded as ONE first-class
		// ministep (StepProto_SetTac): deterministic fixpoint unfold of
		// the default set vocabulary (set_member, set_comprehension, comprehension_spec, union, intersection,
		// insert, big_union, big_intersection, …) across goal AND hyps, then a bare
		// CNF refute on every residual leaf. Close-or-fail. The recorded
		// proto carries the const list, and replay re-runs the SAME
		// driver (tactic.SetTacExpand + _CNFRefute inside
		// _SetTacStep.apply) — see prover/proof/step_composite.go for the
		// record/emit/replay-reuse rationale.
		//
		// The set door (proof.ApplySetTac) is the Go `SetTac()`: the
		// modes in proof.SetTacOrder — MEMBERSHIP, then LEGACY full
		// expansion — tried in turn, and the mode that closes is what
		// gets RECORDED (the proto carries mode + consts), so replay
		// re-runs exactly that driver; both attempts are close-or-fail,
		// so the order hides nothing.
		//
		// The residual sink is the first mode's (the more legible
		// residual — first-order operators, not λ-soup): on failure the
		// agent sees WHICH leaves the refuter could not close (capped).
		// Replay and the emit-time collector pass a nil sink — the sink
		// is runtime-only and never serialized.
		var setTacResiduals []core.Prop
		ok = proof.ApplySetTac(clone, s.env, ctx, proof.DefaultSetTacConsts(), &setTacResiduals)
		if !ok {
			var b strings.Builder
			if ctx.Err() != nil {
				b.WriteString("set_tac ran out of budget (budget_ms) before closing; ")
			}
			if len(setTacResiduals) == 0 {
				b.WriteString("set_tac did not apply: the closing CNF refute failed on the goal")
			} else {
				fmt.Fprintf(&b, "set_tac did not apply (membership then legacy mode): membership-mode residual leaves that failed to refute (first %d shown):",
					len(setTacResiduals))
				for i, r := range setTacResiduals {
					fmt.Fprintf(&b, "\n  [%d] %s", i, prop.PrintProp(r))
				}
			}
			// set_tac unfolds the set vocabulary and then refutes each
			// residual BARE: no strip, no Basic, no premise list. A leaf
			// that fails here and closes under a conditioned closer is a
			// statement about its shape, not about the mathematics.
			b.WriteString("\nset_tac hands its residual leaves to the refuter as they stand — no simplification before, " +
				"no premise list. If `by {settac:true}` (the premises named, the leaf conditioned first) or `auto` " +
				"closes this goal, it wanted that conditioning, not a different lemma.")
			return nil, fmt.Errorf("%s", b.String())
		}
	case "simp_with":
		// The simplifier, recorded as ONE first-class
		// ministep (StepProto_SimpWith): joint-fixpoint rewrite of the
		// goal's conclusion with the ordered rule set — unconditional
		// equations, ⇔⊤-oriented facts, and conditional (Horn/clause-form)
		// rules whose side conditions discharge against goal hyps, fact
		// rules in the set, or the set's own unconditional rewrites.
		// Rules are resolved HERE (key/text + type/term-specialize +
		// polymorphic type adaptation — a polymorphic rule without an
		// explicit σ expands to one copy per distinct goal type-instance,
		// deduplicated; see resolveSimpWithRules) and recorded verbatim in the
		// proto; replay re-runs the same driver (tactic.SimpWithExpand) on
		// the recorded forms — see prover/proof/step_composite.go for the
		// record/emit/replay-reuse rationale. Progress-or-fail; the USED
		// rule children close via the post-step auto-match pass, recording
		// registry deps exactly like `lemma`'s claim child.
		if len(tactic.WithLemmas) == 0 {
			return nil, fmt.Errorf("simp_with requires a non-empty with_lemmas list")
		}
		if err := hypIndexInRange("simp_with", goal, tactic.HypIndex); err != nil {
			return nil, err
		}
		if tactic.HypIndex != nil {
			for _, i := range residentRuleIndices(tactic.WithLemmas) {
				if i == *tactic.HypIndex {
					return nil, fmt.Errorf("simp_with: hyp_index %d is both the rewritten hypothesis and a rule — a fact does not rewrite itself", i)
				}
			}
		}
		rs, rerr := e.resolveSimpWithRules(s, goal, tactic.WithLemmas)
		if rerr != nil {
			return nil, rerr
		}
		// The named rules are the whole set, as they are for the Go
		// Simp(Fwd(…), Rev(…)) the step renders to: the session's
		// installed simp set fires under `simp` and `simp_all`, never
		// here. The instances the rewrite itself exposes are adapted to
		// before the one recorded run (simp_with_multi_instance.go).
		expandErr := rs.expandToFixpoint(goal, tactic.HypIndex)
		if s != nil {
			// Surface the expansion/dedup diagnostics at the RPC boundary
			// (drained by ApplyStep) whether or not the driver fires, and
			// when the adaptation itself refuses: on failure the agent
			// must still see what the rule set actually contained.
			s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, rs.diags...)
		}
		if expandErr != nil {
			return nil, expandErr
		}
		// `hyp_index` addresses a hypothesis (Lean's `simp at h`): it is
		// rewritten in its place, the rules' side conditions discharged
		// against the other hypotheses, the conclusion untouched.
		ok = rs.apply(clone, tactic.HypIndex)
		if !ok {
			if cut := rs.cut(goal, simpTarget(goal, tactic.HypIndex)); cut != "" {
				return nil, fmt.Errorf("simp_with: the rule set was cut as divergent on the selected target, "+
					"and the session is unchanged. %s%s", cut, rs.refusal(goal, simpTarget(goal, tactic.HypIndex)))
			}
			return nil, fmt.Errorf("%s%s", tacticNoProgressDiagnostic("simp_with"),
				rs.refusal(goal, simpTarget(goal, tactic.HypIndex)))
		}
		// Close the rule children — a PROVED sibling's statement, an
		// installed definition's own certificate, the type-instance
		// pass per source for an adapted or specialized copy (deps
		// record through the resulting steps, the channel `lemma`'s
		// claim child uses). The matched list is surfaced through
		// StepResult.AutoMatched (via the pending buffer) so the
		// agent sees exactly which rule instances fired.
		matched := s.closeSimpRuleChildren([]*proof.GoalStackNode{clone}, rs)
		if err := rs.openTextRule("simp_with", goal, []*proof.GoalStackNode{clone}, tactic.WithLemmas); err != nil {
			return nil, err
		}
		s.pendingAutoMatched = append(s.pendingAutoMatched, matched...)
	case "rewrite":
		ok = proof.ApplyRewrite(clone)
	case "simp":
		// The R4 simp verb:
		// rewrite with the session's INSTALLED simp set — the `define`
		// move registers each definition's characterizing theorem (a
		// conjunction is a valid simp_with rule; transcript A4's
		// zero-setup base case). With nothing installed it behaves as
		// `simplify`, the fallback that makes the verb total.
		if err := hypIndexInRange("simp", goal, tactic.HypIndex); err != nil {
			return nil, err
		}
		if s == nil || len(s.simpRules) == 0 {
			ok = proof.ApplyTrivial(clone)
			break
		}
		// The installed set, each polymorphic rule adapted to the
		// goal's type instances and to the ones the rewrite exposes —
		// an imported definition at the chapter's letters fires at the
		// goal's instance (simp_with_multi_instance.go). `hyp_index`
		// addresses a hypothesis instead of the conclusion.
		rs := newSimpRuleSet()
		rs.addInstalled(s)
		expandErr := rs.expandToFixpoint(goal, tactic.HypIndex)
		s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, rs.diags...)
		if expandErr != nil {
			return nil, expandErr
		}
		ok = rs.apply(clone, tactic.HypIndex)
		if !ok {
			if cut := rs.cut(goal, simpTarget(goal, tactic.HypIndex)); cut != "" {
				return nil, fmt.Errorf("simp: the installed rules were cut as divergent on the goal's target "+
					"(%d installed rule(s)), and the session is unchanged. %s%s",
					len(s.simpRules), cut, rs.refusal(goal, simpTarget(goal, tactic.HypIndex)))
			}
			return nil, fmt.Errorf(
				"simp: no installed rule fired on the goal's target (%d installed "+
					"rule(s): the bound families' definitions and the theorems their "+
					"chapters marked Simp; progress-or-fail, the session is unchanged). "+
					"simp_with with an explicit rule list is the general form; hyp_index "+
					"addresses a hypothesis%s", len(s.simpRules), rs.refusal(goal, simpTarget(goal, tactic.HypIndex)))
		}
		// Close the surfaced rule children from the installing
		// definitions' own certs (the define section's promise, an
		// import's replay promise) — α-match for a rule at its own
		// letters, the type-instance pass for an adapted copy; the certs
		// sit in a scratch cache, never the session autoMatchCache:
		// define facts are session-authored, not registry entries, and
		// must not enter the dep-bounded pool.
		matched := s.closeSimpRuleChildren([]*proof.GoalStackNode{clone}, rs)
		s.pendingAutoMatched = append(s.pendingAutoMatched, matched...)
	case "simp_all":
		// Lean's `simp_all` without the hypotheses as rules of each other:
		// the installed simp set (the bound families' definitions and the
		// theorems their chapters marked Simp), plus any `with_lemmas`,
		// rewrites the conclusion and every hypothesis in place, one
		// target per round to a fixpoint across the targets. Progress-or-
		// fail. Each round records one simp_with ministep, so emit renders
		// the rounds as the Simp / fact.Simp steps they are. The rule set
		// is the named rules first and the installed set behind them,
		// each polymorphic rule adapted to the goal's instances.
		rs := newSimpRuleSet()
		if len(residentRuleIndices(tactic.WithLemmas)) > 0 {
			return nil, fmt.Errorf("simp_all: a hyp_index rule is a resident hypothesis, and simp_all rewrites every " +
				"hypothesis, that one among them — rewrite the conclusion or one other hypothesis by it with simp_with")
		}
		if len(tactic.WithLemmas) > 0 {
			named, rerr := e.resolveSimpWithRules(s, goal, tactic.WithLemmas)
			if rerr != nil {
				return nil, rerr
			}
			rs = named
		}
		rs.addInstalled(s)
		if len(rs.rules) == 0 {
			return nil, fmt.Errorf("simp_all: nothing installed and no with_lemmas — bind the session to a family, define, or name rules")
		}
		leaf := clone
		fired := false
		// The adaptation diagnostics reach the agent whether the call
		// applies or refuses (as the simp_with case surfaces them).
		surface := func() {
			if s != nil {
				s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, rs.diags...)
			}
		}
		for round := 0; round < 8*(goal.NumHyps()+1); round++ {
			progressed := false
			if err := rs.expandToFixpoint(leaf.Goal, nil); err != nil {
				surface()
				return nil, err
			}
			if rs.apply(leaf, nil) {
				progressed, fired = true, true
			} else {
				for i := 0; i < leaf.Goal.NumHyps(); i++ {
					if err := rs.expandToFixpoint(leaf.Goal, &i); err != nil {
						surface()
						return nil, err
					}
					if rs.apply(leaf, &i) {
						progressed, fired = true, true
						break
					}
				}
			}
			if !progressed {
				break
			}
			// The used rules' children close through the channels below
			// once the loop ends; the residual is the leaf the next round
			// reads — the last unsolved leaf, the rule children before it.
			open := leaf.UnsolvedLeaves()
			if len(open) == 0 {
				break
			}
			leaf = open[len(open)-1]
		}
		surface()
		ok = fired
		if !ok {
			targets := append(goal.Hyps(), goal.Conclusion())
			if cut := rs.cut(goal, targets...); cut != "" {
				return nil, fmt.Errorf("simp_all: the rule set was cut as divergent on the conclusion or a hypothesis, "+
					"and nothing was rewritten (%d rule(s); the session is unchanged). %s%s",
					len(rs.rules), cut, rs.refusal(goal, targets...))
			}
			return nil, fmt.Errorf("simp_all: no rule fired on the conclusion or any hypothesis (%d rule(s); progress-or-fail, the session is unchanged)%s",
				len(rs.rules), rs.refusal(goal, targets...))
		}
		// Close the rule children: installed rules from their certs,
		// named rules through the auto-match passes, adapted copies
		// through the type-instance pass — the one close simp and
		// simp_with share.
		if s != nil {
			matched := s.closeSimpRuleChildren([]*proof.GoalStackNode{clone}, rs)
			if err := rs.openTextRule("simp_all", goal, []*proof.GoalStackNode{clone}, tactic.WithLemmas); err != nil {
				return nil, err
			}
			s.pendingAutoMatched = append(s.pendingAutoMatched, matched...)
		}
	case "simplify":
		ok = proof.ApplyTrivial(clone)
	case "basic":
		// The chapter verb `Basic()` under its own name: what a rewrite
		// ladder ends on when its result is ⊤ or reflexive.
		ok = proof.ApplyBasic(clone)
	case "denote":
		// Two forms. Bare `denote` is the SEARCH stage: the heuristic
		// picks the subterm (size threshold, then ε) and mints α₀ — the
		// same stage auto / expand run. With `const`, it is the EXPLICIT
		// abbreviation "let <name> = <const>": the agent says WHAT is
		// being named, `name` says what to call it (default α₀), and the
		// step records that choice so replay reproduces the decision
		// instead of re-running the heuristic against a drifted goal. A
		// term the goal does not contain is an error HERE, not a cache
		// miss two hundred steps downstream.
		if tactic.Const != "" {
			term, err := e.resolveTermWithFallback(tactic.Const, goal, nil, s.familyScope())
			if err != nil {
				return nil, err
			}
			hilbert := ext.HilbertSubTerm(term) != nil &&
				ext.HilbertSubTerm(term).Equals(term)
			// The name arrives as wire text and goes on to BE a kernel
			// variable name, so it takes the same identifier
			// normalization every term text takes: the printer renders
			// `x_0` as `x₀`, and a name pasted back from the goal must
			// denote the same variable it looks like — otherwise the
			// collision check below silently passes and the goal grows
			// two distinct variables that print identically.
			name, _ := dsl.NormalizeTextSymbols(tactic.Name)
			if applyErr := func() (applyErr error) {
				defer func() {
					if r := utils.Failure(recover()); r != nil {
						applyErr = fmt.Errorf("denote: %v", r)
					}
				}()
				ok = proof.ApplyDenoteTerm(clone, name, term, hilbert)
				return nil
			}(); applyErr != nil {
				return nil, applyErr
			}
			if !ok {
				return nil, fmt.Errorf("denote did not apply: %s is already denoted by a variable in the goal",
					ext.PrintTerm(term))
			}
		} else {
			if tactic.Name != "" {
				return nil, fmt.Errorf("denote: `name` requires `const` (the term to name) — " +
					"the bare search form mints its own variable")
			}
			ok = proof.ApplyDenote(clone)
		}
	case "let":
		// The definition move — "let <name> := <const>", the Go
		// `a.Let(name, term)`: the equation `name = term` joins the
		// hypotheses, occurrences of the term become the name, and the
		// goal keeps its form. Where `denote` abbreviates a term the goal
		// already carries and moves to ⊥-form, `let` names an object the
		// argument is about to reason ABOUT — a supremum's set, a fold's
		// summand — whether or not the goal mentions it yet, so that
		// later claims and premise lists spell the name.
		if tactic.Name == "" || tactic.Const == "" {
			return nil, fmt.Errorf("let requires `name` (what the object is called) and `const` (the term it is defined as)")
		}
		term, err := e.resolveTermWithFallback(tactic.Const, goal, nil, s.familyScope())
		if err != nil {
			return nil, err
		}
		// The name goes on to BE a kernel variable name, so it takes the
		// identifier normalization every term text takes (as `denote`'s
		// does): `x_0` and the `x₀` the goal prints are one variable.
		name, _ := dsl.NormalizeTextSymbols(tactic.Name)
		if applyErr := func() (applyErr error) {
			defer func() {
				if r := utils.Failure(recover()); r != nil {
					applyErr = fmt.Errorf("let: %v", r)
				}
			}()
			ok = proof.ApplyLetTerm(clone, name, term)
			return nil
		}(); applyErr != nil {
			return nil, applyErr
		}
	case "split_disj", "split_hyp_iff", "split_hyp_imply", "strip_quant", "split_conj":
		// Optional hyp_index: when set, target that specific hyp instead
		// of the first matching one. Absent → the default pick-first path
		// via the structural spec table (back-compat with pre-payload
		// records and every existing call site that omitted the field).
		// split_conj with a hyp_index splits THAT conjunctive hypothesis
		// into its flat conjuncts as the Go verb a.Conjuncts does, the
		// conjunction kept (hypothesis_moves.go), and without one splits
		// the conclusion's conjunction as the table says.
		//
		// The recurring "split_disj ignored my hyp_index" navigation
		// defeat this arm exists to fix: several ∨-hyps in the context
		// and the agent asks for hyp 15 specifically because 13 is
		// unrelated to the current branch. strip_quant has the same
		// defeat one level up: its pick-first form strips a ∀-headed
		// conclusion before it looks at any hyp, and then opens the
		// first ∃-hyp it scans to; a named index opens THAT ∃-hyp and
		// leaves the conclusion alone — the session twin of a.Unpack.
		if tactic.HypIndex != nil {
			idx := *tactic.HypIndex
			if idx < 0 || idx >= goal.NumHyps() {
				return nil, fmt.Errorf("%s hyp_index %d out of range [0, %d)", tactic.Type, idx, goal.NumHyps())
			}
			hyp := goal.Hyp(idx)
			// A membership in a set-builder that is not the shape as
			// written is opened through its predicate's reading, as the
			// moves and the Go verbs open it (hypothesisOpens).
			var (
				shapeName string
				shapeOk   bool
			)
			shaped := func(match func(core.Term) bool) bool { return hypothesisOpens(hyp, match) }
			switch tactic.Type {
			case "split_disj":
				shapeName = "A ∨ B"
				shapeOk = shaped(func(t core.Term) bool { _, _, isOr := ext.MatchesOR(t); return isOr })
				if shapeOk {
					ok = proof.ApplySplitDisjAt(clone, idx)
				}
			case "split_hyp_iff":
				shapeName = "A ⇔ B"
				shapeOk = shaped(func(t core.Term) bool { a, b, isIff := ext.MatchesIFF(t); return isIff && !a.AlphaEquals(b) })
				if shapeOk {
					ok = proof.ApplySplitHypIffAt(clone, idx)
				}
			case "split_hyp_imply":
				shapeName = "A ⇒ B"
				shapeOk = shaped(func(t core.Term) bool { a, b, isImp := ext.MatchesIMPLY(t); return isImp && !a.AlphaEquals(b) })
				if shapeOk {
					ok = proof.ApplySplitHypImplyAt(clone, idx)
				}
			case "strip_quant":
				shapeName = "∃x. …"
				shapeOk = shaped(func(t core.Term) bool { return !ext.MatchesEXISTS(t).IsZero() })
				if shapeOk {
					ok = proof.ApplyStripQuantAt(clone, idx)
				}
			case "split_conj":
				shapeName = "A ∧ B"
				shapeOk = len(proof.FactConjuncts(hyp)) > 1
				if shapeOk {
					if err := e.applyConjunctsOnClone(ctx, s, clone, idx); err != nil {
						return nil, err
					}
					ok = true
				}
			}
			if !shapeOk {
				return nil, fmt.Errorf("%s hyp_index %d (%s) is not %s%s", tactic.Type, idx, ext.PrintTerm(hyp), shapeName,
					membershipReadingNote(hyp))
			}
		} else {
			spec := structuralTacticByName[tactic.Type]
			if spec.shape != nil && !spec.shape(clone.Goal) {
				return nil, fmt.Errorf("%s does not apply: goal shape does not match", tactic.Type)
			}
			ok = spec.run(ctx, clone)
		}
	default:
		// Structural tactics — single source of truth in
		// structural.go drives both this dispatch and the inspect
		// structural-fact enumerator. The shape predicate (when set) gates
		// apply too: an agent calling cond_rewrite on a non-COND goal gets
		// a clean failure instead of silently invoking basic rewrites
		// under a misleading name.
		spec, found := structuralTacticByName[tactic.Type]
		if !found {
			return nil, fmt.Errorf("unknown tactic %q", tactic.Type)
		}
		if spec.shape != nil && !spec.shape(clone.Goal) {
			return nil, fmt.Errorf("%s does not apply: goal shape does not match", tactic.Type)
		}
		ok = spec.run(ctx, clone)
	}
	if !ok {
		if msg := tacticNoProgressDiagnostic(tactic.Type); msg != "" {
			return nil, fmt.Errorf("%s", msg)
		}
		return nil, fmt.Errorf("%s did not apply to this goal", tactic.Type)
	}
	return clone, nil
}

// applySearch runs the `apply_search` tactic: the corpus's candidates for
// the goal (corpusByGoal, exact hits first), each tried as a `lemma` on a
// clone, the first that closes returned with the names tried before it.
// The corpus scan takes 3 s, or the request's budget when that is
// shorter; each candidate's apply is one lemma step.
func (e *Engine) applySearch(ctx context.Context, s *Session, goal core.Prop) (*proof.GoalStackNode, []string, error) {
	deadline := time.Now().Add(3 * time.Second)
	if d, ok := ctx.Deadline(); ok && d.Before(deadline) {
		deadline = d
	}
	group, ok := corpusByGoal(scanGoal(goal, deadline), retrieveDefaultPerGroup, deadline)
	if !ok {
		return nil, nil, nil
	}
	var tried []string
	for _, cand := range group.Entries {
		if ctx.Err() != nil {
			break
		}
		tried = append(tried, cand.Entry)
		c, err := e.runTacticOnClone(ctx, s, goal, TacticReq{Type: "lemma", LemmaKey: cand.Key})
		if err != nil || !c.Proved() {
			continue
		}
		return c, tried, nil
	}
	return nil, tried, nil
}

// applyTacticOnClone is the back-compat wrapper around runTacticOnClone
// that produces an ExpansionPlan suitable for committing into the session
// via GoalStackNode.Commit. Returns (plan, nil) on success or (nil, err)
// where err carries the specific reason for failure (e.g. circular
// lemma_key, shape mismatch).
func (e *Engine) applyTacticOnClone(ctx context.Context, s *Session, goal core.Prop, tactic TacticReq) (*proof.ExpansionPlan, error) {
	clone, err := e.runTacticOnClone(ctx, s, goal, tactic)
	if err != nil {
		return nil, err
	}
	return proof.MakeExpansionPlan(clone), nil
}

// ApplyStep applies an action to the current proof state.
// Returns the new state view and diagnostics on failure.
func (e *Engine) ApplyStep(ctx context.Context, sessionID string, req *ApplyStepRequest) (*StepResult, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if err := s.faultRefusal(); err != nil {
		return nil, err
	}
	return e.applyStepLocked(ctx, s, req)
}

// applyStepLocked is ApplyStep under the session lock.
func (e *Engine) applyStepLocked(ctx context.Context, s *Session, req *ApplyStepRequest) (*StepResult, error) {
	if req.GoalID == "" {
		return nil, fmt.Errorf("apply requires goal_id — `inspect` reports the focused goal's id as focused_goal_id")
	}
	entry, ok := s.goalIndex[req.GoalID]
	if !ok {
		return nil, fmt.Errorf("goal %s not found in session %s", req.GoalID, s.ID)
	}

	// The state this apply is about to change is snapshotted when no
	// auto-checkpoint holds it — before the session's first apply, and
	// after an add-goal — so a first move taken the wrong way can be
	// restored (see the function). Each committed direct apply records
	// the snapshot holding its pre-state, including one a failed
	// attempt created, so resume can map every listed checkpoint.
	s.preApplyCheckpointID, _ = e.ensurePreApplyCheckpointLocked(s)
	preApplyRecorded := s.preApplyCheckpointID

	// Apply the agent-supplied budget, when set. Two effects:
	//
	//  1. ctx deadline becomes the hard wall-clock cap for this apply.
	//  2. The CNF refuter inside auto / refute / expand reads its
	//     per-call timeout off a ctx-value override (see
	//     proof.CnfRefuterTimeoutCtxKey). Without (2) the inner CNF
	//     call is silently capped at env.CnfRefuterTimeout (~2s) and
	//     the agent's larger budget has no effect — the
	//     "auto fail @ ~2s regardless of budget_ms" symptom.
	if req.BudgetMs > 0 {
		bd := time.Duration(req.BudgetMs) * time.Millisecond
		ctx = context.WithValue(ctx, proof.CnfRefuterTimeoutCtxKey, bd)
		var cancel context.CancelFunc
		ctx, cancel = context.WithTimeout(ctx, bd)
		defer cancel()
	}

	scope := faultScope(ctx, s, "apply").onGoal(req.GoalID, entry, req.Tactic, req.BudgetMs)
	clone, fault, applyErr := e.runTactic(ctx, scope)
	// A run that ended well past the request's deadline is written
	// down, whatever it answered (overrun.go).
	if deadline, ok := ctx.Deadline(); ok {
		e.noteOverrun(scope, fmt.Sprintf("the apply of %s", req.Tactic.Type), deadline, cutStackOf(applyErr))
	}
	// Drain the dispatch-internal carry buffers (simp_with multi-instance
	// expansion notes + clone-stage rule-child auto-matches) regardless of
	// outcome — on failure the agent still needs to see what the resolved
	// rule set contained.
	dispatchDiags := s.pendingApplyDiagnostics
	dispatchMatched := s.pendingAutoMatched
	s.pendingApplyDiagnostics = nil
	s.pendingAutoMatched = nil
	if fault != nil {
		// An engine fault is no tactic failure: it names its record and
		// offers no repair, since a move around it is what the record
		// is there to prevent.
		return &StepResult{
			Success:     false,
			EngineFault: fault,
			Diagnostics: append(dispatchDiags, Diagnostic{
				Type:    DiagEngineFault,
				Message: fault.message(fmt.Sprintf("tactic %s on goal %s", req.Tactic.Type, req.GoalID)),
				GoalID:  req.GoalID,
			}),
		}, nil
	}
	var cutOff _CutOffError
	if errors.As(applyErr, &cutOff) {
		// The run's context ended it: nothing was decided, so there is
		// no failure to repair and no hint to give.
		return &StepResult{
			Success: false,
			Diagnostics: append(dispatchDiags, Diagnostic{
				Type:    DiagTacticFailure,
				Message: fmt.Sprintf("tactic %s on goal %s: %v", req.Tactic.Type, req.GoalID, applyErr),
				GoalID:  req.GoalID,
			}),
		}, nil
	}
	if applyErr != nil {
		diag := Diagnostic{
			Type:    DiagTacticFailure,
			Message: fmt.Sprintf("tactic %s failed on goal %s: %v", req.Tactic.Type, req.GoalID, applyErr),
			GoalID:  req.GoalID,
		}
		// Repair hints: the moves that apply to the goal
		// (collectRecommendations — expand, def_expand, induction), ranked,
		// not just "expand every definable constant".
		recs := e.collectRecommendations(ctx, entry.node.Goal, 10)
		diag.RepairHints = recommendationsToHints(recs, req.Tactic.Type, 5)
		// A `subst` refused by its size guard has one repair the generic
		// hints never name — `rw` on the same hypothesis, which is the
		// size-guard-free sibling (inspect's structural_facts lists it
		// for every equality hyp) — so it goes FIRST, ahead of the
		// unfold-the-datatype suggestions the goal's constants attract.
		var sizeGuard substSizeGuardError
		if errors.As(applyErr, &sizeGuard) {
			diag.RepairHints = append([]RepairHint{{
				Description: fmt.Sprintf(
					"try rw (hyp_index %d): the same equality hypothesis as a directed rewrite to fixpoint, "+
						"which has no size guard — subst refuses a rewrite that does not shrink the goal, rw does not; "+
						"flip:true reverses the direction",
					sizeGuard.hypIndex),
			}}, diag.RepairHints...)
		}
		return &StepResult{
			Success:     false,
			Diagnostics: append(dispatchDiags, diag),
		}, nil
	}

	plan := proof.MakeExpansionPlan(clone)

	// Snapshot the focused goal's hyps BEFORE committing the plan, so we can
	// diff against the resulting subgoals and report which hyps this apply
	// introduced (see collectAddedHyps / StepResult.NewHyps). entry.node.Goal
	// stays the pre-apply goal after Commit (Commit only attaches children),
	// but snapshot here for clarity.
	inputGoal := entry.node.Goal
	preHyps := inputGoal.Hyps()
	if !entry.node.Commit(plan) {
		return nil, fmt.Errorf(
			"goal %s is not an open leaf: a tactic was already applied to it "+
				"(it now has subgoals) or it is already closed — apply to one of "+
				"its open subgoals, or restore a checkpoint", req.GoalID)
	}
	matched := dispatchMatched
	// The cited entry certifies its own reproduction child (defer.go
	// certifyCitedEntry): a registry entry or a card this session
	// minted, whichever spelling named it.
	matched = append(matched, s.certifyCitedEntry(req.Tactic)...)
	matched = append(matched, s.runAutoPipeline()...)
	// Second drain: the post-commit pipeline can add diagnostics AFTER
	// the pre-commit buffers were drained above — collect them into the
	// same response.
	dispatchDiags = append(dispatchDiags, s.pendingApplyDiagnostics...)
	s.pendingApplyDiagnostics = nil
	s.rebuildGoalIndex()

	// Auto-checkpoint at the RPC boundary: BEFORE returning to the agent,
	// snapshot the newly-committed state under "auto_<n>". Recovery hook
	// for sub-agents that die to API infrastructure errors mid-proof —
	// the caller can Restore to the latest auto_* on session-inherit.
	// BatchApply / CommitPlan intentionally do NOT call this: they are
	// separate RPC paths whose recovery semantics we'd want to design
	// deliberately rather than add reflexively.
	s.lastAutoCheckpointID = ""
	e.maybeAutoCheckpointLocked(s)

	produced := s.collectProducedSubgoals(entry.node, entry.sectionID, inputGoal)
	effect := classifyEffect(produced)
	if req.Tactic.Type == "def_expand" {
		for _, leaf := range entry.node.UnsolvedLeaves() {
			var changed []string
			for i, h := range preHyps {
				if !leaf.Goal.AnyHyp(h.AlphaEquals) {
					changed = append(changed, fmt.Sprintf("hyp[%d] %s", i, s.Spelling().Term(h)))
				}
			}
			if len(changed) > 0 {
				dispatchDiags = append(dispatchDiags, Diagnostic{Type: DiagContextChanged, GoalID: s.openLeafID(leaf, entry.sectionID),
					Message: "def_expand rewrote or removed these original hypotheses: " + strings.Join(changed, "; ") + ". Read the resulting hypotheses before reusing an index or fact; simp_with rewrites the conclusion only."})
			}
		}
	}

	if req.Tactic.Type == "funext" && !tactic.HoldsSetBuilderAtPoint(inputGoal.Conclusion()) {
		for _, leaf := range entry.node.UnsolvedLeaves() {
			if tactic.HoldsSetBuilderAtPoint(leaf.Goal.Conclusion()) {
				dispatchDiags = append(dispatchDiags, Diagnostic{Type: DiagSetEquation, GoalID: s.openLeafID(leaf, entry.sectionID),
					Message: "funext made an equation between sets pointwise, and a set-builder side now stands applied to the point, " +
						"`{p | φ}(ẋ)`, which no move reads as a membership. " + setEquationRule})
			}
		}
	}

	// Definition sections with an authored obligation (WF) complete on
	// the apply that closes them — R4 installation runs here and the
	// completion rides this response (transcript D's "on close").
	// BatchApply/CommitPlan intentionally do not sweep (the
	// auto-checkpoint precedent): their completion semantics land with
	// a deliberate design if a consumer appears.
	defineCompleted := s.sweepPendingDefines()

	s.recordApply(req, entry.sectionID, effect, false, s.lastAutoCheckpointID, preApplyRecorded)
	s.recordProvedSections()

	return &StepResult{
		Success:         true,
		State:           s.buildStateView(),
		AutoMatched:     matched,
		NewHyps:         s.collectAddedHyps(entry.node, entry.sectionID, preHyps),
		Effect:          effect,
		Produced:        produced,
		Diagnostics:     dispatchDiags,
		DefineCompleted: defineCompleted,
	}, nil
}

// collectProducedSubgoals walks the surviving unsolved leaves under
// `applied` (the goal the tactic was applied to) and pairs each with its
// structural diff against `inputGoal` (what `applied.Goal` was BEFORE the
// commit). Leaf IDs resolve through the (already rebuilt) goalIndex so
// the agent can cross-reference into State.Goals — including the "#<n>"
// ordinal when α-equal open leaves share a content-addressed id.
//
// Returns nil when the apply closed the goal (no surviving leaves) — the
// caller's Effect classification handles "close" via len==0.
func (s *Session) collectProducedSubgoals(applied *proof.GoalStackNode, secIdx int, inputGoal core.Prop) []ProducedSubgoal {
	leaves := applied.UnsolvedLeaves()
	if len(leaves) == 0 {
		return nil
	}
	out := make([]ProducedSubgoal, 0, len(leaves))
	for _, leaf := range leaves {
		out = append(out, ProducedSubgoal{
			GoalID:  s.openLeafID(leaf, secIdx),
			Changes: computeGoalChanges(inputGoal, leaf.Goal),
		})
	}
	return out
}

// classifyEffect maps a produced-subgoal list to the StepResult.Effect /
// ProbeResult.Effect enum. Single source of truth so apply and probe agree
// on the boundary cases (notably "noop" vs "simplify" when one subgoal is
// α-equivalent to the input).
func classifyEffect(produced []ProducedSubgoal) string {
	switch len(produced) {
	case 0:
		return "close"
	case 1:
		if produced[0].Changes.IsNoop() {
			return "noop"
		}
		return "simplify"
	default:
		return "branch"
	}
}

// collectAddedHyps reports the hypotheses the just-applied tactic introduced
// into each still-open subgoal of `applied`, with their post-apply 0-based
// index in that subgoal's canonically-sorted hyp list. A hyp counts as
// "added" when it is not α-present in preHyps (the hyp list of the goal the
// tactic was applied to). The returned GoalIDs match buildStateView's (same
// indexNode formula: "s<sec>_g<shortKey>"). Returns nil when nothing was
// added (e.g. strip_quant on the conclusion, auto, split_conj), so the field
// is omitted for those tactics.
//
// This exists because the hyp list is kept in canonical sort order
// (core.MakeProp), so a hyp-adding tactic re-sorts the list and renumbers the
// tail — a pre-apply index is stale. Reporting the post-apply index lets the
// agent target the new hyp (notably instantiate's partial-∀) without a
// follow-up inspect.
func (s *Session) collectAddedHyps(applied *proof.GoalStackNode, secIdx int, preHyps []core.Term) []AddedHyp {
	var out []AddedHyp
	for _, leaf := range applied.UnsolvedLeaves() {
		for i, h := range leaf.Goal.Hyps() {
			isNew := true
			for _, p := range preHyps {
				if p.AlphaEquals(h) {
					isNew = false
					break
				}
			}
			if isNew {
				out = append(out, AddedHyp{
					GoalID: s.openLeafID(leaf, secIdx),
					Index:  i,
					Term:   s.Spelling().Term(h),
				})
			}
		}
	}
	return out
}

// resolveLemma turns a lemma TacticReq into a concrete Prop, accepting
// an inline Lemma prop, a LemmaText, or a LemmaKey naming a registry
// entry. LemmaKey wins over an inline Lemma prop — it is the canonical
// form (matches what the agent receives from Retrieve, no text-DSL
// round-trip required).
//
// A LemmaKey resolves only to a registry entry (resolveLemmaProp);
// force-replay of the landed file is the gate, not an order among
// entries. Inline lemmas are not admission-checked: the install leaves
// their statement to be proved.
func (e *Engine) resolveLemma(s *Session, tactic TacticReq, goal core.Prop) (core.Prop, error) {
	return e.resolveLemmaProp(s, tactic, goal)
}

// resolveLemmaThm resolves a lemma_key to a Thm-backed Prop for the
// tactics that consume a CERTIFICATE (type_inst, ac_regroup) rather
// than installing a statement. Resolution is resolveLemma's
// (registry-only); a resolution that is not already proved/promised is
// promise-backed through the corpus (corpusBackedInjection — a real
// forceable promise, or a fail-at-force promise that surfaces a
// missing build loudly at replay), never fabricated. No source key is
// recorded: a LemmaKey may be a registry NAME rather than an entry's own
// key, and the emit resolves the cite from the leaf's statement.
func (e *Engine) resolveLemmaThm(s *Session, tactic TacticReq, goal core.Prop) (core.Thm, error) {
	if tactic.LemmaKey == "" {
		return nil, fmt.Errorf("%s requires lemma_key (a registry entry backing a certificate)", tactic.Type)
	}
	p, err := e.resolveLemma(s, tactic, goal)
	if err != nil {
		return nil, err
	}
	if p == nil {
		return nil, fmt.Errorf("%s: lemma %s did not resolve", tactic.Type, tactic.LemmaKey)
	}
	if p.Proved() || core.IsPromised(p) {
		return core.AsThm(p), nil
	}
	if s == nil {
		return nil, fmt.Errorf("%s: lemma %s resolved without a certificate and no session backs a promise",
			tactic.Type, tactic.LemmaKey)
	}
	backed, _ := s.corpusBackedInjection(core.PropKey(tactic.LemmaKey), p,
		func(q core.Prop) core.Prop { return q })
	return core.AsThm(backed), nil
}

// resolveLemmaProp is resolveLemma's body: a LemmaText parsed in the
// focused goal's scope, a LemmaKey resolved to the statement its
// registry entry serves (registry_lemmas.go), or the inline Lemma prop.
// A request naming both a key and a text is refused: the text would be
// the statement and the key its certificate, and no entry is checked
// to state that text.
func (e *Engine) resolveLemmaProp(s *Session, tactic TacticReq, goal core.Prop) (core.Prop, error) {
	if tactic.LemmaKey != "" && tactic.LemmaText != "" {
		return nil, fmt.Errorf("the lemma names both key %q and text %q — it is cited by its key or stated by its text, "+
			"one of the two: drop `text` to cite the entry as it is stated, or `key` to state the claim "+
			"(the claim then opens as a goal of its own)", tactic.LemmaKey, abbreviateString(tactic.LemmaText, 60))
	}
	if tactic.LemmaText != "" {
		// Text-DSL lemma: parse against the focused goal's scope so a bare
		// session free-var or goal-local constant resolves without an
		// explicit `n_0:num ⊢ …` declaration prefix.
		p, err := s.readStepText(tactic.LemmaText, goal, false)
		if err != nil {
			return nil, fmt.Errorf("parse lemma: %w", err)
		}
		return p, nil
	}
	if tactic.LemmaKey != "" {
		// The key slot names a registry entry — by its own key, its
		// registered name, or the library-theorem name it serves as —
		// and nothing else (registry_lemmas.go). The served form is
		// the entry's own statement, the form ctx.Dep(<member>) serves
		// at replay and `query member` shows for the name: one equation
		// orientation, one binder order, one connective structure, one
		// set of binder letters for a term_specialize map.
		if p, rerr, ok := e.registryLemma(s, tactic.LemmaKey); ok {
			return p, rerr
		}
		// A card this session minted (defer.go), by its registered name
		// or its key: served at its statement, as a landed card is.
		if card := s.cardFor(tactic.LemmaKey); card != nil {
			return card.statement, nil
		}
		if miss := e.sessionNodeKeyMiss(s, tactic.LemmaKey); miss != nil {
			return nil, miss
		}
		return nil, e.lemmaKeyMiss(tactic.LemmaKey)
	}
	if tactic.Lemma != nil {
		return tactic.Lemma, nil
	}
	return nil, nil
}

// lemmaConclIsEquality reports whether the lemma's conclusion (after
// stripping outer ∀ binders) is an equality (`=`) or biconditional
// (`⇔` — which is `=` over bool). Used by the `lean_rw` tactic to
// reject non-equational lemmas with a clear typed error rather than
// silently failing inside lemma-application machinery.
func lemmaConclIsEquality(p core.Prop) bool {
	return lemmaTermHasRewriteClause(p.Conclusion())
}

func lemmaTermHasRewriteClause(concl core.Term) bool {
	for {
		abs := ext.MatchesFORALL(concl)
		if abs.IsZero() {
			break
		}
		concl = abs.Body()
	}
	if _, _, ok := ext.MatchesEQ(concl); ok {
		return true
	}
	if _, _, ok := ext.MatchesIFF(concl); ok {
		return true
	}
	if l, r, ok := ext.MatchesAND(concl); ok {
		return lemmaTermHasRewriteClause(l) || lemmaTermHasRewriteClause(r)
	}
	return false
}

// lookupDefConst resolves a constant by name into the ConstTerm that
// the agent-facing def_expand needs to feed proof.ApplyDefExpand.
// (Programmatic search constructs proof.DefAction directly when it
// needs the proto-serializable form; the agent path doesn't need that
// wrapper, only the const itself.)
func (e *Engine) lookupDefConst(constName string) (core.ConstTerm, error) {
	if e.env.ProofService == nil {
		return core.ConstTerm{}, fmt.Errorf("no proof service")
	}
	meta, ok := e.env.ProofService.LoadConstMeta(core.TermName(constName))
	if !ok {
		return core.ConstTerm{}, fmt.Errorf("unknown constant: %s", constName)
	}
	return core.MakeConstTerm(meta, meta.AbsType()), nil
}

// logicConstants are the constants the logic defines before any
// chapter, as ext lists them (ext.InitConstMetaMap): ⊤ and ⊥, the
// connectives, the conditional, ∀, ∃ and ∃!.
var logicConstants = sync.OnceValue(ext.InitConstMetaMap)

// logicConstantUnfoldRefusal is the refusal def_expand raises for a
// constant of the logic itself (logicConstants). No chapter entry
// defines one, so the Go a member is written in has no definition to
// name for it — Unfold takes a definition's entry — and the session
// offers no step its emitted member could not spell. What reads such a
// constant is the move made for it, or a closer.
func logicConstantUnfoldRefusal(c core.ConstTerm) error {
	if _, ofTheLogic := logicConstants().Load(c.Name()); !ofTheLogic {
		return nil
	}
	return fmt.Errorf("def_expand: %s is a constant of the logic itself, and no proof opens it by its definition. "+
		"The moves read it: strip_quant, witness and instantiate a quantifier; split_conj, split_disj, strip_imp "+
		"and case_split a connective. A closer reads ∃! through normalization: `by` with a ∃! fact as a premise "+
		"has its existence and its uniqueness, and to name its witness, `assert` the ∃ statement by the fact and "+
		"`strip_quant` it", c.Name())
}

// resolveCaseTerm resolves the boolean term a `case_split` splits on.
// constSpec is the printed representation of the term.
//
// Resolution is delegated to resolveTermWithFallback with expected=bool,
// giving case_split the same two-stage contract as
// witness/instantiate/trans:
//
//   - Fast path: exact printed-form match on a goal subterm (covers
//     Unicode-subscript inputs copied from `inspect`).
//   - Slow path: text-DSL parse of constSpec; novel composite terms are
//     accepted as long as every free name is either in goal scope or a
//     registered constant.
//
// The underlying proof.ByCaseTactic reconstructs via
// prop.ExcludedMiddle(caseTerm) — a tautology valid for ANY boolean
// term, regardless of whether it appears in the goal. So the agent CAN
// legitimately introduce a fresh discriminant (e.g. WLOG splits like
// `q1 ≤ q2` / `p = 0`). The
// underlying tactic's only no-op guard is when the term is already a
// hypothesis or the conclusion, which is enforced inside ByCaseTactic
// itself.
func (e *Engine) resolveCaseTerm(constSpec string, goal core.Prop, family *familyScope) (core.Term, error) {
	t, err := e.resolveTermWithFallback(constSpec, goal, core.TypeBool(), family)
	if err != nil {
		return nil, err
	}
	if !ext.IsBool(t) {
		return nil, fmt.Errorf("case term %q must be boolean, got type %s", constSpec, t.Type())
	}
	return t, nil
}

// resolveTermWithFallback resolves an agent-supplied printed term
// against the goal. Used by trans (middle), witness (∃- or ∃!-witness),
// instantiate (∀-witness) — tactics that take a term parameter rather
// than a structural axis.
//
// Fast path: scan goal subterms (any type, not just bool) for a
// matching printed form. Covers the common case where the term is
// already in scope (a free variable introduced by strip_quant /
// strip_imp / induction, a const, a small expression already present
// in the goal).
//
// Slow path: parse the printed form as a text-DSL term via
// dsl.ParseTermText. The goal's free-var types are passed in as ctx,
// and `expected` (when non-nil) constrains the parsed term's top type
// — e.g. trans uses the type of an equality side, witness uses the
// ∃- or ∃!-binder type. This is the path that lets the agent construct novel
// terms not appearing as subterms (e.g. `m * suc(n+p)` as a trans
// bridge when only `n+suc(p)` is visible). A scope guard rejects any
// fresh free variable the parsed term would introduce — only names
// already free in the goal, OR names resolvable as registered
// constants, are admissible.
//
// Registered-const fallback: goalConstScope only knows constants that
// occur in the goal, so a witness like `λp. PAIR'(fst(p), snd(p))`
// (the canonical pair_recursion witness) leaves fst/snd as
// free variables — they are registered constants, but they do not appear
// in the goal. Rather than reject the whole class of witness-lambda
// witnesses, we identify the parsed term's non-goal free names, look
// them up in the process-global ConstMetaManager, and re-parse with
// those metas seeded so they resolve as the (polymorphic, type-
// adapting) constants they are. Only names that are NOT goal-local
// (neither a goal const nor a goal free variable) are ever resolved
// this way, so a goal variable can never be shadowed by a same-named
// registered const. A name that is neither goal-local nor a registered
// const is rejected.
func (e *Engine) resolveTermWithFallback(spec string, goal core.Prop, expected core.HolType, family *familyScope) (core.Term, error) {
	if spec == "" {
		return nil, fmt.Errorf("tactic requires a term parameter")
	}
	for s := range ext.SubTerms(append(goal.Hyps(), goal.Conclusion())...) {
		if ext.PrintTerm(s) != spec {
			continue
		}
		// When expected is set, gate on type equality so a printed-
		// form name collision with a wrong-typed subterm doesn't
		// shadow the parser fallback. (In well-typed HOL this is
		// unlikely — names map uniquely to types within a Prop — but
		// the gate is defensive and aligns the fast path's contract
		// with the slow path's expected-type guarantee.)
		if expected != nil && !s.Type().Equals(expected) {
			continue
		}
		return s, nil
	}
	ctx := goalFreeVarTypes(goal)
	// Surface-name aliases (surface_alias.go): a witness/instantiate/
	// trans term may spell `n` for the goal's minted `n₀` where that is
	// unambiguous. Seeded before the parse; the parsed term is renamed
	// to the minted variables right after each parse, BEFORE the
	// frees-must-appear-in-the-goal guard below reads its frees.
	aliasSubsts := seedSurfaceAliases(ctx, goalSurfaceAliases(goal))
	scope := goalTermScope(goal, family)
	res := dsl.ParseTermTextInScope(spec, ctx, scope, expected)
	if len(res.Errors) > 0 {
		return nil, fmt.Errorf(
			"term %q not found as a subterm of the goal and could not be parsed as a fresh term: %s",
			spec, res.Errors[0].Message)
	}
	if len(aliasSubsts) > 0 {
		res.Term = res.Term.Substitute(aliasSubsts...)
	}

	// Classify the parsed term's non-goal free names: registered constants
	// get seeded for a re-parse; a genuinely-unknown name is rejected
	// with the scope-guard error (and we error on the FIRST such name to
	// keep the message deterministic).
	external := make(map[string]core.ConstTermMeta)
	var firstUnbound core.TermName
	haveUnbound := false
	for _, v := range res.Term.Frees(nil) {
		if goal.HasFreeName(v.Name()) {
			continue
		}
		if meta, ok := registry.GetConstMetaManager().LoadConstMeta(v.Name()); ok {
			external[string(v.Name())] = meta
			continue
		}
		if !haveUnbound {
			firstUnbound = v.Name()
			haveUnbound = true
		}
	}
	if haveUnbound {
		return nil, fmt.Errorf(
			"term %q references unbound variable %q; "+
				"free variables must already appear in the goal",
			spec, string(firstUnbound))
	}
	if len(external) == 0 {
		return res.Term, nil
	}

	// Re-parse with the registered constants seeded so applied heads like
	// fst(p) resolve via the polymorphic meta path (and type-adapt to
	// the goal's concrete component types).
	res = dsl.ParseTermTextInScope(spec, ctx, augmentConstScope(scope, external), expected)
	if len(res.Errors) > 0 {
		return nil, fmt.Errorf(
			"term %q could not be parsed after seeding registered constants: %s",
			spec, res.Errors[0].Message)
	}
	if len(aliasSubsts) > 0 {
		res.Term = res.Term.Substitute(aliasSubsts...)
	}
	for _, v := range res.Term.Frees(nil) {
		if !goal.HasFreeName(v.Name()) {
			return nil, fmt.Errorf(
				"term %q references unbound variable %q; "+
					"free variables must already appear in the goal",
				spec, string(v.Name()))
		}
	}
	return res.Term, nil
}

// goalTermScope is the ONE parse scope a term text is read under at a
// goal: a tactic's term parameter (`witness`, `instantiate`, `trans`, a
// `term_specialize` witness, a coefficient) and the `parse-term`
// preview, so what the preview reads is what the tactic reads. The
// goal's constants at their instances, the registry behind them, the
// corpus's syntax, the bound family's instance bindings and `&` domain.
//
// The goal's resident hypotheses are the scope's structure facts: an
// operator at a structure's carrier (`x + y` under a resident
// `comm_ring(R)`, a `Σ` over its addition) lowers off the record field
// or the fact that binds it, as a claim text reads the same goal
// (goalScopedPropText). And a polymorphic constant's type letters are
// the constant's own (FreshenMetaLetters), as at the statement, claim
// and lemma-text doors: `f ∘ e` over a goal whose letters are A and B
// takes composition at whatever instance the operands fix, never at
// the goal's letters because they share a name.
func goalTermScope(goal core.Prop, family *familyScope) *dsl.ParseScope {
	scope := goalConstScope(goal)
	if scope == nil {
		scope = &dsl.ParseScope{}
	}
	scope.ConstResolver = registryConstResolver
	scope.TypeResolver = registryTypeResolver
	scope.Syntax = constSyntax()
	scope.FreshenMetaLetters = true
	family.applyTo(scope)
	scope.ResidentFacts = goal.Hyps()
	scope.ResidentNames = residentSurfaceNames(goal)
	return scope
}

// constSyntax is the text parser's view of the corpus's constant
// syntax (ext/dsl/implicit.go, outfix.go): the chapters' declared
// implicit binders and notations, from the process constant registry.
func constSyntax() dsl.SyntaxTable { return registry.GetConstMetaManager() }

// ImplicitBindings is the instance bindings of the family the session
// works (registry.Family.ImplicitBindings): what a text under this
// session may leave unspelled beyond what its goal binds. nil for a
// session bound to no family, or to a family stating its laws under
// the structure's own binders.
func (s *Session) ImplicitBindings() map[string]core.Term {
	if s == nil || s.family == nil {
		return nil
	}
	return s.family.ImplicitBindings()
}

// CoerceDomain is the numeric domain the family the session works
// declares (registry.Family.CoerceDomain): what an unanchored `&` in a
// text under this session embeds into. nil for a session bound to no
// family, or to a family declaring none — there an unanchored `&` is
// refused at the statement and claim doors, as the family's own Go
// refuses it.
func (s *Session) CoerceDomain() core.HolType {
	if s == nil || s.family == nil {
		return nil
	}
	return s.family.CoerceDomain()
}

// familyScope is what a text under a session is read with beyond its
// goal: the instance bindings and the numeric domain of the family the
// session works — the two things a member's script gets from its
// family's vocabulary — and the abbreviations the session's goals were
// stated with, which a member's script gets from its statement. nil
// reads a text under no family and no table.
type familyScope struct {
	implicit      map[string]core.Term
	coerce        core.HolType
	abbreviations *dsl.AbbreviationTable
}

// familyScope is the session's reading of its family and its goals'
// abbreviations, for the doors that parse a text.
func (s *Session) familyScope() *familyScope {
	if s == nil {
		return nil
	}
	table := s.abbreviationTable()
	if s.family == nil && table == nil {
		return nil
	}
	f := &familyScope{abbreviations: table}
	if s.family != nil {
		f.implicit, f.coerce = s.family.ImplicitBindings(), s.family.CoerceDomain()
	}
	return f
}

// applyTo installs the family's reading on a parse scope. A text under
// a session binds none of a statement's leading binders itself: a
// claim that rebinds a name an abbreviation spells is refused.
func (f *familyScope) applyTo(scope *dsl.ParseScope) {
	if f == nil {
		return
	}
	scope.ImplicitBindings = f.implicit
	scope.CoerceDomain = f.coerce
	scope.Abbreviations = f.abbreviations
	scope.AbbreviationBinders = nil
}

// StatementDoorScope is the parse scope of the statement door of a
// session bound to family (nil: bound to none) — `add-goal`'s text and
// the session-less `parse-prop` preview: strict resolution (an
// undeclared name errors instead of freshening), strict mint (a bare
// polymorphic head's frozen abstract letters error instead of silently
// making the goal a different statement), a constant's type letters
// freshened at every occurrence (a statement's own `A` is never taken
// for composition's), over the corpus's registered constants, under
// the family's instance bindings and the numeric domain it declares.
//
// It is the one constructor of that scope: the door parses with it
// and FormatStatementTypedUnder checks a text against it before
// serving it, so a served `statement_typed` is a text the door reads
// and an absent one is a text the door would not.
func StatementDoorScope(family *registry.Family) *dsl.ParseScope {
	scope := &dsl.ParseScope{
		StrictResolution:   true,
		StrictMint:         true,
		FreshenMetaLetters: true,
		ConstResolver:      registryConstResolver,
		TypeResolver:       registryTypeResolver,
		Syntax:             constSyntax(),
	}
	if family != nil {
		scope.ImplicitBindings = family.ImplicitBindings()
		scope.CoerceDomain = family.CoerceDomain()
		scope.Abbreviations = family.AbbrevTable()
	}
	return scope
}

// StatementDoorScope is the session's statement door: its family's
// (StatementDoorScope), no family's for a session bound to none.
func (s *Session) StatementDoorScope() *dsl.ParseScope {
	if s == nil {
		return StatementDoorScope(nil)
	}
	return StatementDoorScope(s.family)
}

func registryConstResolver(name string) core.ConstTermMeta {
	if meta, ok := registry.GetConstMetaManager().LoadConstMeta(core.TermName(name)); ok {
		return meta
	}
	return core.ConstTermMeta{}
}

// registryTypeResolver is the registry's type vocabulary for a session
// text: a type name is known when a registered constant's type
// mentions it (registry.ConstMetaManager.TypeArity).
func registryTypeResolver(name string) (int, bool) {
	return registry.GetConstMetaManager().TypeArity(name)
}

// augmentConstScope returns a ParseScope that is `base` (the goal-local
// const scope) widened with `extra` registered-const metas. Goal-local
// entries win on name collision, so seeding a global const can never
// override a constant the goal already pins to a specific instance.
func augmentConstScope(base *dsl.ParseScope, extra map[string]core.ConstTermMeta) *dsl.ParseScope {
	metas := make(map[string]core.ConstTermMeta, len(extra))
	var consts map[string]core.ConstTerm
	if base != nil {
		consts = base.Consts
		for k, v := range base.ConstMetas {
			metas[k] = v
		}
	}
	for k, v := range extra {
		if _, ok := metas[k]; !ok {
			metas[k] = v
		}
	}
	out := &dsl.ParseScope{Consts: consts, ConstMetas: metas}
	if base != nil {
		out.Syntax = base.Syntax
		out.ImplicitBindings = base.ImplicitBindings
		out.CoerceDomain = base.CoerceDomain
		out.ResidentFacts = base.ResidentFacts
	}
	return out
}

// goalFreeVarTypes harvests free-variable name → type bindings from
// the goal (hyps + conclusion) for dsl.ParseTermText. A name that
// appears with different types in different hyps is impossible in a
// well-typed Prop, so a flat map is the natural shape.
func goalFreeVarTypes(goal core.Prop) map[string]core.HolType {
	ctx := make(map[string]core.HolType)
	for _, v := range goal.Conclusion().Frees(nil) {
		ctx[string(v.Name())] = v.Type()
	}
	for _, h := range goal.Hyps() {
		for _, v := range h.Frees(nil) {
			ctx[string(v.Name())] = v.Type()
		}
	}
	return ctx
}

// goalConstScope harvests the defined constants occurring in the goal
// (hyps + conclusion) into an dsl.ParseScope. Without this, the term-DSL
// can only resolve a constant by name from the four built-in nat encoders
// (_0/bit0/bit1/suc); every other constant name — e.g. predecessor, even
// when it appears in the goal as a constant — parses as a free variable
// and is then rejected by the scope guard ("references unbound
// variable"). Every constant enters the meta map (ConstMetas, the path
// buildApp and buildVarTerm read a constant's letters from) so a
// witness / instantiate / trans / case_split term names any constant the
// goal already mentions; a MONOMORPHIC one enters the fixed-instance map
// (Consts) beside it. A polymorphic one does not: its occurrence in the
// goal is one instance among those a text may mean, not a pin — `∅` at
// set(set(A)) in a resident `F ≠ ∅` says nothing about the `∅` of
// `s = ∅` for s:set(A). Each occurrence in the text takes its instance
// from its partner or its expected type, as Go's claim parse reads it
// (its scope pins a constant only where the author declares it,
// Script.Const). Returns nil when the goal has no constants, in which
// case parsing behaves exactly as before.
func goalConstScope(goal core.Prop) *dsl.ParseScope {
	return termsConstScope(append(goal.Hyps(), goal.Conclusion())...)
}

// termsConstScope is goalConstScope over terms that are not a goal.
func termsConstScope(terms ...core.Term) *dsl.ParseScope {
	consts := make(map[string]core.ConstTerm)
	metas := make(map[string]core.ConstTermMeta)
	for s := range ext.SubTerms(terms...) {
		c, ok := s.AsConst()
		if !ok {
			continue
		}
		name := string(c.Name())
		if _, seen := metas[name]; seen {
			continue
		}
		metas[name] = c.Meta()
		if len(c.Meta().AbsType().TypeVars()) == 0 {
			consts[name] = c
		}
	}
	if len(metas) == 0 {
		return nil
	}
	return &dsl.ParseScope{Consts: consts, ConstMetas: metas}
}

// parsePropTextInGoalScope parses an agent-supplied text-DSL proposition
// against the focused goal's scope. It is the prop-level analogue of
// resolveTermWithFallback's scope seeding: the goal's free-var types
// (goalFreeVarTypes) and goal-local constants (goalConstScope) are fed
// to the parser so a bare session free-var (n₀) or a goal-local constant
// resolves by name, without the agent having to prepend an explicit
// `n_0:num ⊢ …` type-declaration prefix.
//
// Used by the `assert` (ClaimText) and `lemma` / `lean_rw` (LemmaText)
// tactics, whose text is parsed here rather than at the CLI wire layer
// so a bare free-var's type is inferred from the goal. The `assert` case
// enforces its own frees-⊆-goal scope check downstream; here we only
// supply the types.
// parsePropTextInGoalScope is the LOOSE face: the lemma-text door
// (lemma / lean_rw state an ad-hoc lemma whose install leaves the
// statement itself to be proved) and test scaffolding.
func parsePropTextInGoalScope(text string, goal core.Prop, family *familyScope) (core.Prop, error) {
	p, _, err := goalScopedPropText(text, goal, false, family)
	return p, err
}

// parseClaimTextInGoalScope is the STRICT face — the session claim
// door (assert), resolving like the Go-side parseClaim.
func parseClaimTextInGoalScope(text string, goal core.Prop, family *familyScope) (core.Prop, error) {
	p, _, err := goalScopedPropText(text, goal, true, family)
	return p, err
}

// readStepText reads a text of the step being applied at goal — the
// claim of an assert (strict), a lemma or premise given by text — and
// notes on the step what the parse warns of its numerals
// (DiagNumeralDomain) and, for a claim, the λs it applies in place
// (DiagWrittenRedex), each note once. A session-less caller reads the
// text and notes nothing.
func (s *Session) readStepText(text string, goal core.Prop, strict bool) (core.Prop, error) {
	p, warnings, err := goalScopedPropText(text, goal, strict, s.familyScope())
	if s == nil || err != nil {
		return p, err
	}
	note := func(d Diagnostic) {
		if !slices.ContainsFunc(s.pendingApplyDiagnostics, func(have Diagnostic) bool { return have.Type == d.Type && have.Message == d.Message }) {
			s.pendingApplyDiagnostics = append(s.pendingApplyDiagnostics, d)
		}
	}
	for _, w := range warnings {
		if w.Code != dsl.CodeNumeralDomain {
			continue
		}
		note(Diagnostic{Type: DiagNumeralDomain, Message: fmt.Sprintf("in `%s`: %s; %s.", abbreviateString(text, 80), w.Message, w.Suggestion)})
	}
	if strict {
		if d, found := s.writtenRedexNote(text, p); found {
			note(d)
		}
	}
	return p, nil
}

// writtenRedexShown bounds the redexes a written_redex note spells out;
// the note counts the rest.
const writtenRedexShown = 4

// writtenRedexNote is the note on a claim that applies a λ in place
// (DiagWrittenRedex): each such application the claim holds, outermost
// first in the claim's order and each once, with the term it reduces
// to, in the session's spelling; found=false for a claim that holds
// none. The parser's own sugar builds no such application — a
// set-builder, a unique existence, a conditional are constants applied
// — so one the claim holds is one its text, or an abbreviation's,
// spells.
func (s *Session) writtenRedexNote(text string, claim core.Prop) (Diagnostic, bool) {
	var redexes []core.Term
	collectAppliedLambdas(claim.Conclusion(), &redexes)
	for h := range claim.HypIter() {
		collectAppliedLambdas(h, &redexes)
	}
	if len(redexes) == 0 {
		return Diagnostic{}, false
	}
	sp := s.Spelling()
	ctx := context.Background()
	var shown []string
	seen := map[string]bool{}
	more := 0
	for _, r := range redexes {
		row := fmt.Sprintf("`%s`, reduced `%s`", sp.Term(r), sp.Term(ext.BetaCollapse(ctx, r)))
		if seen[row] {
			continue
		}
		seen[row] = true
		if len(shown) == writtenRedexShown {
			more++
			continue
		}
		shown = append(shown, row)
	}
	rows := strings.Join(shown, "; ")
	if more > 0 {
		rows += fmt.Sprintf("; and %d more", more)
	}
	return Diagnostic{Type: DiagWrittenRedex, Message: fmt.Sprintf(
		"in `%s`: the claim applies a λ in place and is asserted with that redex in it: %s. "+
			"A law taken at a λ hands its instance over reduced, so the reduced term is the one a premise of that instance "+
			"and a later text spell: state the claim reduced, unless the redex is what it is about.",
		abbreviateString(text, 80), rows)}, true
}

// collectAppliedLambdas appends to out the maximal subterms of t that
// apply a λ in place — an application whose head, under its arguments,
// is an abstraction — in t's order. A redex inside one is part of what
// that one reduces to and is not listed again.
func collectAppliedLambdas(t core.Term, out *[]core.Term) {
	if head, args := ext.MatchesApply(t); len(args) > 0 {
		if _, lambda := head.AsAbsTerm(); lambda {
			*out = append(*out, t)
			return
		}
	}
	switch x := t.Core().(type) {
	case core.AppliedTerm:
		collectAppliedLambdas(x.Fun(), out)
		collectAppliedLambdas(x.Arg(), out)
	case core.AbsTerm:
		collectAppliedLambdas(x.Body(), out)
	}
}

// goalScopedPropText reads text at goal's scope, strictly or loosely,
// and returns what the parse warns of beside the statement.
func goalScopedPropText(text string, goal core.Prop, strict bool, family *familyScope) (core.Prop, []dsl.InputDiagnostic, error) {
	vars := goalFreeVarTypes(goal)
	// Surface-name aliases (surface_alias.go): a claim may spell `n`
	// for the goal's minted `n₀` where that is unambiguous. The alias
	// names are seeded into the scope here and the parsed result is
	// renamed to the minted variables below.
	substs := seedSurfaceAliases(vars, goalSurfaceAliases(goal))
	// `strict` is the verb split. The CLAIM door (assert) resolves
	// strictly like the Go-side parseClaim: goal frees and surface
	// aliases are declared above, so an undeclared name errors at the
	// parse with the repair named instead of freshening into a
	// downstream scope-guard mismatch. The LEMMA-text door
	// (lemma / lean_rw, a text premise of by / auto_with / simp_with)
	// stays LOOSE: an ad-hoc lemma text is a statement its install
	// leaves to be proved (the claim child), so a name it leaves free
	// is part of that statement. Both doors read a constant's type
	// letters as the constant's own (FreshenMetaLetters): a text over
	// its own `A` may hold `∘` at an instance containing that `A`, and
	// the text a proved section is cited by (lemma_name_resolve.go) is
	// its statement_typed, which the statement door reads so.
	scope := &dsl.ParseScope{Vars: vars, StrictResolution: strict, FreshenMetaLetters: true,
		Syntax: constSyntax(), ResidentFacts: goal.Hyps(), ResidentNames: residentSurfaceNames(goal)}
	family.applyTo(scope)
	if cs := goalConstScope(goal); cs != nil {
		scope.Consts = cs.Consts
		scope.ConstMetas = cs.ConstMetas
	}
	// Registered-const fallback: a claim can name any registered constant, not just
	// the ones the surrounding goal happens to mention — e.g. an `assert`
	// claim that introduces `dest_nadd(x, n)` over a goal whose free var
	// `x:nadd` does not yet apply `dest_nadd`. Without this, the DSL
	// types `dest_nadd` as a fresh free variable and the assert scope
	// guard then rejects it. The resolver is consulted only for names
	// neither already in scope nor quantifier-bound by the claim.
	scope.ConstResolver = registryConstResolver
	scope.TypeResolver = registryTypeResolver
	// A CLOSED text — every name it uses bound by its own binders, a
	// bundle binder `∀X:presheaf(A, B).` binding X's components itself —
	// is read closed, with nothing of the focus in scope: its `T` is
	// the bundle's component, never the focus's T₀ spelled `T`
	// (which would have the bundle mint X_T beside it and the text
	// state something else than the section it cites). The text
	// decides: one that reads with nothing declared is closed; one that
	// names something of the focus — a free variable, an operator a
	// resident structure fact binds — is read at the focus. The doors'
	// one reading, dsl.ParsePropTextAtDoor, which the Go doors share.
	res := dsl.ParsePropTextAtDoor(text, scope)
	if len(res.Errors) > 0 {
		return nil, nil, fmt.Errorf("%s", res.Errors[0].Message)
	}
	if strict {
		// The claim door refuses what the Go-side parseClaim refuses: a
		// polymorphic constant's letter no term of the claim fixes. An
		// ad-hoc lemma text may be polymorphic and is not asked.
		if unpinned := dsl.UnpinnedLetters(res.Prop); len(unpinned) > 0 {
			rows := make([]string, len(unpinned))
			for i, u := range unpinned {
				rows[i] = u.Repair()
			}
			return nil, nil, fmt.Errorf("the claim leaves a type letter unpinned: no term of it has that type, so nothing "+
				"says at which type the constant is read. Pin it once where the constant is written:\n  %s",
				strings.Join(rows, "\n  "))
		}
	}
	return substituteParsedProp(res.Prop, substs), res.Warnings, nil
}

// ParsePropInGoalScope is the exported preview surface for
// parsePropTextInGoalScope. It resolves (sessionID, goalID) — empty
// goalID falls back to the single focused goal, exactly as Inspect /
// Retrieve / Probe — then parses `text` against the goal's free-var
// types + goal-local constants + registered-const fallback (the same scope
// `assert.ClaimText` / `lemma.LemmaText` will see at apply time).
//
// Returns the raw dsl.ParseResult so callers can surface warnings,
// errors, and normalized_input. A non-nil error is reserved for
// session/goal lookup failure — a parse-only failure returns a valid
// ParseResult whose Errors slice is non-empty.
func (e *Engine) ParsePropInGoalScope(sessionID, goalID, text string) (dsl.ParseResult, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return dsl.ParseResult{}, err
	}
	entry, _, err := e.resolveFocusedGoal(s, goalID)
	if err != nil {
		return dsl.ParseResult{}, err
	}
	if entry == nil {
		return dsl.ParseResult{}, fmt.Errorf("session %s has no open goals", sessionID)
	}
	goal := entry.node.Goal
	vars := goalFreeVarTypes(goal)
	substs := seedSurfaceAliases(vars, goalSurfaceAliases(goal))
	// The preview mirrors the LOOSER of the two doors it serves: a
	// lemma-text preview must not error where apply would succeed. The assert door's strict verdict
	// arrives loudly at apply time either way.
	scope := &dsl.ParseScope{Vars: vars, FreshenMetaLetters: true, Syntax: constSyntax(), ResidentFacts: goal.Hyps(), ResidentNames: residentSurfaceNames(goal)}
	s.familyScope().applyTo(scope)
	if cs := goalConstScope(goal); cs != nil {
		scope.Consts = cs.Consts
		scope.ConstMetas = cs.ConstMetas
	}
	scope.ConstResolver = registryConstResolver
	scope.TypeResolver = registryTypeResolver
	// Read as the doors read it (dsl.ParsePropTextAtDoor): a closed text
	// closed, any other at the focus.
	res := dsl.ParsePropTextAtDoor(text, scope)
	if len(res.Errors) == 0 {
		res.Prop = substituteParsedProp(res.Prop, substs)
	}
	return res, nil
}

// ParseTermInGoalScope is the exported preview surface for
// resolveTermWithFallback's parse path. It resolves (sessionID, goalID)
// the same way ParsePropInGoalScope does, then builds the same scope
// resolveTermWithFallback uses (goal free-var types + goal-local const
// scope + registry resolver) and calls dsl.ParseTermTextInScope with the
// caller-supplied `expected` type.
//
// Unlike resolveTermWithFallback, this preview surface does NOT do the
// second-pass registered-const-seeding rerun — first-pass errors are the
// signal the agent wants when iterating a term-DSL string. Nor does it
// run the subterm-lookup fast path: preview is about "does this text
// parse", not "is this term already in scope".
//
// Returns the raw dsl.ParseResult; a non-nil error is reserved for
// session/goal lookup failure.
func (e *Engine) ParseTermInGoalScope(sessionID, goalID, text string, expected core.HolType) (dsl.ParseResult, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return dsl.ParseResult{}, err
	}
	entry, _, err := e.resolveFocusedGoal(s, goalID)
	if err != nil {
		return dsl.ParseResult{}, err
	}
	if entry == nil {
		return dsl.ParseResult{}, fmt.Errorf("session %s has no open goals", sessionID)
	}
	goal := entry.node.Goal
	ctx := goalFreeVarTypes(goal)
	substs := seedSurfaceAliases(ctx, goalSurfaceAliases(goal))
	res := dsl.ParseTermTextInScope(text, ctx, goalTermScope(goal, s.familyScope()), expected)
	if len(res.Errors) == 0 && res.Term != nil && len(substs) > 0 {
		res.Term = res.Term.Substitute(substs...)
	}
	return res, nil
}

// resolveInduction resolves an `induction` tactic's variable name in
// the focused goal and the induction principle for its type — the two
// inputs of proof.ApplyInduction. Dispatches by the variable's type to
// look up the principle in env.LibraryThms (num → num_induction, list →
// list_induction, etc.). Non-num types require a corresponding induction
// entry in LibraryThms.
func (e *Engine) resolveInduction(varName string, goal core.Prop) (core.VarTerm, *tactic.InductionTemplate, error) {
	inductVar, err := resolveInductionVar(goal, varName)
	if err != nil {
		return core.VarTerm{}, nil, err
	}
	tmpl, err := e.lookupInductionTemplate(inductVar.Type())
	if err != nil {
		return core.VarTerm{}, nil, fmt.Errorf(
			"induction variable %q has type %s; %w",
			varName, ext.FormatType(inductVar.Type()), err)
	}
	return inductVar, tmpl, nil
}

// A goal's induction principle is resolved by prover/tactic
// (PrincipleNameCandidates / AnalyzePrincipleForType), so that
// Script.InductStep / Script.Induct (replay side) and this engine
// dispatch (record side) go through the same logic.

// lookupInductionTemplate finds an induction principle in
// env.LibraryThms appropriate for type t and parses it into an
// InductionTemplate. Handles polymorphic principles by type-
// instantiating them at apply time (so a single `list_induction`
// registration covers list(A) for every concrete A). Returns an
// actionable error when no principle is registered.
func (e *Engine) lookupInductionTemplate(t core.HolType) (*tactic.InductionTemplate, error) {
	if cached := e.inductionTemplateCache(t); cached != nil {
		return cached, nil
	}
	candidates := tactic.PrincipleNameCandidates(t)
	if len(candidates) == 0 {
		return nil, fmt.Errorf("type is not a registered inductive type")
	}
	if e.env.LibraryThms == nil {
		return nil, fmt.Errorf(
			"no induction principle registered (LibraryThms is nil); expected one of %v",
			candidates)
	}
	for _, name := range candidates {
		thm, ok := e.env.LookupLibraryThm(name)
		if !ok || thm == nil {
			continue
		}
		tmpl, err := tactic.AnalyzePrincipleForType(thm, t)
		if err != nil {
			return nil, fmt.Errorf("principle %q has unsupported shape: %w", name, err)
		}
		if tmpl == nil {
			// Principle exists but its index type can't be unified
			// with the goal var's type. Try the next candidate.
			continue
		}
		e.cacheInductionTemplate(t, tmpl)
		return tmpl, nil
	}
	return nil, fmt.Errorf(
		"no induction principle registered (looked for %v in LibraryThms)",
		candidates)
}

// inductionTemplateCache / cacheInductionTemplate are simple per-engine
// memoization of parsed templates by type-key. The env's library
// thms are immutable per session, so the cache is set-once.
func (e *Engine) inductionTemplateCache(t core.HolType) *tactic.InductionTemplate {
	if e.inductionTemplates == nil {
		return nil
	}
	ct, ok := t.(core.CompositeType)
	if !ok {
		return nil
	}
	return e.inductionTemplates[ct.Key()]
}

func (e *Engine) cacheInductionTemplate(t core.HolType, tmpl *tactic.InductionTemplate) {
	ct, ok := t.(core.CompositeType)
	if !ok {
		return
	}
	if e.inductionTemplates == nil {
		e.inductionTemplates = make(map[core.TypeKey]*tactic.InductionTemplate)
	}
	e.inductionTemplates[ct.Key()] = tmpl
}

// resolveInductionVar resolves a variable name to the VarTerm it names
// in the focused goal: a free variable of the goal, or a binder of the
// conclusion's leading ∀-prefix, which the tactic peels. The name is
// the variable's own, as stored or as printed (`k_0`, `k₀`), a free
// variable before a binder; failing that it is the SURFACE name of a
// variable the engine minted — `k` for the `k₀` a strip left, the
// spelling every claim and term text of the session takes
// (surface_alias.go) — where exactly one variable of the goal reads so.
// No type filter: callers (lookupInductionTemplate) handle the "is this
// type inducible" question and emit a type-aware error message.
func resolveInductionVar(goal core.Prop, varName string) (core.VarTerm, error) {
	if varName == "" {
		return core.VarTerm{}, fmt.Errorf("induction requires a variable name")
	}
	var free, bound []core.VarTerm
	insert := func(into *[]core.VarTerm, v core.VarTerm) {
		if !slices.ContainsFunc(*into, func(seen core.VarTerm) bool { return seen.Equals(v) }) {
			*into = append(*into, v)
		}
	}
	for term := range utils.ConcatIter(utils.SingleIter(goal.Conclusion()), goal.HypIter()) {
		for _, v := range term.Frees(nil) {
			insert(&free, v)
		}
	}
	prefix, _ := ext.DecomposesFORALL(goal.Conclusion())
	for v := range prefix.Iter() {
		insert(&bound, v)
	}
	named := func(v core.VarTerm) bool {
		return string(v.Name()) == varName || ext.PrintTerm(v) == varName
	}
	for _, v := range slices.Concat(free, bound) {
		if named(v) {
			return v, nil
		}
	}
	var surface []core.VarTerm
	for _, v := range slices.Concat(free, bound) {
		if proof.SurfaceBase(string(v.Name())) == varName {
			insert(&surface, v)
		}
	}
	printed := func(vars []core.VarTerm) string {
		if len(vars) == 0 {
			return "none"
		}
		names := make([]string, len(vars))
		for i, v := range vars {
			names[i] = ext.PrintTerm(v)
		}
		return strings.Join(names, ", ")
	}
	switch len(surface) {
	case 1:
		return surface[0], nil
	case 0:
		return core.VarTerm{}, fmt.Errorf("induction variable %q is no variable of the focused goal — "+
			"free: %s; bound by the conclusion's leading ∀: %s", varName, printed(free), printed(bound))
	}
	return core.VarTerm{}, fmt.Errorf("induction variable %q reads as more than one variable of the focused goal (%s) — "+
		"name one as the goal prints it", varName, printed(surface))
}

// resolveFocusedGoal centralizes the "pick which open goal to operate on"
// logic shared by Inspect, Retrieve, and Probe.
//
//   - Explicit goalID wins (error if not in session).
//   - Empty goalID + 1 open goal → that goal.
//   - Empty goalID + 0 open goals → (nil, "", nil) — let the caller decide.
//   - Empty goalID + ≥2 open goals → error listing the candidates.
//
// Selection is explicit when ambiguous, so that per-goal results never
// silently apply to the wrong subgoal.
func (e *Engine) resolveFocusedGoal(s *Session, goalID string) (*goalEntry, string, error) {
	if goalID != "" {
		entry, ok := s.goalIndex[goalID]
		if !ok {
			return nil, "", fmt.Errorf("goal %s not found", goalID)
		}
		return entry, goalID, nil
	}
	switch len(s.goalIndex) {
	case 0:
		return nil, "", nil
	case 1:
		for id, entry := range s.goalIndex {
			return entry, id, nil
		}
	}
	ids := make([]string, 0, len(s.goalIndex))
	for id := range s.goalIndex {
		ids = append(ids, id)
	}
	slices.Sort(ids)
	return nil, "", fmt.Errorf("goal_id is required when %d open goals exist; pick one of: %s",
		len(ids), strings.Join(ids, ", "))
}

// collectStructuralMoves enumerates the parameterless structural sub-tactics
// whose shape preconditions match the current goal. Each candidate is verified
// by actually running it on a clone — if the tactic produces SubGoals, it's
// applicable. This matches what apply() will do, so there's no risk of the
// engine recommending a structural move that then fails.
//
// Unlike collectRecommendations, the result is intentionally unranked. Which
// axis to peel (∀ vs ⇒ vs ∧ vs ∨ vs COND) is a forward-planning decision
// driven by the agent's intended proof shape, not a search the engine should
// try to short-circuit. We surface what's available and let the agent choose.
//
// case_split is omitted on purpose — it's parameterized over boolean subterms,
// and the candidate space is too large to enumerate without ranking signal.
// Agents who want it call apply directly with the chosen term.
func collectStructuralMoves(goal core.Prop) []StructuralMove {
	return collectStructuralMovesUnder(unbudgeted, goal)
}

// collectStructuralMovesUnder is collectStructuralMoves with its probes
// under budget: a move whose probe the budget cut off is listed with
// its Unverified set.
func collectStructuralMovesUnder(budget _ProbeBudget, goal core.Prop) []StructuralMove {
	var moves []StructuralMove
	for i := range structuralTacticSpecs {
		spec := &structuralTacticSpecs[i]
		if spec.shape != nil && !spec.shape(goal) {
			continue
		}
		applies, cut := true, ""
		if spec.until != nil {
			applies, cut = budget.under("the "+spec.name+" probe", func(ctx context.Context) bool {
				return spec.until(ctx, proof.CreateGoalStack(goal))
			})
		} else {
			applies = spec.apply(proof.CreateGoalStack(goal))
		}
		if applies || cut != "" {
			moves = append(moves, StructuralMove{
				Tactic:      spec.name,
				Description: spec.description,
				Unverified:  cut,
			})
		}
	}
	return moves
}

// collectRecommendations returns the ranked moves that apply to a goal —
// the repair hints of the ApplyStep and CheckDerivation failure paths.
// Session-independent: it uses e.env directly and does not mutate
// session state.
//
// It tries the moves that change the goal (expand, def_expand,
// induction) and no search that would close it. Its callers are failure
// paths, where a close is vanishingly rare: auto has just failed, or a
// live tactic did. A search there costs seconds on a wide goal — a
// refutation, or a StrongerGoals × Normalize sweep, O(n²) in the
// hypotheses, for a cached or registered theorem stating the goal —
// on every failed apply, and `auto`, `known`, `retrieve goal` and
// `apply_search` run those when the agent asks.
func (e *Engine) collectRecommendations(ctx context.Context, goal core.Prop, maxItems int) []Recommendation {
	if maxItems <= 0 {
		maxItems = 10
	}
	var recs []Recommendation

	// 1. Try expand (BasicTactic + leaf cleanup — succeeds when goal decomposes).
	testNode := proof.CreateGoalStack(goal)
	if proof.ApplySimplify(ctx, testNode) {
		branchCount := testNode.NumUnsolvedLeaves()
		effect := "simplify"
		if testNode.Proved() {
			effect = "close"
			branchCount = 0
		}
		recs = append(recs, Recommendation{
			Tactic:      TacticReq{Type: "expand"},
			Mode:        "backward",
			Effect:      effect,
			Reversible:  false,
			Confidence:  0.9,
			BranchCount: branchCount,
			Description: "structural decomposition (strip implications, split conjunctions, quantifiers, rewrites)",
		})
	}

	// 2. Try each definable constant.
	consts := ext.CollectDefinableConsts(goal)
	for _, c := range consts {
		if len(recs) >= maxItems {
			break
		}
		// Use the rewrite-only predicate to keep Recommendations in lockstep
		// with what `apply def_expand` will commit. See TryDefTacticRewrite.
		residual, defOk := proof.TryDefTacticRewrite(goal, c)
		if !defOk {
			continue
		}
		effect := "close"
		branchCount := 0
		if residual != nil {
			effect = "simplify"
			branchCount = 1
		}
		recs = append(recs, Recommendation{
			Tactic:      TacticReq{Type: "def_expand", Const: string(c.Name())},
			Mode:        "rewrite",
			Effect:      effect,
			Reversible:  true,
			Confidence:  confDefAction,
			BranchCount: branchCount,
			Description: fmt.Sprintf("expand definition of %s", ext.PrintTerm(c)),
		})
	}

	// 3. Try InductionAction for each variable whose type has an
	// induction principle the env serves — num (num_induction), list
	// (list_induction), option (option_induction) and any <T>_INDUCT a
	// datatype door derived. The principle is resolved AT the
	// variable's type (the same lookup the apply path uses), because
	// GeneralInductionTactic asserts the template's index type equals
	// the variable's: a template analyzed at the principle's own index
	// type matches no variable in a monomorphic chapter, where a goal
	// carries `l : list(num)` rather than `l : list(A)`.
	for _, inductVar := range inductionCandidateVars(goal) {
		if len(recs) >= maxItems {
			break
		}
		tmpl, terr := e.lookupInductionTemplate(inductVar.Type())
		if terr != nil || tmpl == nil {
			continue
		}
		if _, _, ok := proof.TryInductionTactic(goal, inductVar, tmpl); !ok {
			continue
		}
		recs = append(recs, Recommendation{
			Tactic:      TacticReq{Type: "induction", Const: string(inductVar.Name())},
			Mode:        "induction",
			Effect:      "simplify",
			Reversible:  false,
			Confidence:  confDefAction,
			BranchCount: len(tmpl.Cases),
			Description: fmt.Sprintf("structural induction on %s : %s",
				ext.PrintTerm(inductVar), ext.FormatType(inductVar.Type())),
		})
	}

	rankRecommendations(recs)
	return recs
}

// recommendationsToHints converts ranked recommendations into
// repair hints, used by ApplyStep / CheckDerivation failure paths.
// excludedTactic (if non-empty) skips hints for that tactic type — pass the
// tactic that just failed so we don't suggest retrying the same thing.
func recommendationsToHints(recs []Recommendation, excludedTactic string, maxHints int) []RepairHint {
	if maxHints <= 0 {
		maxHints = 5
	}
	hints := make([]RepairHint, 0, maxHints)
	for _, r := range recs {
		if len(hints) >= maxHints {
			break
		}
		if excludedTactic != "" && r.Tactic.Type == excludedTactic {
			continue
		}
		desc := fmt.Sprintf("try %s (%s)", r.Tactic.Type, r.Description)
		if r.Tactic.Const != "" {
			desc = fmt.Sprintf("try %s on %s (%s)", r.Tactic.Type, r.Tactic.Const, r.Description)
		}
		hints = append(hints, RepairHint{Description: desc})
	}
	return hints
}

// rankRecommendations sorts recommendations in place:
//  1. Effect == "close" first (BranchCount == 0)
//  2. BranchCount ascending (low branching preferred)
//  3. Confidence descending (high confidence preferred)
//
// Uses stable sort to preserve stage order within equal-priority items.
func rankRecommendations(recs []Recommendation) {
	if len(recs) <= 1 {
		return
	}

	slices.SortStableFunc(recs, func(a, b Recommendation) int {
		// 1. Close actions always first.
		aClose := a.Effect == "close"
		bClose := b.Effect == "close"
		if aClose != bClose {
			if aClose {
				return -1
			}
			return 1
		}
		// 2. Lower branch count first.
		if c := cmp.Compare(a.BranchCount, b.BranchCount); c != 0 {
			return c
		}
		// 3. Higher confidence first.
		return cmp.Compare(b.Confidence, a.Confidence)
	})
}

// BatchApply tries multiple actions. In FirstSuccess mode, stops at first success.
// In CompareAll mode, runs all from the same checkpoint and returns all results.
func (e *Engine) BatchApply(ctx context.Context, sessionID string, req *BatchApplyRequest) (*BatchApplyResult, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if err := s.faultRefusal(); err != nil {
		return nil, err
	}
	return e.batchApplyLocked(ctx, s, req)
}

// batchApplyLocked is BatchApply under the session lock.
func (e *Engine) batchApplyLocked(ctx context.Context, s *Session, req *BatchApplyRequest) (*BatchApplyResult, error) {
	entry, ok := s.goalIndex[req.GoalID]
	if !ok {
		return nil, fmt.Errorf("goal %s not found", req.GoalID)
	}

	results := make([]StepResult, len(req.Tactics))
	winnerIndex := -1

	// Pre-compute path from section root to target node (needed for CompareAll).
	sectionRoot := s.sections[entry.sectionID].root
	var nodePath []int
	if req.Mode == CompareAll {
		nodePath = sectionRoot.NodePath(entry.node)
	}

	for i, tactic := range req.Tactics {
		clone, fault, applyErr := e.runTactic(ctx,
			faultScope(ctx, s, "batch-apply").onGoal(req.GoalID, entry, tactic, 0))
		if fault != nil {
			// The batch ends at an engine fault: a later tactic that
			// closed the goal would be the move around it.
			results[i] = StepResult{EngineFault: fault, Diagnostics: []Diagnostic{{
				Type:    DiagEngineFault,
				Message: fault.message(fmt.Sprintf("tactic %s (%d of the batch) on goal %s", tactic.Type, i, req.GoalID)),
				GoalID:  req.GoalID,
			}}}
			for j := i + 1; j < len(results); j++ {
				results[j] = StepResult{Diagnostics: []Diagnostic{{
					Type:    DiagEngineFault,
					Message: fmt.Sprintf("not run: tactic %d of the batch met engine fault %s, which ends the batch", i, fault.ID),
					GoalID:  req.GoalID,
				}}}
			}
			break
		}
		if applyErr == nil {
			plan := proof.MakeExpansionPlan(clone)
			if req.Mode == FirstSuccess {
				if !entry.node.Commit(plan) {
					return nil, fmt.Errorf(
						"goal %s is not an open leaf (already expanded or closed); "+
							"apply to one of its open subgoals, or restore a checkpoint",
						req.GoalID)
				}
				matched := s.runAutoPipeline()
				s.rebuildGoalIndex()
				s.recordApply(&ApplyStepRequest{GoalID: req.GoalID, Tactic: tactic}, entry.sectionID, "", true, "", "")
				s.recordProvedSections()
				results[i] = StepResult{
					Success:     true,
					State:       s.buildStateView(),
					AutoMatched: matched,
				}
				winnerIndex = i
				break
			}
			// CompareAll: fork state, produce preview, store plan for deferred commit.
			// Auto-match is NOT run on the preview — the session state is
			// unchanged until CommitPlan, and running auto-match on a
			// throwaway clone would require cloning the ThmCache too.
			// Agents see auto-match results only after CommitPlan.
			clonedRoot := sectionRoot.Clone()
			clonedNode := clonedRoot.NodeAt(nodePath)
			clonedNode.Commit(plan)
			preview := s.buildStateViewFromRoot(clonedRoot)

			planRef := uuid.New().String()
			s.pendingPlans[planRef] = &pendingPlan{
				plan:      plan,
				tactic:    tactic,
				goalID:    req.GoalID,
				sectionID: entry.sectionID,
				nodePath:  nodePath,
			}

			results[i] = StepResult{Success: true, State: preview, PlanRef: planRef}
			if winnerIndex == -1 {
				winnerIndex = i
			}
		} else {
			results[i] = StepResult{
				Success: false,
				Diagnostics: []Diagnostic{{
					Type:    DiagTacticFailure,
					Message: fmt.Sprintf("tactic %s failed: %v", tactic.Type, applyErr),
					GoalID:  req.GoalID,
				}},
			}
		}
	}

	return &BatchApplyResult{Results: results, WinnerIndex: winnerIndex}, nil
}

// CommitPlan applies a deferred expansion plan produced by CompareAll mode.
// The plan ref is an opaque token from a previous BatchApply(CompareAll) result.
func (e *Engine) CommitPlan(ctx context.Context, sessionID string, req *CommitPlanRequest) (*StepResult, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if err := s.faultRefusal(); err != nil {
		return nil, err
	}

	pp, ok := s.pendingPlans[req.PlanRef]
	if !ok {
		return nil, fmt.Errorf("plan ref %s not found in session %s", req.PlanRef, sessionID)
	}

	// Validate target node is still unexpanded.
	entry, ok := s.goalIndex[pp.goalID]
	if !ok {
		delete(s.pendingPlans, req.PlanRef)
		return nil, fmt.Errorf("goal %s no longer exists (state may have changed since compare_all)", pp.goalID)
	}

	if !entry.node.Commit(pp.plan) {
		delete(s.pendingPlans, req.PlanRef)
		return nil, fmt.Errorf("failed to commit plan: node may already be expanded")
	}

	// Clear all pending plans — session state has changed, old plans are stale.
	s.pendingPlans = make(map[string]*pendingPlan)
	matched := s.runAutoPipeline()
	s.rebuildGoalIndex()
	s.recordApply(&ApplyStepRequest{GoalID: pp.goalID, Tactic: pp.tactic}, pp.sectionID, "", true, "", "")
	s.recordProvedSections()
	return &StepResult{
		Success:     true,
		State:       s.buildStateView(),
		AutoMatched: matched,
	}, nil
}

// Checkpoint saves the current proof state under a name.
func (e *Engine) Checkpoint(ctx context.Context, sessionID string, name string) (string, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return "", err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if err := s.faultRefusal(); err != nil {
		return "", err
	}
	return e.checkpointLocked(s, name), nil
}

// checkpointLocked is Checkpoint under the session lock.
func (e *Engine) checkpointLocked(s *Session, name string) string {
	id := e.insertCheckpointLocked(s, name)
	s.recordCheckpoint(id, name)
	return id
}

// insertCheckpointLocked clones the current section roots into a new
// checkpoint entry, applying the LRU-eviction pass first when the name
// carries the auto_ prefix. Assumes s.mu is held.
//
// Cloning cost is O(unsolved-tree) per section (GoalStackNode.Clone: shallow
// with structural sharing on proved subtrees) — typical footprint 1-10 KB
// per checkpoint.
func (e *Engine) insertCheckpointLocked(s *Session, name string) string {
	// LRU: before inserting an auto-tagged checkpoint, evict the oldest
	// auto-tagged entry if we're at cap. Only auto_* entries are counted
	// and eligible for eviction — user-named / unnamed checkpoints are
	// sticky by design.
	if strings.HasPrefix(name, autoCheckpointNamePrefix) && e.autoCheckpointCap > 0 {
		s.evictOldestAutoCheckpointIfAtCapLocked(e.autoCheckpointCap)
	}

	cpID := uuid.New().String()

	// Clone-based checkpoint: clone each section root. All logical content
	// (Prop, Thm, SubGoals) is shared by reference; only tree structure is
	// copied. Proved subtrees are shared directly (never mutated again).
	cp := &sessionCheckpoint{
		sections:          make([]*sectionState, len(s.sections)),
		simpRules:         slices.Clone(s.simpRules),
		dataDefines:       slices.Clone(s.dataDefines),
		typedefDefines:    slices.Clone(s.typedefDefines),
		inductiveDefines:  slices.Clone(s.inductiveDefines),
		quotientDefines:   slices.Clone(s.quotientDefines),
		obligationDefines: slices.Clone(s.obligationDefines),
		pendingDefines:    slices.Clone(s.pendingDefines),
		name:              name,
		createdAt:         time.Now(),
	}
	for i, sec := range s.sections {
		cp.sections[i] = &sectionState{root: sec.root.Clone(), deferred: slices.Clone(sec.deferred), abbreviations: sec.abbreviations}
	}

	s.checkpoints[cpID] = cp
	return cpID
}

// evictOldestAutoCheckpointIfAtCapLocked deletes the oldest auto_*
// checkpoint (by createdAt) when the current count of auto_* checkpoints
// is >= cap. User-named checkpoints (names not starting with the auto_
// prefix) are ignored by this pass. Assumes s.mu is held.
func (s *Session) evictOldestAutoCheckpointIfAtCapLocked(cap int) {
	if cap <= 0 {
		return
	}
	count := 0
	var oldestID string
	var oldestAt time.Time
	for id, cp := range s.checkpoints {
		if !strings.HasPrefix(cp.name, autoCheckpointNamePrefix) {
			continue
		}
		count++
		if oldestID == "" || cp.createdAt.Before(oldestAt) {
			oldestID = id
			oldestAt = cp.createdAt
		}
	}
	if count >= cap && oldestID != "" {
		delete(s.checkpoints, oldestID)
	}
}

// ensurePreApplyCheckpointLocked snapshots the state an apply is about
// to change when no auto-checkpoint holds it, and returns the id of the
// checkpoint holding that state — the one it took (created true) or the
// existing one that still held it — and "" with auto-checkpointing off. The auto-checkpoints
// are taken AFTER each apply, so before the session's FIRST apply there
// was nothing to restore to — an induction taken the wrong way on the
// first move could not be undone, and agents abandoned the lineage and
// opened a second session instead — and after an add-goal the newest
// snapshot predates the added section, so restoring past a wrong first
// move on it would lose the section. The snapshot is named `auto_<n>`
// for the n applies so far — `auto_0` before the first — so every
// auto_<n> reads "the state after apply n, with whatever was added
// before apply n+1"; a stale auto_<n> (the post-apply snapshot an
// add-goal outdated) is replaced under the same name, and one that
// still holds the state is kept. Not itself a lineage event: a
// resumed lineage re-issues its applies and this runs again on each;
// the apply event carries the id so a restore to it maps on resume.
// Assumes s.mu is held.
func (e *Engine) ensurePreApplyCheckpointLocked(s *Session) (id string, created bool) {
	if e.autoCheckpointCap <= 0 {
		return "", false
	}
	name := fmt.Sprintf("%s%d", autoCheckpointNamePrefix, s.autoCheckpointSeq)
	for id, cp := range s.checkpoints {
		if cp.name != name {
			continue
		}
		if cp.holds(s) {
			return id, false
		}
		delete(s.checkpoints, id)
	}
	return e.insertCheckpointLocked(s, name), true
}

// holds reports whether the snapshot still covers the session's state
// in the dimensions an apply does not change but the other moves do:
// the sections (add-goal), the rule and definition tables. An apply
// changes a section's TREE, which every post-apply snapshot already
// captured at its own moment.
func (cp *sessionCheckpoint) holds(s *Session) bool {
	return len(cp.sections) == len(s.sections) &&
		len(cp.simpRules) == len(s.simpRules) &&
		len(cp.dataDefines) == len(s.dataDefines) &&
		len(cp.typedefDefines) == len(s.typedefDefines) &&
		len(cp.inductiveDefines) == len(s.inductiveDefines) &&
		len(cp.quotientDefines) == len(s.quotientDefines) &&
		len(cp.obligationDefines) == len(s.obligationDefines) &&
		len(cp.pendingDefines) == len(s.pendingDefines)
}

// maybeAutoCheckpointLocked creates an "auto_<n>" checkpoint when the
// engine's auto-checkpoint cap is > 0. Called from the RPC-boundary
// ApplyStep after a successful commit + rebuildGoalIndex; not called
// from BatchApply / CommitPlan (which are also RPC-boundary commits,
// but current usage keeps the /prove-recovery scope to ApplyStep).
// Assumes s.mu is held.
func (e *Engine) maybeAutoCheckpointLocked(s *Session) {
	if e.autoCheckpointCap <= 0 {
		return
	}
	s.autoCheckpointSeq++
	name := fmt.Sprintf("%s%d", autoCheckpointNamePrefix, s.autoCheckpointSeq)
	s.lastAutoCheckpointID = e.insertCheckpointLocked(s, name)
}

// ListCheckpoints returns metadata for every checkpoint stored in the
// session, sorted by createdAt ascending. The NumOpenLeaves count is
// computed from the snapshot's section roots — a low count typically
// indicates a near-complete state worth restoring to.
//
// Returns an empty slice (no error) when the session has no checkpoints.
func (e *Engine) ListCheckpoints(_ context.Context, sessionID string) ([]CheckpointInfo, error) {
	s, err := e.getSession(sessionID)
	if err != nil {
		return nil, err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	out := make([]CheckpointInfo, 0, len(s.checkpoints))
	for id, cp := range s.checkpoints {
		openLeaves := 0
		for _, sec := range cp.sections {
			openLeaves += sec.root.NumUnsolvedLeaves()
		}
		out = append(out, CheckpointInfo{
			ID:            id,
			Name:          cp.name,
			CreatedAt:     cp.createdAt,
			NumOpenLeaves: openLeaves,
			NumSections:   len(cp.sections),
		})
	}
	slices.SortFunc(out, func(a, b CheckpointInfo) int {
		return a.CreatedAt.Compare(b.CreatedAt)
	})
	return out, nil
}

// Restore reverts the session to a previously saved checkpoint.
func (e *Engine) Restore(ctx context.Context, sessionID string, checkpointID string) error {
	s, err := e.getSession(sessionID)
	if err != nil {
		return err
	}
	s.mu.Lock()
	defer s.mu.Unlock()
	if err := s.faultRefusal(); err != nil {
		return err
	}
	return e.restoreCheckpointLocked(s, checkpointID)
}

// restoreCheckpointLocked is Restore under the session lock.
func (e *Engine) restoreCheckpointLocked(s *Session, checkpointID string) error {
	if _, ok := s.checkpoints[checkpointID]; !ok {
		return fmt.Errorf("checkpoint %s not found in session %s", checkpointID, s.ID)
	}
	e.restoreLocked(s, checkpointID)
	return nil
}

// restoreLocked is Restore under the session lock, for a checkpoint
// known to exist.
func (e *Engine) restoreLocked(s *Session, checkpointID string) {
	cp := s.checkpoints[checkpointID]

	// Clone the checkpoint's sections so the checkpoint itself remains reusable
	// for multiple restores.
	s.sections = make([]*sectionState, len(cp.sections))
	for i, sec := range cp.sections {
		s.sections[i] = &sectionState{root: sec.root.Clone(), deferred: slices.Clone(sec.deferred), abbreviations: sec.abbreviations}
	}
	s.simpRules = slices.Clone(cp.simpRules)
	s.dataDefines = slices.Clone(cp.dataDefines)
	s.typedefDefines = slices.Clone(cp.typedefDefines)
	s.inductiveDefines = slices.Clone(cp.inductiveDefines)
	s.quotientDefines = slices.Clone(cp.quotientDefines)
	s.obligationDefines = slices.Clone(cp.obligationDefines)
	s.pendingDefines = slices.Clone(cp.pendingDefines)
	s.pendingPlans = make(map[string]*pendingPlan) // clear stale plans
	// Re-run the auto-pipeline on the restored state. The checkpoint's
	// tree was already processed at snapshot time, so this is usually a
	// no-op; we run it anyway for idempotency.
	s.runAutoPipeline()
	s.rebuildGoalIndex()
	s.recordRestore(checkpointID)
}
