// Command xugo is XuGo's command line: the read-only queries over the
// corpus, the proof session — one command per process, or served over
// HTTP by `serve` for an agent to drive — and the stateless checks.
//
// Usage:
//
//	xugo [flags] <command> [command-flags]
//
// `xugo --help` lists the commands and `xugo <command> --help` one
// command's inputs; engine/xugo-engine.md is the manual.
//
// All commands accept JSON on stdin and produce JSON on stdout.
// Human-readable errors go to stderr.
package main

import (
	"context"
	"encoding/json/jsontext"
	json "encoding/json/v2"
	"errors"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"
	"time"

	"github.com/euc-ai/xugo/library/registry"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/engine"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/library/integrity/manifest"
	"github.com/euc-ai/xugo/library/serve"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// ---------------------------------------------------------------------------
// Operation trace logging
// ---------------------------------------------------------------------------

// TraceEntry is a single operation trace record, written as one JSON line.
type TraceEntry struct {
	Timestamp   string `json:"ts"`
	Command     string `json:"cmd"`
	InputRaw    string `json:"input_raw"`
	InputParsed any    `json:"input_parsed,omitempty"`
	ParseError  string `json:"parse_error,omitempty"`
	Output      any    `json:"output,omitempty"`
	Error       string `json:"error,omitempty"`
	ExitCode    int    `json:"exit_code"`
	ParseMs     int    `json:"parse_ms"`
	EngineMs    int    `json:"engine_ms"`
	TotalMs     int    `json:"total_ms"`
	DiagCount   int    `json:"diag_count"`
}

var (
	traceLogPath string
	traceStart   time.Time
	traceEntry   TraceEntry
	stdinCached  bool
	stdinData    []byte
)

// ---------------------------------------------------------------------------
// JSON wire types — flat structures for CLI I/O
// ---------------------------------------------------------------------------

// PropInput names a proposition in a JSON envelope:
//
//   - `text`: agent-authored text DSL, parsed by dsl.ParsePropText
//     (handles symbol normalization, type inference, structured
//     diagnostics on failure). A statement — a goal, an assert claim,
//     a check-derivation premise or conclusion — is given this way.
//   - `key`: a proof-registry entry (its own key or registered name),
//     accepted only where a lemma is named (lemma / lean_rw).
//   - `read_at`: beside `key` on a `lemma`, the instance the entry — a
//     structure LAW — is read at, as a `by` premise's or a `simp_with`
//     rule's `{key, read_at}` names it (an entry `{key}`, a resident
//     hypothesis `{hyp_index}`, or a reading `{key, read_at}`): the Go
//     `Law.Read(instance)` cited.
//
// There is no proto / proto_hex ingress through JSON. Proto stays
// inside in-process Go APIs and (future) gRPC.
type PropInput struct {
	Text   string             `json:"text,omitempty"`
	Key    string             `json:"key,omitempty"`
	ReadAt *engine.ReadAtSpec `json:"read_at,omitempty"`
	// Abbreviations is a goal's abbreviation table (add-goal): the
	// names its text and the texts of its proof spell as «Name», each
	// with the term it stands for, in order — an entry may spell the
	// entries before it. Entry names a registry member instead: the
	// goal is that member's statement, its abbreviations the member's
	// own — the way a card is attacked as its author stated it.
	Abbreviations dsl.Abbrev `json:"abbreviations,omitempty"`
	Entry         string     `json:"entry,omitempty"`
	// AllowDuplicate admits a text goal that a PROVED section of the
	// session already states. Without it the door refuses: such a
	// section closes on its sibling at its first step and proves
	// nothing of its own — a clean re-proof of a proved statement goes
	// through `restore` to a checkpoint before that section instead.
	AllowDuplicate bool `json:"allow_duplicate,omitempty"`
}

type CheckDerivationInput struct {
	Premises   []PropInput `json:"premises"`
	Conclusion PropInput   `json:"conclusion"`
	TimeoutMs  int         `json:"timeout_ms,omitempty"`
}

type CheckConsistencyInput struct {
	Statements []PropInput `json:"statements"`
	TimeoutMs  int         `json:"timeout_ms,omitempty"`
}

type AddGoalInput struct {
	SessionID string    `json:"session_id"`
	Goal      PropInput `json:"goal"`
}

type ApplyInput struct {
	SessionID string     `json:"session_id"`
	GoalID    string     `json:"goal_id"`
	Tactic    TacticJSON `json:"tactic"`
	// BudgetMs caps wall-clock time inside search-y tactics (`auto`,
	// `refute`, `expand` — anything that reaches the CNF refuter).
	// When > 0, the engine wraps the apply ctx with this deadline and
	// the inner CnfRefuter honors the parent deadline instead of its
	// own hard-coded default. Absent or ≤ 0: the prover-env default
	// (`CnfRefuterTimeout`) applies. Structural tactics ignore this
	// field — their cost is dominated by unification + kernel checks,
	// not search.
	BudgetMs int `json:"budget_ms,omitempty"`
}

// InspectInput supports the augmented Inspect RPC. GoalID is optional —
// when set (or when the session has exactly one open goal) the response
// includes structural_facts for that goal.
type InspectInput struct {
	SessionID string `json:"session_id"`
	GoalID    string `json:"goal_id,omitempty"`
	// BudgetMs is the time each clocked probe of the structural pass
	// has (engine.InspectRequest.BudgetMs).
	BudgetMs int `json:"budget_ms,omitempty"`
}

// RetrieveInput selects one of the RetrieveModes (goal / consts /
// name_pattern / related_to). Mode is required — no
// implicit default.
type RetrieveInput struct {
	SessionID   string              `json:"session_id"`
	Mode        engine.RetrieveMode `json:"mode"`
	GoalID      string              `json:"goal_id,omitempty"`
	BudgetMs    int                 `json:"budget_ms,omitempty"`
	Consts      []string            `json:"consts,omitempty"`
	NamePattern string              `json:"name_pattern,omitempty"`
	RelatedTo   string              `json:"related_to,omitempty"`
	MaxPerGroup int                 `json:"max_per_group,omitempty"`
}

// ProbeInput drives the Probe RPC. The tactic is the same wire shape as
// for apply / batch-apply.
type ProbeInput struct {
	SessionID string     `json:"session_id"`
	GoalID    string     `json:"goal_id,omitempty"`
	Tactic    TacticJSON `json:"tactic"`
	BudgetMs  int        `json:"budget_ms,omitempty"`
}

type BatchApplyInput struct {
	SessionID string       `json:"session_id"`
	GoalID    string       `json:"goal_id"`
	Tactics   []TacticJSON `json:"tactics"`
	Mode      string       `json:"mode"` // "first_success" or "compare_all"
}

type CheckpointInput struct {
	SessionID string `json:"session_id"`
	Name      string `json:"name"`
}

type RestoreInput struct {
	SessionID    string `json:"session_id"`
	CheckpointID string `json:"checkpoint_id"`
}

type CommitPlanInput struct {
	SessionID string `json:"session_id"`
	GoalID    string `json:"goal_id"`
	PlanRef   string `json:"plan_ref"`
}

type SessionIDInput struct {
	SessionID string `json:"session_id"`
}

// TacticJSON is the wire format for tactics.
//
// HypIndex is a *int (not a plain int) so JSON omission is distinguishable
// from an explicit `0`. Without that, a `{"type":"subst"}` request with no
// hyp_index would silently default to hyp 0, mutate the proof if that hyp
// happens to be a usable equality, and break the agent's mental model
// ("the engine acted on a parameter I didn't supply"). The required-field
// check lives in tacticReqFromInput.
type TacticJSON struct {
	Type       string     `json:"type"`                  // expand, refute, lemma, def_expand, known, case_split, induction, assert, auto, auto_with, by, simp_with, set_tac, type_inst, ac_regroup, arith, rewrite, split_conj, split_disj, strip_imp, strip_quant, simplify, denote, let, plus the LEAN-style additions (assumption, refl, left, right, funext, by_contra, symm, subst, rw, trans, congr, congr_arg, congr_fun, intro, lean_rw) and aliases (apply, unfold, use, specialize, cases, rfl; `simp` is its own verb — the session simp set, falling back to simplify)
	Const      string     `json:"const,omitempty"`       // for def_expand: const name; case_split: term; induction: var name; witness/instantiate/trans: printed term; congr_arg: function term f; congr_fun: argument term x
	Lemma      *PropInput `json:"lemma,omitempty"`       // for lemma / lean_rw — `{"key": "<entry>"}` (a registry entry: its own key or registered name; preferred) or `{"text": "..."}` (ad hoc DSL); for lemma also `{"key": "<law>", "read_at": {…}}`, the law read at an instance (the Go `Law.Read(instance)`)
	Claim      *PropInput `json:"claim,omitempty"`       // for assert — `{"text": "..."}` (ad hoc DSL); must resolve to a hyp-free Prop
	HypIndex   *int       `json:"hyp_index,omitempty"`   // for subst / rw / congr_arg / congr_fun / instantiate (all required — instantiate lost its no-index first-match sugar to give agents ONE grounding action); optional for split_disj / split_hyp_iff / split_hyp_imply / strip_quant (target that hyp instead of the first of the shape), split_conj (split THAT conjunctive hypothesis instead of the conclusion) and def_expand (open const in THAT hypothesis alone); absence ≠ 0
	HypIndices []int      `json:"hyp_indices,omitempty"` // for clear (REQUIRED, its only hyp param) — the SET of 0-based indices to drop in one apply; a single drop is [i]; indices against the goal as shown
	Terms      []string   `json:"terms,omitempty"`       // for instantiate — multi-witness form: ground the ∀-hyp at hyp_index by peeling one leading binder per entry (text-DSL terms, binder order); ONE composite `specialize` ministep, adds only the final instance, consumes the source unless keep. Mutually exclusive with const.
	Keep       bool       `json:"keep,omitempty"`        // for instantiate terms form — keep the grounded source ∀-hyp resident (it will serve another witness tuple later)
	Flip       bool       `json:"flip,omitempty"`        // for rw — false: rewrite the hyp's written direction (a→b); true: reversed (b→a)
	Name       string     `json:"name,omitempty"`        // for denote — the variable name the `const` term is abbreviated by ("let <name> = <const>"); omitted, the step mints α₀. Requires const. For let — the name the `const` term is defined as; required.
	// Specialize is the LEGACY positional-witness form of the
	// pre-instantiation parameter. It was REMOVED in favor of the named-map
	// `term_specialize`. We still parse it here so a request that uses the
	// old shape gets a clean error from tacticReqFromInput — silent drop
	// (Go json's default for unknown fields) would let the agent think
	// specialization fired when nothing happened.
	Specialize     []string                 `json:"specialize,omitempty"`       // LEGACY — rejected with a "use term_specialize" error; see tacticReqFromInput.
	TermSpecialize map[string]string        `json:"term_specialize,omitempty"`  // for lemma / lean_rw / cite-node — pre-substitutes the outer term-level ∀-binders before install/rewrite via β-substitution + type-unification. Keys are ∀-binder names (from the entry's printed statement, or — for cite-node — the cited node's ∀-closed conclusion); values are witness terms parsed via the text-DSL against the goal's scope. Polymorphic binders are pinned automatically by the witness's concrete type — no companion `type_specialize` needed for the binder's vars. On cite-node it collapses the graft-then-instantiate ladder into one call. See engine.TacticReq.TermSpecialize.
	TypeSpecialize map[string]string        `json:"type_specialize,omitempty"`  // for lemma / lean_rw — pre-substitutes the lemma's free TYPE vars before install/rewrite. Keys are the lemma's type-var names (read from the entry's printed statement, e.g. `set_member⟨A:var:B⟩` shows `A` and `B`); values are type expressions parsed via dsl.ParseTypeText (`?71152`, `num`, `num→bool`, `var:A`). Partial maps allowed; unknown key or unparseable value is a hard error. The pre-σ source AlphaKey is still recorded as polymorphicSourceKey, so dep extraction points at the polymorphic entry. See engine.TacticReq.TypeSpecialize.
	WithLemmas     []engine.LemmaWithSpec   `json:"with_lemmas,omitempty"`      // for auto_with (scoped lemma list installed only for this call; failure discards them) AND simp_with (the ordered rewrite-rule set). Each entry: {key | text, optional type_specialize / term_specialize / flip / normalized}.
	KeepHypIndices []int                    `json:"keep_hyp_indices,omitempty"` // for auto_with — every hyp index NOT in this set is cleared. Mutually exclusive with drop_hyp_indices. Empty + drop empty: default heuristic clears every top-level ∀-headed hyp.
	DropHypIndices []int                    `json:"drop_hyp_indices,omitempty"` // for auto_with — exactly those indices are cleared. Mutually exclusive with keep_hyp_indices.
	NodeID         string                   `json:"node_id,omitempty"`          // for cite-node (required) — the target closed-subtree node id. Accepts the local session's own `closed_subtrees[].node_id` (format `s<N>_c<hash>`), the derivation pool's 16-char prefix (as returned by any session's post-close goal id `s0_gprop_<prefix>`), or a full AlphaKey. See engine.TacticReq.NodeID.
	ByHyps         []engine.ByHypSpec       `json:"by_hyps,omitempty"`          // for by — RESIDENT premises: hyps of the focused goal named as premises (kept across by's clear-first; everything unnamed is cleared). Each: {hyp_index, optional terms (witnesses, the hyp's own binder order)}. Recorded by statement, index-free.
	ByShape        *engine.ByShapeReq       `json:"by_shape,omitempty"`         // for by — declared shaping between the installs and the close: {normalized | pre_normalized | denoted:<n> | hilbert}. Omitted = no shaping.
	Arith          bool                     `json:"arith,omitempty"`            // for by — close with the gated arithmetic closer (the math layer's ByArith) instead of the CNF refuter. Scope-gated exactly as replay (omega circularity gate) — never taken silently.
	Settac         bool                     `json:"settac,omitempty"`           // for by — close with the membership-mode set driver (the math layer's BySets) instead of the CNF refuter. Mutually exclusive with arith. A premise-free by{settac} is the one legal bare `by`. See engine.TacticReq.Settac.
	Chase          *engine.ByChaseReq       `json:"chase,omitempty"`            // for by — close with the diagram-chase closer (the math layer's ByChase): {depth:<pull-back rounds>}. Mutually exclusive with arith and settac; premises required. See engine.TacticReq.Chase.
	Broadcast      bool                     `json:"broadcast,omitempty"`        // for by — run the terminal closer over every leaf the shaping fanned out (the math layer's Broadcast option) instead of demanding a single one.
	Source         *engine.ElementarityRef  `json:"source,omitempty"`           // for elementarity — the source: an entry ({"key"}) stating the property at a concrete structure or a family of models by prime, or a resident hypothesis ({"hyp_index"}); absent for the embedding mode. See engine.TacticReq.ElementaritySource.
	Facts          []engine.ElementarityRef `json:"facts,omitempty"`            // for elementarity — the resident hypotheses and entries the step's obligations are read from (the structures, the homomorphism, each parameter's bound). See engine.TacticReq.ElementarityFacts.
	Assoc          string                   `json:"assoc,omitempty"`            // for ac_regroup (required) — the registry entry (own key or registered name) of the ⊕ associativity law (∀m n p. (m⊕n)⊕p = m⊕(n⊕p), either orientation). See engine.TacticReq.Assoc.
	Sym            string                   `json:"sym,omitempty"`              // for ac_regroup (required) — the registry entry (own key or registered name) of the ⊕ commutativity law (∀m n. m⊕n = n⊕m), same op as assoc.
}

// ---------------------------------------------------------------------------
// Globals
// ---------------------------------------------------------------------------

var (
	eng          *engine.Engine
	proverEnv    *proof.ProverEnv
	constMetaMgr *registry.ConstMetaManager
	// dataDirFlag is the --data-dir the command line gave, "" for none.
	dataDirFlag string
)

// engineFreeCommands are the commands that drive no engine: the corpus
// queries, the corpus's browser and the registry fingerprint read the
// registry and library/index, `cards` reads the registry and session
// transcripts, and `faults` reads the fault store. main runs them
// before initEngine.
var engineFreeCommands = map[string]func(args []string){
	"query":                cmdQuery,
	"browse":               cmdBrowse,
	"cards":                cmdCards,
	"registry-fingerprint": func([]string) { cmdRegistryFingerprint() },
	"faults":               cmdFaults,
}

// faultStoreUnder is the fault store of a data dir.
func faultStoreUnder(dataDir string) string { return filepath.Join(dataDir, "faults") }

// whistleTrunc bounds a printed statement for the [whistle] stderr
// line — divergent goals can be enormous; the AlphaKey in the event
// already identifies the goal at the cut exactly.
func whistleTrunc(s string) string {
	const max = 400
	if len(s) <= max {
		return s
	}
	return s[:max] + "…"
}

// initEngine builds the session engine. dataDir, when set, is where
// sessions persist: their lineages under <dataDir>/sessions
// (engine/lineage.go), the CNF certificates and conditioning plans
// they record under <dataDir>/cnf_cache (engine.SessionCNFStore), and
// the records of the engine faults they met under <dataDir>/faults
// (engine/fault.go).
func initEngine(dataDir string) {
	// Divergence-whistle tripwire: fires are impossible on healthy paths
	// (backstops sit above every legitimate maximum), so each one is a
	// live diagnosis lead — a divergent rule that would otherwise hang
	// the session. stderr is the channel agents/orchestrators
	// already tail; the line names the `by` that was running, where one
	// was (the event's Step), and the printed statement plus the session
	// transcript is enough to build a repro. A `by` whose close fired it
	// says so in its own response too (engine.DiagByWhistle). Installed
	// once here, before any session concurrency starts.
	skeleton.OnWhistleFire = func(ev skeleton.WhistleEvent) {
		detail := ev.String()
		if statement := tactic.WhistleCutStatement(ev); statement != "" {
			// goal= keys the goal at the cut. A refused case analysis is
			// read at the goal it was entered with, and says so.
			label := "stmt"
			if ev.Open > 0 {
				label = "entered"
			}
			detail += " " + label + "=" + whistleTrunc(statement)
		}
		fmt.Fprintf(os.Stderr, "[whistle] %s\n", detail)
	}

	opts := initSessionEnv(dataDir)
	installEngineBundles()
	if _, err := manifest.Build(); err != nil {
		panic(fmt.Sprintf("canonical proof dependency manifest: %v", err))
	}
	eng = engine.NewEngine(proverEnv, opts...)
}

// initSessionEnv gives the command handlers a fresh prover environment and
// returns the engine options for its session and certificate stores.
func initSessionEnv(dataDir string) []engine.EngineOption {
	var cnfCache utils.Map[core.TermKey, core.Prop]
	// The session env reads constants from the corpus's registry — the
	// engine's built-ins and the chapters' mints, linked through
	// library/serve — and nothing else: a text that names a constant no
	// chapter defines does not parse.
	constMetaMgr = registry.GetConstMetaManager()
	proverEnv = &proof.ProverEnv{
		ProofService: &proof.ProofService{
			LoadConstMeta:        constMetaMgr.LoadConstMeta,
			LoadOrStoreConstMeta: constMetaMgr.LoadOrStoreConstMeta,
			Syntax:               constMetaMgr,
			// The datatype kit's type-name-in-use probe: freshness of a
			// new type name is checkable only by scanning the registered
			// constants' types (type identity is structural).
			RangeConstMeta: constMetaMgr.Range,
		},
		CnfRefuterTimeout:     2 * time.Second,
		CnfNormalizationCache: &cnfCache,
		CnfNormalizeCache:     proof.NewCNFNormalizeCache(),
	}
	var opts []engine.EngineOption
	if dataDir != "" {
		// Without the store every CNF refute during a session is a fresh
		// live refute whose certificate is discarded, and every
		// conditioned By loses its plan — so emit's CollectCNFCache (which
		// computes the SAME keys) finds nothing, and a resume cannot
		// replay. The store is one value, both tables — see
		// proof.CNFStore.
		store, err := engine.OpenSessionCNFStore(filepath.Join(dataDir, "cnf_cache"))
		if err != nil {
			fatal("open the session CNF store: %v", err)
		}
		proverEnv.ProofService.CNFStore = store
		opts = append(opts, engine.WithSessionStore(filepath.Join(dataDir, "sessions")),
			engine.WithFaultStore(faultStoreUnder(dataDir)))
	}
	// Induction principles: corpus-backed ONLY. Each entry is a promise
	// backed by the chapter member that proves it (peano.Induction /
	// list.Induction / option.Induction) in the analyzer-friendly sequent
	// shape. There is deliberately NO TestThm fallback for corpus-missing
	// names: absence makes
	// `induction` on that type fail attributably, whereas a fabricated
	// placeholder would let it proceed on a forged cert (and the corpus env
	// itself panics at init if a principle's entry does not bridge to its
	// sequent form).
	if proverEnv.LibraryThms == nil {
		proverEnv.LibraryThms = map[string]core.Thm{}
	}
	for name, thm := range serve.InductionPrinciples() {
		proverEnv.LibraryThms[name] = thm
	}
	// Register the kernel-verified corpus by key — each entry under its
	// own key (cheap — stores closures only; defines/forces nothing until
	// a key is required). This lets
	// the engine's auto-match close a proved-earlier leaf with the dep's real,
	// forceable promise instead of a fabricated core.TestThm (serve.RegisterAll
	// / engine.corpusBackedInjection).
	serve.RegisterAll(proverEnv)
	return opts
}

// installEngineBundles installs the proof policy and the corpus-backed
// decision procedures used by the session engine.
func installEngineBundles() {
	// Install omega's NatLemmaBundle from the corpus. This makes the engine's
	// `ring` and `linarith` apply moves SOUND: ring/norm_num/linarith leaves
	// bind real corpus theorems instead of placeholder TestThms. Production has
	// no placeholder fabricator (omega/bundle.go), so any unbound leaf
	// panics at the placeholder seam rather than fabricating.
	serve.InstallProofPolicy()
	serve.InstallNatBundle()
	// Install omega's RealLemmaBundle from the corpus. This turns on the real
	// `arith` / `auto` path: goalHasArithContent (engine/structural.go) now
	// recognizes real `+`/`*`/comparison content via omega.IsRealArithContent,
	// gated on omega.RealArithEnabled() — true iff a real bundle is installed —
	// and ArithDecideWithHyps dispatches its decide leaves PER ATOM by operand
	// type. Same soundness contract as the nat bundle: no placeholder
	// fabricator in production, so a degraded real leaf panics at the seam
	// rather than fabricating. See prover/solver/omega/README.md §"The real (ℝ)
	// layer". Reentrant: InstallRealBundle is promise-based (statements only
	// at install, each entry's Build deferred to first force), so repeat calls
	// from serve_test.go are safe.
	serve.InstallRealBundle()
	// Install omega's IntLemmaBundle (and the IntBridges that IntOfRealThm
	// reads) from the corpus. Turns on the int `arith` / `auto` path: the
	// shape gate (engine/structural.go goalHasArithContent) recognizes int
	// `+` / `*` / comparison content via omega.IsIntArithContent, gated on
	// omega.IntArithEnabled() — true iff an int bundle is installed — and
	// ArithDecideWithHyps dispatches its decide leaves PER ATOM by operand
	// type. Must come AFTER InstallRealBundle: the lifted ℝ sources and
	// the IntOfRealThm bridges' own proofs reach into real arith. Same
	// soundness contract: no placeholder fabricator in production, so a
	// degraded int leaf panics at the seam rather than fabricating. See
	// prover/solver/omega/README.md §"The integer (int) type layer".
	serve.InstallIntBundle()
	// Structure ring: the algebra chapters' general laws and the
	// carrier instances (ℂ) the ring at a comm_ring / field fact reads.
	serve.InstallStructureRingBundle()
	// Diagram chase: the algebra and set chapters' carrier laws the
	// chase closer reads at a module diagram.
	serve.InstallChaseBundle()
	// Record normal form: the record equations an instance is computed
	// with where it is handed over (prover/tactic, InstanceNormal).
	serve.InstallRecordNormal()
}

// ---------------------------------------------------------------------------
// PropInput resolution
// ---------------------------------------------------------------------------

// propFromInput resolves a wire statement `PropInput` to a kernel
// `core.Prop`: its `Text`, parsed and typechecked through
// dsl.ParsePropText. A statement is given as text; `key` names a
// registry entry only in a lemma slot.
func propFromInput(in PropInput) (core.Prop, error) {
	if in.Key != "" {
		return nil, fmt.Errorf("a statement is given as 'text'; 'key' (%q) names a registry entry "+
			"only where a lemma is cited", in.Key)
	}
	if in.ReadAt != nil {
		return nil, fmt.Errorf("a statement is given as 'text'; 'read_at' reads a law at an instance " +
			"only where a lemma is cited")
	}
	if in.Text == "" {
		return nil, fmt.Errorf("PropInput must set 'text'")
	}
	res := dsl.ParsePropText(in.Text)
	if len(res.Errors) > 0 {
		return nil, fmt.Errorf("parse text: %s", res.Errors[0].Message)
	}
	return res.Prop, nil
}

// leanAliasMap normalizes LEAN-style tactic names to XuGo canonical
// forms. Pure surface translation — no behavior change. Engine-level
// dispatchers (`intro`, `lean_rw`) are NOT in this table; they live in
// runTacticOnClone because their semantics differ from a plain rename
// (smart shape dispatch / equality-precondition check).
var leanAliasMap = map[string]string{
	"apply":      "lemma",
	"unfold":     "def_expand",
	"use":        "witness",
	"specialize": "instantiate",
	// "simp" is deliberately NOT an alias any more: it is its own engine
	// verb (the simp set of the manual's R4 — rewrites with the session's
	// define-installed equations, falling back to `simplify` when nothing
	// is installed).
	"cases": "case_split",
	"rfl":   "refl",
	// Not a Lean name: the tactic table is snake_case throughout and
	// `cite-node` is its one hyphenated wire type, so the snake_case
	// spelling is accepted here (and in the engine dispatch) rather
	// than refused as "unknown tactic" with hints pointing at unfolding.
	"cite_node": "cite-node",
}

func tacticReqFromInput(tactic TacticJSON) (engine.TacticReq, error) {
	// LEAN aliases: rewrite the type and fall through to the canonical
	// dispatch below. The other fields (Lemma, Const, HypIndex) are
	// forwarded as-is — they map 1:1 onto the canonical tactic's
	// parameters.
	tType := tactic.Type
	if canonical, ok := leanAliasMap[tType]; ok {
		tType = canonical
	}
	// Legacy-parameter rejection: the positional `specialize` array was
	// removed in favor of the named-map `term_specialize`. Reject any
	// request that still uses the old shape, regardless of tactic type —
	// silent drop (Go json's default) would let an agent believe its
	// specialization fired when nothing happened.
	if len(tactic.Specialize) > 0 {
		return engine.TacticReq{}, fmt.Errorf(
			"the `specialize` parameter (positional witness list) was removed; " +
				"use `term_specialize` instead — a named map " +
				"{\"<binder_name>\": \"<witness_text>\", ...} keyed by the lemma's " +
				"outer ∀-binder names (the manual's `lemma` row)")
	}
	switch tType {
	case "lemma", "lean_rw":
		if tactic.Lemma == nil {
			return engine.TacticReq{}, fmt.Errorf("%s tactic requires a 'lemma' field with 'key' or 'text'", tType)
		}
		if tactic.Lemma.Key != "" && tactic.Lemma.Text != "" {
			return engine.TacticReq{}, fmt.Errorf("lemma PropInput must set exactly one of 'text' or 'key', not both")
		}
		// `read_at` makes the key a structure law read at an instance —
		// the Go `Law.Read(instance)` — on `lemma` alone: `lean_rw` takes
		// the entry as a rewrite rule, and a reading rewrites through
		// `simp_with`. The engine refuses text and type_specialize beside
		// it (hypothesis_moves.go).
		if tactic.Lemma.ReadAt != nil {
			if tType != "lemma" {
				return engine.TacticReq{}, fmt.Errorf("%s takes no read_at — a law read at an instance is cited by `lemma`, "+
					"a `by` premise or a `simp_with` rule", tType)
			}
			if tactic.Lemma.Key == "" {
				return engine.TacticReq{}, fmt.Errorf("lemma: read_at reads a law at an instance — give the law's 'key': an entry's key, or a proved section's id")
			}
		}
		// The key path (a registry entry) is preferred — short-circuit
		// to the engine's LemmaKey resolution so we don't redundantly
		// load the prop into the wire layer just to hand it back.
		// TermSpecialize / TypeSpecialize forward through unchanged
		// (their dispatch happens inside the engine's lemma / lean_rw
		// branch after resolveLemma). Both apply to lemma and lean_rw —
		// term-level pre-substitution operates on the lemma BEFORE the
		// rewrite-path's equality check.
		if tactic.Lemma.Key != "" {
			return engine.TacticReq{
				Type:           tType,
				LemmaKey:       tactic.Lemma.Key,
				ReadAt:         tactic.Lemma.ReadAt,
				TermSpecialize: tactic.TermSpecialize,
				TypeSpecialize: tactic.TypeSpecialize,
			}, nil
		}
		// Text DSL: defer parsing to the engine, where the focused goal's
		// free-var types and constants are in scope. Parsing here at the
		// wire layer would be scope-blind, and a bare session free-var
		// (n₀) would need an explicit `n_0:num ⊢ …` prefix.
		if tactic.Lemma.Text == "" {
			return engine.TacticReq{}, fmt.Errorf("%s tactic requires a 'lemma' field with 'key' or 'text'", tType)
		}
		return engine.TacticReq{
			Type:           tType,
			LemmaText:      tactic.Lemma.Text,
			TermSpecialize: tactic.TermSpecialize,
			TypeSpecialize: tactic.TypeSpecialize,
		}, nil
	case "subst":
		// Required-field validation: hyp_index must be explicit.
		// Without this guard, `{"type":"subst"}` would default to hyp 0
		// (the Go zero value) and silently mutate the proof if hyp 0
		// happens to be a usable equality. Catching it here gives the
		// agent a clear error instead.
		if tactic.HypIndex == nil {
			return engine.TacticReq{}, fmt.Errorf("subst requires the 'hyp_index' field (the index of the equality hyp to substitute by)")
		}
		return engine.TacticReq{
			Type:     tType,
			Const:    tactic.Const,
			HypIndex: tactic.HypIndex,
		}, nil
	case "clear":
		// `hyp_indices` is clear's only hyp param and is required (a single
		// drop is `[i]`). There is no `hyp_index` form for clear — every
		// clear records one `clear_hyps` ministep.
		if len(tactic.HypIndices) == 0 {
			return engine.TacticReq{}, fmt.Errorf("clear requires the 'hyp_indices' field (0-based hyp index/indices to drop; a single drop is [i])")
		}
		return engine.TacticReq{
			Type:       tType,
			HypIndices: tactic.HypIndices,
		}, nil
	case "rw":
		// hyp_index is required and must be explicit — same rationale as
		// subst: a missing index would otherwise silently default to
		// rewriting with hyp 0.
		if tactic.HypIndex == nil {
			return engine.TacticReq{}, fmt.Errorf("rw requires the 'hyp_index' field (the index of the equality hyp to rewrite with; optional 'flip' reverses the direction)")
		}
		return engine.TacticReq{
			Type:     tType,
			HypIndex: tactic.HypIndex,
			Flip:     tactic.Flip,
		}, nil
	case "assert":
		// The claim is a text statement, deferred to the engine so the
		// goal's free-var types / constants are in scope — a bare session
		// free-var (n₀) then resolves without an explicit `n_0:num ⊢ …`
		// prefix.
		if tactic.Claim == nil || tactic.Claim.Text == "" {
			return engine.TacticReq{}, fmt.Errorf("assert tactic requires a 'claim' field with 'text'")
		}
		if tactic.Claim.Key != "" {
			return engine.TacticReq{}, fmt.Errorf("assert claim is given as 'text'; 'key' names a registry entry only where a lemma is cited")
		}
		return engine.TacticReq{Type: tType, ClaimText: tactic.Claim.Text}, nil
	case "auto_with":
		// Scoped lemma + focused auto in one atomic close-or-fail call.
		// Forward with_lemmas (each may carry its own type_specialize),
		// keep_hyp_indices, drop_hyp_indices. The engine layer enforces
		// keep/drop mutual exclusion + index range + the close-or-fail
		// rollback. See engine/auto_with.go.
		return engine.TacticReq{
			Type:           tType,
			WithLemmas:     tactic.WithLemmas,
			KeepHypIndices: tactic.KeepHypIndices,
			DropHypIndices: tactic.DropHypIndices,
		}, nil
	case "by":
		// The math layer's premise-disciplined close as a session move
		// (auto_with's DECLARED sibling): by_hyps (resident premises,
		// kept + optionally grounded) + with_lemmas (named premises,
		// installed + optionally grounded via term_specialize) + by_shape
		// + one refutation (or `arith` for the gated closer). Recorded
		// as ONE `by` composite ministep — exactly the By(...) the
		// Go spells; emit renders it back 1:1. Close-or-fail.
		// See engine/by_tactic.go.
		return engine.TacticReq{
			Type:       tType,
			ByHyps:     tactic.ByHyps,
			ByShape:    tactic.ByShape,
			WithLemmas: tactic.WithLemmas,
			Arith:      tactic.Arith,
			Settac:     tactic.Settac,
			Chase:      tactic.Chase,
			Broadcast:  tactic.Broadcast,
			// auto_with's hypothesis lists reach the engine, which refuses
			// them on a `by` by name (engine/by_tactic.go); left here, the
			// request would run without them.
			KeepHypIndices: tactic.KeepHypIndices,
			DropHypIndices: tactic.DropHypIndices,
		}, nil
	case "by_induction":
		// Go's ByInduction as a session move (engine/by_induction.go):
		// the principle under `lemma` by key, its tuple under
		// term_specialize, the extras under by_hyps / with_lemmas, the
		// shaping under by_shape.
		if tactic.Lemma == nil || tactic.Lemma.Key == "" {
			return engine.TacticReq{}, fmt.Errorf("by_induction takes the induction principle under `lemma`, by key: " +
				"{\"type\":\"by_induction\",\"lemma\":{\"key\":\"<entry>\"},\"by_hyps\":[{\"hyp_index\":0}]} — the predicate " +
				"is read from the goal at the index that hypothesis fixes; \"term_specialize\":{\"P\":\"λ…\"} writes one that is not the goal")
		}
		if tactic.Lemma.Text != "" {
			return engine.TacticReq{}, fmt.Errorf("by_induction: the principle is an entry named by key — a text states nothing the terminal's claim is certified by")
		}
		if tactic.Lemma.ReadAt != nil {
			return engine.TacticReq{}, fmt.Errorf("by_induction takes no read_at — the principle is cited as stated; a law read at an instance is a `lemma`, a `by` premise or a `simp_with` rule")
		}
		return engine.TacticReq{
			Type:           tType,
			LemmaKey:       tactic.Lemma.Key,
			TermSpecialize: tactic.TermSpecialize,
			TypeSpecialize: tactic.TypeSpecialize,
			ByHyps:         tactic.ByHyps,
			WithLemmas:     tactic.WithLemmas,
			ByShape:        tactic.ByShape,
			// `by`'s closers reach the engine, which refuses them on a
			// by_induction by name (engine/by_induction.go).
			Arith:  tactic.Arith,
			Settac: tactic.Settac,
		}, nil
	case "simp_with", "simp_all":
		// Joint-fixpoint conditional rewrite with an ordered rule set
		// (StepProto_SimpWith). The engine reads with_lemmas — the rule
		// set of simp_with, the rules simp_all adds to the installed set
		// — and hyp_index, which makes simp_with rewrite that hypothesis
		// in its place (Lean's `simp at h`). Hyp keep/drop is not a
		// parameter: rules discharge side conditions against the
		// resident hyps as they are. Both fields are named here because
		// the default arm forwards neither list: a dropped with_lemmas
		// reads "requires a non-empty with_lemmas list", and a dropped
		// hyp_index rewrites the conclusion without a word. See
		// engine/engine.go `case "simp_with"`, `case "simp_all"`.
		return engine.TacticReq{
			Type:       tType,
			WithLemmas: tactic.WithLemmas,
			HypIndex:   tactic.HypIndex,
		}, nil
	case "type_inst":
		// A polymorphic entry read AT a type instance — closes the
		// focused goal when it is a type instantiation of the entry (σ is
		// recovered from the goal itself, so there is no type map to
		// pass). Key-only: the tactic consumes a CERTIFICATE, which a
		// text lemma does not carry.
		if tactic.Lemma == nil || tactic.Lemma.Key == "" {
			return engine.TacticReq{}, fmt.Errorf(
				"type_inst requires a 'lemma' field with 'key' (the polymorphic entry; " +
					"σ is recovered from the goal, so no type map is passed)")
		}
		if tactic.Lemma.ReadAt != nil {
			return engine.TacticReq{}, fmt.Errorf("type_inst takes no read_at — it reads the entry at a type instance; a law read at an instance is a `lemma`, a `by` premise or a `simp_with` rule")
		}
		return engine.TacticReq{
			Type:     tType,
			LemmaKey: tactic.Lemma.Key,
		}, nil
	case "ac_regroup":
		// The AC kit's goal face: the focused goal must be the bare
		// equation between two ⊕-sums over one leaf multiset; assoc/sym
		// name the ⊕ laws' entries. Required-field guards here so a
		// missing key errors at the wire instead of silently dropping
		// (the silent-drop bug class this file's guards exist to prevent).
		if tactic.Assoc == "" || tactic.Sym == "" {
			return engine.TacticReq{}, fmt.Errorf(
				"ac_regroup requires 'assoc' and 'sym' — the entries of the op's " +
					"associativity and commutativity laws")
		}
		return engine.TacticReq{
			Type:  tType,
			Assoc: tactic.Assoc,
			Sym:   tactic.Sym,
		}, nil
	case "cite-node":
		// Required-field validation with a clean, actionable error. Without
		// this the default case would silently fall through with NodeID=""
		// (before this field even existed on TacticJSON, the wire layer
		// dropped `node_id` entirely and cite-node's cross-session graft
		// path was unreachable through the RPC while looking superficially
		// invoked — the exact class of silent-drop bug this file's other
		// required-field guards exist to prevent). See engine.TacticReq.NodeID
		// for the format spectrum (session-local closed_subtrees id, pool
		// prefix, full AlphaKey).
		if tactic.NodeID == "" {
			return engine.TacticReq{}, fmt.Errorf(
				"cite-node requires the 'node_id' field (session's closed_subtrees[].node_id like `s0_c<hash>`, a derivation pool 16-char prefix like `s0_gprop_<prefix>` from any session's post-close goal id, or a full AlphaKey)")
		}
		return engine.TacticReq{
			Type:           tType,
			NodeID:         tactic.NodeID,
			TermSpecialize: tactic.TermSpecialize,
		}, nil
	case "denote":
		// `const` (the term to name) + `name` (what to call it) are the
		// EXPLICIT form; both omitted is the search form. Forwarded
		// explicitly because the default arm below drops `name`, and a
		// silently-dropped name would denote under α₀ while the agent
		// believed it had named the term.
		if tactic.Name != "" && tactic.Const == "" {
			return engine.TacticReq{}, fmt.Errorf("denote: 'name' requires 'const' (the term to name); the bare search form mints its own variable")
		}
		return engine.TacticReq{
			Type:  tType,
			Const: tactic.Const,
			Name:  tactic.Name,
		}, nil
	case "let":
		// The definition move, "let <name> := <const>": both are its
		// content, and both are forwarded by name — the default arm
		// drops `name`.
		if tactic.Name == "" || tactic.Const == "" {
			return engine.TacticReq{}, fmt.Errorf("let requires 'name' (what the object is called) and 'const' (the term it is defined as)")
		}
		return engine.TacticReq{
			Type:  tType,
			Const: tactic.Const,
			Name:  tactic.Name,
		}, nil
	case "elementarity":
		// The source, the facts and the fixed-parameter terms are the step's
		// whole call; the engine dispatch validates them.
		return engine.TacticReq{
			Type:               tType,
			ElementaritySource: tactic.Source,
			ElementarityFacts:  tactic.Facts,
			Terms:              tactic.Terms,
		}, nil
	case "instantiate":
		// Forward the multi-witness `terms` form alongside the primitive
		// `const` form — an unforwarded field here is the silent-drop bug
		// class this file's guards exist to prevent (the agent would see
		// "instantiate requires a term" while believing terms was sent).
		// terms-form validation (requires hyp_index, excludes const,
		// binder-type checks) lives in the engine dispatch.
		return engine.TacticReq{
			Type:     tType,
			Const:    tactic.Const,
			HypIndex: tactic.HypIndex,
			Terms:    tactic.Terms,
			Keep:     tactic.Keep,
		}, nil
	default:
		// Forward HypIndex as-is (pointer, so absence vs 0 is preserved).
		// Other tactics ignore it; round-tripping keeps the wire-vs-engine
		// mapping faithful.
		return engine.TacticReq{
			Type:     tType,
			Const:    tactic.Const,
			HypIndex: tactic.HypIndex,
		}, nil
	}
}

// ---------------------------------------------------------------------------
// Output helpers
// ---------------------------------------------------------------------------

func writeJSON(v any) {
	traceEntry.Output = v
	data, err := json.Marshal(v)
	if err != nil {
		fatal("marshal output: %v", err)
	}
	os.Stdout.Write(data)
	os.Stdout.Write([]byte("\n"))
}

func fatal(format string, args ...any) {
	msg := fmt.Sprintf(format, args...)
	fmt.Fprintf(os.Stderr, "xugo: %s\n", msg)
	traceEntry.ExitCode = 1
	traceEntry.Error = msg
	writeTrace()
	os.Exit(1)
}

// captureStdin reads all of stdin on first call, caches the result,
// and records the raw input for tracing. Commands that don't need stdin
// (e.g. session-create) simply never call this, avoiding a terminal hang.
func captureStdin() []byte {
	if !stdinCached {
		var err error
		stdinData, err = io.ReadAll(os.Stdin)
		if err != nil {
			fatal("read stdin: %v", err)
		}
		stdinCached = true
		raw := string(stdinData)
		if len(raw) > 8192 {
			// The byte cut can split a multi-byte glyph; trace entries
			// marshal as JSON, which rejects the invalid tail.
			raw = strings.ToValidUTF8(raw[:8192], "") + "...(truncated)"
		}
		traceEntry.InputRaw = raw
	}
	return stdinData
}

// readInput decodes a command's stdin through the door an RPC body
// enters (decodeRPCInput): a member the input does not declare is
// refused by name and JSON path on the command line as over HTTP.
func readInput(v any) {
	readInputFromBytes(captureStdin(), v)
}

// writeTrace appends a JSON-lines trace entry to the trace log file.
// No-op if tracing is not enabled. Errors are silently ignored —
// trace logging must never break the tool.
func writeTrace() {
	if traceLogPath == "" {
		return
	}
	traceEntry.Timestamp = traceStart.Format(time.RFC3339Nano)
	traceEntry.TotalMs = int(time.Since(traceStart).Milliseconds())

	data, err := json.Marshal(traceEntry)
	if err != nil {
		return
	}

	f, err := os.OpenFile(traceLogPath, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		return
	}
	defer f.Close()
	f.Write(data)
	f.Write([]byte("\n"))
}

// ---------------------------------------------------------------------------
// RPC dispatch — pure functions returning (result, error) for HTTP server reuse
// ---------------------------------------------------------------------------

// decodeRPCInput reads an RPC body — or a command's stdin, which
// readInput sends here — into a handler's input, refusing any member
// the input does not declare: a misspelled or misplaced field
// is an error naming it and its JSON path, never a value silently
// dropped by `omitempty` and reported later as a downstream symptom —
// `tactic.lemma.type_specialize` nested inside the PropInput instead
// of `tactic.type_specialize` on the TacticInput once surfaced as
// "type_specialize did nothing". The envelope's `cmd` is dispatch's
// own — serve.go reads it before the handler sees the body — and is
// dropped here, so no input declares it.
func decodeRPCInput(body []byte, in any) error {
	var members map[string]jsontext.Value
	if err := json.Unmarshal(body, &members); err != nil {
		return fmt.Errorf("parse input: %w", err)
	}
	delete(members, "cmd")
	stripped, err := json.Marshal(members)
	if err != nil {
		return fmt.Errorf("parse input: %w", err)
	}
	if err := json.Unmarshal(stripped, in, json.RejectUnknownMembers(true)); err != nil {
		return fmt.Errorf("parse input: %w%s", err, misplacedSpecializeHint(err))
	}
	return nil
}

// misplacedSpecializeHint says where `term_specialize` / `type_specialize`
// go when the refusal is for one of them written INSIDE the `lemma`
// object. `key` lives there, so the nested spelling is the natural
// guess, and the bare refusal — unknown member within "/tactic/lemma" —
// reads as "this tactic takes no specialize". Empty for any other
// refusal.
func misplacedSpecializeHint(err error) string {
	var refused *json.SemanticError
	if !errors.As(err, &refused) {
		return ""
	}
	pointer := string(refused.JSONPointer)
	for _, member := range []string{"term_specialize", "type_specialize"} {
		if strings.HasSuffix(pointer, "/lemma/"+member) {
			return fmt.Sprintf(" — %s is a SIBLING of `lemma` on the tactic, not a member of it: "+
				"{\"type\":\"lemma\",\"lemma\":{\"key\":\"…\"},\"%s\":{…}}", member, member)
		}
	}
	return ""
}

// rpcDispatch routes a command name + JSON body to the appropriate handler.
// Returns the result to be serialized as JSON, or an error.
func rpcDispatch(ctx context.Context, cmd string, body []byte) (any, error) {
	switch cmd {
	// Session workflow
	case "session-create":
		return rpcSessionCreate(ctx, body)
	// session-close intentionally NOT exposed via RPC. Sessions are
	// load-bearing across multi-sub-agent orchestrations (assert-defer-
	// validate-first decomposition shares state via assert-claim-becomes-
	// hyp + cite-node within ONE session). Closing destroys sibling
	// goals, closed_subtrees, and checkpoints with no recovery; in
	// practice sub-agents called this defensively and trampled
	// orchestrator state. The shared serve auto-times-out (4h default),
	// reclaiming idle sessions naturally. Internal engine.CloseSession
	// remains available for test cleanup; only the agent-facing RPC is
	// removed.
	case "add-goal":
		return rpcAddGoal(body)
	case "session-lineage":
		return rpcSessionLineage(body)
	case "registry-fingerprint":
		return rpcRegistryFingerprint(body)
	case "dump-section":
		return rpcDumpSection(body)
	case "emit-section":
		return rpcEmitSection(body)
	case "defer":
		return rpcDefer(ctx, body)
	case "cards":
		return rpcCards(body)
	case "inspect":
		return rpcInspect(ctx, body)
	case "apply":
		return rpcApply(ctx, body)
	case "retrieve":
		return rpcRetrieve(ctx, body)
	case "probe":
		return rpcProbe(ctx, body)
	case "batch-apply":
		return rpcBatchApply(ctx, body)
	case "checkpoint":
		return rpcCheckpoint(ctx, body)
	case "restore":
		return rpcRestore(ctx, body)
	case "list-checkpoints":
		return rpcListCheckpoints(ctx, body)
	case "commit-plan":
		return rpcCommitPlan(ctx, body)
	// Stateless verification
	case "check":
		return rpcCheck(ctx, body)
	case "check-derivation":
		return rpcCheckDerivation(ctx, body)
	case "check-consistency":
		return rpcCheckConsistency(ctx, body)
	case "parse-prop":
		return rpcParseProp(body)
	case "parse-term":
		return rpcParseTerm(body)
	case "define":
		return rpcDefine(body)
	case "query":
		return rpcQuery(body)
	default:
		return nil, fmt.Errorf("unknown command: %s", cmd)
	}
}

// rpcSessionCreate creates a session. The optional body binds it to a
// family — `{"family":"iterate/real/real_sum"}`, optionally with
// `"imports":["words/machine_word"]` — so the session starts with those
// families' registered definitions installed as use rules
// (engine.SetSessionFamily); the response carries the binding. Every
// session has the semantics: proved sibling sections are
// citable, a cite must be a named theorem or an entry, and
// `emit-section` renders the family form. `{"resume":"<id>"}` rebuilds a persisted
// session from its lineage instead.
func rpcSessionCreate(ctx context.Context, body []byte) (any, error) {
	var in struct {
		Family  string   `json:"family,omitempty"`
		Imports []string `json:"imports,omitempty"`
		// Resume rebuilds a persisted session under its own id by
		// replaying its lineage (engine.ResumeSession). Exclusive with
		// the other fields — the lineage carries the family binding.
		Resume string `json:"resume,omitempty"`
	}
	if len(body) > 0 {
		// Tolerate an empty / absent body.
		if err := decodeRPCInput(body, &in); err != nil {
			return nil, err
		}
	}
	if in.Resume != "" {
		if in.Family != "" || len(in.Imports) > 0 {
			return nil, fmt.Errorf("session-create: resume takes no family — the lineage carries it")
		}
		res, err := eng.ResumeSession(ctx, in.Resume)
		if err != nil {
			return nil, err
		}
		return struct {
			engine.SessionInfo
			Resume *engine.ResumeResult `json:"resume"`
		}{res.Session, res}, nil
	}
	if in.Family == "" && len(in.Imports) > 0 {
		return nil, fmt.Errorf("session-create: imports require a family")
	}
	info, err := eng.CreateSession(ctx)
	if err != nil {
		return nil, err
	}
	if in.Family == "" {
		return info, nil
	}
	binding, err := eng.SetSessionFamily(info.ID, in.Family, in.Imports)
	if err != nil {
		_ = eng.CloseSession(ctx, info.ID)
		return nil, err
	}
	info.Family, info.Imports = binding.Family, binding.Imports
	return struct {
		engine.SessionInfo
		Binding *engine.FamilyBinding `json:"binding"`
	}{*info, binding}, nil
}

// rpcSessionLineage returns a session's recorded transcript,
// summarized (engine.SessionLineage).
// RegistryFingerprintOutput is the registry a binary linked: the entry
// count and registry.Fingerprint's digest over every `name\tkey` line.
// The serve answers it as the `registry-fingerprint` RPC and prints it
// at startup; `xugo registry-fingerprint` computes it for the binary
// at hand. Equal digests mean the serve cites exactly what a fresh
// build would; a differing one means a member landed (or moved key or
// name) since the serve was built, and the serve must be rebuilt
// before a brief names that member.
type RegistryFingerprintOutput struct {
	Entries     int    `json:"entries"`
	Fingerprint string `json:"fingerprint"`
}

func registryFingerprintOutput() RegistryFingerprintOutput {
	entries, digest := registry.Fingerprint()
	return RegistryFingerprintOutput{Entries: entries, Fingerprint: digest}
}

func rpcRegistryFingerprint(body []byte) (any, error) {
	var in struct{}
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	return registryFingerprintOutput(), nil
}

// cmdRegistryFingerprint prints the registry fingerprint of THIS
// binary — the freshly built one — for comparison with a running
// serve's `registry-fingerprint` RPC answer (or its startup line).
func cmdRegistryFingerprint() {
	out, _ := json.Marshal(registryFingerprintOutput())
	fmt.Println(string(out))
}

func rpcSessionLineage(body []byte) (*engine.LineageView, error) {
	var in SessionIDInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	return eng.SessionLineage(in.SessionID)
}

func rpcDumpSection(body []byte) (*engine.SectionDump, error) {
	var in struct {
		SessionID string `json:"session_id"`
		Section   int    `json:"section"`
		MaxNodes  int    `json:"max_nodes,omitempty"`
	}
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	return eng.DumpSection(in.SessionID, in.Section, in.MaxNodes)
}

// rpcEmitSection renders a closed session section (plus the earlier
// proved sections include_prior selects) as a member of a family, and
// returns the CNF certificates its replay would read. See
// engine.Engine.EmitSection for the full contract.
//
// Input: {session_id, section, func_name?, include_prior?, family?}.
//   - func_name defaults to "Build_Draft".
//   - include_prior ([]int, default null): which other proved sections
//     render with the target, as the member's lemmas. See
//     engine.EmitSectionRequest.IncludePrior for the tri-state.
//   - family (string): the family's registered path (e.g.
//     "real/real_field"); defaults to the family the session is bound
//     to. See engine.EmitSectionRequest.Family.
//
// Output: engine.EmitSectionResult. A CNF collection error comes with
// the rendered member (engine.EmitSection): the response carries the
// result's fields beside the error.
func rpcEmitSection(body []byte) (any, error) {
	var in struct {
		SessionID    string `json:"session_id"`
		Section      int    `json:"section"`
		FuncName     string `json:"func_name,omitempty"`
		IncludePrior []int  `json:"include_prior,omitempty"`
		Family       string `json:"family,omitempty"`
	}
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	out, err := eng.EmitSection(&engine.EmitSectionRequest{
		SessionID:    in.SessionID,
		Section:      in.Section,
		FuncName:     in.FuncName,
		IncludePrior: in.IncludePrior,
		Family:       in.Family,
	})
	if out == nil {
		return nil, err
	}
	return out, err
}

func rpcAddGoal(body []byte) (any, error) {
	var in AddGoalInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	return addSessionGoal(in.SessionID, in.Goal)
}

// addSessionGoal is the shared add-goal path used by both the RPC and
// CLI surfaces: the goal's text, parsed in the session's scope, becomes
// a new section. A goal states a closed theorem: a text with
// hypotheses left of ⊢ is refused (closedGoalRefusal).
func addSessionGoal(sessionID string, goal PropInput) (any, error) {
	if goal.Key != "" {
		return nil, fmt.Errorf("a goal is given as 'text' or as 'entry'; 'key' names a registry entry only where a lemma is cited")
	}
	s, err := eng.GetSession(sessionID)
	if err != nil {
		return nil, err
	}
	if err := s.FaultRefusal(); err != nil {
		return nil, err
	}
	text, abbreviations := goal.Text, goal.Abbreviations
	if goal.Entry != "" {
		// The goal is a registered member's statement, as its author
		// stated it — the text its constructor parses, under the
		// member's own abbreviations.
		if text != "" || len(abbreviations) > 0 {
			return nil, fmt.Errorf("a goal given as 'entry' takes its text and abbreviations from the member; drop 'text' and 'abbreviations'")
		}
		entry, ok := registry.ByName(goal.Entry)
		if !ok {
			return nil, fmt.Errorf("add-goal: no registry member is named %q", goal.Entry)
		}
		if entry.Build.Headline == "" {
			return nil, fmt.Errorf("add-goal: %s states its statement through no constructor text; add its statement_typed as 'text'", goal.Entry)
		}
		text, abbreviations = entry.Build.Headline, entry.Abbreviations()
	}
	if text == "" {
		return nil, fmt.Errorf("goal must set 'text' (or 'entry')")
	}
	// The statement door (engine.StatementDoorScope): strict over the
	// corpus's registered constants, under the session's family — which
	// binds the implicit structure arguments its texts may leave
	// unspelled (ext/dsl/implicit.go), declares the domain an
	// unanchored `&` embeds into and declares the chapter's
	// abbreviations — and under the goal's own abbreviations, written
	// over its leading binders: a text goal's are read under the
	// chapter's (a name the chapter declares is refused — one name, one
	// meaning), and a member's come with the chapter's already in them.
	// A served `statement_typed` is checked against this same scope.
	scope := s.StatementDoorScope()
	table, err := dsl.ParseAbbreviations(abbreviations)
	if goal.Entry == "" {
		table, err = scope.Abbreviations.Extend(abbreviations)
	}
	if err != nil {
		return nil, fmt.Errorf("add-goal: %v", err)
	}
	scope.Abbreviations = table
	scope.AbbreviationBinders = map[string]bool{}
	for _, name := range dsl.LeadingBinderNames(text) {
		scope.AbbreviationBinders[name] = true
	}
	res := dsl.ParsePropTextAtDoor(text, scope)
	if len(res.Errors) > 0 {
		return nil, fmt.Errorf("parse goal text: %s", res.Errors[0].Message)
	}
	if refusal := closedGoalRefusal(res.Prop); refusal != "" {
		return nil, fmt.Errorf("add-goal: %s", refusal)
	}
	if !goal.AllowDuplicate {
		if k := s.ProvedSectionStating(res.Prop); k >= 0 {
			return nil, fmt.Errorf("add-goal: section %d already states this goal and is proved, so a new section "+
				"would close on it at its first step and prove nothing of its own. To re-prove the statement "+
				"cleanly, `restore` to a checkpoint before section %d (list-checkpoints) and prove in place; "+
				"to add the duplicate anyway, set goal.allow_duplicate:true", k, k)
		}
	}
	goalID, err := s.AddGoalWith(res.Prop, table)
	if err != nil {
		return nil, fmt.Errorf("add-goal: %v", err)
	}
	return map[string]any{"goal_id": goalID}, nil
}

// closedGoalRefusal is why the add-goal door refuses a parsed goal, ""
// when it does not: a goal with hypotheses left of ⊢ — a section states
// a closed theorem, as the section and statement doors require — named
// with its closed spelling.
func closedGoalRefusal(p core.Prop) string {
	if p.NumHyps() == 0 {
		return ""
	}
	return "the goal has hypotheses left of ⊢, and a goal states a closed theorem — ∀-bind its " +
		"variables and ⇒ its premises: " + proof.ClosedSpelling(p)
}

func rpcInspect(ctx context.Context, body []byte) (any, error) {
	// Accept both the legacy {session_id} shape and the new
	// {session_id, goal_id} shape. Treat missing goal_id as "engine picks
	// the focused goal if there's exactly one open" — same rule as
	// Inspect / Retrieve / Probe.
	var in InspectInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	res, err := eng.Inspect(ctx, in.SessionID, &engine.InspectRequest{GoalID: in.GoalID, BudgetMs: in.BudgetMs})
	if err != nil {
		return nil, err
	}
	type goalOut struct {
		ID        string `json:"id"`
		Statement string `json:"statement"`
		// StatementTyped is the parse-faithful rendering (binder types +
		// free-var declaration prefix); present only when the round-trip
		// closes — paste into `add-goal {text}` verbatim. The plain
		// Statement display does NOT round-trip.
		StatementTyped string    `json:"statement_typed,omitempty"`
		Hypotheses     []hypView `json:"hypotheses,omitempty"`
		Depth          int       `json:"depth"`
	}
	type factOut struct {
		Kind        string            `json:"kind"`
		Params      map[string]string `json:"params,omitempty"`
		Description string            `json:"description,omitempty"`
		// Unverified: the fact's probe was cut off at its budget
		// (engine.StructuralFact.Unverified).
		Unverified string `json:"unverified,omitempty"`
	}
	type out struct {
		Goals           []goalOut                  `json:"goals"`
		NumOpen         int                        `json:"num_open"`
		Complete        bool                       `json:"complete"`
		FocusedGoalID   string                     `json:"focused_goal_id,omitempty"`
		StructuralFacts []factOut                  `json:"structural_facts,omitempty"`
		Truncated       bool                       `json:"truncated,omitempty"`
		ClosedSubtrees  []engine.ClosedSubtreeView `json:"closed_subtrees,omitempty"`
	}
	o := out{
		NumOpen:       res.NumOpen,
		Complete:      res.Complete,
		FocusedGoalID: res.FocusedGoalID,
		Truncated:     res.Truncated,
		// Forward the engine's citable closed sub-derivations verbatim
		// (all-plain fields — JSON-safe).
		ClosedSubtrees: res.ClosedSubtrees,
	}
	for _, g := range res.Goals {
		typed, _ := res.Spelling.Typed(g.Statement)
		o.Goals = append(o.Goals, goalOut{
			ID:             g.ID,
			Statement:      res.Spelling.Prop(g.Statement),
			StatementTyped: typed,
			Hypotheses:     indexedHyps(g.Hypotheses, res.Spelling),
			Depth:          g.Depth,
		})
	}
	for _, f := range res.StructuralFacts {
		o.StructuralFacts = append(o.StructuralFacts, factOut{
			Kind:        f.Kind,
			Params:      f.Params,
			Description: f.Description,
			Unverified:  f.Unverified,
		})
	}
	return o, nil
}

type stateGoalOut struct {
	ID        string `json:"id"`
	Statement string `json:"statement"`
	// StatementTyped: parse-faithful form (see rpcInspect's goalOut).
	StatementTyped string    `json:"statement_typed,omitempty"`
	Hypotheses     []hypView `json:"hypotheses,omitempty"`
	Depth          int       `json:"depth"`
}

type stateOut struct {
	Goals    []stateGoalOut `json:"goals"`
	NumOpen  int            `json:"num_open"`
	Complete bool           `json:"complete"`
}

// stateViewToJSON converts a StateView (which contains core.Prop interfaces that
// can't round-trip through JSON) into a plain JSON-friendly struct.
func stateViewToJSON(sv *engine.StateView) *stateOut {
	if sv == nil {
		return nil
	}
	out := &stateOut{NumOpen: sv.NumOpen, Complete: sv.Complete}
	for _, g := range sv.Goals {
		typed, _ := sv.Spelling.Typed(g.Statement)
		out.Goals = append(out.Goals, stateGoalOut{
			ID:             g.ID,
			Statement:      sv.Spelling.Prop(g.Statement),
			StatementTyped: typed,
			Hypotheses:     indexedHyps(g.Hypotheses, sv.Spelling),
			Depth:          g.Depth,
		})
	}
	return out
}

// hypView pairs a hypothesis with its 0-based index in the goal's
// canonically-sorted hyp list — the index `instantiate`/`subst`/`rw`/`clear`
// consume. Surfacing it (in apply-state goals and inspect goals) lets the
// agent target a hyp without counting it off the pretty-printed `statement`,
// which is error-prone and goes stale after any hyp-adding tactic re-sorts
// the list. The term is spelled through the session's output door
// (engine.Spelling), like the statement.
type hypView struct {
	Index int    `json:"index"`
	Term  string `json:"term"`
}

// indexedHyps builds the hypView list for a goal's hyps. Returns nil for a
// hyp-free goal so the JSON `hypotheses` field is omitted.
//
// Hyp display uses PrintTermWithPolyBinders rather than PrintTerm: when a
// hyp's ∀/∃/∃!/λ binder carries a polymorphic type (one containing any
// VarType), the printed form is `∀f:((var:A, var:B) → var:B). …` instead of
// the type-erased `∀f. …`. Concrete binders (num/bool/…) print exactly as
// PrintTerm — no noise on the common case. The motivation is a recurring
// failure mode where an `instantiate` peels a non-polymorphic outer binder
// from a polymorphic ∀-hyp and the residual hyp still carries a polymorphic
// binder; without the annotation, the next `instantiate` collides with a type
// the agent had no way to see.
func indexedHyps(hyps []core.Term, door *engine.Spelling) []hypView {
	if len(hyps) == 0 {
		return nil
	}
	out := make([]hypView, len(hyps))
	for i, h := range hyps {
		out[i] = hypView{Index: i, Term: door.Hyp(h)}
	}
	return out
}

// stepResultToJSON converts a StepResult to a JSON-friendly map, replacing
// the StateView with its serializable form.
//
// `effect` and `produced` are the response's DISPOSITION — what the apply
// did to the focused goal, not merely that it succeeded. Without them a
// lemma that CLOSES reads identically to a lemma that INSTALLS a wide-∀
// hyp (both `success: true` + an auto_matched entry) unless the agent
// hand-diffs state.goals against new_hyps; a trans-created branch closed
// by auto-match looks like a branch that never existed; a cite
// discharging two obligations looks like one tactic call.
// With the fields surfaced: rewrite = `conclusion_changed: true`, install
// = `hyps_added: 1`, close = `effect: "close"` — read the disposition,
// not the success flag.
func stepResultToJSON(res *engine.StepResult) map[string]any {
	out := map[string]any{
		"success": res.Success,
	}
	if res.State != nil {
		out["state"] = stateViewToJSON(res.State)
	}
	if res.PlanRef != "" {
		out["plan_ref"] = res.PlanRef
	}
	if res.Effect != "" {
		out["effect"] = res.Effect
	}
	if len(res.Produced) > 0 {
		out["produced"] = res.Produced
	}
	if len(res.AutoMatched) > 0 {
		out["auto_matched"] = res.AutoMatched
	}
	if len(res.NewHyps) > 0 {
		out["new_hyps"] = res.NewHyps
	}
	if len(res.Diagnostics) > 0 {
		out["diagnostics"] = res.Diagnostics
	}
	if res.EngineFault != nil {
		out["engine_fault"] = res.EngineFault
	}
	return out
}

func rpcApply(ctx context.Context, body []byte) (any, error) {
	var in ApplyInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	tactic, err := tacticReqFromInput(in.Tactic)
	if err != nil {
		return nil, err
	}
	res, err := eng.ApplyStep(ctx, in.SessionID, &engine.ApplyStepRequest{
		GoalID:   in.GoalID,
		Tactic:   tactic,
		BudgetMs: in.BudgetMs,
	})
	if err != nil {
		return nil, err
	}
	return stepResultToJSON(res), nil
}

func rpcRetrieve(ctx context.Context, body []byte) (*engine.RetrieveResult, error) {
	var in RetrieveInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	res, err := eng.Retrieve(ctx, in.SessionID, &engine.RetrieveRequest{
		Mode:        in.Mode,
		GoalID:      in.GoalID,
		BudgetMs:    in.BudgetMs,
		Consts:      in.Consts,
		NamePattern: in.NamePattern,
		RelatedTo:   in.RelatedTo,
		MaxPerGroup: in.MaxPerGroup,
	})
	if err != nil {
		return nil, err
	}
	// The engine's result is the wire shape (its JSON tags are the
	// contract); nothing is re-spelled here.
	return res, nil
}

func rpcProbe(ctx context.Context, body []byte) (any, error) {
	var in ProbeInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	tactic, err := tacticReqFromInput(in.Tactic)
	if err != nil {
		return nil, err
	}
	res, err := eng.Probe(ctx, in.SessionID, &engine.ProbeRequest{
		GoalID:   in.GoalID,
		Tactic:   tactic,
		BudgetMs: in.BudgetMs,
	})
	if err != nil {
		return nil, err
	}
	if res == nil {
		return nil, fmt.Errorf("probe returned nil result")
	}
	// The engine's ProbeResult is the wire reply as it stands: its JSON
	// tags are the probe row's fields (outcome, reason, effect, subgoals
	// with their changes, auto_matched, diagnostic, by_closer, records,
	// elapsed_ms), and a copy reshaped here would drop each field the
	// engine adds.
	return res, nil
}

func rpcBatchApply(ctx context.Context, body []byte) (any, error) {
	var in BatchApplyInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	tactics := make([]engine.TacticReq, len(in.Tactics))
	for i, t := range in.Tactics {
		var err error
		tactics[i], err = tacticReqFromInput(t)
		if err != nil {
			return nil, fmt.Errorf("tactic %d: %w", i, err)
		}
	}
	mode := engine.FirstSuccess
	if in.Mode == "compare_all" {
		mode = engine.CompareAll
	}
	res, err := eng.BatchApply(ctx, in.SessionID, &engine.BatchApplyRequest{
		GoalID:  in.GoalID,
		Tactics: tactics,
		Mode:    mode,
	})
	if err != nil {
		return nil, err
	}
	// Convert results to JSON-friendly format (StateView contains core.Prop).
	type resultOut struct {
		Success     bool                `json:"success"`
		State       *stateOut           `json:"state,omitempty"`
		PlanRef     string              `json:"plan_ref,omitempty"`
		Diagnostics []engine.Diagnostic `json:"diagnostics,omitempty"`
		EngineFault *engine.EngineFault `json:"engine_fault,omitempty"`
	}
	results := make([]resultOut, len(res.Results))
	for i, r := range res.Results {
		results[i] = resultOut{
			Success:     r.Success,
			PlanRef:     r.PlanRef,
			EngineFault: r.EngineFault,
		}
		if r.State != nil {
			results[i].State = stateViewToJSON(r.State)
		}
		if len(r.Diagnostics) > 0 {
			results[i].Diagnostics = r.Diagnostics
		}
	}
	return map[string]any{
		"results":      results,
		"winner_index": res.WinnerIndex,
	}, nil
}

func rpcCheckpoint(ctx context.Context, body []byte) (any, error) {
	var in CheckpointInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	cpID, err := eng.Checkpoint(ctx, in.SessionID, in.Name)
	if err != nil {
		return nil, err
	}
	return map[string]string{"checkpoint_id": cpID}, nil
}

func rpcRestore(ctx context.Context, body []byte) (any, error) {
	var in RestoreInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	if err := eng.Restore(ctx, in.SessionID, in.CheckpointID); err != nil {
		return nil, err
	}
	return map[string]string{"status": "restored"}, nil
}

func rpcListCheckpoints(ctx context.Context, body []byte) (any, error) {
	var in SessionIDInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	cps, err := eng.ListCheckpoints(ctx, in.SessionID)
	if err != nil {
		return nil, err
	}
	return map[string]any{"checkpoints": cps}, nil
}

func rpcCommitPlan(ctx context.Context, body []byte) (any, error) {
	var in CommitPlanInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	res, err := eng.CommitPlan(ctx, in.SessionID, &engine.CommitPlanRequest{
		GoalID:  in.GoalID,
		PlanRef: in.PlanRef,
	})
	if err != nil {
		return nil, err
	}
	return stepResultToJSON(res), nil
}

func rpcCheck(ctx context.Context, body []byte) (any, error) {
	input := string(body)
	result := engine.Parse(input)
	if len(result.Errors) > 0 {
		return map[string]any{
			"result":           "unknown",
			"parse_errors":     result.Errors,
			"normalized_input": result.NormalizedInput,
			"warnings":         result.Warnings,
		}, nil
	}
	res, err := eng.CheckDerivation(ctx, &engine.CheckDerivationRequest{
		Conclusion: result.Prop,
		TimeoutMs:  5000,
	})
	if err != nil {
		return nil, err
	}
	out := map[string]any{"result": res.Result}
	if res.CapabilityHint != nil {
		out["capability_hint"] = res.CapabilityHint
	}
	if len(res.Diagnostics) > 0 {
		out["diagnostics"] = res.Diagnostics
	}
	if len(result.Warnings) > 0 {
		out["warnings"] = result.Warnings
	}
	if result.NormalizedInput != input {
		out["normalized_input"] = result.NormalizedInput
	}
	return out, nil
}

func rpcCheckDerivation(ctx context.Context, body []byte) (*engine.CheckDerivationResult, error) {
	var in CheckDerivationInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	premises := make([]core.Prop, len(in.Premises))
	for i, p := range in.Premises {
		var err error
		premises[i], err = propFromInput(p)
		if err != nil {
			return nil, fmt.Errorf("premise %d: %w", i, err)
		}
	}
	conclusion, err := propFromInput(in.Conclusion)
	if err != nil {
		return nil, fmt.Errorf("conclusion: %w", err)
	}
	return eng.CheckDerivation(ctx, &engine.CheckDerivationRequest{
		Premises:   premises,
		Conclusion: conclusion,
		TimeoutMs:  in.TimeoutMs,
	})
}

func rpcCheckConsistency(ctx context.Context, body []byte) (*engine.CheckConsistencyResult, error) {
	var in CheckConsistencyInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	stmts := make([]core.Prop, len(in.Statements))
	for i, s := range in.Statements {
		var err error
		stmts[i], err = propFromInput(s)
		if err != nil {
			return nil, fmt.Errorf("statement %d: %w", i, err)
		}
	}
	return eng.CheckConsistency(ctx, &engine.CheckConsistencyRequest{
		Statements: stmts,
		TimeoutMs:  in.TimeoutMs,
	})
}

// ParsePropInput is the RPC input for parse-prop.
//
// Bare mode: only `text` is set — the input parses scope-blind through
// dsl.ParsePropText, exactly as it did before session scoping was
// added. Suitable for standalone previews / lint checks of text DSL.
//
// Scoped mode: `session_id` (and optionally `goal_id`) is set — the
// input parses against the resolved goal's free-var types + goal-local
// constants + registered-const fallback, i.e. the same scope
// `assert.claim.text` / `lemma.lemma.text` will see at apply time.
// Suitable for previewing a claim in the middle of a proof session
// without paying the full apply round-trip. `goal_id` is optional and
// falls back to the session's focused goal when omitted (same rule
// Inspect / Retrieve / Probe use).
type ParsePropInput struct {
	Text      string `json:"text"`
	SessionID string `json:"session_id,omitempty"`
	GoalID    string `json:"goal_id,omitempty"`
}

// rpcParseProp is the authoring aid for text-DSL propositions. It
// parses a proposition and returns the engine's interpretation — the
// normalized input, the printed statement, and any warnings or errors —
// so agents can iterate parse failures without paying the ~5-30s
// apply round-trip.
//
// Bare mode (no session_id) reads at the add-goal statement door of a
// session bound to no family, so a previewed acceptance is the door's.
//
// Scoped mode (session_id set) resolves the goal and parses against
// its scope, so agent-authored `assert.claim_text` / `lemma.lemma_text`
// previews using session free vars produced by `strip_quant` or
// goal-local constants resolve without an explicit `n_0:num ⊢ …` prefix.
//
// A session/goal lookup failure returns `{ok:false, errors:[…]}` rather
// than an RPC-level error, so agents distinguish "session gone" from
// "parse failed" without exception handling.
//
// It does NOT return proto_hex — JSON envelopes carry text and keys,
// not encoded kernel bytes.
func rpcParseProp(body []byte) (any, error) {
	var in ParsePropInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	if in.Text == "" {
		return nil, fmt.Errorf("parse-prop requires 'text'")
	}
	var res dsl.ParseResult
	var door *engine.Spelling // nil: the session-less preview spells under no family
	if in.SessionID == "" {
		// The session-less preview reads at the add-goal statement
		// door of a session bound to no family, so previewed
		// acceptance is the door's.
		res = dsl.ParsePropTextAtDoor(in.Text, engine.StatementDoorScope(nil))
	} else {
		var err error
		res, err = eng.ParsePropInGoalScope(in.SessionID, in.GoalID, in.Text)
		if err == nil {
			door, err = eng.SessionSpelling(in.SessionID)
		}
		if err != nil {
			return map[string]any{
				"ok": false,
				"errors": []map[string]any{
					{"message": err.Error()},
				},
			}, nil
		}
	}
	out := map[string]any{
		"normalized_input": res.NormalizedInput,
	}
	if len(res.Warnings) > 0 {
		out["warnings"] = res.Warnings
	}
	if len(res.Errors) > 0 {
		out["ok"] = false
		out["errors"] = res.Errors
		return out, nil
	}
	if in.SessionID == "" {
		// The add-goal door's own refusal, so previewed acceptance stays
		// the door's.
		if refusal := closedGoalRefusal(res.Prop); refusal != "" {
			out["ok"] = false
			out["errors"] = []map[string]any{{"message": refusal}}
			return out, nil
		}
	}
	out["ok"] = true
	out["statement_text"] = door.Prop(res.Prop)
	return out, nil
}

// ParseTermInput is the RPC input for parse-term. Unlike parse-prop,
// `session_id` is REQUIRED — a bare term without goal scope has no
// type context for free vars, and there is no useful "scope-blind"
// preview mode for terms. `goal_id` is optional (falls back to the
// focused goal). `expected_type`, when non-empty, is parsed via
// dsl.ParseTypeText and passed as the type constraint on the parsed
// term — e.g. `"bool"` when previewing a `case_split` const.
type ParseTermInput struct {
	Text         string `json:"text"`
	SessionID    string `json:"session_id"`
	GoalID       string `json:"goal_id,omitempty"`
	ExpectedType string `json:"expected_type,omitempty"`
}

// rpcParseTerm is the authoring aid for term-DSL strings used as
// tactic parameters (`witness`, `trans`, `instantiate`, `case_split`,
// `assert.witness`). It parses `text` against the session goal's scope
// — the same seed resolveTermWithFallback uses at apply time — and
// returns the printed term, normalized input, warnings, and errors.
//
// Preview intent: iterate first-pass parse failures cheaply. This does
// NOT run resolveTermWithFallback's subterm fast path (that is an
// application-time affordance, not a "does this text parse" signal),
// and does NOT do the second-pass registered-const-seeding rerun — first-
// pass errors are the signal the agent wants.
//
// Session/goal lookup failure returns `{ok:false, errors:[…]}` so
// agents can distinguish it from a parse failure.
func rpcParseTerm(body []byte) (any, error) {
	var in ParseTermInput
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	if in.Text == "" {
		return nil, fmt.Errorf("parse-term requires 'text'")
	}
	if in.SessionID == "" {
		return nil, fmt.Errorf("parse-term requires 'session_id' (a bare term has no type scope)")
	}
	var expected core.HolType
	if in.ExpectedType != "" {
		t, err := dsl.ParseTypeText(in.ExpectedType)
		if err != nil {
			return nil, fmt.Errorf("parse expected_type %q: %w", in.ExpectedType, err)
		}
		expected = t
	}
	res, err := eng.ParseTermInGoalScope(in.SessionID, in.GoalID, in.Text, expected)
	if err != nil {
		return map[string]any{
			"ok": false,
			"errors": []map[string]any{
				{"message": err.Error()},
			},
		}, nil
	}
	out := map[string]any{
		"normalized_input": res.NormalizedInput,
	}
	if len(res.Warnings) > 0 {
		out["warnings"] = res.Warnings
	}
	if len(res.Errors) > 0 {
		out["ok"] = false
		out["errors"] = res.Errors
		return out, nil
	}
	out["ok"] = true
	door, err := eng.SessionSpelling(in.SessionID)
	if err != nil {
		return nil, err
	}
	out["term_text"] = door.Term(res.Term)
	return out, nil
}

// rpcDefine is the `define` RPC — the definition move. The
// payload variants live on engine.DefineRequest; v1 serves the
// `recursive:` payload's direct (single non-recursive equation) shape.
func rpcDefine(body []byte) (*engine.DefineResult, error) {
	if eng == nil {
		return nil, fmt.Errorf("define requires an initialized engine")
	}
	var in struct {
		// Cmd is re-parsed here like every RPC body (see ApplyInput).
		Cmd       string                  `json:"cmd,omitempty"`
		SessionID string                  `json:"session_id"`
		Recursive *engine.DefineRecursive `json:"recursive,omitempty"`
		Data      *engine.DefineData      `json:"data,omitempty"`
		Spec      *engine.DefineSpec      `json:"spec,omitempty"`
		Typedef   *engine.DefineTypedef   `json:"typedef,omitempty"`
		Inductive *engine.DefineInductive `json:"inductive,omitempty"`
		Quotient  *engine.DefineQuotient  `json:"quotient,omitempty"`
	}
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	return eng.Define(&engine.DefineRequest{
		SessionID: in.SessionID,
		Recursive: in.Recursive,
		Data:      in.Data,
		Spec:      in.Spec,
		Typedef:   in.Typedef,
		Inductive: in.Inductive,
		Quotient:  in.Quotient,
	})
}

// ---------------------------------------------------------------------------
// Help text
// ---------------------------------------------------------------------------

var commandHelp = map[string]string{
	"check": `Verify a proposition (text or JSON on stdin).

  echo 'p => p' | xugo check                        # tautology
  echo 'p, p => q ⊢ q' | xugo check                # modus ponens
  echo 'P:A->bool ⊢ (forall x:A. P(x)) => P(y)' | xugo check

Output: {"result":"valid"} or {"result":"invalid","diagnostics":[...]}
Result is "valid", "invalid", or "unknown" (exceeds engine capability).
Text format: hyps ⊢ conclusion. Connectives: =>, <=>, /\, \/, ~, forall, exists.`,

	"check-derivation": `Check if conclusion follows from premises (JSON on stdin).

  echo '{"premises":[...], "conclusion":{...}}' | xugo check-derivation

Each prop slot is a PropInput object:
  {"text": "<text-DSL proposition>"}     # parsed and typechecked

Output: {"result":"valid"|"invalid"|"unknown", "diagnostics":[...]}`,

	"check-consistency": `Check if statements are mutually consistent (JSON on stdin).

  echo '{"statements":[...]}' | xugo check-consistency

Each statement is a PropInput object:
  {"text": "<text-DSL proposition>"}     # parsed and typechecked

Output: {"result":"consistent"|"inconsistent"|"unknown", "conflict_subset":[...]}`,

	"parse-prop": `Preview how the engine parses a text-DSL proposition (debug helper).

  echo '{"text":"P:A->bool ⊢ forall x:A. P(x) => P(x)"}' | xugo parse-prop

Output on success:
  {"ok": true,
   "normalized_input": "P:A→bool ⊢ ∀x:A. P(x) ⇒ P(x)",
   "statement_text": "...",
   "warnings": [...]}

Output on failure:
  {"ok": false,
   "normalized_input": "...",
   "errors": [{"code":"...","message":"...","position":N,...}]}

Use this to lint malformed input or to see what symbol normalization
the engine applies before committing the same text through check /
add-goal / lemma. The output does NOT contain proto_hex — JSON
envelopes carry text and keys, not encoded kernel bytes.`,

	"query": `Ask the corpus as a whole (library/index). To read the corpus in a
browser instead, xugo browse.

  xugo query overview                           the panorama: totals and one line per family
                                                  (gloss, height, counts) — read first
  xugo query family real/real_sequences         a chapter: gloss, imports, members with statements
                                                  and their glosses; the short name alone
                                                  (real_sequences) names it too while no other
                                                  family has it
  xugo query member <member>                    one member in full: statement (the chapter's
                                                  text) and statement_typed (the text that reads
                                                  with nothing declared, paste-ready), kind, shape,
                                                  deps, dependents, card, note, cards, constants
                                                  (and by role: conclusion_constants,
                                                  hypothesis_constants), source; a card's backing:
                                                  theorem_deps, note_names resolved,
                                                  note_names_not_cited; read off the chapter file:
                                                  gloss, the doc comment above it, and outline, its
                                                  proof's narration step by step (verb, label,
                                                  claim, cites, uses, depth, line)
  xugo query dossier <member>                   the member in the round: what it spells, its
                                                  place in the chapter, its plan, deps and
                                                  dependents with their statements, how to cite it
  xugo query deps <member> [--depth N]          what it cites, level by level (--depth 0: all)
  xugo query dependents <member> [--depth N]    what cites it
  xugo query family|member|dossier|deps|dependents <name> <name> …
                                                two or more names in one answer, the corpus read
                                                  once for all of them: each one's answer, in the
                                                  order given, under families, members, dossiers
                                                  or neighborhoods, and each name nothing carries
                                                  under unknown with the reason
  xugo query member|dossier|deps|dependents AddAssoc
                                                a bare name, the name after the family's: every
                                                  member under it, family by family, answered as
                                                  a list however many it holds; between and graph
                                                  proof take one a single member has
  xugo query between <member> <member>          a shortest citation chain, either direction
  xugo query definition nat_gcd                 who defines a constant, who mentions it, who
                                                  establishes it (concluded_by) and who asks for
                                                  it (assumed_by), each by stratum, who cites the
                                                  definition
  xugo query definition nat_gcd int_gcd int_lcm several constants in one answer: each defined
                                                  one's view under definitions, each other name
                                                  under undefined with the reason
  xugo query definitions                        every minted constant and type
  xugo query cards [<family> …]                 every card — a member stated without a proof —
                                                  leaves first, with who stands on it and its
                                                  statement_typed, paste-ready for add-goal;
                                                  with families named, theirs alone
  xugo query graph <scope>                      a graph laid out: its nodes and edges with
                                                  their coordinates; the pages drawing the
                                                  graphs are xugo browse's
      families                                    every family on the row of its height, the
                                                  foundations at the foot, and its imports,
                                                  transitively reduced
      proof <member>                              the results the member's proof stands on, the
                                                  member at the right edge: the theorems of its
                                                  chapter, every card it stands on, for a card
                                                  everything it cites, and of each other family
                                                  the theorems that gather a part of their
                                                  chapter; of the
                                                  families the whole neighbourhood stands on, the
                                                  theorems cited directly, apart; at three grains,
                                                  compact, standard and deep; a door call
                                                  registering several members is one node; a
                                                  definition is drawn as what it is built from
                                                  and who uses it

  A <member> is an index id (real/real_sequences.CauchyConverges), a registered name
  (real_sequences.CauchyConverges) or an own key. --root DIR names library/proofs when the
  working directory is not under the module.

RPC (serve mode): {"cmd":"query","what":"deps","member":"…","depth":2}; the fields are
  what, family, families, member, members, from, to, const, consts, depth, scope, root —
  a field a question does not take is refused by name. A graph names its scope:
  {"cmd":"query","what":"graph","scope":"proof","member":"…"}.`,

	"browse": `Serve the corpus to read in a browser (library/visualize), or write
it as a site: the family graph, the graph of any member, and a search of
the theorems.

  xugo browse [--port N] [--timeout D] [--root DIR]
  xugo browse --write DIR [--root DIR]

It reads the corpus (a few seconds), prints the address as one line of JSON
— {"status":"listening","url":"http://127.0.0.1:8717/",…} — and serves on
this machine alone until it is interrupted.

  /                        every family on the row of its height; a family clicked
                             shows what its README opens with and lists its
                             definitions, theorems and cards, each a link
  /proof.html?m=<member>   the results the member's proof stands on, or for a
                             definition what it is built from and who uses it (query
                             graph proof), drawn when the page is asked for; a name in
                             the sidebar, or a node clicked twice, opens that member's
                             page
  /data/…                  what the two pages paint: the family graph's layout, a
                             file for each family saying what is said of its members,
                             once, and a layout for each member's page. The search
                             field of both pages searches the families' files.

  --port N                 the port (8717; 0 has the system pick one)
  --timeout D              end when no page has been asked for that long (5m, 1h);
                             without it the command serves until interrupted
  --root DIR               library/proofs, when the working directory is not under
                             the module
  --write DIR              serve nothing: write the same site into DIR, an empty
                             directory or a new one, every member's page with it,
                             and print {"status":"written","dir":…,"files":…,"bytes":…}

Serving writes nothing to disk: a page is of the corpus this binary linked. A
site written is the same files, with links that hold under any address, to
publish as they are.`,

	"session-create": `Create a new proof session.

  xugo session-create
  Output: {"id":"<session_id>", "created_at":"..."}

RPC extras (serve mode):
  {"family":"iterate/real/real_sum"}                bind the session to a chapter: its
    registered definitions install as use rules (the bare ` + "`simp`" + ` set); the response
    carries {"binding":{family, imports, installed:[{entry, shape, rule}]}}.
  {"family":"…","imports":["words/machine_word"]}  also install the imported families' definitions.
  {"resume":"<session id>"}                    rebuild a persisted session by replaying its
    lineage (the lineage carries the family binding).`,

	"defer": `RPC (serve mode) — make an open leaf a CARD (a member of the
session's family stated without a proof) and close the leaf by citing it.

Input:  {"session_id": "...", "goal_id": "s1_g...", "name": "MulOne", "note": "why it is a member, what its proof must establish",
         "deps": ["<family>.<Name>", ...]}
Output: {"status": "deferred" | "proved" | "card", "stated_by": [names], "open_elsewhere": [lineage ids],
         "card": {key, name, entry, note, deps, statement, statement_typed, section},
         "section": {section, statement, proved, cards: [cards]}, "state": {...}}

The leaf's conclusion, ∀-closed over its free variables, is the card;
its normalized key is the card's identity; its registered name is
<family>.<name> — the spelling every later cite uses. The session
serves the card as the axiom ⊢ <statement>, the leaf closes by the
lemma move naming it (recorded like any cite), and emit-section
renders the card as a family.Add entry built by family.Card beside the
member, whose proof cites it. deps (optional) are the card's Deps: the
members its proof will cite, each a registered name as a lemma cite
spells it — a registry entry, proved or a card, or a card this session
minted — rendered as the entry's Deps between Key and Build; omitted,
the card stands on nothing. Replay serves a landed card
as its axiom until a proof lands in place of family.Card; nothing
downstream changes then. "proved": a proved entry already states the
card — nothing was minted; cite the name in stated_by. "card": a
landed card states it — cite that one. Refused, with the fix named: a
session bound to no family; a name that is not an exported Go
identifier; an empty note; a leaf mentioning section-local variables
(assert the ∀-closed statement first, then defer its claim leaf); a
card that is the section's own conclusion (the leaf IS the theorem);
a name already minted in this session for another statement; a dep
that is empty, names no registered entry and no card of the session,
names an entry the family's package cannot name in Go, is the card
itself, or stands on the card. The same lemma deferred twice is one
card, under its first name, standing on what either defer named.
Recorded in the lineage; resume re-mints the card with its deps and
the recorded cite re-closes the leaf.`,
	"registry-fingerprint": `The proof registry this binary LINKED: the entry count and a SHA-256
over every registered "name<TAB>key" line in name order.

CLI:  xugo registry-fingerprint
RPC:  {"cmd": "registry-fingerprint"}     (also printed on the serve's startup line)

Output: {"entries": N, "fingerprint": "<hex>"}

A serve links the registry at BUILD time, so a member landed after the
build is a name it cannot cite ("names no proof-registry entry"). Build
the binary, compare its fingerprint with the running serve's: equal
means the serve cites exactly what the tree registers; unequal means
rebuild — and when agents are live on the old serve, start a second
one on its own port file rather than killing the first.`,
	"faults": `The engine faults on record: each a panic that marked a defect of the
engine, or a run that ended well past its deadline, written down by the
engine with the request that met it (<data-dir>/faults, one file per
fault). Reads the store; needs no serve.

CLI:  xugo --data-dir DIR faults [--all]
      xugo --data-dir DIR faults show ID
      xugo --data-dir DIR faults ack ID --note "what was done about it"

faults lists the open faults — the ones no one has acknowledged — newest
first, and exits 1 while there is one, 0 when there is none; --all lists
the acknowledged ones too. A serve whose process ended leaves its crash
report and the requests it had not answered in the store, whatever their
command (a tactic run from its start, any other command once it has run
2 s); the listing turns them into a record first.

Output: {"open": N, "acknowledged": M,
         "faults": [{id, at, command, session, goal_id, tactic, site, panic, goroutine, late,
                     in_flight: [{command, session, goal_id, tactic} of each request a dead
                                 serve had not answered],
                     overrun_ms: <how late a run ended past its deadline; such a record
                                  locks no session>,
                     record: <the file>, ack: {at, note}}]}

show prints one record whole: the request body as /rpc received it, the
goal (its closed spelling for add-goal, its blob for a test), the tactic,
the stack. ack writes the acknowledgment into the record; a session the
fault had locked takes moves again from its next request.`,
	"cards": `The cards the session store (<data-dir>/sessions) knows of — members
stated without a proof, served as axioms until their proofs land:
the cards a lineage minted with defer, and the cards a lineage is
proving, its target stating one. The corpus's own cards, who stands on
each and the order to fill them in, are xugo query cards [<family> …].

CLI:  xugo --data-dir DIR cards [--lineage ID] [--key KEY]
RPC:  {"cmd": "cards", "lineage": "<id>"?, "key": "<key>"?}

Output: {"cards": [{key, name, entry, family, note, statement, statement_typed, landed,
                    parents: [{lineage, section, statement}], attacked_by: [{lineage, section}]}],
         "problems": [declarations this env cannot read]}

statement_typed: the card's parse-faithful spelling, paste-ready for
add-goal {text} (the brief hands the prover this, never the display
statement). landed: the card is a registry entry; otherwise parents
are the lineage sections that minted it, and it is emitted nowhere yet.
attacked_by: lineages whose target states the card — do not dispatch
it twice. By registered name. A card a proved entry states is no card
and is not listed. Filling a card is replacing its family.Card build
by a proof, in place: the entry keeps its name and key, nothing
downstream changes; a restated statement re-keys like any restatement.`,
	"dump-section": `RPC (serve mode) — preorder step+goal walk of one session
section's proof tree. Built for walking a section's proved interior
(invisible to inspect's open-goal view).

  {"session_id":"<id>","section":3}                 → nodes[{path,depth,step,statement,statement_typed,proved}]
  {"session_id":"<id>","section":3,"max_nodes":50}  → cap the walk (default 400; truncated flag set)

statement is display-only and does NOT round-trip through add-goal
(binder types + free-var declarations are dropped). statement_typed is
the parse-faithful rendering — paste it into add-goal {text} verbatim;
present only when the print→parse→α-key round-trip verifiably closes.
The same field appears on inspect's goals[] and apply's state.goals[].`,

	"add-goal": `Add a proof goal to a session.  JSON on stdin.

  echo '{"session_id":"<id>","goal":{"text":"p ⇒ p"}}' | xugo add-goal

The goal field is a PropInput holding "text": the statement, parsed in
the session's scope, becomes a new section. A session states only
constants the corpus defines: define a constant first (the session's
define door, or the chapter's family.Define / DefineType / DefineData /
DefineSpec).

"abbreviations" declares the names the text and the proof's texts
spell as «Name» — [{"name":"R","text":"restrict_ring(field_ring(L), …)"}, …],
in order, an entry spelling only the entries before it. The goal's
inspect, retrieve and emit then spell «R» where the term stands.
"entry" names a registry member instead of "text": the goal is the
member's statement as its author stated it, abbreviations included —
how a card is attacked.

  echo '{"session_id":"<id>","goal":{"entry":"projective_line_free_pair.FreeLinePairSplit"}}' | xugo add-goal`,

	"inspect": `Show open goals + structural facts about the focused goal.  JSON on stdin.

  echo '{"session_id":"<id>"}' | xugo inspect
  echo '{"session_id":"<id>","goal_id":"<gid>"}' | xugo inspect
  echo '{"session_id":"<id>","goal_id":"<gid>","budget_ms":5000}' | xugo inspect

When goal_id is omitted and exactly one goal is open, that goal is focused
automatically. structural_facts lists applicable parameterless moves and
parameterized moves (def_expand, induction, case_split). No score or priority
— ordering expresses position, not preference.

The probes that read a clock (arith, ring_nf, each direction of an rw) run
under a budget of their own: 1 s each, or budget_ms. A fact whose probe was
cut off carries "unverified", the reason: the move is neither verified nor
ruled out, and every other fact stands.`,

	"retrieve": `Look up lemma candidates in the corpus, grouped by strategy.  JSON on stdin.

Modes (mode is required):
  echo '{"session_id":"<id>","mode":"goal","goal_id":"<gid>","budget_ms":3000}' | xugo retrieve
  echo '{"mode":"consts","consts":["dot","vec_add"]}' | xugo retrieve
  echo '{"mode":"name_pattern","name_pattern":"dot."}' | xugo retrieve
  echo '{"mode":"related_to","related_to":"dot.AddLeft"}' | xugo retrieve

Groups (matched_via "corpus"; "corpus_deps" / "corpus_dependents" for
related_to) list family members by registered name — {entry, family,
key, statement, match, witnesses, premises}. In goal mode a member is
listed when its statement IS the goal (match "exact") or when it
APPLIES by the apply rung's plan (match "apply": the witnesses the goal
pins, and each premise resident / stated by an entry / a card / open —
the open ones are yours to supply before the by).

related_to takes an entry name or an entry's own key and answers from
the entries' dependencies (one hop each way).`,

	"probe": fmt.Sprintf(`Non-destructively try a tactic on a goal.  JSON on stdin.

  echo '{"session_id":"<id>","goal_id":"<gid>","tactic":{"type":"auto"},"budget_ms":200}' | xugo probe
  echo '{"session_id":"<id>","tactic":{"type":"lemma","lemma":{"key":"nat_order.LessEqRefl"}}}' | xugo probe

Outcome: success | fail | unknown(reason). Default budget %dms; the request
context deadline is always honored. Fail is strong for structural / lemma
tactics; auto/refute timeouts map to unknown(timeout).`, engine.ProbeDefaultBudgetMs),

	"apply": `Apply one tactic to a goal.  JSON on stdin.

  echo '{"session_id":"<id>","goal_id":"<gid>","tactic":{"type":"auto"}}' | xugo apply
  Tactic types: expand, refute, lemma, def_expand, known, case_split, induction, assert,
  auto, auto_with, by, simp_with, set_tac, arith, rewrite, split_conj, split_disj,
  strip_imp, strip_quant, simplify, denote, let.
  Lemma's "lemma" field is a PropInput — set "key" for a registry entry
  (preferred: its own key or registered name) or "text"
  for an ad-hoc lemma, or "key" with "read_at" for a structure law read at
  an instance (the Go Law.Read(instance)): a goal the reading states closes
  on the cite, any other has it installed as a hypothesis:
    {"type":"lemma","lemma":{"key":"nat_order.LessEqRefl"}}
    {"type":"lemma","lemma":{"text":"P ⇒ P"}}
    {"type":"lemma","lemma":{"key":"comm_ring.MulLeftZero","read_at":{"hyp_index":0}}}
  split_conj and def_expand take an optional "hyp_index": the conjunctive
  hypothesis split into its conjuncts (the Go a.Conjuncts), the constant
  opened in that hypothesis alone (the Go a.Unfolded). Without it,
  def_expand opens the constant in the goal and every resident hypothesis,
  renumbering them, as the Go Unfold does; the goal alone is simp_with by
  the definition entry:
    {"type":"split_conj","hyp_index":0}
    {"type":"def_expand","const":"real_converges_to","hyp_index":0}

` + "`by`" + ` is the math layer's premise-disciplined close (the By(...) a
proof spells), recorded as ONE composite ministep that emit
renders back 1:1: name the resident hyps (by_hyps — kept across the
clear-first, everything else cleared, optional witnesses) and the
lemma premises (with_lemmas — installed, optional term_specialize),
declare the shaping (by_shape:{"normalized":true} runs Basic between
installs and close), then ONE refutation — or the gated arith closer
with "arith":true (scope-gated; never taken silently, so no recorded
Arith() surprises on foundation targets). Close-or-fail.
    {"type":"by","by_hyps":[{"hyp_index":0},{"hyp_index":2,"terms":["a₀"]}],
     "with_lemmas":[{"key":"nat_arith.AddSym","term_specialize":{"n":"a₀"}}],
     "by_shape":{"normalized":true}}`,

	"batch-apply": `Try multiple tactics on a goal.  JSON on stdin.

  echo '{"session_id":"<id>","goal_id":"<gid>","tactics":[...],"mode":"first_success"}' | xugo batch-apply
  Modes: "first_success" (stop on first), "compare_all" (preview all, commit later).`,

	"checkpoint": `Save proof state snapshot.  JSON on stdin.

  echo '{"session_id":"<id>","name":"before_branch"}' | xugo checkpoint`,

	"restore": `Restore proof state from a checkpoint.  JSON on stdin.

  echo '{"session_id":"<id>","checkpoint_id":"<cpid>"}' | xugo restore`,

	"list-checkpoints": `List checkpoints stored in a session, sorted oldest first.  JSON on stdin.

  echo '{"session_id":"<id>"}' | xugo list-checkpoints

Response: {"checkpoints":[{"id","name","created_at","num_open_leaves","num_sections"}, ...]}.
Load-bearing for the proving loop's resume mode: a fresh agent inheriting a
prior session uses this to pick a restore point.`,

	"commit-plan": `Commit a deferred plan from compare_all mode.  JSON on stdin.

  echo '{"session_id":"<id>","goal_id":"<gid>","plan_ref":"<ref>"}' | xugo commit-plan`,
}

func printHelp(command string) {
	if command != "" {
		if h, ok := commandHelp[command]; ok {
			fmt.Fprintf(os.Stderr, "xugo %s\n\n%s\n", command, h)
			return
		}
		fmt.Fprintf(os.Stderr, "unknown command: %s\n\n", command)
	}

	fmt.Fprint(os.Stderr, `XuGo — a library of formal mathematics and the proof session it is written through

Usage: xugo [flags] <command> [command-flags]

Flags:
  --data-dir DIR       Where sessions persist: lineages under DIR/sessions, the CNF
                       certificates they record under DIR/cnf_cache, the records of
                       the engine faults they met under DIR/faults
  --trace-log PATH     Append operation traces to this file (or set XUGO_TRACE_LOG)
  --help, -h           Show this help

Corpus (read-only):
  query                The corpus as a whole: overview | family | member | dossier | deps |
                       dependents | between | definition | definitions | cards | axioms (library/index)

Session (stateful proof navigation):
  session-create       Create a new proof session
  add-goal             Add a proof goal to a session
  inspect              Show open goals + structural facts about the focused goal
  retrieve             Look up corpus members (modes: goal | consts | name_pattern | related_to)
  probe                Non-destructively try a tactic (success | fail | unknown)
  apply                Apply one action to a goal
  batch-apply          Try multiple actions (first_success or compare_all)
  checkpoint           Save proof state snapshot
  restore              Restore proof state from checkpoint
  commit-plan          Commit a deferred plan from compare_all
  cards                The cards — members stated without a proof — landed and in flight, leaves first
  faults               The engine faults on record under --data-dir; exits 1 while one is not
                       acknowledged (faults ack ID --note TEXT acknowledges; faults show ID prints one)
  registry-fingerprint The proof registry this binary linked (entry count + digest); the serve's
                       registry-fingerprint RPC answers the same pair; unequal means a stale serve

  serve                Serve the session commands as JSON over HTTP, for an agent to drive
                       (POST /rpc; --port, --port-file, --timeout)
  browse               Serve the corpus to read in a browser: the family graph, any member's
                       proof graph, a search of the theorems (--port, --timeout, --root)

Divide and conquer (serve RPCs): defer      make an open leaf a card and a premise of its section
                                 cards      the cards: citers, parents, attackers, the fill order

Checks (stateless):
  check                Verify a proposition (text or JSON on stdin)
  check-derivation     Check if conclusion follows from premises (JSON)
  check-consistency    Check if statements are mutually consistent (JSON)
  parse-prop           Preview how the engine parses a text-DSL proposition

Run 'xugo <command> --help' for details on a specific command.
`)
}

func main() {
	traceStart = time.Now()

	// Parse global flags before the command.
	dataDir := ""
	args := os.Args[1:]
	for len(args) > 0 && strings.HasPrefix(args[0], "--") {
		switch {
		case args[0] == "--data-dir" && len(args) > 1:
			dataDir = args[1]
			args = args[2:]
		case strings.HasPrefix(args[0], "--data-dir="):
			dataDir = strings.TrimPrefix(args[0], "--data-dir=")
			args = args[1:]
		case args[0] == "--trace-log" && len(args) > 1:
			traceLogPath = args[1]
			args = args[2:]
		case strings.HasPrefix(args[0], "--trace-log="):
			traceLogPath = strings.TrimPrefix(args[0], "--trace-log=")
			args = args[1:]
		case args[0] == "--help" || args[0] == "-h":
			printHelp("")
			os.Exit(0)
		default:
			fatal("unknown flag: %s", args[0])
		}
	}

	// The environment's fallback for the flag.
	if traceLogPath == "" {
		traceLogPath = os.Getenv("XUGO_TRACE_LOG")
	}

	if len(args) < 1 || args[0] == "help" || args[0] == "--help" || args[0] == "-h" {
		printHelp("")
		os.Exit(0)
	}
	if len(args) >= 2 && (args[1] == "--help" || args[1] == "-h") {
		printHelp(args[0])
		os.Exit(0)
	}

	traceEntry.Command = args[0]
	dataDirFlag = dataDir

	if run, ok := engineFreeCommands[args[0]]; ok {
		run(args[1:])
		writeTrace()
		return
	}

	initEngine(dataDir)
	ctx := context.Background()

	switch args[0] {
	case "check":
		cmdCheck(ctx)
	case "check-derivation":
		cmdCheckDerivation(ctx)
	case "check-consistency":
		cmdCheckConsistency(ctx)
	case "parse-prop":
		cmdParseProp()
	case "session-create":
		cmdSessionCreate(ctx)
	// session-close intentionally NOT exposed via CLI either — same rationale
	// as the RPC dispatch above (sessions are load-bearing across multi-sub-
	// agent orchestrations; auto-timeout reclaims naturally).
	case "add-goal":
		cmdAddGoal()
	case "inspect":
		cmdInspect(ctx)
	case "apply":
		cmdApply(ctx)
	case "retrieve":
		cmdRetrieve(ctx)
	case "probe":
		cmdProbe(ctx)
	case "batch-apply":
		cmdBatchApply(ctx)
	case "checkpoint":
		cmdCheckpoint(ctx)
	case "restore":
		cmdRestore(ctx)
	case "list-checkpoints":
		cmdListCheckpoints(ctx)
	case "commit-plan":
		cmdCommitPlan(ctx)
	case "serve":
		cmdServe(args[1:])
		return
	default:
		fatal("unknown command: %s", args[0])
	}

	writeTrace()
}

// ---------------------------------------------------------------------------
// Command implementations
// ---------------------------------------------------------------------------

// cmdCheck accepts text or JSON on stdin, parses via the input layer, and
// runs CheckDerivation. This is the ergonomic entry point for agents.
//
// Examples:
//
//	echo 'p => p' | xugo check
//	echo '~(p /\ q) <=> (~p \/ ~q)' | xugo check
//	echo 'forall x:A. P(x) ⊢ P(y)' | xugo check
//	echo 'a => b, b => c, a, ~c ⊢ false' | xugo check
func cmdCheck(ctx context.Context) {
	raw := captureStdin()

	parseStart := time.Now()
	result := engine.Parse(string(raw))
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	// If there are parse errors, return them as JSON.
	if len(result.Errors) > 0 {
		traceEntry.ParseError = result.Errors[0].Message
		writeJSON(map[string]any{
			"result":           "unknown",
			"parse_errors":     result.Errors,
			"normalized_input": result.NormalizedInput,
			"warnings":         result.Warnings,
		})
		return
	}

	traceEntry.InputParsed = result.NormalizedInput

	// Successfully parsed. Run derivation check.
	p := result.Prop
	engineStart := time.Now()
	res, err := eng.CheckDerivation(ctx, &engine.CheckDerivationRequest{
		Conclusion: p,
		TimeoutMs:  5000,
	})
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	traceEntry.DiagCount = len(res.Diagnostics)

	// Build response with parse info included.
	out := map[string]any{
		"result": res.Result,
	}
	if res.CapabilityHint != nil {
		out["capability_hint"] = res.CapabilityHint
	}
	if len(res.Diagnostics) > 0 {
		out["diagnostics"] = res.Diagnostics
	}
	if len(result.Warnings) > 0 {
		out["warnings"] = result.Warnings
	}
	if result.NormalizedInput != string(raw) {
		out["normalized_input"] = result.NormalizedInput
	}
	writeJSON(out)
}

func cmdCheckDerivation(ctx context.Context) {
	parseStart := time.Now()
	var in CheckDerivationInput
	readInput(&in)

	premises := make([]core.Prop, len(in.Premises))
	for i, p := range in.Premises {
		var err error
		premises[i], err = propFromInput(p)
		if err != nil {
			fatal("premise %d: %v", i, err)
		}
	}
	conclusion, err := propFromInput(in.Conclusion)
	if err != nil {
		fatal("conclusion: %v", err)
	}
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	res, err := eng.CheckDerivation(ctx, &engine.CheckDerivationRequest{
		Premises:   premises,
		Conclusion: conclusion,
		TimeoutMs:  in.TimeoutMs,
	})
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	traceEntry.DiagCount = len(res.Diagnostics)
	writeJSON(res)
}

func cmdCheckConsistency(ctx context.Context) {
	parseStart := time.Now()
	var in CheckConsistencyInput
	readInput(&in)

	stmts := make([]core.Prop, len(in.Statements))
	for i, s := range in.Statements {
		var err error
		stmts[i], err = propFromInput(s)
		if err != nil {
			fatal("statement %d: %v", i, err)
		}
	}
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	res, err := eng.CheckConsistency(ctx, &engine.CheckConsistencyRequest{
		Statements: stmts,
		TimeoutMs:  in.TimeoutMs,
	})
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	traceEntry.DiagCount = len(res.Diagnostics)
	writeJSON(res)
}

// cmdParseProp is a debug / introspection helper. It parses a text-DSL
// proposition and returns the engine's interpretation — what the input
// normalizes to, what the parsed prop prints as, and any warnings.
//
// Useful for previewing how a snippet of text DSL will be read before
// committing it through check / add-goal / lemma. Also handy as a
// linter for malformed input — the structured diagnostics point at the
// exact byte offset.
func cmdParseProp() {
	parseStart := time.Now()
	body := captureStdin()
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	res, err := rpcParseProp(body)
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	writeJSON(res)
}

func cmdSessionCreate(ctx context.Context) {
	engineStart := time.Now()
	info, err := eng.CreateSession(ctx)
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	writeJSON(info)
}

func cmdAddGoal() {
	parseStart := time.Now()
	var in AddGoalInput
	readInput(&in)
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	out, err := addSessionGoal(in.SessionID, in.Goal)
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	writeJSON(out)
}

func cmdInspect(ctx context.Context) {
	parseStart := time.Now()
	var in InspectInput
	readInput(&in)
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	res, err := eng.Inspect(ctx, in.SessionID, &engine.InspectRequest{GoalID: in.GoalID})
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}

	type goalOut struct {
		ID        string `json:"id"`
		Statement string `json:"statement"`
		// StatementTyped: parse-faithful form (see rpcInspect's goalOut).
		StatementTyped string    `json:"statement_typed,omitempty"`
		Hypotheses     []hypView `json:"hypotheses,omitempty"`
		Depth          int       `json:"depth"`
	}
	type factOut struct {
		Kind        string            `json:"kind"`
		Params      map[string]string `json:"params,omitempty"`
		Description string            `json:"description,omitempty"`
		Unverified  string            `json:"unverified,omitempty"`
	}
	type out struct {
		Goals           []goalOut `json:"goals"`
		NumOpen         int       `json:"num_open"`
		Complete        bool      `json:"complete"`
		FocusedGoalID   string    `json:"focused_goal_id,omitempty"`
		StructuralFacts []factOut `json:"structural_facts,omitempty"`
		Truncated       bool      `json:"truncated,omitempty"`
	}
	o := out{
		NumOpen:       res.NumOpen,
		Complete:      res.Complete,
		FocusedGoalID: res.FocusedGoalID,
		Truncated:     res.Truncated,
	}
	for _, g := range res.Goals {
		typed, _ := res.Spelling.Typed(g.Statement)
		o.Goals = append(o.Goals, goalOut{
			ID:             g.ID,
			Statement:      res.Spelling.Prop(g.Statement),
			StatementTyped: typed,
			Hypotheses:     indexedHyps(g.Hypotheses, res.Spelling),
			Depth:          g.Depth,
		})
	}
	for _, f := range res.StructuralFacts {
		o.StructuralFacts = append(o.StructuralFacts, factOut{
			Kind:        f.Kind,
			Params:      f.Params,
			Description: f.Description,
			Unverified:  f.Unverified,
		})
	}
	writeJSON(o)
}

func cmdApply(ctx context.Context) {
	parseStart := time.Now()
	var in ApplyInput
	readInput(&in)

	tactic, err := tacticReqFromInput(in.Tactic)
	if err != nil {
		fatal("%v", err)
	}
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	res, err := eng.ApplyStep(ctx, in.SessionID, &engine.ApplyStepRequest{
		GoalID:   in.GoalID,
		Tactic:   tactic,
		BudgetMs: in.BudgetMs,
	})
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	traceEntry.DiagCount = len(res.Diagnostics)
	writeJSON(res)
}

func cmdRetrieve(ctx context.Context) {
	parseStart := time.Now()
	var in RetrieveInput
	readInput(&in)
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	res, err := eng.Retrieve(ctx, in.SessionID, &engine.RetrieveRequest{
		Mode:        in.Mode,
		GoalID:      in.GoalID,
		BudgetMs:    in.BudgetMs,
		Consts:      in.Consts,
		NamePattern: in.NamePattern,
		RelatedTo:   in.RelatedTo,
		MaxPerGroup: in.MaxPerGroup,
	})
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}

	writeJSON(res)
}

func cmdProbe(ctx context.Context) {
	parseStart := time.Now()
	var in ProbeInput
	readInput(&in)
	tactic, err := tacticReqFromInput(in.Tactic)
	if err != nil {
		fatal("%v", err)
	}
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	res, err := eng.Probe(ctx, in.SessionID, &engine.ProbeRequest{
		GoalID:   in.GoalID,
		Tactic:   tactic,
		BudgetMs: in.BudgetMs,
	})
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	// The engine's ProbeResult is the reply as it stands (rpcProbe says why).
	writeJSON(res)
}

func cmdBatchApply(ctx context.Context) {
	parseStart := time.Now()
	var in BatchApplyInput
	readInput(&in)

	tactics := make([]engine.TacticReq, len(in.Tactics))
	for i, t := range in.Tactics {
		var err error
		tactics[i], err = tacticReqFromInput(t)
		if err != nil {
			fatal("tactic %d: %v", i, err)
		}
	}
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	mode := engine.FirstSuccess
	if in.Mode == "compare_all" {
		mode = engine.CompareAll
	}

	engineStart := time.Now()
	res, err := eng.BatchApply(ctx, in.SessionID, &engine.BatchApplyRequest{
		GoalID:  in.GoalID,
		Tactics: tactics,
		Mode:    mode,
	})
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	writeJSON(res)
}

func cmdCheckpoint(ctx context.Context) {
	parseStart := time.Now()
	var in CheckpointInput
	readInput(&in)
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	cpID, err := eng.Checkpoint(ctx, in.SessionID, in.Name)
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	writeJSON(map[string]string{"checkpoint_id": cpID})
}

func cmdRestore(ctx context.Context) {
	parseStart := time.Now()
	var in RestoreInput
	readInput(&in)
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	if err := eng.Restore(ctx, in.SessionID, in.CheckpointID); err != nil {
		fatal("%v", err)
	}
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	writeJSON(map[string]string{"status": "restored"})
}

func cmdListCheckpoints(ctx context.Context) {
	parseStart := time.Now()
	var in SessionIDInput
	readInput(&in)
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	cps, err := eng.ListCheckpoints(ctx, in.SessionID)
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	writeJSON(map[string]any{"checkpoints": cps})
}

func cmdCommitPlan(ctx context.Context) {
	parseStart := time.Now()
	var in CommitPlanInput
	readInput(&in)
	traceEntry.ParseMs = int(time.Since(parseStart).Milliseconds())

	engineStart := time.Now()
	res, err := eng.CommitPlan(ctx, in.SessionID, &engine.CommitPlanRequest{
		GoalID:  in.GoalID,
		PlanRef: in.PlanRef,
	})
	traceEntry.EngineMs = int(time.Since(engineStart).Milliseconds())
	if err != nil {
		fatal("%v", err)
	}
	traceEntry.DiagCount = len(res.Diagnostics)
	writeJSON(res)
}

func readInputFromBytes(data []byte, v any) {
	if err := decodeRPCInput(data, v); err != nil {
		fatal("%v", err)
	}
}

// rpcDefer makes an open leaf a card and closes the leaf by it
// (engine.Engine.Defer).
func rpcDefer(ctx context.Context, body []byte) (any, error) {
	var in engine.DeferRequest
	if err := decodeRPCInput(body, &in); err != nil {
		return nil, err
	}
	res, err := eng.Defer(ctx, &in)
	if err != nil {
		return nil, err
	}
	// The state view carries core.Prop goals, which the RPC layer renders
	// as text (stateViewToJSON) — the same rendering every step result
	// goes through; the rest of the result is plain data.
	out := map[string]any{"status": res.Status}
	if len(res.StatedBy) > 0 {
		out["stated_by"] = res.StatedBy
	}
	if len(res.OpenElsewhere) > 0 {
		out["open_elsewhere"] = res.OpenElsewhere
	}
	if res.Card != nil {
		out["card"] = res.Card
	}
	if res.Section != nil {
		out["section"] = res.Section
	}
	if res.State != nil {
		out["state"] = stateViewToJSON(res.State)
	}
	return out, nil
}

// rpcCards renders the card view (engine.Engine.Cards). An
// empty body is the unfiltered view.
func rpcCards(body []byte) (*engine.CardsResult, error) {
	var in engine.CardsRequest
	if len(body) > 0 {
		if err := decodeRPCInput(body, &in); err != nil {
			return nil, err
		}
	}
	return eng.Cards(&in)
}

// moduleRoot walks up from the working directory to the go.mod.
func moduleRoot() (string, error) {
	dir, err := os.Getwd()
	if err != nil {
		return "", err
	}
	for {
		if _, err := os.Stat(filepath.Join(dir, "go.mod")); err == nil {
			return dir, nil
		}
		parent := filepath.Dir(dir)
		if parent == dir {
			return "", fmt.Errorf("no go.mod above the working directory")
		}
		dir = parent
	}
}

// cmdCards is the CLI form of the card view: reads the session store
// under --data-dir, with no proof engine or serve needed.
func cmdCards(args []string) {
	var req engine.CardsRequest
	for i := 0; i < len(args); i++ {
		switch {
		case args[i] == "--lineage" && i+1 < len(args):
			req.Lineage = args[i+1]
			i++
		case strings.HasPrefix(args[i], "--lineage="):
			req.Lineage = strings.TrimPrefix(args[i], "--lineage=")
		case args[i] == "--key" && i+1 < len(args):
			req.Key = args[i+1]
			i++
		case strings.HasPrefix(args[i], "--key="):
			req.Key = strings.TrimPrefix(args[i], "--key=")
		default:
			fatal("cards: unknown argument %s (flags: --lineage ID, --key KEY; the corpus's cards, a family's among them, are xugo query cards)", args[i])
		}
	}
	store := ""
	if dataDirFlag != "" {
		store = filepath.Join(dataDirFlag, "sessions")
	}
	res, err := engine.ViewCards(store, &req)
	if err != nil {
		fatal("%v", err)
	}
	writeJSON(res)
}
