// Package engine implements XuGo's proof session: the stateful
// navigation a proof is found in, and the record a chapter's text is
// emitted from.
//
// The session (CreateSession, Inspect, ApplyStep, Retrieve, Probe,
// BatchApply, Checkpoint, Restore): proof state management and
// agent-driven navigation.
//
// Beside it, the stateless checks (CheckDerivation, CheckConsistency):
// independent checks that need no session.
//
// The agent-facing surface follows the "engine supplies bricks, not
// architecture" principle:
//
//   - Inspect returns goal state plus structural facts about the focused
//     goal (applicable parameterless moves, definable consts, induction
//     vars, case-split positions). No score, no priority — facts only.
//
//   - Retrieve returns corpus members (proof-registry entries) grouped
//     by the strategy that produced them (by goal, by constants, by
//     name, by dependency — retrieve_corpus.go). Per-strategy ranking
//     inside each group; no global fusion across groups.
//
//   - Probe answers "what would happen if I did X?" non-destructively.
//     Returns success/fail/unknown(reason). Unknown always carries a
//     reason from a fixed enum.
//
// The transport is the command line and its HTTP server (engine/cmd/xugo);
// both delegate to Engine.
package engine

import (
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext/dsl"
)

// ---------------------------------------------------------------------------
// Stateless checks: request/response types
// ---------------------------------------------------------------------------

type CheckDerivationRequest struct {
	Premises      []core.Prop `json:"premises"`
	Conclusion    core.Prop   `json:"conclusion"`
	TimeoutMs     int         `json:"timeout_ms,omitempty"`      // 0 = default (200ms)
	SkipDomainChk bool        `json:"skip_domain_chk,omitempty"` // bypass domain classification (for library reconstruction)
}

// ResultType is the three-state outcome for CheckDerivation.
type ResultType string

const (
	ResultValid   ResultType = "valid"   // proved
	ResultInvalid ResultType = "invalid" // confirmed not derivable (positive evidence)
	ResultUnknown ResultType = "unknown" // could not determine (incomplete search or unsupported domain)
)

// ConsistencyResult is the three-state outcome for CheckConsistency.
type ConsistencyResult string

const (
	ConsistencyConsistent   ConsistencyResult = "consistent"   // confirmed consistent (positive evidence or complete search)
	ConsistencyInconsistent ConsistencyResult = "inconsistent" // contradiction found
	ConsistencyUnknown      ConsistencyResult = "unknown"      // could not determine
)

// CapabilityHint explains why a result is "unknown".
type CapabilityHint struct {
	Reason            string   `json:"reason"`                       // unsupported_domain, partially_supported_domain, proof_search_exhausted, timeout
	UnsupportedConsts []string `json:"unsupported_consts,omitempty"` // constant names not in any registered domain
	Domain            string   `json:"domain,omitempty"`             // detected domain (logic, bitops, etc.)
}

type CheckDerivationResult struct {
	Result         ResultType      `json:"result"`
	CapabilityHint *CapabilityHint `json:"capability_hint,omitempty"`
	Diagnostics    []Diagnostic    `json:"diagnostics,omitempty"`
}

type CheckConsistencyRequest struct {
	Statements []core.Prop `json:"statements"`
	TimeoutMs  int         `json:"timeout_ms,omitempty"`
}

type CheckConsistencyResult struct {
	Result         ConsistencyResult `json:"result"`
	ConflictSubset []int             `json:"conflict_subset,omitempty"` // indices into Statements
	CapabilityHint *CapabilityHint   `json:"capability_hint,omitempty"`
	Diagnostics    []Diagnostic      `json:"diagnostics,omitempty"`
}

// ---------------------------------------------------------------------------
// Session types
// ---------------------------------------------------------------------------

type SessionInfo struct {
	ID        string    `json:"id"`
	CreatedAt time.Time `json:"created_at"`
	// Family is the family the session is bound to (empty for
	// a bare session); Imports the further families whose definitions
	// it started with. See Engine.SetSessionFamily.
	Family  string   `json:"family,omitempty"`
	Imports []string `json:"imports,omitempty"`
}

// FamilyBinding reports what SetSessionFamily installed: one entry per
// use rule, naming the registered definition it came from.
type FamilyBinding struct {
	Family    string          `json:"family"`
	Imports   []string        `json:"imports,omitempty"`
	Installed []InstalledRule `json:"installed"`
}

// InstalledRule is one use rule a family binding installed: the
// registered definition entry it came from, the shape that entry was
// served in, and the rule statement.
type InstalledRule struct {
	Entry string `json:"entry"`
	Shape string `json:"shape"`
	Rule  string `json:"rule"`
}

// StateView is the basic open-goal listing for a session. It is a building
// block for both the lightweight session-list path and the richer
// InspectResult.
type StateView struct {
	Goals    []GoalView `json:"goals"`
	NumOpen  int        `json:"num_open"`
	Complete bool       `json:"complete"` // all goals closed

	// Spelling is the door the goals' statements and hypotheses are
	// served through (spelling.go): the session's chapter spelling,
	// which the wire layer renders Statement and Hypotheses with. Not
	// wire data itself.
	Spelling *Spelling `json:"-"`
}

type GoalView struct {
	ID         string      `json:"id"`
	Statement  core.Prop   `json:"statement"`
	Hypotheses []core.Term `json:"hypotheses,omitempty"`
	Depth      int         `json:"depth"`

	// SurfaceNames lists the goal's surface-name aliases (surface_alias.go):
	// base name → the minted variable it denotes, e.g. {"n": "n₀"}. Each
	// base name is a valid spelling in claim texts (assert/lemma/lean_rw)
	// and term parameters (witness/instantiate/trans) at THIS goal — the
	// engine resolves it to the minted variable. Absent when the goal has
	// no unambiguous aliases; the minted spellings are always valid.
	SurfaceNames map[string]string `json:"surface_names,omitempty"`
}

// TacticReq specifies a tactic for agents to apply to a goal.
//
// Lemma-tactics may identify the lemma either by inline Prop (Lemma) or by
// a registry entry (LemmaKey). LemmaKey is preferred when the lemma is a
// registered member — it avoids re-parsing the text-DSL form and serves
// the entry's own statement.
type TacticReq struct {
	Type     string    `json:"type"`
	Lemma    core.Prop `json:"lemma,omitempty"`     // for "lemma" — inline Prop (kept for back-compat)
	LemmaKey string    `json:"lemma_key,omitempty"` // for "lemma" / "lean_rw" — a registry entry: its own key (prop_…) or its registered name (exact, case-sensitive — see lemma_name_resolve.go)
	// LemmaText carries the raw text-DSL form of a "lemma" / "lean_rw"
	// lemma, parsed in-engine against the focused goal's scope rather than
	// scope-blind at the CLI wire layer. Seeding the goal's free-var types
	// and constants lets the agent name a session free-var (n₀) or a
	// goal-local constant directly, without the `n_0:num ⊢ …`
	// type-declaration prefix the scope-less wire parse would require.
	LemmaText string `json:"lemma_text,omitempty"`
	// ReadAt makes a "lemma" cite a structure LAW read at an instance —
	// the Go `Law.Read(instance)` (reading.go): LemmaKey names the law,
	// ReadAt the instance (an entry, a resident hypothesis of the goal,
	// or a reading), exactly as on a `by` premise or a `simp_with` rule.
	// The reading is the law's statement with its components pinned to
	// the instance's and its structure hypothesis discharged, derived by
	// the kernel. Go's `Cite(Law.Read(h))`: a goal the reading states
	// closes on it; any other goal has it installed as a resident
	// hypothesis for the moves that follow, a TermSpecialize PREFIX
	// grounding it at the tuple (`Cite(Law.Read(h), w…)`). LemmaText and
	// TypeSpecialize are refused beside it.
	ReadAt *ReadAtSpec `json:"read_at,omitempty"`
	Const  string      `json:"const,omitempty"` // for "def_expand": const name; "case_split": term JSON; "induction": var name; "witness"/"instantiate"/"trans": printed term; "congr_arg": function term f; "congr_fun": argument term x
	// HypIndex carries an optional 0-based hyp index. Required for
	// "subst" (the equality hyp to substitute by), "rw" (the equality
	// hyp to rewrite with), "congr_arg" (the equality hyp to apply the
	// function to), "congr_fun" (the function-equality hyp to apply the
	// argument to), and "instantiate" (the ∀-hyp to ground; there is no
	// no-index first-∀-hyp sugar, so agents face ONE grounding action —
	// use `inspect` to locate the target hyp). Optional for "split_disj",
	// "split_hyp_iff", "split_hyp_imply" and "strip_quant": absent picks
	// the first hyp of the shape (strip_quant strips a ∀-headed
	// conclusion before it looks at any hyp); set targets that hyp, and
	// strip_quant then leaves the conclusion alone. Optional for
	// "split_conj" and "def_expand": absent, they act on the conclusion;
	// set, split_conj splits THAT conjunctive hypothesis into its
	// conjuncts, the conjunction kept (Go: `a.Conjuncts(fact, …)`), and
	// def_expand opens Const in THAT hypothesis alone, the unfolded
	// statement joining the hypotheses beside the folded one (Go:
	// `a.Unfolded(fact, <c's definition>)`).
	// Pointer (not int) so absence is distinguishable from explicit 0.
	HypIndex *int `json:"hyp_index,omitempty"`
	// Terms is "instantiate"'s multi-witness form: ground the ∀-hyp at
	// HypIndex (required with Terms) by peeling one leading binder per
	// entry, in binder order — recorded as ONE composite `specialize`
	// ministep that adds only the final ground instance (no
	// intermediate partial hyps materialize, so no NewHyps-tracking /
	// re-inspection between rungs) and consumes the source ∀-hyp
	// unless Keep. Each entry is a text-DSL term parsed against the
	// goal's scope (the same path Const uses). Mutually exclusive with
	// Const (the single-witness, keep-source primitive form).
	Terms []string `json:"terms,omitempty"`
	// Keep preserves the grounded source ∀-hyp in the "instantiate"
	// tactic (both single-Const and Terms multi-witness forms), for the
	// classic scenario "one wide ∀-hyp serves several witness tuples in
	// a row." Default per form: Terms → source consumed (Lean-style
	// specialize semantics), single Const → source kept (back-compat
	// with the pre-migration index-targeted primitive; set `keep:false`
	// explicitly to consume). Ignored by every non-`instantiate` tactic.
	Keep bool `json:"keep,omitempty"`
	// HypIndices is "clear"'s sole hyp-targeting parameter: the SET of
	// 0-based indices to drop in one apply (a single drop is [i]). Indices
	// refer to the goal's hyp list as the agent sees it. clear does NOT
	// read HypIndex — every clear routes through ApplyClearHyps and records
	// one clear_hyps ministep.
	HypIndices []int `json:"hyp_indices,omitempty"`
	// Name is the variable name "denote" gives the term in `const` —
	// "let <name> = <const>". Optional there: omitted, the step mints
	// the engine's α₀ (collision-avoided); it requires `const`, the
	// bare search form of denote having nothing to name. "let" — the
	// definition `<name> := <const>` — requires both. Ignored by every
	// other tactic.
	Name string `json:"name,omitempty"`
	// Flip is the direction flag for "rw": false rewrites the equality
	// hyp's written direction (a→b), true the reverse (b→a). Ignored by
	// every other tactic.
	Flip bool `json:"flip,omitempty"`
	// Claim carries the asserted sub-claim φ for the "assert" tactic. Must
	// be a hyp-free Prop. Only programmatic callers populate this
	// directly; the CLI's text form arrives via ClaimText.
	Claim core.Prop `json:"claim,omitempty"`
	// ClaimText carries the raw text-DSL form of an "assert" claim, parsed
	// in-engine against the focused goal's scope (same rationale as
	// LemmaText). A bare session free-var like n₀ resolves from the goal's
	// harvested types instead of needing an explicit `n_0:num ⊢ …` prefix.
	ClaimText string `json:"claim_text,omitempty"`
	// NodeID is the sole input to the "cite-node" tactic: the session goal_id
	// of a previously-closed node whose conclusion ψ we want as a hyp at the
	// current focus. Resolution order: this session's closed subtrees first,
	// then the engine-global cross-session derivation pool (see
	// derivation_pool.go) — the id's hash part is the sequent's canonical
	// AlphaKey prefix, so an id minted by another session of the same serve
	// resolves here too. Soundness preconditions (target.Proved() + target's
	// hyp context ⊆ current focus's hyp context) are checked by the engine
	// dispatch before applying, identically for local and pool hits. See
	// prover.ApplyCiteNode for mechanics.
	NodeID string `json:"node_id,omitempty"`
	// TermSpecialize pre-substitutes the lemma's outer term-level ∀-binders
	// before the lemma is installed (or used as a rewrite). The term-level
	// counterpart of TypeSpecialize: keys are ∀-binder names read off the
	// lemma's printed form; values are witness terms parsed via the text-DSL
	// (same path `instantiate`'s `const` uses) against the goal's scope.
	//
	// Peeling proceeds OUTSIDE-IN from the lemma's conclusion: at each
	// outermost ∀-binder, if its name is in the map, the engine
	// β-substitutes the witness and peels the binder; if the name is NOT
	// in the map, peeling stops there. After processing, every map key
	// must have been consumed — an unmatched key is an error (the named
	// binder lives below a non-specialized outer binder, or it's a typo
	// on a binder that doesn't exist).
	//
	// Polymorphic binders work naturally: when a binder's type contains a
	// type variable (`∀P:(A→bool)→bool. …`), the unifier matches it
	// against the witness's concrete type and σ_type propagates to the
	// rest of the lemma. The agent does NOT need to pre-supply a
	// matching TypeSpecialize for the polymorphic binder's vars — the
	// witness pins them automatically.
	//
	// Mirrors LEAN `apply h (P := λs. …) (a := empty_set)` ergonomics. The
	// pre-σ source AlphaKey is still recorded as polymorphicSourceKey,
	// so emit's leaf resolution points at the original (polymorphic) entry.
	//
	// Also honored by `cite-node`: there the "lemma" is the cited node's
	// ∀-closed conclusion, and the same post-install chain peels its outer
	// ∀-binders at the supplied witnesses in one call — replacing the
	// N-round `cite-node` + `instantiate`×N + `clear` ladder that assembly
	// / coordinator steps (Step 6.6) otherwise pay. Records identically to
	// that expanded ladder (ordinary instantiate/clear ministeps), so the
	// persisted proto / emit / replay are unchanged.
	TermSpecialize map[string]string `json:"term_specialize,omitempty"`
	// WithLemmas is `auto_with`'s scoped lemma list AND `simp_with`'s
	// ordered rewrite-rule set (slice order = firing order). For
	// auto_with each entry is resolved + installed on the focused clone
	// just for this call; failure to close discards the clone (no
	// persist). For simp_with each entry is resolved (key/text +
	// specializations + type adaptation) and recorded verbatim as one
	// rule of the SimpWith ministep, and the entries are the whole rule
	// set: the session's installed definitions fire under `simp` and
	// `simp_all`, never here. Empty unless Type is one of those.
	WithLemmas []LemmaWithSpec `json:"with_lemmas,omitempty"`
	// KeepHypIndices is `auto_with`'s explicit-keep list: every hyp index
	// NOT in this set is cleared before the scoped lemmas install. Mutually
	// exclusive with DropHypIndices. When both are empty the default
	// heuristic clears every top-level ∀-headed hyp.
	KeepHypIndices []int `json:"keep_hyp_indices,omitempty"`
	// DropHypIndices is `auto_with`'s explicit-drop list: exactly those
	// indices are cleared. Mutually exclusive with KeepHypIndices.
	DropHypIndices []int `json:"drop_hyp_indices,omitempty"`
	// ByHyps is the `by` tactic's RESIDENT premise list: hypotheses of
	// the focused goal named as premises (kept across by's clear-first,
	// optionally grounded at witnesses). Everything not named in ByHyps
	// is cleared before the WithLemmas premises install. See by_tactic.go.
	ByHyps []ByHypSpec `json:"by_hyps,omitempty"`
	// ElementaritySource and ElementarityFacts are the `elementarity` tactic's call
	// (Go's ByElementarity): the source — an entry stating the property at a
	// concrete structure, or a resident family of models by prime; absent
	// for none — and the facts the step's obligations are discharged
	// from. Its Terms are the parameters of the fixed-parameter form
	// .At. See elementarity_tactic.go.
	ElementaritySource *ElementarityRef  `json:"source,omitempty"`
	ElementarityFacts  []ElementarityRef `json:"facts,omitempty"`
	// ByShape is the `by` tactic's declared shaping — the normalization
	// the accumulated premises pass through before the terminal close
	// (the math layer's Normalized / PreNormalized / Denoted(n) /
	// HilbertDenoted values). nil = no shaping.
	ByShape *ByShapeReq `json:"by_shape,omitempty"`
	// Arith, on `by`, selects the gated arithmetic closer (the math
	// layer's ByArith) instead of the CNF refuter. The session's proof
	// scope gates it exactly as replay would (omega circularity
	// gate) — a foundation-resident target's by{arith} fails loudly
	// instead of recording an un-replayable Arith. Ignored by every
	// other tactic.
	Arith bool `json:"arith,omitempty"`
	// Settac, on `by`, selects the membership-mode set driver (the math
	// layer's BySets) instead of the CNF refuter: standard-vocabulary
	// definitional unfolding to a membership residual, then the
	// kernel-checked refute. The one closer whose bare form (no premises)
	// is legal — the vocabulary unfolding is its content. Mutually
	// exclusive with arith. Ignored by every other tactic.
	Settac bool `json:"settac,omitempty"`
	// Chase, on `by`, selects the diagram-chase closer (the math layer's
	// ByChase): the named premises read as an abelian diagram — modules,
	// homomorphisms, commuting squares, exactness, onto and one-to-one
	// maps, submodules — and the goal decided by pulling preimages back
	// for Depth rounds. Deterministic and bounded: no key is recorded.
	// Mutually exclusive with arith and settac; premises are required.
	// Ignored by every other tactic.
	Chase *ByChaseReq `json:"chase,omitempty"`
	// Broadcast, on `by`, runs the terminal closer over every leaf the
	// shaping fanned out instead of demanding a single one (the math
	// layer's Broadcast premise-list option). Ignored by every other
	// tactic.
	Broadcast bool `json:"broadcast,omitempty"`
	// TypeSpecialize pre-substitutes the lemma's free TYPE variables
	// before the lemma is installed (or used as a rewrite). Applies to the
	// "lemma" and "lean_rw" verbs. Map keys are the lemma's internal
	// type-variable names — read them off the entry's printed
	// statement, e.g. `set_member⟨A:var:B⟩(y, image(f, s))` exposes `A` and `B`.
	// Map values are type expressions parsed via dsl.ParseTypeText: a
	// concrete type (`num`, `bool`, `num→bool`), an explicit type var
	// (`var:A`), or a `?`-prefixed Skolem name (`?71152` — the printer's
	// form for goal-local fresh type vars). Partial maps are allowed; any
	// type-var the agent doesn't pin is left for the goal-derived
	// adapter to handle. An unknown key (typo) or unparseable value is a
	// hard error — never silently dropped, so a wrong σ never accidentally
	// installs a no-op lemma. The pre-σ source AlphaKey is still recorded
	// as polymorphicSourceKey, so emit's leaf resolution points at the original
	// polymorphic entry. Mirrors LEAN `(A := T) (B := U)` ergonomics.
	//
	// Also honored by "instantiate" as the explicit escape hatch of its
	// automatic type adaptation: keys are the target ∀-HYP's type-var
	// names, the σ seeds the hyp-side substitution before witness
	// resolution, and the same registry-backed re-derivation chain runs
	// (see engine/instantiate_type_adapt.go). Usually unnecessary — the
	// witnesses' types pin σ automatically. NOTE: the xugo CLI wire
	// layer does not yet forward this field for instantiate (only for
	// lemma / lean_rw); engine-API callers get it directly.
	TypeSpecialize map[string]string `json:"type_specialize,omitempty"`
	// Assoc / Sym are the "ac_regroup" tactic's certificate pair: the
	// entries of the associativity law (∀m n p. (m⊕n)⊕p = m⊕(n⊕p),
	// either orientation) and the commutativity law (∀m n. m⊕n = n⊕m),
	// both over the SAME binary op ⊕, which the kit reads off the assoc
	// statement. The focused goal must be the bare equation `lhs = rhs`
	// between two ⊕-sums over one leaf multiset (strip binders first);
	// the kit derives the rearrangement certificate and closes or
	// installs it (proof.ApplyACRegroup — the ACRegroup goal face).
	Assoc string `json:"assoc,omitempty"`
	Sym   string `json:"sym,omitempty"`
}

type ApplyStepRequest struct {
	GoalID string    `json:"goal_id"`
	Tactic TacticReq `json:"tactic"`
	// BudgetMs caps wall-clock time inside search-y tactics (auto /
	// refute / expand). When > 0, ApplyStep wraps its ctx with this
	// deadline so the inner CNF refuter honors the agent's budget
	// instead of falling back to ProverEnv.CnfRefuterTimeout. Absent
	// or ≤ 0: the prover-env default applies.
	BudgetMs int `json:"budget_ms,omitempty"`
}

type StepResult struct {
	Success     bool              `json:"success"`
	State       *StateView        `json:"state,omitempty"`
	PlanRef     string            `json:"plan_ref,omitempty"`     // opaque ref for deferred commit (CompareAll only)
	AutoMatched []AutoMatchedGoal `json:"auto_matched,omitempty"` // subgoals auto-closed by auto-match since the previous step
	// NewHyps lists hypotheses this apply ADDED to a resulting open goal,
	// each with its 0-based index in that goal's (canonically-sorted) hyp
	// list. Populated for hyp-adding tactics (instantiate, assert,
	// congr_arg, congr_fun, lemma, …); empty/omitted otherwise. The agent
	// uses this to target the just-introduced hyp (e.g. the partial-∀ from
	// instantiate) WITHOUT re-inspecting: the hyp list is kept in canonical
	// sort order (core.MakeProp), so introducing a hyp re-sorts the list and
	// renumbers the tail — meaning an index read from an inspect taken
	// BEFORE this apply is stale. NewHyps gives the post-apply index.
	NewHyps []AddedHyp `json:"new_hyps,omitempty"`
	// Effect classifies what this apply did to the focused goal, AFTER
	// auto-match has closed any closeable produced leaves. Same
	// enum as ProbeResult.Effect:
	//   - "close"    — 0 surviving subgoals (the apply closed the goal)
	//   - "simplify" — exactly 1 surviving subgoal AND it differs structurally
	//                  from the input goal
	//   - "noop"     — exactly 1 surviving subgoal AND it is α-equivalent to
	//                  the input (the apply ran but produced no structural
	//                  progress). Distinct from Success=false (which means
	//                  the tactic refused outright).
	//   - "branch"   — ≥2 surviving subgoals
	// Empty when Success=false.
	Effect string `json:"effect,omitempty"`
	// Produced lists the new subgoals this apply created, paired with the
	// structural diff against the input goal. Order matches State.Goals
	// for these particular leaves. Empty when Effect == "close" (no
	// surviving subgoals) or when Success=false. See ProbeSubgoal.Changes
	// for the diff contract — same shape, same semantics.
	Produced    []ProducedSubgoal `json:"produced,omitempty"`
	Diagnostics []Diagnostic      `json:"diagnostics,omitempty"`
	// EngineFault is set when the tactic met an engine fault (fault.go):
	// Success is false, the diagnostic is an engine_fault and carries no
	// repair hint, and the session takes no further move until the
	// fault's record is acknowledged.
	EngineFault *EngineFault `json:"engine_fault,omitempty"`
	// DefineCompleted reports definition moves whose authored
	// obligation THIS apply closed (the WF shape — transcript D's
	// "on close"): the installation (the manual's R4) has run, and the derived
	// guarded readings are live in the session simp set.
	DefineCompleted []DefineCompletion `json:"define_completed,omitempty"`
}

// DefineCompletion is one completed authored-obligation definition
// (see StepResult.DefineCompleted).
type DefineCompletion struct {
	// Defined is the minted constant's name (a spec's joined name
	// list — Consts carries the machine-readable group).
	Defined string `json:"defined"`
	// Consts lists a spec definition's constant group in definition
	// order. Empty for the WF shape.
	Consts []string `json:"consts,omitempty"`
	// Schema names the schema family the compiler will instantiate at
	// replay ("wellfounded_recursion (measure)", "specification").
	Schema string `json:"schema"`
	// SimpInstalled counts the derived readings installed into the
	// session simp set (R4). Always zero for the spec shape — a
	// specification is not a directed rewrite; the author cites the
	// characterizing theorem.
	SimpInstalled int `json:"simp_installed"`
	// Section / Key locate the definition section and its
	// characterizing statement.
	Section int    `json:"section"`
	Key     string `json:"key"`
}

// ProducedSubgoal is the apply-side mirror of ProbeSubgoal: a subgoal this
// apply introduced into the session, plus the per-subgoal structural diff
// from the input goal. The agent reads `Changes` to answer "what did this
// apply actually change?" without diffing PrintProp text.
type ProducedSubgoal struct {
	GoalID  string      `json:"goal_id"` // matches the surviving leaf's ID in State.Goals
	Changes GoalChanges `json:"changes"`
}

// AddedHyp records a hypothesis that an apply introduced into a resulting
// open goal, with its 0-based index in that goal's canonically-sorted hyp
// list — the same index convention `instantiate` / `subst` / `rw` / `clear`
// consume and `inspect` reports. Because the hyp list is kept in canonical
// sort order, introducing a hyp re-sorts the list and renumbers the tail, so
// a pre-apply index is unreliable; this gives the index as it stands after
// the apply.
type AddedHyp struct {
	GoalID string `json:"goal_id"` // the resulting open goal the hyp was added to
	Index  int    `json:"index"`   // 0-based position in that goal's sorted hyp list
	Term   string `json:"term"`    // pretty-printed hypothesis
}

// AutoMatchedGoal records a subgoal that the session auto-closed by
// matching it against a registry entry's statement or a proved sibling
// section. The agent sees this so it understands why a subgoal
// disappeared without any explicit tactic being applied.
type AutoMatchedGoal struct {
	GoalStatement string   `json:"goal_statement"`          // pretty-printed form of the closed subgoal
	MatchedKey    string   `json:"matched_key"`             // the matched entry's own key
	MatchedNames  []string `json:"matched_names,omitempty"` // human-readable names, if any
	// MatchedSection, when non-nil, records that the close came from a
	// PROVED sibling section of the same session (the Use(lemmaK)
	// semantics) rather than a registry entry. 0-based index into the
	// session's sections, in add-goal order. MatchedKey is empty for these.
	MatchedSection *int `json:"matched_section,omitempty"`
}

type CommitPlanRequest struct {
	GoalID  string `json:"goal_id"`
	PlanRef string `json:"plan_ref"`
}

// ---------------------------------------------------------------------------
// Inspect — goal state + structural facts
// ---------------------------------------------------------------------------

// InspectRequest selects which open goal to compute structural facts for
// and to list under Goals. When GoalID is empty and exactly one goal is
// open, that goal is used. When GoalID is empty and ≥2 goals are open,
// structural facts are omitted (the agent must specify which goal it
// cares about — see Retrieve/Probe for the same rule).
type InspectRequest struct {
	GoalID string `json:"goal_id,omitempty"`
	// BudgetMs is the time each probe of the structural pass that reads
	// a clock has (the arith move, an rw): 0 = ProbeDefaultBudgetMs,
	// never past the request context's deadline.
	BudgetMs int `json:"budget_ms,omitempty"`
}

// InspectResult bundles the session's open-goal state with structural facts
// about the focused goal. Structural facts are explicitly facts, not
// recommendations: they describe what shape the goal has and what
// parameterized moves are applicable, without ranking or scoring.
type InspectResult struct {
	// Goals lists the open goals: every one of the session's when the
	// request named no goal, the named goal alone when it did — so the
	// hypothesis indices read off goals[0] are that goal's. NumOpen is
	// the session's count either way.
	Goals    []GoalView `json:"goals"`
	NumOpen  int        `json:"num_open"`
	Complete bool       `json:"complete"`

	// FocusedGoalID is the goal the structural facts are for. Empty when
	// ambiguous (≥2 goals open and no GoalID was specified) or when the
	// session has no open goals.
	FocusedGoalID string `json:"focused_goal_id,omitempty"`

	// StructuralFacts enumerates moves whose preconditions match the
	// focused goal. The list is bounded; when caps trim the result,
	// Truncated is true.
	StructuralFacts []StructuralFact `json:"structural_facts,omitempty"`
	Truncated       bool             `json:"truncated,omitempty"`

	// ClosedSubtrees enumerates proved sub-derivations in this session tree
	// — the citable material for the `cite-node` tactic. Each entry is a
	// closed node whose conclusion ψ can be installed as a hypothesis at
	// the current focus (via `apply cite-node node_id=...`), avoiding
	// re-searching to re-prove ψ when its proof already lives elsewhere in
	// this session. Bounded; the walk does NOT descend into closed
	// sub-trees themselves (children of a closed node are its proof, not
	// separately citable).
	ClosedSubtrees []ClosedSubtreeView `json:"closed_subtrees,omitempty"`

	// Spelling is the door the goals are served through — see
	// StateView.Spelling.
	Spelling *Spelling `json:"-"`
}

// ClosedSubtreeView is one entry in InspectResult.ClosedSubtrees — a
// citable closed sub-derivation in the session tree.
type ClosedSubtreeView struct {
	// NodeID is the stable identifier the agent passes as `cite-node`'s
	// `node_id` to install this sub-derivation's conclusion as a hyp.
	NodeID string `json:"node_id"`

	// Statement is the conclusion ψ (printable form). Hypotheses are
	// summarized by HypCount only — agents pick by conclusion shape +
	// rough context size; the full hyp list would balloon inspect output.
	Statement string `json:"statement"`
	HypCount  int    `json:"hyp_count"`
	Depth     int    `json:"depth"`
	SectionID int    `json:"section_id"`
}

// StructuralFact is one applicable structural / parameterized move on the
// focused goal. The schema is intentionally rigid — no Score, no Priority,
// no Confidence. Ordering is stable but expresses position, not preference.
type StructuralFact struct {
	// Kind is the tactic / move name: def_expand, induction, case_split,
	// strip_quant, split_conj, split_disj, strip_imp, cond_rewrite.
	Kind string `json:"kind"`

	// Params carries what the agent must supply to invoke the move
	// (const name, variable, term position). Empty for parameterless moves.
	Params map[string]string `json:"params,omitempty"`

	// Description is a one-line explanation, mirroring the existing
	// structural-tactic spec descriptions for parameterless moves.
	Description string `json:"description,omitempty"`

	// Unverified is set where the probe that verifies the move was cut
	// off at its budget: the reason. The move is then neither verified
	// nor ruled out, and every other fact of the answer stands.
	Unverified string `json:"unverified,omitempty"`
}

// ---------------------------------------------------------------------------
// Retrieve — corpus lookup, grouped by strategy
// ---------------------------------------------------------------------------

// RetrieveMode selects which corpus query the engine runs. Exactly one of
// the per-mode fields on RetrieveRequest must be set. Modes do not fuse:
// each strategy returns its own group, ranked locally.
type RetrieveMode string

const (
	// RetrieveByGoal reads a session goal: the members whose statement
	// is the goal (by key) and the members that apply to it (the apply
	// rung's plan).
	RetrieveByGoal RetrieveMode = "goal"

	// RetrieveByConsts looks up members mentioning all/any of the named
	// constants. Topic-style retrieval, independent of goal structure.
	RetrieveByConsts RetrieveMode = "consts"

	// RetrieveByName looks up members whose registered name matches a
	// substring or prefix pattern (case-insensitive substring; suffix
	// '*' is treated as the same — names are normally short and
	// prefix-leaning).
	RetrieveByName RetrieveMode = "name_pattern"

	// RetrieveByRelated looks up the members "near" a member in the
	// registry's dependency graph: the entries it cites and the entries
	// citing it, one hop each. Topic-style retrieval, independent of
	// goal structure.
	RetrieveByRelated RetrieveMode = "related_to"
)

type RetrieveRequest struct {
	Mode RetrieveMode `json:"mode"`

	// For RetrieveByGoal:
	GoalID   string `json:"goal_id,omitempty"`
	BudgetMs int    `json:"budget_ms,omitempty"` // total budget across strategies; default 3000

	// For RetrieveByConsts:
	Consts []string `json:"consts,omitempty"`

	// For RetrieveByName:
	NamePattern string `json:"name_pattern,omitempty"`

	// For RetrieveByRelated: the member (a registered entry name, or its
	// own key) to look up neighbors of.
	RelatedTo string `json:"related_to,omitempty"`

	// MaxPerGroup caps results within each strategy group. Zero = engine default (10).
	MaxPerGroup int `json:"max_per_group,omitempty"`
}

// RetrieveResult is the grouped response. Per-strategy ranking only — no
// cross-strategy fusion. Scores are meaningful only within a group.
type RetrieveResult struct {
	GoalID    string          `json:"goal_id,omitempty"`
	Groups    []RetrieveGroup `json:"groups"`
	ElapsedMs int             `json:"elapsed_ms"`
}

type RetrieveGroup struct {
	// MatchedVia names the strategy that produced the entries:
	// "corpus", "corpus_deps", "corpus_dependents" (retrieve_corpus.go).
	MatchedVia string `json:"matched_via"`

	// Truncated is true when the per-group cap trimmed the list.
	Truncated bool `json:"truncated,omitempty"`

	Entries []RetrieveEntry `json:"entries"`
}

type RetrieveEntry struct {
	// Key is the member's OWN key, one spelling the key slot takes
	// (TacticReq.LemmaKey, with_lemmas[].key); Entry, the registered
	// name, is the other.
	Key string `json:"key"`

	// Statement is the member's statement, pretty-printed.
	Statement string `json:"statement,omitempty"`
	// Abbreviations are the names Statement spells as «Name», each with
	// the term it stands for, as the member's author declared them.
	Abbreviations dsl.Abbrev `json:"abbreviations,omitempty"`

	// Entry is the member's registered name, what the key slot of by /
	// lemma / auto_with takes; Family is its chapter. Card says the
	// member is stated without a proof — an axiom until its proof
	// lands — so a close standing on it stands on a card. Match says
	// how the member met the goal: "exact" (its statement is the goal,
	// by key) or "apply" (its conclusion matches the goal by the apply
	// rung's plan, at Witnesses, and Premises are what the rung would
	// need — each "resident" in the context, stated by a proved
	// "entry" or by a "card" (named in Entry either way), or "open").
	Entry     string            `json:"entry,omitempty"`
	Family    string            `json:"family,omitempty"`
	Card      bool              `json:"card,omitempty"`
	Match     string            `json:"match,omitempty"`
	Witnesses []RetrieveWitness `json:"witnesses,omitempty"`
	Premises  []RetrievePremise `json:"premises,omitempty"`

	// Reading is set when the member met the goal as a READING — a law
	// read through a chain of projections from a structure the goal
	// holds a fact of (the `corpus_readings` group). Statement is then
	// what the reading states, Key and Entry name the law, Card says
	// the law or a projection in the chain is a card, and the first
	// premise is the structure fact the chain is read at.
	Reading *RetrieveReading `json:"reading,omitempty"`
}

// RetrieveReading is how a law read through projections is cited: the
// projection chain, outermost first (the law of the structure whose
// fact the reading starts at, down to the law of the structure the
// read law belongs to), and the two spellings of the value — Go's
// `Law.Read(Pₙ.Read(… P₁.Read(instance)))`, the instance an entry's
// name or `ResidentHyp(<fact>)` for a hypothesis (a chapter writes
// its Fact parameter there), and the session's `read_at` for the
// law's premise, `{"key": Pₙ, "read_at": {… {"key": P₁, "read_at":
// R}}}`, present when R is known: the fact as a hypothesis of the
// goal (`{"hyp_index": i}`) or as an instance entry (`{"key": …}`).
// A fact resident only once the goal is opened, or open, leaves
// ReadAt absent: strip to it, or supply it, then name it.
type RetrieveReading struct {
	Through []string    `json:"through"`
	Go      string      `json:"go"`
	ReadAt  *ReadAtSpec `json:"read_at,omitempty"`
}

// RetrieveWitness is one binder of an applying member pinned by the
// goal or the context, in the member's stated binder order.
type RetrieveWitness struct {
	Binder string `json:"binder"`
	Term   string `json:"term"`
}

// RetrievePremise is one antecedent of an applying member,
// instantiated at the witnesses, with its status (see RetrieveEntry).
type RetrievePremise struct {
	Statement string `json:"statement"`
	Status    string `json:"status"`
	Entry     string `json:"entry,omitempty"`
}

// ---------------------------------------------------------------------------
// Probe — non-destructive lookahead
// ---------------------------------------------------------------------------

// ProbeRequest runs a single tactic against a clone of the named goal and
// reports the outcome. Always non-destructive.
type ProbeRequest struct {
	GoalID   string    `json:"goal_id"`
	Tactic   TacticReq `json:"tactic"`
	BudgetMs int       `json:"budget_ms,omitempty"` // 0 = ProbeDefaultBudgetMs; clamped to ctx deadline
}

// ProbeOutcome is the three-state result of a probe.
type ProbeOutcome string

const (
	ProbeSuccess ProbeOutcome = "success" // tactic applies; subgoals returned
	ProbeFail    ProbeOutcome = "fail"    // strong negative for structural / unification tactics
	ProbeUnknown ProbeOutcome = "unknown" // soft negative; carries Reason
)

// ProbeReason classifies an unknown outcome. Always set when Outcome is unknown.
type ProbeReason string

const (
	ProbeReasonTimeout           ProbeReason = "timeout"
	ProbeReasonUnsupportedTactic ProbeReason = "unsupported_tactic"
	ProbeReasonCandidateTooLarge ProbeReason = "candidate_too_large"
	ProbeReasonIndexNotReady     ProbeReason = "index_not_ready"
	ProbeReasonPanicRecovered    ProbeReason = "panic_recovered"
	ProbeReasonBudgetExhausted   ProbeReason = "budget_exhausted"
)

type ProbeResult struct {
	Outcome ProbeOutcome `json:"outcome"`
	Reason  ProbeReason  `json:"reason,omitempty"` // set when Outcome is unknown

	// Subgoals lists what the move would produce on success, AFTER predicted
	// auto-match has closed any closeable leaves. Empty when the
	// move closes the goal (or when every produced leaf gets auto-matched).
	Subgoals []ProbeSubgoal `json:"subgoals,omitempty"`

	// AutoMatched lists subgoals that the predicted apply would silently
	// close via the same auto-match pipeline that ApplyStep runs
	// (type-instance for `lemma` / `lean_rw`, then plain match by
	// AlphaKey against the registry and the proved siblings). Same shape
	// as StepResult.AutoMatched. Read it together with Effect: an effect
	// of "simplify" with one entry here means "the move would have
	// produced 2 subgoals, but one is auto-closed by the listed entry."
	AutoMatched []AutoMatchedGoal `json:"auto_matched,omitempty"`

	// Effect is one of:
	//   - "close"    — 0 subgoals after auto-match (the move closed the goal)
	//   - "simplify" — exactly 1 subgoal AND it differs structurally from the
	//                  input (hyps added/dropped OR conclusion changed)
	//   - "noop"     — exactly 1 subgoal AND it is α-equivalent to the input
	//                  (no hyps changed, conclusion unchanged). The tactic
	//                  ran without erroring but produced no structural
	//                  progress — distinct from "fail" (which means the
	//                  tactic refused to apply).
	//   - "branch"   — ≥2 subgoals
	// Empty when Outcome != success.
	//
	// The "noop" outcome separates "ran successfully but didn't help" from
	// both "made progress" (simplify) and "refused to apply" (fail) — three
	// distinct cases. See ProbeSubgoal.Changes for the exact
	// per-subgoal structural diff that drives this classification.
	Effect string `json:"effect,omitempty"`

	// Diagnostic carries an explanation when Outcome is fail (most often:
	// the tactic returned not-applicable). Free-form text.
	Diagnostic string `json:"diagnostic,omitempty"`

	// ByCloser names the routes a `by` / `by_induction` probe's close
	// used (apply/conditioning, shaping, cnf prelude (no key), cnf live
	// refute, cnf cached certificate), as the apply response's by_closer
	// diagnostic does — so `probe` no longer answers success/close with
	// no closer at all. Empty for a non-`by` probe or one that did not
	// close.
	ByCloser string `json:"by_closer,omitempty"`
	// Records is the rows the recorder would write for the probed close
	// ("records: 1 key (prop_…), 1 plan" or "records nothing"), the
	// by_records diagnostic's text. Empty for a non-`by` probe or one
	// that did not close.
	Records string `json:"records,omitempty"`
	// Whistle is the by_whistle diagnostic's text: the divergence-whistle
	// cuts the probed close fired, each with the goal it was made at.
	// Empty for a close that fired none.
	Whistle string `json:"by_whistle,omitempty"`

	// EngineFault is set with unknown(panic_recovered): the probed
	// tactic met an engine fault (fault.go), recorded under this id, and
	// the session takes no further move until the record is
	// acknowledged.
	EngineFault *EngineFault `json:"engine_fault,omitempty"`

	ElapsedMs int `json:"elapsed_ms"`
}

// ProbeSubgoal is a lightweight pretty-printed view of a probe-generated
// subgoal. We do not fabricate goal IDs (probe never mutates session state).
type ProbeSubgoal struct {
	Statement string `json:"statement"`
	Depth     int    `json:"depth"`
	// Changes summarizes how this subgoal differs from the probe's input
	// goal — answering "what did the tactic actually do" without forcing
	// the agent to diff PrintProp text. Set on every successful probe.
	Changes GoalChanges `json:"changes"`
}

// GoalChanges is the structural diff from a probe/apply's INPUT goal to
// one of its OUTPUT subgoals. Hyp comparison is by α-equivalence (modulo
// bound-var rename — `Term.AlphaEquals`); conclusion comparison likewise.
//
// Why this exists: `effect: "simplify"` says "something changed" but is
// silent on what. A common case the LLM-agent caller routinely misreads:
// `arith` drops a hyp it identified as a tautology, leaving the conclusion
// unchanged — the printed statement looks identical to the agent, who
// concludes "no progress" when the tactic did meaningful work. Surfacing
// (hyps_dropped: 1) inline at the subgoal disambiguates this without
// requiring a diff of two PrintProp strings.
//
// When all three fields are zero, the produced subgoal is α-equivalent to
// the input — `Effect == "noop"`.
type GoalChanges struct {
	HypsAdded         int  `json:"hyps_added"`
	HypsDropped       int  `json:"hyps_dropped"`
	ConclusionChanged bool `json:"conclusion_changed"`
}

// IsNoop reports whether the input goal and the output subgoal are
// α-equivalent (no hyp added, no hyp dropped, conclusion unchanged).
func (c GoalChanges) IsNoop() bool {
	return c.HypsAdded == 0 && c.HypsDropped == 0 && !c.ConclusionChanged
}

// ---------------------------------------------------------------------------
// BatchApply
// ---------------------------------------------------------------------------

type BatchMode string

const (
	FirstSuccess BatchMode = "first_success"
	CompareAll   BatchMode = "compare_all"
)

type BatchApplyRequest struct {
	GoalID  string      `json:"goal_id"`
	Tactics []TacticReq `json:"tactics"`
	Mode    BatchMode   `json:"mode"`
}

// BatchApplyResult is one result per tactic, in order. A tactic that
// met an engine fault ends the batch: its result carries the fault,
// and each later tactic's result says it was not run.
type BatchApplyResult struct {
	Results     []StepResult `json:"results"`
	WinnerIndex int          `json:"winner_index"` // -1 if none succeeded
}

// ---------------------------------------------------------------------------
// Diagnostics
// ---------------------------------------------------------------------------

type DiagnosticType string

const (
	DiagTypeMismatch       DiagnosticType = "type_mismatch"
	DiagUnificationFailure DiagnosticType = "unification_failure"
	DiagMissingPremise     DiagnosticType = "missing_premise"
	DiagPremisePartial     DiagnosticType = "premise_partial"
	DiagPremiseNoMatch     DiagnosticType = "premise_no_match"
	DiagTacticFailure      DiagnosticType = "tactic_failure"
	DiagTimeout            DiagnosticType = "timeout"
	// DiagAutoTypeInstances is informational (attached to SUCCESSFUL
	// StepResults too): a simp_with polymorphic rule without explicit
	// type_specialize was auto-expanded to multiple goal type-instances,
	// a >cap instance count was truncated, or a duplicate resolved rule
	// was deduplicated. Names each instance so the agent sees exactly
	// what the auto-adaptation did.
	DiagAutoTypeInstances DiagnosticType = "auto_type_instances"
	// DiagRuleShape is informational (attached to SUCCESSFUL StepResults
	// too): a simp_with rule carries a clause the driver reads as a
	// closure rule — an atom under a Horn antecedent, which discharges
	// side conditions and rewrites nothing (tactic.ClosureSimpClauses).
	// Names the clause so a later no-progress failure is read at the
	// rule, not at the goal.
	DiagRuleShape DiagnosticType = "rule_shape"
	// DiagByEconomy is informational, attached to a SUCCESSFUL `by`: a
	// leaf the close sent to the refuter closes under a plain Basic(),
	// and the same `by` under by_shape:{normalized:true} (Go:
	// By(Normalized, …)) was run and closes on fewer rows — the
	// refuter, and the key a recording of this spelling would write,
	// is avoidable. The economy audit's first probe
	// (proof.BySpec.Report), read before any blob is written; the
	// recorder's audit stays the oracle for what a spelling costs.
	DiagByEconomy DiagnosticType = "by_economy"
	// DiagByCloser names the successful attempt's actual closing routes.
	DiagByCloser DiagnosticType = "by_closer"
	// DiagByRecords is informational, attached to a SUCCESSFUL `by`: the
	// rows the recorder would write for this close — the certificate keys
	// its refutes wrote (a live refute) or read (a cached certificate),
	// and the conditioning plan keys the stage persisted or read — or "records
	// nothing" for a keyless close (the apply rung, a shaping, a prelude
	// close, arith/chase). The author reads this before a blob is
	// written, where today only the recorder's dry run says it; it is the
	// session's own close, so where the recorder's route differs the dry
	// run stays the oracle (see xugo-engine.md, the `by` row).
	DiagByRecords DiagnosticType = "by_records"
	// DiagByWhistle is informational, attached to a SUCCESSFUL `by` or
	// `by_induction`: the close fired the divergence whistle — a case
	// analysis refused at its breadth backstop, a simplification or a
	// rewrite cut as divergent — and closed on what its search had left.
	// It states each cut and the goal it was made at. The close stands
	// in the session; a cut is a function of the goal, so the member's
	// replay meets it again, and the recorder refuses a member whose
	// replay fires the whistle (xugo-engine.md, "The recorder's two
	// gates"). Read here, the spelling can still be changed before any
	// Go is written.
	DiagByWhistle DiagnosticType = "by_whistle"
	// DiagContextChanged names hypotheses rewritten or removed by unfolding.
	DiagContextChanged DiagnosticType = "context_changed"
	// DiagNumeralDomain says a claim or lemma text of the step states a
	// relation between `&` numerals alone: the type it was read at, that
	// the session's `&` domain decided it and nothing in the text, and
	// how to state it at another type (dsl.CodeNumeralDomain). The text
	// is read as it stands; the diagnostic is what its echo does not
	// show, since a numeral prints the same at every type.
	DiagNumeralDomain DiagnosticType = "numeral_domain"
	// DiagWrittenRedex says the claim of an `assert` applies a λ in
	// place, `(λx. t)(a)`, and is asserted with that redex in it: each
	// such application and what it reduces to. The claim is read as it
	// stands and the step is not refused. A law taken at a λ hands its
	// instance over reduced (tactic.InstanceNormal), so the reduced term
	// is what a premise of that instance spells and what a claim that is
	// to meet it should state.
	DiagWrittenRedex DiagnosticType = "written_redex"
	// DiagSetEquation says a `funext` made an equation between sets
	// pointwise: its result holds a set-builder applied to the point,
	// which no move reads as a membership, where the rewrite by
	// set_basic.Extension leaves memberships. The step stands; a
	// set-builder is the one side that says its equation is between
	// sets, so an equation between set variables or constants, which
	// funext leaves as applications too, carries no such line.
	DiagSetEquation DiagnosticType = "set_equation"
	// DiagEngineFault is the diagnostic of a tactic that met an engine
	// fault (fault.go) — a defect of the engine, where a tactic_failure
	// is a move that did not apply. It carries no repair hint.
	DiagEngineFault DiagnosticType = "engine_fault"
)

type Diagnostic struct {
	Type        DiagnosticType `json:"type"`
	Message     string         `json:"message"`
	GoalID      string         `json:"goal_id,omitempty"`
	RepairHints []RepairHint   `json:"repair_hints,omitempty"`
}

// RepairHint is a suggestion for fixing a failed derivation. It is a
// JSON-safe wire type: only human-readable description text is emitted.
// Concrete prover.Action values are intentionally NOT embedded here — they
// carry core.ConstTerm / core.Prop with unexported fields that would cause
// encoding/json to panic.
type RepairHint struct {
	Description string `json:"description"`
}
