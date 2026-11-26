/** File: macro.go
 *
 * The compound Macro layer: interface Macro and the ONE macro that is
 * still a primitive, AutoExpand (the `auto` closer — simplify, denote,
 * refute every residual leaf), plus the closers built on it
 * (CloseByAuto, CloseByCNFRefute) and the definition helpers
 * (ApplyDefExpand, TryCloseByConstDef, ConstDefDefiningHints).
 *
 * A Macro operates on a GoalStackNode (so it can see the whole proof
 * tree), orchestrates one or more Steps, and expands the node such that
 * it has at most one unproved leaf. It returns a bool indicating whether
 * the application is successful. Both Macro and Step satisfy the umbrella
 * Action interface (action.go).
 *
 * What is deliberately NOT here: Action macros that wrap a ministep
 * with a post-`_TrivialSimplify` on a child (InductionMacro,
 * ByCaseMacro, ExistentialConstDefMacro, LemmaMacro, DefMacro, …) and a
 * macro serialization to replay them from. A proof records ministeps only
 * (DetailedProofProto): the chapter verbs (a.Induct, a.Cases, Cite,
 * Unfold, ExistentialConstDefStep) and the session tactics (`induction`,
 * `case_split`, `def_expand`, `lemma`) both record the BARE step, and a
 * simplification of a child is its own recorded step — a session
 * `simplify`, a Go `TrivialSimplify()` — so the two surfaces record one
 * tree and emit renders it without knowing which side wrote it. A
 * search probe that wants the simplified residual runs the step and the
 * simplification itself (probeLemma below).
 */

package proof

import (
	"context"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
)

const (
	_AUTO_EXPAND = "Auto Expand."
)

// Macro transforms a node to at most 1 unproved child.
// returns whether the application works.
type Macro interface {
	String() string
	Apply(*GoalStackNode) bool

	// applyAction makes every concrete Macro type satisfy the umbrella
	// Action interface (see action.go). Delegates to leaf.Apply internally.
	applyAction(s *Script, root *GoalStackNode)
}

type AutoExpand struct {
	env *ProverEnv
	Ctx context.Context
}

func (AutoExpand) String() string { return _AUTO_EXPAND }

func (env *ProverEnv) AutoExpand() Macro { return AutoExpand{env: env, Ctx: context.Background()} }

// AutoExpandWithCtx creates an AutoExpand action with a cancellable context.
// When ctx is cancelled, in-flight CNF refutation is interrupted.
func (env *ProverEnv) AutoExpandWithCtx(ctx context.Context) Macro {
	return AutoExpand{env: env, Ctx: ctx}
}

// Apply closes n completely or reports false; it never leaves n with an
// open leaf it counts as progress. On false, n is left part-expanded —
// the pipeline's steps and whichever leaves did close stay attached — so
// a caller that goes on using the node passes a fresh one or a clone
// (TryExpandPlan runs it on a fresh node and returns a plan only on
// success).
func (action AutoExpand) Apply(n *GoalStackNode) bool {
	ctx := action.Ctx
	autoExpandPipeline(n, ctx)
	// NOTE: `_Arith{}` is deliberately NOT in this pipeline. A member's
	// replay uses CloseByAuto → env.AutoExpand().Apply, and `_Arith` reads
	// the corpus-backed `NatLemmaBundle` whose fields' promise builders run
	// members' Builds. Running arith inside AutoExpand would risk re-
	// forcing a bundle promise the current Build is already mid-force on
	// (deadlock on the promise cell's mutex / on buildMu). The agent-facing
	// "auto" engine move tries `_Arith` separately at the dispatch layer
	// (engine.go) before AutoExpand — that path is never reached by corpus
	// replay, so the cycle hazard is structurally avoided. (The
	// conditioning ladder below is safe here: its stages are
	// bundle-free — e-matching is pure planning, denotes and strips are
	// kernel steps — so no promise cell is ever re-entered.)
	for leaf := range n.unsolvedLeavesIter() {
		if ctx.Err() != nil || !closeAutoLeaf(action.env, ctx, leaf) {
			return false
		}
	}
	Assert(n.Proved())
	return true
}

// autoExpandPipeline is AutoExpand's pre-refute pipeline. The
// conditioning ladder lives per-leaf in the refute loop, behind rung 1,
// so the leaves this pipeline produces are the BARE forms every
// recorded AutoExpand keyed.
// CondRewrite first: eliminate/push COND so downstream tactics (basic
// rewrites, CNF refuter) see goals in standard propositional form.
func autoExpandPipeline(n *GoalStackNode, ctx context.Context) {
	n.runStepOnLeaves(ctx, _CondRewrite{})
	n.runStepOnLeaves(ctx, _BasicTactic{})
	n.runStepOnLeaves(ctx, _AutoDenote{sizeThreshold: _DENOTE_SIZE_THRES})
	n.runStepOnLeaves(ctx, _AutoDenote{hilbert: true})
	n.runStepOnLeaves(ctx, _BasicTactic{})
}

// closeAutoLeaf closes one AutoExpand residual through the door's
// conditioning ladder (it mirrors _ByStep.applyLadder and the raw set_tac
// door).
//
// Rung 1 refutes the bare leaf with CNF cache-only semantics: every
// AutoExpand recorded before this door conditioned keeps closing on
// its recorded keys — the macro re-runs its whole pipeline at replay
// (MacroProto_AutoExpand carries no internals), so the certificate
// keys are the only recorded artifact this loop owns. Then, LIVE
// ONLY, the bare refute runs with full semantics (see the rung-order
// note in the body — bare keeps first claim on the shared search
// budget). Last, the conditioned attempt (grounding of wide ∀-hyps, the
// manual's S4 — the session-level `ematch` verb become a stage — and
// comprehension denotation, the CnfRefute matrix column): it runs on
// a THROWAWAY stack first so a failure leaves the real leaf
// untouched, then commits by re-running the same deterministic
// sequence on the real leaf — existing step protos only, so the tree
// stays serializable (DetailedProofProto walks macro internals). At
// strict replay the order is probe → conditioned (plans + recorded
// certificates, zero live search), so conditioned-recorded rows
// replay exactly.
func closeAutoLeaf(env *ProverEnv, ctx context.Context, leaf *GoalStackNode) bool {
	if func() (ok bool) {
		defer func() { rungFailure(recover()) }() // the probe's MISS panic is its graceful failure
		return leaf.runStep(_CNFRefute{env: env, ctx: withCNFCacheOnlyProbe(ctx)})
	}() {
		return true
	}
	// LIVE RUNG ORDER — bare BEFORE conditioned, the list_reverse of the By
	// ladder, and measured, not stylistic: auto is a searcher whose ctx
	// deadline is SHARED across a whole cascade of close attempts, so a
	// conditioned attempt that fails does not merely cost its own ≤2×
	// (the By ruling's accepted failure-path price) — it drains the
	// budget of every later attempt in the same search
	// (TestEMatch_GroundsMembershipKit went red exactly this way when
	// this door ran conditioned-first). And unlike the By door, no
	// measured wall is one the conditioned form of this door
	// deletes (the denotation face was already absorbed by the pipeline's
	// size-denote; probed S4 chain shapes close bare) — so bare keeps
	// first claim on the live budget, and conditioning is the
	// last-chance extra on leaves that were failing anyway.
	if !env.RequireCNFCacheHit {
		if leaf.runStep(_CNFRefute{env: env, ctx: ctx}) {
			return true
		}
	}
	probeOK, changed := autoConditionedRefute(env, ctx, CreateGoalStack(leaf.Goal))
	if !probeOK {
		// changed=false means conditioning had nothing to say and the
		// probe refuted the identical bare clause set — which the live
		// rung above already answered. Either way the leaf stays open.
		_ = changed
		return false
	}
	// The committing re-run is the sequence the probe stack has just
	// run to its end, so it takes no deadline: one that passed between
	// the two runs would cut the stage short here and read as a stage
	// that is not deterministic.
	if ok, _ := autoConditionedRefute(env, context.WithoutCancel(ctx), leaf); !ok {
		panic("AutoExpand: the conditioned close succeeded on the probe stack " +
			"but not on the committing re-run — the conditioning stage is not " +
			"deterministic (G2)")
	}
	return true
}

// autoConditionedRefute is one conditioned close attempt over the
// subtree rooted at root (a throwaway stack on the probe pass, the
// real leaf on the commit pass — the same pure function either way).
// Plans persist only on success, and only from the probe pass:
// the commit pass reads them back from the store, which is itself the
// determinism the panic above guards. changed reports whether the
// stage transformed the leaf at all — false means the refuted clause
// set was the BARE one, so the caller must not pay a rung-3 re-refute
// of the identical sequent.
func autoConditionedRefute(env *ProverEnv, ctx context.Context, root *GoalStackNode) (ok, changed bool) {
	bareKey := ""
	if l := byWorkingLeaf(root, nil); l != nil {
		bareKey = string(l.Goal.AlphaKey())
	}
	c := &conditioner{env: env, ctx: ctx, s4: &byS4State{}}
	// The pruned leaf: live, the door refutes the bare leaf, every source
	// wide, before it comes here (closeAutoLeaf).
	c.conditionLeaf(root, conditionOpts{ground: true, prune: true, denote: true, recordParts: true, readMemberships: true, readRecords: true})
	if c.cut != "" {
		// The context ended the stage part way: the leaf is not the
		// conditioned one, and a close of it is not this attempt's.
		return false, true
	}
	leaf := byWorkingLeaf(root, nil)
	if leaf == nil {
		return root.Proved(), true
	}
	changed = string(leaf.Goal.AlphaKey()) != bareKey
	if !changed {
		// Conditioning had nothing to say (no split, no strip, no
		// grounding, no denote): this attempt's clause set IS the bare
		// one the live rung already refuted. Answering it again buys
		// nothing and doubles the failing-leaf cost — decline instead.
		return false, false
	}
	if !leaf.runStep(_CNFRefute{env: env, ctx: ctx}) {
		return false, changed
	}
	c.persistConditionPlans()
	return true, changed
}

// CloseByAuto runs the "Normalize→⊤ first, then AutoExpand" closure on
// n: a goal whose normal form is ⊤ closes by _TrivialNormalizedStep
// (cheap; no CNFRefute is invoked when it fires — the close goes through
// prop.DerivesTrue), and on a miss it falls through to env.AutoExpand.
// Script.CloseByAuto (a Step expression inside a chapter body) runs this;
// the fluent CloseByAuto node method runs the same two steps.
//
// Returns true iff n is fully closed afterwards.
func CloseByAuto(n *GoalStackNode, env *ProverEnv) bool {
	if n.runStep(_TrivialNormalizedStep{}) {
		return true
	}
	return env.AutoExpand().Apply(n)
}

// CloseByCNFRefute runs the bare `_CNFRefute` ministep on n — exactly what a
// member replays for a recorded `cnf_refute` step (emitted as `CnfRefute()`):
// `env.tryCNFRefute(n.Goal)` directly, with NO AutoExpand preprocessing.
// Returns true iff it closed n.
//
// emit's CNF-cache collection MUST use this (not CloseByAuto) for Detailed
// CnfRefute targets. CloseByAuto prepends AutoExpand's denote/basic/
// cond-rewrite pass, which can transform the recorded CnfRefute goal into a
// different (e.g. no-longer-trivially-refutable) shape — so the goal fed to
// the refuter, and hence the cache key it reads/writes, diverges from what
// replay's bare ministep computes. That divergence made recorded proofs
// collect a CNF key replay never looks up (and demand a proof for a refute
// replay discharges trivially).
func CloseByCNFRefute(n *GoalStackNode, env *ProverEnv) bool {
	return n.runStep(_CNFRefute{env: env, ctx: context.Background()})
}

// lemmaSourceKey returns the key `lemma` (the pre-adaptation form
// passed into ApplyLemma / ApplyLeanRw / probeLemma) is resolved by at
// emit. Registry entries — and the registry's const-def index — are
// keyed by the AlphaKey of the NORMALIZED statement, so we normalize
// before hashing.
//
// Why normalize: callers reach these entry points with the lemma in
// two distinct shapes:
//
//  1. A cite of a registry entry (by name or key) serves the entry's
//     statement; the entry's own key is that statement's normalized
//     AlphaKey.
//
//  2. A def-equation cite passes `c.Meta().DefThm()` — the raw kernel
//     def_thm in λ-equation shape `⊢ c = λ.../body`; the const-def
//     index keys the def under its normalized form.
//
// Using `lemma.AlphaKey()` directly would record a key no entry carries
// whenever the served form is not already normal — always on path 2.
func lemmaSourceKey(lemma Prop) core.PropKey {
	normalized, _ := Normalize(lemma)
	return normalized.AlphaKey()
}

// LemmaSourceKey is the exported alias of lemmaSourceKey. Callers
// outside the prover package (the engine layer, in particular) compute
// the key of a polymorphic source lemma before applying an
// agent-supplied type substitution, so the recorded
// `polymorphicSourceKey` still points at the source entry — not at the
// post-σ form, whose AlphaKey keys no entry.
func LemmaSourceKey(lemma Prop) core.PropKey {
	return lemmaSourceKey(lemma)
}

// probeLemma is ApplyLemma (tactic_apply.go) followed by a
// residual-child simplification: the residual (child(1), present iff
// LemmaTactic produced 2 subgoals) runs _TrivialSimplify, so a PROBE
// reads the residual the way a proof would after its own simplify
// step. It exists for the search-side probes only (TryLemmaTactic —
// the derivation checks and the registry-repair recommender ask "does
// this premise reduce the goal, and to what"), on a
// throwaway node that records nothing. A recording surface — the
// session's `lemma` tactic, a chapter's Cite — applies the bare step
// and records a simplification, when it wants one, as its own step.
//
// The type-adaptation boundary lives in ApplyLemma; do not duplicate
// adaptLemmaIfPolymorphic here.
func probeLemma(n *GoalStackNode, lemma Prop) bool {
	Assert(lemma != nil)
	if !ApplyLemma(n, lemma) {
		return false
	}
	// LemmaTactic invariant: child(0) is the lemma itself (possibly
	// type-adapted), child(1) (if present) is the residual. We don't
	// re-assert child(0).Goal.AlphaEquals(adapted) here because
	// `adapted` is not accessible — ApplyLemma owns the adaptation —
	// but the >=1 child structural check + LemmaTactic's own
	// contract make this safe.
	Assert(len(n.children) >= 1)
	if len(n.children) > 1 {
		Assert(len(n.children) == 2)
		n.child(1).runStep(_TrivialSimplify{})
	}
	return true
}

// ApplyDefExpand is the agent-facing entry point for the def_expand
// tactic. Pure rewrite semantics: no hypMatch fallback.
//
// It commits a SINGLE _DefExpandStep composite, whatever kind of
// definition c has, whose wire tag records only c. Record and replay
// share computeDefExpandSubGoals — the composite's apply IS the
// dispatch driver, so the choice between TryDefExpand and the general
// LeanRw cannot drift between record and replay: same inputs → same
// subgoals → same emit. No LeanRw+AxiomDef+TrivialSimplify subtree is
// materialized at record time (see step_composite.go). A choice
// constant (`c = εx.P(x)`) takes the same step: the opened ε-term
// closes against a resident existence through the tidy, as the
// chapter's Unfold does; the reading that keeps c folded and hands its
// two obligations over as cases is the chapter step
// ExistentialConstDefStep, which no session command records.
func ApplyDefExpand(n *GoalStackNode, c ConstTerm) bool {
	return n.runStep(_DefExpandStep{constTerm: c})
}

// ApplyByCase is the session `case_split` tactic's step: the BARE
// _ByCaseStep, two children `φ ⊢ G` and `¬φ ⊢ G` — the same record the
// chapter verb a.Cases (ByCaseStep) makes. The retired ByCaseMacro
// followed the split with a _TrivialSimplify on the `¬φ` branch that
// only the session saw; a session wanting that shape records it as its
// own `simplify` step, as a Go author writes `TrivialSimplify()`.
func ApplyByCase(n *GoalStackNode, caseTerm core.Term) bool {
	return n.runStep(_ByCaseStep{caseTerm: caseTerm})
}

// ApplyInduction is the session `induction` tactic's step: the BARE
// _InductionStep, one child per case of the principle (`P(base)`,
// `P(n) ⊢ P(suc n)`, …) — the same record the chapter verb a.Induct
// (Script.InductStep) makes. The retired InductionMacro ran
// _TrivialSimplify on every step child, which on a `¬`/`≠` goal
// contraposed it (`factorial(n) ≠ 0 ⊢ factorial(suc n) ≠ 0` arrived as
// `factorial(suc n) = 0 ⊢ factorial(n) = 0`) and on an implication moved the
// antecedent into the hyps — a shaping the Go door never made, so a
// session record and its chapter twin disagreed on every such
// induction. The step case is now handed over as the principle states it;
// `by` takes it as is.
func ApplyInduction(n *GoalStackNode, inductVar core.VarTerm, template *tactic.InductionTemplate) bool {
	if inductVar.IsZero() || template == nil {
		return false
	}
	return n.runStep(_InductionStep{inductVar: inductVar, template: template})
}

// TryCloseByConstDef closes n iff its goal IS the defining equation of some
// constant occurring in it — i.e. the goal is `∀x. c(x) = <def>(x)` (any
// arity, modulo type-instantiation), the residual a `congr`/`funext` reduction
// of a const's pointwise definitional equation leaves behind. It closes via
// `_AxiomDefStep{c}` — the SAME closer + recording (`AxiomDef`) + dep-extraction
// (Type-1: no dep; Type-2: DefSource) + emit path that `def_expand` already
// uses — so it adds no new record/replay surface.
//
// This makes a const's own definitional equation an O(small) "known fact" the
// way a registry entry is: the session's `known` closer calls it when its
// theorem-cache lookups miss. The candidate consts are exactly those
// in the goal (`CollectDefinableConsts` — a tiny set); `_AxiomDefStep`'s
// internal `IsTypeMatchOf` + `IsStronger` gate is the soundness check, so a
// non-def-equation goal (a `+` term, nat_mod inside a larger statement) is a clean
// no-op on each candidate — `runStep` leaves n untouched when the step's
// `apply` returns nil. Type matching (for polymorphic consts) is handled by
// `makeAxiomDefSubGoals` (`prop.IsTypeMatchOf`); no normalize/SkeletonKey index
// needed. Returns true iff some candidate closed n.
func TryCloseByConstDef(n *GoalStackNode) bool {
	for _, c := range ext.CollectDefinableConsts(n.Goal) {
		if getDefThm(c).IsZero() {
			continue
		}
		// _AxiomDefStep (via makeAxiomDefSubGoals) handles both the clean
		// type-instance case and the normalize-bridge case (conjunct /
		// equality reorder, e.g. a congr-reduced `c = f`); returns nil — a
		// clean no-op leaving n untouched — when the goal isn't c's def axiom.
		if n.runStep(_AxiomDefStep{c}) {
			return true
		}
	}
	return false
}

// ConstDefHint is one defining-equation fact to surface for a constant: the
// Prop plus a short Role tag describing what it is.
type ConstDefHint struct {
	Role string // "def" (c = f) | "typedef_abs" (abs(rep a)=a) | "typedef_rep" (P(r) ⇔ rep(abs r)=r)
	Prop Prop
}

// ConstDefDefiningHints returns the defining-equation fact(s) worth surfacing
// for c as a `def_eq` structural hint — so the agent is reminded "this is how c
// is defined; maybe it's useful." Covers BOTH const-introduction kinds, whose
// definitions live in different places and never appear as the agent's
// def_expand output:
//
//   - NewConstDef Hilbert/ε const (nat_mod, nat_div, HD, +, *): the point-free
//     `c = εx.…` equation, from the const-meta def thm (getDefThm). This is
//     const-meta-only — NOT a registry entry — and the def_expand tactic only
//     surfaces the weaker property P(c), so without this hint the agent never
//     sees `c = f`.
//
//   - NewTypeDef abs/rep const (mk_option, mk_prod, …): the type-definition
//     axioms `abs(rep a) = a` and `P(r) ⇔ rep(abs r) = r`, recovered via
//     meta.TypeDefExpand on the (unproved) defSource Prop — text only, no
//     proved thm needed. These ARE registry entries (the type definition's
//     <Name>Retraction / <Name>Membership), but an agent working with the
//     constants has no reason to go dig them out; surfacing them here is the
//     reminder. Their shape is tricky (not `c = …`), which makes the reminder
//     more valuable, not less.
//
// Returns nil when c has no recoverable definition (basic consts =, ε, or a
// NewConstDef whose def thm is absent). Hilbert reports whether the NewConstDef
// const is ε-shaped (informational; both ε and λ NewConstDefs are surfaced).
func ConstDefDefiningHints(c ext.ConstTerm) (hints []ConstDefHint, hilbert bool) {
	meta := c.Meta()
	if meta.IsTypeDefAbs() || meta.IsTypeDefRep() {
		src := meta.DefSource()
		if src == nil {
			return nil, false
		}
		// TypeDefExpand returns plain Props for an unproved source (we only
		// need the statement text for the hint, not a proved thm).
		out1, out2 := meta.TypeDefExpand(src)
		return []ConstDefHint{
			{Role: "typedef_abs", Prop: out1},
			{Role: "typedef_rep", Prop: out2},
		}, false
	}
	thm := getDefThm(c)
	if thm.IsZero() {
		return nil, false
	}
	return []ConstDefHint{{Role: "def", Prop: thm}}, prop.IsHilbertConstDef(c)
}
