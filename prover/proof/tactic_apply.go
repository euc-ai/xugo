// tactic_apply.go — the tactic application functions the engine drives.
//
// These functions let the engine package apply individual tactics on
// GoalStackNode clones without importing internal ministep types.
// Programmatic search continues to use Action.Apply directly.

package proof

import (
	"fmt"

	"context"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/euc-ai/xugo/utils"
)

// ---------------------------------------------------------------------------
// Composite tactics
// ---------------------------------------------------------------------------

// ApplySimplify runs BasicTactic on the node, then cleans up unsolved leaves
// with AutoDenote and TrivialSimplify. Returns true if BasicTactic succeeded
// (even if some leaves remain unsolved).
//
// ctx is polled between mini-step stages and between leaves so a cancelled
// ctx stops work promptly.
func ApplySimplify(ctx context.Context, n *GoalStackNode) bool {
	if !n.runStep(_BasicTactic{}) {
		return false
	}
	n.runStepOnLeaves(ctx, _AutoDenote{sizeThreshold: _DENOTE_SIZE_THRES})
	n.runStepOnLeaves(ctx, _AutoDenote{hilbert: true})
	n.runStepOnLeaves(ctx, _TrivialSimplify{})
	return true
}

// ---------------------------------------------------------------------------
// Single-step tactics
// ---------------------------------------------------------------------------

// ApplyRefute runs CNF refutation on the node. Closes the goal or returns false.
func ApplyRefute(n *GoalStackNode, env *ProverEnv, ctx context.Context) bool {
	return n.runStep(_CNFRefute{env: env, ctx: ctx})
}

// ApplyKnown checks the ThmCache for a proved theorem matching the goal.
// Closes the goal if found, returns false otherwise.
//
// Strict cache-lookup semantics: trivial-true goals are NOT closed here —
// the tier lookups refuse to match them, so this returns false for a goal
// that happens to normalize to ⊤. The engine's `auto` tactic /
// `_TrivialNormalized` ministep handle that case; conflating them with
// `known` would surprise agents that pick `known` specifically to test
// cache contents.
//
// The RECORDED step depends on which cache tier hit — α-key/normalized
// hits record _KnownThmStep, type-instance hits record _TypeInstStep
// with the polymorphic source. See commitFoundThmStep (try.go) for why
// this distinction is load-bearing for emit/replay.
func ApplyKnown(n *GoalStackNode, cache *ThmCache) bool {
	return commitFoundThmStep(cache, n)
}

// ApplyKnownWithKey is ApplyKnown for callers that resolved the goal's
// registry identity themselves (engine auto-match, the sourceKey-channel
// closes). `entryKey` — the key of the registry entry whose statement is
// the goal's normalize-α class — is stamped onto the recorded
// _KnownThmStep so emit's leaf resolution reads the entry directly
// instead of re-deriving the key from the session-form payload. The
// stamp is dropped when the committed payload is not the goal's own
// class (see commitFoundThmStepWithKey), so a mismatched claim degrades
// to ApplyKnown, never to a wrong dep.
func ApplyKnownWithKey(n *GoalStackNode, cache *ThmCache, entryKey core.PropKey) bool {
	return commitFoundThmStepWithKey(cache, n, entryKey)
}

// ApplyCiteKnown closes n outright by a known theorem stronger than
// its goal — the Cite verb's bare close at a session node, recording
// the KnownThm leaf whose key emit resolves. `stronger` must be an
// honest certificate or promise. The `define typedef:` door closes the
// composite's inhabitation child with the proved section's promised
// theorem this way.
func ApplyCiteKnown(n *GoalStackNode, stronger Prop) bool {
	if stronger == nil || !(stronger.Proved() || core.IsPromised(stronger)) {
		return false
	}
	if !IsStronger(stronger, n.Goal) {
		return false
	}
	return n.runStep(_KnownThmStep{strongerGoal: stronger})
}

// ApplyCiteReading closes n outright by a structure law read at an
// instance — the derived theorem `cert` with the record of what it was
// read from — at the Cite verb's two closing tiers (fact.go, Cite): the
// certificate stronger than the goal, or the goal the certificate's
// statement modulo Normalize (normalizeTierCloser). The recorded
// KnownThm carries the reading, so emit spells the cite
// `Cite(Law.Read(instance))`; the session's `lemma {key, read_at}`
// records it on the goal and on its install's claim child. Returns
// false, nothing recorded, when neither tier closes the goal.
func ApplyCiteReading(n *GoalStackNode, cert Prop, record *ReadingRecord) bool {
	if record == nil {
		panic("ApplyCiteReading: a reading's cite without the record of what it was read from")
	}
	if (cert.Proved() || core.IsPromised(cert)) && IsStronger(cert, n.Goal) {
		return n.runStep(_KnownThmStep{strongerGoal: cert, reading: record})
	}
	if stronger := normalizeTierCloser(n.Goal, cert); stronger != nil {
		return n.runStep(_KnownThmStep{strongerGoal: stronger, equivalentThm: cert, reading: record})
	}
	return false
}

// ApplyTrivialNormalized closes the node when its goal's normalized form has
// conclusion ⊤ (i.e. the hypotheses fold the conclusion into a tautology).
// Returns true on close, false if the normalize doesn't reach ⊤.
//
// Use this from producers (e.g. engine auto-match) that need to close a leaf
// whose normalized key is the ⊢⊤ class every tautology shares — going through
// _TrivialNormalizedStep avoids recording a phantom dep on whichever cached
// theorem sits in that equivalence class.
func ApplyTrivialNormalized(n *GoalStackNode) bool {
	return n.runStep(_TrivialNormalizedStep{})
}

// ApplyTypeInst closes the node when its goal is a type instantiation of the
// provided polymorphic source theorem. The source must be an honest
// certificate or IOU — Proved() or core.IsPromised() — never a bare unproved
// Prop: the trust decision belongs to the caller, who knows the source's
// registry identity and can promise-back it (engine: corpusBackedInjection —
// a real forceable corpus promise, or a fail-at-force promise that surfaces
// a missing build loudly at replay). The former core.TestThm lift here
// minted a forged kernel cert for whatever Prop the caller passed.
func ApplyTypeInst(n *GoalStackNode, source Prop) bool {
	return ApplyTypeInstWithKey(n, source, "")
}

// ApplyTypeInstWithKey is ApplyTypeInst for callers that know which
// registry entry `source` was loaded from. `entryKey` is stamped onto
// the recorded _TypeInstStep so emit's leaf resolution reads the entry
// directly instead of re-deriving the key from `source` — same
// contract as ApplyKnownWithKey. Pass "" when the source has
// no registry identity (behaves exactly like ApplyTypeInst).
func ApplyTypeInstWithKey(n *GoalStackNode, source Prop, entryKey core.PropKey) bool {
	if source == nil {
		return false
	}
	if source.NumHyps() != 0 {
		return false
	}
	Assert(source.Proved() || core.IsPromised(source))
	return n.runStep(_TypeInstStep{source: source, sourceEntryKey: entryKey})
}

// TypeInstCloses reports whether ApplyTypeInst from source closes goal:
// the step's own reading of "goal is a type instance of source", for a
// caller that chooses among sources before it commits one. It records
// nothing.
func TypeInstCloses(source, goal Prop) bool {
	return source.NumHyps() == 0 && _TypeInstStep{source: source}.apply(goal) != nil
}

// ApplyLemma applies a lemma to the goal via LemmaTactic.
//
// When the lemma is polymorphic, try both the original lemma and the
// type-adapted candidate against the current goal, then commit the
// better tactic result. This keeps replay aligned with record-time
// success even when two Equals-equal lemma representations expose
// different polymorphic const instantiations to the matcher.
func ApplyLemma(n *GoalStackNode, lemma Prop) bool {
	step, subGoals := chooseTypeAdaptedStep(
		n,
		lemma,
		func(lemma Prop, sourceKey core.PropKey) _Step {
			return _LemmaTactic{lemma: lemma, polymorphicSourceKey: sourceKey}
		})
	return n.commitStep(step, subGoals)
}

// ApplyLemmaPreserve applies a lemma via LemmaPreserveTactic — the
// hypothesis-preserving variant backing the agent-facing session
// `lemma` dispatch. Same multi-strategy chain as ApplyLemma, but a
// result that would rewrite or drop a pre-existing goal hyp is
// downgraded to a plain "add the lemma's conclusion as a new hyp"
// (no simplifyNewGoal whole-context re-normalization) — the fix for
// `lemma` re-normalizing the hyp context. Same polymorphic-lemma
// type-adaptation selection as ApplyLemma; records a
// `_LemmaPreserveTactic` ministep (proto tag `lemma_preserve`) so
// replay re-runs the preserving chain.
func ApplyLemmaPreserve(n *GoalStackNode, lemma Prop) bool {
	step, subGoals := chooseTypeAdaptedStep(n, lemma, lemmaPreserveStep)
	return n.commitStep(step, subGoals)
}

func lemmaPreserveStep(lemma Prop, sourceKey core.PropKey) _Step {
	return _LemmaPreserveTactic{lemma: lemma, polymorphicSourceKey: sourceKey}
}

// installLemmaPreserveUntil is ApplyLemmaPreserve — with exact,
// ApplyLemmaPreserveExactWithSource at no source key — with the
// preserving chain abandoned once ctx is done
// (tactic.LemmaPreserveTacticUntil). The step it commits is
// _LemmaPreserveTactic, the one a replay runs with no deadline. cut
// reports the abandon: the node is then left as it was, and its caller
// does not go on as if the lemma did not install.
func (n *GoalStackNode) installLemmaPreserveUntil(ctx context.Context, lemma Prop, exact bool) (installed, cut bool) {
	// The selection applies up to two candidates; once one is abandoned
	// the other is not run, and what the selection returns is not read.
	apply := func(step _Step, goal Prop) *SubGoals {
		if cut {
			return nil
		}
		var sg *SubGoals
		sg, cut = tactic.LemmaPreserveTacticUntil(ctx, step.(_LemmaPreserveTactic).lemma, goal)
		return sg
	}
	var step _Step
	var subGoals *SubGoals
	if exact {
		step = lemmaPreserveStep(lemma, "")
		subGoals = apply(step, n.Goal)
	} else {
		step, subGoals = chooseTypeAdaptedStepBy(n, lemma, lemmaPreserveStep, apply)
	}
	if cut {
		return false, true
	}
	return n.commitStep(step, subGoals), false
}

// LemmaPreserveInstall is what ApplyLemmaPreserve would leave on goal
// for lemma — the preserving chain's subgoals, on the lemma as stated
// or on its adaptation to the goal's types, whichever the selection
// takes — with no node touched and no step recorded. It answers a
// reader of a recorded proof that must know what a bare cite of the
// lemma installs at a goal (emit's section cites). nil when the chain
// does not apply.
func LemmaPreserveInstall(lemma, goal Prop) *SubGoals {
	_, subGoals := chooseTypeAdaptedStep(CreateGoalStack(goal), lemma, lemmaPreserveStep)
	return subGoals
}

// ApplyLeanRw applies the lemma as an explicit equational rewrite via
// LeanRwTactic. Unlike ApplyLemma, this dispatches to a pure rewrite
// path:
//
//   - The size-decrease guard inside eqSimplify is bypassed, so
//     expansion-style equational lemmas (extensionality, COND
//     distribution, definitional unfolding) apply normally.
//   - There is NO fallback to lemmaConclMatchTactic /
//     lemmaHypMatchTactic. When the rewrite path doesn't match, the
//     tactic returns clean failure rather than silently adding the
//     lemma's conclusion as a new hypothesis.
//
// Same polymorphic-lemma type-adaptation selection as ApplyLemma.
func ApplyLeanRw(n *GoalStackNode, lemma Prop) bool {
	step, subGoals := chooseTypeAdaptedStep(
		n,
		lemma,
		func(lemma Prop, sourceKey core.PropKey) _Step {
			return _LeanRwTactic{lemma: lemma, polymorphicSourceKey: sourceKey}
		})
	return n.commitStep(step, subGoals)
}

// ApplyLemmaPreserveWithSource is the agent-type-specialize entry point
// for `lemma`. Same dispatch as ApplyLemmaPreserve, except the recorded
// ministep's `polymorphicSourceKey` is forced to `sourceKey` regardless
// of what chooseTypeAdaptedStep would have computed. Used when the engine
// has already applied an agent-supplied σ to a cited lemma — `lemma` is
// the post-σ form, `sourceKey` is the PRE-σ entry's key so dep
// extraction still records the polymorphic source as the dep.
// Empty `sourceKey` falls through to ApplyLemmaPreserve's behavior (no
// override).
func ApplyLemmaPreserveWithSource(n *GoalStackNode, lemma Prop, sourceKey core.PropKey) bool {
	if sourceKey == "" {
		return ApplyLemmaPreserve(n, lemma)
	}
	step, subGoals := chooseTypeAdaptedStep(
		n,
		lemma,
		func(lemma Prop, _ core.PropKey) _Step {
			return _LemmaPreserveTactic{lemma: lemma, polymorphicSourceKey: sourceKey}
		})
	return n.commitStep(step, subGoals)
}

// ApplyLemmaPreserveExactWithSource installs `lemma` exactly as given —
// no speculative type adaptation. Used when the caller has already
// resolved the lemma's full type instantiation (e.g. via the engine's
// `term_specialize` pre-pass, which computes σ_type from the witness
// and applies it before install). Bypassing chooseTypeAdaptedStep is
// load-bearing here: `tryAdaptLemmaTypes` may otherwise compute a
// COMPETING σ that collapses lemma type-vars against the goal context,
// overriding the agent's explicit type choice and breaking the
// post-install instantiate chain (binder type post-collapse no longer
// matches the agent-supplied witness's type).
//
// `sourceKey` is forced into the recorded ministep's
// `polymorphicSourceKey` so emit's leaf resolution points at the original
// polymorphic registry entry. Empty `sourceKey` records a ground lemma
// (no override).
func ApplyLemmaPreserveExactWithSource(n *GoalStackNode, lemma Prop, sourceKey core.PropKey) bool {
	return n.runStep(_LemmaPreserveTactic{lemma: lemma, polymorphicSourceKey: sourceKey})
}

// ApplyLeanRwExactWithSource is the `lean_rw` counterpart of
// ApplyLemmaPreserveExactWithSource. Same skip-adapt rationale.
func ApplyLeanRwExactWithSource(n *GoalStackNode, lemma Prop, sourceKey core.PropKey) bool {
	return n.runStep(_LeanRwTactic{lemma: lemma, polymorphicSourceKey: sourceKey})
}

// ApplyLeanRwWithSource is the `lean_rw` counterpart of
// ApplyLemmaPreserveWithSource. Same source-key override semantics.
func ApplyLeanRwWithSource(n *GoalStackNode, lemma Prop, sourceKey core.PropKey) bool {
	if sourceKey == "" {
		return ApplyLeanRw(n, lemma)
	}
	step, subGoals := chooseTypeAdaptedStep(
		n,
		lemma,
		func(lemma Prop, _ core.PropKey) _Step {
			return _LeanRwTactic{lemma: lemma, polymorphicSourceKey: sourceKey}
		})
	return n.commitStep(step, subGoals)
}

// chooseTypeAdaptedStep picks between the original lemma and its
// type-adapted candidate, and returns BOTH the winning ministep and the
// SubGoals it produced on `n.Goal`. The caller commits those SubGoals via
// commitStep, so the winning tactic is applied exactly once during
// selection — never re-applied at commit time.
//
//   - Ground lemma (no type vars): apply the original once; nothing to adapt.
//   - No adaptation found: same — apply the original once.
//   - Otherwise: apply both candidates, compare, and return the winner's
//     SubGoals. Two applies total (one per candidate).
//
// A nil SubGoals is propagated to commitStep, which treats it as "tactic
// did not apply" — identical to runStep's nil contract.
func chooseTypeAdaptedStep(
	n *GoalStackNode,
	lemma Prop,
	makeStep func(Prop, core.PropKey) _Step,
) (_Step, *SubGoals) {
	return chooseTypeAdaptedStepBy(n, lemma, makeStep, _Step.apply)
}

// chooseTypeAdaptedStepBy is chooseTypeAdaptedStep with the candidates
// applied by apply, for a caller that runs them under a deadline
// (installLemmaPreserveUntil).
func chooseTypeAdaptedStepBy(
	n *GoalStackNode,
	lemma Prop,
	makeStep func(Prop, core.PropKey) _Step,
	apply func(_Step, Prop) *SubGoals,
) (_Step, *SubGoals) {
	goal := n.Goal
	orig := makeStep(lemma, "")
	if !ext.PropHasTypeVars(lemma) {
		return orig, apply(orig, goal)
	}

	adapted := typematch.TryAdaptLemmaTypes(lemma, goal)
	if adapted == nil {
		return orig, apply(orig, goal)
	}

	adaptedStep := makeStep(adapted, lemmaSourceKey(lemma))
	origSG := apply(orig, goal)
	adaptedSG := apply(adaptedStep, goal)
	switch {
	case origSG == nil:
		return adaptedStep, adaptedSG
	case adaptedSG == nil:
		return orig, origSG
	case origSG.Size() <= 1:
		// Lean-style conservatism: if the original lemma already closes
		// directly modulo proving the lemma child, do not let speculative
		// type adaptation rewrite it into a different theorem instance.
		return orig, origSG
	case adaptedSG.Size() < origSG.Size():
		return adaptedStep, adaptedSG
	case origSG.Size() < adaptedSG.Size():
		return orig, origSG
	default:
		// Tie: use the adapted form so genuinely polymorphic applications
		// keep the concrete binder types that later tactics expect.
		return adaptedStep, adaptedSG
	}
}

// ApplyBasic runs the step `Basic()` is on the node: the propositional
// rewrites alone. A ⊤ conclusion, a reflexive equation and a conclusion
// that is a hypothesis close; any other goal is left as those rewrites
// leave it.
func ApplyBasic(n *GoalStackNode) bool {
	return n.runStep(_BasicTactic{})
}

// ApplyTrivial runs TrivialSimplifyTactic on the node.
func ApplyTrivial(n *GoalStackNode) bool {
	return n.runStep(_TrivialSimplify{})
}

// ApplyDenote runs AutoDenote (both size-threshold and Hilbert modes) on
// the node — the SEARCH form: the heuristic picks the subterm and mints
// α₀. The firing records what it chose (see _AutoDenote), so the
// persisted step replays the decision rather than re-deriving it.
func ApplyDenote(n *GoalStackNode) bool {
	if n.runStep(_AutoDenote{sizeThreshold: _DENOTE_SIZE_THRES}) {
		return true
	}
	return n.runStep(_AutoDenote{hilbert: true})
}

// ApplyDenoteTerm is the EXPLICIT denote: name `term` by `name`. When
// `hilbert`, the term must be an ε-term and the ε transform runs
// instead. Panics (loudly, at this step) when the goal does not contain
// the term or the name is already free in it — see
// tactic.DenoteTermTactic.
func ApplyDenoteTerm(n *GoalStackNode, name string, term core.Term, hilbert bool) bool {
	return n.runStep(_AutoDenote{term: term, name: name, hilbert: hilbert})
}

// ApplyLetTerm is the DEFINITION move, "let name := term" — the session
// face of Argument.Let (LetTerm): the equation `name = term` joins the
// hypotheses, every occurrence of the term in the goal becomes the
// name, and the goal keeps its form. The term need not occur. Panics
// (loudly, at this step) when the name is already free in the goal.
func ApplyLetTerm(n *GoalStackNode, name string, term core.Term) bool {
	return n.runStep(_AutoDenote{term: term, name: name, let: true})
}

// ---------------------------------------------------------------------------
// Structural sub-tactics (individual components of BasicTactics)
// ---------------------------------------------------------------------------

// ApplyRewrite normalizes terms via basic rewrites.
func ApplyRewrite(n *GoalStackNode) bool {
	return n.runStep(_Rewrite{})
}

// ApplyCondRewrite normalizes COND terms via cond rewrites.
func ApplyCondRewrite(n *GoalStackNode) bool {
	return n.runStep(_CondRewrite{})
}

// ApplyArith runs the unified num-arithmetic ministep (`_Arith`): one deep,
// hyp-aware, fixpoint rewrite that does identity simplification (a+0→a,
// a*1→a, …), atom decision (`<` `≤` `>` `≥` `=` to ⊤/⊥, incl. nonlinear
// semiring equalities via RingProveFull), and bool/cond/quantifier collapses
// — all in ONE call via `prop.BasicRewritesWith`. Records `arith=42`.
// Returns false (cleanly declines) when nothing reduces.
//
// Differs from the pre-unification `_Arith`: that was close-only (ring →
// linarith dispatch); the new one is the unified rewriter that may close
// (rewrite the whole conclusion to ⊤, which `_TrivialSimplify` closes on
// the residual `⊢ ⊤` child) OR partially simplify, advancing the goal. Use
// `ApplyArithSimplify` for the standard composite that pairs `_Arith` with
// `_TrivialSimplify` for the close.
// ApplyRingNf runs the ring-normal-form rewrite (_RingNormalize) on n's
// goal; false when no arithmetic subterm changes.
//
// ctx cuts the rewrite off before a subterm is normalized: a done
// context raises a utils.Cut there, and n is left as it was.
func ApplyRingNf(ctx context.Context, n *GoalStackNode) bool {
	return n.runStep(_RingNormalize{ctx: ctx})
}

func ApplyArith(n *GoalStackNode) bool {
	return n.runStep(_Arith{})
}

// ApplyArithSimplify is the standard agent-facing composite: runs the unified
// `_Arith` rewrite, then `_TrivialSimplify` on the resulting leaves to close
// any `⊢ ⊤` (or refl) residual via DerivesTrue. Each underlying step records
// under its OWN proto tag (`arith=42` / `trivial_simplify=7`) — never a
// reused `basic` tag — so stored steps don't drift and replay of omega's own
// foundation theorems never re-enters omega.
//
// The rule cascade (`Cond(a=a, 0, 1) → a` and similar) happens INSIDE
// `_Arith`'s rewrite — `prop.BasicRewritesWith`'s underlying DeepRewrite
// iterates to fixpoint over all the leaves (identity folds, atom decision, bool, cond,
// quantifier, neg) in one pass — so the composite doesn't loop. Returns true
// when the composite changed the leaf: `_Arith` fired and the tidy did not
// take the firing back.
//
// ctx is polled between leaf passes, and inside the decision before each
// leaf of the decider: a done context raises a utils.Cut there, which
// unwinds the step and leaves n as it was.
//
// Leading-wrapper strip: when the direct `_Arith` pass makes no progress, a
// leading `∀`/`⇒` wrapper on the conclusion may be hiding an arith sequent from
// the hyp-aware decider — `⊢ (a≤b)⇒(b≤c)⇒(a≤c)` is opaque to it, while the
// equivalent `a≤b, b≤c ⊢ a≤c` closes in one pass (the antecedents are exactly
// the Farkas facts). So as a fallback we strip those sound, equivalence-
// preserving wrappers (antecedent → hypothesis via `_StripImp`, conclusion `∀`
// → fresh var via `_StripQuant`) and retry the decider. The strip is committed
// ONLY when the decider then FULLY closes the stripped goal — a non-closing
// arith call never leaves a surprising half-stripped residual for the next
// tactic — so the only observable effect is that `arith`/`auto` closes the
// implication/∀-prenex forms without a manual `strip_imp; arith`.
func ApplyArithSimplify(ctx context.Context, n *GoalStackNode) bool {
	arith := _Arith{ctx: ctx}
	residual := arith.applyScoped(n.Goal, n.proofScope)
	if residual == nil {
		return closeByStrippedArith(ctx, n)
	}
	// A firing the mop-up takes back is no step: a law that grows a term
	// (an absolute value pushed through a product) rewrites the conclusion,
	// and _TrivialSimplify folds it back by the bridge equation an earlier
	// firing left among the hypotheses. Committed, it would report
	// progress on a leaf it left as it found it, pass after pass; n stays
	// the bare leaf instead, as after an `_Arith` that did not fire.
	var tidied *SubGoals
	if residual.Size() == 1 {
		tidied = _TrivialSimplify{}.apply(residual.ChildGoal(0))
		if tidied != nil && tidied.Size() == 1 && tidied.ChildGoal(0).AlphaEquals(n.Goal) {
			return closeByStrippedArith(ctx, n)
		}
	}
	n.commitStep(arith, residual)
	switch {
	case residual.Size() != 1:
		n.runStepOnLeaves(ctx, _TrivialSimplify{})
	case tidied != nil:
		// The one residual's tidy, computed above.
		n.children[0].commitStep(_TrivialSimplify{}, tidied)
	}
	return true
}

// closeByStrippedArith strips leading conclusion `∀`/`⇒` wrappers and runs the
// arith decider, committing onto n only when the stripped goal fully closes. It
// is invoked from ApplyArithSimplify after a no-progress `_Arith` pass (so n is
// pristine — a failed runStep never sets a ministep). The trial runs on a Clone
// so that on non-closure n is left untouched: the `auto` fast-path reads
// `clone.Proved()` and falls through to AutoExpand, which must see the original
// (unstripped) goal.
func closeByStrippedArith(ctx context.Context, n *GoalStackNode) bool {
	// The strip and the leaf loops stop at a done context: a trial the
	// context ended is cut off, not a decline.
	stopIfDone := func() {
		if stop := utils.Stopper(ctx); stop != nil {
			stop("inside arith, in the trial on the stripped goal")
		}
	}
	trial := n.Clone()
	if !stripConclWrappers(ctx, trial) {
		stopIfDone()
		return false
	}
	trial.runStepOnLeaves(ctx, _Arith{ctx: ctx})
	trial.runStepOnLeaves(ctx, _TrivialSimplify{})
	if !trial.Proved() {
		stopIfDone()
		return false
	}
	// Trial closed — replay the identical, deterministic steps on n to
	// commit. The replay runs to its end whatever the context: it is the
	// trial's cost again, and a replay the context stopped half way would
	// leave n stripped and open.
	stripConclWrappers(context.Background(), n)
	n.runStepOnLeaves(context.Background(), _Arith{})
	n.runStepOnLeaves(context.Background(), _TrivialSimplify{})
	return true
}

// stripConclWrappers strips leading conclusion `∀` (`_StripQuant`) and `⇒`
// (`_StripImp`) from every unsolved leaf, to a fixpoint, and reports whether it
// stripped anything. The `||` short-circuit is load-bearing: `_StripQuant`
// is tried first and, on success, leaves the node with a ministep — so
// `_StripImp` must NOT also run on it (commitStep asserts ministep==nil); a
// false `_StripQuant` leaves the leaf pristine, so the `_StripImp` attempt is
// safe. New child leaves surface in the next outer iteration's fresh
// UnsolvedLeaves() snapshot. Termination: each strip strictly shrinks the
// conclusion's leading wrapper depth.
func stripConclWrappers(ctx context.Context, n *GoalStackNode) bool {
	stripped := false
	for {
		progressed := false
		for _, leaf := range n.UnsolvedLeaves() {
			if ctx.Err() != nil {
				return stripped
			}
			if leaf.runStep(_StripQuant{}) || leaf.runStep(_StripImp{}) {
				progressed, stripped = true, true
			}
		}
		if !progressed {
			return stripped
		}
	}
}

// ApplySplitConj splits conclusion A∧B into subgoals ⊢ A and ⊢ B.
func ApplySplitConj(n *GoalStackNode) bool {
	return n.runStep(_SplitConj{})
}

// ApplySplitConjAll flattens conclusion A∧B∧…∧Z into N flat subgoals
// ⊢ A, ⊢ B, …, ⊢ Z in one step (vs N-1 nested ApplySplitConj peels).
func ApplySplitConjAll(n *GoalStackNode) bool {
	return n.runStep(_SplitConjAll{})
}

// ApplySplitDisj splits hypothesis A∨B ⊢ C into subgoals A ⊢ C and B ⊢ C.
// Picks the first ∨-shaped hyp. Use ApplySplitDisjAt to target a specific
// index.
func ApplySplitDisj(n *GoalStackNode) bool {
	return n.runStep(_SplitDisj{})
}

// ApplySplitDisjAt is the index-targeted variant: split the ∨-hyp at
// hypIdx. Returns false (no step recorded) if hypIdx is out of range
// or the hyp there is not A∨B — the wire layer surfaces the reason.
func ApplySplitDisjAt(n *GoalStackNode, hypIdx int) bool {
	return n.runStep(_SplitDisj{hypIndex: &hypIdx})
}

// ApplyStripImp moves antecedent to hypothesis: ⊢ A⇒B → A ⊢ B.
func ApplyStripImp(n *GoalStackNode) bool {
	return n.runStep(_StripImp{})
}

// ApplyStripQuant strips ∀ from conclusion and ∃ from hypotheses.
func ApplyStripQuant(n *GoalStackNode) bool {
	return n.runStep(_StripQuant{})
}

// ApplyStripQuantAt is the index-targeted variant: Skolemize the ∃-hyp
// at hypIdx and leave the conclusion alone. Returns false (no step
// recorded) if hypIdx is out of range or the hyp there is not ∃-headed
// — the wire layer surfaces the reason.
func ApplyStripQuantAt(n *GoalStackNode, hypIdx int) bool {
	return n.runStep(_StripQuant{hypIndex: &hypIdx})
}

// ApplySplitIff splits conclusion A⇔B into subgoals B⊢A and A⊢B, in
// that order — the ⇐ direction FIRST (tactic.ConclIffTactic builds
// goal0 with conclusion A under hypothesis B). Case labels on a
// SplitIff must follow that order. It declines (false) where the two
// halves merge into one because one subsumes the other (`L ⊢ L ⇔ ⊥`).
func ApplySplitIff(n *GoalStackNode) bool {
	return n.runStep(_SplitIff{})
}

// ApplySplitHypIff case-analyzes hypothesis A⇔B into A,B⊢C and ¬A,¬B⊢C.
// Picks the first ⇔-shaped hyp whose split stands: one whose sides are
// α-equal, or whose two branches merge into one because one subsumes
// the other (`p ⇔ q, p, q ⊢ C`), is passed over. Use ApplySplitHypIffAt
// for a specific index.
func ApplySplitHypIff(n *GoalStackNode) bool {
	return n.runStep(_SplitHypIff{})
}

// ApplySplitHypIffAt is the index-targeted variant of ApplySplitHypIff;
// it declines (false) where that hypothesis's two branches merge.
func ApplySplitHypIffAt(n *GoalStackNode, hypIdx int) bool {
	return n.runStep(_SplitHypIff{hypIndex: &hypIdx})
}

// ApplySplitHypImply case-analyzes hypothesis A⇒B into ¬A⊢C and B⊢C.
// Picks the first ⇒-shaped hyp. Use ApplySplitHypImplyAt for a specific
// index.
func ApplySplitHypImply(n *GoalStackNode) bool {
	return n.runStep(_SplitHypImply{})
}

// ApplySplitHypImplyAt is the index-targeted variant of ApplySplitHypImply.
func ApplySplitHypImplyAt(n *GoalStackNode, hypIdx int) bool {
	return n.runStep(_SplitHypImply{hypIndex: &hypIdx})
}

// ApplyWitness instantiates the concl-level ∃ at the supplied witness
// term, producing the subgoal ⊢ P(t); a concl-level ∃! leaves
// ⊢ P(t) ∧ (∀y. P(y) ⇒ y = t).
func ApplyWitness(n *GoalStackNode, witness Term) bool {
	return n.runStep(_WitnessStep{witness: witness})
}

// ApplySpecialize is the index-targeted grounding primitive: each spec
// grounds one ∀-hyp's leading binders at its witness list in ONE goal
// transition, adding only the final instance; sources are consumed
// unless keepSources. All hyp indices refer to the node's current
// goal. See tactic.SpecializeTactic.
func ApplySpecialize(n *GoalStackNode, specs []SpecializeHyp, keepSources bool) bool {
	return n.runStep(_SpecializeStep{specs: specs, keepSources: keepSources})
}

// ---------------------------------------------------------------------------
// LEAN-style tactics
// ---------------------------------------------------------------------------

// ApplyAssumption closes the goal when concl α-equals some hyp.
func ApplyAssumption(n *GoalStackNode) bool {
	return n.runStep(_Assumption{})
}

// ApplyRefl closes the goal when concl is `t = t`.
func ApplyRefl(n *GoalStackNode) bool {
	return n.runStep(_Refl{})
}

// ApplyLeft peels the right disjunct: ⊢ A∨B → ⊢ A.
func ApplyLeft(n *GoalStackNode) bool {
	return n.runStep(_Left{})
}

// ApplyRight peels the left disjunct: ⊢ A∨B → ⊢ B.
func ApplyRight(n *GoalStackNode) bool {
	return n.runStep(_Right{})
}

// ApplyFunext rewrites ⊢ f = g (function-typed) into ⊢ ∀x. f(x) = g(x).
func ApplyFunext(n *GoalStackNode) bool {
	return n.runStep(_Funext{})
}

// ApplyByContra negates the conclusion: ⊢ G → ¬G ⊢ ⊥. Returns false
// when the conclusion is already ⊥.
func ApplyByContra(n *GoalStackNode) bool {
	return n.runStep(_ByContra{})
}

// ApplySymm flips an equality conclusion: ⊢ a = b → ⊢ b = a.
func ApplySymm(n *GoalStackNode) bool {
	return n.runStep(_Symm{})
}

// ApplySubst substitutes using hypothesis at hypIndex (must be an equality
// whose LHS or RHS is a free variable).
func ApplySubst(n *GoalStackNode, hypIndex int) bool {
	return n.runStep(_SubstStep{hypIndex: hypIndex})
}

// ApplyRw rewrites with the equality hyp at hypIndex to fixpoint across
// the conclusion and all other hyps — written direction when flip is
// false, reversed when true. Returns false when the hyp isn't a
// top-level equality or no occurrence of the oriented LHS rewrites.
//
// ctx cuts the rewrite off between the passes of its fixpoint: a done
// context raises a utils.Cut there, and n is left as it was.
func ApplyRw(ctx context.Context, n *GoalStackNode, hypIndex int, flip bool) bool {
	return n.runStep(_RwStep{hypIndex: hypIndex, flip: flip, ctx: ctx})
}

// ApplyTrans splits ⊢ a = c into ⊢ a = b and ⊢ b = c via the supplied
// middle term `b`.
func ApplyTrans(n *GoalStackNode, middle Term) bool {
	return n.runStep(_TransStep{middle: middle})
}

// ApplyAssert introduces a hyp-free boolean claim φ as a sub-claim of
// the current goal Γ ⊢ G, producing two subgoals:
//
//	child(0) = Γ ⊢ φ          (the asserted claim)
//	child(1) = Γ, φ ⊢ G       (residual goal with φ as a new hyp)
//
// Returns false when applying the assertion would be a no-op or
// self-referential (φ is already a hyp of the goal, or φ's conclusion
// is α-equal to G's conclusion). The claim must be a hyp-free Prop; the
// engine RPC layer validates this before invoking.
func ApplyAssert(n *GoalStackNode, claim Prop) bool {
	return n.runStep(_AssertStep{claim: claim})
}

// ApplyCiteNode adds the conclusion of a proved node `target` as a
// hypothesis at `n`. Implements session-internal "cut by existing
// derivation": skips re-searching to re-prove ψ when ψ is already proved
// elsewhere in this same session tree.
//
// Mechanically a sugar for `assert(target.Concl)` whose first (claim) child
// is materialized inline from target's cloned proof subtree. The resulting
// tree serializes as a regular assert with a fully-proven first branch —
// replay re-verifies the inlined proof; no new ministep type, no proto
// change, no new replay path.
//
// Soundness preconditions (caller MUST verify):
//   - target.Proved() — refusing an open target prevents citing-the-unproved.
//   - target's hyp context ⊆ n's hyp context (α-equiv subset) — verify with
//     target.Goal.AllHyp(n.Goal.HasHyp) at the call site, e.g. the engine
//     RPC dispatch.
//
// Returns false (n untouched) on the underlying assert no-op (claim already
// a hyp of n, or α-equal to n's conclusion). Returns true on success;
// afterward n.children[0] is the cited subtree (proved), n.children[1] is
// the new focus (Γ_n, ψ ⊢ G).
//
// A DEFINITION section (IsDefinitionSection — a define composite at its
// root, any payload) is the exception to the splice: its theorem is an
// ENTRY at landing, so the claim child closes as a KNOWN THEOREM — the
// section's promised theorem, a KnownThm leaf emit resolves to the entry
// by key — and the composite that derived it is never inlined (emit
// refuses a mint inside a body, and a member must not re-run one).
func ApplyCiteNode(n *GoalStackNode, target *GoalStackNode) bool {
	claim := prop.MakeProp(target.Goal.Conclusion())
	if !n.runStep(_AssertStep{claim: claim}) {
		return false
	}
	// n.children = [firstChild (Γ_n ⊢ ψ), secondChild (Γ_n, ψ ⊢ G)]
	firstChild := n.children[0]
	if target.IsDefinitionSection() {
		if !firstChild.runStep(_KnownThmStep{strongerGoal: target.PromisedThm()}) {
			panic(fmt.Sprintf("ApplyCiteNode: the definition's theorem %s does not close its own claim %s",
				prop.PrintProp(target.Goal), prop.PrintProp(firstChild.Goal)))
		}
		return true
	}

	// Compute Γ_n \ Γ_target: hyps that firstChild carries but target
	// doesn't. Target's proof is under a possibly-smaller hyp context;
	// splicing it directly would leave firstChild.miniStep operating on
	// Γ_n but firstChild.children reporting Γ_target-context Goals — a
	// wire-time asymmetry that emit + replay currently paper over with
	// ClearHypsNoAnchor / StripQuantNoAnchor inference. Materialize the
	// weakening as an explicit _ClearHypsStep so it appears in
	// DetailedProofProto (record) → getStep (replay) with no
	// emit-time inference.
	var drop []int
	for i := 0; i < firstChild.Goal.NumHyps(); i++ {
		if !target.Goal.HasHyp(firstChild.Goal.Hyp(i)) {
			drop = append(drop, i)
		}
	}

	targetClone := target.Clone()
	if len(drop) == 0 {
		// Target already carries all of n's hyps — a bare splice suffices.
		firstChild.miniStep = targetClone.miniStep
		firstChild.subGoals = targetClone.subGoals
		firstChild.provedThm = targetClone.provedThm
		firstChild.children = targetClone.children
		for _, c := range firstChild.children {
			c.parent = firstChild
		}
		return true
	}
	// Wrap: firstChild → _ClearHypsStep(drop) → targetClone
	// firstChild.Goal is Γ_n⊢ψ; after ClearHyps(drop), the child Goal is
	// Γ_target⊢ψ, exactly targetClone.Goal.
	clearStep := _ClearHypsStep{hypIndices: drop}
	sg := clearStep.apply(firstChild.Goal)
	Assert(sg != nil && sg.Size() == 1)
	Assert(sg.ChildGoal(0).AlphaEquals(target.Goal))
	targetClone.parent = firstChild
	firstChild.miniStep = clearStep
	firstChild.subGoals = sg
	firstChild.children = []*GoalStackNode{targetClone}
	// Weakening preserves provability: target's thm proves Γ_target⊢ψ,
	// which α-implies Γ_n⊢ψ. Reuse target's thm as firstChild's cert.
	firstChild.provedThm = targetClone.provedThm
	return true
}

// ApplyCongr structurally decomposes an equality goal.
func ApplyCongr(n *GoalStackNode) bool {
	return n.runStep(_Congr{})
}

// ApplyClearHyps drops the SET of hyps at hypIndices in ONE ministep
// (_ClearHypsStep, proto tag `clear_hyps`). All indices refer to the
// hyp list of n's goal as the agent sees it — the set is removed
// atomically, so there is no sequential index shifting. One ministep /
// one tree node regardless of how many hyps are swept, which keeps
// recorded proofs and emitted members proportional to the proof, not to
// the hyp-context width. Returns false (n untouched) on an empty list,
// a duplicate, or any out-of-range index.
//
// This is the sole agent-facing clear path: every `clear` apply (single
// or batch) routes here.
func ApplyClearHyps(n *GoalStackNode, hypIndices []int) bool {
	return n.runStep(_ClearHypsStep{hypIndices: hypIndices})
}

// ApplyCongrArg adds the hyp fn(a)=fn(b) from the equality hyp a=b at
// hypIndex (Lean congrArg). Returns false when the hyp
// isn't an equality, fn's domain doesn't match, or there's no progress.
func ApplyCongrArg(n *GoalStackNode, fn Term, hypIndex int) bool {
	return n.runStep(_CongrArgStep{fn: fn, hypIndex: hypIndex})
}

// ApplyCongrFun adds the hyp f(arg)=g(arg) from the function-equality
// hyp f=g at hypIndex (Lean congrFun). Returns false under
// the dual conditions to ApplyCongrArg.
func ApplyCongrFun(n *GoalStackNode, arg Term, hypIndex int) bool {
	return n.runStep(_CongrFunStep{arg: arg, hypIndex: hypIndex})
}
