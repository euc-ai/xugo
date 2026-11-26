package proof

import (
	"fmt"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/utils"
)

// TryLemmaTactic is a PROBE: it applies a lemma (as Prop) to a goal on
// a throwaway node and reports the resulting subgoals — the derivation
// checks and the registry-repair recommender ask "does this premise
// apply, and what is left". It does NOT require the lemma to be proved
// and records nothing.
//
// Returns (childGoals, true) if the lemma is applicable, (nil, false)
// otherwise. childGoals[0] is always the lemma itself; childGoals[1] (if
// present) is the residual AS A PROOF WOULD SEE IT after its own
// simplify step: probeLemma runs the bare step and then _TrivialSimplify
// on the residual, because the question the probe answers is about the
// reduced goal, not the raw one. A recording
// surface never takes this path (macro.go's header).
func TryLemmaTactic(goal Prop, lemma Prop) (childGoals []Prop, ok bool) {
	Assert(lemma != nil)
	node := CreateGoalStack(goal)
	if !probeLemma(node, lemma) {
		return nil, false
	}
	Assert(len(node.children) >= 1)
	if len(node.children) == 1 {
		// _LemmaTactic produced 1 subgoal — the lemma directly proves the goal.
		return []Prop{node.child(0).Goal}, true
	}
	Assert(len(node.children) == 2)
	// Read the residual from child(1)'s actual unsolved LEAF, not from
	// child(1).Goal: probeLemma's _TrivialSimplify pushes a rewritten
	// goal into a CHILD of child(1) when it fires, so child(1).Goal
	// stays the raw pre-process residual and the leaf is the goal a
	// next step would see.
	leaves := node.child(1).UnsolvedLeaves()
	if len(leaves) == 0 {
		// The simplification closed the residual outright: the lemma
		// proves the goal up to simplification.
		return []Prop{node.child(0).Goal}, true
	}
	Assert(len(leaves) == 1)
	return []Prop{node.child(0).Goal, leaves[0].Goal}, true
}

// TryDefTacticRewrite is the agent-facing `def_expand` applicability
// predicate: it runs the SAME `_DefExpandStep` composite ApplyDefExpand
// commits (proto tag 51; computeDefExpandSubGoals in step_composite.go)
// on a throwaway node, so the surfaced applicability agrees with a
// commit by construction — one driver, not a mirrored pair. Used by
// inspect / Recommendations.
//
// This is the predicate to consult when answering "would `apply
// def_expand` succeed here?" — a positive answer here matches a
// successful commit; a negative answer means agents should not be
// surfaced this option (no `def_expand` structural fact, no
// `def_expand` recommendation).
func TryDefTacticRewrite(goal Prop, c ext.ConstTerm) (residual Prop, ok bool) {
	n := CreateGoalStack(goal)
	if !n.runStep(_DefExpandStep{constTerm: c}) {
		return nil, false
	}
	leaves := n.UnsolvedLeaves()
	switch len(leaves) {
	case 0:
		return nil, true
	case 1:
		return leaves[0].Goal, true
	}
	// computeDefExpandSubGoals emits at most one residual child.
	panic(fmt.Sprintf("TryDefTacticRewrite: def_expand composite produced %d residuals", len(leaves)))
}

// getDefThm returns the Thm to unfold for a given const:
//   - Type 1: c.DefThm()
//   - Type 2 abs-meta: out1 of TypeDefExpand (a = abs(rep a))
//   - Type 2 rep-meta: out2 of TypeDefExpand (P(r) ⇔ rep(abs r) = r)
//   - anything else (basic const / unProved defSource): nil
func getDefThm(c ext.ConstTerm) ThmCert {
	// Type 1 (NewConstDef): return the def thm SPECIALIZED to c's
	// type substitution. c.DefThm() does
	// `PropTypeInst(meta.def, c.typeSubsts...)`, producing
	// `c⟨A:t⟩ = body[A↦t]` for c's specific type instance — the LHS that
	// actually appears in the goal. The generic meta.DefThm() would
	// require adaptLemmaIfPolymorphic at the rewriter to pick a σ from
	// the goal, which is ambiguous when the goal contains multiple
	// distinct type instances of c (e.g. the I-combinator's polymorphic
	// uses). c.typeSubsts is unambiguous because the action's proto
	// records the exact ConstTerm including its typeSubsts.
	if thm := c.DefThm(); !thm.IsZero() {
		return thm
	}
	// Type 2 (NewTypeDef abs/rep): meta.def is nil, so c.DefThm() is
	// nil too and we land here. Recover the abs/rep axiom from
	// TypeDefExpand against meta's DefSource.
	meta := c.Meta()
	src := meta.DefSource()
	if src == nil || !src.Proved() {
		return ThmCert{}
	}
	out1, out2 := meta.TypeDefExpand(src)
	if meta.IsTypeDefAbs() {
		return out1.AsThmCert()
	}
	return out2.AsThmCert()
}

// NormalizedPropTypeMatch checks if target is a (strict) type instantiation
// of pattern. Returns the type substitution if so. The substitution list is
// non-empty on success — alpha-equivalent props without any actual type
// substitution return (nil, false), since that means the props are already
// the same theorem.
//
// INVARIANT: both `pattern` and `target` MUST already be normalized (via
// ext/prop.Normalize). NormalizedPropTypeMatch does not normalize internally;
// matching bottoms out in α-equivalence checks that don't canonicalize
// equality orientation, disjunct ordering, quantifier ordering, or other
// structural rewrites that Normalize performs. Passing non-normalized props
// may miss logically valid matches (false negatives); correctness is
// preserved either way (no false positives).
//
// Implementation: thin wrapper over prop.IsTypeMatchOf with all of
// pattern's type vars instantiable. The "strict" semantics (reject the
// empty-subst case where pattern is already α-equal to target) is
// re-imposed here since IsTypeMatchOf itself accepts the empty σ as a
// valid match.
func NormalizedPropTypeMatch(pattern, target core.Prop) ([]core.TypeSubst, bool) {
	// Normalized prop has no hyp.
	Assert(pattern.NumHyps() == 0 && target.NumHyps() == 0)
	substs, ok := prop.IsTypeMatchOf(pattern, target, utils.FullPredicate[core.VarType])
	if !ok || len(substs) == 0 {
		// Empty σ from IsTypeMatchOf means pattern is already α-equal
		// to target — not an interesting type-instantiation match.
		return nil, false
	}
	return substs, true
}

func TryMatchKnownThm(thmCache *ThmCache, n *GoalStackNode) bool {
	// Trivial-true short-circuit: if the goal normalizes to a ⊤ conclusion,
	// close it via the dedicated _TrivialNormalizedStep instead of letting
	// the cache lookup hit the imported ⊢ ⊤ entry and emit a misleading
	// Known step. The cache lookup also has this guard (LoadNormalizedThm)
	// — handling it here keeps trivial-true out of replay traces too.
	if normalized, _ := Normalize(n.Goal); normalized.Conclusion().Equals(T) {
		Assert(n.runStep(_TrivialNormalizedStep{}))
		return true
	}
	return commitFoundThmStep(thmCache, n)
}

// commitFoundThmStep is the single commit point for "this goal is
// already proved in a ThmCache" closes (ApplyKnown / TryMatchKnownThm /
// the KnownThm action). The FindProvedThm TIER decides the RECORDED
// step shape — this is load-bearing for replay/emit, not cosmetics:
//
//   - Tier 1 (raw α-key) / Tier 2 (normalized α-key): the stored thm IS
//     the goal's own statement (exactly, or modulo Normalize). Record
//     the _KnownThmStep; its payload resolves at emit through the
//     exact / normalize reference tiers.
//   - Tier 3 (SkeletonKey type-match): the stored thm is a POLYMORPHIC
//     generalization, and the closing thm is a per-goal TYPE INSTANCE
//     whose statement has no stable identity outside this session.
//     Recording that instance in a _KnownThmStep poisons the
//     recording — emit's lemma-reference resolution has no tier that
//     can resolve it and panics (live instance: fst adapted at cart
//     types in cardinality.HasSizeProduct, produced via the agent-facing `known`
//     tactic against s.autoMatchCache). Record
//     _TypeInstStep{source: the normalized polymorphic form} instead —
//     the exact shape the engine auto-match type-instance branch
//     commits — so the wire carries the SOURCE and replay re-derives
//     the instance deterministically. Sibling of the paired_beta
//     composite (proto tag 53): record source + derivation, never the
//     instance.
func commitFoundThmStep(thmCache *ThmCache, n *GoalStackNode) bool {
	return commitFoundThmStepWithKey(thmCache, n, "")
}

// commitFoundThmStepWithKey is commitFoundThmStep with the caller's
// registry identity claim attached (ApplyKnownWithKey). `entryKey` is
// the key of the registry entry the CALLER resolved for n.Goal's
// normalize-α class;
// it is stamped onto the recorded _KnownThmStep only when the committed
// payload actually IS that class (goalPayloadEntryKey) — a tier-1/2
// hit on a strict StrongerGoals variant records a different statement
// than the one the caller vouched for, and must keep the payload-derived
// dep resolution. Tier 3 never stamps: its dep is the polymorphic
// SOURCE, about which the caller's goal-derived key says nothing (the
// engine's type-instance close path stamps through ApplyTypeInstWithKey
// instead, where source↔key is by construction).
func commitFoundThmStepWithKey(thmCache *ThmCache, n *GoalStackNode, entryKey core.PropKey) bool {
	Assert(!n.Goal.Proved())
	goals := StrongerGoals(n.Goal)

	// Tier 1 — exact AlphaKey hit.
	for _, g := range goals {
		if stronger := thmCache.LoadThm(g); stronger != nil {
			return n.runStep(_KnownThmStep{strongerGoal: stronger,
				sourceEntryKey: goalPayloadEntryKey(entryKey, n.Goal, stronger)})
		}
	}
	// Tier 2 — normalized-form AlphaKey hit. equivalentThm (when
	// non-nil) is normalize-equal to strongerGoal by construction of
	// the hit; _KnownThmStep.proto's backstop enforces this invariant
	// at serialization time.
	for _, g := range goals {
		if stronger, eq := thmCache.LoadNormalizedThm(g); stronger != nil {
			step := _KnownThmStep{strongerGoal: stronger,
				sourceEntryKey: goalPayloadEntryKey(entryKey, n.Goal, stronger)}
			if eq != nil {
				step.equivalentThm = eq
			}
			return n.runStep(step)
		}
	}
	// Tier 3 — type-instance hit: re-route to _TypeInstStep (see doc
	// above). The step's apply re-derives the instance from the source
	// against n.Goal; a hit found only on a strict StrongerGoals
	// variant (g ≠ n.Goal) may not re-derive against n.Goal itself —
	// in that rare case refuse the close (runStep returns false)
	// rather than fall back to the unreplayable instance shape.
	for _, g := range goals {
		if stronger, _, normSrc := thmCache.LoadMatchThmWithSource(g); stronger != nil {
			return n.runStep(_TypeInstStep{source: normSrc})
		}
	}
	return false
}

// goalPayloadEntryKey gates a caller-claimed registry identity onto a
// KnownThm payload: the claim describes GOAL's normalize-α class, so it
// transfers to the recorded payload only when the payload is in that
// same class. Returns "" (no stamp — payload-derived dep resolution
// applies) for an empty claim or a class mismatch.
func goalPayloadEntryKey(claimed core.PropKey, goal, payload Prop) core.PropKey {
	if claimed == "" {
		return ""
	}
	goalNorm, _ := Normalize(goal)
	payloadNorm, _ := Normalize(payload)
	if goalNorm.AlphaKey() != payloadNorm.AlphaKey() {
		return ""
	}
	return claimed
}

// TryByCaseTactic attempts boolean case split on caseTerm. Returns
// (positive, negative, true) in the split's own order: positive holds
// the term under one leading ¬ — caseTerm itself where it has none —
// and negative its negation, so for caseTerm ¬p positive holds p
// (ByCaseBranch names the branch on which caseTerm holds). Returns
// (nil, nil, false) if not applicable.
//
// Returns the RAW _ByCaseStep subgoals — the branches exactly as the
// session's `case_split` (ApplyByCase) and the chapter's a.Cases
// record them.
func TryByCaseTactic(goal Prop, caseTerm core.Term) (positive, negative Prop, ok bool) {
	subGoals, success := tryStep(goal, _ByCaseStep{caseTerm: caseTerm})
	if !success {
		return nil, nil, false
	}
	if subGoals.Size() != 2 {
		return nil, nil, false
	}
	return subGoals.ChildGoal(0), subGoals.ChildGoal(1), true
}

// TryInductionTactic attempts structural induction on inductVar using
// the given InductionTemplate. Returns (subGoals[0], subGoals[1], true)
// when the template has exactly two cases (num/list/option/sum and
// any other single-IH binary inductive); returns (nil, nil, false)
// otherwise — including when template is nil or has a different arity.
//
// For num the two children are:
//   - child(0): base case   (goal with _0 substituted for inductVar)
//   - child(1): step case   (inductVar as IH hyp, suc(inductVar) in concl)
//
// This is the search-phase entry point — callers that want the
// per-case subgoals without committing to the step yet (the engine's
// induction recommendations). For execution inside a proof use
// ApplyInduction (the session) / a.Induct (a chapter).
//
// Runs the BARE _InductionStep on a throwaway GoalStackNode — the same
// step both recording surfaces commit — so the step case a
// recommendation shows is the step case the tactic will hand over:
// `P(n) ⊢ P(suc n)` as the principle states it, no simplification.
func TryInductionTactic(goal Prop, inductVar core.VarTerm,
	template *tactic.InductionTemplate) (base, step Prop, ok bool) {
	n := CreateGoalStack(goal)
	if !ApplyInduction(n, inductVar, template) {
		return nil, nil, false
	}
	if len(n.children) != 2 {
		return nil, nil, false
	}
	return n.child(0).Goal, n.child(1).Goal, true
}

// CollectInductionVars finds all variables of type numType in a proposition
// that could serve as induction variables.
//
// Priority: free num-typed variables first (from conclusion + hypotheses).
// Only if none are found, fall back to forall-bound num-typed variables
// at the outermost level of the conclusion.
//
// This matters for goals like Q(n), h ⊢ ∀m:num. P(m): the free n from the
// hypothesis should be the induction candidate, not the bound m.
//
// indexType is the principle's index type, which must EQUAL a
// candidate variable's type (see the body); if nil, returns nil.
func CollectInductionVars(p Prop, indexType core.HolType) []core.VarTerm {
	if indexType == nil {
		return nil
	}

	var indexVars []core.VarTerm

	insert := func(v core.VarTerm) {
		i, found := slices.BinarySearchFunc(indexVars, v,
			func(v0, v1 core.VarTerm) int { return v0.Compare(v1) })
		if !found {
			indexVars = slices.Insert(indexVars, i, v)
		}
	}

	// First: collect free variables of the index type from the
	// conclusion and the hypotheses. The type must be EQUAL, not merely
	// an instance: GeneralInductionTactic asserts the template's index
	// type equals the variable's, so a caller holding a polymorphic
	// principle resolves it AT the variable's type first
	// (tactic.AnalyzePrincipleForType, what the engine's apply path
	// does) rather than passing the abstract index type here.
	for s := range utils.ConcatIter(utils.SingleIter(p.Conclusion()), p.HypIter()) {
		for _, fv := range s.Frees(
			func(v core.VarTerm) bool { return v.Type().Equals(indexType) }) {
			insert(fv)
		}
	}

	// Fallback: if no free ones were found, check forall-bound variables
	// at the outermost level of the conclusion.
	if len(indexVars) == 0 {
		vars, _ := ext.DecomposesFORALL(p.Conclusion())
		for v := range vars.Iter() {
			if v.Type().Equals(indexType) {
				insert(v)
			}
		}
	}

	return indexVars
}
