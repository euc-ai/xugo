package engine

import (
	"context"
	"fmt"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/utils"
)

// LemmaWithSpec is one entry in TacticReq.WithLemmas — same surface as
// `case "lemma"` accepts (key-or-text + optional type/term
// specialization), scoped to one auto_with call.
type LemmaWithSpec struct {
	Key            string            `json:"key,omitempty"`
	Text           string            `json:"text,omitempty"`
	TypeSpecialize map[string]string `json:"type_specialize,omitempty"`
	TermSpecialize map[string]string `json:"term_specialize,omitempty"`
	// ReadAt makes the entry a structure LAW read at an instance — the
	// Go `law.Read(instance)` (reading.go): `key` names the law, ReadAt
	// the instance (an entry, a resident hypothesis of the goal, or a
	// reading). The premise or rule is the law's statement with its
	// components pinned to the instance's and its structure hypothesis
	// discharged, derived by the kernel; a term_specialize table then
	// names the READING's binders, the component slots being gone. On a
	// `by` premise and a `simp_with` rule; `auto_with` refuses it.
	ReadAt *ReadAtSpec `json:"read_at,omitempty"`
	// Flip flips the orientation of an equation/iff rule for `simp_with`
	// — a first-class per-rule bit. When
	// true AND the resolved rule's ∀-stripped clause is `l = r` or
	// `l ⇔ r` (also inside a conditional `C₁ ⇒ … ⇒ (l = r)` or its
	// clause form `¬C₁ ∨ … ∨ (l = r)`), the simp-set driver applies
	// EqSym to the equation head BEFORE mining so the rule fires as
	// `r → l`. The RECORDED rule prop stays the entry's statement
	// (SimpWithProto.rules[i]) and only the parallel
	// SimpWithProto.rule_flip[i] bit changes — so the ministep's rule
	// child closes against the entry exactly as an unflipped rule
	// would, and emit resolves the same entry. Flipping a fact-shaped rule (a plain boolean P
	// that isn't an equation/iff after ∀-strip) is rejected at
	// resolveSimpWithRules with a typed error. On `auto_with` the
	// field is ignored (auto_with installs lemmas as hypotheses; there
	// is no orientation to flip). Composes with type_specialize /
	// term_specialize: those apply FIRST, then flip
	// swaps sides of the resolved rule's equation head. For
	// polymorphic no-explicit-σ multi-instance expansion, every
	// adapted copy carries the same flip bit.
	Flip bool `json:"flip,omitempty"`
	// Coefficient scales a `by` premise (the Go Scaled(c, h); Lean's
	// linear_combination coefficient): the lemma, an equation once
	// installed and grounded, is followed by its congruence under
	// multiplication by this term, added as a hypothesis. A term text
	// in the goal's scope. Refused on `simp_with` and `auto_with`, which
	// have no premise to scale.
	Coefficient string `json:"coefficient,omitempty"`
	// Normalized serves the rule in the orientation the NORMALIZER
	// gives the entry's statement — the session twin of the Go
	// `Fwd(MakeFact(ctx.DepNormalized(name)))` — instead of the stated form a
	// key cite serves (registryLemma). The rule the driver records is
	// proof.NormalizedForm(stated): the closed clause form with the
	// stated ∀-prefix order, exactly what ctx.DepNormalized resolves
	// to, so the recorded prop, the emitted `Simp(Fwd(MakeFact(
	// ctx.DepNormalized(<var>))))` and replay agree byte-for-byte. It exists for the
	// one-pass rewrite whose middle rule leaves an equation
	// in the orientation a later rule's STATED form has no redex for
	// (`0 = list_length(l) + list_length(m)` meets `nat_arith.AddEqZero` stated as
	// `m + n = 0 ⇔ …`, whose normal form reads `0 = m + n ⇔ …`).
	// Composes with flip (normalize first, then turn the equation
	// around) and with the polymorphic multi-instance expansion (each
	// adapted copy is the normalized form at that instance — emitted as
	// `Fwd(ctx.AtTypes(ctx.DepNormalized(name), τ…))`). Refused beside
	// an explicit type_specialize / term_specialize (a specialized
	// instance is served stated, as AtTypes serves it), on `by` (a
	// premise is installed in its normalized clause form already) and
	// on `auto_with` (an install, not a rewrite).
	Normalized bool `json:"normalized,omitempty"`
	// HypIndex makes the rule a RESIDENT hypothesis of the goal, by its
	// index — the session twin of the Go `Simp(Fwd(fact))` with fact a
	// resident Fact. The rule is the hypothesis assumed, `h ⊢ h`: it
	// fires where the goal holds h, a guarded equation as a conditional
	// rule whose guard discharges against the context, a closure as a
	// side-condition oracle, and its child closes on h itself, never on
	// an entry. Alone on its entry beside flip; on `simp_with` only.
	HypIndex *int `json:"hyp_index,omitempty"`
}

// applyAutoWithOnClone implements the `auto_with` tactic: clear noisy
// session ∀-hyps, install a scoped list of lemmas, then run arith +
// autoexpand on the focused clone. Close-or-fail: if the clone doesn't
// .Proved() at the end, return an error so the caller discards the
// clone — the session never absorbs the scoped state without a close.
//
// All sub-steps record standard ministeps on the clone via existing
// kernel paths (ApplyClearHyps / ApplyLemmaPreserveWithSource /
// ApplyArithSimplify / AutoExpand). MakeExpansionPlan preserves the
// chain, so replay re-runs the same sequence — no new proto tag, no
// replay-path change.
//
// Benign branching tolerated. A `lemma` install produces a SubGoals of
// size 2 — child[0] is the claim subgoal (`⊢ ψ`), child[1] is the
// residual. Claim closing runs BOTH close channels, same as plain
// `lemma` / `simp_with`:
//
//   - the sibling pass (`applyAutoMatchOnRoots`) for claims a proved
//     section of the session states;
//   - type-instance match (`applyAutoMatchTypeInstanceOnRoots` with the
//     entry's key + pre-specialization prop) for claims whose install
//     specialized (type_specialize / term_specialize σ) or internally
//     type-adapted a polymorphic entry, and for the entry's own
//     statement. Key-loaded entries only: an ad-hoc text lemma names no
//     entry for dep recording (same guard as plain `lemma`'s post-commit
//     runAutoMatchTypeInstance).
//
// When the claim STILL doesn't auto-match, it survives as a sibling
// leaf. Earlier revisions of auto_with rejected this with "unexpected
// branching — single-residual step produced 2 leaves"; agents on
// the union, difference, inclusion-exclusion and image laws of an
// iterated operation all hit it on multi-lemma chains and reported "the
// branching is benign". The strict guard is gone: subsequent installs
// target the LAST leaf (the most-recently-created residual), unmatched
// claim leaves accumulate as siblings, and the final close pass tries
// to close every leaf.
func (e *Engine) applyAutoWithOnClone(
	ctx context.Context,
	s *Session,
	clone *proof.GoalStackNode,
	req TacticReq,
) error {
	// Capture pre-state for the failure diagnostic — clone.Goal stays
	// stable (commitStep only sets miniStep / children), so reading it
	// at function end still gives the original input goal.
	preGoal := clone.Goal
	preForallCount := countForallHyps(preGoal)

	// (1) Clear pass — three modes:
	//   - DropHypIndices non-empty: exactly those indices
	//   - KeepHypIndices non-empty: everything NOT in keep
	//   - neither (default): every top-level ∀-headed hyp
	//     (the refute-poisoning class)
	leaf := clone
	toClear, cerr := computeAutoWithClearSet(leaf.Goal, req.KeepHypIndices, req.DropHypIndices)
	if cerr != nil {
		return cerr
	}
	if len(toClear) > 0 {
		if !proof.ApplyClearHyps(leaf, toClear) {
			return fmt.Errorf("auto_with: clear of hyps %v had no effect", toClear)
		}
		leaf = pickInstallLeaf(clone)
	}

	// (2) Install each scoped lemma on the current install leaf. Reuses
	// the existing lemma dispatch path (resolveLemma →
	// buildSpecializedLemma → ApplyLemmaPreserveWithSource) so the
	// polymorphic type-adapter / registry resolution behaviors are
	// identical to plain `lemma`. After each install, the
	// type-instance pass closes the claim leaf against the entry it names
	// (and the sibling pass against proved sections); surviving siblings
	// are tolerated and closed by the final pass.
	// Sources of the key-loaded entries, captured PRE-specialization
	// — fed to the type-instance close channel after each install and in
	// the final close pass (mirrors simp_with's srcs loop).
	type installSrc struct {
		key  core.PropKey
		prop core.Prop
	}
	var srcs []installSrc
	for i, l := range req.WithLemmas {
		if leaf == nil {
			break // all leaves closed already
		}
		if l.Normalized {
			return fmt.Errorf("auto_with: with_lemmas[%d]: normalized is a simp_with rule form — auto_with installs a lemma as a hypothesis, which the closer reads in its normalized clause form already", i)
		}
		if l.Coefficient != "" {
			return fmt.Errorf("auto_with: with_lemmas[%d]: coefficient scales a `by` premise (Lean's linear_combination) — auto_with has no premise to scale", i)
		}
		if l.ReadAt != nil {
			return fmt.Errorf("auto_with: with_lemmas[%d]: read_at reads a structure law at an instance, as a `by` premise or a `simp_with` rule — auto_with installs entries as they are stated", i)
		}
		if l.HypIndex != nil {
			return fmt.Errorf("auto_with: with_lemmas[%d]: hyp_index names a resident hypothesis as a `simp_with` rule — auto_with installs entries, and a resident hypothesis is in context already", i)
		}
		lemmaReq := TacticReq{
			Type:           "lemma",
			LemmaKey:       l.Key,
			LemmaText:      l.Text,
			TypeSpecialize: l.TypeSpecialize,
			TermSpecialize: l.TermSpecialize,
		}
		lemmaProp, lerr := e.resolveLemma(s, lemmaReq, leaf.Goal)
		if lerr != nil {
			return fmt.Errorf("auto_with: lemma #%d: %w", i, lerr)
		}
		if lemmaProp == nil {
			return fmt.Errorf("auto_with: lemma #%d: missing key or text", i)
		}
		if l.Key != "" {
			srcs = append(srcs, installSrc{key: core.PropKey(l.Key), prop: lemmaProp})
		}
		// No recorded source key for a bare cite (same as the `lemma`
		// dispatch: a Key may be a registry NAME, not a statement
		// key); a specialization records its polymorphic source.
		var srcKey core.PropKey
		var fixed core.VarTypePredicate = utils.EmptyPredicate[core.VarType]
		if len(l.TypeSpecialize) > 0 {
			specialized, goalLetters, sErr := buildSpecializedLemma(lemmaProp, l.TypeSpecialize, leaf.Goal)
			if sErr != nil {
				return fmt.Errorf("auto_with: lemma #%d: %w", i, sErr)
			}
			srcKey = proof.LemmaSourceKey(lemmaProp)
			lemmaProp, fixed = specialized, goalLetters
		}
		if len(l.TermSpecialize) > 0 {
			specialized, sErr := e.buildTermSpecializedLemma(lemmaProp, l.TermSpecialize, leaf.Goal, s.familyScope(), fixed)
			if sErr != nil {
				return fmt.Errorf("auto_with: lemma #%d: %w", i, sErr)
			}
			if srcKey == "" {
				srcKey = proof.LemmaSourceKey(lemmaProp)
			}
			lemmaProp = specialized
		}
		// Explicit-σ fork — same contract as plain `lemma`'s dispatch: an
		// agent-supplied type/term specialization is honored EXACTLY (the
		// adapt-enabled install would let chooseTypeAdaptedStep's
		// speculative tryAdaptLemmaTypes re-bind a var-typed σ target to
		// the goal-context instance, silently overriding the agent).
		installed := false
		if len(l.TypeSpecialize) > 0 || len(l.TermSpecialize) > 0 {
			installed = proof.ApplyLemmaPreserveExactWithSource(leaf, lemmaProp, srcKey)
		} else {
			installed = proof.ApplyLemmaPreserveWithSource(leaf, lemmaProp, srcKey)
		}
		if !installed {
			return fmt.Errorf("auto_with: lemma #%d did not install (type mismatch or already a hyp?)", i)
		}
		s.applyAutoMatchOnRoots([]*proof.GoalStackNode{clone}, s.autoMatchCache)
		if l.Key != "" {
			// Type-instance channel for the just-installed entry: closes
			// the claim subgoal when the installed form is a (specialized
			// or type-adapted) instance of the polymorphic entry — the
			// sibling pass above cannot see those.
			src := srcs[len(srcs)-1]
			s.applyAutoMatchTypeInstanceOnRoots(
				[]*proof.GoalStackNode{clone}, src.key, src.prop, nil, s.autoMatchCache)
		}
		leaf = pickInstallLeaf(clone)
	}

	// (3) Close every remaining leaf. Run arith per-leaf, then autoexpand
	// on the whole clone (which iterates leaves internally), then a final
	// close pass for anything autoexpand simplified into a cited
	// entry's shape. Loop while progress is being made — multi-leaf states may
	// need several passes to fully close.
	for {
		if clone.Proved() {
			break
		}
		before := clone.NumUnsolvedLeaves()

		// arith per leaf. ApplyArithSimplify operates on a single leaf
		// via runStep, and UnsolvedLeaves only returns nodes with no
		// miniStep set, so calling runStep is safe per element. Gated
		// per leaf on the explicit `arith` tactic's shape predicate —
		// an ungated pass records a spurious StepProto_Arith on
		// arith-free leaves (the generic logic rewrites share _Arith's
		// fixpoint), recording a use of the whole arith:nat bundle; see
		// the `auto` fast-path gate in engine.go.
		for _, lf := range clone.UnsolvedLeaves() {
			if goalHasArithContent(lf.Goal) {
				proof.ApplyArithSimplify(ctx, lf)
			}
		}
		if clone.Proved() {
			break
		}

		// autoexpand iterates over n.unsolvedLeavesIter() internally
		// (prover/proof/macro.go:110) so a single call attempts every leaf.
		// Skip when the clone has no unsolved leaves to avoid the
		// macro's "no unsolved leaves" panic on a freshly-closed state.
		if clone.NumUnsolvedLeaves() > 0 {
			_ = s.env.AutoExpandWithCtx(ctx).Apply(clone)
		}
		if clone.Proved() {
			break
		}

		// One more close pass — autoexpand may have simplified some
		// leaves into shapes that now match. Run both channels: the
		// sibling pass, then type-instance per installed entry (a
		// reshaped leaf may now be an instance of one of them).
		s.applyAutoMatchOnRoots([]*proof.GoalStackNode{clone}, s.autoMatchCache)
		for _, src := range srcs {
			s.applyAutoMatchTypeInstanceOnRoots(
				[]*proof.GoalStackNode{clone}, src.key, src.prop, nil, s.autoMatchCache)
		}
		if clone.Proved() {
			break
		}

		if clone.NumUnsolvedLeaves() >= before {
			break // no progress; surface as failure
		}
	}

	// (4) Close-or-fail.
	if !clone.Proved() {
		return formatAutoWithFailure(preGoal, preForallCount, toClear, req.WithLemmas, clone)
	}
	return nil
}

// pickInstallLeaf returns the LAST unsolved leaf — the most-recently-
// created residual after a lemma install — or nil when all leaves are
// closed. Multi-leaf intermediate states are accepted: surviving claim
// siblings stay open and are closed by the final pass. The earlier
// "single residual" guard rejected this benign branching, which
// agents on the iterated-operation laws reported as the canonical false-positive failure mode.
func pickInstallLeaf(clone *proof.GoalStackNode) *proof.GoalStackNode {
	leaves := clone.UnsolvedLeaves()
	if len(leaves) == 0 {
		return nil
	}
	return leaves[len(leaves)-1]
}

// formatAutoWithFailure renders the close-or-fail diagnostic: what state
// auto_with was entered with, what it cleared/installed, and what's still
// open. The output is one line per fact + a one-line hint, so an agent
// reading the failure can decide between (a) preserve a needed ∀-hyp via
// keep_hyp_indices, (b) add a missing lemma, or (c) fall back to manual
// `lemma + auto`. Hyps and concl are abbreviated at ~120 chars so a wide
// goal doesn't blow up the diagnostic.
func formatAutoWithFailure(
	preGoal core.Prop,
	preForallCount int,
	cleared []int,
	withLemmas []LemmaWithSpec,
	clone *proof.GoalStackNode,
) error {
	var b strings.Builder
	fmt.Fprintf(&b, "auto_with: did not close.\n")
	fmt.Fprintf(&b, "  Initial: %d hyps (%d ∀-headed)\n",
		preGoal.NumHyps(), preForallCount)

	// Cleared list — show indices + short shapes for the first few.
	if len(cleared) > 0 {
		fmt.Fprintf(&b, "  Cleared: %d hyps at indices %v\n", len(cleared), cleared)
		max := 3
		shown := 0
		for _, idx := range cleared {
			if shown >= max {
				fmt.Fprintf(&b, "    ... +%d more cleared hyps\n", len(cleared)-max)
				break
			}
			fmt.Fprintf(&b, "    [%d] %s\n", idx, abbreviateTerm(preGoal.Hyp(idx), 120))
			shown++
		}
	} else {
		fmt.Fprintf(&b, "  Cleared: 0 hyps (default heuristic found no ∀-headed hyps to drop)\n")
	}

	// Installed lemmas — show key or text identifier.
	if len(withLemmas) > 0 {
		fmt.Fprintf(&b, "  Installed: %d lemma(s)\n", len(withLemmas))
		max := 5
		shown := 0
		for _, l := range withLemmas {
			if shown >= max {
				fmt.Fprintf(&b, "    ... +%d more installed lemmas\n", len(withLemmas)-max)
				break
			}
			fmt.Fprintf(&b, "    - %s\n", lemmaIdentifier(l))
			shown++
		}
	} else {
		fmt.Fprintf(&b, "  Installed: 0 lemmas (called auto_with with empty with_lemmas)\n")
	}

	// Residual leaves — what auto+arith couldn't close. Show up to 3.
	leaves := clone.UnsolvedLeaves()
	fmt.Fprintf(&b, "  Residual: %d open leaf(es)\n", len(leaves))
	max := 3
	anyContraposed := false
	for i, lf := range leaves {
		if i >= max {
			fmt.Fprintf(&b, "    ... +%d more open leaves\n", len(leaves)-max)
			break
		}
		marker := ""
		if isContraposedConcl(preGoal, lf.Goal.Conclusion()) {
			marker = "   ← contraposed hyp"
			anyContraposed = true
		}
		fmt.Fprintf(&b, "    [%d] %d hyps (%d ∀-headed) ⊢ %s%s\n",
			i, lf.Goal.NumHyps(), countForallHyps(lf.Goal),
			abbreviateTerm(lf.Goal.Conclusion(), 120), marker)
	}
	if anyContraposed {
		fmt.Fprintf(&b, "  Note: \"← contraposed hyp\" — refutation-form normalization flipped a "+
			"pre-auto negated hypothesis's body into the conclusion; the leaf keeps its full hyp "+
			"context and is equivalent to refuting that branch, NOT a new freestanding obligation.\n")
	}

	// Actionable hint — pick one based on what we see.
	hint := autoWithHint(preForallCount, cleared, withLemmas, leaves)
	if hint != "" {
		fmt.Fprintf(&b, "  Hint: %s\n", hint)
	}

	return fmt.Errorf("%s", strings.TrimRight(b.String(), "\n"))
}

// isContraposedConcl reports whether concl α-equals the body of a negated
// hypothesis of preGoal — i.e. the leaf is ContrapositionTactic's
// proof-by-contradiction reformulation of that hyp, not a fact auto newly
// demands. Without the marker, agents read such leaves as unprovable
// minted obligations (the conclusion alone looks underivable).
func isContraposedConcl(preGoal core.Prop, concl core.Term) bool {
	for i := range preGoal.NumHyps() {
		if body := ext.MatchesNOT(preGoal.Hyp(i)); body != nil && body.AlphaEquals(concl) {
			return true
		}
	}
	return false
}

// autoWithHint returns one actionable suggestion based on the failure shape,
// or "" when nothing specific applies. Priority order: bad clear → missing
// lemmas → claim-subgoals-unmatched → branching residual → ∀-hyp survived
// → generic fallback advice.
func autoWithHint(
	preForallCount int,
	cleared []int,
	withLemmas []LemmaWithSpec,
	residualLeaves []*proof.GoalStackNode,
) string {
	if len(cleared) == preForallCount && preForallCount > 0 && len(residualLeaves) > 0 {
		return "default heuristic cleared all ∀-hyps; try keep_hyp_indices=[<idx>] " +
			"to preserve a hyp the goal still needs, or drop_hyp_indices for finer control"
	}
	if len(withLemmas) == 0 && len(residualLeaves) > 0 {
		return "no with_lemmas given; if the residual needs an entry to chain, " +
			"add it via with_lemmas: [{key: \"<entry>\"}]"
	}
	// Multiple residuals AND we installed lemmas: the most likely cause is
	// claim-subgoal-unmatched (a lemma install's `⊢ ψ` child didn't close
	// against its entry). Distinguish that from a real branching by checking if every
	// extra leaf is short / lemma-claim-shaped — heuristic: if there's more
	// than one leaf AND we installed N lemmas, suspect (residual - 1) claim
	// leaves.
	if len(residualLeaves) > 1 && len(withLemmas) > 0 {
		return fmt.Sprintf("residual has %d open leaves after %d lemma install(s); "+
			"likely some lemma claim subgoals didn't close against their entries "+
			"(normalization gap or polymorphic-key mismatch). Fall back to manual "+
			"`lemma + auto` to see which install left an open claim",
			len(residualLeaves), len(withLemmas))
	}
	if len(residualLeaves) > 1 {
		return fmt.Sprintf("residual has %d open branches; consider split_disj / case_split + "+
			"auto_with per branch instead of one shared call", len(residualLeaves))
	}
	if len(residualLeaves) > 0 {
		if countForallHyps(residualLeaves[0].Goal) > 0 {
			return "residual still carries ∀-hyp(s); the chain may need an instantiate " +
				"or a type_specialize on one of the installed lemmas"
		}
	}
	return "fall back to manual `lemma + auto` to see where the chain breaks"
}

// countForallHyps returns the number of top-level ∀-headed hyps. The same
// predicate the default-clear heuristic uses (matchesFORALL), so the
// pre/post counts in the diagnostic align with what the heuristic saw.
func countForallHyps(p core.Prop) int {
	n := 0
	for i := 0; i < p.NumHyps(); i++ {
		if !ext.MatchesFORALL(p.Hyp(i)).IsZero() {
			n++
		}
	}
	return n
}

// abbreviateTerm renders a Term and clips it at maxLen, suffixing "…" when
// truncated, so a wide goal doesn't dominate the failure diagnostic.
func abbreviateTerm(t core.Term, maxLen int) string {
	return abbreviateString(ext.PrintTerm(t), maxLen)
}

// lemmaIdentifier picks the most informative single-line label for a
// LemmaWithSpec: the key when given, else the text (clipped), else a
// placeholder for the empty case.
func lemmaIdentifier(l LemmaWithSpec) string {
	if l.Key != "" {
		parts := []string{l.Key}
		if len(l.TypeSpecialize) > 0 {
			parts = append(parts, fmt.Sprintf("type_specialize=%v", l.TypeSpecialize))
		}
		if len(l.TermSpecialize) > 0 {
			parts = append(parts, fmt.Sprintf("term_specialize=%v", l.TermSpecialize))
		}
		return strings.Join(parts, " with ")
	}
	if l.Text != "" {
		return fmt.Sprintf("text: %s", abbreviateTerm0(l.Text, 80))
	}
	return "(no key or text — invalid entry)"
}

// abbreviateTerm0 abbreviates a raw string (for LemmaText, not a Term).
func abbreviateTerm0(s string, maxLen int) string {
	return abbreviateString(s, maxLen)
}

func abbreviateString(s string, maxLen int) string {
	s = strings.ToValidUTF8(s, "�")
	if maxLen <= 0 {
		return ""
	}
	runes := []rune(s)
	if len(runes) <= maxLen {
		return s
	}
	if maxLen == 1 {
		return "…"
	}
	return string(runes[:maxLen-1]) + "…"
}

// computeAutoWithClearSet picks the hyp indices to clear. Returns a
// deduped sorted list, or an error if an index is out of range.
//
//   - drop non-empty: exactly that set (explicit drop list).
//   - keep non-empty: every index in [0, NumHyps) NOT in keep.
//   - neither: every top-level ∀-headed hyp (default heuristic for
//     refute-poisoning class — narrow non-∀ hyps stay, wide ∀-hyps
//     from prior lemma() / def_expand calls go).
//
// drop and keep are mutually exclusive at the agent layer (validated
// before this point); both non-empty is a usage error.
func computeAutoWithClearSet(goal core.Prop, keep, drop []int) ([]int, error) {
	if len(drop) > 0 && len(keep) > 0 {
		return nil, fmt.Errorf("auto_with: keep_hyp_indices and drop_hyp_indices are mutually exclusive")
	}
	n := goal.NumHyps()
	if len(drop) > 0 {
		return validateAndSort(drop, n, "drop_hyp_indices")
	}
	if len(keep) > 0 {
		if _, err := validateAndSort(keep, n, "keep_hyp_indices"); err != nil {
			return nil, err
		}
		keepSet := make(map[int]bool, len(keep))
		for _, i := range keep {
			keepSet[i] = true
		}
		out := make([]int, 0, n)
		for i := 0; i < n; i++ {
			if !keepSet[i] {
				out = append(out, i)
			}
		}
		return out, nil
	}
	// Default heuristic: clear every top-level ∀-headed hyp.
	out := []int{}
	for i := 0; i < n; i++ {
		if !ext.MatchesFORALL(goal.Hyp(i)).IsZero() {
			out = append(out, i)
		}
	}
	return out, nil
}

func validateAndSort(in []int, bound int, field string) ([]int, error) {
	seen := make(map[int]bool, len(in))
	out := make([]int, 0, len(in))
	for _, x := range in {
		if x < 0 || x >= bound {
			return nil, fmt.Errorf("auto_with: %s entry %d out of range [0, %d)", field, x, bound)
		}
		if seen[x] {
			return nil, fmt.Errorf("auto_with: %s contains duplicate index %d", field, x)
		}
		seen[x] = true
		out = append(out, x)
	}
	sort.Ints(out)
	return out, nil
}
