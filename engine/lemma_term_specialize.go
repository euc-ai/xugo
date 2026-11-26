package engine

import (
	"fmt"
	"sort"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/dsl"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/prover/proof"
	"github.com/euc-ai/xugo/prover/tactic"
	"github.com/euc-ai/xugo/prover/typematch"
	"github.com/euc-ai/xugo/utils"
)

// termSpecWitness pairs a term_specialize map key with its resolved
// witness term. `free` marks a sequent-level FREE variable of the lemma
// (free in the conclusion or any hypothesis) as opposed to an outer
// ∀-binder of the conclusion. The two kinds are applied differently by
// applyLemmaTermSpecializeChain: free vars are auto-generalized by the
// install's hypMatching to the OUTERMOST ∀-positions of the added hyp
// (matched by NAME there), while outer-binder witnesses are peeled
// positionally in lemma-binder order (their post-install names may have
// been α-renamed by the denorm path's collision handling).
type termSpecWitness struct {
	name    string
	witness core.Term
	free    bool
}

// resolveTermSpecializeWitnesses validates `m` against the lemma's
// outer ∀-binders AND its sequent-level free variables, returning the
// corresponding witnesses. Outer-binder witnesses come in lemma-binder
// order (outside-in); the binder walk stops at the first outer ∀-binder
// whose name is NOT in `m`. Sequent-level free-var witnesses (instantiation
// targets — sound by the INST rule on a theorem's free variables) are
// resolved by name. Every key in `m` MUST be consumed; an unmatched key
// indicates the key lives below a non-specialized binder (or is a typo).
//
// For each (binder|free var, witness) pair the witness is parsed
// against the goal's scope and read at the variable's type
// (proof.FitWitness: a bare polymorphic constant's fresh letters take
// the binder's type); if the variable's type contains a type variable,
// the unifier matches it against the witness's concrete type and
// σ_type accumulates across the chain. The accumulated σ_type is
// applied to the lemma once at the end, returning a "pre-install lemma"
// whose variable types are concrete (or pinned to goal-local Skolems),
// and to the witnesses, which spell the lemma's letters as it does.
//
// fixed admits the lemma's type letters that are the goal's own — a
// reading's hypothesis letters, the letters an explicit type_specialize
// read at the goal's (buildSpecializedLemma) — never freshened apart
// from the goal's and never instantiated; a plain lemma's letters are
// all its own.
//
// Returns:
//   - witnesses []termSpecWitness (binder ones in lemma-binder order,
//     then free-var ones in sorted-name order)
//   - the type-adapted lemma (core.Prop), with σ_type applied
//   - typesPinned: the witnesses bind EVERY type variable of the lemma
//     — the instance is then the author's, whatever letters it is
//     stated over (the goal's own included), and false for a lemma
//     with a type variable the tuple leaves free
//   - error if any name is unknown, witness parse fails, types can't
//     unify, or a key in m wasn't consumed
func (e *Engine) resolveTermSpecializeWitnesses(
	lemma core.Prop,
	m map[string]string,
	goal core.Prop,
	family *familyScope,
	fixed core.VarTypePredicate,
) (witnessList []termSpecWitness, adapted core.Prop, typesPinned bool, err error) {
	if len(m) == 0 {
		return nil, lemma, false, nil
	}
	if m, err = textBinderTable(m); err != nil {
		return nil, nil, false, err
	}

	available := collectGuardedForAllBinderNames(lemma)
	sequentFrees := collectSequentFreeVars(lemma)
	var freeNames []string
	for k := range m {
		if available[k] {
			continue
		}
		if _, isFree := sequentFrees[k]; isFree {
			// Sequent-level free variable — specializable by instantiation.
			freeNames = append(freeNames, k)
			continue
		}
		msg := fmt.Sprintf(
			"term_specialize: ∀-binder %q not found in lemma's outer binders; available: %v",
			k, printedBinderNames(available))
		if len(sequentFrees) > 0 {
			msg += fmt.Sprintf("; sequent-level free vars (also specializable): %v",
				sortedFreeVarNames(sequentFrees))
		}
		return nil, nil, false, fmt.Errorf("%s", msg)
	}
	sort.Strings(freeNames) // deterministic resolve order

	// α-rename the lemma's type vars to fresh names disjoint from the
	// goal's type-var universe BEFORE unifying against goal-side witness
	// types. Without this rename, a lemma type var (e.g. lemma "B") and a
	// goal type var with the same NAME collide inside `MatchTypeInto`'s
	// env: env lookup is name-based (`VarType.equalsVar`), so a prior
	// iteration's binding `{lemma-A → goal-B}` looks up positive for
	// lemma-B in the next iteration and rejects the correct binding
	// `{lemma-B → prod(A,B)}` as inconsistent (goal-B ≠ prod(A,B)). See
	// `TestApply_LemmaTermSpecialize_GoalLemmaTypeVarNameCollision` for the
	// verbatim finite_set.FiniteImage repro. The rename is undone at the end
	// for the letters no witness bound (typematch.ResidualLetterNames): each
	// keeps its lemma name unless the goal spells that name too. A fixed
	// letter is the goal's own and is not renamed.
	freshen, unfreshen := freshenLemmaTypeVars(lemma, goal, fixed)
	renamedLemma := lemma
	if len(freshen) > 0 {
		renamedLemma = core.PropTypeInst(lemma, freshen...)
	}

	renamedTypeVarNames := collectLemmaTypeVarNames(renamedLemma)
	instantiable := func(v core.VarType) bool {
		return renamedTypeVarNames[string(v.Name())] && !fixed(v)
	}

	current := prop.WrapProp(renamedLemma)
	var witnesses []termSpecWitness
	var freeWitnesses []termSpecWitness
	var σ []core.TypeSubst
	consumed := make(map[string]bool, len(m))

	// Free sequent-level vars pass (runs FIRST so the σ_type its
	// witnesses pin is visible to the binder walk below). The lookup
	// uses the RENAMED lemma's free vars so their types carry the
	// fresh (collision-proof) type-var names that `instantiable` and
	// σ operate on; freshening only touches type-var names, so the
	// term-level names validated against the original lemma above
	// still resolve here.
	renamedFrees := collectSequentFreeVars(renamedLemma)
	for _, k := range freeNames {
		v := renamedFrees[k]
		spelling := m[k]
		witness, perr := e.resolveTermWithFallback(spelling, goal, nil, family)
		if perr != nil {
			return nil, nil, false, fmt.Errorf("term_specialize[%s]: %w", k, perr)
		}
		witness, perr = witnessAtBinder(k, v.Type(), spelling, witness, instantiable, &σ)
		if perr != nil {
			return nil, nil, false, perr
		}
		freeWitnesses = append(freeWitnesses, termSpecWitness{name: k, witness: witness, free: true})
		consumed[k] = true
	}
	if clean := dropIdentityTypeSubsts(σ); len(clean) > 0 {
		// Surface the free-pass σ on the binder-walk cursor so binder
		// types reflect it (idempotent re-application is harmless —
		// the binder loop below re-applies the whole accumulated σ).
		current = prop.WrapProp(core.PropTypeInst(current, clean...))
	}

	for {
		// A guarded lemma states its content behind an antecedent
		// (`∀op. monoidal_op(op) ⇒ ∀f p s. …`): the binders after the
		// guard are the ones a ground cite names, so the walk steps
		// over an implication whenever a ∀ lies below it — the same
		// read the specialize step performs when it grounds.
		current = prop.WrapProp(prop.MakeProp(skipLeadingGuards(current.Conclusion())))
		abs := ext.MatchesFORALL(current.Conclusion())
		if abs.IsZero() {
			break
		}
		binderName := string(abs.Var().Name())
		spelling, present := m[binderName]
		if !present {
			break
		}
		binderType := abs.Var().Type()

		witness, perr := e.resolveTermWithFallback(spelling, goal, nil, family)
		if perr != nil {
			return nil, nil, false, fmt.Errorf("term_specialize[%s]: %w", binderName, perr)
		}
		witness, perr = witnessAtBinder(binderName, binderType, spelling, witness, instantiable, &σ)
		if perr != nil {
			return nil, nil, false, perr
		}

		clean := dropIdentityTypeSubsts(σ)
		if len(clean) > 0 {
			// The σ belongs to the lemma's (now fresh-named) type
			// variables only. The witness is a goal/context term and
			// must remain rigid — with the freshen rename above, goal
			// type-vars never share a name with lemma type-vars, so
			// applying σ to `current` only touches lemma-owned positions.
			current = prop.WrapProp(core.PropTypeInst(current, clean...))
			// Re-peel to refresh the binder under the (possibly
			// updated) σ — the next iteration must see the post-σ
			// binder type.
			abs = ext.MatchesFORALL(current.Conclusion())
			if abs.IsZero() {
				// Shouldn't happen — type-σ doesn't peel ∀s.
				return nil, nil, false, fmt.Errorf(
					"term_specialize[%s]: internal: outer ∀ disappeared after type substitution",
					binderName)
			}
		}

		witnesses = append(witnesses, termSpecWitness{name: binderName, witness: witness})
		consumed[binderName] = true
		// Step past this binder for the next iteration.
		current = prop.WrapProp(makePeeledLemma(abs))
	}
	witnesses = append(witnesses, freeWitnesses...)

	for k := range m {
		if !consumed[k] {
			return nil, nil, false, fmt.Errorf(
				"term_specialize: ∀-binder %q lives below a non-specialized outer binder; "+
					"supply every outermost ∀-binder up to %q (or use plain `instantiate` for inner binders)",
				k, k)
		}
	}

	// Apply σ to the renamed lemma, then name the residual
	// (uninstantiated) fresh letters (typematch.ResidualLetterNames). A
	// witness read at a binder's letter spells that letter too, so the
	// witnesses take the same σ and the same names.
	σ = chainTypeSubsts(σ)
	out := core.PropTypeInst(renamedLemma, σ...)
	back := typematch.ResidualLetterNames(out, goal, unfreshen)
	if len(back) > 0 {
		out = core.PropTypeInst(out, back...)
	}
	for i := range witnesses {
		witnesses[i].witness = witnesses[i].witness.TypeSubstitute(σ...).TypeSubstitute(back...)
	}
	// The lemma's type variables carry names the goal's do not (the
	// freshening above), so "bound by the tuple" is read off σ by name —
	// the instance itself cannot say, since one stated over the goal's
	// letters has type variables left and binds every one of the lemma's.
	bound := make(map[string]bool, len(σ))
	for _, sub := range dropIdentityTypeSubsts(σ) {
		bound[string(sub.VarType.Name())] = true
	}
	typesPinned = len(renamedTypeVarNames) > 0
	for name := range renamedTypeVarNames {
		if !bound[name] {
			typesPinned = false
			break
		}
	}
	return witnesses, out, typesPinned, nil
}

// witnessAtBinder reads a resolved witness at the binder it grounds
// (proof.FitWitness: a bare polymorphic constant's fresh letters take
// the binder's type, the lemma's own letters open to it) and matches
// the binder's type against the witness so read, the lemma's letters
// binding into σ. An identity entry the match records — a lemma letter
// the witness now spells, met by itself — is dropped: the letter is
// the lemma's, still open for a later witness to fix. A witness that
// fits the binder no way, or still carries a letter the binder does not
// fix, is refused naming the binder's type, the witness's, and the
// ⟨A:τ⟩ tie that pins the letter.
func witnessAtBinder(name string, binder core.HolType, spelling string, witness core.Term, instantiable core.VarTypePredicate, σ *[]core.TypeSubst) (core.Term, error) {
	fitted, ok := proof.FitWitness(binder, witness, instantiable, *σ)
	if !ok || !core.MatchTypeInto(binder, fitted.Type(), instantiable, σ) {
		return nil, fmt.Errorf("term_specialize[%s]: the witness %q of type %s does not fit the binder %s:%s%s",
			name, spelling, ext.FormatType(witness.Type()), utils.FormatSubscript(name), ext.FormatType(binder),
			proof.UnpinnedWitnessRepair(witness, binder))
	}
	*σ = dropIdentityTypeSubsts(*σ)
	if repair := proof.UnpinnedWitnessRepair(fitted, binder); repair != "" {
		return nil, fmt.Errorf("term_specialize[%s]: the witness %q of type %s leaves a letter the binder %s:%s does not fix%s",
			name, spelling, ext.FormatType(witness.Type()), utils.FormatSubscript(name), ext.FormatType(binder), repair)
	}
	return fitted, nil
}

// chainTypeSubsts resolves a substitution recorded binding by binding
// — a later binding may fix a letter an earlier one's target spells
// (f at `♭B → ♭B` read for `♭A → ♭B`, then s : set(num) for `set(♭B)`)
// — into one whose targets spell no letter it binds, so that applied
// at once it reads as the bindings read in order.
func chainTypeSubsts(substs []core.TypeSubst) []core.TypeSubst {
	out := append([]core.TypeSubst(nil), substs...)
	for range out {
		changed := false
		for i, s := range out {
			target := s.HolType.Substitute(out...)
			if !target.Equals(s.HolType) {
				out[i] = core.MakeTypeSubst(s.VarType, target)
				changed = true
			}
		}
		if !changed {
			break
		}
	}
	return out
}

// makePeeledLemma returns the body Prop after stripping one outer ∀
// (without substituting the bound var). Used by
// resolveTermSpecializeWitnesses for the iteration cursor — the cursor
// only needs to track "what's the NEXT outer binder", not the result
// of any β-substitution (β happens post-install via the instantiate
// chain).
func makePeeledLemma(abs core.AbsTerm) core.Prop {
	// Peel: replace concl with the body of the ∀-binder. We retain
	// the bound var as a fresh free var via ConclForAllInst at the
	// bound var itself — this is the identity peel.
	body := abs.Body()
	_ = body
	// Cheap path: just wrap the body as a Prop. We don't care about
	// hyps for the cursor — only the conclusion's outer ∀-chain
	// matters for resolveTermSpecializeWitnesses' purposes.
	return prop.MakeProp(body)
}

// applyLemmaTermSpecializeChain grounds the just-installed lemma hyp
// for `lemma + term_specialize`. The clone has been advanced past the
// `lemma_preserve` install — the residual leaf carries the lemma's
// conclusion as a ∀-headed hyp (with any goal-side free vars
// auto-generalized to the outermost positions by hypMatching). The
// grounding is ONE composite `specialize` ministep
// (proof.ApplySpecialize): the installed hyp's outer ∀-binders are
// peeled at `witnesses` (in order) with only the final instance added,
// and the source ∀-hyp consumed — the intermediate partials never
// materialize on any goal, so emit renders one line and replay re-runs
// the same driver (tactic.SpecializeTactic).
//
// `lemma` is the PRE-install form (with any pre-σ_type applied by
// resolveTermSpecializeWitnesses). Outer-binder witnesses are in
// lemma-binder order — the order they're peeled positionally from the
// post-install hyp. Free-var witnesses are matched by NAME against the
// hyp's outermost ∀-binders (hypMatching auto-generalizes the lemma's
// sequent-level free vars to the outermost positions on install).
// `originalGoalHypKeys` snapshots the focused goal's hyp set before
// lemma install, so we can identify the newly-added ∀-headed hyp
// regardless of canonical reordering.
func (e *Engine) applyLemmaTermSpecializeChain(
	clone *proof.GoalStackNode,
	lemma core.Prop,
	witnesses []termSpecWitness,
	originalGoalHypKeys map[core.TermKey]struct{},
) error {
	if len(witnesses) == 0 {
		return nil
	}

	freeByName := make(map[string]core.Term)
	freeNames := make(map[string]bool)
	var binderWitnesses []termSpecWitness
	for _, w := range witnesses {
		if w.free {
			freeByName[w.name] = w.witness
			freeNames[w.name] = true
		} else {
			binderWitnesses = append(binderWitnesses, w)
		}
	}

	residual, currentForAllTerm, found := findLemmaResidualLeaf(
		clone, originalGoalHypKeys, lemma, freeNames)
	if !found {
		return fmt.Errorf(
			"term_specialize: lemma was consumed by the eq-rewrite path "+
				"or the conclusion-match path (no newly-added ∀-headed hyp on "+
				"the residual leaf; conclusion matching instantiates the lemma's "+
				"free vars and ∀-binders by unification automatically). "+
				"Drop `term_specialize` and use plain `lemma`, or use `lean_rw` "+
				"(which accepts `term_specialize` for the rewrite-rule path). (lemma=%s)",
			prop.PrintProp(lemma))
	}

	// Pre-validate binder shape + witness types with verbose errors —
	// the composite tactic itself reports failure only as a bare
	// no-progress. Binder types don't depend on earlier witnesses, so
	// a structural Body() walk suffices.
	//
	// Peel order: the install's hypMatching generalizes the lemma's
	// sequent-level free vars to the OUTERMOST ∀-positions of the added
	// hyp (in an implementation-defined Frees order), so the free-var
	// section is matched by NAME first; the lemma's own outer ∀-binders
	// follow and are peeled positionally (their post-install names may
	// have been α-renamed by the denorm path's collision handling, so
	// positional matching is load-bearing there).
	var peel []core.Term
	cur := currentForAllTerm
	for len(freeByName) > 0 {
		abs := ext.MatchesFORALL(cur)
		if abs.IsZero() {
			break
		}
		name := string(abs.Var().Name())
		w, requested := freeByName[name]
		if !requested {
			break
		}
		if !abs.Var().Type().Equals(w.Type()) {
			return fmt.Errorf(
				"term_specialize[%s]: post-install ∀-binder type %s does not match witness type %s",
				name, ext.FormatType(abs.Var().Type()), ext.FormatType(w.Type()))
		}
		peel = append(peel, w)
		delete(freeByName, name)
		cur = abs.Body()
	}
	if len(freeByName) > 0 {
		leftover := make([]string, 0, len(freeByName))
		for k := range freeByName {
			leftover = append(leftover, k)
		}
		sort.Strings(leftover)
		return fmt.Errorf(
			"term_specialize: free var(s) %v not found among the outermost ∀-binders "+
				"of the installed hyp %s — either the free var is buried below a "+
				"non-specialized auto-generalized binder (specialize the outer ones too, "+
				"or use `instantiate`), or the install path renamed it",
			leftover, ext.PrintTerm(currentForAllTerm))
	}
	for i, w := range binderWitnesses {
		cur = skipLeadingGuards(cur)
		abs := ext.MatchesFORALL(cur)
		if abs.IsZero() {
			return fmt.Errorf(
				"term_specialize[%d]: residual ∀-binder exhausted (have %d witnesses, only %d ∀-binders reachable through leading implications on the installed hyp)",
				i, len(witnesses), len(peel)+i)
		}
		// Witness type alignment: pre-σ_type already applied by
		// resolveTermSpecializeWitnesses, so binder.Type and
		// witness.Type should be equal. Defensive check.
		if !abs.Var().Type().Equals(w.witness.Type()) {
			return fmt.Errorf(
				"term_specialize[%d]: post-install ∀-binder type %s does not match witness type %s "+
					"(the install pipeline's tryAdaptLemmaTypes may have applied a competing σ — "+
					"this should be impossible since case \"lemma\" routes term_specialize through "+
					"ApplyLemmaPreserveExactWithSource which bypasses chooseTypeAdaptedStep; "+
					"if you see this, something else in the install path is mutating types)",
				i, ext.FormatType(abs.Var().Type()), ext.FormatType(w.witness.Type()))
		}
		peel = append(peel, w.witness)
		cur = abs.Body()
	}

	hypIdx, ok := findHypIndexByKey(residual.Goal, currentForAllTerm.AlphaKey())
	if !ok {
		return fmt.Errorf(
			"term_specialize: target ∀-hyp %s no longer present on residual leaf",
			ext.PrintTerm(currentForAllTerm))
	}
	if !proof.ApplySpecialize(residual,
		[]proof.SpecializeHyp{proof.InstHyp(hypIdx, peel...)}, false) {
		return fmt.Errorf(
			"term_specialize: specialize of hyp_index=%d at %d witness(es) made no progress "+
				"(the ground instance may already be in scope)",
			hypIdx, len(peel))
	}
	return nil
}

// findLemmaResidualLeaf locates the lemma_preserve "residual" leaf by
// searching for the open leaf that carries a newly-added ∀-headed hyp
// (one whose alpha-key is not in `origHypKeys`). That hyp is the
// installed lemma. Returns (nil, nil, false) when no open leaf carries
// such a hyp — typically because inner ran the eq-rewrite path (or,
// for free-var witnesses, the conclusion-match path) and the lemma is
// not installed as a hyp at all.
//
// Leaves α-equal to the lemma itself are skipped: they are the lemma's
// own reproduction child (open at chain time — the auto-match close
// runs post-Commit), and a hyps-carrying statement's reproduction child
// carries the lemma's own ∀-headed hyps, which the key filter would
// otherwise misidentify as the installed hyp.
//
// When `freeNames` is non-empty (free-var witnesses present), a
// candidate hyp must additionally carry every requested free name
// among its outermost ∀-binders (the auto-generalized section) — a
// pre-existing goal hyp restructured by simplifyNewGoal (∧-split) can
// otherwise masquerade as "newly added" and produce a misleading peel
// error instead of the actionable consumed-by-install diagnostic.
func findLemmaResidualLeaf(
	root *proof.GoalStackNode,
	origHypKeys map[core.TermKey]struct{},
	lemma core.Prop,
	freeNames map[string]bool,
) (*proof.GoalStackNode, core.Term, bool) {
	for _, leaf := range root.UnsolvedLeaves() {
		if leaf.Goal.AlphaEquals(lemma) {
			continue
		}
		if len(freeNames) == 0 {
			hyp, err := findAddedForAllHyp(leaf.Goal, origHypKeys)
			if err == nil {
				return leaf, hyp, true
			}
			continue
		}
		for i := leaf.Goal.NumHyps() - 1; i >= 0; i-- {
			h := leaf.Goal.Hyp(i)
			if _, was := origHypKeys[h.AlphaKey()]; was {
				continue
			}
			if hypFrontBindersCover(h, freeNames) {
				return leaf, h, true
			}
		}
	}
	return nil, nil, false
}

// hypFrontBindersCover reports whether every name in `names` appears
// among the hyp's outermost ∀-binder chain BEFORE any binder that is
// not in `names` — i.e. the peel (which can only instantiate a front
// prefix positionally) can reach all of them.
func hypFrontBindersCover(h core.Term, names map[string]bool) bool {
	remaining := len(names)
	seen := make(map[string]bool, len(names))
	cur := h
	for remaining > 0 {
		abs := ext.MatchesFORALL(cur)
		if abs.IsZero() {
			return false
		}
		n := string(abs.Var().Name())
		if !names[n] {
			return false
		}
		if !seen[n] {
			seen[n] = true
			remaining--
		}
		cur = abs.Body()
	}
	return true
}

func findAddedForAllHyp(goal core.Prop, origKeys map[core.TermKey]struct{}) (core.Term, error) {
	for i := goal.NumHyps() - 1; i >= 0; i-- {
		h := goal.Hyp(i)
		if _, was := origKeys[h.AlphaKey()]; was {
			continue
		}
		if ext.MatchesFORALL(h).IsZero() {
			continue
		}
		return h, nil
	}
	return nil, fmt.Errorf("no newly-added ∀-headed hyp on residual leaf")
}

func findHypIndexByKey(goal core.Prop, key core.TermKey) (int, bool) {
	for i := range goal.NumHyps() {
		if goal.Hyp(i).AlphaKey() == key {
			return i, true
		}
	}
	return 0, false
}

// buildTermSpecializedLemma applies an agent-supplied term-level
// substitution to a lemma's outer ∀-binders by β-substituting
// each named binder with the supplied witness. Used by the `lean_rw`
// dispatch — pure rewrite path, no install-as-hyp step, so the
// β-substituted lemma is the rewrite rule directly.
//
// `case "lemma"` does NOT use this path: install's hypMatching step
// auto-generalizes goal-side free vars before adding as a hyp, so a
// pre-install β-substitute would be undone by the install. That path
// uses applyLemmaTermSpecializeChain instead (post-install named
// instantiate chain), driven by resolveTermSpecializeWitnesses's
// pre-σ_type computation.
//
// fixed admits the lemma's type letters that are the goal's own — the
// letters an explicit type_specialize read at the goal's
// (buildSpecializedLemma) — never freshened apart from the goal's and
// never bound by a witness. A rewrite rule is never a reading, so no
// other letter of it is fixed.
func (e *Engine) buildTermSpecializedLemma(
	lemma core.Prop,
	m map[string]string,
	goal core.Prop,
	family *familyScope,
	fixed core.VarTypePredicate,
) (core.Prop, error) {
	if len(m) == 0 {
		return lemma, nil
	}
	m, err := textBinderTable(m)
	if err != nil {
		return nil, err
	}

	available := collectOuterForAllBinderNames(lemma)
	for k := range m {
		if !available[k] {
			if _, isFree := collectSequentFreeVars(lemma)[k]; isFree {
				return nil, fmt.Errorf(
					"term_specialize: %q is a sequent-level FREE variable of the lemma, "+
						"not an outer ∀-binder — free-var specialization is supported for "+
						"the `lemma` tactic only (its install auto-generalizes free vars); "+
						"use `lemma` instead of this rewrite-path verb. Outer binders available: %v",
					k, printedBinderNames(available))
			}
			return nil, fmt.Errorf(
				"term_specialize: ∀-binder %q not found in lemma's outer binders; available: %v",
				k, printedBinderNames(available))
		}
	}

	// α-rename lemma type vars away from goal-side names to avoid
	// name-based collision inside `MatchTypeInto`'s env. Mirrors the
	// resolveTermSpecializeWitnesses path — same bug shape (see the
	// comment there). A fixed letter is the goal's own and is not
	// renamed.
	freshen, unfreshen := freshenLemmaTypeVars(lemma, goal, fixed)
	renamedLemma := lemma
	if len(freshen) > 0 {
		renamedLemma = core.PropTypeInst(lemma, freshen...)
	}

	renamedTypeVarNames := collectLemmaTypeVarNames(renamedLemma)
	instantiable := func(v core.VarType) bool {
		return renamedTypeVarNames[string(v.Name())] && !fixed(v)
	}

	current := prop.WrapProp(renamedLemma)
	consumed := make(map[string]bool, len(m))

	for {
		// A guarded lemma states its content behind an antecedent
		// (`∀op. monoidal_op(op) ⇒ ∀f p s. …`): the binders after the
		// guard are the ones a ground cite names, so the walk steps
		// over an implication whenever a ∀ lies below it — the same
		// read the specialize step performs when it grounds.
		current = prop.WrapProp(prop.MakeProp(skipLeadingGuards(current.Conclusion())))
		abs := ext.MatchesFORALL(current.Conclusion())
		if abs.IsZero() {
			break
		}
		binderName := string(abs.Var().Name())
		spelling, present := m[binderName]
		if !present {
			break
		}
		binderType := abs.Var().Type()

		witness, perr := e.resolveTermWithFallback(spelling, goal, nil, family)
		if perr != nil {
			return nil, fmt.Errorf("term_specialize[%s]: %w", binderName, perr)
		}

		var subst []core.TypeSubst
		witness, perr = witnessAtBinder(binderName, binderType, spelling, witness, instantiable, &subst)
		if perr != nil {
			return nil, perr
		}

		clean := dropIdentityTypeSubsts(subst)
		if len(clean) > 0 {
			// Keep the witness rigid; see resolveTermSpecializeWitnesses.
			current = current.TypeInst(clean...)
		}

		current = current.ConclForAllInst(witness)
		consumed[binderName] = true
	}

	for k := range m {
		if !consumed[k] {
			return nil, fmt.Errorf(
				"term_specialize: ∀-binder %q lives below a non-specialized outer binder; "+
					"supply every outermost ∀-binder up to %q in the map (or load the lemma without term_specialize "+
					"and use `instantiate` for inner binders)",
				k, k)
		}
	}

	// The install boundary hands over instances in the normal form: a λ
	// witness applied inside the matrix mints redexes ConclForAllInst does
	// not reduce, and a packed record witness projections of it (the
	// tactic.SpecializeTactic contract, engine side).
	out := current.RewriteConcl(tactic.InstanceNormal(nil)).Core()
	if back := typematch.ResidualLetterNames(out, goal, unfreshen); len(back) > 0 {
		out = core.PropTypeInst(out, back...)
	}
	return out, nil
}

// collectSequentFreeVars returns the lemma's sequent-level free
// variables (free in the conclusion or in any hypothesis) keyed by
// name. These are the instantiation targets `term_specialize` accepts in
// addition to the conclusion's outer ∀-binders — e.g. binary induction
// stated as a sequent, `P(0), ∀n.(P(n) ⇒ P(2n) ∧ P(2n+1)) ⊢ ∀n.P(n)`, carries
// P free at the sequent level. When two distinct free vars share a
// name (shadowing across types — pathological), the first one seen
// (conclusion first, then hyps in order) wins.
func collectSequentFreeVars(p core.Prop) map[string]core.VarTerm {
	out := map[string]core.VarTerm{}
	collect := func(t core.Term) {
		for _, v := range t.Frees(nil) {
			name := string(v.Name())
			if _, dup := out[name]; !dup {
				out[name] = v
			}
		}
	}
	collect(p.Conclusion())
	for h := range p.HypIter() {
		collect(h)
	}
	return out
}

func sortedFreeVarNames(m map[string]core.VarTerm) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, k)
	}
	sort.Strings(out)
	return out
}

// collectOuterForAllBinderNames returns the set of names of the
// lemma's OUTER ∀-binders (the chain on the conclusion, outside-in,
// stopping at the first non-∀ head). Used to validate `term_specialize`
// keys.
// collectGuardedForAllBinderNames is collectOuterForAllBinderNames
// reading through leading implications: `∀op. A ⇒ ∀f p s. …` yields
// {op f p s}. The `lemma` path uses it — its install keeps the guard,
// and the composite specialize grounds through it. The lean_rw path
// keeps the outer-only read: it β-substitutes into the statement
// directly and has no guard-carrying instance to build.
func collectGuardedForAllBinderNames(p core.Prop) map[string]bool {
	out := map[string]bool{}
	for _, name := range guardedForAllBinderOrder(p) {
		out[name] = true
	}
	return out
}

// guardedForAllBinderOrder is collectGuardedForAllBinderNames keeping
// the STATED order: the binders reachable through leading
// implications, outside-in.
func guardedForAllBinderOrder(p core.Prop) []string {
	var out []string
	concl := p.Conclusion()
	for {
		concl = skipLeadingGuards(concl)
		abs := ext.MatchesFORALL(concl)
		if abs.IsZero() {
			return out
		}
		out = append(out, string(abs.Var().Name()))
		concl = abs.Body()
	}
}

// termSpecializeNamesPrefix reports whether the map's keys are exactly
// the first len(m) stated binders of the lemma — the shape the
// positional grounding path serves. Any other table is SPARSE: a
// binder is skipped, so no prefix instantiation can reach the named
// ones, and the premise becomes the apply rung's seeded head instead
// (proof.ByPremiseSpec.Named).
func termSpecializeNamesPrefix(lemma core.Prop, m map[string]string) bool {
	order := guardedForAllBinderOrder(lemma)
	if len(m) > len(order) {
		return false
	}
	for _, name := range order[:len(m)] {
		if _, present := m[name]; !present {
			return false
		}
	}
	return true
}

// skipLeadingGuards steps over leading implications while a ∀-binder
// is reachable below them; a term with no ∀ below its antecedents is
// returned unchanged.
func skipLeadingGuards(t core.Term) core.Term {
	for ext.MatchesFORALL(t).IsZero() {
		_, rest, ok := ext.MatchesIMPLY(t)
		if !ok || !forallReachableThroughGuards(rest) {
			return t
		}
		t = rest
	}
	return t
}

func forallReachableThroughGuards(t core.Term) bool {
	for {
		if !ext.MatchesFORALL(t).IsZero() {
			return true
		}
		_, rest, ok := ext.MatchesIMPLY(t)
		if !ok {
			return false
		}
		t = rest
	}
}

func collectOuterForAllBinderNames(p core.Prop) map[string]bool {
	out := map[string]bool{}
	concl := p.Conclusion()
	for {
		abs := ext.MatchesFORALL(concl)
		if abs.IsZero() {
			return out
		}
		out[string(abs.Var().Name())] = true
		concl = abs.Body()
	}
}

// printedBinderNames lists a lemma's binder names as every served
// statement prints them (`x₀` for the kernel's `x_0`), sorted — the
// spelling a term_specialize table takes (textBinderTable).
func printedBinderNames(m map[string]bool) []string {
	out := make([]string, 0, len(m))
	for k := range m {
		out = append(out, utils.FormatSubscript(k))
	}
	sort.Strings(out)
	return out
}

// printedBinderNamesWith is printedBinderNames for a reading: a binder
// the reading holds under another name than its law states (renamed,
// law name → held name) is listed under both, the law's first.
func printedBinderNamesWith(m map[string]bool, renamed map[string]string) []string {
	lawName := make(map[string]string, len(renamed))
	for law, held := range renamed {
		lawName[held] = law
	}
	out := make([]string, 0, len(m))
	for k := range m {
		if law, ok := lawName[k]; ok {
			out = append(out, fmt.Sprintf("%s (held here as %s)", utils.FormatSubscript(law), utils.FormatSubscript(k)))
			continue
		}
		out = append(out, utils.FormatSubscript(k))
	}
	sort.Strings(out)
	return out
}

// textBinderTable reads a term_specialize table's keys as the text DSL
// reads an identifier (dsl.IdentifierName): a binder printed `x₀` — in
// the statement, the served goal, `query member`, a brief — names the
// binder the kernel calls `x_0`, and both spellings are accepted. Two
// keys naming one binder are refused.
func textBinderTable(m map[string]string) (map[string]string, error) {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	out := make(map[string]string, len(m))
	spelled := make(map[string]string, len(m))
	for _, k := range keys {
		v := m[k]
		name := dsl.IdentifierName(k)
		if other, dup := spelled[name]; dup {
			return nil, fmt.Errorf("term_specialize: %q and %q name one binder, %s — name it once",
				other, k, utils.FormatSubscript(name))
		}
		spelled[name] = k
		out[name] = v
	}
	return out, nil
}

func dropIdentityTypeSubsts(subst []core.TypeSubst) []core.TypeSubst {
	out := make([]core.TypeSubst, 0, len(subst))
	for _, s := range subst {
		if !s.HolType.Equals(s.VarType) {
			out = append(out, s)
		}
	}
	return out
}

// freshenLemmaTypeVars returns a pair of type substitutions that α-renames
// the lemma's type variables to fresh names disjoint from `goal`'s
// type-var universe, and its inverse. Applied at the entry to the
// term_specialize path, the freshening isolates the lemma's polymorphic
// type vars from goal-side rigid type vars that happen to share the same
// (printed) name — which otherwise pollute `MatchTypeInto`'s
// name-keyed env and cause spurious binding-consistency failures.
//
// If lemma and goal already share no type-var names, both returned
// slices are empty and the caller can skip the (cheap) round-trip. The
// inverse is applied through typematch.ResidualLetterNames, never as it
// stands. A letter fixed admits is the goal's own — a reading's
// hypothesis letters, an explicit type_specialize's letters the goal
// spells — and shares its name with the goal's by identity, not
// collision: it is neither renamed nor counted as colliding.
//
// The fresh name scheme uses a Unicode-tag prefix (`♭`) that is not a
// legal DSL identifier char, so it cannot collide with any user-typed
// or registered type-var name.
func freshenLemmaTypeVars(lemma, goal core.Prop, fixed core.VarTypePredicate) (freshen, unfreshen []core.TypeSubst) {
	lemmaNames := collectLemmaTypeVarNames(lemma)
	for name := range lemmaNames {
		if fixed(core.MakeVarType(name)) {
			delete(lemmaNames, name)
		}
	}
	if len(lemmaNames) == 0 {
		return nil, nil
	}
	goalNames := collectLemmaTypeVarNames(goal)
	// Only rename the ones that actually collide (or MIGHT collide with
	// witness-side types — witnesses live in the goal's scope, so the
	// goal's type-var universe is a superset). To keep the rewrite
	// deterministic and self-contained, rename ALL lemma type-vars when
	// ANY collision exists; the unfreshen pass restores the names.
	collides := false
	for name := range lemmaNames {
		if goalNames[name] {
			collides = true
			break
		}
	}
	if !collides {
		return nil, nil
	}
	names := make([]string, 0, len(lemmaNames))
	for name := range lemmaNames {
		names = append(names, name)
	}
	sort.Strings(names) // deterministic order
	for _, name := range names {
		orig := core.MakeVarType(name)
		// ♭ is not a legal DSL identifier char (identifiers are
		// [A-Za-z_][A-Za-z0-9_]* plus the `?` prefix); goal-side
		// type-vars can only be spelled with those, so a name with `♭` at
		// front cannot collide.
		fresh := core.MakeVarType("♭" + name)
		freshen = append(freshen, core.MakeTypeSubst(orig, fresh))
		unfreshen = append(unfreshen, core.MakeTypeSubst(fresh, orig))
	}
	return freshen, unfreshen
}
