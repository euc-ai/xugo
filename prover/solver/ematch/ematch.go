// Package ematch is E-matching ground instantiation PLANNING: given a
// goal, enumerate ground instances of its ∀-hypotheses whose trigger
// patterns match the goal's own ground subterm pool. It produces PLANS
// (hypothesis + witness tuple), never applies them — application is the
// caller's step vocabulary (proof.ApplySpecialize), so the search and
// its heuristics stay out of every recorded artifact.
//
// Two callers, one algorithm:
//
//   - the session-level `ematch` tactic (engine/ematch.go), the
//     agent-invoked verb this core was extracted from — the recorded
//     decomposition carries the plans as data (hyp + witness tuple per
//     entry), not the search that found them;
//   - the By executor's grounding stage (the manual's S4;
//     proof/step_by.go), which
//     runs the same enumeration over a By leaf's installed premises and
//     persists the surviving plans in the CNF store's plan table.
//
// Motivation.
// The CNF refuter's unification/paramodulation primitives handle every
// individual inference the comprehension-equality bridges need,
// but the unguided saturation cannot COMPOSE the ≥4-rung chain: wide
// ∀-lemma clauses (membership kits, pairs.PairSurjective) act as junk
// amplifiers. The manual workaround — a grounding ladder —
// instantiates each lemma BY HAND at the goal's specific terms, after
// which the refute closes in seconds. This core mechanizes exactly that
// ladder:
//
//	for each ∀-hyp H of the goal:
//	  1. extract TRIGGER patterns from H's matrix (const-headed atoms
//	     mentioning the ∀-binders) — the SMT E-matching notion;
//	  2. match triggers against the goal's GROUND subterm pool using
//	     skeleton path indexing (head token + rigid-prefix filter,
//	     ext/skeleton) to prune, and unify.TermMatch (deterministic
//	     one-way HO matching: Miller patterns + abstract-all) to
//	     confirm and extract witnesses.
//
// Three trigger levels, tried in order per hypothesis:
//
//	L1 whole-atom triggers covering ALL binders → full ground σ.
//	L2 (when L1 yields nothing) proper const-headed subterm triggers →
//	   partial σ, remaining binders filled from the pool by exact type
//	   (bounded combinations).
//	L3 (when L2 yields nothing) first-binder type fallback: instantiate
//	   the leading binder at each pool term of its exact type — the
//	   case of pairs.PairSurjective, whose matrix (∃x y. p = (x,y)) has no
//	   ground-matchable trigger.
//
// Determinism: the pool, triggers, and instances are all enumerated in
// sorted order; TermMatch is search-free; caps are constants. Same goal
// → same plans. This is what lets a caller treat the enumeration as a
// pure function (the By conditioning stage's determinism contract) — and what
// lets the heuristics here evolve freely: no stored artifact ever
// re-runs the search, so a cap or trigger change affects future
// enumerations only.
package ematch

import (
	"slices"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/ext/unify"
	"github.com/euc-ai/xugo/utils"
)

const (
	// maxPerHyp caps the ground instances planned per ∀-hyp.
	maxPerHyp = 8
	// maxTotal caps the total instances planned per enumeration.
	maxTotal = 32
	// maxTypeFill caps the pool terms tried per type-filled slot
	// (L2 completion and the L3 fallback).
	maxTypeFill = 4
)

// Plan is one ground instantiation of a ∀-hypothesis: peel Hyp's
// leading binders at Witnesses, positionally. len(Witnesses) may be
// SHORTER than the binder count (a prefix-partial match, or the L3
// fallback) — the remaining binders stay universally quantified in the
// instance.
type Plan struct {
	// Hyp is the ∀-hypothesis term as it stood in the enumerated goal
	// (index-free identity: application sites locate it by α-key).
	Hyp       core.Term
	Witnesses []core.Term
	// filled marks a plan at least one of whose witnesses came from
	// type-fill completion (L2's slot fill, or the L3 first-binder
	// fallback) rather than a trigger MATCH. A filled tuple is a
	// bounded guess, not evidence the instance is wanted — replace
	// policies must not delete a wide source on its strength (see
	// FullyMatched).
	filled bool
	// viaConclusion marks a plan every witness of which came from
	// matching the hypothesis's CONCLUSION — its matrix past the leading
	// implications — and none from an antecedent atom. Such a plan is
	// the instance whose conclusion the leaf spells; nothing in the
	// match says the instance's antecedents hold. A plan some antecedent
	// atom of which matched is triggered by a fact the leaf holds. The
	// By conditioning stage reads this with the instance's antecedents
	// to tell a wanted instance from a guess (ViaConclusion).
	viaConclusion bool
}

// ViaConclusion reports whether p's witnesses came from the hypothesis's
// conclusion alone — no antecedent atom took part in the match.
func (p Plan) ViaConclusion() bool { return p.viaConclusion }

// FullyMatched reports whether every leading ∀-binder of p.Hyp is
// pinned by a trigger MATCH — a full-length witness tuple with no
// type-filled slot. This is the By conditioning stage's
// replace-eligibility test (S4: a premise every one of whose binders is
// pinned by some match is REPLACED by its instances); prefix-partial and
// type-filled plans keep the wide source alongside the instance.
func (p Plan) FullyMatched() bool {
	binders, _ := StripGuardedForalls(p.Hyp)
	return !p.filled && len(p.Witnesses) == len(binders)
}

// Valid re-checks p structurally: every witness's type must equal the
// corresponding leading ∀-binder's type of hyp (positionally). The
// matcher guarantees this by construction; application sites run it as
// the defensive per-plan guard so one malformed plan drops out alone
// instead of nil-ing a whole batch. hyp is the α-located hypothesis at
// the application site (α-equal to p.Hyp, so binder types agree).
func (p Plan) Valid(hyp core.Term) bool {
	cur := hyp
	for _, w := range p.Witnesses {
		cur = skipGuards(cur)
		abs := ext.MatchesFORALL(cur)
		if abs.IsZero() || !abs.Var().Type().Equals(w.Type()) {
			return false
		}
		cur = abs.Body()
	}
	return true
}

// cand is one ground pool entry with its skeleton encoding.
type cand struct {
	term  core.Term
	paths [][]string // ExtractPaths, split into token slices
	head  string     // first token of the first path (head discriminator)
}

// GroundPlans enumerates the deterministic, capped plan set for goal's
// ∀-hypotheses against goal's own ground subterm pool (non-∀ hyps +
// conclusion). "Ground" means: free variables of the goal only — a
// term mentioning a binder is not a candidate witness. Plans are
// deduplicated ((hyp, tuple) α-keyed) and returned in enumeration
// order (hyp order major, trigger selectivity minor).
func GroundPlans(goal core.Prop) []Plan {
	goalFrees := utils.EmptySet[core.TermName]()
	collectFrees := func(t core.Term) {
		for _, v := range t.Frees(nil) {
			goalFrees.Add(v.Name())
		}
	}
	for i := range goal.NumHyps() {
		collectFrees(goal.Hyp(i))
	}
	collectFrees(goal.Conclusion())
	isGroundTerm := func(t core.Term) bool {
		return t.AllFree(func(v core.VarTerm) bool { return goalFrees.Has(v.Name()) })
	}

	pool := buildPool(goal, isGroundTerm)
	if len(pool) == 0 {
		return nil
	}

	var plans []Plan
	planAt := map[string]int{}
	total := 0

	for i := range goal.NumHyps() {
		if total >= maxTotal {
			break
		}
		h := goal.Hyp(i)
		rawBinders, rawMatrix := StripGuardedForalls(h)
		if len(rawBinders) == 0 {
			continue
		}
		binders, matrix, slots := renameSlots(rawBinders, rawMatrix, goalFrees)

		addPlan := func(witnesses []core.Term, filled, viaConclusion bool) bool {
			if total >= maxTotal {
				return false
			}
			key := planKey(h, witnesses)
			if at, seen := planAt[key]; seen {
				// The same tuple reached through an antecedent atom is
				// not a conclusion-only match.
				if !viaConclusion {
					plans[at].viaConclusion = false
				}
				return true
			}
			planAt[key] = len(plans)
			plans = append(plans, Plan{Hyp: h, Witnesses: witnesses, filled: filled, viaConclusion: viaConclusion})
			total++
			return true
		}

		perHyp := 0
		emit := func(witnesses []core.Term, filled, viaConclusion bool) bool {
			if perHyp >= maxPerHyp {
				return false
			}
			if !addPlan(witnesses, filled, viaConclusion) {
				return false
			}
			perHyp++
			return true
		}

		// L1: whole-atom triggers covering all binders.
		matched := runTriggers(
			atomTriggers(matrix, slots, true),
			binders, slots, pool, isGroundTerm, nil, emit)

		// L2: proper subterm triggers with type-filled completion.
		if !matched {
			matched = runTriggers(
				subtermTriggers(matrix, slots),
				binders, slots, pool, isGroundTerm,
				typeFillCompleter(pool), emit)
		}

		// L3: first-binder type fallback.
		if !matched {
			first := binders[0]
			filled := 0
			for _, c := range pool {
				if filled >= maxTypeFill {
					break
				}
				if !c.term.Type().Equals(first.Type()) {
					continue
				}
				if !emit([]core.Term{c.term}, true, false) {
					break
				}
				filled++
			}
		}
	}
	return plans
}

// buildPool enumerates the goal's ground subterms (non-∀ hyps +
// conclusion) with their skeleton encodings, deduplicated by α-key and
// sorted for determinism.
func buildPool(goal core.Prop, isGround func(core.Term) bool) []cand {
	var roots []core.Term
	for i := range goal.NumHyps() {
		h := goal.Hyp(i)
		if !ext.MatchesFORALL(h).IsZero() {
			continue
		}
		roots = append(roots, h)
	}
	roots = append(roots, goal.Conclusion())

	seen := utils.EmptySet[core.TermKey]()
	var pool []cand
	for t := range ext.SubTerms(roots...) {
		if seen.Has(t.AlphaKey()) {
			continue
		}
		seen.Add(t.AlphaKey())
		if !isGround(t) {
			continue
		}
		paths := splitPaths(skeleton.ExtractPaths(skeleton.IndexedTerm{Term: t}))
		if len(paths) == 0 {
			continue
		}
		pool = append(pool, cand{term: t, paths: paths, head: paths[0][0]})
	}
	slices.SortStableFunc(pool, func(a, b cand) int { return a.term.Compare(b.term) })
	return pool
}

// StripGuardedForalls peels the ∀-binders reachable from h through
// leading implications and returns them in stated order, with the
// matrix keeping those antecedents in place (binder-free): a guarded
// lemma `∀op. A(op) ⇒ ∀f p s. B` yields [op f p s] and the matrix
// `A(op) ⇒ B`. A lemma states its content behind a guard exactly this
// way, so reading only the surface ∀-prefix would ground the guard
// variable alone and leave the content wide — the shape every
// `iterate/monoidal` law has. The trigger walkers read the matrix as
// a boolean formula, and an antecedent's atoms are triggers too. The
// matching instantiation step is SpecializeTactic's guarded rung.
//
// An implication whose consequent has no ∀ below it is left in the
// matrix untouched: it is the ordinary body of the last binder.
func StripGuardedForalls(h core.Term) ([]core.VarTerm, core.Term) {
	var binders []core.VarTerm
	var antes []core.Term
	body := h
	for {
		if abs := ext.MatchesFORALL(body); !abs.IsZero() {
			binders = append(binders, abs.Var())
			body = abs.Body()
			continue
		}
		if ante, rest, ok := ext.MatchesIMPLY(body); ok && forallBelowGuards(rest) {
			antes = append(antes, ante)
			body = rest
			continue
		}
		break
	}
	if len(antes) == 0 {
		return binders, body
	}
	matrix := body
	for i := len(antes) - 1; i >= 0; i-- {
		matrix = ext.Apply(ext.IMPLY, antes[i], matrix).Core()
	}
	return binders, matrix
}

// Telescope reads a hypothesis the way Lean reads a lemma statement:
// as a function of its ∀-binders AND its antecedents, uniformly. It
// returns the binders reachable through leading implications (stated
// order), every antecedent met on the way plus the leading antecedents
// of the innermost body, and the final conclusion — `∀op. monoidal_op(op)
// ⇒ ∀f p s. bij ⇒ eq` telescopes to ([op f p s], [monoidal_op(op), bij],
// eq). The binders are α-renamed away from `avoid` (a goal's free
// names) so a TermMatch keyed on the returned slot set cannot capture
// a goal variable that happens to share a binder's name; positions are
// preserved, so witnesses read off the bindings instantiate the
// ORIGINAL hypothesis in stated order.
//
// This is the shared read behind the By executor's apply-close (the
// conclusion is what the goal must match, the antecedents what the
// context must discharge) and the grounding stage's trigger walk.
func Telescope(h core.Term, avoid utils.Set[core.TermName]) (
	binders []core.VarTerm, antecedents []core.Term, conclusion core.Term, slots unify.TermNameSet) {
	rawBinders, rawMatrix := StripGuardedForalls(h)
	binders, matrix, slots := renameSlots(rawBinders, rawMatrix, avoid)
	for {
		ante, rest, ok := ext.MatchesIMPLY(matrix)
		if !ok {
			break
		}
		antecedents = append(antecedents, ante)
		matrix = rest
	}
	return binders, antecedents, matrix, slots
}

// forallBelowGuards reports whether a ∀-binder is reachable from t
// through leading implications alone.
func forallBelowGuards(t core.Term) bool {
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

// skipGuards steps over leading implications while a ∀-binder is
// reachable below them — the read Valid performs per witness, mirroring
// the guarded instantiation rung.
func skipGuards(t core.Term) core.Term {
	for ext.MatchesFORALL(t).IsZero() {
		_, rest, ok := ext.MatchesIMPLY(t)
		if !ok || !forallBelowGuards(rest) {
			return t
		}
		t = rest
	}
	return t
}

// StripLeadingForalls peels the leading ∀-binders off h.
func StripLeadingForalls(h core.Term) ([]core.VarTerm, core.Term) {
	var binders []core.VarTerm
	body := h
	for {
		abs := ext.MatchesFORALL(body)
		if abs.IsZero() {
			return binders, body
		}
		binders = append(binders, abs.Var())
		body = abs.Body()
	}
}

// renameSlots α-renames the hyp's ∀-binders to fresh names that cannot
// collide with the goal's free variables (TermMatch keys flexibility
// by NAME — a collision would make a rigid goal var spuriously
// flexible, and lemma binder names like s/t/a/p collide with session
// Skolems constantly). Returns the renamed binders (same order —
// instantiation is positional), the matrix with the renames applied,
// and the slot-name set.
func renameSlots(
	binders []core.VarTerm,
	matrix core.Term,
	goalFrees utils.Set[core.TermName],
) ([]core.VarTerm, core.Term, unify.TermNameSet) {
	taken := func(n core.TermName) bool {
		return goalFrees.Has(n) || matrix.HasFreeName(n)
	}
	slots := utils.EmptySet[core.TermName]()
	renamed := make([]core.VarTerm, len(binders))
	for i, v := range binders {
		name := utils.Subscript(core.TermName("ǝm"), i)
		for taken(name) || slots.Has(name) {
			name = utils.NextName(name)
		}
		fresh := core.Var(name, v.Type())
		matrix = matrix.Substitute(ext.MakeTermSubst(v, fresh))
		renamed[i] = fresh
		slots.Add(name)
	}
	return renamed, matrix, slots
}

// trigger is one trigger pattern with its skeleton encoding.
type trigger struct {
	pattern core.Term
	paths   [][]string
	head    string
	rigid   int // rigid-token count (selectivity score)
	// conclusion marks a trigger taken from the matrix's conclusion —
	// past its leading implications — rather than from an antecedent.
	conclusion bool
}

// atomTriggers walks the matrix through the boolean connectives AND
// through quantified subformulas, collecting const-headed atoms that
// mention ≥1 slot and no descended binder. When fullCover is set, only
// atoms mentioning EVERY slot qualify (L1). Triggers are sorted
// most-selective-first.
//
// Each trigger records whether it sits in the matrix's CONCLUSION —
// the matrix past its leading implications, the Horn reading Telescope
// gives — or in an antecedent; a plan matched through the conclusion
// alone is the instance whose conclusion the leaf spells, and the
// conditioning stage reads that mark (Plan.ViaConclusion).
//
// Descending under a quantifier is sound because a plan instantiates
// the hyp's OUTER ∀-binders only — where inside the matrix the trigger
// sat changes which instance is found, never whether the instance is
// a consequence. What it buys is the prenex shape every normalized
// lemma with an existential hypothesis takes: `∀op s f p. ∃y. (¬A(op)
// ∨ eq(op, s, f, p) ∨ …)`, where the equation that pins every binder
// lives under the ∃ and, read as an opaque atom, left the stage with
// nothing but the type-fill guess. An atom mentioning a descended
// binder is skipped: that variable is bound, not a witness candidate,
// and matching it against a goal term of the same name would be a
// capture.
func atomTriggers(matrix core.Term, slots unify.TermNameSet, fullCover bool) []trigger {
	type atom struct {
		term       core.Term
		conclusion bool
	}
	var atoms []atom
	bound := utils.EmptySet[core.TermName]()
	var walk func(t core.Term, conclusion bool)
	walk = func(t core.Term, conclusion bool) {
		if n := ext.MatchesNOT(t); n != nil {
			walk(n, conclusion)
			return
		}
		if l, r, ok := ext.BinaryBooleanOpMatchers(t); ok {
			walk(l, conclusion)
			walk(r, conclusion)
			return
		}
		if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
			bound.Add(abs.Var().Name())
			walk(abs.Body(), conclusion)
			return
		}
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			bound.Add(abs.Var().Name())
			walk(abs.Body(), conclusion)
			return
		}
		atoms = append(atoms, atom{term: t, conclusion: conclusion})
	}
	// The Horn reading: the leading implications' antecedents, then the
	// conclusion they guard.
	conclusion := matrix
	for {
		ante, rest, ok := ext.MatchesIMPLY(conclusion)
		if !ok {
			break
		}
		walk(ante, false)
		conclusion = rest
	}
	walk(conclusion, true)

	var out []trigger
	for _, a := range atoms {
		if !constHeaded(a.term) {
			continue
		}
		if mentionsAny(a.term, bound) {
			continue
		}
		mentioned := slotsMentioned(a.term, slots)
		if mentioned == 0 || (fullCover && mentioned < len(slots)) {
			continue
		}
		out = append(out, makeTrigger(a.term, a.conclusion))
	}
	sortTriggers(out)
	return out
}

// subtermTriggers collects proper const-headed applied subterms of the
// matrix's atoms that mention ≥1 slot, NOT descending into λ-bodies
// (patterns with non-slot bound vars cannot match ground pool terms).
func subtermTriggers(matrix core.Term, slots unify.TermNameSet) []trigger {
	roots := atomTriggers(matrix, slots, false)
	seen := utils.EmptySet[core.TermKey]()
	var out []trigger
	var walk func(t core.Term, isRoot, conclusion bool)
	walk = func(t core.Term, isRoot, conclusion bool) {
		if _, ok := t.AsAppliedTerm(); ok {
			if !isRoot && constHeaded(t) && slotsMentioned(t, slots) > 0 && !seen.Has(t.AlphaKey()) {
				seen.Add(t.AlphaKey())
				out = append(out, makeTrigger(t, conclusion))
			}
			_, args := ext.MatchesApply(t)
			for _, arg := range args {
				walk(arg, false, conclusion)
			}
		}
		// Deliberately no descent into AbsTerm bodies.
	}
	for _, tr := range roots {
		walk(tr.pattern, true, tr.conclusion)
	}
	sortTriggers(out)
	return out
}

func makeTrigger(t core.Term, conclusion bool) trigger {
	paths := splitPaths(skeleton.ExtractPaths(skeleton.IndexedTerm{Term: t}))
	head := ""
	if len(paths) > 0 {
		head = paths[0][0]
	}
	return trigger{pattern: t, paths: paths, head: head, rigid: rigidTokenCount(paths), conclusion: conclusion}
}

func sortTriggers(ts []trigger) {
	slices.SortStableFunc(ts, func(a, b trigger) int {
		if a.rigid != b.rigid {
			return b.rigid - a.rigid // most selective first
		}
		return a.pattern.Compare(b.pattern)
	})
}

// runTriggers matches each trigger against the pool and emits
// instantiation witness chains. complete, when non-nil, fills slots the
// trigger match left unbound (L2); with complete == nil a partial match
// is discarded (L1). Returns true when at least one chain was emitted.
func runTriggers(
	triggers []trigger,
	binders []core.VarTerm,
	slots unify.TermNameSet,
	pool []cand,
	isGround func(core.Term) bool,
	complete func(missing []core.VarTerm, emit func([]core.Term) bool, partial map[core.TermName]core.Term) bool,
	emit func(witnesses []core.Term, filled, viaConclusion bool) bool,
) bool {
	any := false
	for _, tr := range triggers {
		for _, c := range pool {
			if tr.head != c.head {
				continue
			}
			if !tr.pattern.Type().Equals(c.term.Type()) {
				continue
			}
			if !rigidPrefixCompatible(tr.paths, c.paths) {
				continue
			}
			bindings, ok := unify.TermMatch(tr.pattern, c.term, slots)
			if !ok {
				continue
			}
			// Every bound witness must be ground.
			groundOK := true
			for _, w := range bindings {
				if !isGround(w) {
					groundOK = false
					break
				}
			}
			if !groundOK {
				continue
			}

			var missing []core.VarTerm
			for _, v := range binders {
				if _, ok := bindings[v.Name()]; !ok {
					missing = append(missing, v)
				}
			}
			if len(missing) == 0 {
				witnesses := make([]core.Term, len(binders))
				for i, v := range binders {
					witnesses[i] = bindings[v.Name()]
				}
				if emit(witnesses, false, tr.conclusion) {
					any = true
				}
				continue
			}
			emitted := false
			if complete != nil {
				partial := map[core.TermName]core.Term{}
				for n, w := range bindings {
					partial[n] = w
				}
				completeEmit := func(fill []core.Term) bool {
					witnesses := make([]core.Term, len(binders))
					fi := 0
					for i, v := range binders {
						if w, ok := partial[v.Name()]; ok {
							witnesses[i] = w
						} else {
							witnesses[i] = fill[fi]
							fi++
						}
					}
					// Type-filled slots are bounded guesses, not
					// matches — the plan is marked so replace
					// policies keep the wide source.
					if emit(witnesses, true, tr.conclusion) {
						any = true
						emitted = true
						return true
					}
					return false
				}
				complete(missing, completeEmit, partial)
			}
			if !emitted {
				// Prefix-partial fallback: instantiation is positional,
				// so a σ that binds a PREFIX of the binder list is still
				// applicable — the remaining binders stay universally
				// quantified. This is exactly the "ground-specialized
				// pair-comprehension membership" shape: binder 0 is the predicate P,
				// bound by matching the set_comprehension comprehension argument,
				// while the pair coordinates a, b stay ∀.
				prefix := 0
				for _, v := range binders {
					if _, ok := bindings[v.Name()]; !ok {
						break
					}
					prefix++
				}
				if prefix > 0 {
					witnesses := make([]core.Term, prefix)
					for i := range prefix {
						witnesses[i] = bindings[binders[i].Name()]
					}
					if emit(witnesses, false, tr.conclusion) {
						any = true
					}
				}
			}
		}
	}
	return any
}

// typeFillCompleter fills unbound slots from the pool by exact type,
// enumerating bounded combinations in deterministic order.
func typeFillCompleter(pool []cand) func([]core.VarTerm, func([]core.Term) bool, map[core.TermName]core.Term) bool {
	return func(missing []core.VarTerm, emit func([]core.Term) bool, _ map[core.TermName]core.Term) bool {
		// Per-slot candidate lists (capped). λ-headed pool terms are
		// skipped: they duplicate the named set they η/def-wrap
		// (λx.set_member(x,s) ≡ s modulo set_member's definition) and only add junk
		// instances.
		options := make([][]core.Term, len(missing))
		for i, v := range missing {
			for _, c := range pool {
				if len(options[i]) >= maxTypeFill {
					break
				}
				if _, isAbs := c.term.AsAbsTerm(); isAbs {
					continue
				}
				if c.term.Type().Equals(v.Type()) {
					options[i] = append(options[i], c.term)
				}
			}
			if len(options[i]) == 0 {
				return false
			}
		}
		// Cartesian enumeration, first-slot-major.
		fill := make([]core.Term, len(missing))
		var rec func(i int) bool
		rec = func(i int) bool {
			if i == len(missing) {
				return emit(fill)
			}
			for _, opt := range options[i] {
				fill[i] = opt
				if !rec(i + 1) {
					return false
				}
			}
			return true
		}
		rec(0)
		return true
	}
}

// constHeaded reports whether t is an application (or constant) with a
// constant head.
func constHeaded(t core.Term) bool {
	head, _ := ext.MatchesApply(t)
	_, ok := head.AsConst()
	return ok
}

// mentionsAny reports whether any variable of names occurs free in t.
func mentionsAny(t core.Term, names utils.Set[core.TermName]) bool {
	if names.Size() == 0 {
		return false
	}
	hit := false
	t.AllFree(func(v core.VarTerm) bool {
		if names.Has(v.Name()) {
			hit = true
			return false
		}
		return true
	})
	return hit
}

// slotsMentioned counts distinct slots occurring free in t.
func slotsMentioned(t core.Term, slots unify.TermNameSet) int {
	found := utils.EmptySet[core.TermName]()
	t.AllFree(func(v core.VarTerm) bool {
		if slots.Has(v.Name()) {
			found.Add(v.Name())
		}
		return true
	})
	return len(found)
}

// splitPaths converts skeleton PathKeys into token slices.
func splitPaths(paths []skeleton.PathKey) [][]string {
	out := make([][]string, len(paths))
	for i, p := range paths {
		out[i] = strings.Split(string(p), "|")
	}
	return out
}

// rigidTokenCount counts non-wildcard tokens across the path set — the
// trigger selectivity score.
func rigidTokenCount(paths [][]string) int {
	n := 0
	for _, p := range paths {
		for _, tok := range p {
			if !isWildcardToken(tok) {
				n++
			}
		}
	}
	return n
}

func isWildcardToken(tok string) bool {
	return tok == "*F/0" || strings.Contains(tok, "*F")
}

// rigidPrefixCompatible is the skeleton discrimination filter: every
// trigger path's rigid prefix (tokens before its first wildcard) must
// be the prefix of SOME candidate path. A cheap over-approximation of
// matchability that prunes most non-matching (trigger, candidate)
// pairs before TermMatch runs.
func rigidPrefixCompatible(trig, c [][]string) bool {
	for _, tp := range trig {
		prefix := tp
		for i, tok := range tp {
			if isWildcardToken(tok) {
				prefix = tp[:i]
				break
			}
		}
		if len(prefix) == 0 {
			continue
		}
		found := false
		for _, cp := range c {
			if len(cp) >= len(prefix) && slices.Equal(cp[:len(prefix)], prefix) {
				found = true
				break
			}
		}
		if !found {
			return false
		}
	}
	return true
}

// planKey is the dedup key of one instantiation plan.
func planKey(hyp core.Term, witnesses []core.Term) string {
	var sb strings.Builder
	sb.WriteString(string(hyp.AlphaKey()))
	for _, w := range witnesses {
		sb.WriteString("|")
		sb.WriteString(string(w.AlphaKey()))
	}
	return sb.String()
}
