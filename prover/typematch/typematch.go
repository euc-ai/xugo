// Package typematch is type-only structural matching for lemma type
// adaptation — a leaf package over core/ext/skeleton with no prover
// dependency, so the matcher is testable and reusable without the goal
// stack.
//
// When a polymorphic lemma is applied to a concretely-typed goal, the lemma's
// type variables must be instantiated so that downstream tactics (which filter
// candidates by `HolType.Equals`) can see the lemma's bound vars as
// matching the witness's concrete types. The package provides two primitives
// for the cheap path of that adaptation:
//
//   - TypeOnlyMatch:  first-order structural match between a pattern term
//     (typically a stripped lemma side: lhs of an iff, body of a forall) and
//     a target term (typically a goal subterm). Recovers a TypeSubst, ignores
//     term substitution. Cheaper than higher-order unify.Unify by orders of
//     magnitude — no β-η normalization, no imitation/projection search.
//
//   - GoalSubtermIndex: head-keyed index over all subterms of a goal. Lets the
//     caller filter candidate target subterms by const-head before invoking
//     TypeOnlyMatch, eliminating the vast majority of irrelevant candidates
//     for free.
//
// These primitives are intended to be wired together by a future
// `tryAdaptLemmaTypes` rewrite that strips the lemma's outer ∀-binders, treats
// them as pattern slots, and matches the body (or each side of an iff) against
// candidate subterms drawn from the index.
//
// `tryAdaptLemmaTypes` is invoked from `ApplyLemma` when a polymorphic lemma
// is being introduced into a concretely-typed goal. It strips the lemma's
// outer ∀-binders, treats them as pattern slots, and matches the body (or
// each side of an iff/equality) against goal subterms using `TypeOnlyMatch`,
// recovering a TypeSubst that the caller applies to the lemma via
// `core.PropTypeInst`. The point is to ensure that downstream structural
// tactics (instantiate, subst, …) that filter candidates by `HolType.Equals`
// see lemma hypotheses with concrete types matching the goal's witnesses,
// rather than being silently rejected because of leftover lemma type
// variables.
//
// Architecture decision:
// type unification happens *only* at the lemma-application boundary. Every
// other tactic keeps its existing strict type-equality check. The cost of
// the unification is paid once per `ApplyLemma`; downstream cascades are
// unaffected.
package typematch

import (
	"fmt"
	"os"
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/skeleton"
	"github.com/euc-ai/xugo/prover/solver/ematch"
)

// ---------------------------------------------------------------------------
// 1. Type-only structural matcher
// ---------------------------------------------------------------------------

// TypeOnlyMatch performs first-order structural matching between `pattern` and
// `target`, recovering only the type substitution that aligns them. The
// resulting term-level substitution (where `patternVars` would be bound to
// concrete subterms of the target) is discarded — the caller is expected to
// use the returned TypeSubst for `core.PropTypeInst`, never for term rewrite.
//
// `patternVars` selects which free term variables of the pattern act as
// "pattern slots" — they may match any target subterm of compatible type, but
// must do so consistently (multiple occurrences of the same pattern slot must
// yield α-equal targets). For lemma-type-adaptation, this is the set of
// variables freshly stripped from the lemma's outer ∀-binders.
//
// `instantiableTypes` selects which type variables on the pattern side are
// open for substitution. Type variables not in this set are treated as rigid
// — they must literally equal the corresponding target type variable. For
// lemma-type-adaptation, this is the lemma's own type variables; the goal's
// type variables (if any) are rigid.
//
// Complexity: O(min(pattern.Size(), target.Size())). No β-η normalization,
// no search. Rejects β-η-equivalent terms that differ syntactically — a
// deliberate tradeoff acceptable in the lemma-application pipeline because
// both sides are typically already normalized.
//
// Returns the substitution and true on success; nil/false on any structural,
// type, or consistency mismatch.
func TypeOnlyMatch(
	pattern, target core.Term,
	patternVars core.VarPredicate,
	instantiableTypes core.VarTypePredicate,
) ([]core.TypeSubst, bool) {
	// core.MatchTypeInto invokes the predicate directly and would
	// panic on nil. TypeOnlyMatch tolerates nil (nil = "no var
	// instantiable", i.e. all type vars are rigid): a literal-false
	// predicate is substituted at the boundary.
	if instantiableTypes == nil {
		instantiableTypes = func(core.VarType) bool { return false }
	}
	s := &typeOnlyMatchState{
		patternVars:       patternVars,
		instantiableTypes: instantiableTypes,
	}
	if !s.match(pattern, target) {
		return nil, false
	}
	return s.typeSubsts, true
}

type typeOnlyMatchState struct {
	patternVars       core.VarPredicate
	instantiableTypes core.VarTypePredicate
	typeSubsts        []core.TypeSubst
	boundEnv          []core.VarPair
	bindings          []termBinding
}

type termBinding struct {
	patternVar core.VarTerm
	target     core.Term
}

func (s *typeOnlyMatchState) match(pattern, target core.Term) bool {
	if pv, ok := pattern.AsVar(); ok {
		return s.matchVarPos(pv, target)
	}
	switch p := pattern.Core().(type) {
	case core.ConstTerm:
		tc, ok := target.AsConst()
		if !ok || !p.Meta().Equals(tc.Meta()) {
			return false
		}
		return s.unifyTypes(p.Type(), tc.Type())
	case core.AppliedTerm:
		ta, ok := target.AsAppliedTerm()
		if !ok {
			return false
		}
		return s.match(p.Fun(), ta.Fun()) && s.match(p.Arg(), ta.Arg())
	case core.AbsTerm:
		ta, ok := target.AsAbsTerm()
		if !ok {
			return false
		}
		if !s.unifyTypes(p.Var().Type(), ta.Var().Type()) {
			return false
		}
		s.boundEnv = append(s.boundEnv, core.VarPair{V0: p.Var(), V1: ta.Var()})
		ok2 := s.match(p.Body(), ta.Body())
		s.boundEnv = s.boundEnv[:len(s.boundEnv)-1]
		return ok2
	}
	return false
}

// matchVarPos handles the pattern side being a VarTerm. Three cases:
//   - bound by current α-env: target must be the env partner (literal alpha-bound match)
//   - free, in patternVars: pattern slot — type-unify, record binding, check consistency
//   - free, not a pattern var: rigid — target must be a same-name VarTerm
func (s *typeOnlyMatchState) matchVarPos(pv core.VarTerm, target core.Term) bool {
	for i := len(s.boundEnv) - 1; i >= 0; i-- {
		pair := s.boundEnv[i]
		if pair.V0.Equals(pv) {
			tv, ok := target.AsVar()
			if !ok || !pair.V1.Equals(tv) {
				return false
			}
			return s.unifyTypes(pv.Type(), tv.Type())
		}
	}
	if s.patternVars != nil && s.patternVars(pv) {
		if !s.unifyTypes(pv.Type(), target.Type()) {
			return false
		}
		for _, b := range s.bindings {
			if b.patternVar.Equals(pv) {
				return b.target.AlphaEquals(target)
			}
		}
		s.bindings = append(s.bindings, termBinding{pv, target})
		return true
	}
	tv, ok := target.AsVar()
	if !ok || pv.Name() != tv.Name() {
		return false
	}
	return s.unifyTypes(pv.Type(), tv.Type())
}

// unifyTypes extends the accumulated typeSubsts so that the pattern
// type matches the target type under them, and reports false when the
// pair is inconsistent with a binding already made. The walk is
// core.MatchTypeInto's over the shared environment: a bound pattern
// letter must meet its binding literally, an unbound one is bound to
// the target's type, a rigid one must meet itself.
//
// The pattern is never substituted ahead of the walk: a binding's
// image is the target's type, and its letters are the target's even
// where they spell a pattern letter's name — an instance swapping two
// letters binds B ↦ D and D ↦ B, and the adaptation sweep's anchor
// carries the goal's A inside an earlier binding's image num → A.
// Read through the environment, a pattern letter stays the pattern's
// whatever the target calls its image, as core's own term matcher
// (prop.IsTypeMatchOf) reads it.
func (s *typeOnlyMatchState) unifyTypes(patType, tgtType core.HolType) bool {
	return core.MatchTypeInto(patType, tgtType, s.instantiableTypes, &s.typeSubsts)
}

// ---------------------------------------------------------------------------
// 2. Goal subterm index
// ---------------------------------------------------------------------------

// GoalSubtermIndex is a head-keyed index over the matching anchors of a
// goal — every const-headed subterm reachable through the propositional
// skeleton + term-level descent (see `skeleton.MatchingPoints`). Used as
// a coarse pre-filter for type-adaptation matching: a pattern with a
// const head only needs to be tried against subterms sharing that head.
//
// Both this index and the lemma-side pattern enumeration consume the
// same `skeleton.MatchingPoints` enumerator, so the matching anchors
// recovered on either side are drawn from a consistent universe.
//
// Construction is O(goal.Size()); lookup is O(1).
type GoalSubtermIndex struct {
	byHead map[core.TermName][]skeleton.IndexedTerm
}

// BuildGoalSubtermIndex enumerates the goal's matching points via
// `skeleton.MatchingPointsUnderLambda` and buckets them by their head
// const's name. A subterm whose head is not a const is dropped (the
// enumerator already filters these out, but the safety check is cheap).
//
// Under-λ subterms are included for type adaptation: type vars are
// concrete regardless of binder depth, so an under-λ const-headed
// occurrence is just as good a witness as a top-level one (e.g.,
// a wellfounded-recursion law has `tailadmissible(...)` buried inside
// `pattern_abstraction(λf. ...)` and the standard MatchingPoints walk would miss
// it). The under-λ subterms carry empty BoundVars — see
// MatchingPointsUnderLambda's godoc for the slot-tracking limitation
// that follows.
func BuildGoalSubtermIndex(goal core.Prop) *GoalSubtermIndex {
	idx := &GoalSubtermIndex{byHead: map[core.TermName][]skeleton.IndexedTerm{}}
	for _, it := range skeleton.MatchingPointsUnderLambda(goal) {
		idx.byHead[headKey(it.Term)] = append(idx.byHead[headKey(it.Term)], it)
	}
	return idx
}

// Candidates returns the goal subterms whose head shares a const name
// with `pattern`'s head. The returned slice is the index's internal
// storage — callers must not mutate it. Not size-filtered.
func (idx *GoalSubtermIndex) Candidates(pattern core.Term) []skeleton.IndexedTerm {
	return idx.byHead[headKey(pattern)]
}

// headKey returns the index key for `t`: the name of `t`'s leftmost
// applied const, or "" if the head is not a const.
func headKey(t core.Term) core.TermName {
	head, _ := ext.MatchesApply(t)
	if c, ok := head.AsConst(); ok {
		return c.Name()
	}
	return ""
}

// typeAdaptDebug is set from the TYPEADAPT_DEBUG env var at process start.
// When true, tryAdaptLemmaTypes emits one stderr line per non-trivial
// adaptation, showing the lemma's AlphaKey and the substitution it applied.
// Useful for diagnosing "the bridge didn't get adapted" reports — log
// presence distinguishes "fix didn't fire" from "fix fired with wrong sub".
var typeAdaptDebug = os.Getenv("TYPEADAPT_DEBUG") == "1"

// TryAdaptLemmaTypes searches for a type substitution that aligns the
// polymorphic `lemma` with concrete types in `goal`. Returns the
// type-instantiated lemma on success, nil if no useful substitution was
// recovered (caller falls back to applying the lemma as-is).
//
// Strategy:
//  1. Collect the lemma's type variable names — these are the substitution
//     candidates. Type variables in the goal stay rigid.
//  2. Enumerate the lemma's matching anchors via
//     `skeleton.MatchingPoints` — every const-headed subterm reachable
//     through propositional skeleton + term-level descent. Each anchor
//     comes with a `BoundVars` set of outer ∀/∃ binders that were stripped
//     above it; those vars become pattern slots for `TypeOnlyMatch`.
//  3. Build a head-keyed index of the goal's matching anchors via the
//     same enumerator (so both sides are drawn from a consistent universe).
//  4. For each lemma anchor × goal candidate with compatible head and
//     size, run `TypeOnlyMatch` on the anchor pre-substituted with the
//     subs accumulated from prior matches. Merge each new match into
//     the accumulator; reject candidates whose substitution conflicts
//     with already-bound type variables. After the sweep, apply the
//     accumulated union to the whole lemma.
//
// Multi-match accumulation matters for lemmas whose type variables are
// scattered across multiple non-overlapping subterms — e.g., a
// casewise-recursion law, where A, ?130398, ?130409, ?130403 each appear in
// different positions. A single anchor's match is often partial; the
// union covers everything. Earlier first-match-wins behavior left
// binder types polymorphic in such cases, breaking downstream
// `instantiate` even when the lemma was conceptually applicable.
//
// Within one anchor's candidate list we still pick the first compatible
// match — search depth doesn't escalate per anchor.
//
// The sweep's commit (sweepCommit) is then held against the constants
// the goal holds: where it reads one of the law's at a type the goal
// does not hold it at, it gives way to an instance the goal offers that
// reads every one where the goal holds it (readsEvery).
func TryAdaptLemmaTypes(lemma core.Prop, goal core.Prop) core.Prop {
	return readsEvery(lemma, goal, sweepCommit(lemma, goal))
}

// sweepCommit is the anchor sweep's one commit, retried with the lemma's
// letters renamed apart where it left a captured letter. Nil where the
// sweep makes no instance.
func sweepCommit(lemma core.Prop, goal core.Prop) core.Prop {
	// No renamed-apart retry where the sweep binds every letter it
	// leaves sharing a name with the goal's, an identity binding
	// included (renameLemmaTypeVarsApart): this is the single
	// adaptation that REPLACES the bare lemma at the install, and the
	// by-name occurs-check filters not only recursive bindings but
	// coincidental wrong candidates that happen to be recursive by
	// name. At functions.InjectiveOnLeftInverse and
	// functions.FactorsLeftGen the goal is the law's own statement at
	// its own letters: the sweep binds each letter to itself and
	// commits no instance, and a retry there reaches a coincidental
	// wrong one (`f` at (B → A) → A) that does not close where the
	// bare install does.
	//
	// The one exception is a CAPTURED letter: the sweep dropped a
	// binding as recursive and left a lemma letter with no binding at
	// all, identity included, whose name the goal also spells. What it
	// commits then reads that letter as the goal's — beside the rest of
	// an instance, `∘` read at (num → A) becomes composition at A,
	// num → A, num → A; with nothing committed, the bare lemma keeps
	// its own letters, and `∀s t u:set(A). s ∪ t ⊆ u ⇔ …` cited at sets
	// of prod(B, C) → A stays a law about sets of the goal's A. Neither
	// is an instance the goal holds, and no premise of the By closes
	// with it.
	// There the retry runs, and its instance is taken when it binds
	// every letter it renamed.
	adapted, substs, occursDropped := tryAdaptLemmaTypesWithSubsts(lemma, goal, false)
	if !occursDropped || !capturesGoalLetter(lemma, goal, substs) {
		return adapted
	}
	renamed, _ := renameLemmaTypeVarsApart(lemma, goal)
	if renamed == nil {
		return adapted
	}
	retry, _, _ := tryAdaptLemmaTypesWithSubsts(renamed, goal, false)
	if retry == nil || mentionsApartLetter(retry) {
		return adapted
	}
	return retry
}

// capturesGoalLetter reports whether the committed σ leaves a lemma
// letter unbound — no binding at all, identity included — whose name
// the goal spells too: the instance then reads it as the goal's letter.
func capturesGoalLetter(lemma, goal core.Prop, substs []core.TypeSubst) bool {
	bound := map[core.TypeName]bool{}
	for _, s := range substs {
		bound[s.VarType.Name()] = true
	}
	goalNames := map[core.TypeName]bool{}
	collect := func(v core.VarType) bool {
		goalNames[v.Name()] = true
		return false
	}
	ext.TermAnyTypeVar(goal.Conclusion(), collect)
	for h := range goal.HypIter() {
		ext.TermAnyTypeVar(h, collect)
	}
	for v := range collectLemmaTypeVarPointers(lemma) {
		if !bound[v.Name()] && goalNames[v.Name()] {
			return true
		}
	}
	return false
}

// mentionsApartLetter reports whether a renamed-apart adaptation left a
// renamed letter free — a letter the retry did not bind.
func mentionsApartLetter(p core.Prop) bool {
	apart := func(v core.VarType) bool { return strings.HasPrefix(string(v.Name()), "?apart") }
	if ext.TermAnyTypeVar(p.Conclusion(), apart) {
		return true
	}
	for h := range p.HypIter() {
		if ext.TermAnyTypeVar(h, apart) {
			return true
		}
	}
	return false
}

// EnumerateLemmaTypeAdaptations returns EVERY distinct consistent
// full-lemma type instantiation of `lemma` against `goal`, deduplicated
// by the instantiated lemma's AlphaKey. Multi-instance sibling of
// TryAdaptLemmaTypes for the goal class of zip and the two-list map, where the same
// polymorphic const occurs at several type instances in one goal
// (`list_length⟨?A⟩(l1)` and `list_length⟨?B⟩(l2)`): TryAdaptLemmaTypes commits
// only the FIRST consistent union, so a `simp_with` rule adapted through
// it fires at one instance and the agent must re-load the lemma with an
// explicit `type_specialize` per remaining instance.
//
// Mechanism: PIN-based enumeration, not in-sweep branching. The sweep's
// commit order is deliberately asymmetric (context-rich anchors first, and
// partial-application anchors like `∧(list_length(nil) = 0)` can only ever
// match ONE side of a goal conjunction), so once the first anchor commits
// an instance every later anchor sees the type var bound and passes — an
// in-sweep branch never even SEES the alternate instances. Instead:
//
//  1. collectAnchorPins enumerates every distinct single-anchor σ the
//     goal offers — same anchor walk, same informative-anchor /
//     weak-anchor / occurs-check gating as the sweep (so coincidental
//     weak-anchor σ noise is filtered identically), but scanning ALL
//     candidates of every anchor instead of committing the first, and
//     NOT skipping the ambiguous bare-const case (there the ambiguity IS
//     the multi-instance signal; the single-adaptation path skips it as
//     an order-dependence guard — see bareConstAnchorAmbiguous).
//  2. Each pin seeds one full deterministic sweep (the pin is merged
//     into the accumulator before the anchor walk), completing the
//     remaining type vars exactly as the single-adaptation path would.
//  3. Results dedup by the instantiated lemma's AlphaKey, with the
//     UNPINNED sweep's result first.
//
// Contract:
//   - result[0] is the unpinned sweep's instance wherever that sweep
//     makes one (it runs first);
//   - alternates follow in anchor/candidate discovery order;
//   - identity adaptations (adapted α= lemma) are dropped;
//   - nil means no adaptation exists at all.
//
// The walk completes every distinct anchor pin of the finite goal — it
// is bounded by the goal's anchors, so an instance never hides a later
// one by coming first — as finite structural enumeration, not an
// exhaustive higher-order search. The Simp adaptation and the `by`
// rung's head candidates read this one enumeration.
func EnumerateLemmaTypeAdaptations(lemma core.Prop, goal core.Prop) []core.Prop {
	out, captured, occursDropped := enumerateLemmaTypeAdaptationsWithCaptures(lemma, goal, false)
	if !occursDropped {
		return out
	}
	renamed, back := renameLemmaTypeVarsApart(lemma, goal)
	if renamed == nil {
		return out
	}
	extra, _ := enumerateLemmaTypeAdaptationsImpl(renamed, goal, false)
	extra = renameBackDroppingIdentity(lemma, goal, extra, back)
	if len(extra) > 0 {
		// An instance that read a captured letter as the goal's
		// (TryAdaptLemmaTypes) is the collision's, not the goal's: where
		// the renamed-apart sweep reaches instances, it gives way to them.
		kept := out[:0:0]
		for i, p := range out {
			if !captured[i] {
				kept = append(kept, p)
			}
		}
		out = kept
	}
	return appendDistinctTypeAdaptations(out, extra)
}

// appendDistinctTypeAdaptations retains the original sweep's ordering
// while adding instances reached with the lemma's letters renamed apart.
// A compound instance can be dropped by the occurs-check even when
// another instance was found, so successful sweeps need the retry too.
func appendDistinctTypeAdaptations(out, extra []core.Prop) []core.Prop {
	seen := make(map[core.PropKey]bool, len(out))
	for _, p := range out {
		seen[p.AlphaKey()] = true
	}
	for _, p := range extra {
		if !seen[p.AlphaKey()] {
			seen[p.AlphaKey()] = true
			out = append(out, p)
		}
	}
	return out
}

// renameBackDroppingIdentity names the apart letters a renamed-apart
// sweep's results still hold and drops the identity adaptation in
// disguise: an instance that is the lemma once its apart letters are
// read as the lemma's own (the renamed letter bound to the goal's
// same-named letter). A kept instance's free apart letters are named by
// ResidualLetterNames, so none is read as the goal's.
func renameBackDroppingIdentity(lemma, goal core.Prop, adapted []core.Prop, back []core.TypeSubst) []core.Prop {
	var out []core.Prop
	for _, a := range adapted {
		if core.PropTypeInst(a, back...).AlphaEquals(lemma) {
			continue
		}
		out = append(out, core.PropTypeInst(a, ResidualLetterNames(a, goal, back)...))
	}
	return out
}

// ResidualLetterNames names the fresh letters `instance` still holds —
// the lemma's letters no binding reached, renamed apart from the goal's
// by `back`, which maps each fresh letter to the lemma's own. Each takes
// back its lemma name unless the goal spells that name: renamed back, it
// would read as the goal's letter and identify two type variables the
// lemma keeps independent (a law's value letter B at a goal with an
// unrelated y : B; term_specialize's Q : complex_ops(A, D) at a goal's
// N : module_ops(A, D), binding Q's carrier to N's). Such a letter takes
// the first uppercase letter that neither the goal nor the instance
// spells, after the letters that keep their names have taken theirs;
// past Z, a `var:` name. Returns the substitution to apply to `instance`.
func ResidualLetterNames(instance, goal core.Prop, back []core.TypeSubst) []core.TypeSubst {
	if len(back) == 0 {
		return nil
	}
	free := map[core.TypeName]bool{}
	for v := range collectLemmaTypeVarPointers(instance) {
		free[v.Name()] = true
	}
	taken := map[core.TypeName]bool{}
	for v := range collectLemmaTypeVarPointers(goal) {
		taken[v.Name()] = true
	}
	for name := range free {
		taken[name] = true
	}
	out := make([]core.TypeSubst, 0, len(back))
	var apart []core.TypeSubst
	for _, sub := range back {
		fresh := sub.VarType
		if !free[fresh.Name()] {
			continue
		}
		name := sub.HolType.(core.VarType).Name()
		if taken[name] {
			apart = append(apart, sub)
			continue
		}
		taken[name] = true
		out = append(out, core.MakeTypeSubst(fresh, core.MakeVarType(name)))
	}
	for _, sub := range apart {
		name := core.TypeName("var:" + string(sub.HolType.(core.VarType).Name()) + "_apart")
		for c := 'A'; c <= 'Z'; c++ {
			if !taken[core.TypeName(string(c))] {
				name = core.TypeName(string(c))
				break
			}
		}
		taken[name] = true
		out = append(out, core.MakeTypeSubst(sub.VarType, core.MakeVarType(name)))
	}
	return out
}

// EnumerateLemmaTypeAdaptationsPinned is the enumeration run from a
// caller's pin: `pinned` names stated ∀-binders of the lemma and the
// type each must have — the type of the term a `Where` / term_specialize
// pinned to it. Matching each named binder's stated type against its
// pinned type fixes every type letter that type mentions; the anchor
// sweep then completes the rest, consistently with that pin, and the
// one instance it reaches is returned. Empty when a pinned type cannot
// match its binder's, or when the pin is inconsistent with what the
// goal's anchors force.
//
// This is what a law with two carrier letters needs: read from the
// goal's anchors alone, `monoidal.Homomorphic`'s B and C are a coin
// toss (the goal holds folds at both carriers), but the map pinned to
// `h : B → C` carries both letters in its own type.
func EnumerateLemmaTypeAdaptationsPinned(lemma core.Prop, goal core.Prop, pinned map[string]core.HolType) []core.Prop {
	out, occursDropped := enumerateLemmaTypeAdaptationsPinnedImpl(lemma, goal, pinned)
	if !occursDropped {
		return out
	}
	renamed, back := renameLemmaTypeVarsApart(lemma, goal)
	if renamed == nil {
		return out
	}
	extra, _ := enumerateLemmaTypeAdaptationsPinnedImpl(renamed, goal, pinned)
	return appendDistinctTypeAdaptations(out, renameBackDroppingIdentity(lemma, goal, extra, back))
}

func enumerateLemmaTypeAdaptationsPinnedImpl(lemma core.Prop, goal core.Prop, pinned map[string]core.HolType) ([]core.Prop, bool) {
	if len(pinned) == 0 {
		return nil, false
	}
	lemma = unshareLemmaTypeVars(lemma, goal)
	c := newTypeAdaptContext(lemma, goal)
	if c == nil {
		return nil, false
	}
	// The binders are the telescope's — through the guards, since a
	// structure law binds its operation, states the structure, and only
	// then binds what the pin names (`∀op. monoidal_op(op) ⇒ ∀op2 h …`).
	binders, _ := ematch.StripGuardedForalls(lemma.Conclusion())
	var pin []core.TypeSubst
	seen := 0
	for _, b := range binders {
		if want, ok := pinned[string(b.Name())]; ok {
			seen++
			if !core.MatchTypeInto(b.Type(), want, c.isInstantiable, &pin) {
				return nil, c.occursDropped
			}
		}
	}
	if seen == 0 {
		return nil, c.occursDropped
	}
	accumulated, ok := c.sweep(dropIdentityTypeSubsts(pin), false)
	if !ok || len(accumulated) == 0 {
		return nil, c.occursDropped
	}
	adapted := core.PropTypeInst(lemma, accumulated...)
	if adapted.AlphaEquals(lemma) {
		return nil, c.occursDropped
	}
	return []core.Prop{adapted}, c.occursDropped
}

func enumerateLemmaTypeAdaptationsImpl(lemma core.Prop, goal core.Prop, skipIdentityOnlyCandidates bool) ([]core.Prop, bool) {
	out, _, dropped := enumerateLemmaTypeAdaptationsWithCaptures(lemma, goal, skipIdentityOnlyCandidates)
	return out, dropped
}

// enumerateLemmaTypeAdaptationsWithCaptures is the enumeration marking,
// per instance, whether its σ leaves a captured letter
// (capturesGoalLetter).
func enumerateLemmaTypeAdaptationsWithCaptures(lemma core.Prop, goal core.Prop, skipIdentityOnlyCandidates bool) ([]core.Prop, []bool, bool) {
	stated := lemma
	lemma = unshareLemmaTypeVars(lemma, goal)
	c := newTypeAdaptContext(lemma, goal)
	if c == nil {
		return nil, nil, false
	}
	// Pin nil = the unpinned primary sweep: its instance, where it makes
	// one, is result[0].
	pins := append([][]core.TypeSubst{nil}, c.collectAnchorPins(skipIdentityOnlyCandidates)...)
	var out []core.Prop
	var captured []bool
	seen := map[core.PropKey]struct{}{}
	identityOnly := false
	for _, pin := range pins {
		accumulated, ok := c.sweep(pin, skipIdentityOnlyCandidates)
		if !ok || len(accumulated) == 0 {
			continue
		}
		adapted := core.PropTypeInst(lemma, accumulated...)
		if adapted.AlphaEquals(lemma) {
			identityOnly = true
			continue
		}
		key := adapted.AlphaKey()
		if _, dup := seen[key]; dup {
			continue
		}
		seen[key] = struct{}{}
		if typeAdaptDebug {
			logTypeAdapt(lemma, accumulated)
		}
		out = append(out, adapted)
		captured = append(captured, capturesGoalLetter(stated, goal, accumulated))
	}
	// Self-image retry, mirroring tryAdaptLemmaTypesImpl: when the goal
	// carries the lemma's own conclusion as a hyp, identity-only anchors
	// from that self-image can mask a useful concrete occurrence.
	if len(out) == 0 && identityOnly && !skipIdentityOnlyCandidates && goalHasLemmaSelfImageHyp(goal, lemma) {
		out, captured, dropped := enumerateLemmaTypeAdaptationsWithCaptures(stated, goal, true)
		return out, captured, dropped || c.occursDropped
	}
	return out, captured, c.occursDropped
}

func tryAdaptLemmaTypesImpl(lemma core.Prop, goal core.Prop, skipIdentityOnlyCandidates bool) (core.Prop, bool) {
	adapted, _, dropped := tryAdaptLemmaTypesWithSubsts(lemma, goal, skipIdentityOnlyCandidates)
	return adapted, dropped
}

// tryAdaptLemmaTypesWithSubsts is tryAdaptLemmaTypesImpl returning the
// committed σ beside the instance it makes. A σ of identity bindings
// alone makes no instance and is returned without one: the letters it
// binds are bound (capturesGoalLetter).
func tryAdaptLemmaTypesWithSubsts(lemma core.Prop, goal core.Prop, skipIdentityOnlyCandidates bool) (core.Prop, []core.TypeSubst, bool) {
	lemma = unshareLemmaTypeVars(lemma, goal)
	c := newTypeAdaptContext(lemma, goal)
	if c == nil {
		return nil, nil, false
	}
	accumulated, ok := c.sweep(nil, skipIdentityOnlyCandidates)
	if !ok || len(accumulated) == 0 {
		return nil, nil, c.occursDropped
	}
	adapted := core.PropTypeInst(lemma, accumulated...)
	if adapted.AlphaEquals(lemma) {
		// If the goal already contains this lemma's own conclusion as a hyp,
		// identity-only anchors from that self-image can mask a useful concrete
		// occurrence elsewhere in the goal. Retry once while ignoring vacuous
		// identity-only candidates, but keep the normal first pass unchanged for
		// legitimate reproduction subgoals.
		if !skipIdentityOnlyCandidates && goalHasLemmaSelfImageHyp(goal, lemma) {
			retried, substs, dropped := tryAdaptLemmaTypesWithSubsts(lemma, goal, true)
			if retried != nil {
				return retried, substs, dropped || c.occursDropped
			}
			return nil, accumulated, dropped || c.occursDropped
		}
		return nil, accumulated, c.occursDropped
	}
	if typeAdaptDebug {
		logTypeAdapt(lemma, accumulated)
	}
	return adapted, accumulated, c.occursDropped
}

// typeAdaptContext is the shared setup of the adaptation sweep: the
// lemma's type-var pointer set, the goal subterm index, the sorted anchor
// list, the informative-var ownership set and the existential-binder
// seed. Built once, consumed by (potentially several) sweep runs.
type typeAdaptContext struct {
	lemma, goal         core.Prop
	lemmaTypeVars       map[core.VarType]struct{}
	isInstantiable      core.VarTypePredicate
	idx                 *GoalSubtermIndex
	anchors             []skeleton.IndexedTerm
	informativeTypeVars map[core.VarType]struct{}
	seed                []core.TypeSubst
	// occursDropped records that a candidate binding was dropped by the
	// by-name occurs-check during this context's sweeps — the one
	// condition under which the entry points retry with the lemma's
	// letters renamed apart (renameLemmaTypeVarsApart).
	occursDropped bool
}

// newTypeAdaptContext builds the sweep setup, or nil when adaptation is
// structurally pointless (ground lemma / goal α-equal to the lemma).
func newTypeAdaptContext(lemma core.Prop, goal core.Prop) *typeAdaptContext {
	if !ext.PropHasTypeVars(lemma) {
		return nil
	}
	// Goal α-equals lemma: no adaptation can usefully change the lemma
	// without making it stop matching the goal. Without this early-out,
	// the anchor walk picks up structurally-coincidental matches across
	// the lemma's own internal type-var instances (e.g. a `=`-at-A
	// anchor matched against the same prop's `⇔` which is `=`-at-bool)
	// and commits wrong substitutions like `A := bool` that corrupt the
	// lemma. The downstream `_LemmaTactic` then bypasses its α-circular
	// guard (because adapted ≠ original) and silently routes through a
	// fallback strategy. Returning nil here keeps the lemma unchanged,
	// the α-circular guard fires as designed, and `runAutoMatch` /
	// `tryCloseAsTypeVariantOfEntry` close the leaf via the
	// trusted-Thm injection path. See engine's
	// TestApplyLemma_TypeVariantOfEntryCloses.
	if lemma.AlphaEquals(goal) {
		return nil
	}

	// Collect the lemma's actual `VarType` pointers (not names). Two
	// VarTypes with the same name but different pointer identity are
	// distinct under the logic's semantics: a lemma's polymorphic type
	// var `B` and a goal's free type var also named `B` are unrelated
	// schema variables that happen to print identically. Confusing them
	// — which a name-based predicate does — wedges the matcher when
	// the goal's free type vars happen to share names with the lemma's.
	//
	// The classic failure shape: lemma's `B` gets bound to a compound
	// type `T[B_goal]` from a structurally-relevant anchor (e.g. fst's
	// `prod(A,B) → A` against the goal's `prod(qType, pType) → qType`).
	// When the matcher later recurses INTO that binding and re-encounters
	// `B_goal`, a name-based `isInstantiable` returns true for `B_goal`,
	// the env lookup finds the lemma's `B` → `T[B_goal]` binding, and
	// fails the structural check `T[B_goal].Equals(B_goal)`. The whole
	// anchor's match is aborted, and a smaller anchor (e.g. just `=`)
	// commits a wrong substitution like `{A := B_goal, B := B_goal}`.
	//
	// The concrete case is a leaf of a pairwise casewise-recursion proof
	// where fst anchor `fst(,(x,y))` fails to match the goal's
	// `fst(,(qʹ₀, pʹ₀))` because the matcher conflates lemma's "B" with
	// goal's "B").
	lemmaTypeVars := collectLemmaTypeVarPointers(lemma)
	isInstantiable := func(v core.VarType) bool {
		_, ok := lemmaTypeVars[v]
		return ok
	}

	idx := BuildGoalSubtermIndex(goal)

	// Sort anchors size-descending so context-rich patterns set bindings
	// before generic-const heads can. The bug we're avoiding: a bare
	// const head like `=` (size 1) is polymorphic and matches against
	// any instance of `=` in the goal — producing bindings determined
	// by the GOAL's surrounding type context, not the lemma's intended
	// shape. E.g., for a lemma `∀l. c(l) = ...` over lists, the lemma's
	// internal `=` is on `list(?A)` but the goal's outer `=` may be on
	// `list(prod(?B, ?C))` — matching them binds `?A := prod(?B, ?C)`,
	// which then corrupts later merges against the
	// structurally-relevant `c(l)` anchor.
	//
	// Processing larger anchors first lets the structurally-meaningful
	// patterns commit their bindings; the bare-const matches that come
	// later either confirm those bindings or fail to merge (skipped).
	//
	// We use MatchingPointsUnderLambda so under-λ anchors are included
	// for both lemma and goal (via BuildGoalSubtermIndex). This catches
	// shapes like `⊢ ∀f. f(λx:A. c(x)) = …` where the lemma's only
	// A-bearing const witness `c` sits under a λ — the standard
	// (skip-λ) walk would emit no useful anchor.
	anchors := skeleton.MatchingPointsUnderLambda(lemma)
	sort.SliceStable(anchors, func(i, j int) bool {
		pi, pj := typeAdaptAnchorPriority(anchors[i].Term), typeAdaptAnchorPriority(anchors[j].Term)
		if pi != pj {
			return pi < pj
		}
		return anchors[i].Term.Size() > anchors[j].Term.Size()
	})

	// Seed the accumulator with existential-binder-type matches BEFORE the
	// const-anchor sweep. The lemma's conclusion existentials are the
	// "outputs" it provides; aligning their binder types with the goal's
	// existential binder types recovers the type substitution that the
	// goal's witness type demands — information that is INVISIBLE to the
	// const-head anchor walk because an existential's bound variable is
	// var-headed, never a const anchor.
	//
	// Worked example (num_recursion applied to a 2-arg primitive-recursion
	// existence goal): lemma `∀f e. ∃fn:num→A. …`, goal `∃fn:num→num→num. …`.
	// The only A-bearing const anchor is the bare `=` (at lemma type A),
	// which matches the goal's `=` (at type num) and would pin A:=num — a
	// misadaptation that leaves the lemma's `∃fn:num→num` unable to provide
	// the goal's `∃fn:num→num→num`. Matching the binder types `num→A` vs
	// `num→num→num` instead pins A:=num→num, the value the goal actually
	// needs. Seeding first means the weak `=` anchor is then a no-op: the
	// pre-substitute step (below) rewrites its A away, so it no longer
	// carries an instantiable var and is skipped.
	//
	// Scope: existentials only. The lemma's universal binders are parameters
	// the agent will instantiate, NOT outputs aligned with the goal; matching
	// them against goal binders would reintroduce the very ambiguity this
	// seeding resolves.
	// Type vars that an INFORMATIVE anchor (one carrying a real, non-logical
	// const — mk_pair, the pair `,`, a defined symbol) constrains. A weak
	// logical-only anchor must not bind any of these: their binding comes
	// from the informative anchor (even when that binding is identity, e.g.
	// `,(a,b)` at prod(A,B) matched against the goal's prod(A,B)). Without
	// this, a `(a = x)` anchor at value type A coincidentally type-matches
	// the goal's `⇔` (= at bool) and clobbers A := bool — the bridge-lemma
	// adaptation bug on iff goals (citing `goal ⇔ R`). When NO informative
	// anchor covers a var (e.g. lemma `∀x:A. x = x`), the weak `=` anchor is
	// the only witness and IS honored — a legitimate poly-eq → ground-eq
	// adaptation.
	informativeTypeVars := map[core.VarType]struct{}{}
	for _, anchor := range anchors {
		if !anchorHasInformativeConst(anchor.Term) {
			continue
		}
		ext.TermAnyTypeVar(anchor.Term, func(v core.VarType) bool {
			if _, ok := lemmaTypeVars[v]; ok {
				informativeTypeVars[v] = struct{}{}
			}
			return false
		})
	}

	return &typeAdaptContext{
		lemma:               lemma,
		goal:                goal,
		lemmaTypeVars:       lemmaTypeVars,
		isInstantiable:      isInstantiable,
		idx:                 idx,
		anchors:             anchors,
		informativeTypeVars: informativeTypeVars,
		seed:                seedExistentialBinderSubsts(lemma, goal, isInstantiable),
	}
}

// candidateSubsts runs the shared per-candidate gate chain (the
// dropVars drop — a weak anchor's informative-owned vars — the
// occurs-check drop, optional identity drop) on a raw TypeOnlyMatch
// result. Returns nil when the candidate contributes nothing admissible.
func (c *typeAdaptContext) candidateSubsts(
	anchorTerm core.Term,
	dropVars map[core.VarType]struct{},
	isPatternVar core.VarPredicate,
	candidate core.Term,
	skipIdentityOnlyCandidates bool,
) []core.TypeSubst {
	newSubsts, ok := TypeOnlyMatch(anchorTerm, candidate, isPatternVar, c.isInstantiable)
	if !ok || len(newSubsts) == 0 {
		return nil
	}
	if len(dropVars) > 0 {
		// Drop bindings for type vars an informative anchor owns (see
		// informativeTypeVars) — the caller passes that set for a weak
		// anchor and nothing for an informative one. Keeps weak-anchor
		// bindings only for vars no informative anchor witnesses.
		newSubsts = dropSubstsForVars(newSubsts, dropVars)
		if len(newSubsts) == 0 {
			return nil
		}
	}
	// Reject occurs-check failures (e.g. B := (C,P)→B from a name
	// collision between the lemma's polymorphic slot and a goal free
	// type-var of the same name); see dropRecursiveTypeSubsts. This
	// occurs-check lives in the lemma-adaptation path, NOT the core
	// matcher: MakeConstTerm legitimately produces self-mentioning
	// substitutions like `A := T[A]` when instantiating a polymorphic
	// const at a type built over its own schema var, which must be
	// applied, not dropped.
	var dropped bool
	if newSubsts, dropped = dropRecursiveTypeSubsts(newSubsts); dropped {
		c.occursDropped = true
	}
	if len(newSubsts) == 0 {
		return nil
	}
	if skipIdentityOnlyCandidates {
		newSubsts = dropIdentityTypeSubsts(newSubsts)
		if len(newSubsts) == 0 {
			return nil
		}
	}
	return newSubsts
}

// sweep runs the deterministic anchor sweep: per anchor, the FIRST
// candidate whose gated substitution merges consistently commits, and the
// walk moves on. `pin` (may be nil) is merged into the accumulator ahead
// of the walk — the enumeration's way of forcing one specific instance
// choice before the deterministic completion; a pin inconsistent with the
// existential-binder seed returns ok=false.
func (c *typeAdaptContext) sweep(pin []core.TypeSubst, skipIdentityOnlyCandidates bool) ([]core.TypeSubst, bool) {
	accumulated := c.seed
	if len(pin) > 0 {
		merged, ok := mergeTypeSubsts(accumulated, pin)
		if !ok {
			return nil, false
		}
		accumulated = merged
	}
	for _, anchor := range c.anchors {
		anchorTerm := anchor.Term
		if len(accumulated) > 0 {
			anchorTerm = anchorTerm.TypeSubstitute(accumulated...)
		}
		// Bare logical/equality constants are too weak as type witnesses:
		// `=` alone can match an unrelated outer boolean equality and bind a
		// definition's domain type to bool before the real const anchor is seen.
		if isBareGenericTypeAdaptAnchor(anchorTerm) {
			continue
		}
		if !ext.TermAnyTypeVar(anchorTerm, c.isInstantiable) {
			continue // anchor's lemma-side type vars all bound by prior matches
		}
		// A bare (size-1) polymorphic const anchor is an ORDER-dependent
		// type witness: it type-matches EVERY bare occurrence of the same
		// const in the goal, so whichever candidate happens to come first
		// in index order decides the binding. When the goal carries the
		// const at several DISTINCT type instances, that pick is a
		// coin-flip, not a structural finding — worse, the name-collision
		// occurs-check (dropRecursiveTypeSubsts) can eliminate the
		// structurally-relevant instance and let the loop fall through to
		// a wrong one. Classic repro: loading finite_set.FiniteImage
		// (∀s:(A→bool).∀f:(A→B). finite(image(f,s)) ∨ ¬finite(s)) into a
		// goal with bare finite at prod(A,B), A and B — the bare
		// finite⟨B⟩ anchor's B := prod(A,B) candidate is occurs-dropped,
		// then B := A commits, collapsing f's binder to A→A and wedging
		// every downstream instantiate. So: a bare-const anchor may bind
		// only when its goal-side bare instances are UNAMBIGUOUS; with
		// conflicting instances the lemma's var stays free/general (the
		// agent can still pin it via instantiate/term_specialize).
		// Single-instance goals keep the pre-existing behavior — see
		// TestTryAdaptLemmaTypes_LemmaSideUnderLambda, which relies on a
		// bare under-λ const anchor binding. (Enumeration recovers the
		// skipped instances as PINS — collectAnchorPins deliberately
		// omits this guard.)
		if pc, isBareConst := anchorTerm.AsConst(); isBareConst {
			if bareConstAnchorAmbiguous(pc, c.idx.Candidates(anchorTerm), c.isInstantiable) {
				continue
			}
		}
		var dropVars map[core.VarType]struct{}
		if !anchorHasInformativeConst(anchorTerm) {
			dropVars = c.informativeTypeVars
		}
		isPatternVar := makeIsPatternVar(anchor)

		patSize := anchorTerm.Size()
		for _, candidate := range c.idx.Candidates(anchorTerm) {
			if candidate.Term.Size() < patSize {
				continue
			}
			newSubsts := c.candidateSubsts(anchorTerm, dropVars, isPatternVar, candidate.Term, skipIdentityOnlyCandidates)
			if len(newSubsts) == 0 {
				continue
			}
			merged, mergeOk := mergeTypeSubsts(accumulated, newSubsts)
			if !mergeOk {
				continue // inconsistent with prior anchors — try next candidate
			}
			accumulated = merged
			break // committed; move to next anchor
		}
	}
	return accumulated, true
}

// collectAnchorPins enumerates the DISTINCT single-anchor substitutions
// the goal offers — the instance choices the deterministic sweep never
// revisits after its first commit. Same anchor walk and per-candidate
// gate chain as sweep, with two deliberate differences:
//
//   - every candidate of every anchor is considered (no first-commit
//     break), each pre-substituted with the existential seed only, so
//     instance alternatives hidden behind the sweep's commit order (the
//     partial-application `∧(list_length(nil) = 0)` anchor can only ever
//     match a conjunction's FIRST conjunct, committing that instance
//     before any list_length-headed anchor runs) become visible;
//   - the ambiguous-bare-const guard is omitted: for enumeration the
//     ambiguity IS the multi-instance signal, and each distinct
//     instance becomes a pin (the primary unpinned sweep keeps the
//     guard, preserving TryAdaptLemmaTypes' order-independence);
//   - an equation between two of the lemma's own binders at a COMPOUND
//     type pins (slotEquationAtCompoundType): `s = t` for `∀s t:(A →
//     bool)` is weak by the informative-const test — its one constant
//     is `=` — and the sweep's informative-var drop would discard the
//     binding it reads off the goal's equation whenever the lemma also
//     carries a real constant for A (`x ∈ s`); but that constant may
//     occur nowhere in the goal (extensionality is the FIRST move of a
//     set-equality proof, and `∈` appears only after it fires), so a
//     rule anchored by polymorphic built-ins alone was never enumerated
//     at a goal carrying a second element type and fired nothing, with
//     no diagnostic. The type of such an anchor is the author's own
//     binder declaration, and a compound type cannot unify with bool,
//     so the ⇔ coincidence the drop guards against is structurally
//     impossible there: the equation's own type is a pin a reader takes
//     at a glance. A slot equation at a BARE type variable (`∀x y:A. x =
//     y`) stays weak — it matches every `⇔` in the goal.
//
// Pins dedup by canonical substitution key; the walk completes, bounded
// by the goal's anchors and their candidates.
func (c *typeAdaptContext) collectAnchorPins(skipIdentityOnlyCandidates bool) [][]core.TypeSubst {
	var pins [][]core.TypeSubst
	seen := map[string]struct{}{}
	for _, anchor := range c.anchors {
		anchorTerm := anchor.Term
		if len(c.seed) > 0 {
			anchorTerm = anchorTerm.TypeSubstitute(c.seed...)
		}
		if isBareGenericTypeAdaptAnchor(anchorTerm) {
			continue
		}
		if !ext.TermAnyTypeVar(anchorTerm, c.isInstantiable) {
			continue
		}
		isPatternVar := makeIsPatternVar(anchor)
		var dropVars map[core.VarType]struct{}
		if !anchorHasInformativeConst(anchorTerm) && !slotEquationAtCompoundType(anchorTerm, isPatternVar) {
			dropVars = c.informativeTypeVars
		}
		patSize := anchorTerm.Size()
		for _, candidate := range c.idx.Candidates(anchorTerm) {
			if candidate.Term.Size() < patSize {
				continue
			}
			newSubsts := c.candidateSubsts(anchorTerm, dropVars, isPatternVar, candidate.Term, skipIdentityOnlyCandidates)
			if len(newSubsts) == 0 {
				continue
			}
			pin, ok := mergeTypeSubsts(c.seed, newSubsts)
			if !ok {
				continue // conflicts with the existential-binder seed
			}
			k := typeSubstsStateKey(pin)
			if _, dup := seen[k]; dup {
				continue
			}
			seen[k] = struct{}{}
			pins = append(pins, pin)
		}
	}
	return pins
}

// slotEquationAtCompoundType reports whether t is an equation between
// two pattern slots — the lemma's own ∀-binders — whose type is not a
// bare type variable: `s = t` under `∀s t:(A → bool)`, `l = m` under
// `∀l m:list(A)`. See collectAnchorPins: the enumeration reads a pin off
// such an anchor's type although its only constant is `=`.
func slotEquationAtCompoundType(t core.Term, isPatternVar core.VarPredicate) bool {
	l, r, ok := core.MatchesEQ(t)
	if !ok {
		return false
	}
	lv, lok := l.AsVar()
	rv, rok := r.AsVar()
	if !lok || !rok || !isPatternVar(lv) || !isPatternVar(rv) {
		return false
	}
	_, bare := lv.Type().(core.VarType)
	return !bare
}

// typeSubstsStateKey renders an accumulated substitution as a canonical
// (order-insensitive) dedup key for the enumeration's pin set. Keyed by
// the source VarType's pointer identity — the same discipline as the
// sweep's isInstantiable predicate — so two lemma vars that merely share a
// name never collapse into one pin.
func typeSubstsStateKey(substs []core.TypeSubst) string {
	parts := make([]string, 0, len(substs))
	for _, s := range substs {
		parts = append(parts, fmt.Sprintf("%p:=%s", s.VarType, s.HolType.Key()))
	}
	sort.Strings(parts)
	return strings.Join(parts, ";")
}

func typeAdaptAnchorPriority(t core.Term) int {
	if _, _, ok := ext.MatchesAND(t); ok {
		return 1
	}
	if _, _, ok := ext.MatchesOR(t); ok {
		return 1
	}
	if _, _, ok := ext.MatchesIMPLY(t); ok {
		return 1
	}
	if _, _, ok := ext.MatchesIFF(t); ok {
		return 1
	}
	if ext.MatchesNOT(t) != nil {
		return 1
	}
	if _, _, ok := ext.MatchesEQ(t); ok {
		return 1
	}
	return 0
}

func isBareGenericTypeAdaptAnchor(t core.Term) bool {
	c, ok := t.AsConst()
	if !ok {
		return false
	}
	return isLogicalOpConst(c)
}

// isLogicalOpConst reports whether c is one of the bare logical/equality
// connectives whose polymorphic type carries no reliable type-pinning
// information (=, which also represents ⇔; ¬; ∧; ∨; ⇒).
func isLogicalOpConst(c core.ConstTerm) bool {
	return c.Meta().Equals(core.MetaEq()) ||
		c.Meta().Equals(ext.NOT.Meta()) ||
		c.Meta().Equals(ext.AND.Meta()) ||
		c.Meta().Equals(ext.OR.Meta()) ||
		c.Meta().Equals(ext.IMPLY.Meta())
}

// anchorHasInformativeConst reports whether t contains any constant that
// is NOT a bare logical/equality op (see isLogicalOpConst). Such a const —
// mk_pair, the pair `,`, any defined symbol — carries real type structure
// that pins the lemma's type vars to the goal's concrete types. An anchor
// built ONLY from logical ops and variables (e.g. `(a = x)`, `(= a)`,
// `(a ≠ x)`) derives its type binding solely from the polymorphic `=`/op,
// which type-matches any same-shaped op in the goal — including `⇔` (= at
// bool) — and so binds value type vars to bool by coincidence. Skipping
// such anchors generalizes the size-1-only isBareGenericTypeAdaptAnchor
// skip to applied logical terms.
func anchorHasInformativeConst(t core.Term) bool {
	switch ct := t.Core().(type) {
	case core.ConstTerm:
		return !isLogicalOpConst(ct)
	case core.AppliedTerm:
		return anchorHasInformativeConst(ct.Fun()) || anchorHasInformativeConst(ct.Arg())
	case core.AbsTerm:
		return anchorHasInformativeConst(ct.Var()) || anchorHasInformativeConst(ct.Body())
	default: // core.VarTerm
		return false
	}
}

// collectLemmaTypeVarPointers walks the lemma's conclusion + hyps and
// returns the set of `VarType` pointers appearing as type variables.
// Used by `tryAdaptLemmaTypesImpl`'s `isInstantiable` predicate to
// distinguish the lemma's own polymorphic schema variables from
// goal-side free type vars that happen to share names — name-based
// predicates conflate them and break the matcher when a goal's free
// type vars carry names shared with the lemma's. See the comment at
// the predicate's construction site for the live-frontier repro shape.
// renameLemmaTypeVarsApart is the ENUMERATIONS' second attempt, reached
// when the shared-name sweep dropped a
// candidate binding by its by-name occurs-check (typeAdaptContext.
// occursDropped) — a sweep that found nothing for another reason (an
// identity-only match, no anchor) keeps its recorded answer, and the
// single adaptation (TryAdaptLemmaTypes) retries only where the sweep
// left a captured letter, since it replaces the bare lemma rather than
// adding an instance beside it. The sweep's
// occurs-check (dropRecursiveTypeSubsts) is by NAME: a lemma letter `A`
// and a goal letter `A` are one name to it, so the instance
// `A := A → bool` — a set lemma read at families, the goal's own point
// type inside the image — is dropped as recursive, and the lemma is
// never adapted. That name-collision behaviour is part of every
// recorded σ's semantics (see unshareLemmaTypeVars), so it is not
// changed; what this adds is an instance the first sweep could not
// reach: the lemma's colliding letters are renamed apart from the
// goal's, the sweep runs on the renamed lemma, and letters the
// adaptation leaves free are named apart from the goal's
// (ResidualLetterNames). A σ the first sweep records is untouched — the
// retry appends only distinct additional instances.
//
// Returns nil when no lemma letter shares a name with a goal letter
// (the retry would repeat the first sweep).
func renameLemmaTypeVarsApart(lemma core.Prop, goal core.Prop) (core.Prop, []core.TypeSubst) {
	goalNames := map[core.TypeName]struct{}{}
	collectGoal := func(v core.VarType) bool {
		goalNames[v.Name()] = struct{}{}
		return false
	}
	ext.TermAnyTypeVar(goal.Conclusion(), collectGoal)
	for h := range goal.HypIter() {
		ext.TermAnyTypeVar(h, collectGoal)
	}
	if len(goalNames) == 0 {
		return nil, nil
	}
	byName := map[core.TypeName]core.VarType{}
	var names []core.TypeName
	for v := range collectLemmaTypeVarPointers(lemma) {
		if _, shared := goalNames[v.Name()]; !shared {
			continue
		}
		if _, dup := byName[v.Name()]; !dup {
			byName[v.Name()] = v
			names = append(names, v.Name())
		}
	}
	if len(names) == 0 {
		return nil, nil
	}
	sort.Slice(names, func(i, j int) bool { return names[i] < names[j] })
	fwd := make([]core.TypeSubst, 0, len(names))
	back := make([]core.TypeSubst, 0, len(names))
	for i, n := range names {
		// Reserved name: cannot collide with a lemma, chapter or goal
		// letter, and never escapes — every free occurrence is named
		// again by ResidualLetterNames.
		apart := core.MakeVarType(core.TypeName(fmt.Sprintf("?apart%d_%s", i, n)))
		fwd = append(fwd, core.MakeTypeSubst(byName[n], apart))
		back = append(back, core.MakeTypeSubst(apart, core.MakeVarType(n)))
	}
	if typeAdaptDebug {
		fmt.Fprintf(os.Stderr, "[renameLemmaTypeVarsApart] lemma=%s renamed %d colliding letter(s) apart\n",
			lemma.AlphaKey(), len(names))
	}
	return core.PropTypeInst(lemma, fwd...), back
}

// unshareLemmaTypeVars restores the adaptation sweep's precondition that the
// lemma's `VarType` POINTERS are disjoint from the goal's — with the NAMES
// unchanged, so every name-based mechanism behaves exactly as it does on the
// live search path.
//
// The sweep separates "the lemma's instantiable slots" from "the goal's rigid
// free type vars" via the pointer-keyed `isInstantiable` set (see the long
// comment in newTypeAdaptContext) — which silently assumes the two props were
// built independently, as they are on the live search path (cited lemma vs
// session goal — distinct decodes, distinct pointers, even when the NAMES
// collide). The emit/replay paths break that assumption: goal and lemma are
// decoded from the SAME proto pool (PoolReader restores structural sharing) or
// built through emit's shared symbol table, so a goal type var named B and the
// lemma's polymorphic B are literally the same pointer. `isInstantiable` then
// treats goal-side occurrences as pattern slots: the structurally-relevant
// anchors abort mid-match and a small anchor commits a degenerate binding
// instead (observed: FiniteImage against a finite⟨A→bool⟩/finite⟨B⟩ goal
// adapting to B:=B instead of B:=A→bool, which shifted the AutoExpand target
// and broke emit's CNF collection —"polymorphic
// type-var assignment").
//
// Names must NOT change: the sweep's name-collision behaviors — the
// dropRecursiveTypeSubsts occurs-check and the identity-binding drops — are
// part of the RECORDED σ's semantics (a proof recorded at session time chose
// its bindings under those collisions; an emit-side sweep that dodges them
// picks a different σ and diverges). But a direct same-name pointer
// refresh is impossible: VarType.Equals/Substitute and the typeSubstituteImpl
// "unchanged" shortcuts are all name-based, so a fresh pointer with the old
// name is judged a no-op and the old node is returned. Hence the TWO-STEP
// rebuild: substitute each shared name X to a reserved temp name (a real
// rebuild — names differ), then substitute the temp back to a FRESH VarType
// named X (again a real rebuild). Net: α-identical lemma, fresh pointers.
// Returns lemma unchanged when no pointer is shared (the live-search
// configuration, byte-identical behavior).
func unshareLemmaTypeVars(lemma core.Prop, goal core.Prop) core.Prop {
	lemmaPtrs := collectLemmaTypeVarPointers(lemma)
	if len(lemmaPtrs) == 0 {
		return lemma
	}
	shared := false
	check := func(v core.VarType) bool {
		_, ok := lemmaPtrs[v]
		shared = shared || ok
		return ok
	}
	ext.TermAnyTypeVar(goal.Conclusion(), check)
	for h := range goal.HypIter() {
		if shared {
			break
		}
		ext.TermAnyTypeVar(h, check)
	}
	if !shared {
		return lemma
	}
	names := make([]core.TypeName, 0, len(lemmaPtrs))
	byName := map[core.TypeName]core.VarType{}
	for v := range lemmaPtrs {
		if _, dup := byName[v.Name()]; !dup {
			byName[v.Name()] = v
			names = append(names, v.Name())
		}
	}
	sort.Slice(names, func(i, j int) bool { return names[i] < names[j] })
	fwd := make([]core.TypeSubst, 0, len(names))
	back := make([]core.TypeSubst, 0, len(names))
	for i, n := range names {
		// Reserved temp name: cannot collide with lemma / goal names.
		tmp := core.MakeVarType(core.TypeName(fmt.Sprintf("?taush%d_%s", i, n)))
		fwd = append(fwd, core.MakeTypeSubst(byName[n], tmp))
		back = append(back, core.MakeTypeSubst(tmp, core.MakeVarType(n)))
	}
	if typeAdaptDebug {
		fmt.Fprintf(os.Stderr, "[unshareLemmaTypeVars] lemma=%s refreshed %d shared type var name(s)\n",
			lemma.AlphaKey(), len(names))
	}
	return core.PropTypeInst(core.PropTypeInst(lemma, fwd...), back...)
}

func collectLemmaTypeVarPointers(lemma core.Prop) map[core.VarType]struct{} {
	out := map[core.VarType]struct{}{}
	collect := func(v core.VarType) bool {
		out[v] = struct{}{}
		return false
	}
	ext.TermAnyTypeVar(lemma.Conclusion(), collect)
	for h := range lemma.HypIter() {
		ext.TermAnyTypeVar(h, collect)
	}
	return out
}

func goalHasLemmaSelfImageHyp(goal, lemma core.Prop) bool {
	lemmaConcl := lemma.Conclusion()
	return goal.AnyHyp(func(h core.Term) bool {
		return h.AlphaEquals(lemmaConcl)
	})
}

// seedExistentialBinderSubsts recovers a type substitution by aligning
// the existential-binder types of the lemma's conclusion with those of
// the goal's conclusion. It pairs the lemma's i-th conclusion existential
// with the goal's i-th conclusion existential (by skeleton-walk order) and
// type-matches their binder types via core.MatchTypeInto, treating the
// lemma's type vars as instantiable. Bindings are merged across pairs and
// must be consistent; an inconsistent pair is skipped rather than
// aborting the whole seed.
//
// This is the "existential witness type" anchor described in
// tryAdaptLemmaTypes: it sees type-var information that the const-head
// anchor walk cannot, because an existential's bound variable is
// var-headed. Universals are deliberately excluded — they are the lemma's
// parameters, not outputs aligned with the goal.
func seedExistentialBinderSubsts(lemma, goal core.Prop, isInstantiable core.VarTypePredicate) []core.TypeSubst {
	lemmaTypes := conclusionExistentialBinderTypes(lemma.Conclusion())
	if len(lemmaTypes) == 0 {
		return nil
	}
	goalTypes := conclusionExistentialBinderTypes(goal.Conclusion())
	if len(goalTypes) == 0 {
		return nil
	}
	// SAFETY GATE: positional pairing requires the lemma's ∃-binder count to
	// match the goal's. With a mismatch, lemma's i-th ∃ is not necessarily
	// the binder the goal's i-th ∃ is meant to provide — they could lie in
	// unrelated sub-skeletons. The classic miss is set_fold_stage: lemma's
	// conclusion has 2 ∃-binders (∃x:A inside the second conjunct, ∃c:B
	// next to it) and the goal (set_fold_stage's successor lemma) has 4 (∃uʹ:A, ∃y:A,
	// ∃t:B, ∃w:B at top level). Position pairs lemma[1]=B with goal[1]=A
	// and silently commits B := A — collapsing the lemma's polymorphism
	// so a downstream `instantiate` at a (A,B)→B witness fails with
	// "expected ((A,A)→A)" on the residual ∀f. Requiring count parity
	// keeps the worked example (1 ∃ on each side, the documented
	// num_recursion case) and skips the set_fold_stage-style mismatch.
	if len(lemmaTypes) != len(goalTypes) {
		return nil
	}
	n := len(lemmaTypes)
	var accumulated []core.TypeSubst
	for i := 0; i < n; i++ {
		lt := lemmaTypes[i]
		if !ext.TypeAnyVar(lt, isInstantiable) {
			continue // binder carries no instantiable var — nothing to recover
		}
		patType := lt
		if len(accumulated) > 0 {
			patType = patType.Substitute(accumulated...)
			if !ext.TypeAnyVar(patType, isInstantiable) {
				continue // already bound by an earlier pair
			}
		}
		var env []core.TypeSubst
		if !core.MatchTypeInto(patType, goalTypes[i], isInstantiable, &env) {
			continue
		}
		env = dropIdentityTypeSubsts(env)
		// Reject occurs-check failures from a name collision between
		// the lemma's polymorphic ∃-binder type and a goal type-var of
		// the same name — same rationale as the anchor walk above.
		env, _ = dropRecursiveTypeSubsts(env)
		if len(env) == 0 {
			continue
		}
		if merged, ok := mergeTypeSubsts(accumulated, env); ok {
			accumulated = merged
		}
	}
	if len(accumulated) == 0 {
		return nil
	}
	// POST-CHECK: even with count parity, the committed σ must be
	// CONSISTENT with every ∃-binder pair — applying σ to lemma[i] must
	// yield a type that core-matches goal[i]. If any pair would type-
	// disagree after σ, the seed corrupts the lemma; discard.
	//
	// This catches the same-count cousin of the set_fold_stage miss: lemma
	// `∃u:A.∃v:B` vs goal `∃u:C.∃v:C` — pair[0] gives A→C, pair[1] is
	// vacuous (B isn't pinned because the goal's v is C, but C is not
	// a lemma var), and the lemma's B silently remains polymorphic
	// while A→C is committed — the lemma loads with A:=C but B still
	// free, which is silently wrong-shaped. With this check we keep the
	// match-clean cases and bail when any pair would mis-bind.
	for i := 0; i < n; i++ {
		applied := lemmaTypes[i].Substitute(accumulated...)
		if !typesMatchUpToInstantiable(applied, goalTypes[i], isInstantiable) {
			return nil
		}
	}
	return accumulated
}

// typesMatchUpToInstantiable reports whether `pat` matches `tgt` allowing
// only the lemma's own type vars (those satisfying `instantiable`) to be
// further specialized. Used by the seedExistentialBinderSubsts post-check
// to ensure the committed σ is consistent with every paired position.
func typesMatchUpToInstantiable(
	pat, tgt core.HolType, instantiable core.VarTypePredicate) bool {
	var env []core.TypeSubst
	return core.MatchTypeInto(pat, tgt, instantiable, &env)
}

// conclusionExistentialBinderTypes returns the binder types of every
// existential reached by walking the propositional skeleton of `concl`
// (stripping ∀/∃, recursing through ∧/∨/⇒/⇔/¬), in walk order. Mirrors
// skeleton.MatchingPoints' skeleton traversal so the lemma and goal sides
// are enumerated under the same discipline.
func conclusionExistentialBinderTypes(concl core.Term) []core.HolType {
	var out []core.HolType
	var walk func(t core.Term)
	walk = func(t core.Term) {
		if abs := ext.MatchesFORALL(t); !abs.IsZero() {
			walk(abs.Body())
			return
		}
		if abs := ext.MatchesEXISTS(t); !abs.IsZero() {
			out = append(out, abs.Var().Type())
			walk(abs.Body())
			return
		}
		if l, r, ok := ext.MatchesAND(t); ok {
			walk(l)
			walk(r)
			return
		}
		if l, r, ok := ext.MatchesIFF(t); ok {
			walk(l)
			walk(r)
			return
		}
		if l, r, ok := ext.MatchesIMPLY(t); ok {
			walk(l)
			walk(r)
			return
		}
		if l, r, ok := ext.MatchesOR(t); ok {
			walk(l)
			walk(r)
			return
		}
		if a := ext.MatchesNOT(t); a != nil {
			walk(a)
			return
		}
	}
	walk(concl)
	return out
}

// dropIdentityTypeSubsts removes identity entries (A := A) that
// core.MatchTypeInto leaves in its env for cross-position consistency.
// They are vacuous for accumulation and would spuriously conflict in
// mergeTypeSubsts (A bound to A vs A bound to a real type).
func dropIdentityTypeSubsts(substs []core.TypeSubst) []core.TypeSubst {
	out := substs[:0]
	for _, s := range substs {
		if !s.HolType.Equals(s.VarType) {
			out = append(out, s)
		}
	}
	return out
}

// bareConstAnchorAmbiguous reports whether the bare-const lemma anchor
// `pat` has two or more bare-const goal candidates with DISTINCT type
// instances that each type-match it. For a fixed const pattern the
// induced type substitution is a pure function of the candidate's
// instance type, so "all matching instances are Equals-equal" is exactly
// "the binding is candidate-order independent". Non-const candidates
// (applied occurrences) are ignored — a bare-const pattern can never
// structurally match them anyway. Candidates whose instance does NOT
// type-match the (possibly pre-substituted) pattern don't count either:
// they could never produce a binding, so they cannot make the pick
// ambiguous.
func bareConstAnchorAmbiguous(
	pat core.ConstTerm,
	candidates []skeleton.IndexedTerm,
	isInstantiable core.VarTypePredicate,
) bool {
	var matched core.HolType
	for _, c := range candidates {
		ct, ok := c.Term.AsConst()
		if !ok {
			continue
		}
		var env []core.TypeSubst
		if !core.MatchTypeInto(pat.Type(), ct.Type(), isInstantiable, &env) {
			continue
		}
		if matched == nil {
			matched = ct.Type()
			continue
		}
		if !matched.Equals(ct.Type()) {
			return true
		}
	}
	return false
}

// dropSubstsForVars removes substitutions whose source type var is in
// `owned` — used to stop a weak logical-only anchor from binding a type
// var that an informative anchor already constrains.
func dropSubstsForVars(substs []core.TypeSubst, owned map[core.VarType]struct{}) []core.TypeSubst {
	out := substs[:0]
	for _, s := range substs {
		if _, ok := owned[s.VarType]; !ok {
			out = append(out, s)
		}
	}
	return out
}

func dropRecursiveTypeSubsts(substs []core.TypeSubst) (out []core.TypeSubst, dropped bool) {
	out = substs[:0]
	for _, s := range substs {
		if s.HolType.Equals(s.VarType) {
			out = append(out, s) // pure identity: vacuous, keep (locks the name)
			continue
		}
		if !ext.TypeHasVar(s.HolType, s.VarType) {
			out = append(out, s)
		} else {
			dropped = true
		}
	}
	return out, dropped
}

// mergeTypeSubsts returns the union of `existing` and `additional`
// substitutions. Any type variable bound in both must map to equal
// HolTypes; on conflict returns (nil, false). Used to accumulate
// substitutions across matching anchors of a single lemma.
func mergeTypeSubsts(existing, additional []core.TypeSubst) ([]core.TypeSubst, bool) {
	out := append([]core.TypeSubst{}, existing...)
	for _, s := range additional {
		conflict := false
		merged := false
		for _, e := range out {
			if e.VarType.Equals(s.VarType) {
				if !e.HolType.Equals(s.HolType) {
					conflict = true
				}
				merged = true
				break
			}
		}
		if conflict {
			return nil, false
		}
		if !merged {
			out = append(out, s)
		}
	}
	return out, true
}

// makeIsPatternVar turns an IndexedTerm's BoundVars set into a
// VarPredicate suitable for TypeOnlyMatch. A pattern var (slot) is one
// that was bound by an outer ∀/∃ stripped during the skeleton walk —
// these may match any target subterm. λ-bound vars inside the anchor
// are NOT slots; they are matched alpha-style by the structural matcher.
func makeIsPatternVar(it skeleton.IndexedTerm) core.VarPredicate {
	if len(it.BoundVars) == 0 {
		return func(core.VarTerm) bool { return false }
	}
	return it.IsBound
}

// logTypeAdapt writes a one-line summary of a successful adaptation to
// stderr. Only called when typeAdaptDebug is set.
func logTypeAdapt(lemma core.Prop, substs []core.TypeSubst) {
	fmt.Fprintf(os.Stderr, "[tryAdaptLemmaTypes] lemma=%s substs=[%s]\n",
		lemma.AlphaKey(), formatTypeSubsts(substs))
}

func formatTypeSubsts(substs []core.TypeSubst) string {
	parts := make([]string, 0, len(substs))
	for _, s := range substs {
		parts = append(parts, fmt.Sprintf("%s:=%s", s.VarType.Name(), s.HolType.Key()))
	}
	return strings.Join(parts, ",")
}
