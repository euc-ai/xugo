/**
 * File: subterm.go
 *
 * Implements functions for manipulating and analyzing subterms of logical expressions.
 *
 * Main functions:
 * - SubTerms(terms ...Term): Returns iterator over all subterms, including the terms themselves
 *   Handles variable scoping in abstractions, e.g., λx.P(x) is a subterm of ∃x.Q(P(x))
 *
 * - IsSub(s, t Term, env ...VarTerm): Tests if s is a subterm of t, considering bindings
 *   Properly accounts for variable scoping and abstraction environments
 *
 * - FrequentSubTerms(sizeThreshold int, terms ...Term): Finds common subterms above threshold size
 *   Returns the subterm with highest (size × frequency) value
 *
 * - HilbertSubTerm(s Term): Finds a subterm that is a Hilbert term (containing ε calculus)
 */

package ext

import (
	"iter"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

// All subterms of the given terms, including themselves.
// If a subterm has free vars that are under abstraction,
// add the abstracted vars to the subterm so the result
// is consistent under α-equal.
// For example, P(x) is not considered a sub term of ∃x.Q(P(x)),
// but λx.P(x) is considered a sub term of ∃x.Q(P(x)),
// even though it is not a structure-wise sub.
// For binary op connected terms, we directly work with the components,
// E.g. for x ∧ y, we only returns subterms of x and y plus x and y themselves,
// not one-side subterms like "x ∧ ".
//
// Precision/termination policy (the size switch): enumeration is NOT a
// pure function of node pointers — the Abs case re-wraps body subterms
// with the enclosing binders (ReverseAbsFreeVars), so a pointer-shared
// node reached under two different binder paths emits two DIFFERENT
// wrapped values. Exact enumeration therefore costs O(naive tree size)
// and is exponential on shared DAGs; pointer dedup is bounded but LOSSY
// (first-wrapping-wins: re-wrapped variants under later binder paths
// are dropped). The policy: below the size gate exact enumeration is
// affordable (naive size IS the cost) and consumers that distinguish
// wrapped variants — clause deduce position enumeration, CNF prep —
// rely on it; above the gate we degrade to pointer dedup, losing
// variants in a regime where exact enumeration never terminates anyway.
// This switch is about WHICH VALUES appear, not how often — occurrence
// counting is FrequentSubTerms' own contract, over the per-path walk.
func SubTerms(terms ...Term) iter.Seq[Term] {
	needsDedup := false
	for _, t := range terms {
		if NaiveWalkNeedsMemo(t) {
			needsDedup = true
			break
		}
	}
	if !needsDedup {
		seqs := make([]iter.Seq[Term], len(terms))
		for i, t := range terms {
			seqs[i] = utils.MapIter(subTermsSeq(t, false, nil), occurrence.Term)
		}
		return utils.ConcatIter(seqs...)
	}
	// The seen set is allocated per ITERATION (not per SubTerms call) so
	// the returned Seq stays safely re-rangeable. It spans input terms:
	// hyps and conclusion routinely share structure.
	return func(yield func(Term) bool) {
		seen := &SeenSet{}
		for _, t := range terms {
			for o := range subTermsSeq(t, false, seen) {
				if !yield(o.term) {
					return
				}
			}
		}
	}
}

// occurrence is one subterm occurrence of a walk: the subterm (wrapped
// with the binders it sits under, see SubTerms) and whether this
// occurrence is a proper prefix of an application spine — `(<) a`
// inside `a < b`, a node of the curried encoding rather than a
// subexpression the proof talks about. A term can occur both ways:
// `f a` applied to `x` in one place and passed as an argument in
// another.
type occurrence struct {
	term   Term
	prefix bool
}

func (o occurrence) Term() Term { return o.term }

// subTermsSeq is SubTerms' single-term recursion, per occurrence. A nil
// seen means the plain per-path walk — a subtree pointer-shared by k
// parents is enumerated k times, so counting over the enumeration is
// exact, at a cost of O(naive tree size) that grows O(2^depth) on
// shared DAGs (NaiveWalkNeedsMemo is the exact test); a non-nil seen
// dedupes pointer-shared Applied/Abs nodes across the whole top-level
// call (including across multiple input terms — hyps and conclusion
// routinely share structure). prefix is the tag of s itself.
func subTermsSeq(s Term, prefix bool, seen *SeenSet) iter.Seq[occurrence] {
	switch s := s.Core().(type) {
	case VarTerm, ConstTerm:
		return utils.SingleIter(occurrence{Term(s), prefix})
	case AppliedTerm:
		if seen.Visited(s) {
			return utils.EmptyIter[occurrence]
		}
		if l, r, ok := binaryOpMatchers(s); ok {
			return utils.ConcatIter(
				utils.SingleIter(occurrence{Term(s), prefix}),
				subTermsSeq(l, false, seen),
				subTermsSeq(r, false, seen))
		}
		return utils.ConcatIter(
			utils.SingleIter(occurrence{Term(s), prefix}),
			subTermsSeq(s.Fun(), true, seen),
			subTermsSeq(s.Arg(), false, seen))
	case AbsTerm:
		if seen.Visited(s) {
			return utils.EmptyIter[occurrence]
		}
		vars, body := MatchesAbs(s)
		subTerms := utils.MapIter(
			subTermsSeq(body, false, seen),
			func(o occurrence) occurrence {
				return occurrence{ReverseAbsFreeVars(o.term, vars...), o.prefix}
			})

		return utils.ConcatIter(
			utils.SingleIter(occurrence{Term(s), prefix}),
			utils.FilterIter(subTerms, func(o occurrence) bool { return s.AlphaEquals(o.term) }))
	}
	panic("Wrong term type.")
}

var binaryOpMatchers = MergeBinaryOpMatchers(
	MatchesAND,
	MatchesOR,
	MatchesIMPLY,
	MatchesEQ,
)

var BinaryBooleanOpMatchers = MergeBinaryOpMatchers(
	MatchesAND,
	MatchesOR,
	MatchesIMPLY,
	MatchesIFF,
)

// The definition of subterm here is consistent with the subTerms function above.
// For example, P(x) is not considered a sub term of ∃x.Q(P(x)),
// but λx.P(x) is considered a sub term of ∃x.Q(P(x)),
// even though it is not a structure-wise sub.
//
// The size-gated memo records the negative ("s not found in this
// subtree") results, keyed by (binder-env content, node pointer) — see
// EnvMemo in this file. Only misses are recorded: a hit
// short-circuits the whole walk immediately.
func IsSub(s, t Term, env ...VarTerm) bool {
	// s is fixed across the whole walk — decompose it and build the
	// matcher once, not per visited node.
	sVars, sBody := MatchesAbs(s)
	match := ReverseAbsFreeVarsMatch(sVars, sBody)
	return isSubImpl(s, t, env, match, EnvMemoFor[struct{}](t))
}

func isSubImpl(
	s, t Term, env []VarTerm,
	match func(Term, ...VarTerm) ([]VarTerm, bool),
	memo *EnvMemo[struct{}]) bool {

	if _, ok := match(t, env...); ok {
		return true
	}

	switch t := t.Core().(type) {
	case AppliedTerm:
		scope := memo.Scope(env)
		if _, ok := scope.Get(t); ok {
			return false
		}
		if isSubImpl(s, t.Fun(), env, match, memo) ||
			isSubImpl(s, t.Arg(), env, match, memo) {
			return true
		}
		scope.Put(t, struct{}{})
		return false
	case AbsTerm:
		if s.HasFree(t.Var()) {
			n := t.Var().Name()
			for s.HasName(n) || t.Body().HasName(n) {
				n = utils.NextName(n)
			}
			return isSubImpl(s,
				t.ChangeAbsVar(n).Body(),
				env, match, memo)
		}
		return isSubImpl(
			s, t.Body(), utils.CloneAppend(env, t.Var()), match, memo)
	}
	return false
}

// FrequentSubTerms finds the subterm worth naming: among the subterms
// of size ≥ sizeThreshold occurring more than once across terms, the
// one of the largest volume — size × occurrences, the size a denote of
// it removes (at equal volume, the larger size). A term whose
// occurrences are all spine prefixes is not a candidate: a proof never
// talks about `(<) a`, and naming it hides the relation behind a
// function variable — at equal count the prefix would always beat its
// own argument by exactly one node. A term that occurs as a value
// somewhere (an argument, a whole term) counts every occurrence,
// applied ones included, because the rewrite folds those too.
//
// Occurrences are counted per path, at the term's naive tree size —
// unbounded on shared DAGs — so a term the gate (NaiveWalkNeedsMemo)
// flags is enumerated with pointer dedup instead: its duplicate counts
// collapse and it mostly declines (count > 1 required) rather than
// never terminating. Counting still spans terms: the same subterm in
// two hyps counts twice either way.
func FrequentSubTerms(sizeThreshold int, terms ...Term) Term {
	var repeatingTerms []Term
	var counter, valueCounter []int
	for _, t := range terms {
		var seen *SeenSet
		if NaiveWalkNeedsMemo(t) {
			seen = &SeenSet{}
		}
		for o := range subTermsSeq(t, false, seen) {
			if o.term.Size() < sizeThreshold {
				continue
			}
			i, found := slices.BinarySearchFunc(repeatingTerms, o.term, Term.Compare)
			if !found {
				repeatingTerms = slices.Insert(repeatingTerms, i, o.term)
				counter = slices.Insert(counter, i, 0)
				valueCounter = slices.Insert(valueCounter, i, 0)
			}
			counter[i]++
			if !o.prefix {
				valueCounter[i]++
			}
		}
	}

	volume, count := 0, 0
	var s Term
	for i := range repeatingTerms {
		if valueCounter[i] == 0 {
			continue
		}
		if v := repeatingTerms[i].Size() * counter[i]; counter[i] > 1 &&
			v >= volume &&
			(v > volume || counter[i] < count) {
			s, volume, count = repeatingTerms[i], v, counter[i]
		}
	}
	return s
}

// Find the first subterm (from top to bottom) that satisfies the given predicate.
//
// Size-gated shared-DAG miss memo: the seen set
// records AppliedTerm subtrees that returned nil ("no hit below"), so a
// second visit through a pointer-sharing parent skips the re-descent.
// Miss results are binder-independent — the predicate is tested on RAW
// nodes; ReverseAbsFreeVars wrapping happens only on a hit's return
// path, and a hit short-circuits the whole walk — so pointer-keyed
// memoization cannot change the result, unlike SubTerms' wrapped
// enumeration (see its doc).
func FindTopSubTerm(s Term, predicate utils.Predicate[Term]) Term {
	return findTopSubTerm(s, predicate, "", SeenSetFor(s))
}

// FindTopSubTermCarrying is FindTopSubTerm for a predicate that holds
// only on terms in which name occurs: a subterm without name is not
// entered, so the walk costs the part of s that carries name rather than
// all of s (core memoizes HasName per node). The result is
// FindTopSubTerm's.
func FindTopSubTermCarrying(s Term, name core.TermName, predicate utils.Predicate[Term]) Term {
	return findTopSubTerm(s, predicate, name, SeenSetFor(s))
}

// findTopSubTerm and findBottomSubTerm enter only subterms carrying
// name; the empty name enters every subterm.
func findTopSubTerm(s Term, predicate utils.Predicate[Term], name core.TermName, seen *SeenSet) Term {
	if name != "" && !s.HasName(name) {
		return nil
	}
	if predicate(s) {
		return s
	}
	switch s := s.Core().(type) {
	case AppliedTerm:
		if seen.Visited(s) {
			return nil
		}
		if t := findTopSubTerm(s.Fun(), predicate, name, seen); t != nil {
			return t
		}
		if t := findTopSubTerm(s.Arg(), predicate, name, seen); t != nil {
			return t
		}
	case AbsTerm:
		// AbsTerm not memoized: the returned subterm gets re-wrapped
		// with the abstraction's bound vars via ReverseAbsFreeVars, so
		// the result depends on the enclosing binder identity (not just
		// the pointer). Body subterms pass through the same `seen` set,
		// so shared AppliedTerms inside still get the memo benefit.
		vars, body := MatchesAbs(s)
		if t := findTopSubTerm(body, predicate, name, seen); t != nil {
			return ReverseAbsFreeVars(t, vars...)
		}
	}
	return nil
}

// Find the first subterm (from bottom to top) that satisfies the given predicate.
// Size-gated shared-DAG miss memo — same rationale as FindTopSubTerm.
func FindBottomSubTerm(s Term, predicate utils.Predicate[Term]) Term {
	return findBottomSubTerm(s, predicate, "", SeenSetFor(s))
}

// FindBottomSubTermCarrying is FindBottomSubTerm for a predicate that
// holds only on terms in which name occurs; see FindTopSubTermCarrying.
func FindBottomSubTermCarrying(s Term, name core.TermName, predicate utils.Predicate[Term]) Term {
	return findBottomSubTerm(s, predicate, name, SeenSetFor(s))
}

func findBottomSubTerm(s Term, predicate utils.Predicate[Term], name core.TermName, seen *SeenSet) Term {
	if name != "" && !s.HasName(name) {
		return nil
	}
	switch s := s.Core().(type) {
	case AppliedTerm:
		if seen.Visited(s) {
			return nil
		}
		if t := findBottomSubTerm(s.Fun(), predicate, name, seen); t != nil {
			return t
		}
		if t := findBottomSubTerm(s.Arg(), predicate, name, seen); t != nil {
			return t
		}
	case AbsTerm:
		vars, body := MatchesAbs(s)
		if t := findBottomSubTerm(body, predicate, name, seen); t != nil {
			return ReverseAbsFreeVars(t, vars...)
		}
	}
	if predicate(s) {
		return s
	}
	return nil
}

// Find a subterm that is a meaningful Hilbert term. The walk enters only
// subterms that carry ε.
func HilbertSubTerm(s Term) Term {
	return FindTopSubTermCarrying(s, core.MetaHilbert().Name(), func(t Term) bool {
		if t, ok := t.AsAppliedTerm(); ok {
			if fun, ok := t.Fun().AsConst(); ok &&
				fun.Meta().Equals(core.MetaHilbert()) {
				// If the ε is not free in the body, it's not
				// a meaningful Hilbert term. e.g. εx.⊥.
				if abs, ok := t.Arg().AsAbsTerm(); ok {
					return abs.Body().HasFree(abs.Var())
				} else { // εP is fine, which is essentially εx.P(x)
					return true
				}
			}
		}
		return false
	})
}

// Recursively decomposes a term by binary operations, collecting all the component terms.
// Used to break down complex formulas into their atomic components.
func decomposeBinaryOp(t Term) []Term {
	if l, r, ok := BinaryBooleanOpMatchers(t); ok {
		return append(decomposeBinaryOp(l), decomposeBinaryOp(r)...)
	} else {
		return []Term{t.Core()}
	}
}

// Replaces the outmost quantifiers to abstractions.
// This is used to help identify nested quantifiers during normalization.
func absQuantifier(t Term) Term {
	existsVars, t := DecomposesEXISTS(t)
	forallVars, t := DecomposesFORALL(t)
	for _, v := range forallVars.Backward() {
		t = Abs(v, t)
	}
	for _, v := range existsVars.Backward() {
		t = Abs(v, t)
	}
	return t
}

// check whether there are quantifiers or bool op terms inside the cnf components.
// E.g. ∃y.P(∀x.Q(x)) or ∃y.P(x ∧ y).
// This might make cnf refuter confused, so they should be taken out first.
func InsideQuantifierBoolOp(t Term) Term {
	// We take _t to be the term that replace the outmost quantifiers to abstrictions.
	// therefore, if any subterm of _t still has quantifeirs, it must be inside the term.
	// E.g. when t = ∃y.P(∀x.Q(x), y), _t = λy.P(∀x.Q(x), y), so the only subterm of _t
	// that still has quantifiers is ∀x.Q(x).
	_t := absQuantifier(t)
	for s := range SubTerms(_t) {
		if s.Equals(_t) {
			continue
		}
		_, _s := MatchesAbs(s)
		if !MatchesFORALL(_s).IsZero() {
			Assert(IsSub(s, t))
			return s
		}
		if !MatchesEXISTS(_s).IsZero() {
			Assert(IsSub(s, t))
			return s
		}
		if !MatchesUNIQUE(_s).IsZero() {
			Assert(IsSub(s, t))
			return s
		}
	}
	// For bool op terms, we first decompose the body to components as much as possible,
	// then add free abs vars to them, then check their subterms.
	// If their subterms still contain bool op, they should be taken out.
	absVars, _t := MatchesAbs(_t)
	for _, term := range decomposeBinaryOp(_t) {
		for s := range SubTerms(ReverseAbsFreeVars(term, absVars...)) {
			if s.Equals(_t) {
				continue
			}
			_, _s := MatchesAbs(s)
			if _, _, ok := BinaryBooleanOpMatchers(_s); ok {
				Assert(IsSub(s, t))
				return s
			}
		}
	}
	return nil
}

// NaiveWalkNeedsMemo is the gate every DAG-walking primitive here
// shares with core's: a per-call pointer memo above
// core.NaiveWalkMemoThreshold, a naive walk that allocates nothing
// below it.
var NaiveWalkNeedsMemo = core.NaiveWalkNeedsMemo

// MemoFor is the walk-entry gate: it returns a live memo iff the memo
// policy requires one for a walk rooted at t, and nil (disabled)
// otherwise.
//
// M is the walker's memo state: one of the memo types below, or a
// walker-local struct composing several of them (see betaEtaMemo). The
// zero value of M must mean "enabled, empty".
func MemoFor[M any](t core.Term) *M {
	if NaiveWalkNeedsMemo(t) {
		return new(M)
	}
	return nil
}

// AdaptiveMemo wraps a walker's memo state M with a cumulative
// visit-budget escalation, for TERM-REBUILDING walks (the βη family)
// where the entry size gate is not a sound work bound.
//
// For a STATIC walk (one that only descends into existing nodes), the
// naive tree size IS the exact naive visit count, so NaiveWalkNeedsMemo
// at entry is a precise work-bound test and nothing more is needed —
// static walkers thread bare memos. A rebuilding walk, however,
// β-substitutes mid-walk and recurses into freshly built terms whose
// cumulative size is unbounded by the entry size. v1 patched that with
// a per-fresh-term size check (memoFor); AdaptiveMemo keeps both
// predictions and adds the sound backstop:
//
//   - entry arm:  AdaptiveFor consults the size gate on the root
//     (identical to the bare-memo entry gate);
//   - fresh arm:  ArmFor consults the size gate on a freshly built
//     mid-walk term (the old memoFor upgrade — arms earlier than the
//     budget would);
//   - budget arm: Arrive counts node arrivals; crossing
//     core.NaiveWalkMemoThreshold arms regardless of what the predictions
//     said. Total naive work is then bounded by
//     budget + O(unique nodes) — bounded regret even on shapes both
//     size checks miss.
//
// Unlike v1's memoFor, arming is walk-global (the state is threaded by
// pointer, so callers above the arming point see the live memo too).
// That widening only ADDS memo hits — the memo is a pure cache.
//
// Determinism: visits is a pure function of the walk's inputs, so
// arming points — and therefore ctx-budget consumption in walkers that
// CheckCtx per arrival — remain deterministic.
//
// Declare the state as a stack value at the walk entry and thread its
// pointer; the zero value is "counting, disarmed". Never share across
// top-level calls or goroutines.
type AdaptiveMemo[M any] struct {
	visits int
	memo   *M
}

// AdaptiveFor returns the walk-entry state, entry-armed per the size
// gate (nil memo, counting mode, when the gate says the naive walk is
// cheap).
func AdaptiveFor[M any](t core.Term) AdaptiveMemo[M] {
	return AdaptiveMemo[M]{memo: MemoFor[M](t)}
}

// Arrive records one node arrival and returns the current memo — nil
// while disarmed. Crossing the visit budget arms it: cumulative naive
// work beyond the threshold means the walk is in blowup territory no
// matter what the entry- and fresh-term size checks predicted.
func (a *AdaptiveMemo[M]) Arrive() *M {
	a.visits++
	if a.memo == nil && a.visits > core.NaiveWalkMemoThreshold {
		a.memo = new(M)
	}
	return a.memo
}

// ArmFor arms on a freshly built mid-walk term that crosses the size
// gate (typically a β-substitution result, which can be exponentially
// larger than the walk's root). No-op when already armed.
func (a *AdaptiveMemo[M]) ArmFor(t core.Term) {
	if a.memo == nil {
		a.memo = MemoFor[M](t)
	}
}

// Memo returns the current memo without recording an arrival — for
// post-recursion stores, where the memo may have been armed during the
// recursion and a stale pre-recursion snapshot would miss it.
func (a *AdaptiveMemo[M]) Memo() *M {
	return a.memo
}

// PtrMemo is a per-call memo table for one pure function of the node
// pointer. A nil *PtrMemo is the plain, zero-allocation path: Load
// always misses and Store is a no-op. The inner map is allocated
// lazily on first Store, so a live-but-unused memo costs nothing.
type PtrMemo[R any] struct {
	m map[Term]R
}

// PtrMemoFor is MemoFor for a bare pointer-keyed memo.
func PtrMemoFor[R any](t core.Term) *PtrMemo[R] {
	return MemoFor[PtrMemo[R]](t)
}

func (m *PtrMemo[R]) Load(t Term) (R, bool) {
	if m == nil {
		var zero R
		return zero, false
	}
	r, ok := m.m[t]
	return r, ok
}

func (m *PtrMemo[R]) Store(t Term, r R) {
	if m == nil {
		return
	}
	if m.m == nil {
		m.m = make(map[Term]R)
	}
	m.m[t] = r
}

// SeenSet is a per-call visited set over node pointers, for walks whose
// per-node contribution is env-independent (pure structural folds,
// early-exit searches). Visited marks t on first call and reports
// whether t had already been visited. A nil *SeenSet never marks and
// always reports false — the plain, multiplicity-preserving path.
type SeenSet struct {
	m map[Term]struct{}
}

// SeenSetFor is MemoFor for a visited set.
func SeenSetFor(t core.Term) *SeenSet {
	return MemoFor[SeenSet](t)
}

func (s *SeenSet) Visited(t Term) bool {
	if s == nil {
		return false
	}
	if _, ok := s.m[t]; ok {
		return true
	}
	if s.m == nil {
		s.m = make(map[Term]struct{})
	}
	s.m[t] = struct{}{}
	return false
}

// EnvMemo memoizes per (binder-env content, term pointer) within one
// top-level walk, for walks whose per-node result depends on the
// abstracted-vars env threaded through binder descent. env only ever
// changes at binder descent, and its entries are the binders' own
// VarTerm pointers, so two visits of a pointer-shared subterm under
// α-identical binder paths reach the same scope node and reuse the
// result. The trie is keyed by env CONTENT (var pointers), not slice
// identity, because each binder descent re-CloneAppends a fresh env
// slice even for a pointer-shared AbsTerm.
//
// A nil *EnvMemo means "memo disabled": Scope returns nil, and nil
// Get/Put/Load/Store are no-ops, so callers need no nil checks.
type EnvMemo[R any] struct {
	results  map[Term]R
	children map[VarTerm]*EnvMemo[R]
}

// EnvMemoFor is MemoFor for an env-scoped memo.
func EnvMemoFor[R any](t core.Term) *EnvMemo[R] {
	return MemoFor[EnvMemo[R]](t)
}

// Scope walks (creating as needed) the trie path for env and returns
// its scope node. Callers that both Get and Put at one visit should
// capture the scope once instead of paying the trie walk twice.
func (c *EnvMemo[R]) Scope(env []VarTerm) *EnvMemo[R] {
	if c == nil {
		return nil
	}
	for _, v := range env {
		child := c.children[v]
		if child == nil {
			if c.children == nil {
				c.children = make(map[VarTerm]*EnvMemo[R])
			}
			child = &EnvMemo[R]{}
			c.children[v] = child
		}
		c = child
	}
	return c
}

// Get reads this scope node's result for t.
func (c *EnvMemo[R]) Get(t Term) (R, bool) {
	if c == nil {
		var zero R
		return zero, false
	}
	r, ok := c.results[t]
	return r, ok
}

// Put records this scope node's result for t.
func (c *EnvMemo[R]) Put(t Term, r R) {
	if c == nil {
		return
	}
	if c.results == nil {
		c.results = make(map[Term]R)
	}
	c.results[t] = r
}

// Load is Scope+Get for single-lookup visits.
func (c *EnvMemo[R]) Load(env []VarTerm, t Term) (R, bool) {
	return c.Scope(env).Get(t)
}

// Store is Scope+Put for single-store visits.
func (c *EnvMemo[R]) Store(env []VarTerm, t Term, r R) {
	c.Scope(env).Put(t, r)
}
