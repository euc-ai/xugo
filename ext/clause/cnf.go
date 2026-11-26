/**
 * File: cnf.go
 *
 * Implements Conjunctive Normal Form (CNF) representation and conversion.
 *
 * Key structure:
 * - CNFClauses: Conjunction of disjunctive clauses (A ∧ B ∧ ...)
 *   Fields:
 *   - groundVars: Free variables in original term that cannot be instantiated
 *   - clauses: Array of disjunctive clauses, ordered by size
 *
 * Main functions:
 * - isCNF(t Term): Tests if a term is already in CNF
 * - makeCNF(t Term): Creates CNFClauses from a term in CNF
 * - (cnf *CNFClauses).GroundVars(): Returns ground variables
 * - (cnf *CNFClauses).Clauses(): Returns clauses array
 * - (cnf *CNFClauses).ClausesMap(): Converts clauses to map keyed by ClauseKey
 * - (cnf *CNFClauses).RefuteProp(): Creates proposition for refutation proof
 * - NegateGoalCNF(goal Prop, cnfNormalizationCache *TermKeyPropMap):
 *   Converts a goal proposition to CNF of its negation for refutation proving.
 *   Uses a single raw-keyed cache for the whole cnfNormalizeWorkFlow output.
 *   Returns:
 *   - CNF clauses
 *   - A direct theorem if found during conversion
 *   - A reconstruction function to restore the original goal from refutation
 *   - Error if conversion fails
 * - NegateGoalCNFFromPreNormalized(goal Prop, cache *CNFNormalizeCache):
 *   Same as NegateGoalCNF but uses the prelude/middle/tail-split pipeline
 *   with a two-level cache: per-hyp PreCNFNormalize result
 *   cached on raw-hyp alpha key, middle+tail result cached on pre-CNF
 *   alpha key. Resolves alpha-distinct-but-pre-CNF-equivalent cache misses.
 */

package clause

import (
	"context"
	"slices"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

// CNF clauses with form A ∧ B ∧ ...
// where A, B, ... are all disjunctive clauses, each of them lools like
// ∀x.∀y.(P(x) ∨ Q(y) ∨ ...)
type CNFClauses struct {
	// vars that are free in the original term.
	// They are essentially "given const", meaning they cannot be instantiated.
	groundVars VarList

	// ordered by size.
	clauses []*Clause
}

// Checks if a term is in Conjunctive Normal Form (CNF).
// A term is in CNF if it's either a disjunctive clause or a conjunction of disjunctive clauses,
// and doesn't contain any OR, IMPLY, IFF, FORALL, EXISTS, or UNIQUE terms that need to be normalized.
func isCNF(t Term) bool {
	if ext.IsDisjunctive(t) {
		return true
	} else if _, _, ok := MatchesOR(t); ok {
		return false
	} else if _, _, ok := MatchesIMPLY(t); ok {
		return false
	} else if _, _, ok := MatchesIFF(t); ok {
		return false
	} else if !MatchesFORALL(t).IsZero() {
		return false
	} else if !MatchesEXISTS(t).IsZero() {
		return false
	} else if !MatchesUNIQUE(t).IsZero() {
		return false
	}
	return utils.All(DecomposesAND(t), ext.IsDisjunctive)
}

var FalseCNF = &CNFClauses{clauses: []*Clause{FClause}}

// Returns the list of ground variables in the CNF
func (cnf *CNFClauses) GroundVars() *VarList { return &cnf.groundVars }

// Returns the list of clauses in the CNF
func (cnf *CNFClauses) Clauses() []*Clause { return cnf.clauses }

// Returns a map of clause keys to clauses for efficient lookup
func (cnf *CNFClauses) ClausesMap() map[ClauseKey]*Clause {
	m := make(map[ClauseKey]*Clause, len(cnf.clauses))
	for _, c := range cnf.clauses {
		m[c.Key()] = c
	}
	return m
}

// Creates a proposition in the form of {cnf clauses} ⊢ ⊥
// This is used for refutation proofs
func (cnf *CNFClauses) RefuteProp() Prop {
	return MakeProp(F, utils.MapSlice(cnf.Clauses(), (*Clause).Term)...)
}

// Removes existential vars of a give hyp
// Also returns a callback that can be used to recover the original prop.
func removeHypExistsVars(w Prop, h Term) (*PropWrapper, utils.EndoFunc[Prop]) {
	vars, body := DecomposesEXISTS(h)
	Assert(w.HasHyp(h) && !vars.Empty())
	wOrig, s := w, h
	for v := range vars.Iter() {
		Assert(!wOrig.HasFreeName(v.Name()))
		w = prop.InstExists(s, v).DeriveTrans(w)
		s = MatchesEXISTS(s).Body()
	}
	reconstruct := func(prop Prop) Prop {
		if prop.HasHyp(body) {
			_body := body
			for _, v := range vars.Backward() {
				prop = WrapProp(prop).HypExists(v, _body)
				_body = Exists(v)(_body)
			}
		}
		return prop
	}
	Assert(reconstruct(w).AlphaEquals(wOrig))
	return WrapProp(w), reconstruct
}

type NegateGoalCNFResult struct {
	CNF         *CNFClauses
	Thm         Thm
	Reconstruct utils.EndoFunc[Prop]

	// SelfConsistentGoal is the input goal restated with each hypothesis in the EXACT
	// form the per-hyp pipeline actually normalized (Lhs(cnfHyps[i]) — the
	// cnfNormalizeCache representative, which on a cache hit carries the
	// representative's bound-variable naming, e.g. ∃m.∃n where the raw input
	// was ∃a.∃b). It is alpha-equal to the input goal, but normalizing IT with
	// a fresh/nil cache deterministically reproduces THIS result's CNF — so a
	// CNF-refute proof that stores SelfConsistentGoal as its goal is self-consistent
	// (front half ↔ refutation cert) regardless of cache warming order, which
	// is what makes replay cache-independent. nil only on the early
	// already-refuted (FalseCNF) return paths, which never produce a stored
	// certificate.
	SelfConsistentGoal Prop
}

// CNFNormalizeCache bundles the two caches used by the prelude/middle/tail-split
// CNF normalization pipeline:
//
//   - PreCNF: term-level PreCNFNormalize result. Keyed on raw-hyp alpha key,
//     value is ⊢ h = h_pre. The same type as prop.PreCNFCache, so a single
//     cache instance can be shared by prop.Normalize (via cache.Normalize)
//     and the CNF refuter prelude — alpha-distinct hyps with the same
//     pre-CNF form share one cache slot.
//
//   - Tail: middle (Skolemization) + tail (denote + distribute + per-clause
//     normalization) result. Keyed on the *pre-CNF* alpha key, value is
//     ⊢ h_pre = h_cnf. Two hyps that pre-CNF to the same shape share the
//     expensive distribute step.
//
// Either field may be nil to disable that level of caching independently.
//
// Safe for concurrent use; the underlying maps are sync.Map-backed.
type CNFNormalizeCache struct {
	PreCNF *PreCNFCache
	Tail   *ext.TermKeyPropMap
}

// preCNFCache returns c.PreCNF or nil if c is nil.
func (c *CNFNormalizeCache) preCNFCache() *PreCNFCache {
	if c == nil {
		return nil
	}
	return c.PreCNF
}

// tailCache returns c.Tail or nil if c is nil.
func (c *CNFNormalizeCache) tailCache() *ext.TermKeyPropMap {
	if c == nil {
		return nil
	}
	return c.Tail
}

// Given a prop (to be proved), make a cnf out of the negation of the prop.
// If a thm that is stronger than the goal is directly proved
// during the process, returns the thm.
// Also returns a reconstruct callback that can be used to reconstruct the original prop
// if the cnf clauses are refuted. The input of the reconstruct callback is in the form
// of {cnf clauses} ⊢ ⊥
// The output is the original goal in general, but sometimes
// the reconstruct callback might return a stronger prop than the original one
// because the hyps might get merged during the reconstruction.
func NegateGoalCNF(
	ctx context.Context,
	goal Prop,
	cnfNormalizationCache *ext.TermKeyPropMap,
) (*NegateGoalCNFResult, error) {
	// Full pipeline; uses a single raw-keyed cache for the whole
	// cnfNormalizeWorkFlow output (legacy behaviour).
	//
	// ctx gates the coarse boundaries inside negateGoalCNF (entry, per-hyp
	// fan-out, post-wait loop). The per-hyp heavy work itself runs through
	// cnfNormalizeWorkFlow, which is still Background-tailed — the raw entry
	// is not on the agent's budgeted auto / probe path (only the
	// FromPreNormalized variant is), so deep ctx threading into the raw tail
	// was deliberately not pursued.
	perHyp := func(h Term) *PropWrapper {
		if cnfNormalizationCache == nil {
			return cnfNormalizeWorkFlow(h)
		}
		// Name-faithful hit only (Equals, not α): see NegateGoalCNFFromPre-
		// Normalized's perHyp for why an α-keyed hit breaks the persisted
		// proof's goal↔cert naming self-consistency.
		if u, ok := cnfNormalizationCache.Load(h.AlphaKey()); ok && Lhs(u).Equals(h) {
			return WrapProp(u)
		}
		w := cnfNormalizeWorkFlow(h)
		if w != nil {
			// First entry wins (no α-variant thrash).
			cnfNormalizationCache.LoadOrStore(h.AlphaKey(), w)
		}
		return w
	}
	return negateGoalCNF(ctx, goal, perHyp)
}

// NegateGoalCNFFromPreNormalized is the prelude-split variant of NegateGoalCNF.
//
// It runs the per-hypothesis prelude → middle → tail decomposition explicitly,
// using the two-level cache in CNFNormalizeCache:
//   - PreCNF stage: ⊢ h = h_pre (cached on raw-hyp alpha key).
//   - Middle+tail: ⊢ h_pre = h_cnf (cached on pre-CNF alpha key, so two
//     hyps with the same pre-CNF form share the expensive Skolem+distribute
//     work).
//
// cache may be nil to disable both levels of caching.
//
// ctx is honored at coarse boundaries inside negateGoalCNF and the underlying
// cnfNormalizeWorkFlowFromPreNormalized — entry, between per-hyp fan-out and
// the post-wait loop, and at each iteration of the post-wait loop. The inner
// rewrite combinators (Skolem / distribute / per-clause) are not interrupted
// mid-traversal; the assumption is that any single coarse stage finishes in
// well under a budget tick. Non-agent call sites pass context.Background().
func NegateGoalCNFFromPreNormalized(
	ctx context.Context,
	goal Prop,
	cache *CNFNormalizeCache,
) (*NegateGoalCNFResult, error) {
	preCache := cache.preCNFCache()
	tailCache := cache.tailCache()
	perHyp := func(h Term) *PropWrapper {
		// Stage 1: term-level pre-CNF rewrite (⊢ h = h_pre). Used as the
		// CNFTail cache key (h_pre.AlphaKey collapses alpha-distinct-but-
		// pre-CNF-equivalent hyps into a single cache slot) and as a bridge
		// for composing cached tail results back to the current hyp.
		//
		// NAME-FAITHFUL (both stages): a cache hit is taken only when the
		// cached equation's LHS Equals the probe syntactically (names
		// included). An α-keyed hit would splice in the FIRST populator's
		// binder naming, which determines the Skolem-witness names of the
		// resulting CNF clauses — while Lhs(cnfHyps[i]) (what
		// buildSelfConsistentGoal persists) keeps the CURRENT naming. That
		// LHS/RHS naming split is exactly what broke the stored-proof
		// self-consistency invariant (cold renorm of the stored goal must
		// reproduce the cert's clause naming; the ẋ₀/ẋʹ₀ row of real_construction.AddSym).
		// α-variants are rare, so the lost sharing is negligible; refuter.
		// Prove's write gate backstops any residual naming decoupling.
		preH := preCache.NormalizeTermNameFaithful(h)
		hPre := Rhs(preH)
		hPreKey := hPre.AlphaKey()

		// Stage 2: tail cache lookup. Cached value is ⊢ h_pre = h_cnf for
		// some hyp that previously hashed to this pre-CNF key; reused only
		// when that hyp was h_pre VERBATIM (see name-faithfulness above).
		if tailCache != nil {
			if u, ok := tailCache.Load(hPreKey); ok && Lhs(u).Equals(hPre) {
				return preH.EqTrans(u)
			}
		}

		// Cache miss: run the refuter-only middle+tail from h_pre. The
		// FromPreNormalized workflow may still run TrivialNormalize for the
		// specific shapes PreCNF deliberately preserves (⇔/∃!/COND/Hilbert/
		// FunEq), but it does not try to predict every raw-input basic rewrite.
		tail := cnfNormalizeWorkFlowFromPreNormalized(ctx, hPre)
		if tail == nil {
			return nil
		}
		if tailCache != nil {
			// First entry wins: a name-mismatched α-variant recomputes its own
			// tail but must NOT evict the resident entry (alternating variants
			// would otherwise thrash the slot).
			tailCache.LoadOrStore(hPreKey, tail)
		}
		return preH.EqTrans(tail)
	}
	return negateGoalCNF(ctx, goal, perHyp)
}

// negateGoalCNF is the shared body of NegateGoalCNF /
// NegateGoalCNFFromPreNormalized. perHyp encodes the per-hypothesis CNF
// preprocessing pipeline (full vs prelude/middle/tail-split, with their
// respective caches).
//
// ctx is checked at coarse boundaries: function entry, before each per-hyp
// goroutine starts work (so an already-cancelled ctx leaves cnfHyps[i] nil
// and surfaces as errCNF after wg.Wait), after wg.Wait itself, and at the
// top of each iteration of the post-wait `for i := range cnfHyps` loop. The
// rewrite combinators (Skolem / AssocAND / SimplifyConjunct) are not
// interrupted mid-traversal — each individual stage is expected to finish
// in well under a budget tick.
// buildSelfConsistentGoal restates `original` with each component in the cache-
// representative form `lhsTerms` (= Lhs(cnfHyps[i]), one per post-negation
// hyp), so re-normalizing the result with a fresh cache reproduces the same
// CNF (see NegateGoalCNFResult.SelfConsistentGoal). The result is alpha-equal to
// `original`.
//
//   - ⊥-conclusion goal: hyps are 1:1 with lhsTerms → restate directly.
//   - C-conclusion goal: negation appended ¬C as a hyp, so exactly one lhsTerm
//     is the (representative of) ¬C; identify it by alpha key, strip the ¬ to
//     recover the representative conclusion, and use the rest as hyps.
//
// Falls back to `original` if the ¬C entry can't be cleanly isolated (e.g.
// MakeProp deduped ¬C into an existing hyp) — that goal simply keeps its raw
// form, no worse than before.
func buildSelfConsistentGoal(original Prop, negConcl Term, lhsTerms []Term) Prop {
	if original.Conclusion().Equals(F) {
		return MakeProp(F, lhsTerms...)
	}
	if original.HasHyp(negConcl) {
		// The appended ¬conclusion was deduped into an existing hypothesis.
		// Keep that literal as a hypothesis; there is no separate appended entry
		// to remove.
		return MakeProp(original.Conclusion(), lhsTerms...)
	}
	negKey := negConcl.AlphaKey()
	idx := slices.IndexFunc(lhsTerms, func(t Term) bool { return t.AlphaKey() == negKey })
	if idx < 0 {
		return original
	}
	concl := MatchesNOT(lhsTerms[idx])
	if concl == nil {
		return original
	}
	hyps := append(slices.Clone(lhsTerms[:idx:idx]), lhsTerms[idx+1:]...)
	return MakeProp(concl, hyps...)
}

func negateGoalCNF(
	ctx context.Context,
	goal Prop,
	perHyp func(Term) *PropWrapper,
) (*NegateGoalCNFResult, error) {
	if err := ctx.Err(); err != nil {
		return nil, err
	}

	originalGoal := goal
	var reconstructs []utils.EndoFunc[Prop]
	var negConclTerm Term // the ¬conclusion added below (nil when goal is already ⊥)

	// If conclusion is not ⊥, negate it and add to hypotheses
	// This transforms G ⊢ C to G, ¬C ⊢ ⊥
	if !goal.Conclusion().Equals(F) {
		concl, negConcl := goal.Conclusion(), Not(goal.Conclusion())
		negConclTerm = negConcl
		goal = MakeProp(F, append(goal.Hyps(), negConcl)...)
		_goal := goal // for capturing
		reconstruct := func(p Prop) Prop {
			Assert(IsStronger(p, _goal))
			if !p.HasHyp(negConcl) {
				return p
			}
			return prop.DoubleNeg(concl).EqMP(WrapProp(p).NegHyp(negConcl))
		}
		reconstructs = []utils.EndoFunc[Prop]{reconstruct}
	}

	// A goal that is already `{} ⊢ ⊥` (the arith fast-path rewrites an
	// identically-false conclusion to ⊥ before the refuter runs) has no
	// hypotheses to build clauses from: the negated-goal CNF is the empty
	// conjunction (⊤), which nothing can refute. Not a conversion failure
	// (errCNF) — the goal is legal, just unrefutable. Decline cleanly; the
	// downstream AND-decomposition asserts on an empty hyp slice.
	if goal.NumHyps() == 0 {
		return nil, errNothingToRefute
	}

	// Normalize each hypothesis in parallel using the supplied per-hyp
	// pipeline; a panic in one is raised here (utils.Tasks).
	wg := utils.Tasks{}

	cnfHyps := make([]*PropWrapper, goal.NumHyps())
	for i := range goal.NumHyps() {
		wg.Go(func() {
			// Skip work on an already-cancelled ctx; perHyp itself may
			// be a long-running rewrite pipeline. cnfHyps[i] stays nil
			// and surfaces as errCNF after wg.Wait — caller sees the
			// ctx.Err() check below first and gets the right error.
			if ctx.Err() != nil {
				return
			}
			cnfHyps[i] = perHyp(goal.Hyp(i))
		})
	}
	wg.Wait()

	if err := ctx.Err(); err != nil {
		return nil, err
	}

	// Check if normalization failed for any hypothesis
	for i := range cnfHyps {
		if cnfHyps[i] == nil {
			return nil, errCNF
		}
		// If a hypothesis normalizes to ⊥, the goal is already proven
		if Rhs(cnfHyps[i]).Equals(F) {
			p := Prop(cnfHyps[i].LeftAssume())
			if reconstructs != nil {
				p = reconstructs[0](p)
			}
			Assert(IsStronger(p, originalGoal))
			return &NegateGoalCNFResult{FalseCNF, p.AsThmCert(), nil, nil}, nil
		}
	}

	// The cache-representative restatement of the goal (see SelfConsistentGoal doc):
	// each hyp/conclusion in the exact form the per-hyp pipeline used
	// (Lhs(cnfHyps[i])), so re-normalizing it with a fresh cache reproduces this
	// result's CNF. Storing THIS as a CNF-refute proof's goal makes the proof
	// self-consistent (front ↔ cert) independent of cnfNormalizeCache warming
	// order. When the conclusion was negated above, that ¬conclusion is the
	// LAST cnfHyps entry (it was appended last); strip its ¬ to recover the
	// representative conclusion, so SelfConsistentGoal stays alpha-equal to the input
	// goal (same shape) rather than the F-form.
	lhsTerms := utils.MapSlice(cnfHyps, func(w *PropWrapper) Term { return Lhs(w) })
	selfConsistentGoal := buildSelfConsistentGoal(originalGoal, negConclTerm, lhsTerms)

	// Process each normalized hypothesis
	for i := range cnfHyps {
		if err := ctx.Err(); err != nil {
			return nil, err
		}
		w := cnfHyps[i]
		if !goal.HasHyp(Lhs(w)) {
			// This can happen if the correspoding hyp was
			// already processed in a previous iteration.
			continue
		}

		// Handle variable subscripting for existential quantifiers
		w = w.RewriteConclRhs(prop.SubscriptExistsVars(goal.HasFreeName))
		reconstructs = append(reconstructs, w.LeftAssume().MaybeDeriveTrans)

		h := Rhs(w)
		goal = w.RightAssume().DeriveTrans(goal)

		// Handle existential quantifiers in hypotheses
		if !MatchesEXISTS(h).IsZero() {
			_goal, reconstruct := removeHypExistsVars(goal, h)
			goal = _goal
			_, h = DecomposesEXISTS(h)
			reconstructs = append(reconstructs, reconstruct)
		}

		// Handle conjunctions in hypotheses by breaking them apart
		if _, _, ok := MatchesAND(h); ok {
			Assert(prop.AssocANDRewrite(h) == nil)
			hyps := DecomposesAND(h)
			u := prop.ConclANDRecursive(hyps...)
			goal = u.DeriveTrans(goal)
			_goal := goal // for capturing
			reconstruct := func(p Prop) Prop {
				Assert(IsStronger(p, _goal))
				if utils.None(hyps, p.HasHyp) {
					return p
				}
				for _, t := range prop.HypANDRecursive(hyps...) {
					p = t.MaybeDeriveTrans(p)
				}
				return p
			}
			reconstructs = append(reconstructs, reconstruct)
		}
	}

	// Combine all reconstruction functions to create the final reconstruction function
	reconstruct := utils.RevChainFunc(reconstructs)
	Assert(goal.Conclusion().Equals(F) && IsStronger(reconstruct(goal), originalGoal))

	// Additional transformations on the goal to prepare for CNF conversion

	// Break apart hypotheses using AND decomposition
	hyps := goal.Hyps()

	for _, u := range prop.HypANDRecursive(hyps...) {
		goal = u.DeriveTrans(goal)
	}
	u := prop.ConclANDRecursive(hyps...)

	Assert(goal.NumHyps() == 1 && !goal.Hyp(0).Equals(F))
	if !isCNF(goal.Hyp(0)) {
		// Same capability-gap class as makeCNF's per-clause reject (see its
		// doc): the per-hyp tail can leave non-clausal residue (e.g. an ∃
		// stuck under ∧ after a stalled denote pass). Input-dependent, so a
		// clean decline — not an internal-invariant Assert.
		return nil, errCNF
	}

	// Simplify conjuncts in the CNF
	w := prop.SimplifyConjunct(goal.Hyp(0))
	if w == nil {
		cnf, err := makeCNF(goal.Hyp(0))
		if err != nil {
			return nil, err
		}
		return &NegateGoalCNFResult{cnf, Thm{}, reconstruct, selfConsistentGoal}, nil
	}

	w = w.RewriteConclRhs(prop.AssocANDRewrite)

	// Replace goal with a new goal with the simpler hypothesis
	goal = w.RightAssume().DeriveTrans(goal) // ∧ {new hyps} ⊢ ⊥

	w = w.EqMP(u) // {old hyps} ⊢ ∧ {new hyps}

	// If the simplified CNF is ⊥, the goal is already proven
	if w.Conclusion().Equals(F) {
		p := reconstruct(w) // {old hyps} ⊢ ⊥
		Assert(IsStronger(p, originalGoal))
		return &NegateGoalCNFResult{FalseCNF, p.AsThmCert(), nil, nil}, nil
	}
	Assert(isCNF(w.Conclusion()))

	// Create the final callback that reconstructs the original goal from the refutation proof
	finalReconstruct := func(p Prop) Prop {
		if _, _, ok := MatchesAND(w.Conclusion()); ok {
			for _, t := range prop.HypANDRecursive(DecomposesAND(w.Conclusion())...) {
				p = t.MaybeDeriveTrans(p)
			}
		}
		p = w.DeriveTrans(p)
		return reconstruct(p)
	}
	Assert(IsStronger(
		finalReconstruct(MakeProp(F, DecomposesAND(w.Conclusion())...)),
		originalGoal))

	cnf, err := makeCNF(goal.Hyp(0))
	if err != nil {
		return nil, err
	}
	return &NegateGoalCNFResult{cnf, Thm{}, finalReconstruct, selfConsistentGoal}, nil
}

// Should be called after CNFRewrite, or when we know for sure the input is in CNF.
// Constructs a CNFClauses structure from a term in CNF, collecting ground variables
// and adjusting universal variables in each clause.
//
// Returns errCNF when a conjunct is not a legal clause — i.e. it still
// carries a quantifier or boolean operator nested INSIDE an atom (e.g. a
// λ-comprehension argument `λs.P(λx.∃y. …)` that the tail's denote pass
// could not extract: insideDenoteRewrite denotes one instance-specific
// pattern at a time and cannot reach every binder-nested occurrence, so
// set-comprehension-heavy hypotheses — the set_tac wide-hyp De Morgan
// incident — can legitimately reach here un-clausified). Such input is a
// CNF-preprocessing capability gap, not a soundness violation: the caller
// (negateGoalCNF) propagates the error and the refuter declines to build,
// surfacing a clean tactic failure instead of a panic.
func makeCNF(t Term) (*CNFClauses, error) {
	groundVars := VarList{}
	terms := DecomposesAND(t)
	for _, h := range terms {
		for _, v := range h.Frees(nil) {
			groundVars.Add(v)
		}
	}
	adjustVars := prop.AdjustUnivVars(groundVars.HasName)

	clauses := make([]*Clause, len(terms))

	for i, s := range terms {
		if ext.InsideQuantifierBoolOp(s) != nil {
			return nil, errCNF
		}
		if u := adjustVars(s); u != nil {
			s = Rhs(u)
		}
		clauses[i] = MakeClause(s)
	}

	slices.SortStableFunc(clauses, CompareClauses)

	return &CNFClauses{groundVars, clauses}, nil
}

// PreCNFCache aliases prop.PreCNFCache so a single cache instance can be
// shared between prop.Normalize (via cache.Normalize / cache.NormalizeTerm)
// and the CNF refuter's prelude. Defined in prop because non-CNF callers
// (e.g. the lemma matcher's witness-bridging path) use it without
// depending on clause.
type PreCNFCache = prop.PreCNFCache
