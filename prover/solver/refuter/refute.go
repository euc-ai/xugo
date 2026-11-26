/**
 * File: refute.go
 *
 * Implements the core refutation algorithm for automated theorem proving.
 *
 * Main functions:
 * - (s *_RefuteState) refute(ctx context.Context): Attempts to find a refutation proof
 *   using a combination of strategies (divide-and-conquer, resolution, factoring)
 *
 * - (s *_RefuteState) selectNewClause(ctx context.Context): Selects next clause for processing
 *   based on heuristic criteria like size and complexity
 *
 * - (s *_RefuteState) processNewClause(ctx, succeedChan, newClause): Processes a newly
 *   added clause by attempting factoring and resolution operations
 *
 * - (s *_RefuteState) divideConquer(ctx, divisibleClause): Implements divide-and-conquer
 *   strategy by splitting a clause into components and solving each separately
 *
 * - (s *_RefuteState) findContradicts(c *Clause): Searches for direct contradictions
 *   between clauses
 *
 * Inference operations:
 * - (s *_RefuteState) factor(ctx, succeedChan, wg, c): Performs factoring on a clause
 * - (s *_RefuteState) resolve(ctx, succeedChan, wg, c, clauses): Performs resolution
 *   between clauses
 *
 * Processing functions:
 * - (s *_RefuteState) merge(ctx, division, states): Combines results from sub-problems
 * - (s *_RefuteState) triageClauseThm(ctx, succeedChan, clauseThm): Evaluates and
 *   processes new derived clause theorems
 * - (s *_RefuteState) addToRecord(ctx, clauseThm): Records a derived clause theorem
 * - (s *_RefuteState) checkCache(ctx, succeedChan): Checks proof cache for existing results
 * - (s *_RefuteState) cleanUpRecords(ctx, newClause, kept): Removes redundant clauses
 * - refutesByRewrite(c0, c1): The refutation Simplifies finds between two clauses,
 *   applied to the clauses a search starts from
 */

package refuter

import (
	"context"
	"maps"
	"slices"
	"sync"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/utils"
)

type _RefuteStatus int

const (
	succeed _RefuteStatus = iota
	fail
	cancelled
)

// refute attempts to find a refutation using the given clause loop algorithm.
//
// The method implements a complete theorem proving strategy:
// 1. First checks for divisible clauses to apply divide-and-conquer
// 2. Processes all initial active clauses for factoring and resolution
// 3. Runs the main given clause loop:
//   - Selects clauses from deduction records (passive set)
//   - Moves selected clauses to active set with forward subsumption
//   - Generates new clauses through factoring and resolution
//   - Continues until refutation found, timeout, or search space exhausted
//
// Returns succeed if refutation found, fail if search exhausted,
// or cancelled if context cancelled/timeout.
func (s *_RefuteState) refute(ctx context.Context) _RefuteStatus {
	if s.isRefuted() {
		return succeed
	}
	// A search one of whose goroutines panicked is over: the fault is
	// the search's answer (_Refuter.search raises it).
	if s.fault.recorded() != nil {
		return cancelled
	}

	// First strategy: Try divide and conquer if possible
	// If we find an init clause that is divisible,
	// we can divide the problem into subproblems.
	for _, c := range s.origInitClauses {
		// Some original clauses may not be active (because they failed to be added),
		// We need to filter them out.
		if s.activeSet.has(c) && c.Divisible() {
			division := c.Division()
			// the divided clause should not be among the init clauses
			// because the divisible clause was able to be added to init clauses.
			Assert(utils.None(division.DividedClauses, s.isInitClause))
			if !s.divisionHasExistingClause(division) {
				return s.divideConquer(ctx, division)
			}
			// if one of the divided clauses exists,
			// we can mark the original clause as useless.
			s.retire(c)
		}
	}

	// Second strategy: case split on boolean ground variables.
	// For a bool variable b₀, we know b₀ = ⊤ ∨ b₀ = ⊥ (excluded middle),
	// so we split into two sub-problems assuming b₀ and ¬b₀ respectively.
	for v := range s.groundVars.Iter() {
		if core.IsBool(v) {
			division := clause.BoolVarDivision(v)
			if !s.divisionHasExistingClause(division) {
				return s.divideConquer(ctx, division)
			}
		}
	}

	wg := &sync.WaitGroup{}
	defer wg.Wait()

	ctx, cancel := context.WithCancel(ctx)
	defer cancel()

	succeedChan, failChan := make(chan struct{}, 1), make(chan struct{}, 1)

	// Start processing all active clauses
	// This initiates the core inference process through factoring and resolution
	for _, c := range s.activeSet.snapshot() {
		s.processNewClause(ctx, succeedChan, c)
	}

	// The given-clause loop. Every producer of a passive clause runs inside
	// processNewClause and returns before it does, so a selection that finds
	// nothing means the search is saturated: no clause arrives later. The
	// loop then waits for the cache checks it started, which can still
	// commit a proof, seals the passive set, and reports the outcome.
	cacheChecks := &sync.WaitGroup{}
	wg.Go(s.fault.guard(func() {
		defer cacheChecks.Wait()
		for ctx.Err() == nil {
			c := s.selectNewClause(ctx)
			if c == nil {
				cacheChecks.Wait()
				if s.isRefuted() {
					utils.TrySend(succeedChan, struct{}{})
				} else if ctx.Err() == nil {
					s.passiveSet.seal()
					utils.TrySend(failChan, struct{}{})
				}
				return
			}
			cacheChecks.Go(s.fault.guard(func() { s.checkCache(ctx, succeedChan) }))
			if c.Divisible() {
				division := c.Division()
				if !s.divisionHasExistingClause(division) {
					switch s.divideConquer(ctx, division) {
					case succeed:
						utils.TrySend(succeedChan, struct{}{})
					case fail:
						utils.TrySend(failChan, struct{}{})
					}
					return
				}
				// A divided clause already exists and subsumes c.
				s.retire(c)
			} else {
				s.processNewClause(ctx, succeedChan, c)
			}
			if s.isRefuted() {
				utils.TrySend(succeedChan, struct{}{})
				return
			}
		}
	}))

	// Wait for one of three outcomes:
	// 1. Context cancellation (timeout or external cancellation)
	// 2. Failure signal (search space exhausted)
	// 3. Success signal (refutation found)
	select {
	case <-ctx.Done():
		return cancelled

	case <-failChan:
		return fail

	case <-succeedChan:
		return succeed
	}
}

// divisionHasExistingClause reports whether a proposed branch clause already
// belongs to this state. In particular, initial-clause identity outlives
// passive-set membership: cleanup may retire an initial clause from the
// passive list, but divideConquer must never reclassify it as an assumption.
func (s *_RefuteState) divisionHasExistingClause(
	division *clause.ClauseDivision,
) bool {
	return utils.Any(division.DividedClauses, func(c *Clause) bool {
		return s.isInitClause(c) || s.passiveSet.has(c) || s.activeSet.has(c)
	})
}

// refutesByRewrite returns the refutation Simplifies finds between two
// clauses — one rewriting the other to ⊥ (Clause.RefutesByRewrite) — or
// nil. Contradicts finds a refutation by unifying two literals; this finds
// the one a unit equation gives by rewriting, which is how the pointwise
// unit a function equation normalizes to reaches an argument occurrence
// of the function (EqRewrite reads λx. f(x) as f). cleanUpRecords finds
// it for a derived clause on entry; refuteStateFromCNF and divideConquer
// apply it to the clauses a search starts from, so a given or assumed
// clause closes a goal a derived one closes. Nothing is retired or added:
// a rewrite that does not refute is left to the search.
func refutesByRewrite(c0, c1 *Clause) *ClauseThm {
	if u := c0.RefutesByRewrite(c1); u != nil {
		return u
	}
	return c1.RefutesByRewrite(c0)
}

// findRefutesByRewrite runs refutesByRewrite between c and every clause
// of the passive set, in passive-set order, and returns the first
// refutation.
func (s *_RefuteState) findRefutesByRewrite(ctx context.Context, c *Clause) *ClauseThm {
	for _, ci := range s.passiveSet.snapshot() {
		if ctx.Err() != nil || s.isRefuted() {
			return nil
		}
		if t := refutesByRewrite(c, ci); t != nil {
			return t
		}
	}
	return nil
}

// retire marks c useless: it leaves the passive set, so it is never
// selected, and the active set, so it is no longer a resolution partner.
// A clause outside the active set is only marked.
func (s *_RefuteState) retire(c *Clause) {
	s.passiveSet.markUseless(c)
	s.activeSet.remove(c)
}

// Selects a useful new clause from the record and insert to the state.
// Returns the selected clause or nil if no useful clause is found.
// This function is critical for pruning the search space by focusing on promising clauses.
func (s *_RefuteState) selectNewClause(ctx context.Context) *Clause {
	if s.deductionRecords.empty() {
		return nil
	}
	// select from the useful clauses, which are already sorted.
	for _, c := range s.passiveSet.snapshot() {
		if s.isRefuted() || ctx.Err() != nil {
			break
		}
		// Non-equality clauses will create too many deduced clauses but mostly
		// not useful (non-equality are not as informative as equality).
		// So we don't add those to active set. Instead, they will be used
		// to check for contradictions.
		if c.IsNeq() {
			continue
		}
		if !s.activeSet.has(c) && s.activeSet.insert(c) {
			return c
		}
	}
	return nil
}

// Calculates factoring and resolving of the new clause w.r.t the existing clauses.
// This is where new clauses are generated through inference rules.
// Both operations are performed concurrently.
// This is the core of the proof search algorithm, where new knowledge is derived
// from existing clauses through logical inference operations.
func (s *_RefuteState) processNewClause(
	ctx context.Context,
	succeedChan chan<- struct{},
	newClause *Clause) {

	if s.isRefuted() {
		return
	}

	wg := &sync.WaitGroup{}
	defer wg.Wait()

	// Launch factoring operation in the background
	// Factoring combines compatible literals within the same clause
	s.factor(ctx, succeedChan, wg, newClause)

	// Launch resolution operation in the background
	// Resolution combines compatible literals between different clauses
	s.resolve(
		ctx, succeedChan, wg, newClause, s.activeSet.snapshot())
}

// Implements divide and conquer strategy using a divisible clause.
// Creates multiple sub-problems by dividing the original problem,
// solves them independently, and then merges the results.
func (s *_RefuteState) divideConquer(
	ctx context.Context,
	division *clause.ClauseDivision) _RefuteStatus {

	// Create sub-states for each divided clause
	states := make([]*_RefuteState, len(division.DividedClauses))
	wg := &sync.WaitGroup{}

	// Process each divided clause in parallel
	for i, newClause := range division.DividedClauses {
		wg.Go(s.fault.guard(func() {
			contradict := s.findContradicts(newClause)

			// Clone active clauses for the sub-state
			activeSet := s.activeSet.clone()
			activeSet.insert(newClause)

			// Create a new refutation state for this sub-problem
			states[i] = newRefuteState(
				&s.groundVars,     // no clone, same across sub states
				s.origInitClauses, // no clone, same across sub states
				maps.Clone(s.assumptionClauses),
				activeSet,
				s.passiveSet.clone(),
				s.deductionRecords.clone(),
				s.attemptRecords.clone(),
				s.cache,   // no clone, same across sub states
				s.whistle, // no clone, same across sub states
				s.fault,   // no clone, same across sub states
			)
			// Add the new clause as an assumption in this sub-state
			states[i].passiveSet.add(newClause)
			states[i].assumptionClauses[newClause.Key()] = newClause

			// Check if the new clause immediately leads to a contradiction
			if refutedThm := <-contradict; refutedThm != nil {
				// Mark the sub-state as refuted if contradiction found
				states[i].setProof(makeDeduceStep(refutedThm))
				return
			}
			// The assumed clause meets the rewrite check a derived clause
			// meets in cleanUpRecords.
			if t := states[i].findRefutesByRewrite(ctx, newClause); t != nil {
				states[i].setProof(makeDeduceStep(t))
			}
		}))
	}
	wg.Wait()
	// A sub-state whose goroutine panicked may not exist: the search is
	// over, with the fault as its answer.
	if s.fault.recorded() != nil {
		return cancelled
	}

	// Merge the results from all sub-states
	return s.merge(ctx, division, states)
}

// Searches for contradictions between the given clause and existing clauses.
// Returns a channel that will receive the contradicting theorem if found.
// Uses parallel workers to check for contradictions efficiently. The pool
// is not waited for: a check can still be running when the search that
// queued it has returned, and its panic is then a late fault of the
// search's slot.
// Finding a contradiction is the ultimate goal of the refutation process,
// as it proves the negation of the original goal.
func (s *_RefuteState) findContradicts(c *Clause) <-chan *ClauseThm {
	result := make(chan *ClauseThm, 1)
	ctx, cancel := context.WithCancel(context.Background())
	_ = cancel // cancellation is signalled by the explicit cancel calls below

	// First check the cache for previously found contradictions
	if clauseThm := s.cache.loadContradict(c, c); clauseThm != nil {
		utils.TrySend(result, clauseThm)
		cancel()
	}

	pool := utils.NewWorkerPoolWithResChan(_CONTRADICT_WORKERS, result)

	// For unit clauses (single term), check for self-contradiction
	// This is a special case that can be checked directly
	if c.EffectiveNumLits() == 1 {
		pool.Go(s.fault.guard(func() {
			if clauseThm := c.SelfContradict(); clauseThm != nil {
				utils.TrySend(result, clauseThm)
				cancel()
				s.cache.storeContradict(c, c, clauseThm)
			}
		}))
	}

	// Collect all clauses that need to be checked for contradiction
	// This includes original init clauses and assumptions not in deduction records
	clauses := s.passiveSet.snapshot()
	for _, clause := range s.origInitClauses {
		if !s.deductionRecords.has(clause) {
			clauses = append(clauses, clause)
		}
	}
	for _, clause := range s.assumptionClauses {
		if !s.deductionRecords.has(clause) {
			clauses = append(clauses, clause)
		}
	}

	// Check for contradictions between the new clause and each existing clause
	for _, ci := range clauses {
		if clauseThm := s.cache.loadContradict(c, ci); clauseThm != nil {
			utils.TrySend(result, clauseThm)
			cancel()
		}

		// Skip contradiction checks for non-unit clauses
		// Unit clauses have better chances of finding direct contradictions
		if c.EffectiveNumLits() > 1 || ci.EffectiveNumLits() > 1 {
			continue
		}

		if ctx.Err() != nil {
			break
		}

		// Add task to worker pool to check for contradiction
		pool.Go(s.fault.guard(func() {
			if clauseThm := c.Contradicts(ci); clauseThm != nil {
				utils.TrySend(result, clauseThm)
				cancel()
				s.cache.storeContradict(c, ci, clauseThm)
			}
		}))
	}
	// result channel will be closed when all work in the pool is done.
	pool.CloseAsync()
	return result
}

// Performs factoring operation on a clause.
// Factoring combines literals in a clause that can be unified.
// Given l and ~l being unifiable, returns a thm with form
// ∀...(... ∨ ¬(l = r) ∨ t(~l) ...) ⊢ ∀...(... ∨ ¬(l = r) ∨ t(r) ∨ ...)
// ∀...(... ∨ ¬l ∨ t(~l) ...) ⊢ ∀...(... ∨ ¬l ∨ t(⊤) ∨ ...)
// ∀...(... ∨ l ∨ t(~l) ...) ⊢ ∀...(... ∨ l ∨ t(⊥) ∨ ...)
func (s *_RefuteState) factor(
	ctx context.Context,
	succeedChan chan<- struct{},
	wg *sync.WaitGroup,
	c *Clause) {

	// Skip if we've already tried factoring this clause
	if s.attemptRecords.loadOrStoreFactor(c) {
		return
	}

	// Create a channel to receive factoring results
	results := make(chan *ClauseThm, _CLAUSE_DEDUCE_BUFFER_SIZE)

	// Launch factoring in a separate goroutine
	wg.Go(s.fault.guard(func() { c.Factor(ctx, results) }))

	// Process the results as they arrive
	for {
		select {
		case <-ctx.Done():
			return
		case result, ok := <-results:
			if !ok {
				return
			}

			// Process the newly derived clause theorem
			s.triageClauseThm(ctx, succeedChan, result)
		}
	}
}

// Performs resolution between the given clause and a set of clauses.
// Resolution combines two clauses that contain complementary literals
// to derive a new clause without those literals.
func (s *_RefuteState) resolve(
	ctx context.Context,
	succeedChan chan<- struct{},
	wg *sync.WaitGroup,
	c *Clause,
	clauses []*Clause) {

	resolve := func(c0, c1 *Clause) {
		// Skip resolution if clauses are equivalent or if we've tried this pair before
		if c0.Equivalent(c1) || s.attemptRecords.loadOrStoreResolve(c0, c1) {
			return
		}

		// Create a channel for receiving resolution results
		results := make(chan *ClauseThm, _CLAUSE_DEDUCE_BUFFER_SIZE)

		// Launch resolution in a separate goroutine
		wg.Go(s.fault.guard(func() { c0.Resolve(ctx, c1, results) }))

		// Process the results as they arrive
		for {
			select {
			case <-ctx.Done():
				return
			case result, ok := <-results:
				if !ok {
					return
				}

				// Process the newly derived clause theorem
				s.triageClauseThm(ctx, succeedChan, result)
			}
		}
	}

	// Try resolution between the new clause and each existing clause
	// We attempt resolution in both directions (c with ci and ci with c).
	// Bound the concurrent fan-out via a semaphore. The active set can
	// reach hundreds of clauses; spawning 2×len(active) goroutines on top
	// of inner Resolve fan-out produced tens of thousands of live
	// goroutines under 10× outer test concurrency, and the resulting
	// scheduling skew non-deterministically reordered clause arrivals
	// enough that the saturation occasionally drifted into a divergent
	// search trajectory and missed the contradiction within the deadline.
	sem := make(chan struct{}, _RESOLVE_FANOUT)
	for _, ci := range clauses {
		if ctx.Err() != nil {
			return
		}
		sem <- struct{}{}
		wg.Go(s.fault.guard(func() {
			defer func() { <-sem }()
			resolve(c, ci)
		}))
		sem <- struct{}{}
		wg.Go(s.fault.guard(func() {
			defer func() { <-sem }()
			resolve(ci, c)
		}))
	}
}

// merge combines the results from multiple sub-problems created by division.
// This function is the implementation of the "conquer" part in the divide-and-conquer approach.
// It takes:
//   - ctx: The context for cancellation and timeout control
//   - division: Information about how the original clause was divided
//   - states: The refutation states for each sub-problem
//
// The function:
//  1. Processes each sub-state to collect their refutation results
//  2. Checks if any sub-proof is independent of its divided clause. If so,
//     it can be used directly as a proof for the parent state.
//  3. Ensures all sub-problems were successfully refuted
//  4. Combines the theorems from all sub-problems to create a unified proof
//  5. Validates that the merged theorem only contains hypotheses from the current proof level
//
// Returns:
//   - succeed: All sub-problems were refuted and results merged successfully
//   - fail: At least one sub-problem could not be refuted
//   - cancelled: The process was cancelled before completion
func (s *_RefuteState) merge(
	ctx context.Context,
	division *clause.ClauseDivision,
	states []*_RefuteState) _RefuteStatus {

	thms := make([]*ClauseThm, len(states))
	results := make([]*_RefuteState, len(states))

	Assert(len(division.DividedClauses) == len(states))

	// Process each sub-state and collect its results
	// We don't run them concurrently as it will increase the number
	// of goroutines exponentially.
	for i, si := range states {
		if ctx.Err() != nil {
			return cancelled
		}
		if !si.isRefuted() {
			status := si.refute(ctx)
			if status == fail {
				return fail
			}
			if status == cancelled {
				// we don't return here because it's possible that the parent state
				// is directly proved by other divisions.
				continue
			}
		}

		refutedThm := si.refutedThm()
		for h := range refutedThm.HypClauseIter() {
			// Each hyp of the thm proved by a sub state should satisfy
			// one of the following:
			// a) it's in the deduction steps of the parent state
			// b) it's in the inital clauses of the parent state
			// c) it's the respective divided clause.
			Assert(
				s.deductionRecords.has(h) ||
					s.isInitClause(h) ||
					h.Equivalent(division.DividedClauses[i]))
		}

		// Check if the theorem is independent of the division
		// If the subproof doesn't depend on the divided clause,
		// we can use it directly as a proof for the parent state
		if !refutedThm.HasHypClause(division.DividedClauses[i]) {
			Assert(si.proof != nil)
			if s.setProof(makeProofCache(si.proof)) {
				return succeed
			}
			// The builder panicked on the reuse: the search is stopping
			// (setProof), and what follows runs out on its cancelled context.
		}
		thms[i] = refutedThm
		results[i] = si
	}

	// Ensure all subproblems were successfully refuted
	// If any subproblem wasn't solved, we can't complete the proof
	for i := range division.DividedClauses {
		if results[i] == nil {
			return cancelled
		}
		Assert(results[i].isRefuted())
	}

	// Combine the theorems from all subproblems
	clauseThm := division.Merge(thms)

	// Now merge thm should only contain hyps that come from this level of proof.
	for h := range clauseThm.HypClauseIter() {
		Assert(s.deductionRecords.has(h) || s.isInitClause(h))
	}
	// A builder panic on the merge step committed nothing: the search is
	// stopping (setProof), so the status is the cancelled search's.
	if s.setProof(makeMergeStep(clauseThm, division, states)) {
		return succeed
	}
	return cancelled
}

// Processes a new clause theorem by either:
// 1. Setting it as the proof if it's a refutation
// 2. Adding it to the deduction record for further processing
// Also caches contradictions for future use.
// This is a critical routing function that determines how each derived clause is handled.
func (s *_RefuteState) triageClauseThm(
	ctx context.Context,
	succeedChan chan<- struct{},
	clauseThm *ClauseThm) {

	if clauseThm.IsRefuted() {
		// If the theorem represents a refutation (contradiction found),
		// cache it based on number of hypotheses for future use
		if clauseThm.NumHyps() == 1 {
			s.cache.storeContradict(
				clauseThm.HypClause(0), clauseThm.HypClause(0), clauseThm)
		} else if clauseThm.NumHyps() == 2 {
			s.cache.storeContradict(
				clauseThm.HypClause(0), clauseThm.HypClause(1), clauseThm)
		}
		select {
		case <-ctx.Done():
			return
		default:
			// Set the contradiction as our proof and signal success. Only
			// signal if the proof actually committed: setProof returns false
			// when the builder panicked, and the search is then stopping.
			if s.setProof(makeDeduceStep(clauseThm)) {
				utils.TrySend(succeedChan, struct{}{})
			}
		}
	} else {
		// If not a refutation, add to the record for further processing
		select {
		case <-ctx.Done():
			return
		default:
			s.addToRecord(ctx, clauseThm)
			if s.isRefuted() {
				utils.TrySend(succeedChan, struct{}{})
				return
			}
		}
	}
}

// deriveInitFunext runs the FUNEXT enrichment over the ORIGINAL initial
// clauses (see ext/clause/funext.go): unit ∀-equality clauses contract to
// their function-level equality; complementary pointwise implication pairs
// (the FunEqRewrite+IffToOr residue of a set-typed equality hypothesis)
// recombine and contract likewise. Each derivation enters the record as an
// ordinary derived clause (recipe rule FUNEXT), immediately usable by the
// unit-equality Simplifies paramodulation.
//
// Called exactly once per refuter (before the search and before any
// divide-and-conquer cloning). Deterministic: clauses are visited in
// CompareClauses order; the builders are search-free. The initial clause
// set is NOT modified — RefuteProp() and the cnf_proofs cache key are
// byte-identical to the pre-FUNEXT pipeline, so existing stored
// certificates and their cache rows are unaffected.
func (s *_RefuteState) deriveInitFunext(ctx context.Context) {
	inits := make([]*Clause, 0, len(s.origInitClauses))
	for _, c := range s.origInitClauses {
		inits = append(inits, c)
	}
	slices.SortStableFunc(inits, clause.CompareClauses)

	// The enrichment records the fully contracted equalities
	// (LambdaFreeEqSides) and the naming equalities — a λ-sided equality
	// whose other side is a variable the value does not mention,
	// `e = λx. T(x)`, the hypothesis that names a function value
	// (NamingEqSides): the pointwise clause reaches
	// e through its applications alone, and e as an argument of an opaque
	// head is unreachable without the equality. A constant against a λ,
	// a vocabulary constant's definition (the set driver's residence rule
	// contracted), is not recorded: as a unit equality it would unfold
	// the constant wherever the search spells it. The other partially
	// contracted (λ-sided) equalities funextContract produces are left to
	// the nested alpha-bridge chain (ext/clause/alpha_bridge.go) —
	// recording them here would add inert clauses to every search that
	// has a pointwise pair.
	recorded := func(c *clause.Clause) bool {
		return clause.LambdaFreeEqSides(c) || clause.NamingEqSides(c)
	}
	for _, c := range inits {
		if ctx.Err() != nil || s.isRefuted() {
			return
		}
		if thm := clause.FunextFromUnitEq(c); thm != nil && recorded(thm.ConclClause()) {
			s.addToRecord(ctx, thm)
		}
	}
	for i, c0 := range inits {
		for _, c1 := range inits[i+1:] {
			if ctx.Err() != nil || s.isRefuted() {
				return
			}
			// FunextFromIffPair's complementarity check is symmetric in
			// its arguments, so each unordered pair is tried once.
			if thm := clause.FunextFromIffPair(c0, c1); thm != nil && recorded(thm.ConclClause()) {
				s.addToRecord(ctx, thm)
			}
		}
	}
}

// deriveInitAlphaMerge runs the ALPHA-MERGE enrichment over the ORIGINAL
// initial clauses (see ext/clause/alpha_merge.go): α-duplicated
// Skolem-abstraction symbol pairs (the same ∃-under-λ body denoted apart
// across sibling hyps — the `H, ¬H ⊢ ⊥` CNF bug) are equated via a chain of
// ≤2-hyp derived steps reusing existing recipe rules (resolve ×2 + FUNEXT
// recombine + Simplifies twins), and each step enters the record as an
// ordinary derived clause. The twins restore first-order reachability of
// the duplicated symbols, so findContradicts (inside addToRecord) closes
// the complementary pair during init, search-free.
//
// Called exactly once per refuter, right after deriveInitFunext (before the
// search and before divide-and-conquer cloning). Deterministic: clauses are
// visited in CompareClauses order and the chain builders are search-free.
// The initial clause set — and hence RefuteProp() and the cnf_proofs cache
// key — is untouched.
func (s *_RefuteState) deriveInitAlphaMerge(ctx context.Context) {
	inits := make([]*Clause, 0, len(s.origInitClauses))
	for _, c := range s.origInitClauses {
		inits = append(inits, c)
	}
	slices.SortStableFunc(inits, clause.CompareClauses)
	known := func(h *Clause) bool {
		return s.deductionRecords.has(h) || s.isInitClause(h)
	}
	for _, thm := range clause.DeriveAlphaMergeChain(inits) {
		if ctx.Err() != nil || s.isRefuted() {
			return
		}
		// A multi-step direction chain derives through intermediate
		// clauses; one the whistle dropped leaves the steps over it with
		// nothing to derive from, and they are skipped (the pair then
		// stays unmerged, as without the chain).
		if !thm.AllHypClause(known) {
			continue
		}
		s.addToRecord(ctx, thm)
	}
}

// Adds a new clause theorem to the deduction record if it passes various checks.
// Also checks if the new clause leads to a contradiction with existing clauses.
// Skips clauses that are too large, already exist, or would create cycles.
// This function implements several pruning strategies to manage the growth of the search space.
func (s *_RefuteState) addToRecord(ctx context.Context, clauseThm *ClauseThm) {
	if s.isRefuted() {
		return
	}
	Assert(!clauseThm.IsRefuted())

	newClause := clauseThm.ConclClause()

	// Skip adding the clause in various situations that would lead to inefficiency or cycles
	if ctx.Err() != nil ||
		s.isInitClause(newClause) ||
		s.deductionRecords.has(newClause) ||
		// One hyp has the same key as the conclusion
		// this will cause self cycle in the records.
		clauseThm.HasHypClause(newClause) ||
		// Growth-chain divergence throttle + policy-sized cap
		// (replaces the flat _CLAUSE_SIZE_LIMIT gate; see
		// clause_whistle.go).
		s.whistle.Rejects(clauseThm, newClause) {
		return
	}

	// Verify that all hypotheses are from known sources
	for h := range clauseThm.HypClauseIter() {
		Assert(s.deductionRecords.has(h) || s.isInitClause(h))
	}
	// Ensure the clause body has no unbound variables
	Assert(newClause.Term().AllFree(s.groundVars.Has))

	// Check if the new clause leads to a contradiction with existing clauses
	contradict := s.findContradicts(newClause)

	// Add the clause to the deduction records if it passes all checks
	if s.deductionRecords.write(clauseThm) {
		s.passiveSet.add(newClause)
		// A naming equality (ext/clause, NamingEqSides) derived by FUNEXT
		// stands beside its pointwise source: the two are one fact in
		// two spellings, and each rewrites where the other cannot — the
		// pointwise clause an application of the name, the equality the
		// value where it stands as an argument — so neither retires the
		// other as redundant. A λ-free derivation replaces its sources,
		// since it rewrites in both positions.
		var kept []*Clause
		if clause.NamingEqSides(newClause) {
			kept = clauseThm.FunextSources()
		}
		// We don't concurrently run this because that will
		// add too many goroutines and caused jam.
		s.cleanUpRecords(ctx, newClause, kept)
	}
	// If a contradiction is found, set it as the proof
	if refutedThm := <-contradict; refutedThm != nil {
		s.setProof(makeDeduceStep(refutedThm))
	}
}

// Checks the cached proof to see if any of the stored proofs can be applied
// with the current set of active clauses and deduction records.
// This is an optimization to avoid redoing work that has already been done.
// The cache acts as a memory of previously discovered proofs and contradictions,
// allowing the system to reuse results of previous searches.
func (s *_RefuteState) checkCache(ctx context.Context, succeedChan chan<- struct{}) {
	if s.isRefuted() {
		return
	}
	// Iterate through all cached proofs to see if any can be directly applied
	for _, p := range s.cache.proof.Range {
		if ctx.Err() != nil {
			return
		}
		clauseThm := p.ClauseThm()
		if clauseThm == nil {
			// Invalid/in-progress DAGs must never be published, but keep cache
			// reads defensive so one bad entry cannot crash a worker goroutine.
			continue
		}
		// Check if all hypotheses of the cached proof are satisfied by current clauses
		if clauseThm.AllHypClause(
			utils.Disjunct(s.isInitClause, s.deductionRecords.has)) {
			// If so, we can reuse this proof. setProof returns false if the
			// cross-context reconstruction panicked: the search is then
			// stopping, and the loop runs out on its cancelled context.
			if s.setProof(makeProofCache(p)) {
				utils.TrySend(succeedChan, struct{}{})
				return
			}
		}
	}
}

// Optimizes the deduction records by removing redundant or subsumed clauses.
// This is important for efficiency as it prevents the search space from growing too large.
// Uses various simplification techniques like subsumption and simplification.
// The function implements two key space reduction techniques:
// 1. Subsumption: A clause subsumes another if it is more general
// 2. Simplification: A clause can sometimes simplify another through resolution
//
// kept are the clauses newClause neither retires nor is retired by: the
// sources of a FUNEXT naming derivation (addToRecord), which spell the
// same fact in the form that rewrites the positions newClause cannot.
func (s *_RefuteState) cleanUpRecords(ctx context.Context, newClause *Clause, kept []*Clause) {
	// Skip if the clause is already marked as useless
	if s.passiveSet.checkUselessness(newClause) {
		return
	}

	wg := sync.WaitGroup{}
	defer wg.Wait()
	// Check against all useful clauses for potential optimizations
	for _, clause := range s.passiveSet.snapshot() {
		if ctx.Err() != nil {
			return
		}
		if slices.ContainsFunc(kept, func(k *Clause) bool { return k.Key() == clause.Key() }) {
			continue
		}

		// If an existing clause subsumes the new one, mark new as useless
		if clause.TriviallySubsumes(newClause) {
			s.retire(newClause)
			return
		} else if u := clause.Simplifies(newClause); u != nil {
			// If an existing clause can simplify the new one
			s.retire(newClause)
			if u.IsRefuted() {
				// If simplification leads to a refutation, set it as the proof
				s.setProof(makeDeduceStep(u))
			} else if !u.Conclusion().Equals(ext.T) {
				// If simplification leads to something useful, add it to records
				wg.Go(s.fault.guard(func() { s.addToRecord(ctx, u) }))
			}
			return
		}

		// If the new clause subsumes an existing one, mark existing as useless
		if newClause.TriviallySubsumes(clause) {
			s.retire(clause)
		} else if u := newClause.Simplifies(clause); u != nil {
			// If new clause can simplify an existing one
			s.retire(clause)
			if u.IsRefuted() {
				// If simplification leads to a refutation, set it as the proof
				s.setProof(makeDeduceStep(u))
				return
			} else if !u.Conclusion().Equals(ext.T) {
				// If simplification leads to something useful, add it to records
				wg.Go(s.fault.guard(func() { s.addToRecord(ctx, u) }))
			}
		}
	}
}
