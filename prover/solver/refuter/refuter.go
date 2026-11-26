/**
 * File: refuter.go
 *
 * Defines the main refuter interface and state management for theorem proving.
 *
 * Key structures:
 * - _Refuter: Primary interface for creating and managing refutation proofs
 *   Fields:
 *   - goal: The proposition to be proved
 *   - cnf: CNF (Conjunctive Normal Form) clauses to be refuted
 *   - reconstruct: Function to convert CNF refutation to original goal proof
 *   - provedThm: Resulting theorem when proof is complete
 *   - refutedCNFClauseThm: Refutation in CNF form
 *
 * - _RefuteState: State management for the refutation process
 *   Fields:
 *   - groundVars: Variables that cannot be instantiated
 *   - origInitClauses: Original clauses from the problem
 *   - assumptionClauses: Clauses assumed from parent divisions
 *   - activeSet: Clauses currently being processed
 *   - passiveSet: Clauses that are waiting to be processed
 *   - deductionRecords: Record of inference steps
 *   - attemptRecords: Record of attempted operations
 *   - cache: Shared proof cache
 *   - proof: Resulting proof structure when refutation succeeds
 *
 * Main functions:
 * - CreateRefuter(goal, cnfNormalizationCache): Creates a new refuter for a goal
 * - (p *_Refuter) Prove(ctx): Performs the refutation and returns a proof
 * - (p *_Refuter) refute(ctx): Core refutation function that manages the process
 * - refuteStateFromCNF(cnf): Creates initial refutation state from CNF clauses
 *
 * Utility functions:
 * - Various methods for checking clause properties and state management
 */

// Package refuter is the refutation prover for propositional and
// equational logic: it takes the negation of a goal to conjunctive
// normal form and saturates the clauses until they contradict,
// returning the goal as a kernel theorem.
//
// CreateRefuter builds the clause set (ext/clause) and Prove runs the
// given-clause loop over it: an active set and a passive set, with the
// deduction rules of ext/clause between them. A refutation is turned
// back into a proof of the goal as it was stated; a search that finds
// none within its budget fails, and says nothing about the goal. A
// clause whose literals fall into independent components divides the
// problem: the search splits into sub-problems on it, and their
// refutations are merged. Like
// every solver under prover/solver it sits below the proof calculus: it
// is handed a goal, returns a certificate, and never touches the goal
// stack.
package refuter

import (
	"context"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/ext/clause"
	"github.com/euc-ai/xugo/ext/prop"
	"github.com/euc-ai/xugo/utils"
)

type _Refuter struct {
	// {h...} ⊢ c
	goal Prop

	// cnf information
	cnfResult *clause.NegateGoalCNFResult

	// If filled, it's proved and nothing needs to be done.
	provedThm Thm

	// The refuted cnf, only filled after refuted.
	// This is in the form of {clauses} ⊢ ⊥ and usually different from the proved thm.
	// The proved thm can be reconstructed from this.
	refutedCNFClauseThm *ClauseThm

	// The normal form of the CNF's refute prop and the lift of a proof of
	// it to a proof of the refute prop, once KeyForm has computed them.
	keyForm     Prop
	liftKeyForm utils.EndoFunc[Prop]
}

// CreateRefuter builds a refuter via the full (raw-input) CNF pipeline.
//
// ctx is threaded into clause.NegateGoalCNF, which honors it at the coarse
// per-hyp boundaries. Pass context.Background() at non-agent call sites.
func CreateRefuter(ctx context.Context, goal Prop, cnfNormalizationCache *ext.TermKeyPropMap) *_Refuter {
	return buildRefuter(goal, func() (*clause.NegateGoalCNFResult, error) {
		return clause.NegateGoalCNF(ctx, goal, cnfNormalizationCache)
	})
}

// CreateRefuterFromPreNormalized is the prelude-split variant of CreateRefuter.
// Per-hypothesis CNF preprocessing uses the prelude/middle/tail-split pipeline
// with a two-level cache. cache may be nil to disable caching.
//
// ctx is threaded into clause.NegateGoalCNFFromPreNormalized so that the
// agent's budget_ms (passed through probe / apply via the CnfRefuterTimeout
// ctx-value override and the parent deadline) caps pre-CNF preprocessing
// too — not just the downstream Prove(ctx) call. Pass context.Background()
// at non-agent call sites; behaviour matches the pre-ctx signature.
//
// See clause.NegateGoalCNFFromPreNormalized for the underlying split.
func CreateRefuterFromPreNormalized(
	ctx context.Context,
	goal Prop,
	cache *clause.CNFNormalizeCache,
) *_Refuter {
	return buildRefuter(goal, func() (*clause.NegateGoalCNFResult, error) {
		return clause.NegateGoalCNFFromPreNormalized(ctx, goal, cache)
	})
}

func buildRefuter(
	goal Prop,
	negateGoal func() (*clause.NegateGoalCNFResult, error),
) *_Refuter {
	var provedThm Thm
	result, err := negateGoal()
	if err != nil {
		// Failure modes: prelude budget exhausted on a large goal, CNF
		// normalization timeout, malformed input. All callers (production
		// step.go:1036, prover.go cache wrappers) treat a nil refuter as
		// "couldn't build, give up cleanly"; the methods below tolerate a
		// nil receiver for the same reason, so an unchecked-nil caller
		// degrades to "not refuted / nothing to prove" instead of SIGSEGV.
		return nil
	}
	if !result.Thm.IsZero() {
		Assert(prop.IsStronger(result.Thm, goal))
		provedThm = result.Thm
	}
	return &_Refuter{
		goal:      goal,
		cnfResult: result,
		provedThm: provedThm,
	}
}

func (r *_Refuter) CNF() *clause.CNFClauses {
	if r == nil {
		return nil
	}
	return r.cnfResult.CNF
}

func (r *_Refuter) Refuted() bool {
	if r == nil {
		return false
	}
	return !r.provedThm.IsZero()
}

func (r *_Refuter) ProvedThm() Thm {
	if r == nil {
		return Thm{}
	}
	return r.provedThm
}

// KeyForm is the normal form of r's refute prop: the proposition a
// certificate of r's goal is stored under, by its key. The form is a run
// of seconds on a wide leaf (PreCNFCache.NormalizeUntil, which ctx cuts),
// so r computes it once and keeps it with its lift: the reading of a
// stored certificate that needs the form (ReconstructStoredProof) reads
// what the lookup of its key computed, where asking the cache again
// would hand back the form and run the whole normalization a second time
// for the lift.
func (r *_Refuter) KeyForm(ctx context.Context, cache *clause.CNFNormalizeCache) Prop {
	if r.keyForm == nil {
		r.keyForm, r.liftKeyForm = cache.PreCNF.NormalizeUntil(ctx, r.CNF().RefuteProp())
	}
	return r.keyForm
}

func (r *_Refuter) Reconstruct(prop Prop) Prop {
	if r == nil {
		return nil
	}
	return r.cnfResult.Reconstruct(prop)
}

func (r *_Refuter) Prove(ctx context.Context) *CNFRefuteProofProto {
	if r == nil {
		return nil
	}
	if state := r.refute(ctx); state != nil {
		// Store the cache-representative restatement of the goal (SelfConsistentGoal,
		// alpha-equal to r.goal) rather than the raw input: it normalizes with a
		// fresh cache to exactly the refutation cert below, so the stored proof
		// is self-consistent (front ↔ cert) independent of cnfNormalizeCache
		// warming order. refute() returns non-nil only on the normal refutation
		// path, where SelfConsistentGoal is always set. (See NegateGoalCNFResult.SelfConsistentGoal
		// and step.go's reconstruction, which normalizes the stored goal with
		// a fresh cache so replay is cache-order-independent.)
		goal := r.cnfResult.SelfConsistentGoal
		Assert(goal != nil)
		// SelfConsistentGoal must be a faithful (alpha-equal) restatement of the
		// proved goal — only its bound-variable naming differs. If this ever
		// fails, storing it would change what the proof claims.
		Assert(r.goal.AlphaEquals(goal))
		// The proto's two halves are self-consistent BY CONSTRUCTION:
		//   - Root cert (refutedCNFClauseThm, {used clauses} ⊢ ⊥) refutes a
		//     subset of the goal's CNF clauses (the Assert below);
		//   - SelfConsistentGoal's hyps are Lhs(cnfHyps[i]) — the exact form
		//     the warm pipeline normalized — and the name-faithful cache guards
		//     in clause.NegateGoalCNF* guarantee that re-normalizing each such
		//     Lhs with a fresh cache reproduces cnfHyps[i] verbatim.
		// So a cold renormalization at replay time recovers the same CNF the
		// cert refutes. A previous "write gate" actually re-ran the cold
		// normalization here as a backstop, but the check duplicates the
		// pipeline run, and its 500ms _CNF_REWRITE_TIMEOUT made it produce
		// false negatives under CPU contention that then dropped good rows.
		// A timeout failure carries no information about correctness (same
		// program, different wall clock), so the check was both expensive and
		// useless. Source-side guards are the single source of truth; if they
		// have a hole, the right place for that to surface is at replay
		// (ReconstructStoredProof returns nil → RequireCNFCacheHit panic),
		// not as a silently-dropped row here.
		Assert(prop.IsStronger(r.refutedCNFClauseThm.Thm, r.cnfResult.CNF.RefuteProp()))
		pool := ext.NewPoolBuilder()
		goalRef := pool.PropRef(goal)
		root := proofStateProto(state, pool)
		return &CNFRefuteProofProto{
			Pool: pool.Pool(),
			Goal: goalRef,
			Root: root,
		}
	}
	return nil
}

// ReconstructStoredProof replays a stored CNF refute proof (the inverse of
// Prove) against THIS refuter — which must have been built from the goal the
// proof is for — and returns the reconstructed theorem, or nil if the stored
// proof no longer reproduces (stale clause inferences, a diverged goal, etc.).
// A stale recipe is recovered to nil, so a caller can tell a clean
// reconstruction failure from a key miss. A certificate is data read from a
// blob, and the reading reports one that no longer runs by a panic of its own
// or a failed assertion: the pool reader's, the clause inferences' and the
// reconstructor's checks of the recorded shape. An error of the Go runtime
// and a fault carried off another goroutine report no certificate: they are
// raised again.
func (r *_Refuter) ReconstructStoredProof(
	ctx context.Context,
	proof *CNFRefuteProofProto,
	cache *clause.CNFNormalizeCache,
	loadConstMeta ext.LoadConstMeta,
) (result Thm) {
	defer func() {
		if stale := recover(); stale != nil {
			if utils.IsFault(stale) && !utils.IsAssertionFailure(stale) {
				panic(stale)
			}
			result = Thm{}
		}
	}()
	return r.reconstructStoredProof(ctx, proof, cache, loadConstMeta)
}

// reconstructStoredProof is ReconstructStoredProof's reading of the stored
// proof, under no recover. A certificate that does not refute the stored
// goal's clauses, or a reconstruction that does not prove r's goal, is
// answered nil here; a panic is a recipe the pool reader or the clause
// inferences could not run, or a defect.
//
// The stored goal is normalized with a nil cache so the result is independent of
// cnfNormalizeCache warming order — the proof stores its goal in self-consistent
// form (see Prove). `cache` backs only the naming-canonical PreCNF normalization
// that carries a certificate recorded under other names to r.CNF(); a
// certificate of r's own clauses is read with no normalization at all.
func (r *_Refuter) reconstructStoredProof(
	ctx context.Context,
	proof *CNFRefuteProofProto,
	cache *clause.CNFNormalizeCache,
	loadConstMeta ext.LoadConstMeta,
) Thm {
	// The proof carries one shared pool; the reader rebuilds every clause/term
	// once, bottom-up, restoring structural sharing. Both the refutation cert
	// and the stored goal index into it.
	reader := ext.NewPoolReader(proof.Pool, loadConstMeta)
	clauseThm := ReconstructCNFProofNode(proof.Root, reader)
	if clauseThm == nil {
		return Thm{}
	}
	storedGoal, _ := reader.Prop(proof.Goal)
	if storedGoal == nil {
		return Thm{}
	}
	// Cache-free normalization deterministically reproduces the refutation cert.
	res, err := clause.NegateGoalCNFFromPreNormalized(ctx, storedGoal, nil)
	if err != nil {
		return Thm{}
	}
	// The certificate is of the stored goal where it refutes clauses the
	// goal's normal form gives; one that refutes another clause is stale.
	ofStoredGoal := prop.WeakenTo(clauseThm.Thm, res.CNF.RefuteProp())
	if ofStoredGoal == nil {
		return Thm{}
	}
	thm := ofStoredGoal.AsThmCert()
	if thm.IsZero() {
		return Thm{}
	}
	// The certificate refutes the clauses the stored goal's normal form
	// gives, under the stored goal's names; r's clauses are the same goal's
	// under the names this run gave them. Where the two sets are one up to
	// α the certificate is already a refutation of r's clauses. Where they
	// are not — a certificate another spelling of the leaf recorded — both
	// sides go through the naming-canonical normal form the key is
	// computed from: the certificate is normalized, compared with r's key
	// form, and lifted to r's clauses by the lift of that form.
	reconstructedCNF := thm
	if !prop.IsStronger(thm, r.CNF().RefuteProp()) {
		// The form is the lookup's where a lookup of the key preceded this
		// reading; a reading with none computes it here, uncut.
		normalizedCNFProp := r.KeyForm(context.Background(), cache)
		provedNormalizedCNFThm, _ := cache.PreCNF.Normalize(thm)
		if !normalizedCNFProp.AlphaEquals(provedNormalizedCNFThm) {
			return Thm{}
		}
		reconstructedCNF = r.liftKeyForm(provedNormalizedCNFThm).AsThmCert()
		if !prop.IsStronger(reconstructedCNF, r.CNF().RefuteProp()) {
			return Thm{}
		}
	}
	reconstructedThm := r.Reconstruct(
		prop.WeakenTo(reconstructedCNF, r.CNF().RefuteProp())).AsThmCert()
	if !prop.IsStronger(reconstructedThm, r.goal) {
		return Thm{}
	}
	return reconstructedThm
}

func (r *_Refuter) refute(ctx context.Context) *_RefuteState {
	if r.CNF() == nil || r.Refuted() {
		return nil
	}
	return r.search(ctx, r.initialState())
}

// initialState is the state a search over r's clauses starts from. Its
// construction checks the initial clauses against each other, the
// search's first step, so a panic in it is raised as the search's fault
// like one in search.
func (r *_Refuter) initialState() *_RefuteState {
	defer func() {
		if rec := recover(); rec != nil {
			panic(r.faultOf(rec))
		}
	}()
	return refuteStateFromCNF(r.CNF())
}

// faultOf is the search's fault for rec, a panic value recovered on the
// goroutine that asked for the search. It is called from the deferred
// function that recovered rec.
func (r *_Refuter) faultOf(rec any) SearchFault {
	return SearchFault{Fault: utils.RecoveredFault(rec), Goal: r.goal}
}

// search runs the refutation over s, a state over r's clauses, and keeps
// its result on r: the state when it refuted, nil when the search failed
// or was cut off. A panic on any goroutine of the search — this one, or
// one the search started (_FaultSlot.guard, setProof), which stops the
// search — is raised here, on the caller's goroutine, as a SearchFault
// in place of either answer. A panic of a contradiction check still
// running when the search returns goes to the reader the caller's
// context carries (WithLateFaultReport).
func (r *_Refuter) search(ctx context.Context, s *_RefuteState) *_RefuteState {
	caller := ctx
	ctx, stop := context.WithCancel(ctx)
	defer stop()
	s.fault.arm(stop, func(fault utils.Fault) {
		reportLateFault(caller, SearchFault{Fault: fault, Goal: r.goal})
	})
	defer func() {
		rec := recover()
		fault := s.fault.answer()
		switch {
		case rec != nil:
			panic(r.faultOf(rec))
		case fault != nil:
			panic(SearchFault{Fault: *fault, Goal: r.goal})
		}
	}()
	// The state's construction sets a proof for a contradiction among the
	// initial clauses, before the search is armed.
	if s.fault.recorded() != nil {
		return nil
	}
	// FUNEXT enrichment (see ext/clause/funext.go): derive function-typed
	// equality clauses from their pointwise initial-clause forms, so
	// unit-equality Simplifies can paramodulate them into argument
	// positions of opaque heads (the set_tac gap). Runs ONCE here, before
	// the search (and before any divide-and-conquer cloning, so sub-states
	// inherit the derived clauses); the initial clause set — and hence
	// RefuteProp() and the cnf_proofs cache key — is untouched.
	s.deriveInitFunext(ctx)
	// ALPHA-MERGE enrichment (see ext/clause/alpha_merge.go): equate
	// α-duplicated Skolem-abstraction symbols (the same ∃-under-λ body
	// denoted apart across sibling hyps) and enter their rewritten twins,
	// so the H, ¬H ⊢ ⊥ class closes at init. Same contract as FUNEXT
	// above: derivations only, initial clause set and cache keys untouched.
	s.deriveInitAlphaMerge(ctx)
	status := s.refute(ctx)
	if s.fault.recorded() != nil {
		return nil
	}

	if status == succeed {
		Assert(s.isRefuted())
		Assert(prop.IsStronger(s.refutedThm().Thm, r.CNF().RefuteProp()))
		provedThm := r.Reconstruct(s.refutedThm().Thm).AsThmCert()
		Assert(prop.IsStronger(provedThm, r.goal))
		r.refutedCNFClauseThm = s.refutedThm()
		r.provedThm = provedThm
		return s
	}
	return nil
}

type _RefuteState struct {
	// Not modified after construction, so no mutex protection.
	// When sub env is created, this is shared and never changed.
	groundVars ext.VarList

	// the original initial clauses for the whole problem.
	// identical across all sub problems
	// Not modified after construction, so no mutex protection.
	// When sub env is created, this is shared and never changed.
	// isOrigInitClause / isInitClause methods are preferred than directly accessing this.
	origInitClauses ClauseMap

	// the assumed divided clauses coming from the upper level
	// Not shared with children envs, every new env creates its own.
	assumptionClauses ClauseMap

	// the current active clauses that need to be factored / resolved.
	activeSet *_ActiveSet

	// the passive clauses set
	// the given clauses are chosen from this set.
	passiveSet *_PassiveSet

	// records of every steps of the deduction
	// stored by the key of the conclusion clause
	// when sub env is created, the record is cloned and the new env will amend its own.
	deductionRecords *_DeductionRecords

	// record of factor or resolve attempts.
	// not storing any real content, just "this has been tried before".
	// when sub env is created, the record is cloned and the new env will amend its own.
	attemptRecords *_AttemptRecords

	// when sub env is created, the cache is shared across the env and sub envs.
	cache *_RefuteCache

	// growth-chain divergence throttle for derived clauses; shared
	// across the env and sub envs like cache. See clause_whistle.go.
	whistle *_ClauseWhistle

	// the first panic among the search's goroutines, and the search's
	// stop; shared across the env and sub envs like cache. See
	// search_fault.go.
	fault *_FaultSlot

	// if filled, nothing needs to be done anymore.
	proof *_ProofDAG
}

func newRefuteState(
	groundVars *ext.VarList,
	origInitClauses, assumptionClauses ClauseMap,
	activeSet *_ActiveSet,
	passiveSet *_PassiveSet,
	deductionRecords *_DeductionRecords,
	attemptRecords *_AttemptRecords,
	cache *_RefuteCache,
	whistle *_ClauseWhistle,
	fault *_FaultSlot,
) *_RefuteState {
	return &_RefuteState{
		groundVars:        *groundVars,
		origInitClauses:   origInitClauses,
		assumptionClauses: assumptionClauses,
		activeSet:         activeSet,
		passiveSet:        passiveSet,
		deductionRecords:  deductionRecords,
		attemptRecords:    attemptRecords,
		cache:             cache,
		whistle:           whistle,
		fault:             fault,
		proof:             emptyProof(),
	}
}

func refuteStateFromCNF(cnf *clause.CNFClauses) *_RefuteState {
	activeClauses := &_ActiveSet{m: make(ClauseMap)}

	initClauses := cnf.ClausesMap()
	state := newRefuteState(
		cnf.GroundVars(),
		initClauses,
		make(ClauseMap),
		activeClauses,
		emptyPassiveSet(),
		emptyDeductRecord(),
		&_AttemptRecords{},
		&_RefuteCache{},
		newClauseWhistle(initClauses),
		&_FaultSlot{},
	)

	for _, ci := range cnf.Clauses() {
		Assert(ci.Term().AllFree(state.groundVars.Has))
		if state.activeSet.insert(ci) {
			if t := ci.SelfContradict(); t != nil {
				state.setProof(makeDeduceStep(t))
				state.cache.storeContradict(ci, ci, t)
				return state
			}
			for _, cj := range state.activeSet.snapshot() {
				if t := ci.Contradicts(cj); t != nil {
					state.setProof(makeDeduceStep(t))
					state.cache.storeContradict(ci, cj, t)
					return state
				}
				// The rewrite check a derived clause meets in
				// cleanUpRecords (refutesByRewrite).
				if t := refutesByRewrite(ci, cj); t != nil {
					state.setProof(makeDeduceStep(t))
					return state
				}
			}
		}
	}

	for _, c := range state.activeSet.snapshot() {
		state.passiveSet.add(c)
	}
	return state
}

func (s *_RefuteState) String() string {
	return clause.FormatConjunctiveClauses(
		&s.groundVars, s.activeSet.snapshot())
}

func (s *_RefuteState) refutedThm() *ClauseThm { return s.proof.ClauseThm() }

func (s *_RefuteState) isRefuted() bool { return s.proof.ClauseThm() != nil }

func (s *_RefuteState) isOrigInitClause(c *Clause) bool {
	_, ok := s.origInitClauses[c.Key()]
	return ok
}

func (s *_RefuteState) isAssumptionClause(c *Clause) bool {
	_, ok := s.assumptionClauses[c.Key()]
	return ok
}

func (s *_RefuteState) isInitClause(c *Clause) bool {
	return s.isOrigInitClause(c) || s.isAssumptionClause(c)
}

func (s *_RefuteState) findInitClause(c *Clause) *Clause {
	if clause, ok := s.origInitClauses[c.Key()]; ok {
		return clause
	}
	if clause, ok := s.assumptionClauses[c.Key()]; ok {
		return clause
	}
	return nil
}

// setProof sets the proof for this refutation state using the ProofBuilder.
//
// It returns true iff a proof is committed when it returns — either built by
// this call or already present from a concurrent call — and false iff the
// ProofBuilder panicked.
//
// A builder panic (an Assert inside it, such as the cross-context
// proof-cache-reuse invariant Assert(b.isInitClause(h)) in computeFinalThm)
// is recovered HERE rather than by the goroutine's guard, because the
// in-progress proof DAG is rolled back to empty under the lock it was built
// under, so the state is not left half-built. It is no proof attempt that
// "did not apply": the fault is recorded on the search's slot, which stops
// the search, and the search raises it on its caller's goroutine in place of
// an answer (_Refuter.search). Nothing the search found is trusted past the
// break.
func (s *_RefuteState) setProof(root _ProofNode) (committed bool) {
	// Clear active clauses since they're no longer needed once a proof is found
	s.activeSet.reset()

	s.proof.Lock()
	defer s.proof.Unlock()

	if s.proof.clauseThm != nil {
		return true
	}

	// Registered after the Unlock defer so it runs FIRST on a panic (LIFO):
	// the rollback mutates s.proof while still holding the write lock.
	defer func() {
		if rec := recover(); rec != nil {
			fault := utils.RecoveredFault(rec)
			s.proof.root = nil
			s.proof.clauseThm = nil
			clear(s.proof.nodeSet)
			committed = false
			s.fault.record(fault)
		}
	}()

	cxt := _ProofContext{
		isOrigInitClause:   s.isOrigInitClause,
		isAssumptionClause: s.isAssumptionClause,
		isInitClause:       s.isInitClause,
		findInitClause:     s.findInitClause,
		lookUpDeduceStep:   s.deductionRecords.lookup,
	}

	// Build the complete proof using ProofBuilder
	builder := newProofBuilder(cxt, s.proof)
	builder.build(root)

	if err := cxt.validate(s.proof); err != nil {
		panic("Proof validation failed: " + err.Error())
	}

	// Publish only a validated DAG. The cache shares this exact pointer with
	// sibling refutation states, so publishing before validation would let the
	// panic rollback above turn a live cache entry into a nil-ClauseThm DAG.
	s.cache.loadOrStoreProof(s.proof.clauseThm.AlphaKey(), s.proof)

	return true
}
