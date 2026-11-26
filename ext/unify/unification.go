/**
 * File: unification.go
 *
 * Implements higher-order unification algorithms based on Huet's approach.
 */

package unify

import (
	"context"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// Term unification without type unification.
func UnifyTerms(
	ctx context.Context,
	s, t Term, ground TermNamePredicate) []TermSubstsGroup {

	if s.AlphaEquals(t) {
		return []TermSubstsGroup{nil}
	}
	substs := Unify(ctx, s, t, utils.EmptyPredicate, ground)
	return utils.MapSlice(substs,
		func(t SubstsTuple) TermSubstsGroup { return t.TermSubsts })
}

// Higher-order unification algorithm by G. Huet.
// see G. Huet, Unification in typed lambda calculus, 1975.
// see also F. Huch, Higher Order Unification, 2020.

// The instantiableTypes arg means the var types that can be used for instantiation.
// The ground arg means the var terms that cannot be used for instantiation.
// This algorithm implements Huet's higher-order unification approach which:
// 1. First checks for trivial alpha-equivalence
// 2. Performs type unification
// 3. Handles flexible/rigid and flexible/flexible term pairs
// 4. Uses imitation and projection for finding substitutions
func Unify(
	ctx context.Context,
	s, t Term,
	instantiableTypes VarTypePredicate,
	ground TermNamePredicate) (result []SubstsTuple) {

	// BetaEtaNormalize (and helpers reached via it) panic with QuitSentinel
	// when ctx fires mid-normalize. Unwind the whole unify stack cleanly and
	// surface a nil result — identical to "unification failed" from the
	// caller's perspective, which is the right behavior on timeout.
	defer func() {
		if utils.RecoverQuit(recover()) {
			result = nil
		}
	}()

	if s.AlphaEquals(t) {
		return []SubstsTuple{{nil, nil}}
	}

	// Budget installation for callers that didn't set a deadline:
	//
	//   - Default: a deterministic work budget (_BudgetCtx). Every ctx
	//     poll — one β-η node visit or one search-loop check — consumes a
	//     unit; exhaustion reads as cancellation at all existing poll
	//     sites. The branches of the search are explored in a fixed
	//     order on this goroutine (see expandSearchTree /
	//     unifyAllFlexiblePairs), so this makes Unify a pure function of
	//     (s, t): same inputs, same result set, on any machine under any
	//     load. Record/replay of lemma steps depends on exactly this
	//     property.
	//
	//   - XUGO_UNIFY_WALLCLOCK=1: the DefaultUnifyTimeout wall-clock
	//     cap, an escape hatch and A-B knob.
	//
	// Callers that DID set a deadline (e.g. the CNF refuter's proveCtx)
	// run the same search in the same order, cut by their clock at its
	// next poll instead of by the budget.
	if _, ok := ctx.Deadline(); !ok {
		if useWallClock() {
			var cancel context.CancelFunc
			ctx, cancel = context.WithTimeout(ctx, DefaultUnifyTimeout)
			defer cancel()
		} else if !isBudgetCtx(ctx) {
			ctx = newBudgetCtx(ctx, unifyBudgetUnits())
		}
	}

	s0, t0 := s, t

	// the 2 terms are both β-η normalized.
	s, t = ext.BetaEtaNormalize(ctx, s), ext.BetaEtaNormalize(ctx, t)

	if s.AlphaEquals(t) {
		return []SubstsTuple{{nil, nil}}
	}

	// Type unification must happen before term unification
	typeSubsts, ok := unifyTypePair(s.Type(), t.Type(), instantiableTypes)
	if !ok {
		return nil
	}
	s = s.TypeSubstitute(typeSubsts...)
	t = t.TypeSubstitute(typeSubsts...)

	substs := SubstsTuple{typeSubsts, nil}
	if s.AlphaEquals(t) {
		return []SubstsTuple{substs}
	}

	// Cannot unify if both terms are ground and non-equivalent after type substitution
	grounded := func(v VarTerm) bool { return ground(v.Name()) }
	if !ext.TermAnyTypeVar(s, instantiableTypes) &&
		!ext.TermAnyTypeVar(t, instantiableTypes) &&
		s.AllFree(grounded) &&
		t.AllFree(grounded) {
		return nil
	}

	// Create environment for unification and start recursive process
	env := _UnifyEnv{s, t, instantiableTypes, ground, substsTooDeep(s, t)}
	substsTuples := env.tryUnify(
		ctx,
		[]_TermPair{makeBodyPair(s, t, &VarList{})},
		substs,
		utils.EmptySet[TermName]())

	// Clean up the final substitutions by removing unused variables
	for i, substs := range substsTuples {
		substsTuples[i].TermSubsts = cleanupSubsts(
			ctx,
			substs.TermSubsts,
			[]_TermPair{makeBodyPair(
				s.TypeSubstitute(substs.TypeSubsts...),
				t.TypeSubstitute(substs.TypeSubsts...),
				&VarList{})})
		Assert(ext.BetaEtaEquals(
			ctx,
			s0.TypeSubstitute(substs.TypeSubsts...).Substitute(substsTuples[i].TermSubsts...),
			t0.TypeSubstitute(substs.TypeSubsts...).Substitute(substsTuples[i].TermSubsts...)))
	}
	substsTuples = sortSubsts(substsTuples)
	if len(substsTuples) == 0 {
		// we don't return non-nil empty slice
		// as the caller might use " == nil" to check whether the unification fails.
		return nil
	}
	return substsTuples
}

// performs initial verification and name avoidance setup
func (env _UnifyEnv) preprocessPairs(
	pairs []_TermPair,
	substs SubstsTuple,
	avoidNames TermNameSet) TermNameSet {

	verifyPairs(pairs, substs)
	return avoidSubstsNames(avoidNames, pairs, nil)
}

// _UnifyEnv contains the environment for the unification process,
// including the original terms, allowed variable types for instantiation,
// ground variables that cannot be instantiated, and a function to detect
// when substitution search becomes too deep
type _UnifyEnv struct {
	origTerm0, origTerm1 Term
	allowedVarTypes      VarTypePredicate
	ground               TermNamePredicate
	tooDeep              func(TermSubstsGroup) bool
}

// processes the case where all pairs are flexible/flexible
func (env _UnifyEnv) handleAllFlexiblePairs(
	ctx context.Context,
	pairs []_TermPair,
	substs SubstsTuple,
	avoidNames TermNameSet) []SubstsTuple {

	allFlexibleSubstsGroups := unifyAllFlexiblePairs(env, ctx, pairs, avoidNames)
	if len(allFlexibleSubstsGroups) == 0 {
		return nil
	}
	substsTuples := make([]SubstsTuple, len(allFlexibleSubstsGroups))
	for i, allFlexibleSubsts := range allFlexibleSubstsGroups {
		substsTuples[i].TypeSubsts = substs.TypeSubsts
		substsTuples[i].TermSubsts, _ = insertOrderedTermSubsts(
			ctx, substs.TermSubsts.Clone(), allFlexibleSubsts...)
	}
	return substsTuples
}

// finds all possible substitutions for flexible/rigid pairs
func (env _UnifyEnv) findFlexibleRigidSubstitutions(
	ctx context.Context,
	pairs []_TermPair,
	substs SubstsTuple,
	avoidNames TermNameSet) (*SubstsTuple, []SubstsTuple) {

	var singleSubst *SubstsTuple
	var newSubsts []SubstsTuple

	avoidNames = avoidSubstsNames(avoidNames, pairs, substs.TermSubsts)

	for i := range pairs {
		_, _, isRigid0 := decomposeHead(pairs[i].t0, &pairs[i].boundVars, env.ground)
		_, _, isRigid1 := decomposeHead(pairs[i].t1, &pairs[i].boundVars, env.ground)
		Assert(!isRigid0)
		if !isRigid1 {
			// a flexible/flexible pair.
			continue
		}
		Assert(!pairs[i].t0.AlphaEquals(pairs[i].t1))
		// a flexible/rigid pair, find all available substitutions.
		matchResults := matchFlexibleRigid(
			ctx, &pairs[i], avoidNames, env,
			!rhsFreeMetaOccursInOtherPair(pairs, i, env))
		// If there is no available new substitution, declare fail.
		if len(matchResults) == 0 {
			return nil, nil
		} else if len(matchResults) == 1 {
			if singleSubst == nil {
				singleSubst = &matchResults[0]
			}
		} else if newSubsts == nil {
			newSubsts = matchResults
		}
	}

	return singleSubst, newSubsts
}

func rhsFreeMetaOccursInOtherPair(
	pairs []_TermPair, pairIndex int, env _UnifyEnv) bool {
	p := pairs[pairIndex]
	for _, fv := range p.t1.Frees(nil) {
		if p.boundVars.Has(fv) || env.ground(fv.Name()) {
			continue
		}
		for i := range pairs {
			if i == pairIndex {
				continue
			}
			if pairs[i].t0.HasFree(fv) || pairs[i].t1.HasFree(fv) {
				return true
			}
		}
	}
	return false
}

// applies a single substitution and recursively unifies
func (env _UnifyEnv) applySingleSubstitution(
	ctx context.Context,
	pairs []_TermPair,
	substs SubstsTuple,
	singleSubst *SubstsTuple,
	avoidNames TermNameSet) []SubstsTuple {

	ok := false
	for i := range singleSubst.TypeSubsts {
		substs.TypeSubsts, ok = insertOrderedTypeSubsts(
			substs.TypeSubsts, singleSubst.TypeSubsts[i])
		if !ok {
			return nil
		}
	}

	for j := range pairs {
		pairs[j] = typeSubstPair(
			ctx,
			pairs[j].t0, pairs[j].t1, &pairs[j].boundVars, substs.TypeSubsts)
	}

	for j := range substs.TermSubsts {
		typeSubstTermSubst(&substs.TermSubsts[j], substs.TypeSubsts)
	}

	Assert(len(singleSubst.TermSubsts) == 1)
	typeSubstTermSubst(&singleSubst.TermSubsts[0], substs.TypeSubsts)

	termSubsts, inserted := insertOrderedTermSubsts(
		ctx, substs.TermSubsts, singleSubst.TermSubsts[0])
	substs.TermSubsts = termSubsts
	Assert(inserted)

	for j := range pairs {
		pairs[j] = termSubstPair(ctx, pairs[j], singleSubst.TermSubsts)
	}

	if ctx.Err() != nil {
		return nil
	}

	return env.tryUnify(ctx, pairs, substs, avoidNames)
}

// expandOneBranch explores one candidate substitution of an
// expandSearchTree fan-out: clone the state, commit newSubst, recurse.
// Returns the sub-tree's solutions (nil on inconsistency / cancellation).
// QuitSentinel from a fired ctx is swallowed here so one cancelled
// branch does not discard sibling branches' already-collected results.
func (env _UnifyEnv) expandOneBranch(
	ctx context.Context,
	pairs []_TermPair,
	substs SubstsTuple,
	newSubst SubstsTuple,
	avoidNames TermNameSet) (results []SubstsTuple) {

	defer func() {
		if utils.RecoverQuit(recover()) {
			results = nil
		}
	}()
	ok := false
	typeSubsts := utils.Clone(substs.TypeSubsts)
	clonePairs := utils.Clone(pairs)
	termSubsts := utils.Clone(substs.TermSubsts)

	for i := range newSubst.TypeSubsts {
		if typeSubsts, ok = insertOrderedTypeSubsts(
			typeSubsts, newSubst.TypeSubsts[i]); !ok {
			return nil
		}
	}

	for j := range clonePairs {
		clonePairs[j] = typeSubstPair(
			ctx,
			clonePairs[j].t0, clonePairs[j].t1, &clonePairs[j].boundVars, typeSubsts)
	}

	for j := range termSubsts {
		typeSubstTermSubst(&termSubsts[j], typeSubsts)
	}

	Assert(len(newSubst.TermSubsts) == 1)
	typeSubstTermSubst(&newSubst.TermSubsts[0], typeSubsts)
	termSubsts, inserted := insertOrderedTermSubsts(
		ctx, termSubsts, newSubst.TermSubsts[0])
	Assert(inserted)

	for j := range clonePairs {
		clonePairs[j] = termSubstPair(ctx, clonePairs[j], newSubst.TermSubsts)
	}

	if ctx.Err() != nil {
		return nil
	}

	return env.tryUnify(
		ctx, clonePairs,
		SubstsTuple{typeSubsts, termSubsts},
		avoidNames)
}

// explores multiple substitution possibilities, one after another in
// newSubsts order, on the calling goroutine, under either cut.
//
// Under the work budget the budget is consumed in a fixed order, so the
// cut point — and therefore the result set — is identical on every
// run. A branch cut mid-flight contributes nothing; later branches fail
// their first poll immediately (cheap), and results collected before
// the cut survive.
//
// Under a caller's deadline the same order holds and the clock cuts.
// A search stays one goroutine so that a caller running many searches
// at once — the CNF refuter resolves every literal of a clause against
// every subterm of another concurrently — holds one goroutine per
// search, each at most one poll away from a fired deadline. A pool of
// workers per fan-out, nested at every level of the tree, would
// multiply the goroutines and their stacks by the depth of the search;
// under load the runtime then sees the deadline late and unwinds
// slowly, with the caller's session locked for the duration.
func (env _UnifyEnv) expandSearchTree(
	ctx context.Context,
	pairs []_TermPair,
	substs SubstsTuple,
	newSubsts []SubstsTuple,
	avoidNames TermNameSet) []SubstsTuple {

	var results []SubstsTuple
	for _, newSubst := range newSubsts {
		results = append(results,
			env.expandOneBranch(ctx, pairs, substs, newSubst, avoidNames)...)
	}
	return results
}

// tryUnify recursively tries to unify the pairs.
// This is the core recursive function of the unification algorithm that:
// 1. Simplifies pairs to reduce the problem
// 2. Handles the case where all pairs are flexible/flexible (which can be unified in multiple ways)
// 3. Tries various substitution strategies for flexible/rigid pairs using imitation and projection
// 4. Builds a search tree of possible substitutions and explores them in order
func (env _UnifyEnv) tryUnify(
	ctx context.Context,
	pairs []_TermPair,
	substs SubstsTuple,
	avoidNames TermNameSet) []SubstsTuple {

	// Step 1: Preprocessing
	avoidNames = env.preprocessPairs(pairs, substs, avoidNames)

	// Step 2: Simplify pairs
	pairs, typeSubsts, allFlexibleFlexible, ok := env.simplifyPairs(
		ctx, pairs, substs.TypeSubsts, avoidNames)

	if !ok {
		// this happens when a rigid/rigid pair cannot resolve.
		return nil
	}
	substs.TypeSubsts = typeSubsts

	if len(pairs) == 0 {
		return []SubstsTuple{substs}
	}

	// Step 3: Handle all flexible/flexible pairs
	if allFlexibleFlexible {
		return env.handleAllFlexiblePairs(ctx, pairs, substs, avoidNames)
	}

	// Step 4: Check depth limit
	if env.tooDeep(substs.TermSubsts) || ctx.Err() != nil {
		return nil
	}

	// Step 5: Find substitutions for flexible/rigid pairs
	singleSubst, newSubsts := env.findFlexibleRigidSubstitutions(ctx, pairs, substs, avoidNames)
	// If both singleSubst and newSubsts are nil, no substitutions are available
	if singleSubst == nil && newSubsts == nil {
		return nil
	}

	// Step 6: Apply single substitution if available
	if singleSubst != nil {
		return env.applySingleSubstitution(ctx, pairs, substs, singleSubst, avoidNames)
	}

	// Step 7: Expand search tree for multiple substitutions
	Assert(len(newSubsts) > 1)
	return env.expandSearchTree(ctx, pairs, substs, newSubsts, avoidNames)
}
