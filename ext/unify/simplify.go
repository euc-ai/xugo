package unify

import (
	"context"

	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// simplifyPairs recursively simplifies pairs until one of the following is true:
// 1. all pairs are flexible/flexible pairs.
// 2. the first term of all pairs are flexible terms.
// 3. one rigid/rigid pair is known to be un-unifiable, declare fail in that case.
// If none of these is true, recursively does the following things:
// 1. remove pairs that have identical terms.
// 2. for a rigid/rigid pair, if the rigid heads are same, discard the head and
// pair the args correspondingly.
// 3. swap a rigid/flexible pair.
// Returns
// - the simplified pairs
// - the substitutions in the case of all flexible/flexible pairs
// - if we can determine the unification is impossible, return a false boolean.
func (env _UnifyEnv) simplifyPairs(
	ctx context.Context,
	pairs []_TermPair,
	typeSubsts TypeSubstsGroup,
	avoidNames TermNameSet) (
	[]_TermPair, TypeSubstsGroup, bool, bool) {
	if len(pairs) == 0 {
		return nil, typeSubsts, false, true
	}

	removeIdenticalPairs := make([]_TermPair, 0, len(pairs))
	for i := range pairs {
		if !pairs[i].t0.AlphaEquals(pairs[i].t1) {
			removeIdenticalPairs = append(removeIdenticalPairs, pairs[i])
		}
	}
	if len(removeIdenticalPairs) < len(pairs) {
		return env.simplifyPairs(ctx, removeIdenticalPairs, typeSubsts, avoidNames)
	}

	allFlexibleFlexible, allFlexibleAny := checkFlexiblePairs(pairs, env.ground)
	if allFlexibleFlexible {
		return pairs, typeSubsts, true, true
	} else if allFlexibleAny {
		// all pairs are either flexible/rigid or flexible/flexible, can proceed.
		return pairs, typeSubsts, false, true
	}
	p := pairs[0]
	pairs = pairs[1:]

	Assert(!ext.IsFunType(p.t0.Type()))

	f0, args0, isRigid0 := decomposeHead(p.t0, &p.boundVars, env.ground)
	f1, args1, isRigid1 := decomposeHead(p.t1, &p.boundVars, env.ground)

	if isRigid0 && isRigid1 {
		_typeSubsts, ok := unifyTypePair(f0.Type(), f1.Type(), env.allowedVarTypes)
		if !ok || !f0.TypeSubstitute(_typeSubsts...).
			Equals(f1.TypeSubstitute(_typeSubsts...)) {
			return nil, nil, false, false
		}
		for _, _subst := range _typeSubsts {
			typeSubsts, ok = insertOrderedTypeSubsts(typeSubsts, _subst)
			if !ok {
				return nil, nil, false, false
			}
		}

		Assert(len(args0) == len(args1))
		typePairs := make([]_TypePair, 0, len(args0))
		for i := range args0 {
			if !args0[i].Type().Equals(args1[i].Type()) {
				typePairs = append(typePairs, _TypePair{args0[i].Type(), args1[i].Type()})
			}
		}
		_typeSubsts, ok = unifyTypePairs(typePairs, env.allowedVarTypes)
		if !ok {
			return nil, nil, false, false
		}
		for _, _subst := range _typeSubsts {
			typeSubsts, ok = insertOrderedTypeSubsts(typeSubsts, _subst)
			if !ok {
				return nil, nil, false, false
			}
		}
		_pairs := make([]_TermPair, len(pairs)+len(args0))
		for i := range pairs {
			_pairs[i] = typeSubstPair(
				ctx,
				pairs[i].t0, pairs[i].t1, &pairs[i].boundVars, typeSubsts)
		}
		for i := range args0 {
			_pairs[i+len(pairs)] = typeSubstPair(
				ctx,
				args0[i], args1[i], &p.boundVars, typeSubsts)
		}
		return env.simplifyPairs(ctx, _pairs, typeSubsts, avoidNames)
	}
	if isRigid0 && !isRigid1 {
		// swap
		return env.simplifyPairs(
			ctx,
			append(pairs, _TermPair{p.t1, p.t0, p.boundVars}),
			typeSubsts, avoidNames)
	}

	// p.t0 has a flexible head. Put it at the end of the queue.
	return env.simplifyPairs(ctx, append(pairs, p), typeSubsts, avoidNames)
}

// cleans up substitutions as the final step.
// 1. if the var of a substitution is not free in the original pairs, discard it.
// 2. if a substitution is from a var to a newly introduced var, swap it and simplify others.
// e.g. 2 substitutions {x ↦ new, y ↦ new} can be simplified to {x ↦ y}.
func cleanupSubsts(ctx context.Context, termSubsts TermSubstsGroup, pairs []_TermPair) TermSubstsGroup {
	_termSubsts := make(TermSubstsGroup, 0, len(termSubsts))
	for i := range termSubsts {
		if utils.Any(pairs, func(p _TermPair) bool {
			return p.t0.HasFree(termSubsts[i].VarTerm) ||
				p.t1.HasFree(termSubsts[i].VarTerm)
		}) {
			_termSubsts = append(_termSubsts, termSubsts[i])
		}
	}
	termSubsts = _termSubsts

	// to prevent infinite loop
	maxIterations := len(termSubsts) * 2
	for range maxIterations {
		i := -1
		var swap TermSubst
		for j := range termSubsts {
			if v, ok := termSubsts[j].Term.AsVar(); ok &&
				utils.All(pairs, func(p _TermPair) bool {
					return !p.t0.HasFree(v) && !p.t1.HasFree(v)
				}) {
				// Only swap when the fresh variable v is actually referenced by
				// some other substitution term. Otherwise, swapping a singleton
				// mapping like {x ↦ v} would drop the only binding for x and may
				// break unification on the original pairs.
				referencedElsewhere := false
				for k := range termSubsts {
					if k == j {
						continue
					}
					if termSubsts[k].Term.HasFree(v) {
						referencedElsewhere = true
						break
					}
				}
				if !referencedElsewhere {
					continue
				}
				i, swap = j, MakeTermSubst(v, termSubsts[j].VarTerm)
				break
			}
		}
		if i < 0 {
			break
		}
		_termSubsts = make(TermSubstsGroup, 0, len(termSubsts))
		for j := range termSubsts {
			if j != i {
				termSubsts[j].Term = ext.EtaCollapse(ctx, ext.BetaCollapse(
					ctx,
					termSubsts[j].Term.Substitute(swap)))
				_termSubsts = append(_termSubsts, termSubsts[j])
			}
		}
		termSubsts = _termSubsts
	}
	return termSubsts
}

// unifies type pair.
func unifyTypePair(
	t0, t1 HolType,
	allowedVarTypes VarTypePredicate) (TypeSubstsGroup, bool) {
	anyVar0 := ext.TypeAnyVar(t0, allowedVarTypes)
	anyVar1 := ext.TypeAnyVar(t1, allowedVarTypes)
	if !anyVar0 && !anyVar1 {
		return nil, t0.Equals(t1)
	} else if !anyVar0 {
		return t1.Matches(t0, allowedVarTypes)
	} else if !anyVar1 {
		return t0.Matches(t1, allowedVarTypes)
	}
	substs, ok := unifyTypePairs([]_TypePair{{t0, t1}}, allowedVarTypes)
	if ok {
		Assert(t0.Substitute(substs...).Equals(t1.Substitute(substs...)))
	}
	return substs, ok
}

// unifies type pairs.
func unifyTypePairs(
	pairs []_TypePair, allowedVarTypes VarTypePredicate) (TypeSubstsGroup, bool) {
	// simplify the pairs.
	var _pairs []_TypePair
	changed := false
	for i := range pairs {
		if pairs[i].t0.Equals(pairs[i].t1) {
			changed = true
			continue
		}
		t0, ok0 := pairs[i].t0.(CompositeType)
		t1, ok1 := pairs[i].t1.(CompositeType)
		if ok0 && ok1 {
			if !t0.Meta().Equals(t1.Meta()) {
				return nil, false
			}
			Assert(t0.Meta().Arity() == t1.Meta().Arity())
			for i := range t0.Meta().Arity() {
				_pairs = append(_pairs, _TypePair{t0.SubType(i), t1.SubType(i)})
			}
			changed = true
		} else if ok0 && !ok1 {
			if !allowedVarTypes(pairs[i].t1.(VarType)) {
				return nil, false
			}
			_pairs = append(_pairs, _TypePair{pairs[i].t1, pairs[i].t0})
			changed = true
		} else { // the first type is a var type
			if !allowedVarTypes(pairs[i].t0.(VarType)) {
				// not an allowed var
				if ok1 || !allowedVarTypes(pairs[i].t1.(VarType)) {
					return nil, false
				}
				_pairs = append(_pairs, _TypePair{pairs[i].t1, pairs[i].t0})
				changed = true
			} else {
				_pairs = append(_pairs, pairs[i])
			}
		}
	}
	if changed {
		return unifyTypePairs(_pairs, allowedVarTypes)
	}

	// Now the 1st type in each pair is a var type.
	substs, possible, ok := typeOccursCheck(pairs, allowedVarTypes)
	if !possible {
		return nil, false
	}
	if ok {
		return substs, true
	}
	// Needs more work. Use the first pair to substitute others.
	p := pairs[0]
	pairs = pairs[1:]
	subst := MakeTypeSubst(p.t0.(VarType), p.t1)
	for j := range pairs {
		pairs[j].t0 = pairs[j].t0.Substitute(subst)
		pairs[j].t1 = pairs[j].t1.Substitute(subst)
	}
	return unifyTypePairs(append(pairs, p), allowedVarTypes)
}

// checks whether the type pairs can be transformed to type substitutions.
// Returns substitutions, true, true if it's ok.
// Returns nil, true, false if it's not ok but possible (i.e. needs more work).
// Returns nil, false, false if it's impossible to be unified. Declares fail.
func typeOccursCheck(
	pairs []_TypePair, allowedVarTypes VarTypePredicate) (
	TypeSubstsGroup, bool, bool) {
	if len(pairs) == 0 {
		return nil, true, true
	}

	// The 1st type in a pair should be a var and not identical to the 2nd type.
	Assert(utils.All(pairs, func(p _TypePair) bool {
		t0, ok := p.t0.(VarType)
		return ok && !t0.Equals(p.t1) && allowedVarTypes(t0)
	}))

	// If the 1st type in a pair is contained in the 2nd type,
	// declares failure.
	if utils.Any(pairs, func(p _TypePair) bool {
		return ext.TypeHasVar(p.t1, p.t0.(VarType))
	}) {
		return nil, false, false
	}

	var substs TypeSubstsGroup
	for i := range pairs {
		newSubst, ok := MakeTypeSubst(pairs[i].t0.(VarType), pairs[i].t1), false
		substs, ok = insertOrderedTypeSubsts(substs, newSubst)
		if !ok {
			return nil, true, false
		}
	}
	return substs, true, true
}
