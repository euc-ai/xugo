package unify

import (
	"context"
	"slices"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

// Creates a term substitution for unification, handling normalization
func makeUnifyTermSubst(ctx context.Context, v, t Term) TermSubstsGroup {
	t = ext.EtaCollapse(ctx, ext.BetaCollapse(ctx, t))
	_v, _ := v.AsVar()
	Assert(!t.HasFree(_v))
	return TermSubstsGroup{MakeTermSubst(_v, t)}
}

// First remove the abstraction vars and add those to the bound vars,
// then make a pair for the bodies.
// Should only be used for β-η normalized terms.
func makeBodyPair(t0, t1 Term, boundVars *VarList) _TermPair {
	_t0, _t1 := alignAbsVars(t0, t1)
	vars0, body0 := ext.MatchesAbs(_t0)
	vars1, body1 := ext.MatchesAbs(_t1)
	Assert(_t0.AlphaEquals(t0) && _t1.AlphaEquals(t1) && len(vars0) == len(vars1))
	for i, v := range vars0 {
		Assert(v.Equals(vars1[i]))
		boundVars.Add(v)
	}
	return _TermPair{body0, body1, *boundVars}
}

// Makes a pair of terms for unification.
// If the type of the terms is an atomic type, just make the pair directly.
// If the type is not atomic, i.e. it is a function type,
// β-η normalizes the terms,
// then uses makeBodyPair to make the pair.
func makePair(ctx context.Context, t0, t1 Term, boundVars *VarList) _TermPair {
	_boundVars := boundVars.Clone()
	Assert(t0.Type().Equals(t1.Type()))
	for v := range boundVars.Iter() {
		if !t0.HasFree(v) && !t1.HasFree(v) {
			_boundVars.Remove(v)
		}
	}
	t0, t1 = ext.BetaEtaNormalize(ctx, t0), ext.BetaEtaNormalize(ctx, t1)
	return makeBodyPair(t0, t1, &_boundVars)
}

// Verifies if the pairs satisfy some initial constraints.
// Ensures variable capture is avoided by renaming bound variables when necessary.
// Performs checks on type substitutions to prevent circular dependencies.
func verifyPairs(pairs []_TermPair, substs SubstsTuple) {
	for i := range substs.TypeSubsts {
		Assert(!ext.TypeHasVar(substs.TypeSubsts[i].HolType, substs.TypeSubsts[i].VarType))
	}
	for j := range substs.TermSubsts {
		v, t := substs.TermSubsts[j].VarTerm, substs.TermSubsts[j].Term
		Assert(!t.HasFree(v))
		for i := range substs.TypeSubsts {
			varType := substs.TypeSubsts[i].VarType
			Assert(!ext.TermHasTypeVar(v, varType) && !ext.TermHasTypeVar(t, varType))
		}
	}
	for k := range pairs {
		for i := range substs.TypeSubsts {
			varType := substs.TypeSubsts[i].VarType
			Assert(!ext.TermHasTypeVar(pairs[k].t0, varType) &&
				!ext.TermHasTypeVar(pairs[k].t1, varType))
			for v := range pairs[k].boundVars.Iter() {
				Assert(!ext.TypeHasVar(v.Type(), varType))
			}
		}

		for j := range substs.TermSubsts {
			vSubst, tSubst := substs.TermSubsts[j].VarTerm, substs.TermSubsts[j].Term
			if pairs[k].boundVars.HasNo(vSubst) {
				Assert(!pairs[k].t0.HasFree(vSubst) && !pairs[k].t1.HasFree(vSubst))
			}
			// If a bound var is a var of a subst, simply replace that var.
			for _, v := range tSubst.Frees(pairs[k].boundVars.Has) {
				vp := v
				for tSubst.HasFree(vp) ||
					pairs[k].boundVars.Has(vp) ||
					pairs[k].t0.HasName(vp.Name()) ||
					pairs[k].t1.HasName(vp.Name()) {
					vp = vp.Rename()
				}
				vSub := MakeTermSubst(v, vp)
				pairs[k].boundVars.Replace(v, vp)
				pairs[k].t0 = pairs[k].t0.Substitute(vSub)
				pairs[k].t1 = pairs[k].t1.Substitute(vSub)
			}
		}
	}
}

// Instantiates types in a term pair.
// Creates a new pair with type substitutions applied to both terms and bound variables.
func typeSubstPair(ctx context.Context, t0, t1 Term, boundVars *VarList, substs TypeSubstsGroup) _TermPair {
	_boundVars := VarList{}
	for v := range boundVars.Iter() {
		_v := v.TypeSubstitute(substs...).(VarTerm)
		_boundVars.Add(_v)
	}
	return makePair(
		ctx,
		t0.TypeSubstitute(substs...),
		t1.TypeSubstitute(substs...),
		&_boundVars)
}

// Instantiates terms in a term pair.
// If the var of a substitution is bound, ignore it, because the var is essentially
// an abstracted var and should not be instantiated.
// If a free var of a substitution term is bound, first rename the bound (abstracted) var
// to avoid variable capture during substitution.
func termSubstPair(ctx context.Context, p _TermPair, substs TermSubstsGroup) _TermPair {
	_substs := make(TermSubstsGroup, 0, len(substs))
	for i := range substs {
		if p.boundVars.Has(substs[i].VarTerm) {
			continue
		}
		if !p.t0.HasFree(substs[i].VarTerm) && !p.t1.HasFree(substs[i].VarTerm) {
			continue
		}
		_substs = append(_substs, substs[i])
	}
	if len(_substs) == 0 {
		return p
	}
	boundVars := p.boundVars.Clone()
	t0, t1 := p.t0, p.t1

	avoidName := func(name TermName) bool {
		return t0.HasName(name) ||
			t1.HasName(name) ||
			utils.Any(_substs,
				func(subst TermSubst) bool {
					return subst.Term.HasName(name)
				})
	}

	for i := range _substs {
		// If a bound var is a var of a subst, simply replace that var.
		for _, v := range _substs[i].Term.Frees(boundVars.Has) {
			vp := v
			for _substs[i].Term.HasFree(vp) || boundVars.Has(vp) {
				name := chooseName(vp.Name(), avoidName)
				vp = core.Var(name, vp.Type())
			}
			Assert(!v.Equals(vp))
			vSub := MakeTermSubst(v, vp)
			boundVars.Replace(v, vp)
			t0, t1 = t0.Substitute(vSub), t1.Substitute(vSub)
		}
	}
	return makePair(
		ctx,
		t0.Substitute(_substs...),
		t1.Substitute(_substs...),
		&boundVars)
}

// Instantiates types in a term substitution.
func typeSubstTermSubst(subst *TermSubst, typeSubsts TypeSubstsGroup) {
	varTerm := subst.VarTerm.TypeSubstitute(typeSubsts...)
	term := subst.Term.TypeSubstitute(typeSubsts...)
	if !varTerm.Equals(subst.VarTerm) || !term.Equals(subst.Term) {
		*subst = MakeTermSubst(varTerm, term)
	}
}

func CompareTermSubsts(subst0, subst1 TermSubstsGroup) int {
	return slices.CompareFunc(subst0, subst1,
		func(e0, e1 TermSubst) int {
			if c := e0.VarTerm.Compare(e1.VarTerm); c != 0 {
				return c
			}
			return e0.Term.Compare(e1.Term)
		})
}

// CompareSubsts compares two substitution tuples for ordering.
func CompareSubsts(subst0, subst1 SubstsTuple) int {
	if c := slices.CompareFunc(subst0.TypeSubsts, subst1.TypeSubsts,
		func(e0, e1 TypeSubst) int {
			if c := e0.VarType.CompareVar(e1.VarType); c != 0 {
				return c
			}
			return e0.HolType.Compare(e1.HolType)
		}); c != 0 {
		return c
	}

	return CompareTermSubsts(subst0.TermSubsts, subst1.TermSubsts)
}

func eqSubsts(subst0, subst1 SubstsTuple) bool {
	return CompareSubsts(subst0, subst1) == 0
}

// sortSubsts sorts and deduplicates substitutions.
func sortSubsts(substs []SubstsTuple) []SubstsTuple {
	slices.SortStableFunc(substs, CompareSubsts)
	return slices.CompactFunc(substs, eqSubsts)
}

func compareTypeSubstByVar(subst0, subst1 TypeSubst) int {
	return subst0.VarType.CompareVar(subst1.VarType)
}

// insertOrderedTypeSubsts inserts a type substitution into an ordered list of substitutions
// Returns the updated substitution list and whether the insertion was successful
// The insertion might fail if it would create a circular dependency
func insertOrderedTypeSubsts(
	substs TypeSubstsGroup, newSubst TypeSubst) (TypeSubstsGroup, bool) {
	if i, found := slices.BinarySearchFunc(
		substs, newSubst, compareTypeSubstByVar); !found {
		newSubst.HolType = newSubst.HolType.Substitute(substs...)
		if ext.TypeHasVar(newSubst.HolType, newSubst.VarType) {
			// self contained substitusion
			return nil, false
		}
		for j := range substs {
			substs[j].HolType = substs[j].HolType.Substitute(newSubst)
		}
		substs = slices.Insert(substs, i, newSubst)
	} else if !substs[i].HolType.Equals(newSubst.HolType) {
		// 2 different substitutions have the same var
		return nil, false
	}
	return substs, true
}

func compareTermSubstByVar(subst0, subst1 TermSubst) int {
	return subst0.VarTerm.Compare(subst1.VarTerm)
}

// insertOrderedTermSubsts inserts term substitutions into an ordered list of substitutions
// Returns the updated substitution list and whether the insertion was successful
// The insertion might fail if it would create a circular dependency
func insertOrderedTermSubsts(
	ctx context.Context,
	substs TermSubstsGroup, newSubsts ...TermSubst) (TermSubstsGroup, bool) {
	inserted := false
	for _, newSubst := range newSubsts {
		Assert(utils.None(substs,
			func(s TermSubst) bool { return newSubst.Term.HasFree(s.VarTerm) }))
		if i, found := slices.BinarySearchFunc(
			substs, newSubst, compareTermSubstByVar); !found {
			for j := range substs {
				if !substs[j].Term.HasFree(newSubst.VarTerm) {
					continue
				}
				substs[j].Term = ext.EtaCollapse(
					ctx,
					ext.BetaCollapse(
						ctx,
						substs[j].Term.Substitute(newSubst)))
			}
			inserted = true
			substs = slices.Insert(substs, i, newSubst)
		} else {
			// if the var of the new substitution is already in the list
			// the substitution term should be same.
			Assert(substs[i].Term.AlphaEquals(newSubst.Term))
		}
	}
	return substs, inserted
}

// Creates a term that maps arguments of the given types to the target term
// Used to create substitution terms for variables with function types
// For example, creates λx₁...λxₙ.target for the given argument types
func mapToTarget(types []HolType, target Term) Term {
	Assert(target != nil && utils.Last(types).Equals(target.Type()))
	t := target
	for i, ti := range slices.Backward(utils.BeforeLast(types)) {
		// add indices to the name to make sure that it won't collide
		// with each other or the body.
		t = core.Abs(
			core.Var(
				chooseName(utils.Subscript(string(utils.X_DOT), i), t.HasName),
				ti),
			t)
	}
	return t
}

// avoidSubstsNames avoids names that show up in the substitutions.
func avoidSubstsNames(
	avoidNames TermNameSet,
	pairs []_TermPair,
	substs TermSubstsGroup) TermNameSet {
	avoidNames = avoidNames.Clone()
	for i := range pairs {
		addNames(pairs[i].t0, avoidNames)
		addNames(pairs[i].t1, avoidNames)
	}
	for i := range substs {
		addNames(substs[i].VarTerm, avoidNames)
		addNames(substs[i].Term, avoidNames)
	}
	return avoidNames
}

// Creates a function that checks if a substitution search has become too deep
// This prevents potential infinite loops in unification by limiting the complexity
// of generated substitutions based on the size of the original terms
func substsTooDeep(s, t Term) func(TermSubstsGroup) bool {
	sizeLimit := (s.Size() + t.Size()) + _UNIFY_SIZE_LIMIT_THRES
	return func(substs TermSubstsGroup) bool {
		for j := range substs {
			if s.HasFree(substs[j].VarTerm) || t.HasFree(substs[j].VarTerm) {
				if substs[j].Term.Size() > sizeLimit {
					return true
				}
			}
		}
		return false
	}
}
