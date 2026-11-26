package unify

import (
	"time"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/utils"
)

type (
	HolType           = core.HolType
	VarType           = core.VarType
	CompositeType     = core.CompositeType
	Term              = core.Term
	VarTerm           = core.VarTerm
	ConstTerm         = core.ConstTerm
	AppliedTerm       = core.AppliedTerm
	AbsTerm           = core.AbsTerm
	TermName          = core.TermName
	TermSubst         = core.TermSubst
	Prop              = core.Prop
	Thm               = core.ThmCert
	VarTypePredicate  = core.VarTypePredicate
	VarPredicate      = core.VarPredicate
	TypeSubst         = core.TypeSubst
	TypeSubstsGroup   = []core.TypeSubst
	VarList           = ext.VarList
	TermSubstsGroup   = ext.TermSubstsGroup
	TermNamePredicate = utils.Predicate[TermName]
	TermNameSet       = utils.Set[TermName]
)

var (
	Assert        = utils.Assert
	TypeA         = core.TypeA()
	TypeB         = ext.TypeB
	TypeBool      = core.TypeBool()
	MakeFun       = core.MakeFun
	IsBool        = core.IsBool
	MakeTypeSubst = core.MakeTypeSubst
	Abs           = core.Abs
	Eq            = core.Eq
	MatchesEQ     = core.MatchesEQ
	WrapTerm      = ext.WrapTerm
	Var           = ext.Var
	Const         = ext.Const
	Apply         = ext.Apply

	F             = ext.F
	T             = ext.T
	NOT           = ext.NOT
	Not           = ext.Not
	ForAll        = ext.ForAll
	Exists        = ext.Exists
	MakeTermSubst = ext.MakeTermSubst
)

const (
	// DefaultUnifyTimeout is the wall-clock cap Unify installs under
	// XUGO_UNIFY_WALLCLOCK=1 when the caller's ctx has no deadline (the
	// default is the deterministic work budget, DefaultUnifyBudget).
	// Callers that want a different cap should wrap their ctx with
	// context.WithTimeout before calling Unify; Unify will then respect that
	// deadline instead.
	DefaultUnifyTimeout = 100 * time.Millisecond

	// _UNIFY_SIZE_LIMIT_THRES is the threshold for detecting when
	// substitution search has become too deep, preventing infinite loops
	_UNIFY_SIZE_LIMIT_THRES = 8
)

// SubstsTuple represents a pair of type and term substitutions
// that together form a complete unification solution
type SubstsTuple struct {
	TypeSubsts TypeSubstsGroup
	TermSubsts TermSubstsGroup
}

// _TypePair represents a pair of types to be unified
type _TypePair struct{ t0, t1 HolType }

// _TermPair represents a pair of terms to be unified along with their bound variables
type _TermPair struct {
	t0 Term
	t1 Term
	// boundVars contains the vars that are eventually abstracted.
	// e.g. when comparing {λx.f(x), λx.g(x), {}}, put x into bound vars
	// then work on {f(x), g(x), {x}}.
	boundVars VarList
}

func chooseName[Name ~string](initName Name, avoidNames TermNamePredicate) TermName {
	name := TermName(initName)
	// we check name + "0" because the new variables that consume the generated name
	// are usually using name + "i" rather than the name itself.
	for avoidNames(name) || avoidNames(utils.Subscript(name, 0)) {
		name = utils.NextName(name)
	}
	return name
}

// Renames abstracted vars of the 2 terms with the same type
// with multiple levels of abstractions
// such that the abstracted vars are exactly same.
// The input terms should be β-η normalized so the levels
// are aligned.
func alignAbsVars(t0, t1 Term) (Term, Term) {
	Assert(t0.Type().Equals(t1.Type()))
	if !ext.IsFunType(t0.Type()) {
		return t0, t1
	}
	_t0, _t1 := ext.AlignAbstractedVar(t0, t1)
	body0, body1 := alignAbsVars(_t0.Body(), _t1.Body())
	if !body0.Equals(_t0.Body()) {
		_t0 = core.Abs(_t0.Var(), body0)
	}
	if !body1.Equals(_t1.Body()) {
		_t1 = core.Abs(_t1.Var(), body1)
	}
	return _t0, _t1
}

// Decomposes the term (without abstraction vars) to its head and args.
// Also returns whether the term is rigid.
// A term is rigid if its head is a bound var or a const.
// otherwise it is flexible, i.e. the head is instantiable.
func decomposeHead(
	t Term,
	boundVars *VarList,
	ground TermNamePredicate) (Term, []Term, bool) {
	f, args := ext.MatchesApply(t)
	switch f := f.(type) {
	case VarTerm:
		return f, args, boundVars.Has(f) || ground(f.Name())
	case ConstTerm:
		return f, args, true
	default:
		panic("Should not happen.")
	}
}

// Adds var/const names that are used in this term (type doesn't matter).
// A shared DAG is walked once per node (ext.SeenSetFor's gate).
func addNames(t Term, s TermNameSet) {
	addNamesIn(t, s, ext.SeenSetFor(t))
}

func addNamesIn(t Term, s TermNameSet, seen *ext.SeenSet) {
	switch t := t.Core().(type) {
	case VarTerm:
		s.Add(t.Name())
	case ConstTerm:
		s.Add(t.Meta().Name())
	case AppliedTerm:
		if seen.Visited(t) {
			return
		}
		addNamesIn(t.Fun(), s, seen)
		addNamesIn(t.Arg(), s, seen)
	case AbsTerm:
		if seen.Visited(t) {
			return
		}
		s.Add(t.Var().Name())
		addNamesIn(t.Body(), s, seen)
	default:
		panic("Should not happen.")
	}
}

// Returns whether all pairs are of particular flexibility patterns
// First return value: true if all pairs are flexible/flexible
// Second return value: true if all pairs are either flexible/rigid or flexible/flexible
// This helps determine which unification strategy to apply
func checkFlexiblePairs(pairs []_TermPair, ground TermNamePredicate) (bool, bool) {
	Assert(len(pairs) > 0)
	// the first bool means all pairs are flexible/flexible
	// the second bool means all pairs are either flexible/rigid or flexible/flexible
	allFlexibleFlexible, allFlexibleAny := true, true
	for i := range pairs {
		Assert(!pairs[i].t0.AlphaEquals(pairs[i].t1))
		_, _, isRigid0 := decomposeHead(pairs[i].t0, &pairs[i].boundVars, ground)
		_, _, isRigid1 := decomposeHead(pairs[i].t1, &pairs[i].boundVars, ground)
		if isRigid0 || isRigid1 {
			allFlexibleFlexible = false
			if isRigid0 {
				allFlexibleAny = false
				break
			}
		}
	}
	return allFlexibleFlexible, allFlexibleAny
}
