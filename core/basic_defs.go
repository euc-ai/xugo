/**
 * File: basic_defs.go
 *
 * This file contains the definitions of the core types and const terms.
 *
 * The types defined here are:
 * - A (the basic variable type that can be instantiated to any type)
 * - bool
 * - fun (the meta type to compose a function type)
 *
 * The const terms defined here are:
 * - =
 * - ⇔ (iff, the special case of = when both sides are boolean terms)
 * - ε (Hilbert ε operator)
 */

package core

import "github.com/euc-ai/xugo/utils"

// The predefined types and constants. Each is held in an unexported
// variable and handed out by a function: a package variable is
// assignable by any importer, a function is not.
var (
	metaTypeBool = MakeMetaType("bool", 0)
	metaTypeFun  = MakeMetaType("fun", 2)

	typeA    = MakeVarType("A")
	typeBool = makeCompositeType(metaTypeBool, nil)

	metaEq = MakeConstMeta(
		utils.EqStr,
		MakeFun(typeA, typeA, typeBool))

	metaHilbert = MakeConstMeta(
		utils.HilbertStr,
		MakeFun(MakeFun(typeA, typeBool), typeA))

	iff = typeBool.eqTerm()
)

// MetaTypeBool is the type constructor of bool.
func MetaTypeBool() MetaType { return metaTypeBool }

// MetaTypeFun is the type constructor of the function type.
func MetaTypeFun() MetaType { return metaTypeFun }

// TypeA is the type variable A.
func TypeA() VarType { return typeA }

// TypeBool is the type bool.
func TypeBool() CompositeType { return typeBool }

// MetaEq is the constant "=".
func MetaEq() ConstTermMeta { return metaEq }

// MetaHilbert is Hilbert's ε operator.
func MetaHilbert() ConstTermMeta { return metaHilbert }

// IFF is ⇔, if and only if: "=" at bool.
func IFF() ConstTerm { return iff }

// The composite type of a function from the first n-1 types to the last type.
func MakeFun(t0, t1 HolType, types ...HolType) CompositeType {
	if len(types) == 0 {
		return makeCompositeType(metaTypeFun, []HolType{t0.core(), t1.core()})
	}
	return MakeFun(t0, MakeFun(t1, types[0], types[1:]...))
}

// Returns a closure that returns the eq const term for a given type.
// The closure will only be lazily executed if needed.
func eqByType(t HolType) func() ConstTerm {
	return func() ConstTerm { return MakeConstTerm(metaEq, MakeFun(t, t, typeBool)) }
}

// If the type of the term is bool.
func IsBool(t Term) bool { return t.kernel().Type().Equals(typeBool) }

// Makes a term "l = r"
func Eq(l, r Term) AppliedTerm {
	l, r = l.kernel(), r.kernel()
	return eq(l, r)
}

// eq is Eq over kernel values.
func eq(l, r Term) AppliedTerm {
	utils.Assert(l.Type().Equals(r.Type()))
	return apply(apply(l.Type().eqTerm(), l), r)
}

// Matches the term to "l = r".
func MatchesEQ(t Term) (Term, Term, bool) {
	if t, ok := t.AsAppliedTerm(); ok {
		if s, ok := t.fun.AsAppliedTerm(); ok {
			if c, ok := s.fun.AsConst(); ok && c.meta.Equals(metaEq) {
				return s.arg, t.arg, true
			}
		}
	}
	return nil, nil, false
}

// Makes a term "εx.t"
func Hilbert(v VarTerm, t Term) AppliedTerm {
	t = t.kernel()
	utils.Assert(t.Type().Equals(typeBool))
	return apply(
		MakeConstTerm(
			metaHilbert,
			MakeFun(MakeFun(v.Type(), typeBool), v.Type())),
		abs(v, t))
}

// MatchesHilbert matches the term to "εx.t" and returns the abstraction
// λx.t, or the zero AbsTerm when t is not of that form.
func MatchesHilbert(t Term) AbsTerm {
	if t, ok := t.AsAppliedTerm(); ok {
		if s, ok := t.Fun().AsConst(); ok &&
			s.Meta().Equals(metaHilbert) {
			if abs, ok := t.Arg().AsAbsTerm(); ok {
				return abs
			}
		}
	}
	return AbsTerm{}
}
