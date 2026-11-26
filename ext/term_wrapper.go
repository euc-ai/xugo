package ext

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/utils"
)

type _UnexportedTerm = Term

// _ExprCore is the body of the untyped wrapper — the sealed term
// storage plus every untyped method, written once. TermWrapper embeds
// it, so the whole set is TermWrapper's; a typed wrapper HOLDS it as
// a named field and promotes nothing — Go compiles every method of a
// generic type once per instantiation, and a family instantiates the
// typed wrappers at every phantom it names — so a typed value yields
// its term through Core() and is built on by the proof surface's
// functions over TermLike.
//
// Embedding Term through the unexported alias promotes
// its methods without exposing a writable Term field on TermWrapper.
// The field is also unsettable through ordinary reflection. A typed
// wrapper separately hides _ExprCore behind _TypedCore's unexported,
// named untyped field, which prevents field and method promotion.
type _ExprCore struct{ _UnexportedTerm }

// TermLike is what a term-taking operation accepts: a core term, or a
// typed wrapper, each yielding the term through Core(). A typed
// wrapper is not itself a Term — its method set is kept to this one
// door, since Go compiles every method of a generic type once per
// instantiation — and the verbs read the term through it.
type TermLike interface{ Core() Term }

// CoreTerms is the terms behind a TermLike list; a nil stays nil, for
// the verb that validates it by name.
func CoreTerms(s []TermLike) []Term {
	out := make([]Term, len(s))
	for i, t := range s {
		out[i] = CoreOf(t)
	}
	return out
}

// CoreOf is the term behind a TermLike; nil for nil.
func CoreOf(t TermLike) Term {
	if t == nil {
		return nil
	}
	return t.Core()
}

// TermWrapper is the untyped wrapper — the term-with-methods as it
// existed before the typed surface, and still the machinery's
// workhorse. It is deliberately its OWN struct, not an Expr
// instantiation: with the untyped wrapper nominally separate, an
// untyped term in a typed position is an ordinary compile-time type
// mismatch, and the phantom vocabulary needs no untyped sentinel —
// TypePhantom is the one constraint.
type TermWrapper struct{ _ExprCore }

// Expr is the GENERIC typed wrapper: a term the compiler knows to
// have HOL type HolTypeOf[T](), at any phantom T. Its method set is
// Core() alone; the typed face — the adoption gate and the currency
// interface — lives in expr.go, the arrow-shaped family
// (born-applicable function terms) in holtype_phantom.go.
type Expr[T TypePhantom] struct {
	_TypedCore[T]
}

func WrapTerm(t Term) *TermWrapper {
	return &TermWrapper{_ExprCore{_UnexportedTerm: t.Core()}}
}

func Var(v TermName, holType HolType) *TermWrapper {
	return WrapTerm(core.Var(v, holType))
}

func Const(meta core.ConstTermMeta, holType HolType) *TermWrapper {
	return WrapTerm(core.MakeConstTerm(meta, holType))
}

func Apply(t Term, s ...Term) AppliedTerm {
	Assert(len(s) > 0)
	return utils.Foldl(
		func(t, s Term) Term { return core.Apply(t, s) }, t, s).(AppliedTerm)
}

func (t *_ExprCore) Apply(s ...TermLike) *TermWrapper { return WrapTerm(Apply(t, CoreTerms(s)...)) }

// Create a lambda abstraction term λt.s
func (t *_ExprCore) To(s TermLike) *TermWrapper {
	return WrapTerm(Abs(t.Core().(VarTerm), s.Core()))
}

// Create a Hilbert choice term εt.s
func (t *_ExprCore) SuchThat(s TermLike) *TermWrapper {
	return WrapTerm(core.Hilbert(t.Core().(VarTerm), s.Core()))
}

// Create an equality term t = s
func (t *_ExprCore) Eq(s TermLike) *TermWrapper { return WrapTerm(Eq(t, s.Core())) }

// Create term t ≠ s
func (t *_ExprCore) Neq(s TermLike) *TermWrapper { return Not(Eq(t, s.Core())) }

// Create term t ⊕ s
func (t *_ExprCore) Xor(s TermLike) *TermWrapper {
	Assert(IsBool(t))
	return Not(core.Eq(t, s.Core()))
}

// Panic if t is not a wrapper of a var term.
func (t *_ExprCore) AssertVar() VarTerm { return t.Core().(VarTerm) }

// Panic if t is not a wrapper of a const term.
func (t *_ExprCore) AssertConst() ConstTerm { return t.Core().(ConstTerm) }

func (t *_ExprCore) String() string { return PrintTerm(t) }

func MakeTermSubst(v, t Term) TermSubst {
	return core.MakeTermSubst(v.Core().(VarTerm), t)
}

func ConstDef(t Term, n TermName) *TermWrapper {
	return WrapTerm(core.NewConstDef(t, n))
}

func TypeDef(
	thm Thm,
	metaTypeName core.TypeName, absConstName, repConstName TermName) (
	core.MetaType, *TermWrapper, *TermWrapper) {
	metaType, absConst, repConst := core.NewTypeDef(
		thm, metaTypeName, absConstName, repConstName)
	return metaType, WrapTerm(absConst), WrapTerm(repConst)
}
