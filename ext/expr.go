// expr.go — the typed face of the term wrapper (term_wrapper.go holds
// the sealed core, the untyped wrapper and the untyped methods;
// holtype_phantom.go holds the arrow family).
//
// A typed wrapper carries the invariant "the wrapped term's HOL type
// is HolTypeOf[T]()" in its Go type: *Expr[T] at any phantom, and
// the Arrow family at arrow phantoms (born applicable —
// holtype_phantom.go).
// The invariant is established at the leaves — ext.As, the proof
// layer's typed verbs, all funneling through the one adopt gate below
// — and carried by the compiler from then on. The typed world is left
// explicitly: Core() is the term, and no typed value flows into the
// proof machinery as anything else.
//
// Typed[T] is the parameter CURRENCY of the typed surface: any typed
// wrapper whose phantom is T, whatever its family. Signatures accept
// Typed[T]; values stay concrete. Its bridge method is unexported, so
// the interface is SEALED — only this package's wrappers implement
// it. Reflection-borne callers (the section binder) go through the
// sealed descriptor bridge in this file instead.
//
// The typed surface deliberately carries NO term-construction methods
// of its own beyond the Arrow family's application: propositions are
// written as claim TEXT, and the term-building functions of the proof
// surface (Equal, Lambda, over TermLike) cover the occasional Go-built
// term. What the
// typed layer is for is CHECKING and FLOW — adopting a value at an
// asserted type, and carrying that assertion into the slots that
// consume it (theorem-wrapper witnesses, typed binder closures).

package ext

import (
	"fmt"
	"reflect"

	"github.com/euc-ai/xugo/core"
)

// _TypedCore is the shared body of every TYPED wrapper, whatever its
// shape: the sealed storage (via _ExprCore), the anti-conversion tooth
// `_ [0]T` (with it, instantiations at different phantoms — and the
// wrappers embedding them — have DIFFERENT underlying structs, so a
// cross-phantom conversion forge is a compile error), and the typed
// world's exit. Expr[T] embeds it at T; an arrow wrapper embeds it at
// the arrow's phantom. It holds the untyped core as a named field,
// never embedded: what it promotes would be compiled once per
// instantiation, so its method set is Core and typed alone.
type _TypedCore[T TypePhantom] struct {
	untyped _ExprCore
	_       [0]T
}

// Core is the term itself: the one method a typed wrapper shares with
// a core term, and the whole of what the verbs read from it.
func (t *_TypedCore[T]) Core() Term { return t.untyped.Core() }

// typed is the currency bridge: T in a method PARAMETER position ties
// the interface below to the phantom. Unexported — the seal.
func (*_TypedCore[T]) typed(T) {}

// Typed is the parameter currency of the typed surface: any typed
// wrapper asserting phantom T. *Expr[T] implements Typed[T]; a
// *Arrow[X, Y] implements Typed[Fun[X, Y]]. Sealed: the bridge
// method is unexported, so no outside type can impersonate a typed
// wrapper to a Typed signature.
type Typed[T TypePhantom] interface {
	TermLike
	typed(T)
}

// adopt is the ONE checked gate into the typed world: the term's
// actual HOL type must equal T's reification. Every typed constructor
// in the package funnels through it.
func adopt[T TypePhantom](t Term) _TypedCore[T] {
	want := HolTypeOf[T]()
	got := t.Core().Type()
	if !got.Equals(want) {
		panic(fmt.Sprintf("ext.As: %s has type %s, not %s",
			PrintTerm(t), FormatType(got), FormatType(want)))
	}
	return _TypedCore[T]{untyped: _ExprCore{_UnexportedTerm: t.Core()}}
}

// As adopts a term into the typed world, CHECKED — the public face of
// the adopt gate. Everything already typed composes by signature;
// everything untyped must pass here (or through a proof-layer typed
// verb, which funnels into the same gate) before a typed signature
// will accept it.
func As[T TypePhantom](t Term) *Expr[T] { return &Expr[T]{adopt[T](t)} }

// the sealed reflection bridge: how a caller that
// holds a typed wrapper type only as a reflect.Type (the section
// binder reading a closure's parameter types) recovers that
// instantiation's capabilities.
// Go cannot instantiate As[T] from a reflect.Type — a reflected type
// is not a generic type argument. What reflection CAN do is dispatch
// ONE method on a value of the concrete instantiation, and a method
// body runs with T bound: the generic machinery is re-entered exactly
// once, and everything the outside needs — the reified HOL type, the
// target Go type, the checked constructor — comes back as plain
// runtime values in a descriptor. The trick lives in this file only;
// the public math API carries no reflection methods.

// _ExprRuntime is the sealed hook: its method is unexported, so only
// *Expr[T] — declared in this package — satisfies it, and an outside
// type cannot impersonate a typed expression to the probe. (An
// outside type EMBEDDING *Expr[T] inherits the method by promotion;
// DescribeExprType's goType identity check rejects exactly that.)
type _ExprRuntime interface{ exprRuntimeInfo() _ExprRuntimeInfo }

// _ExprRuntimeInfo is one instantiation's capabilities, captured with
// T bound: the phantom reified, the instantiation's own Go type, and
// the checked constructor as a closure. adopt funnels through As —
// the single adoption gate. Its TermLike result keeps the concrete
// wrapper for reflection while requiring access to the wrapped term.
type _ExprRuntimeInfo struct {
	holType core.HolType
	goType  reflect.Type
	adopt   func(Term) TermLike
}

func (*Expr[T]) exprRuntimeInfo() _ExprRuntimeInfo {
	return _ExprRuntimeInfo{
		holType: HolTypeOf[T](),
		goType:  reflect.TypeFor[*Expr[T]](),
		adopt:   func(t Term) TermLike { return As[T](t) },
	}
}

func (*Arrow[X, Y]) exprRuntimeInfo() _ExprRuntimeInfo {
	return _ExprRuntimeInfo{
		holType: HolTypeOf[Fun[X, Y]](),
		goType:  reflect.TypeFor[*Arrow[X, Y]](),
		adopt:   func(t Term) TermLike { return &Arrow[X, Y]{adopt[Fun[X, Y]](t)} },
	}
}

func (*Arrow2[X, Y, R]) exprRuntimeInfo() _ExprRuntimeInfo {
	return _ExprRuntimeInfo{
		holType: HolTypeOf[Fun2[X, Y, R]](),
		goType:  reflect.TypeFor[*Arrow2[X, Y, R]](),
		adopt:   func(t Term) TermLike { return &Arrow2[X, Y, R]{adopt[Fun2[X, Y, R]](t)} },
	}
}

// ExprDescriptor is a typed wrapper instantiation described at
// runtime: what a reflection-borne caller may know (the asserted HOL
// type) and do (construct, checked). Obtain one from
// DescribeExprType; the zero value describes nothing.
type ExprDescriptor struct {
	info _ExprRuntimeInfo
}

// DescribeExprType reports whether rt is a TYPED wrapper type —
// *Expr[T] at some phantom, or the Arrow family — and
// returns its descriptor. The untyped *TermWrapper needs no special
// exclusion: it is its own struct, the probe method is declared on
// the typed wrappers only, and so the interface assertion below
// rejects it structurally.
func DescribeExprType(rt reflect.Type) (ExprDescriptor, bool) {
	if rt == nil || rt.Kind() != reflect.Pointer {
		return ExprDescriptor{}, false
	}
	// A non-nil zero value, used only to reach the instantiation's
	// method table.
	probe, ok := reflect.New(rt.Elem()).Interface().(_ExprRuntime)
	if !ok {
		return ExprDescriptor{}, false
	}
	info := probe.exprRuntimeInfo()
	if info.goType != rt {
		return ExprDescriptor{}, false
	}
	return ExprDescriptor{info: info}, true
}

// HOLType is the HOL type the described parameter asserts — what the
// section binder checks against the statement's binder at plan time.
func (d ExprDescriptor) HOLType() core.HolType { return d.info.holType }

// Adopt runs the instantiation's checked constructor on t and returns
// the new value at the descriptor's own Go type, ready to pass to
// reflect.Call. The identity re-check is an internal invariant, not a
// user-facing gate — the type check on t itself happens inside the
// constructor (As), as everywhere.
func (d ExprDescriptor) Adopt(t Term) reflect.Value {
	v := reflect.ValueOf(d.info.adopt(t))
	if v.Type() != d.info.goType {
		panic("ext: internal Expr descriptor type mismatch")
	}
	return v
}
