package core

import (
	"cmp"
	"fmt"
	"slices"
	"strings"

	"github.com/euc-ai/xugo/utils"
)

type TypeName string

// A TypeKey is a digest of a type, read as a TermKey is: equal types
// have one key, and a key equal for two types that differ is the hash
// collision or the spelled name described there.
type TypeKey string

type HolType interface {
	Equals(HolType) bool
	Compare(HolType) int
	Key() TypeKey

	// Type vars contained in the type.
	TypeVars() []VarType

	// Substitute types for type variables.
	Substitute(...TypeSubst) HolType

	// Abstract matches particular type.
	// E.g. A->A matches bool->bool, but not bool->(bool->bool).
	// The predicate arg determines the var types that are allowed for instantiation.
	// Returns the corresponding substs if matches.
	Matches(HolType, VarTypePredicate) ([]TypeSubst, bool)

	// Returns the holtype itself.
	// This is to make sure wrappers of the holtype get unwrapped.
	core() HolType

	// Internal implementation of match.
	// The last arg is the resulting instantiation if matched.
	matchesImpl(HolType, VarTypePredicate, *[]TypeSubst) bool

	// The term "=" associated with the equality of terms with this type.
	// Lazily calculated.
	eqTerm() ConstTerm
}

// A TypeSubst is a value a caller may build as a literal, so the kernel
// reads its HolType through core() wherever it takes one out.
type TypeSubst struct {
	VarType
	HolType
}

func MakeTypeSubst(v VarType, t HolType) TypeSubst { return TypeSubst{v, t.core()} }

// VarType is a type variable. Like every kernel object it is a handle:
// one word, passed by value, over a node only this package can reach,
// so a holder can copy it and compare it and cannot write what it
// stands for. The zero handle stands for nothing and panics when read.
type VarType struct{ *_VarTypeNode }

type _VarTypeNode struct {
	name TypeName
	eq   utils.Lazy[ConstTerm]
}

func MakeVarType[Name ~string](name Name) VarType {
	return VarType{&_VarTypeNode{name: TypeName(name)}}
}

// IsZero reports whether t is the zero handle.
func (t VarType) IsZero() bool { return t._VarTypeNode == nil }

func (t VarType) Name() TypeName { return t.name }

func (t VarType) Equals(s HolType) bool {
	if s, ok := s.core().(VarType); ok {
		return t.equalsVar(s)
	}
	return false
}

func (t VarType) Compare(s HolType) int {
	if s, ok := s.core().(VarType); ok {
		return t.CompareVar(s)
	}
	return -1
}

func (t VarType) Key() TypeKey { return TypeKey(_VAR_TYPE_KEY_PREFIX + t.name) }

func (t VarType) Substitute(substs ...TypeSubst) HolType {
	for _, s := range substs {
		if s.name == t.name {
			return s.HolType.core()
		}
	}
	return t
}

func (t VarType) Matches(s HolType, f VarTypePredicate) ([]TypeSubst, bool) {
	// Identity-first: a literal same-var match always succeeds with
	// empty σ regardless of `f`. Catching this before the predicate
	// gate means a rigid (non-instantiable) pattern var still matches
	// a literally-equal target.
	if t.Equals(s) {
		return nil, true
	}
	if !f(t) {
		return nil, false
	}
	return []TypeSubst{{t, s.core()}}, true
}

func (t VarType) CompareVar(s VarType) int { return cmp.Compare(t.name, s.name) }

func (t VarType) equalsVar(s VarType) bool { return t == s || t.name == s.name }

func (t VarType) core() HolType {
	if t._VarTypeNode == nil {
		panic("core: the zero VarType stands for no type")
	}
	return t
}

func (t VarType) TypeVars() []VarType { return []VarType{t} }

func (t VarType) matchesImpl(s HolType, f VarTypePredicate, env *[]TypeSubst) bool {
	if !f(t) {
		// Rigid pattern var: target must literally equal. Symmetric
		// to VarType.Matches.
		return t.Equals(s)
	}
	for i := range *env {
		if t.Equals((*env)[i].VarType) {
			return (*env)[i].HolType.Equals(s)
		}
	}
	(*env) = append(*env, TypeSubst{t, s.core()})
	return true
}

func (t VarType) eqTerm() ConstTerm { return t.eq.InitOrLoad(eqByType(t)) }

// MetaType is a type constructor: a name and an arity.
type MetaType struct{ *_MetaTypeNode }

type _MetaTypeNode struct {
	name  TypeName
	arity int
}

func MakeMetaType[Name ~string](name Name, arity int) MetaType {
	return MetaType{&_MetaTypeNode{TypeName(name), arity}}
}

// IsZero reports whether t is the zero handle.
func (t MetaType) IsZero() bool { return t._MetaTypeNode == nil }

func (t MetaType) Name() TypeName { return t.name }

func (t MetaType) Arity() int { return t.arity }

func (t MetaType) Equals(s MetaType) bool {
	return t == s || (t.name == s.name && t.arity == s.arity)
}

// CompositeType is a type constructor applied to its argument types.
type CompositeType struct{ *_CompositeTypeNode }

type _CompositeTypeNode struct {
	meta     MetaType
	subTypes []HolType
	eq       utils.Lazy[ConstTerm]
}

// MakeCompositeType applies metaType to types. The node keeps a slice
// of its own, each element read through core(): the caller's slice is
// the caller's to write afterwards.
func MakeCompositeType(metaType MetaType, types ...HolType) CompositeType {
	own := make([]HolType, len(types))
	for i, t := range types {
		own[i] = t.core()
	}
	return makeCompositeType(metaType, own)
}

// makeCompositeType takes subTypes as the node's own: a fresh slice of
// kernel values.
func makeCompositeType(metaType MetaType, subTypes []HolType) CompositeType {
	utils.Assert(metaType.arity == len(subTypes))
	return CompositeType{&_CompositeTypeNode{meta: metaType, subTypes: subTypes}}
}

// IsZero reports whether t is the zero handle.
func (t CompositeType) IsZero() bool { return t._CompositeTypeNode == nil }

func (t CompositeType) Meta() MetaType { return t.meta }

func (t CompositeType) SubType(i int) HolType { return t.subTypes[i] }

func (t CompositeType) Equals(s HolType) bool {
	if s, ok := s.core().(CompositeType); ok {
		return t == s ||
			(t.meta.Equals(s.meta) &&
				slices.EqualFunc(s.subTypes, t.subTypes, HolType.Equals))
	}
	return false
}

func (t CompositeType) Compare(s HolType) int {
	if s, ok := s.core().(CompositeType); ok {
		// The same type object reaches this compare over and over (every
		// num-typed const shares one CompositeType), and the walk below
		// is a name compare per node plus a recursion into the subtypes.
		// Equals has carried this shortcut all along; Compare did not.
		if t == s {
			return 0
		}
		if c := cmp.Compare(t.meta.name, s.meta.name); c != 0 {
			return c
		}
		return slices.CompareFunc(t.subTypes, s.subTypes, HolType.Compare)
	}
	return 1
}

func (t CompositeType) Key() TypeKey {
	if len(t.subTypes) == 0 {
		return TypeKey(_COMPOSITE_TYPE_KEY_PREFIX + t.meta.name)
	}

	l, seeds := 0, make([]string, len(t.subTypes))
	for i, subtype := range t.subTypes {
		key := subtype.Key()
		seeds[i] = string(key)
		l += len(key)
	}

	var s string
	// usually a key is not longer than this. Only hash when it's too long.
	if l > _TYPE_KEY_HASH_THRES {
		s = utils.GenerateHash(seeds...)
	} else {
		s = strings.Join(seeds, "|")
	}
	return TypeKey(
		fmt.Sprintf("%s%s:[%s]", _COMPOSITE_TYPE_KEY_PREFIX, t.meta.name, s))
}

func (t CompositeType) Substitute(substs ...TypeSubst) HolType {
	if len(substs) == 0 || len(t.subTypes) == 0 {
		return t
	}
	newTypes := utils.MapSlice(
		t.subTypes,
		func(s HolType) HolType { return s.Substitute(substs...) })
	if !slices.EqualFunc(newTypes, t.subTypes, HolType.Equals) {
		return makeCompositeType(t.meta, newTypes)
	}
	return t
}

func (t CompositeType) Matches(s HolType, f VarTypePredicate) ([]TypeSubst, bool) {
	var env []TypeSubst
	if !t.matchesImpl(s, f, &env) {
		return nil, false
	}
	// Strip identity entries from the final result. matchesImpl needs
	// them in-walk for cross-position consistency checks (first leaf
	// pinning A→A means a later A→B occurrence must fail), but they
	// carry no information for the caller.
	return slices.DeleteFunc(env, uselessTypeSubst), true
}

func (t CompositeType) core() HolType {
	if t._CompositeTypeNode == nil {
		panic("core: the zero CompositeType stands for no type")
	}
	return t
}

func (t CompositeType) TypeVars() []VarType {
	var vars []VarType
	for _, t := range t.subTypes {
		vars = utils.OrderedSlicesUnion(
			vars, t.TypeVars(), (VarType).equalsVar, (VarType).CompareVar)
	}
	return vars
}

func (t CompositeType) matchesImpl(s HolType, f VarTypePredicate, env *[]TypeSubst) bool {
	if s, ok := s.core().(CompositeType); ok {
		if !t.meta.Equals(s.meta) {
			return false
		}
		utils.Assert(len(t.subTypes) == len(s.subTypes))
		for i, subType := range t.subTypes {
			if !subType.matchesImpl((s.subTypes)[i], f, env) {
				return false
			}
		}
		return true
	}
	return false
}

func (t CompositeType) eqTerm() ConstTerm { return t.eq.InitOrLoad(eqByType(t)) }

// MatchTypeInto is the env-threading public entry point for the
// recursive type matcher. It walks `pat` against `tgt`, treats type
// vars satisfying `instantiable` as substitution candidates, and
// appends new bindings to `*env`. Returns whether the match succeeded.
//
// Semantics:
//
//   - Instantiable pattern var: if already bound in `env`, the prior
//     binding's HolType must equal the target (consistency check);
//     otherwise append a new binding.
//   - Non-instantiable pattern var: the target must literally equal
//     it (rigid match). This case is reachable by callers that
//     pre-substitute the pattern with accumulated bindings before
//     calling.
//   - Composite: meta must match and subtypes recurse.
//
// `*env` carries identity entries in-flight (e.g. `{A,A}` from an
// early bind of A→A) — these are load-bearing for cross-position
// consistency (a later A→B occurrence must fail). The one-shot public
// `Matches` strips them at the boundary via `slices.DeleteFunc`;
// callers of MatchTypeInto receive the raw env and decide for
// themselves.
//
// On false-return the env may be in a partial state — caller must
// discard or roll back.
func MatchTypeInto(pat, tgt HolType, instantiable VarTypePredicate, env *[]TypeSubst) bool {
	return pat.core().matchesImpl(tgt, instantiable, env)
}

func uselessTypeSubst(s TypeSubst) bool { return s.HolType.core().Equals(s.VarType) }
