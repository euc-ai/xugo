// Set-theory constants and the setOperator dispatch table for the text DSL.
//
// The text parser recognizes set-theory infix operators (∈, ∉, ⊆, ⊊, ∪, ∩,
// ∖), nullary atoms (∅, 𝕌), unary big-op prefixes (⋃, ⋂), plus the set-
// enumeration bracket form `{a₁, …, aₙ}` and the set-builder bracket form
// `{f(x) | φ(x)}`. All lower to polymorphic const applications named as
// sets/set_basic mints them (set_member, subset, proper_subset, union,
// intersection, set_difference, empty_set, universe, big_union,
// big_intersection, insert, set_comprehension, comprehension_spec), `∉`
// to a negated set_member, so a statement written in the surface builds
// the term the chapter's definitions state.
//
// The dispatch is name-only (no per-domain overload like arith's num/real/int
// three-way): every set const has a single polymorphic instance whose type
// variable A is unified against the operand types by buildAppViaMeta at build
// time. The `setOperator` switch mirrors natOperator/realOperator/intOperator
// in arith.go for consistency with the buildBinOp dispatch style.

package dsl

import (
	"github.com/euc-ai/xugo/core"
)

// setElemVar is the abstract element type A that parameterizes every
// polymorphic set const's absType. Kept as a single shared VarType so the
// generated ConstTermMeta AbsTypes are structurally identical — mirrors the
// discipline arith.go follows for RealType/IntType.
var setElemVar = core.MakeVarType("A")

// setOfVar is the abstract set type A → bool: a set is its membership
// predicate — `empty_set : A → bool`, `set_member : A → (A → bool) → bool`,
// `insert : A → (A → bool) → (A → bool)`, etc.
var setOfVar = core.MakeFun(setElemVar, core.TypeBool())

// Set-theory const metas: the def-less surface fallback a parse uses only
// when neither its scope nor its resolver supplies the name (the chapter
// mint wins wherever it is registered). Each meta's (name, absType) is the
// mint's. All are polymorphic in the element type A.
var (
	// set_member : A → (A → bool) → bool. Membership predicate.
	InMeta = core.MakeConstMeta("set_member", core.MakeFun(setElemVar, setOfVar, core.TypeBool()))
	// subset : (A → bool) → (A → bool) → bool.
	SubsetMeta = core.MakeConstMeta("subset", core.MakeFun(setOfVar, setOfVar, core.TypeBool()))
	// proper_subset : (A → bool) → (A → bool) → bool. Proper subset.
	PSubsetMeta = core.MakeConstMeta("proper_subset", core.MakeFun(setOfVar, setOfVar, core.TypeBool()))
	// union : (A → bool) → (A → bool) → (A → bool).
	UnionMeta = core.MakeConstMeta("union", core.MakeFun(setOfVar, setOfVar, setOfVar))
	// intersection : (A → bool) → (A → bool) → (A → bool).
	InterMeta = core.MakeConstMeta("intersection", core.MakeFun(setOfVar, setOfVar, setOfVar))
	// set_difference : (A → bool) → (A → bool) → (A → bool).
	DiffMeta = core.MakeConstMeta("set_difference", core.MakeFun(setOfVar, setOfVar, setOfVar))

	// empty_set : A → bool. The empty set — a nullary term, i.e. its "value" IS
	// the meta.Term() at whatever A instantiation the context pins.
	EmptyMeta = core.MakeConstMeta("empty_set", setOfVar)
	// universe : A → bool. The universe set.
	UnivMeta = core.MakeConstMeta("universe", setOfVar)

	// big_union : ((A → bool) → bool) → (A → bool). Big union over a set-of-sets.
	UnionsMeta = core.MakeConstMeta("big_union",
		core.MakeFun(core.MakeFun(setOfVar, core.TypeBool()), setOfVar))
	// big_intersection : ((A → bool) → bool) → (A → bool). Big intersection.
	IntersMeta = core.MakeConstMeta("big_intersection",
		core.MakeFun(core.MakeFun(setOfVar, core.TypeBool()), setOfVar))

	// insert : A → (A → bool) → (A → bool). Add element to set. The base
	// building block behind the enumeration form `{a₁, …, aₙ}`, which folds
	// as `insert(a₁, insert(a₂, …, insert(aₙ, empty_set)))`.
	InsertMeta = core.MakeConstMeta("insert", core.MakeFun(setElemVar, setOfVar, setOfVar))

	// set_comprehension : (A → bool) → (A → bool). The set-builder encoder: takes a
	// generator predicate (typically `λv. ∃x. comprehension_spec(v, φ(x), f(x))`) and
	// returns a set. The printer detects the specific λv.∃x.comprehension_spec(...)
	// shape to render as `{f(x) | φ(x)}`.
	SetComprehensionMeta = core.MakeConstMeta("set_comprehension", core.MakeFun(setOfVar, setOfVar))
	// comprehension_spec : A → bool → A → bool. The generator body's assertion —
	// `comprehension_spec(v, φ, x)` reads "v = x ∧ φ". Only meaningful inside a set_comprehension
	// generator; the parser accepts it as a plain 3-arg application so
	// already-emit'd text keeps parsing, and the set-builder desugarer emits
	// this exact shape.
	ComprehensionSpecMeta = core.MakeConstMeta("comprehension_spec",
		core.MakeFun(setElemVar, core.TypeBool(), setElemVar, core.TypeBool()))
)

// setOperator returns the const meta for a recognized set-theory infix
// operator symbol, or nil. Keyed by the canonical lex form (Unicode
// symbol as it appears in symbolTokens). Mirrors natOperator's shape so
// buildBinOp dispatches uniformly across arith and set-theory infix.
func setOperator(op string) core.ConstTermMeta {
	switch op {
	case "∈":
		return InMeta
	case "⊆":
		return SubsetMeta
	case "⊊":
		return PSubsetMeta
	case "∪":
		return UnionMeta
	case "∩":
		return InterMeta
	case "∖":
		return DiffMeta
	}
	return core.ConstTermMeta{}
}

// unarySetOperator returns the const meta for a unary set-theory prefix
// operator symbol (the big-ops ⋃, ⋂), or nil. Applied at atom position by
// the parser: `⋃(s)` and `⋂(s)` build big_union(s) / big_intersection(s).
func unarySetOperator(op string) core.ConstTermMeta {
	switch op {
	case "⋃":
		return UnionsMeta
	case "⋂":
		return IntersMeta
	}
	return core.ConstTermMeta{}
}

// seedSetScopeConstFallback fills the env's ConstMetas table with the
// DSL-side set-theory surface metas by name — but only for entries
// that aren't already present. Called by buildProp /
// ParseTermTextInScope AFTER the caller-supplied scope has merged onto
// the env AND after the resolver pre-seed (seedResolverConsts) has
// run, so the precedence is caller scope > const resolver > this
// table: a caller-provided canonical corpus meta (typically with an
// abstract type-var name of its own) wins on collision, and a resolver
// hit wins over the surface meta.
//
// The resolver is deliberately NOT consulted here. The surface metas
// are def-less α-variants of the registered metas — a term built from one
// is indistinguishable by name+instance-type yet answers DefThm() nil,
// and mixing the two meta pointers in one process trips the
// ConstTermMeta.Equals soundness assert — so a resolver-wired parse
// must reach the resolver for every set name the text uses; but ONLY
// for those. The resolver walker surfaces the lowered name of every
// set surface form (`x ∈ s` → set_member, `∅` → empty_set, `{a, b}` → insert,
// `{x | φ}` → set_comprehension/comprehension_spec, `⋃` → big_union; walkResolverNames), so by
// the time this runs every set name the text mentions has been asked
// of the resolver, and a name the text does NOT mention is never
// asked: the resolver serves a constant on demand (a chapter-minted
// definition is served from its mint, and a name still in the
// inventory snapshot is not served — and thereby locked against a
// later mint — by a parse that never spells it). Only when nothing
// above supplied the name (bare `dsl.ParsePropText(...)` in tests or
// agent surfaces, or a resolver with no row) does the DSL-side meta
// kick in.
//
// Populates the ConstMetas table only. Every set const is polymorphic in A
// (its absType contains a var), so meta.Term() is nil — putting them into
// Consts would insert nil entries that panic in lookupType. buildApp's
// meta-only branch handles polymorphic instantiation at use-site — the
// same path defaultNatScopeConstMetas relies on for `,` and COND (see
// arith.go's note there).
func seedSetScopeConstFallback(metas map[string]core.ConstTermMeta) {
	for _, e := range surfaceFallbackEntries {
		if _, ok := metas[e.name]; ok {
			continue
		}
		metas[e.name] = e.meta
	}
}

// surfaceFallbackEntries is seedSetScopeConstFallback's table — the
// set-theory consts the DSL can supply by name when neither the caller
// scope nor its const resolver does. SurfaceFallbackMetas exposes the
// same table for read-only identity checks.
var surfaceFallbackEntries = []struct {
	name string
	meta core.ConstTermMeta
}{
	{"set_member", InMeta},
	{"subset", SubsetMeta},
	{"proper_subset", PSubsetMeta},
	{"union", UnionMeta},
	{"intersection", InterMeta},
	{"set_difference", DiffMeta},
	{"empty_set", EmptyMeta},
	{"universe", UnivMeta},
	{"big_union", UnionsMeta},
	{"big_intersection", IntersMeta},
	{"insert", InsertMeta},
	{"set_comprehension", SetComprehensionMeta},
	{"comprehension_spec", ComprehensionSpecMeta},
}

// SurfaceFallbackMetas returns the DSL-side def-less surface metas by
// const name: the set-theory table above plus funcops' ComposeMeta.
// These are the metas a parse falls back to only when neither the
// caller's scope nor its const resolver supplied the name — so a
// parsed statement carrying one of THESE meta pointers resolved that
// name with no scope authority behind it. Read-only: consumers compare
// pointers (a ConstTerm's Meta()) against the table; seeding scopes
// stays seedSetScopeConstFallback's job, with its resolver-first
// precedence. The monomorphic arith/nat defaults are deliberately not
// here — they are the corpus-wide machine spelling and cannot freshen
// an instance.
func SurfaceFallbackMetas() map[string]core.ConstTermMeta {
	out := make(map[string]core.ConstTermMeta, len(surfaceFallbackEntries)+1)
	for _, e := range surfaceFallbackEntries {
		out[e.name] = e.meta
	}
	out[string(ComposeMeta.Name())] = ComposeMeta
	return out
}
