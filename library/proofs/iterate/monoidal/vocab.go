// vocab.go — the chapter's statement vocabulary.
//
// The fold alphabet is doubly polymorphic: `A` is the INDEX type the
// sets range over, `B` the CARRIER the operation acts on, and every
// row here keeps both free — the whole point of the chapter is that
// no CARRIER domain is named (the index side admits one concrete
// reading, ℕ: its ranges and intervals). The set surface the statements speak
// (`∈` and, as members land, the constructors) is declared locally at
// those variable types: the sets domain's own type table is internal
// to `sets/`, so a chapter outside it spells the types itself — the
// same local-declaration arrangement `real_sup_inf` uses for its ℝ
// instance, except that here nothing is pinned.
//
// Declaring the names is load-bearing, not decoration: the text-DSL
// parses `∈` on its own but its own metas are def-LESS, and this
// chapter's method is definitional unfolding: the membership driver's
// unfolds resolve through the defs carried by the goal's own const
// occurrences. Only names the members state are
// declared, never speculative ones.
//
// The rows spell their types as PHANTOMS: each constant's type is a
// phantom expression reified through ext.HolTypeOf rather than a
// MakeFun/MakeVarType assembly, so the row reads as the type it
// declares and reifies from one source. The generated handles
// (zz_vocab_gen.go) are untyped: a handle is a term at the letters,
// and the bodies apply it with the untyped chain —
// proposition-building stays on claim TEXT, so the handles are
// deliberately the whole of the build surface.

package monoidal

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// The chapter's alphabet as phantom spellings: the two letters, a set
// over the index, the binary operation on the carrier.
type (
	index   = A
	carrier = B

	indexSet = Set[index]
	binOp    = Op[carrier]
)

// vocab is the chapter alphabet as data — one row per name, each at
// its fully general type, which is what lets claim TEXT spell the
// name. Every row yields a handle; the ones a body builds with are
// Support, Neutral, Insert, Empty, Univ, In and Finite.
var vocab = registry.NewVocabSpec(nil).
	OpsName("foldOps").
	// The subject predicate — declaration-only: statements spell it
	// and Unfolds resolve it, no body builds it.
	Spelled("monoidal_op", ext.HolTypeOf[Fun[binOp, Bool]]).
	// The set surface the support laws are read through: inclusion and
	// the constructors the support commutes with — declaration-only.
	// Each is declared once at variable types; a statement using one
	// at several index types instantiates the same meta per site.
	Spelled("subset", ext.HolTypeOf[Fun2[indexSet, indexSet, Bool]]).
	Spelled("disjoint", ext.HolTypeOf[Fun2[indexSet, indexSet, Bool]]).
	Spelled("delete", ext.HolTypeOf[Fun2[indexSet, index, indexSet]]).
	Spelled("union", ext.HolTypeOf[Fun2[indexSet, indexSet, indexSet]]).
	Spelled("intersection", ext.HolTypeOf[Fun2[indexSet, indexSet, indexSet]]).
	Spelled("set_difference", ext.HolTypeOf[Fun2[indexSet, indexSet, indexSet]]).
	Spelled("image", ext.HolTypeOf[Fun2[Fun[index, C], indexSet, Set[C]]]).
	// Composition, so the image clause's `g ∘ f` summand can be
	// unfolded to an application by name — declared at its textbook
	// letters, `(B → C) → (A → B) → (A → C)`.
	Spelled("o", ext.HolTypeOf[Fun2[Fun[B, C], Fun[A, B], Fun[A, C]]]).As("Compose").
	// The fold itself and the raw combinator inside its definition —
	// declaration-only: statements and Have claims spell them, the
	// recursion members unfold `iterated_op`, no body builds with either.
	Spelled("iterated_op", ext.HolTypeOf[Fun3[binOp, indexSet, Fun[index, carrier], carrier]]).
	Spelled("set_fold", ext.HolTypeOf[Fun3[Fun2[index, carrier, carrier], indexSet, carrier, carrier]]).
	// Support builds `op_support(op, f, s)` — the set a ground cite of a
	// law quantifying over sets has to be handed.
	Spelled("op_support", ext.HolTypeOf[Fun3[binOp, Fun[index, carrier], indexSet, indexSet]]).
	// Neutral builds `neutral_elem(op)` — the base value the recursion
	// members ground the recursion theorem at.
	Spelled("neutral_elem", ext.HolTypeOf[Fun[binOp, carrier]]).
	// Insert and Empty build the one-point set `{a}` the delta laws
	// ground their finiteness at. Empty is pinned at the index-set
	// type: it is nullary, so a use site has nothing to re-instantiate
	// from, and an undeclared ∅ would freshen silently — the pin is
	// the row's type.
	Spelled("insert", ext.HolTypeOf[Fun2[index, indexSet, indexSet]]).
	Spelled("empty_set", ext.HolTypeOf[indexSet]).
	// Univ builds `𝕌`, the whole index type — the set a fold over
	// everything ranges across. Pinned at the index-set type for the
	// same reason Empty is, and with the same hazard: it is nullary,
	// so an undeclared 𝕌 prints identically to this one while keying
	// a weaker proposition.
	Spelled("universe", ext.HolTypeOf[indexSet]).
	// In builds the membership discriminant `x ∈ s` the recursion
	// tier's case analyses split on.
	Spelled("set_member", ext.HolTypeOf[Fun2[index, indexSet, Bool]]).
	// Finite builds `finite(s)`. The members that split on whether a
	// fold's support is finite need the predicate as a TERM, not only
	// as a name their statements spell.
	Spelled("finite", ext.HolTypeOf[Fun[indexSet, Bool]])
