// Package setvocab holds what is left of the set domain's statement
// alphabet after its names moved to their mints: the two nullary
// rows, empty_set and universe, as an instance of the framework's
// registry.Alphabet.
//
// Every other name of the domain — set_member, insert, delete, union, intersection,
// set_difference, subset, proper_subset, disjoint, big_union, big_intersection, image, and the
// comprehension internals set_comprehension and comprehension_spec — is DEFINED by the
// set_basic chapter (set_basic/definitions.go), and a chapter that
// spells one declares it by name (`Term("set_member")`): the Alphabet's
// fallback reads the type off the mint, which is the one authoritative
// source of it, so this table does not spell it. What a declaration
// buys is the chapter's own statement of its alphabet: a
// constructor is declared when a member states it, never in advance,
// and the vocab generator renders the build surface from those
// declarations (zz_vocab_gen.go).
//
// Why the two rows remain. empty_set and universe are nullary and polymorphic:
// a use site has nothing to re-instantiate from, so a chapter must
// declare them POLYMORPHICALLY — a pinned instance in the ParseScope
// would shadow the meta, and a chapter stating `∅` at two levels (the
// empty set AND the empty family of sets) fails to parse otherwise.
// The Alphabet carries that fact as its PolyConst rows so no chapter
// has to; the mint fallback cannot, since a set is a function type and
// the fallback's nullary test reads a function type as applied.
//
// `Sing` is a set the domain's NOTATION supplies rather than its
// constructors. Where a witness term lives is otherwise a chapter's own
// business, stated in `sets.go`.
//
// It lives under `internal/` so that only packages rooted at
// `proofs/sets` can reach it: this is domain machinery, not a chapter,
// and Go's import rule says so rather than a convention anyone can
// forget.
package setvocab

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// The alphabet is polymorphic in the element type A: a set of A's IS its
// membership predicate, `A → bool`.
func elem() core.HolType { return core.MakeVarType("A") }
func set() core.HolType  { return core.MakeFun(elem(), core.TypeBool()) }

// The two PolyConst rows — see the package comment for why they are
// the ones that remain. The type spelled is the mint's (set_basic's
// EmptySetDef / UniverseDef).
var alphabet = registry.NewAlphabet("set").
	Over("A").
	PolyConst("empty_set", set).
	PolyConst("universe", set)

func Table() *registry.Alphabet { return alphabet }

// Declare registers the named constructors into ctx's ParseScope at
// their types — the table's for empty_set / universe, the mint's for every
// other name; statement-only names, a built name enters via Term.
func Declare(ctx *proof.Script, names ...string) { alphabet.Declare(ctx, names...) }

// Term declares name and returns its build handle — see
// registry.Alphabet.Term.
func Term(ctx *proof.Script, name string) ext.Term { return alphabet.Term(ctx, name) }

// Pinned returns the build handle for a nullary name (empty_set, universe) at
// the build site — see registry.Alphabet.Pinned.
func Pinned(ctx *proof.Script, name string) ext.Term { return alphabet.Pinned(ctx, name) }

// PinnedAt is Pinned at a chosen element type, for a chapter needing
// `∅` or `𝕌` at two instances at once — a statement about a map
// `f : A → B` wants the empty set and the universe on BOTH sides.
func PinnedAt(ctx *proof.Script, name string, elem core.HolType) *ext.TermWrapper {
	return alphabet.PinnedAt(ctx, name, elem)
}

// The one-point set `{y}` is written as a TEXT literal at each site —
// `a.Term("{y}")` — and that is a fact about the set-builder rather
// than a choice: `{y}` is `insert(y, ∅)`, whose `∅` is a nullary name
// needing an instance the surrounding term does not supply, while in
// text the parser reads the instance off `y`. Its siblings `{x | φ}`
// and `{f(x) | x | φ}` have no Go constructor behind them at all, so
// a chapter building any of the three is building text regardless.
// (`a.Term` resolves the block's surface names, so the literal spells
// the binder the proof just fixed.)

// Known lists the names the table itself types, sorted: empty_set and universe.
func Known() []string { return alphabet.Known() }
