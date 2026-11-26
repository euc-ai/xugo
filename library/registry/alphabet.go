// alphabet.go — the domain alphabet: one table, three verbs.
//
// A DOMAIN with several chapters shares one statement alphabet, and
// before this type each chapter re-spelled the shared constants' types
// (sets grew a hand-rolled table first; int_num had three independent
// spellings of `int_add`'s type, one of them inline in a proof file).
// An Alphabet is that table made a framework value: NAME → the type it
// is declared at, plus the one fact a chapter must not have to know —
// whether the name is nullary and so is registered polymorphically by
// the type-driven Declare
// (a pinned instance in the ParseScope shadows the polymorphic meta,
// and a chapter stating `∅` at two levels fails to parse).
//
// Three verbs, all routing through the table:
//
// - Declare(ctx, names…) — statement-only names, into the ParseScope
// at the domain's types, with the correct verb (Const/PolyConst)
// per entry.
// - Term(ctx, name) — declare AND return the build handle, for a name
// the chapter constructs terms with. The only way to a handle is
// through the declaration, so a handle cannot exist for a name the
// chapter never declared and the two surfaces cannot drift.
// - Pinned(ctx, name) — the build handle for a NULLARY name, taken at
// the build site (inside a member body, after its statements have
// parsed). It pins an instance into the ParseScope, which is why it
// must not run in the vocabulary hook — Term refuses nullary
// entries and points here. PinnedAt is the same verb at a CHOSEN
// element type, for the chapter whose statements live on both sides
// of a map; a domain reaches it by naming its element type variable
// with Over.
//
// Placement rule (mirrors the domain aggregator): the Alphabet instance
// lives in `<domain>/internal/<domain>vocab`, importable only inside
// the domain; a single-family domain inlines its types in the family's
// registry.Vocab closure and grows an alphabet when its second family
// arrives.

package registry

import (
	"sort"
	"strings"

	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/ext"
	"github.com/euc-ai/xugo/prover/proof"
)

// Alphabet is one domain's statement alphabet. Construct with
// NewAlphabet and the Const/PolyConst builders at package-var time.
type Alphabet struct {
	domain  string
	elem    string // the element type variable, if the domain has one
	entries map[string]alphabetEntry
}

type alphabetEntry struct {
	typ     func() core.HolType
	nullary bool
}

// NewAlphabet starts an empty table. The domain name appears in every
// panic message, so a chapter reaching for a name the domain never
// typed is told whose table it hit.
func NewAlphabet(domain string) *Alphabet {
	return &Alphabet{domain: domain, entries: map[string]alphabetEntry{}}
}

// Over names the domain's ELEMENT type variable — the one every
// polymorphic entry in the table is written over. Only a domain that
// HAS one declares it (an ℤ alphabet's constants are monomorphic and
// says nothing here), and only PinnedAt reads it.
func (a *Alphabet) Over(varName string) *Alphabet {
	a.elem = varName
	return a
}

// Const records name at typ. typ is a FUNCTION so every declaration
// mints fresh type-variable instances rather than sharing one.
func (a *Alphabet) Const(name string, typ func() core.HolType) *Alphabet {
	return a.add(name, typ, false)
}

// PolyConst records a NULLARY name. Declaration registers it
// polymorphically — see this file's header for why a pinned instance
// would be wrong — and its build handle comes from Pinned, at the
// build site.
func (a *Alphabet) PolyConst(name string, typ func() core.HolType) *Alphabet {
	return a.add(name, typ, true)
}

func (a *Alphabet) add(name string, typ func() core.HolType, nullary bool) *Alphabet {
	if _, dup := a.entries[name]; dup {
		panic(a.domain + " alphabet: " + name + " recorded twice")
	}
	a.entries[name] = alphabetEntry{typ: typ, nullary: nullary}
	return a
}

// Declare registers the named constructors into ctx's ParseScope at the
// domain's types. It panics on a name the table does not carry — a
// chapter reaching for a constructor the domain has never typed is an
// authoring error, and the alternative (declaring nothing and letting
// the DSL's def-less meta answer) is the silent failure the table
// exists to prevent.
func (a *Alphabet) Declare(ctx *proof.Script, names ...string) {
	for _, n := range names {
		e := a.entry(n)
		if e.nullary {
			ctx.PolyConst(n, e.typ())
			continue
		}
		ctx.Const(n, e.typ())
	}
}

// Term declares name PINNED at the alphabet's type and returns its
// build handle. A nullary name is pinned too — whether a chapter wants
// the pin is the chapter's own statement (VocabSpec's Term row) rather
// than a fact about the type: a pin fixes ONE instance for every
// statement the chapter parses, which is what a chapter naming `nil`
// beside an `A`-lettered term needs, and what a chapter naming `∅` at
// two levels at once cannot have. The latter declares it polymorphically
// instead — the Poly row, whose build handle is Pinned.
func (a *Alphabet) Term(ctx *proof.Script, name string) *ext.TermWrapper {
	return ctx.Const(name, a.entry(name).typ())
}

// DeclarePinned declares the named constants PINNED at the alphabet's
// types — Term's declaration half, for the statement-only side of a
// Term row.
func (a *Alphabet) DeclarePinned(ctx *proof.Script, names ...string) {
	for _, n := range names {
		ctx.Const(n, a.entry(n).typ())
	}
}

// Pinned returns the build handle for a NULLARY name, pinned at the
// domain's generic instance. Build sites run after the member's
// statements have parsed, which is what makes the pin harmless there.
func (a *Alphabet) Pinned(ctx *proof.Script, name string) *ext.TermWrapper {
	e := a.entry(name)
	if !e.nullary {
		panic(a.domain + " alphabet: " + name + " is not nullary — take its handle " +
			"with Term, in the vocabulary hook")
	}
	return ctx.Const(name, e.typ())
}

// PinnedAt is Pinned at a CHOSEN element type, for a chapter whose
// statements live on both sides of a map and so need the same nullary
// name at two instances at once. Pinned answers only at the table's own
// element type variable, which left such a chapter with no route
// through the domain table at all — it had to spell the constant as
// raw `⟨A:…⟩` DSL text, the one thing the Alphabet exists to prevent.
//
// Calling it twice at different types is the point and is safe:
// Script.Const returns the handle at whatever type it is asked for, and
// pins only the FIRST into ParseScope.Consts while always refreshing
// ParseScope.ConstMetas — so a statement's own `⟨A:…⟩` annotation keeps
// resolving through the polymorphic path.
func (a *Alphabet) PinnedAt(ctx *proof.Script, name string, elem core.HolType) *ext.TermWrapper {
	e := a.entry(name)
	if !e.nullary {
		panic(a.domain + " alphabet: " + name + " is not nullary — take its handle " +
			"with Term, in the vocabulary hook")
	}
	if a.elem == "" {
		panic(a.domain + " alphabet: PinnedAt needs the domain's element type variable — " +
			"declare it with Over(\"…\") on the table, or use Pinned for the generic instance")
	}
	typ := e.typ().Substitute(core.MakeTypeSubst(core.MakeVarType(a.elem), elem))
	return ctx.Const(name, typ)
}

// Known lists the typed names, sorted — for the panic messages and for
// a chapter checking what the domain already carries.
func (a *Alphabet) Known() []string {
	out := make([]string, 0, len(a.entries))
	for n := range a.entries {
		out = append(out, n)
	}
	sort.Strings(out)
	return out
}

func (a *Alphabet) entry(name string) alphabetEntry {
	if e, ok := a.entries[name]; ok {
		return e
	}
	if e, ok := mintedEntry(name); ok {
		return e
	}
	panic(a.domain + " alphabet: no type recorded for " + name +
		" — known names: " + strings.Join(a.Known(), ", "))
}

// mintedEntry is the alphabet entry a registered constant supplies
// for itself: its one authoritative type is its mint, so a domain
// table need not (and, once the constant is minted in a chapter,
// should not) spell it. A nullary polymorphic constant — the ∅-class —
// is recognized off the type, as the table's PolyConst rows are.
func mintedEntry(name string) (alphabetEntry, bool) {
	meta, ok := GetConstMetaManager().LoadConstMeta(core.TermName(name))
	if !ok || meta.IsZero() {
		return alphabetEntry{}, false
	}
	absType := meta.AbsType()
	return alphabetEntry{
		typ:     func() core.HolType { return absType },
		nullary: !ext.IsFunType(absType) && len(absType.TypeVars()) > 0,
	}, true
}

// mintedAlphabet is the alphabet a chapter with no domain table
// declares through: every name resolves to its mint. Term / Declare /
// Pinned read as they do on a table.
var mintedAlphabet = &Alphabet{domain: "minted", entries: map[string]alphabetEntry{}}
