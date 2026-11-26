// definitions.go — the chapter's definitional layer: the term-level
// carrier's four constants, each through the define door.
//
// A dimensioned tuple is an ordinary function `num → A` whose entries
// beyond the active range 0..n-1 are pinned to `junk`. The chapter
// OWNS that convention as four constants — the membership predicate and
// the three block operations. Each equation is read in the chapter's own
// vocabulary and the kernel mints the constant with its defining theorem
// ⊢ c = λ…, which is what `ctx.ConstDef`/`ConstDefNormalized` and the
// rewrite steps consume; the entry is the characterizing statement a
// proof cites.
//
// The active range is 0-based (`i < n`): the range guard is ONE atom,
// the value substrate the chapter meets (nat_div/nat_mod digits, the words
// face's bit positions, window sums) is exponent-indexed from 0, and
// `tuple_drop` needs no COND at all — the high block is bare
// precomposition past the cut, its own high end junk by the SOURCE's
// membership. The type-level statements these members mirror index their
// components from 1; the dimension translation carries that difference
// mechanically — a change of index variable, folded into the guards and
// access positions it emits.

package carrier

import (
	"github.com/euc-ai/xugo/core"
	"github.com/euc-ai/xugo/library/registry"

	// functions mints junk, the default the tuples are pinned to, which
	// the equations here spell: the import initializes the mint before
	// they are parsed.
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
)

// TupleDef — membership in the n-dimensional carrier: junk past the
// active range.
var TupleDef = tupleDefThm{family.Define(registry.DefEntry{
	Name:      "TupleDef",
	Key:       "prop_680bad2fefef3a7b",
	Const:     "tuple",
	Type:      "num → (num → A) → bool",
	Equations: []string{"∀n:num. ∀f:(num → A). tuple(n, f) ⇔ ∀i:num. ¬(i < n) ⇒ f(i) = junk"},
})}

// TupleCatDef — concatenation at a cut: the active low range reads
// the first tuple, everything past it reads the second at the offset.
var TupleCatDef = tupleCatDefThm{family.Define(registry.DefEntry{
	Name:  "TupleCatDef",
	Key:   "prop_5990eeb2169c5441",
	Const: "tuple_cat",
	Type:  "num → (num → A) → (num → A) → num → A",
	Equations: []string{
		"∀m:num. ∀u v:(num → A). ∀i:num. tuple_cat(m, u, v, i) = COND(i < m, u(i), v(i - m))",
	},
})}

// TupleTakeDef — the low block, which is also the chapter's
// normalizer: it truncates any function into the n-dimensional
// carrier.
var TupleTakeDef = tupleTakeDefThm{family.Define(registry.DefEntry{
	Name:      "TupleTakeDef",
	Key:       "prop_c8810e53f10510bb",
	Const:     "tuple_take",
	Type:      "num → (num → A) → num → A",
	Equations: []string{"∀n:num. ∀u:(num → A). ∀i:num. tuple_take(n, u, i) = COND(i < n, u(i), junk)"},
})}

// TupleDropDef — the high block at cut m: bare precomposition past the
// cut. No COND: 0-based, the high block STARTS at the cut, and past
// the source's own range the source holds junk itself — membership
// closure needs no case of its own.
var TupleDropDef = tupleDropDefThm{family.Define(registry.DefEntry{
	Name:      "TupleDropDef",
	Key:       "prop_fc91633c446d094d",
	Const:     "tuple_drop",
	Type:      "num → (num → A) → num → A",
	Equations: []string{"∀m:num. ∀u:(num → A). ∀i:num. tuple_drop(m, u, i) = u(i + m)"},
})}

// The minted metas the proofs build terms over (vectors.go). Each is
// read through mintedMeta, whose first argument is the DEFINITION: an
// initialization-order edge Go can see, so the mint has run first.
var (
	TupleMeta    = mintedMeta(TupleDef, "tuple")
	TupleCatMeta = mintedMeta(TupleCatDef, "tuple_cat")
)

// mintedMeta returns the named constant's meta, ordered after the
// definition that mints it. The entry is the ordering edge and is not
// otherwise read.
func mintedMeta(_ registry.EntryLike, name string) core.ConstTermMeta {
	return constMeta(name)
}
