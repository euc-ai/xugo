// definitions.go — the chapter's definitional layer: the product type
// and the constants stated over it, minted here.
//
// `prod(A, B)` is carved out of `A → B → bool`: a pair is encoded by
// the two-argument predicate holding of exactly its own components,
// `mk_pair(x, y) = λa b. a = x ∧ b = y`, and the type is declared to be
// in bijection with the predicates of that shape. The bijection is the
// pair mk_prod / dest_prod, and the two facts it comes with —
// ProdDef.Retraction and ProdDef.Membership — are this chapter's entire
// foundation: nothing here cites a theorem, which is what lets
// the chapter's floor carry no dependencies at all.
//
// The type's inhabitation is trivial — any mk_pair(a, b) has the pair
// shape — and is proved at the mint by normalization: the two axioms
// are derived from that certificate, never trusted.
//
// The pairing constructor `(x, y)` is `mk_prod(mk_pair(x, y))`; its
// name is `,`, which the text DSL cannot spell in head position, so
// its equation spells the stand-in `pair`. The projections are choice
// terms, and pattern_abstraction — the abstraction a pair-pattern λ lowers to — is a
// choice over the functions meeting a predicate.

package pairs

import (
	"github.com/euc-ai/xugo/library/registry"
)

// MkPairDef — a pair, encoded: the predicate holding of exactly (x, y).
var MkPairDef = mkPairDefThm{family.Define(registry.DefEntry{
	Name:      "MkPairDef",
	Key:       "prop_3e6981d6626ad19e",
	Const:     "mk_pair",
	Type:      "A → B → A → B → bool",
	Equations: []string{"∀x:A. ∀y:B. mk_pair(x, y) = λa:A. λb:B. a = x ∧ b = y"},
})}

// ProdDef — the product type: the predicates of the pair shape, made a
// type. ProdDef.Retraction (`mk_prod(dest_prod(p)) = p`) and
// ProdDef.Membership (`(∃a b. r = mk_pair(a, b)) ⇔ dest_prod(mk_prod(r)) = r`)
// are the two facts the type definition comes with.
var ProdDef = family.DefineType(registry.TypeEntry{
	Name: "Prod",
	Type: "prod",
	Abs:  "mk_prod",
	Rep:  "dest_prod",
	Pred: "λr:(A → B → bool). ∃a:A. ∃b:B. r = mk_pair(a, b)",
	Deps: []registry.EntryLike{MkPairDef},
})

// PairDef — the pairing constructor: a pair is the abstraction of its
// encoding. Named `,`, spelled `pair` in the equation.
var PairDef = pairDefThm{family.Define(registry.DefEntry{
	Name:      "PairDef",
	Key:       "prop_c4551e3dad7c7092",
	Const:     ",",
	Spelled:   "pair",
	Type:      "A → B → prod(A, B)",
	Equations: []string{"∀x:A. ∀y:B. pair(x, y) = mk_prod(mk_pair(x, y))"},
	Deps:      []registry.EntryLike{ProdDef.Retraction},
})}

// FstDef — the first projection: the x for which p is (x, z) for some z.
var FstDef = fstDefThm{family.Define(registry.DefEntry{
	Name:      "FstDef",
	Key:       "prop_45246c9c1323346e",
	Const:     "fst",
	Type:      "prod(A, B) → A",
	Equations: []string{"∀p:prod(A, B). fst(p) = εx:A. ∃y:B. p = (x, y)"},
	Deps:      []registry.EntryLike{PairDef},
})}

// SndDef — the second projection: the y for which p is (z, y) for some z.
var SndDef = sndDefThm{family.Define(registry.DefEntry{
	Name:      "SndDef",
	Key:       "prop_e78525168d9e6d7b",
	Const:     "snd",
	Type:      "prod(A, B) → B",
	Equations: []string{"∀p:prod(A, B). snd(p) = εy:B. ∃x:A. p = (x, y)"},
	Deps:      []registry.EntryLike{PairDef},
})}

// PatternAbstractionDef — the generalized abstraction a pair-pattern λ lowers to: a
// choice among the functions meeting the pattern's predicate.
var PatternAbstractionDef = patternAbstractionDefThm{family.Define(registry.DefEntry{
	Name:      "PatternAbstractionDef",
	Key:       "prop_a8adce5078967942",
	Const:     "pattern_abstraction",
	Type:      "(A → bool) → A",
	Equations: []string{"∀P:(A → bool). pattern_abstraction(P) = εx:A. P(x)"},
})}
