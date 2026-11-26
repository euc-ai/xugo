// vocab.go — the chapter's alphabet, declared once and handed back.
//
// The text-DSL parses `(a, b)` literals on its own, but its comma meta
// is def-LESS, and this chapter's whole method is definitional
// unfolding. Declaring the def-CARRYING metas is what puts them where
// scope-first resolution looks, so a member can unfold `(x, y)` down
// to the construction when its proof needs to.
//
// The generated `ops` (zz_vocab_gen.go) hands the same declarations
// back as values, so no constant's type is spelled twice in the
// package: the chapter's own mints (definitions.go) are read through
// their metas, at THIS chapter's instance (A, B) — the one its own
// statements are written at. A member or a consumer working at some
// other instance asks alphabet.go for it instead. A constant is declared
// here when a member states it, never in advance.
//
// This file is the alphabet AT THIS CHAPTER'S INSTANCE. The same
// alphabet parameterized by component types — what every consumer of
// `prod` needs — is alphabet.go.

package pairs

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// patternAbstractionType is pattern_abstraction's OWN polymorphic type rather than a pair instance:
// it is the generic choose-something-satisfying operator, and the pair
// enters only through the predicate it is applied to — which is why
// the type variable is a fresh one rather than either component. No
// statement in the chapter names it (`λ(x, y). body` is the surface
// the DSL lowers into it), but that surface is def-less, so a member
// that has to unfold the abbreviation needs the def-carrying constant
// declared for scope-first resolution to find.
func patternAbstractionType() HolType {
	chosen := MakeVarType("X")
	return MakeFun(MakeFun(chosen, TypeBool), chosen)
}

// vocab is the chapter alphabet as data — one row per name. Members
// bind the generated handles as `op`.
var vocab = registry.NewVocabSpec(nil).
	OpsName("pairOps").
	Spelled("pattern_abstraction", patternAbstractionType).
	Term("mk_pair").       // A → B → (A → B → bool): a pair as a predicate
	Term("mk_prod").       // (A → B → bool) → prod(A, B)
	Term("dest_prod").     // prod(A, B) → (A → B → bool)
	Term(",").As("Pair").  // A → B → prod(A, B): the `,` of `(x, y)`
	Term("fst").As("Fst"). // prod(A, B) → A
	Term("snd").As("Snd")  // prod(A, B) → B

// GraphOf is `mk_pair(x, y)` — the predicate encoding the pair (x, y),
// and the term the membership criterion is taken at whenever a proof
// descends from two components.
func (v *pairOps) GraphOf(x, y Term) Term { return v.MkPair.Apply(x, y) }

// GraphOfPair is `dest_prod(p)` — the predicate a pair of the type
// carries, which is where membership is taken instead when the proof
// starts from an arbitrary pair.
func (v *pairOps) GraphOfPair(p Term) Term { return v.DestProd.Apply(p) }
