// vocab.go — the chapter's statement vocabulary: the constants this
// chapter mints, and the names from the list, pair, relation and group
// chapters its statements spell.

package free_group

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data — one row per name, each typed
// by its mint. The list chapter's constants are declared at their own
// letter, as that chapter mints them; a statement here reads them at
// words — `cons(x, nil)` with x a letter puts nil at the empty word —
// because the text DSL re-reads a declared constant at the instance an
// application fixes for it.
var vocab = registry.NewVocabSpec(nil).
	OpsName("freeGroupOps").
	// The chapter's own constants.
	Term("letter_inverse").     // prod(A, bool) → prod(A, bool)
	Term("word_inverse").       // list(prod(A, bool)) → list(prod(A, bool))
	Term("word_equiv").         // list(prod(A, bool)) → list(prod(A, bool)) → bool
	Term("free_group_of_word"). // list(prod(A, bool)) → free_group(A): the class map, ⁅w⁆
	Term("mk_free_group").      // set(list(prod(A, bool))) → free_group(A)
	Term("dest_free_group").    // free_group(A) → set(list(prod(A, bool)))
	Term("free_one").           // free_group(A)
	// The list chapter's: words are lists of letters.
	Term("nil").
	Term("cons").
	Term("list_append").
	Term("list_reverse").
	Term("list_map").
	// The pair chapter's: a letter is a generator and a sign.
	Term("fst").
	Term("snd").
	// relations/equivalence's predicate the quotient is taken by, and
	// the group chapter's structure the chapter instantiates.
	Term("equivalence").
	Term("group")

// FreeGroup is `free_group(A)` as a phantom of the typed term surface —
// the type-level twin of the chapter's carrier, declared beside it per
// the phantom vocabulary's decentralization rule (ext/holtype_phantom.go).
// A signature over the chapter reads `Typed[FreeGroup[A]]` exactly as
// its statement reads `g:free_group(A)`; the typed-wrapper generator
// (gen_family) spells the type through it.
type FreeGroup[Elem ext.TypePhantom] struct{}

func (FreeGroup[Elem]) Reify() ext.HolType { return MakeType("free_group", ext.HolTypeOf[Elem]()) }
