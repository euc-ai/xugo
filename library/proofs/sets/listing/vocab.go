// vocab.go — the chapter's statement vocabulary.
//
// The set constructors come from the domain table
// (`internal/setvocab`), because their types are a fact about the
// domain; the count is declared here as the cardinality chapter
// declares it, the domain table taking only names the `set_tac`
// driver unfolds; the list names are `datatypes/list`'s, declared
// here because this is the chapter that states lists and sets in one
// sentence.
//
// The chapter states more names than it declares — list_member, list_append, list_map,
// list_reverse, finite, has_size, distinct, list_sum and nat_sum appear in
// members with no row — and that is the rule, not an oversight: a
// stated name resolves through the mint at the instance its arguments
// give it, and a row buys a PINNED instance or a HANDLE
// (chapter_constitution.md, "What a row buys"). The rows
// below are handles the bodies build with (nil, cons, insert, the two
// constants) and the count and length the choice function's statement
// pins; a row here that is neither is a pin nobody needs.

package listing

import (
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/registry"
)

var vocab = registry.NewVocabSpec(setvocab.Table()).
	OpsName("listingOps").
	Poly("empty_set"). // the set of the empty list
	Term("insert").    // the set of cons(h, t) is h laid into the set of t
	Term("card").      // list_of_set asks for a list as long as the count
	Term("nil").       // the two constructors the recursion runs over
	Term("cons").
	Term("list_length"). // the length list_of_set's choice pins
	// The chapter's own two constants.
	Term("set_of_list").
	Term("list_of_set")
