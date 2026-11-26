// vocab.go — the chapter's statement vocabulary.
//
// The alphabet is the ordering itself (⊆, ⊊) over sets of an
// unconstrained element type A, plus what a statement has to name on
// either side of it: membership, the two constant sets that bound the
// ordering, and — since the chapter also places the CONSTRUCTED sets in
// it — the constructions themselves.
//
// Every name here is defined in set_basic (its definitions.go), and
// its TYPE is read off that mint through the Alphabet's fallback; the
// sets domain's setvocab table carries only the two nullary rows. The
// NAMES are declared here because which constructors a chapter states
// is a statement about that chapter: a constructor is declared when a
// member states it, never in advance. The text-DSL parses
// `∈ ⊆ ∪ ∩ ⋂ ∅ 𝕌` on its own (ext/dsl/setops.go) and resolves each
// name a surface form lowers to through the family's resolver to the
// mint's def-carrying meta, so an undeclared name still parses; a
// speculative entry buys nothing and quietly claims the chapter meets
// a notion it does not yet.
//
// `empty_set` and `universe` are registered polymorphically rather than at a
// pinned instance — the Poly rows — and it matters here: this chapter
// needs ∅ at two levels, the empty set and the empty FAMILY of sets
// that IntersSubset's hypothesis rules out.

package set_order

import (
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data: the family installs it into
// every member's ParseScope (family.go's WithVocabSpec), and the vocab
// generator renders the build surface from it (zz_vocab_gen.go).
var vocab = registry.NewVocabSpec(setvocab.Table()).
	OpsName("setOrderOps").
	Term("set_member").                                        // membership itself
	Poly("empty_set").Poly("universe").                        // the ordering's bottom and top
	Term("subset").Term("proper_subset").                      // the ordering, and its strict part
	Term("insert").Term("delete").                             // adding one element, removing one
	Term("union").Term("intersection").Term("set_difference"). // meet, join, and the asymmetric one
	Term("big_intersection").Term("big_union")                 // meet and join at arbitrary arity
