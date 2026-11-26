// vocab.go — the chapter's statement vocabulary, and its two closers.
//
// The alphabet is the set language this chapter reads image through:
// membership, the empty set, the element-wise pair, the three binary
// operations, the ordering, the two big operators — and image itself,
// the only name here that carries a second element type, since a map
// between sets need not be an endofunction. `universe` has no row:
// members state `𝕌` — a map's range, injectivity outright, the whole
// preimage — at the instance their arguments give it, which needs none,
// and the preimage part's proofs take it from the domain table at the
// two types they ask for (set_image.go, "The sets these proofs build").
// A name is declared when a member needs its row, never in advance,
// since a speculative entry quietly claims the chapter meets a notion it
// does not.
//
// Every set name here is defined in set_basic (its definitions.go),
// and its TYPE is read off that mint through the Alphabet's fallback;
// the sets domain's setvocab table carries only the two nullary rows.
// The NAMES are declared here because which constructors a chapter
// states is a statement about that chapter: a constructor is declared
// when a member states it. The text-DSL parses `∈ ⊆ ∪ ∩ ∖ ⋃ ⋂ ∅` and
// the set-builder on its own (ext/dsl/setops.go) and resolves each
// name a surface form lowers to through the family's resolver to the
// mint's def-carrying meta, so an undeclared name still parses.
//
// `identity_map` and `o` are function combinators, not set constructors: they
// are defined in sets/functions (IdentityApply, ComposeApply), which
// this chapter imports, and are declared here by name like the rest.
// `ImageI` and `ImageCompose` do unfold their combinator on the way to
// the close, but `Unfold` takes the NAME and resolves it out of the
// scope the family's install populated, so no member ever builds a
// term over either one.

package set_image

import (
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// vocab is the chapter alphabet as data: the family installs it into
// every member's ParseScope (family.go's WithVocabSpec), and the vocab
// generator renders the build surface from it (zz_vocab_gen.go). The
// set names' types go through setvocab, a fact about the domain rather
// than about this chapter.
var vocab = registry.NewVocabSpec(setvocab.Table()).
	OpsName("setImageOps").
	// membership — what every law is read through
	Term("set_member").
	Poly("empty_set"). // the empty image
	// the recursion clause, and the injective delete law
	Term("insert").Term("delete").
	// the three binary operations image passes through
	Term("union").Term("intersection").Term("set_difference").
	Term("subset").                             // the monotonicity and subset-image laws
	Term("big_union").Term("big_intersection"). // the two big operators
	Term("image").                              // the chapter's subject
	Term("identity_map").                       // the identity combinator
	Term("o").                                  // composition, `∘`
	// the preimage: the witness the image parts build, and the last part's subject
	Term("preimage_on")

	// --- The terms this chapter BUILDS -------------------------------------
	//
	// The last three parts' proofs are the only ones that have to produce a
	// set rather than unfold one. The shapes are the one-point set `{y}`,
	// the preimage restricted to a source set (`preimage_on(src, f, tgt)`
	// — the LARGEST set whose image lies in `tgt`, which is what makes it
	// the canonical witness wherever a subset has to be produced) or whole
	// (`preimage_on(𝕌, f, tgt)`), and an image offered as a witness. All
	// of them are TEXT: `{y}` abbreviates an `insert(y, ∅)` whose nullary
	// `∅` only the parser can instantiate off `y`, and the preimage's `𝕌`
	// is the same case. `BySets` reads `preimage_on` as its membership
	// condition, so a witness needs no unfolding. Each site writes the
	// literal via `a.Term`, which resolves the block's surface names; a
	// misspelled name fails loudly at the parse. The preimage part also
	// cites its laws at `∅` and `𝕌` themselves, at the map's source and
	// target both, and those it pins from the domain table instead.
