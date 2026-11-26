// vocab.go — the chapter's statement vocabulary, and its one closer.
//
// One alphabet, polymorphic in the element type A: a set is its
// membership predicate `A → bool` (`set(A)` in text), and every constructor below is
// introduced as a comprehension over that.
//
// The constructors are this chapter's own definitions
// (definitions.go), and each name's TYPE is read off its mint — the
// one authoritative source of it — through the Alphabet's fallback;
// the sets domain's setvocab table carries only the two nullary rows,
// empty_set and universe, which a chapter must declare polymorphically. The
// NAMES are declared here because which constructors a chapter states
// IS a statement about that chapter: the list grows one tier at a
// time, and a constructor is declared when a member states it, never
// in advance. The text-DSL parses `∈ ∪ ∩ ∖ ∅ 𝕌 ⊆ {…|…}` on its own
// (ext/dsl/setops.go) and resolves each name a surface form lowers to
// through the family's resolver to the mint's def-carrying meta, so an
// undeclared name still parses; a speculative entry buys nothing and
// quietly claims the chapter meets a notion it does not yet.

package set_basic

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// vocab is the chapter alphabet as data: the family installs it into
// every member's ParseScope (family.go's WithVocabSpec), and the vocab
// generator renders the build surface from it (zz_vocab_gen.go).
var vocab = registry.NewVocabSpec(setvocab.Table()).
	OpsName("setOps").
	Term("set_member").                                        // membership itself
	Poly("empty_set").Poly("universe").                        // the two constant sets
	Term("insert").                                            // adding one element
	Term("union").Term("intersection").Term("set_difference"). // the binary operations
	Term("image").                                             // the image of a set under a map
	Term("big_union").Term("big_intersection").                // the big operators, over a set OF sets
	// removing one element — built, not just stated
	Term("delete")

// emptySet is ∅ at the chapter's element type, for the one member that
// case-splits on a set BEING empty rather than merely stating it. A
// nullary handle is taken at the build site (setvocab.Pinned), never in
// the hook — pinned before parsing it would shadow the polymorphic ∅.
func emptySet(ctx *proof.Script) Term {
	return setvocab.Pinned(ctx, "empty_set")
}

// deleteFrom builds `delete(s, x)` — the one term this chapter has to
// construct rather than merely name. It is the witness that makes
// Decomposition work: what is left of s once x is taken out.
func deleteFrom(ctx *proof.Script, s, x Term) Term {
	return ops(ctx).Delete.Apply(s, x)
}
