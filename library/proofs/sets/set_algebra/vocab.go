// vocab.go — the chapter's statement vocabulary, and its two closers.
//
// The alphabet is the constructions themselves: the two constant sets,
// the element-wise pair, the three binary operations, the two big
// operators, and the one relation this chapter states about them. What
// the chapter does NOT name is the ordering — no member here mentions ⊆.
// An algebra of sets speaks in equations.
//
// Every name here is defined in set_basic (its definitions.go), and
// its TYPE is read off that mint through the Alphabet's fallback; the
// sets domain's setvocab table carries only the two nullary rows. The
// NAMES are declared here because which constructors a chapter states
// is a statement about that chapter: a constructor is declared when a
// member states it, never in advance. The text-DSL parses
// `∈ ∪ ∩ ∖ ⋃ ⋂ ∅ 𝕌` on its own (ext/dsl/setops.go) and resolves each
// name a surface form lowers to through the family's resolver to the
// mint's def-carrying meta, so an undeclared name still parses.
//
// `empty_set` and `universe` are registered polymorphically rather than at a
// pinned instance — the Poly rows — and this chapter is the one that
// most needs it: nine members instantiate the vocabulary at two type
// levels in a single statement (`⋃∅ = ∅` names a constant set of each
// kind in five characters), which a pinned instance cannot spell.

package set_algebra

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
	OpsName("setAlgebraOps").
	// membership — what every law is read through
	Term("set_member").
	Poly("empty_set").Poly("universe").                        // the lattice's bottom and top
	Term("insert").Term("delete").                             // adding one element, removing one
	Term("union").Term("intersection").Term("set_difference"). // join, meet, and the asymmetric one
	Term("big_union").Term("big_intersection").                // join and meet at arbitrary arity
	Term("disjoint")                                           // meeting in nothing

// setTacExpand runs the driver's FULL-EXPANSION mode instead of the
// membership mode `BySets` runs. Membership mode reduces to a first-order
// residual about points; full expansion computes at the λ level, and
// some goals are only settled there. Four members of this chapter need
// it: the conditional laws (InsertUnion, InsertInter, InsertDiff,
// DeleteInsert), whose right-hand side is a set-valued COND —
// pushing an inserted element through a binary operation has to ask
// whether the element is already on the other side, and the answer
// is a set, which the membership residual keeps opaque. (The two-member
// cases UnionsPair and IntersPair once stood here too; their siblings'
// recursion and singleton laws compute them without a driver.)
//
// That list is measured, not derived: which mode a goal needs is a fact
// about its residual that only running both reveals. The helper spells
// the exact-mode form, not the door `SetTac()` that tries membership
// first, because a recorded step should be what the file says it is.
func setTacExpand() proof.Step {
	return SetTacLegacy()
}
