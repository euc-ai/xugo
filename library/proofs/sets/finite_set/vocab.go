// vocab.go — the chapter's statement vocabulary.
//
// Two groups, and the split is not cosmetic. The set constructors come
// from the domain table (`internal/setvocab`), because their types are a
// fact about the domain. `finite` is declared HERE, at its type, because
// it is not a constructor and the domain table will not take it: every
// name in setvocab is one the `set_tac` driver unfolds, and the driver
// has no notion of finiteness (setvocab_test.go pins that containment).
//
// The containment is the interesting half: it says the driver's reach
// and this chapter's subject are disjoint by construction, which is why
// no member here is settled by `set_tac` alone and yet it stays the
// right tool for a leaf that is genuinely about constructors. The README
// carries the rest of that story.

package finite_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// A set of A's IS its membership predicate — the domain's convention,
// and the element type this chapter states everything over.
//
// A statement naming these two types in TEXT writes them `∅⟨A:A⟩` and
// `∅⟨A:set(A)⟩` (finite_set.go's consts), and the first of those looks
// like it says nothing, so read the annotation once here. `∅` is
// nullary: a text carries no argument for it to read its type from, and
// where the surrounding text cannot pin it either, the annotation does.
// `⟨A:τ⟩` substitutes τ for the type variable named A IN THE CONSTANT'S
// OWN declaration — every constant's annotation names that constant's
// slots — so it reads "the empty set of τ's". empty_set happens to call its
// slot A, and so does this chapter, and the two A's are unrelated:
// `∅⟨A:A⟩` sets empty_set's slot to the chapter's element type, which is a
// real instruction and not the tautology it resembles. The letter cannot
// be changed, a constant having no slot but the one it declared.
//
// A chapter wanting just one instance pins the name at a type instead
// (`setvocab.Pinned`/`PinnedAt`), and this one does that too. The
// annotation is what a statement reaches for when it wants BOTH levels,
// since a pin answers at one.
func elemType() HolType { return MakeVarType("A") }
func setType() HolType  { return MakeFun(elemType(), TypeBool) }

// The same alphabet as phantom spellings — the type arguments a
// wrapper cite (`FiniteSubset.Inst[elementSet]()`) takes. element is
// the chapter's point type; elementSet a set of points, the type a
// law is instantiated at when its "elements" are themselves sets (the
// collections finite_set.go counts).
//
// The chapter states everything at the element type, but several
// arguments live on two levels at once — a powerset whose subject is
// a collection while its induction runs over a set, a family of
// fibres cut out of a finite set of values. A cross-level cite
// instantiates the law FIRST (the wrapper's `Inst`, letters read off
// the stated form) and grounds the instance: a bare ground cite would
// check its witnesses against binders still carrying the element
// type, and the specialize fails.
type (
	element    = A
	elementSet = Set[element]
)

// vocab is the chapter alphabet as data: the family installs it into
// every member's ParseScope (family.go's WithVocabSpec), and the vocab
// generator renders the build surface — finiteOps, the constants a
// member BUILDS terms with — from the same rows (zz_vocab_gen.go). One
// declaration is the point: a chapter that spelled a type once for the
// parser and again for its builders would have two copies that nothing
// keeps in agreement.
//
// A name is declared when a member STATES it, never in advance — an
// undeclared name still parses (the text-DSL carries its own def-less
// metas for `∈ ∅ ⊆`), so a speculative entry buys nothing and quietly
// claims the chapter reaches a notion it does not. The list therefore
// grows one packet at a time, and every entry below is carried by a
// member's own headline.
//
// No member builds a term over finite, though it is the chapter's
// subject: even FiniteInductFresh's induction predicate
// `λa. finite(a) ∧ P(a)` is a compound witness, spelled with
// `ctx.TermText`, which resolves finite from the very ParseScope these
// rows populate.
var vocab = registry.NewVocabSpec(setvocab.Table()).
	OpsName("finiteOps").
	Poly("empty_set").  // the base of every induction here
	Term("set_member"). // FiniteInductFresh's step rule assumes x ∉ s
	Term("subset").     // finiteness descends along ⊆ (finite_set.go)
	// image is the subject of the map part, and the one name in this chapter
	// carrying a second element type — the domain table declares it
	// at `(A → B) → set(A) → set(B)`, so the chapter states
	// image members over A and B without pinning B itself.
	Term("image").
	// big_union is a families subject, and the one that crosses levels
	// DOWNWARD: it takes a COLLECTION of sets to a set of points, so
	// a member stating it speaks at both of the chapter's type levels
	// at once. FiniteUnions and FiniteFiniteUnions state it.
	Term("big_union").
	// big_intersection is big_union' dual and arrives with it, for the pair of
	// members that read a finite CHAIN of sets: a chain has a largest
	// and a smallest member, and those are exactly its union and its
	// intersection.
	Term("big_intersection").
	// proper_subset is the ordering's strict part, and the chapter states
	// it for one purpose: descent. Every induction above walks a
	// finite set UP from ∅ along insert; the descent principle walks
	// it DOWN, and what makes that walk terminate is that ⊊ has no
	// infinite descending chain below a finite set.
	Term("proper_subset").
	// finite is declared at an explicit type so a headline pins the
	// element variable rather than letting inference freshen a second
	// one: `finite(∅)` with both names left open is a strictly weaker
	// proposition that parses, normalizes and PRINTS identically.
	// (Spelled, not Term: the domain table will not take it — see the
	// header.)
	Term("finite").
	// infinite, the same way and for the same two reasons.
	Term("infinite").
	// Insert is `insert : A → set(A) → set(A)`, the one
	// construction finite is closed under.
	Term("insert").
	// Union is `union`, the first construction the closure tier carries
	// finiteness across; finite_set.go grounds the insert rule at `u ∪ t`.
	Term("union").
	// Inter, Diff and Delete are the constructions that only ever SHRINK
	// a set. Each closure-tier member built over one of them has to name
	// the shrunk set as a term, because that is the `small` witness of
	// its `At(FiniteSubset, small, big)` — which is the whole tier's one
	// move.
	Term("intersection").Term("set_difference").Term("delete")

// The chapter's set-side closes go to `BySets`. No member here is one
// call to it and no headline here goes to it outright: finite is not in
// the driver's vocabulary and cannot be, so every member has spent its
// finiteness by other means before the driver is reached. (A member may
// still END on it, over premises already in hand.)
//
// What it closes is a leaf genuinely about the constructors, and those
// are a CLASS, not a list — deliberately stated without counts or an
// enumeration, because both go stale on the next packet and have twice
// been corrected here: inclusions, memberships in a construction, and
// quantified forms of either.
