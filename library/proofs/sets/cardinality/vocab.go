// vocab.go — the chapter's statement vocabulary.
//
// Three groups. The set constructors come from the domain table
// (`internal/setvocab`), because their types are a fact about the
// domain, not about this chapter. `finite` is declared here at its type
// for the same reason the parent chapter declares it — the domain table
// takes only names the `set_tac` driver unfolds, and the driver has no
// notion of finiteness. And the counting names are declared here because
// this is the chapter that states them.
//
// The parent declares finite too, and that is not duplication to remove:
// the two packages have separate parse scopes. A row buys a pinned
// instance or a handle, and a chapter declares one when it wants one
// of the two — not for every name its statements mention
// (chapter_constitution.md, "What a row buys"); the counting
// names below are handles the bodies build with.

package cardinality

import (
	"github.com/euc-ai/xugo/core"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/registry"
)

// A set of A's IS its membership predicate — the domain's convention,
// and the element type this chapter counts over. Members that relate two
// sets across a map state a second element type as a binder; nothing
// here needs it declared, because a pinned declaration is not rigid (see
// the counting names below).
func elemType() core.HolType { return MakeVarType("A") }
func setType() core.HolType  { return MakeFun(elemType(), TypeBool) }

// The same alphabet as phantom spellings — the type arguments a
// wrapper cite (`HasSizeZero.Inst[pair]()`) takes: element and value
// are the chapter's two letters, mapping the maps constructions.go counts,
// pair and splitPair the two pairings the pairs part and the
// function-space part of constructions.go construct. A law stated over ONE element type is read at each of
// these in turn, and the wrapper's explicit instance is what pins it
// there — at a BUILT type a bare ground cite leaves the law's own
// type variable standing, and the closer will not identify a variable
// with a built type; at the chapter's other letter the cite resolves
// at the wrong one and the premise cannot meet its term.
type (
	element   = A
	value     = B
	mapping   = Fun[element, value]
	pair      = Prod[element, value]
	splitPair = Prod[value, mapping]
)

// valueType is the second ELEMENT type: where a map sends this chapter's
// points. It coincides with accType only by accident of spelling — that
// one is what an iteration accumulates into, and the image members are
// not iterating — so they are kept apart, and a member counting across a
// map says which of the two it means.
func valueType() core.HolType { return MakeVarType("B") }

// accType is what an iteration over a set accumulates into — the type
// `set_fold` folds towards, and the only place in the chapter where a
// second type variable is part of a STATEMENT rather than of a binder.
// It is not the element type of a second set: `card` is the instance
// that matters here, and it accumulates into num.
func accType() core.HolType { return MakeVarType("B") }

// vocab is the chapter alphabet as data: the family installs it into
// every member's ParseScope (family.go's WithVocabSpec), and the build
// surface — countingOps, one handle per row — is rendered from the same
// rows (zz_vocab_gen.go). A name is declared when a member STATES it,
// never in advance — an undeclared name still parses, so a speculative
// entry buys nothing and quietly claims the chapter reaches a notion it
// does not.
//
// A handle exists for every row, so which constants a member BUILDS
// terms with is not a fact the struct carries — an unused field costs
// nothing. The distinction is in the row comments,
// and the pattern that EARNS a handle a build site is worth naming
// precisely, because what looks like the criterion is not it. A numeric
// law is GROUNDED at a count — so that count has to be built. Which law
// does not matter; being the witness does.
//
// "Grounded at", not "cannot close without": the union-and-difference part measured
// a site where the bare law closes too (see `+` below). A build site is
// earned by a member needing to NAME an instance, which is the
// ground-witness rule, and not by the closer failing without it.
// `has_size` has no build site at all: a member states a size and
// grounds its citations at the SET, so it is never a witness.
var vocab = registry.NewVocabSpec(setvocab.Table()).
	OpsName("countingOps").
	Poly("empty_set").  // a set of size zero is the empty one
	Term("set_member"). // the recursion step turns on whether an element is already present
	// insert: the recursion step turns on putting an element back — and
	// the enlargement is a handle that earned its build site late. Its
	// field read "insert is deliberately NOT here — every member states
	// an insertion and none builds one: a cite grounds at the point and
	// the set, and the enlargement is what the cited law returns." That
	// was true of every member up to the bounding part and is not true of
	// `ChooseSubsetStrong`, whose induction step EXHIBITS the enlarged
	// set as its existential witness and then grounds the size clause AT
	// it. Which is the trigger stated at `card` below: a law read at a
	// term makes that term a witness, and a witness has to be built.
	//
	// The distinction the old text was reaching for is still worth
	// keeping, because it is why this build site stayed absent so long: a
	// member that PROVES something about an insertion grounds at the
	// point and the set and never names the enlargement, while a member
	// that CONSTRUCTS one has to name it. Only the second needs the
	// handle, and this chapter had no member of the second kind until
	// it began choosing subsets rather than counting given ones.
	Term("insert").
	Term("subset"). // the pigeonhole compares a set with one that contains it
	// image: counting under a map is what the pigeonhole is about — and
	// it is built rather than statement-only because the counting members
	// read a cardinality law AT the image of a map, so `image(f, s)` is a
	// witness and not just a name they mention.
	Term("image").
	// union: counts add over a union — and the disjoint-union count is
	// proved by induction on one side, so the union it grows is a term a
	// cite has to be handed.
	Term("union").
	// intersection: …exactly when the intersection is empty. What two sets
	// share is the quantity the sum of two counts pays for twice, and
	// `CardUnionMinusOverlap` is the one member that names it: the
	// correction its headline subtracts is a count read AT the overlap.
	//
	// Both roles at that member, and the second is what earns the build
	// site. It NAMES the overlap in the split that reaches it, and it
	// GROUNDS the closing pair — the count of the overlap is one slot of
	// the monus law and one of the commutation that stands the sum ready
	// for it. Grounding there is not decoration: with both laws bare the
	// leaf falls through to a refutation and mints a key, and with the
	// two slots handed over it closes by substitution and mints none.
	Term("intersection").
	// set_difference: the comparison part splits a set at a subset — which is what
	// comparing two counts needs: the remainder of that split is a term
	// every step of it has to be handed — its finiteness, its
	// disjointness from the subset, and the union count read across the
	// two.
	Term("set_difference").
	Term("proper_subset"). // which compares by containment, strictly and not
	Term("disjoint").      // the union-and-difference part states its hypothesis this way once
	// delete is how a counting proof takes a set apart at a POINT —
	// remove a member, and the count drops by exactly one.
	Term("delete").
	// finite is declared at an explicit type so a headline pins the
	// element variable rather than letting inference freshen a second
	// one. It cannot be unfolded — the door refuses the closure form —
	// so finiteness arrives as a hypothesis or from a cited rule.
	Term("finite").
	// The counting names. `card(s)` is how many elements s has and
	// `has_size(s, n)` says that count is n; `suc` and `≤` come with
	// them, because the recursion clause counts up by one and the
	// pigeonhole compares two counts.
	//
	// Both are declared at this chapter's element type and both are
	// nonetheless stated at two element types at once — the pigeonhole's
	// equal-count hypothesis relates a set of A's to a set of B's. A
	// pinned declaration is not rigid: where a binder's type does not
	// fit, the parser falls through to the polymorphic meta this same
	// declaration registers, so the second element type needs no second
	// declaration and no annotation in the statement text.
	//
	// card is the count a numeric law is read at, and the one counting
	// name a member ever hands to a cite. It is the chapter's
	// most-built term. The laws it is read at span successor, order and
	// cancellation, which is why the trigger above is stated at "a
	// numeric law" rather than at any of them: the first two sites were
	// both successor laws, and reading that off as the rule was a
	// description of two instances rather than the invariant.
	//
	// It BUILDS only at the chapter's own element type. The parser's
	// fallthrough above is what lets a statement name a count at a
	// second element type; it does nothing for the handle, which is
	// pinned `set(A) → num`, so applying it to a set of B's — the
	// image of a map — fails in `core.Apply` with a bare
	// `Should not happen` and no type in the message. A member that wants
	// the image's count reaches it through `ctx.TermText`, where the
	// parser resolves the second element type; that yields a WITNESS and
	// not merely claim prose, and `maps.go`'s bound-under-a-map member
	// hands one to two order laws that way. Measured at the image part,
	// which is the first to relate two element types and not the last.
	Term("card").
	Term("has_size").
	Term("suc").
	Term("<=").As("Le").
	// `<` arrives with the union-and-difference part, and only there: a union whose
	// count falls SHORT of the sum is the one statement in the chapter
	// that needs the strict order, every other comparison being made at
	// `≤` or at an equation.
	Term("<").As("Lt").
	// `+` and `-` arrive with the calculus: counts add over a disjoint
	// union, and deleting a member drops one. `-` is stated only; `+`
	// became a build handle at the union-and-difference part, at two sites and for
	// two different reasons. `OverlapOfShortUnion` GROUNDS the strict
	// order at `card(s) + card(t)`, the sum its union is assumed to fall
	// short of; `CardUnionMinusOverlap` NAMES that same sum, which is
	// what the two splits add to and the one quantity its closing claim
	// states.
	//
	// The grounding site measured the bare law to close as well, so this
	// handle is not what makes that leaf close — which is the honest
	// reason to keep its build sites rather than a weaker one. Grounding
	// puts the contradiction (one term standing on both sides of a single
	// `<`) in the checked layer instead of in a comment, and that is the
	// ground-witness rule at a composition, not a necessity.
	// Everywhere a sum is merely stated — and that is most of this
	// chapter — it stays a name.
	//
	// `-` deliberately has no build site, and the difference members
	// confirm the choice: both state a difference in their headline and
	// neither forms one in its proof. Each grounds its closing laws at
	// the COUNTS — a remainder's and a subtrahend's — so every slot a
	// ground cite has to fill is a count, and the difference the theorem
	// states is built by the headline and nowhere else.
	Term("+").As("Plus").
	Term("-").As("Minus").
	// `*` arrives in the pairs part, where a rectangle's count is the
	// product of its sides' — the first place in the chapter where two
	// counts combine by anything but addition.
	//
	// Stated only, and NOT because no law here takes a product: three
	// sites hand one over. `HasSizeProductDependent`'s induction step
	// builds `m * n` and grounds `HasSizeUnion`'s count slot with it;
	// `HasSizeProductImage` grounds `HasSizeImageInj`'s at `m * n`; and
	// the function-space step grounds the size transfer's at
	// `n * nat_pow(n, m)` — the same naming-and-grounding pair that
	// earned `+` its build sites. Whether those sites earn `*` one too is
	// a live question for the chapter's members to answer; a vocabulary
	// declaration is the wrong place to settle it, because a claim about
	// how members BEHAVE cannot be checked from here.
	Term("*").As("Times").
	// `nat_pow` arrives with the function-space part: the maps from one
	// finite set into another number the codomain's size raised to the
	// domain's, which is the first count in the chapter that is neither
	// a sum nor a product. It is a FUNCTION and not an infix —
	// `nat_pow(n, m)` is nᵐ — and the infix spelling is a type error.
	//
	// Declared here because a member of that part states it. Whether it
	// also earns a build site is a question for the members, and this
	// comment does not answer it in advance: see the `*` note above for
	// why a vocabulary declaration must not carry a prediction about how
	// the part will use the name.
	Term("nat_pow").
	// `set_comprehension`/`comprehension_spec` are deliberately NOT declared, though the pairs and
	// powerset parts state both — a rectangle and a powerset are comprehensions
	// and there is no other way to write them. They resolve from the
	// default parse scope at whatever type the surrounding statement
	// pins, which is the same reason `COND` below is left alone, and it
	// is what the parent chapter's family members already rely on for
	// its own powerset and product members.
	// `COND` is deliberately NOT declared, though both members of
	// `counting.go` state it. The two state it at DIFFERENT branch
	// types — `accType` in the recursion theorem, num in the counting
	// clauses — so a pinned declaration would be wrong for one of them,
	// and it resolves from the default parse scope unpinned. The rule
	// above is "declare what a member states"; this is the one place
	// where obeying it would make a statement worse.
	//
	// set_fold is what card is DEFINED by, and the chapter states it in
	// exactly one member: the recursion theorem that makes the
	// definition total on finite sets. It is declared at the chapter's
	// element type folding into `accType`, and card is the instance
	// that fold is taken at.
	//
	// This is the chapter's one name from the iteration layer. It is
	// here rather than in a future iteration chapter for the same reason
	// the package is nested inside `finite_set`: without this theorem
	// card is not a function, so the recursion is part of what
	// cardinality IS rather than a neighbouring subject it cites.
	Term("set_fold")

	// The pointwise fold, which is why `Normalized` appears where it does.
	// A set law arrives from an install with its equation spread POINTWISE
	// (`∀ẋ. p(ẋ) ⇔ q(ẋ)`), while the claim standing beside it is about the
	// sets themselves. Folding the one back into the other is
	// extensionality, which `Basic` performs between installs and the
	// refuter does not — so a close that carries a COUNT across an
	// installed set law asks for `Normalized` unless the By's
	// conditioning already settles it, and one that does not, does not.
	//
	// It is stated here rather than in any one proof file because closes
	// across every proof file in this chapter turn on it. Every site is
	// measured BY REMOVAL rather than assumed, and each says only its own
	// delta: which law, and what failed without it. Two deltas worth
	// knowing in advance — the same shaping also settles an equation
	// between COUNTS (rewriting rather than refutation, one level down
	// from a set law), and a set equation proved LOCALLY rather than
	// installed needs no fold at all, because it never arrived spread.
	//
	// A note on receiver names, since several entries here depart from the
	// corpus default and the reason is the same one each time. An Argument
	// receiver is `a`, and an inner Given/Derive receiver is `b`. But this
	// chapter's subject is a set and a POINT of it, and the natural name
	// for the point is `a` — so wherever a statement binds one, the
	// receiver becomes `arg` and the term keeps the name the statement gave
	// it. A statement's own vocabulary outranks the file's.
	//
	// The chapter's set-side closes go to `BySets`. It closes no
	// cardinality statement and cannot — card and has_size are not in the
	// driver's vocabulary, for the same reason finite is not. What it
	// closes here is a leaf genuinely about the constructors, reached on the
	// way to a count — and the criterion is that the leaf mentions no count,
	// not that it is small: the driver settles membership and containment
	// facts of any size, and is simply inert to card standing beside them.
	// That covers more than constructor bookkeeping, since an INJECTIVITY
	// statement is also a membership fact, and `maps.go` closes one that
	// way. The one case worth flagging is a member's TERMINAL goal, where
	// the residual is a set equality and the counting facts around it are
	// inert.
