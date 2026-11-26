// vocab.go — the chapter's statement vocabulary.
//
// Two halves, and the split is the useful part. The first half is the
// names a statement MENTIONS; the second is the handful of those a
// proof body has to BUILD a term with, which is what `ops` hands back.
//
// The names, and why each is here.
//
// `∈` and `insert` come from the set domain's table
// (internal/setvocab), because their types are a fact about the domain
// rather than about this chapter. Declaring them at all matters even
// though the text-DSL reads `∈` and `{…}` unaided: the DSL's own metas
// carry no definition, and unfolding is how every set chapter works.
//
// `∅` is the domain's nullary name, so it takes an element type at the
// declaration rather than from an operand — `PinnedAt(…, NumType)`,
// since an interval's elements are numbers. Pinning is also what gives
// num_segment.go a term to hand `set_basic.InInsert` when the set being
// inserted into is the empty one.
//
// `..` is this chapter's own constant, and the domain table will not
// take it — every name there is one the `set_tac` driver unfolds
// (setvocab_test.go pins that containment) and the driver has never
// heard of an interval. Its declared type is the same one the DSL
// builds the infix `m .. n` at, and that agreement is load-bearing:
// only a scope declaration at the matching type displaces the DSL's
// definition-less meta, and num_segment.go's unfolding step needs the
// definition it carries.
//
// `⊆`, `∩`, `∪`, `disjoint` and `image` are the rest of the domain's
// table, and they arrive with the members that compare two intervals,
// combine them, or move one: an interval sits inside an interval, meets
// one, misses one, is cut into two, or is the shift of one.
//
// `≤`, `<`, `suc`, `+`, `-`, `nat_max` and `nat_min` are the names from outside
// the set domain. ℕ has no shared alphabet table — each of its chapters
// spells the relation and the operations itself — so this one does the
// same: the Spelled rows. They arrive one member at a time: `≤` with
// membership, `suc`, `+` and `-` with the recursion clauses, which move
// a bound by one at each end, and `<`, `nat_max`, `nat_min` with the members
// that say when an interval is empty and where two of them overlap.
//
// `card` and `has_size` are the last names to arrive and the only ones
// that are not about an interval's shape: one counts a set and the
// other says what a set's count is. They come in with `num_segment.go`, at the
// type an interval's own count is taken — a set of numbers, and a
// number. `has_size` is declared rather than merely mentioned because
// it is DEFINED as that conjunction and the counting members open it.
//
// The element type is `num` here — an interval's elements are the
// numbers its bounds are. The chapter has one member whose set is not a
// set of numbers, `FiniteIndex`, where an interval at `num` indexes a
// set of anything; that is why num_segment.go spells its own `card` term
// rather than building it from this table.
//
// The pin costs nothing for a name a member only STATES — such a name
// registers its POLYMORPHIC meta and the parser instantiates it from
// the operands at each use — and it is exactly what `∅` needs, having
// no operand to be instantiated from.

package num_segment

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/internal/setvocab"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// vocab is the chapter alphabet as data: the family installs it into
// every member's ParseScope (family.go's WithVocabSpec), and the vocab
// generator renders the build surface — segmentOps, the constants a
// body BUILDS terms with — from the same rows (zz_vocab_gen.go). One
// declaration is the point: a constant's type is spelled once, for the
// parser and the builders alike.
//
// A name is declared when a member STATES it, never in advance: an
// undeclared name still parses, so a speculative entry buys nothing and
// quietly claims the chapter reaches a notion it does not.
//
// Every named build handle below is carried by a witness somewhere in
// num_segment.go — the interval whose membership is being read, the
// empty set that `{0}` inserts into and that a crossed interval comes
// to, the two bounds where intervals meet, the three ways a bound moves
// by one, and the comparison counting splits on. `insert`, though six
// members state it, is never built: the one place a body would need it
// as a term is the set-equality bridge, and that cite is bare
// (`samePoints` says why).
var vocab = registry.NewVocabSpec(setvocab.Table()).
	OpsName("segmentOps").
	Term("set_member").Term("insert").
	Term("subset").Term("intersection").Term("union").
	Term("disjoint").Term("image").
	Term("<=").As("Le").
	Term("card").
	Term("has_size").
	// Interval is `.. : num → num → set(num)`, the chapter's
	// subject; a witness names it whenever a membership law is read at
	// one of the two intervals a recursion clause relates.
	Term("..").As("Interval").
	// `∅` is pinned at install time — see the header: a nullary name has
	// no operand to take its element type from, so the DECLARATION
	// carries it. The rows cannot say "pinned", so the pin itself is the
	// Custom closure and the build handle is the Built row beside it,
	// running the same idempotent PinnedAt at ops-build time.
	Custom(func(ctx *proof.Script) {
		setvocab.PinnedAt(ctx, "empty_set", NumType)
	}).
	// EmptySet is `∅` at `set(num)` — the set `{0}` inserts into, and
	// the only nullary name here. Named for the SET, not for the
	// emptiness criterion `Empty`, which is a member of num_segment.go.
	Built("EmptySet", func(ctx *proof.Script) *TermWrapper {
		return setvocab.PinnedAt(ctx, "empty_set", NumType)
	}).
	// suc, Plus and Minus are how a bound moves by one: the upper bound
	// grows by `suc`, the lower bound by `+ 1`, and the upper bound
	// shrinks by `- 1`. That the first two are the same step spelled
	// differently is a fact num_segment.go has to prove, not assume.
	Term("suc").As("SucOp"). // the Suc shorthand below builds suc(a)
	Term("+").As("Plus").
	Term("-").As("Minus").
	// Max and Min are the bounds of the interval where two intervals
	// overlap: the larger lower bound and the smaller upper bound. They
	// are terms rather than statement-only names because the overlap's
	// membership law is read AT them.
	Term("nat_max").
	Term("nat_min").
	// LessThan is `<`, and it is a build handle rather than a
	// statement-only name because counting splits on it: an interval
	// holds nothing exactly when its upper bound is under its lower one,
	// so that comparison has to be built as the discriminant of a case
	// split rather than merely stated.
	Term("<").As("LessThan")

// Term-building shorthands, so a witness list reads as mathematics
// rather than as applications.

// Seg is the interval lo .. hi.
func (v *segmentOps) Seg(lo, hi Term) Term { return v.Interval.Apply(lo, hi) }

// Suc is suc(n).
func (v *segmentOps) Suc(n Term) Term { return v.SucOp.Apply(n) }

// Add is a + b.
func (v *segmentOps) Add(a, b Term) Term { return v.Plus.Apply(a, b) }

// Sub is a - b, truncated at zero as ℕ subtraction always is.
func (v *segmentOps) Sub(a, b Term) Term { return v.Minus.Apply(a, b) }

// Larger is nat_max(a, b) and Smaller is nat_min(a, b) — the two bounds of the
// interval two intervals share.
func (v *segmentOps) Larger(a, b Term) Term  { return v.NatMax.Apply(a, b) }
func (v *segmentOps) Smaller(a, b Term) Term { return v.NatMin.Apply(a, b) }

// Under is a < b — read of two bounds, "the interval they name is
// empty".
func (v *segmentOps) Under(a, b Term) Term { return v.LessThan.Apply(a, b) }

// samePoints is the move every set equation in this chapter opens with:
// it suffices to show the two sides admit the same points, so state
// that, discharge the equation from it, and hand back the arbitrary
// point the rest of the proof argues about.
//
// The `Extension` cite is bare because grounding it would spell the
// equation's two sides a second time — they are already written, in
// the claim this is called with.
//
// **Extension rather than `funext`, and that is not a preference.**
// `funext` leaves the goal in APPLIED form — `(m₀ .. suc n₀)(ẋ)` —
// while every membership premise below carries `∈`, and `Normalize`
// does not identify `set_member(x, s)` with `s(x)`. A `By` with correct ground
// premises then fails with "no hyp was cleared … not in the shape the
// closer meets them in", which reads as a wrong premise list and is
// not. Extension is what keeps both sides in `∈`.
func samePoints(a *Argument, pointwise string) Term {
	claim := a.Ctx().MakePropText(pointwise)
	a.Do(Suffices(claim, "two sets are equal when they have the same members",
		By(ResidentHyp(claim), set_basic.Extension)))
	return a.Fix()
}

// reading states what membership comes to at the point on the sides the
// set vocabulary alone settles: a builder read as its own condition,
// `{a}` as an equation, `∅` as nothing, an insert as either the added
// point or the rest. A bare `BySets()` is the closer because that
// residue IS plumbing — no `≤` or `<` survives into it, which is
// exactly the test the chapter applies when choosing between the set
// driver and a refuting `By`.
//
// **The driver's role is per LEAF, not per member.** `Membership` is
// the only member it closes outright — that statement IS about the set
// vocabulary, and unfolding `..` leaves a comprehension. Through the
// first three movements every other member ends at `≤` or `<` on the
// bounds, which the driver cannot settle; but most of them reach that
// end through a leaf with a SET half, and there the driver is exactly
// right: state the set-only fact here, and hand it to the `By` as a
// named premise. The counting members end at a count instead and never
// reach the driver at all.
//
// The claim is stated ground, at the point `samePoints` just fixed, so
// the fact goes straight into the premise list of the close.
func reading(a *Argument, memberships string) Fact {
	return a.Have(
		"what membership comes to at the point, by the set vocabulary alone",
		memberships,
		BySets())
}

// A polymorphic set law read at `num` is pinned by the wrapper's
// explicit instance — `set_basic.InInsert.Inst[Nat]()` — before it is
// grounded. A row that needs the pin fails a plain ground cite with
// `no certificate covers the premise obligation`, printing its
// polymorphic statement while the `num` instance stays uncovered; and
// which rows need it is not predicted by polymorphism, or by anything
// else a call site can see. The ladder is plain ground cite → type
// pin → naming the membership as a fact (`reading` above), each rung
// reached only when the one before it fails. Witnesses onto the
// pinned instance go in the row's own STATED binder order, like every
// other ground cite.
