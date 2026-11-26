// set_algebra.go — the chapter: the algebra of sets.
//
// Five parts, marked by banners:
//
// - ∪ and ∩ as join and meet
// - Set difference, and the complement it spells
// - insert and delete: putting one element in, and taking one out
// - Meeting in nothing
// - ⋃ and ⋂ against the constructors

package set_algebra

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// ∪ and ∩ as join and meet
// ---------------------------------------------------------------------------
//
// Each of the two operations is commutative, associative and
// idempotent, so a union or an intersection depends on nothing beyond
// the collection of sets it is taken over — not on their order, their
// bracketing, or how often each was named. ∅ is the unit for ∪ and 𝕌
// the unit for ∩, and each is absorbing for the operation the other is
// neutral for.
//
// The two closing members go further than that. Nothing about a
// lattice forces either operation through the other; here each passes
// through, which is what the word distributive names.

// UnionComm — union is symmetric in its two arguments. An element earns
// its place by lying in one of them, and nothing records which.
var UnionComm = unionCommThm{family.Add(registry.ProofEntry{
	Name:  "UnionComm",
	Key:   "prop_ed003bdf76bdf260",
	Build: family.Theorem("∀s t:set(A). s ∪ t = t ∪ s", BySets()),
})}

// UnionAssoc — union is associative, so a join of three sets needs no
// bracketing. Either grouping asks the same question of an element: is
// it held by any one of the three.
var UnionAssoc = unionAssocThm{family.Add(registry.ProofEntry{
	Name: "UnionAssoc",
	Key:  "prop_e9482fe44804d83",
	Build: family.Theorem(
		"∀s t u:set(A). s ∪ (t ∪ u) = s ∪ t ∪ u",
		BySets()),
})}

// UnionIdempot — union is idempotent. Joining a set to itself offers no
// element it did not already hold.
var UnionIdempot = unionIdempotThm{family.Add(registry.ProofEntry{
	Name: "UnionIdempot",
	Key:  "prop_b7a5a8cefefa8a71",
	Build: family.Theorem(
		"∀s:set(A). s ∪ s = s",
		BySets()),
})}

// UnionEmpty — ∅ is the unit for union, on either side. It contributes
// no element, so the join is decided by the other set alone.
var UnionEmpty = unionEmptyThm{family.Add(registry.ProofEntry{
	Name: "UnionEmpty",
	Key:  "prop_828f9a81534e1a44",
	Build: family.Theorem(
		"∀s:set(A). s ∪ ∅ = s ∧ ∅ ∪ s = s",
		BySets()),
})}

// UnionUniv — and 𝕌 absorbs union, on either side. It already admits
// every element of the type, so joining anything to it reaches no
// further.
var UnionUniv = unionUnivThm{family.Add(registry.ProofEntry{
	Name: "UnionUniv",
	Key:  "prop_b47861a91af3a685",
	Build: family.Theorem(
		"∀s:set(A). s ∪ 𝕌 = 𝕌 ∧ 𝕌 ∪ s = 𝕌",
		BySets()),
})}

// UnionEqEmpty — a union is empty exactly when both of its parts are.
// Joining creates no element, so the only way for it to hold none is
// for neither side to have offered one.
var UnionEqEmpty = unionEqEmptyThm{family.Add(registry.ProofEntry{
	Name: "UnionEqEmpty",
	Key:  "prop_61b514da01a6ac43",
	Build: family.Theorem(
		"∀s t:set(A). s ∪ t = ∅ ⇔ s = ∅ ∧ t = ∅",
		BySets()),
})}

// InterComm — intersection is symmetric. It makes two demands of an
// element, and the order in which they are made is immaterial.
var InterComm = interCommThm{family.Add(registry.ProofEntry{
	Name: "InterComm",
	Key:  "prop_b6ca870888077b8b",
	Build: family.Theorem(
		"∀s t:set(A). s ∩ t = t ∩ s",
		BySets()),
})}

// InterAssoc — intersection is associative. Either grouping admits
// exactly those elements held by all three sets.
var InterAssoc = interAssocThm{family.Add(registry.ProofEntry{
	Name: "InterAssoc",
	Key:  "prop_76ae901278c53d38",
	Build: family.Theorem(
		"∀s t u:set(A). s ∩ (t ∩ u) = s ∩ t ∩ u",
		BySets()),
})}

// InterIdempot — intersection is idempotent. Meeting a set with itself
// makes the same demand twice, which is to make it once.
var InterIdempot = interIdempotThm{family.Add(registry.ProofEntry{
	Name: "InterIdempot",
	Key:  "prop_1110f399b5a7d419",
	Build: family.Theorem(
		"∀s:set(A). s ∩ s = s",
		BySets()),
})}

// InterEmpty — ∅ absorbs intersection, on either side. There is no
// element in it for the meet to keep.
var InterEmpty = interEmptyThm{family.Add(registry.ProofEntry{
	Name: "InterEmpty",
	Key:  "prop_e6dfcf878b5cc3ae",
	Build: family.Theorem(
		"∀s:set(A). s ∩ ∅ = ∅ ∧ ∅ ∩ s = ∅",
		BySets()),
})}

// InterUniv — and 𝕌 is the unit for intersection, on either side. The
// demand it makes is met by every element of the type, so it discards
// nothing.
var InterUniv = interUnivThm{family.Add(registry.ProofEntry{
	Name: "InterUniv",
	Key:  "prop_74628d4a9edfd88",
	Build: family.Theorem(
		"∀s:set(A). s ∩ 𝕌 = s ∧ 𝕌 ∩ s = s",
		BySets()),
})}

// InterDistribUnion — ∩ distributes over ∪: a meet against a fixed set
// may be pushed inside a join. An element gets in, either way, by lying
// in the fixed set and in at least one of the other two, and the meet
// never disturbs that choice.
var InterDistribUnion = interDistribUnionThm{family.Add(registry.ProofEntry{
	Name: "InterDistribUnion",
	Key:  "prop_95672b604fd13679",
	Build: family.Theorem(
		"∀s t u:set(A). s ∩ (t ∪ u) = s ∩ t ∪ s ∩ u",
		BySets()),
})}

// UnionDistribInter — and the mirror, ∪ distributing over ∩. In any
// lattice the two directions are equivalent, each derivable from the
// other, so this and the law above make one claim between them: that
// the lattice of sets is distributive.
var UnionDistribInter = unionDistribInterThm{family.Add(registry.ProofEntry{
	Name: "UnionDistribInter",
	Key:  "prop_5c7bc2e0a62ba460",
	Build: family.Theorem(
		"∀s t u:set(A). s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u)",
		BySets()),
})}

// ---------------------------------------------------------------------------
// Set difference, and the complement it spells
// ---------------------------------------------------------------------------
//
// ∖ is the chapter's one asymmetric operation, and the only one whose
// two arguments play different roles. Its laws come in four groups:
// what the two constant sets do in either position; what a set does to
// itself, once directly and once as the repeated removal that changes
// nothing the second time; the involution; and the two that trade an
// insertion on one side for a deletion on the other. Complement belongs
// here rather than in a chapter of its own, because this corpus has no
// separate name for it — the complement of s is what remains of 𝕌 after
// s is taken out — so the involution is a law about ∖ like the rest.
//
// The file boundary in this chapter follows the OPERATION, not the
// constructor: ∖ against insert and delete is here, while ∪ and ∩
// against insert are below. So InsertDiff sits in this
// part even though it is one of the chapter's four conditional laws,
// and it is this part's only member closing by setTacExpand.

// DiffEmpty — removing nothing is doing nothing. ∅ offers no element to
// withdraw, so every element of s survives.
var DiffEmpty = diffEmptyThm{family.Add(registry.ProofEntry{
	Name: "DiffEmpty",
	Key:  "prop_8efbb43650704ae9",
	Build: family.Theorem(
		"∀s:set(A). s ∖ ∅ = s",
		BySets()),
})}

// DiffUniv — removing everything leaves nothing. 𝕌 holds every element
// of the type, so in particular every element of s is withdrawn.
var DiffUniv = diffUnivThm{family.Add(registry.ProofEntry{
	Name: "DiffUniv",
	Key:  "prop_aa2cdfdac983c265",
	Build: family.Theorem(
		"∀s:set(A). s ∖ 𝕌 = ∅",
		BySets()),
})}

// DiffEqEmpty — a set removes itself completely. Surviving would mean
// belonging to s and failing to, so nothing does.
var DiffEqEmpty = diffEqEmptyThm{family.Add(registry.ProofEntry{
	Name: "DiffEqEmpty",
	Key:  "prop_8d47cecd13d2c2ac",
	Build: family.Theorem(
		"∀s:set(A). s ∖ s = ∅",
		BySets()),
})}

// DiffDiff — removing the same set twice is removing it once. The first
// pass leaves nothing of t behind for the second to take, so ∖ is
// idempotent in the set it subtracts.
var DiffDiff = diffDiffThm{family.Add(registry.ProofEntry{
	Name: "DiffDiff",
	Key:  "prop_f0203bef0e56d9cb",
	Build: family.Theorem(
		"∀s t:set(A). s ∖ t ∖ t = s ∖ t",
		BySets()),
})}

// EmptyDiff — ∅ in the other position, where the law is vacuous rather
// than cancelling: there is nothing to take anything away from.
var EmptyDiff = emptyDiffThm{family.Add(registry.ProofEntry{
	Name: "EmptyDiff",
	Key:  "prop_8d9d2a5af819b0a5",
	Build: family.Theorem(
		"∀s:set(A). ∅ ∖ s = ∅",
		BySets()),
})}

// DoubleComplement — complementing twice returns the set. What is left
// over from what was left over is what one started with, since an
// element either belongs to s or does not and no third case remains.
// This is the one law in the file that genuinely uses that dichotomy;
// the others hold constructively.
var DoubleComplement = doubleComplementThm{family.Add(registry.ProofEntry{
	Name: "DoubleComplement",
	Key:  "prop_71a494eaf42aba55",
	Build: family.Theorem(
		"∀s:set(A). 𝕌 ∖ (𝕌 ∖ s) = s",
		BySets()),
})}

// DiffInsert — enlarging the subtracted set by one element is the same
// as deleting that element first and subtracting the rest afterwards.
// This is what lets a difference against a set built up element by
// element be taken apart the same way.
var DiffInsert = diffInsertThm{family.Add(registry.ProofEntry{
	Name: "DiffInsert",
	Key:  "prop_9ad4446a3ed8178f",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. s ∖ insert(x, t) = delete(s, x) ∖ t",
		BySets()),
})}

// InsertDiff — the mirror, where the extra element is added on the side
// being subtracted FROM. That element survives exactly when the set being
// removed does not already hold it, so unlike its mirror this law splits:
// a single test decides which of two sets the answer is.
var InsertDiff = insertDiffThm{family.Add(registry.ProofEntry{
	Name: "InsertDiff",
	Key:  "prop_e2969e0752024e51",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. insert(x, s) ∖ t = COND(x ∈ t, s ∖ t, insert(x, s ∖ t))",
		setTacExpand()),
})}

// ---------------------------------------------------------------------------
// insert and delete: putting one element in, and taking one out
// ---------------------------------------------------------------------------
//
// The two element-wise constructions, and what they do to each other
// and to the binary operations. Each is idempotent and commutative in
// its element, and the two are mutually inverse wherever the element's
// membership is settled. Three laws here are not unconditional, and each
// states the case it turns on: moving an inserted element across ∪ or ∩
// has to ask whether the other operand already holds it, and composing a
// removal with an insertion has to ask whether the two name the same
// element.

// InsertContains — whatever else a set holds, it holds the element that
// was put into it. This is the half of insert's meaning that does not
// depend on what was there before.
var InsertContains = insertContainsThm{family.Add(registry.ProofEntry{
	Name: "InsertContains",
	Key:  "prop_df8c5ce2da218ce6",
	Build: family.Theorem(
		"∀s:set(A). ∀x:A. x ∈ insert(x, s)",
		BySets()),
})}

// InsertAbsorb — adding an element leaves a set unchanged exactly when
// the element was already there. Membership is therefore recoverable
// from the equation alone: a set knows nothing more about an element
// than whether putting it in makes a difference.
var InsertAbsorb = insertAbsorbThm{family.Add(registry.ProofEntry{
	Name: "InsertAbsorb",
	Key:  "prop_5a490cef32ae1e02",
	Build: family.Theorem(
		"∀s:set(A). ∀x:A. x ∈ s ⇔ insert(x, s) = s",
		BySets()),
})}

// InsertInsert — adding the same element twice is adding it once. A set
// records that an element is present, not how often it was put in.
var InsertInsert = insertInsertThm{family.Add(registry.ProofEntry{
	Name: "InsertInsert",
	Key:  "prop_9a3a9d3c62ca3999",
	Build: family.Theorem(
		"∀s:set(A). ∀x:A. insert(x, insert(x, s)) = insert(x, s)",
		BySets()),
})}

// InsertComm — two elements may be added in either order. Nothing about
// the result remembers which of them arrived first.
var InsertComm = insertCommThm{family.Add(registry.ProofEntry{
	Name: "InsertComm",
	Key:  "prop_dae44cb9c4b9d518",
	Build: family.Theorem(
		"∀s:set(A). ∀x y:A. insert(x, insert(y, s)) = insert(y, insert(x, s))",
		BySets()),
})}

// InsertUniv — 𝕌 already admits every element of the type, so there is
// nothing left for an insertion to contribute.
var InsertUniv = insertUnivThm{family.Add(registry.ProofEntry{
	Name: "InsertUniv",
	Key:  "prop_31e27182f26bfbf2",
	Build: family.Theorem(
		"∀x:A. insert(x, 𝕌) = 𝕌",
		BySets()),
})}

// InsertNotEmpty — a set that something was put into is never empty. It
// holds at least what was put in, and ∅ holds nothing.
var InsertNotEmpty = insertNotEmptyThm{family.Add(registry.ProofEntry{
	Name: "InsertNotEmpty",
	Key:  "prop_9299c8ebcc7cf39c",
	Build: family.Theorem(
		"∀s:set(A). ∀x:A. ¬(insert(x, s) = ∅)",
		BySets()),
})}

// InsertUnionEq — an element added to a union may equally be added to
// the left operand first. Alone among the laws that move an insertion
// across a binary operation this one needs no case: the element ends up
// inside the union either way, so whether the other operand already
// held it never changes the answer.
var InsertUnionEq = insertUnionEqThm{family.Add(registry.ProofEntry{
	Name: "InsertUnionEq",
	Key:  "prop_ca640abd945fd0fd",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. insert(x, s ∪ t) = insert(x, s) ∪ t",
		BySets()),
})}

// InsertUnion — the same insertion pushed OUT of the union rather than
// in, and read that way the case is unavoidable. An insertion into the
// left operand is an insertion into the union, unless the right operand
// already supplied the element, in which case the union never noticed
// the insertion at all.
var InsertUnion = insertUnionThm{family.Add(registry.ProofEntry{
	Name: "InsertUnion",
	Key:  "prop_2fba3876734571c8",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. insert(x, s) ∪ t = COND(x ∈ t, s ∪ t, insert(x, s ∪ t))",
		setTacExpand()),
})}

// InsertInter — the same question asked of ∩, and answered the other
// way round: an intersection keeps an added element only when the other
// operand has it too, and otherwise discards it along with everything
// else the two sets do not share.
var InsertInter = insertInterThm{family.Add(registry.ProofEntry{
	Name: "InsertInter",
	Key:  "prop_168bc96f4a64dcdd",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. insert(x, s) ∩ t = COND(x ∈ t, insert(x, s ∩ t), s ∩ t)",
		setTacExpand()),
})}

// EmptyDelete — removing an element from nothing leaves nothing. There
// was never anything to take away.
var EmptyDelete = emptyDeleteThm{family.Add(registry.ProofEntry{
	Name: "EmptyDelete",
	Key:  "prop_615a306d6ea3413e",
	Build: family.Theorem(
		"∀x:A. delete(∅, x) = ∅",
		BySets()),
})}

// DeleteComm — two elements may be removed in either order. Taking one
// out cannot affect whether the other is still present.
var DeleteComm = deleteCommThm{family.Add(registry.ProofEntry{
	Name: "DeleteComm",
	Key:  "prop_c9687c69a71cceed",
	Build: family.Theorem(
		"∀s:set(A). ∀x y:A. delete(delete(s, x), y) = delete(delete(s, y), x)",
		BySets()),
})}

// DeleteDelete — removing the same element twice is removing it once.
// The second removal finds it already gone.
var DeleteDelete = deleteDeleteThm{family.Add(registry.ProofEntry{
	Name: "DeleteDelete",
	Key:  "prop_a89423e9a3db7155",
	Build: family.Theorem(
		"∀s:set(A). ∀x:A. delete(delete(s, x), x) = delete(s, x)",
		BySets()),
})}

// DeleteInter — an element removed from an intersection may be removed
// from the first set instead. Once it is gone from there nothing on the
// other side can put it back, and the intersection is asked about
// nothing else.
var DeleteInter = deleteInterThm{family.Add(registry.ProofEntry{
	Name: "DeleteInter",
	Key:  "prop_b76c0755aec49ef",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. delete(s ∩ t, x) = delete(s, x) ∩ t",
		BySets()),
})}

// DeleteInsert — a removal applied to an insertion. Naming the same
// element, the removal simply undoes the insertion it was handed;
// naming different ones, the two moves are independent and may be
// exchanged. Nothing decides between those readings but the identity of
// the two elements, which is why the law carries the comparison.
var DeleteInsert = deleteInsertThm{family.Add(registry.ProofEntry{
	Name: "DeleteInsert",
	Key:  "prop_3450f159d1194f83",
	Build: family.Theorem(
		"∀s:set(A). ∀x y:A. delete(insert(x, s), y) = COND(x = y, delete(s, y), insert(x, delete(s, y)))",
		setTacExpand()),
})}

// InsertDelete — taking out an element a set has, then putting it back,
// recovers the set. The hypothesis is what makes this an inverse:
// without it the insertion would leave behind an element the set never
// held.
var InsertDelete = insertDeleteThm{family.Add(registry.ProofEntry{
	Name: "InsertDelete",
	Key:  "prop_e61ba93c888a4707",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(A). ∀x:A.",
			Hypotheses: []string{
				"x ∈ s",
			},
			Conclusion: "insert(x, delete(s, x)) = s",
		},
		BySets()),
})}

// DeleteNonElement — removing an element leaves a set unchanged exactly
// when the set never held it. The exact mirror of InsertAbsorb, with
// both the construction and the side of membership exchanged.
var DeleteNonElement = deleteNonElementThm{family.Add(registry.ProofEntry{
	Name: "DeleteNonElement",
	Key:  "prop_1c1db8d5a5ee815f",
	Build: family.Theorem(
		"∀s:set(A). ∀x:A. x ∉ s ⇔ delete(s, x) = s",
		BySets()),
})}

// DeleteMembershipSwap — two elements agree about belonging to a set
// exactly when they still agree after each has had the other removed.
// A removal only ever takes out the element it names, so away from the
// diagonal the swapped question is the plain one; on it, each side has
// been removed from the set it is asked about and both readings are
// vacuously yes.
var DeleteMembershipSwap = deleteMembershipSwapThm{family.Add(registry.ProofEntry{
	Name: "DeleteMembershipSwap",
	Key:  "prop_2f2aadb2c7aba85a",
	Build: family.Theorem(
		"∀s:set(A). ∀x y:A. (x ∈ s ⇔ y ∈ s) ⇔ (x ∈ delete(s, y) ⇔ y ∈ delete(s, x))",
		BySets()),
})}

// ---------------------------------------------------------------------------
// Meeting in nothing
// ---------------------------------------------------------------------------
//
// `disjoint(s, t)` is defined as an equation, `s ∩ t = ∅`, which puts
// it with the rest of the chapter. But an argument almost never uses it
// in that shape: it uses "no element lies in both", and translating
// between the two is `InDisjoint`, the first law below and the one the
// others are read through.
//
// After it: the symmetry, then the three cases where disjointness
// collapses to something simpler — against ∅, against itself, against a
// one-element set — and then what insert, delete and ∪ do to it.

// InDisjoint — the bridge from the defining equation to the way
// disjointness is used. An intersection is empty precisely when no
// element was there to put into it, which is a condition on the two
// sets' elements rather than on a third set.
var InDisjoint = inDisjointThm{family.Add(registry.ProofEntry{
	Name: "InDisjoint",
	Key:  "prop_a423dfa34cbc37fb",
	Build: family.Theorem(
		"∀s t:set(A). disjoint(s, t) ⇔ ¬∃x:A. x ∈ s ∧ x ∈ t",
		BySets()),
})}

// DisjointSym — disjointness is symmetric. It asks that the two sets
// share no element, and sharing is mutual: neither set is the subject
// of the claim.
var DisjointSym = disjointSymThm{family.Add(registry.ProofEntry{
	Name: "DisjointSym",
	Key:  "prop_6900b988474e98ca",
	Build: family.Theorem(
		"∀s t:set(A). disjoint(s, t) ⇔ disjoint(t, s)",
		BySets()),
})}

// DisjointEmpty — ∅ is disjoint from everything, and on either side of
// the relation: it holds no element that a second set could also hold.
var DisjointEmpty = disjointEmptyThm{family.Add(registry.ProofEntry{
	Name: "DisjointEmpty",
	Key:  "prop_e14eefa8cfbaf3df",
	Build: family.Theorem(
		"∀s:set(A). disjoint(s, ∅) ∧ disjoint(∅, s)",
		BySets()),
})}

// DisjointSelf — a set meets itself in every element it has, so sharing
// one with itself is nothing more than having one. Self-disjointness is
// therefore emptiness, and holds of a single set out of all of them.
var DisjointSelf = disjointSelfThm{family.Add(registry.ProofEntry{
	Name: "DisjointSelf",
	Key:  "prop_540a6af46453a94f",
	Build: family.Theorem(
		"∀s:set(A). disjoint(s, s) ⇔ s = ∅",
		BySets()),
})}

// DisjointSing — against a one-element set, disjointness is a
// membership question. There is only one element available to be
// shared, so the condition is that s should miss that one.
var DisjointSing = disjointSingThm{family.Add(registry.ProofEntry{
	Name: "DisjointSing",
	Key:  "prop_c7365d46c2eba958",
	Build: family.Theorem(
		"∀s:set(A). ∀a:A. (disjoint(s, {a}) ⇔ a ∉ s) ∧ (disjoint({a}, s) ⇔ a ∉ s)",
		BySets()),
})}

// DisjointInsert — adding an element to a set keeps it clear of t
// exactly when the addition was itself harmless and the set was clear
// before: the one new element must miss t, and the old ones still must.
var DisjointInsert = disjointInsertThm{family.Add(registry.ProofEntry{
	Name: "DisjointInsert",
	Key:  "prop_c8bdb2477ebe400",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. disjoint(insert(x, s), t) ⇔ x ∉ t ∧ disjoint(s, t)",
		BySets()),
})}

// DisjointDeleteSym — symmetry survives setting one element aside.
// Whichever of the two sets x is removed from, what is left to share is
// the elements common to both apart from x, so the side the removal
// happened on cannot be recovered from the answer.
var DisjointDeleteSym = disjointDeleteSymThm{family.Add(registry.ProofEntry{
	Name: "DisjointDeleteSym",
	Key:  "prop_d3ce4d41318d7021",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. disjoint(delete(s, x), t) ⇔ disjoint(delete(t, x), s)",
		BySets()),
})}

// DisjointUnion — a union meets u exactly when one of its two parts
// does, so it misses u exactly when both parts do. Disjointness from a
// fixed set is a condition each part carries on its own.
var DisjointUnion = disjointUnionThm{family.Add(registry.ProofEntry{
	Name: "DisjointUnion",
	Key:  "prop_cd73d6886b3dcc4e",
	Build: family.Theorem(
		"∀s t u:set(A). disjoint(s ∪ t, u) ⇔ disjoint(s, u) ∧ disjoint(t, u)",
		BySets()),
})}

// ---------------------------------------------------------------------------
// ⋃ and ⋂ against the constructors
// ---------------------------------------------------------------------------
//
// The two big operators are each read off one word: a point lies in ⋃s
// when it lies in SOME member of the family s, and in ⋂s when it lies in
// EVERY member. Everything below follows from that reading, and the two
// separate wherever the quantifier does — over a family with no members
// "some" fails for every point while "every" holds for every point, so
// the two land at opposite ends of the lattice.
//
// The chapter's binary operations are the arity-two cases of these: the
// recursions for insert say that enlarging a family by one set enlarges
// its union by that set and cuts its intersection down by it, so ⋃ and ⋂
// do not merely resemble ∪ and ∩ but restrict to them. Each half runs
// the same way — the empty family, one member, two members, then the
// recursion, then how the operator meets a union of families, and last
// the test for reaching the lattice's end.
//
// The ⋃ half carries three more with no ⋂ mirror: `⋃𝕌 = 𝕌`, and the
// two saying an empty member may be adjoined to or discarded from a
// family without moving the union. All three turn on a member that
// contributes NOTHING — which is ∅ for a union and 𝕌 for an
// intersection, so the ⋂ statements of that shape would be about
// adjoining 𝕌 instead.

// UnionsEmpty — over no members at all there is nothing for a point to
// belong to, so the union collects nothing.
var UnionsEmpty = unionsEmptyThm{family.Add(registry.ProofEntry{
	Name: "UnionsEmpty",
	Key:  "prop_f11914b8a828deee",
	Build: family.Theorem(
		"⋃∅ = ∅",
		BySets()),
})}

// UnionsSing — with one member to choose from, "some member" can only
// mean that one.
var UnionsSing = unionsSingThm{family.Add(registry.ProofEntry{
	Name: "UnionsSing",
	Key:  "prop_76940e6d06c9f269",
	Build: family.Theorem(
		"∀s:set(A). ⋃{s} = s",
		BySets()),
})}

// UnionsPair — and with two, the choice between them is exactly the
// binary union. This is where ⋃ is pinned down as ∪ at arbitrary arity
// rather than merely something like it. The pair is a singleton with
// one member adjoined, so UnionsInsert and UnionsSing compute it.
var UnionsPair = unionsPairThm{family.Add(registry.ProofEntry{
	Name: "UnionsPair",
	Key:  "prop_b5f64751e7a5233c",
	Build: family.Theorem(
		"∀s t:set(A). ⋃{s, t} = s ∪ t",
		Chain(Simp(Fwd(UnionsSing), Fwd(UnionsInsert)), Basic())),
})}

// UnionsInsert — the recursion for ⋃: a new member contributes exactly
// its own points. Applied down to a family listed one set at a time, it
// rewrites the union into a chain of binary unions.
var UnionsInsert = unionsInsertThm{family.Add(registry.ProofEntry{
	Name: "UnionsInsert",
	Key:  "prop_a9015f7f839499a6",
	Build: family.Theorem(
		"∀u:set(set(A)). ∀s:set(A). ⋃insert(s, u) = s ∪ ⋃u",
		BySets()),
})}

// UnionsUnion — union passes through union across the two levels: to
// lie in some member of either family is to lie in one of the two
// unions.
var UnionsUnion = unionsUnionThm{family.Add(registry.ProofEntry{
	Name: "UnionsUnion",
	Key:  "prop_9e36e83de5bd164e",
	Build: family.Theorem(
		"∀s t:set(set(A)). big_union(s ∪ t) = ⋃s ∪ ⋃t",
		BySets()),
})}

// UnionsEqEmpty — when the union collects nothing. The demanding
// direction is that one inhabited member would hand its element to the
// union, so the condition falls on every member at once; the family
// itself may be as large as it likes, provided everything it holds is
// empty.
var UnionsEqEmpty = unionsEqEmptyThm{family.Add(registry.ProofEntry{
	Name: "UnionsEqEmpty",
	Key:  "prop_391f7336896d4910",
	Build: family.Theorem(
		"∀s:set(set(A)). ⋃s = ∅ ⇔ ∀t:set(A). t ∈ s ⇒ t = ∅",
		BySets()),
})}

// UnionsUniv — the family of ALL sets has a member for every point, so
// its union misses nothing.
var UnionsUniv = unionsUnivThm{family.Add(registry.ProofEntry{
	Name: "UnionsUniv",
	Key:  "prop_e5223109dbf333c8",
	Build: family.Theorem(
		"⋃𝕌 = 𝕌",
		BySets()),
})}

// UnionsInsertEmpty — an empty member contributes no point, so adjoining
// one to a family leaves the union where it was.
var UnionsInsertEmpty = unionsInsertEmptyThm{family.Add(registry.ProofEntry{
	Name: "UnionsInsertEmpty",
	Key:  "prop_9de2bc6a2806821",
	Build: family.Theorem(
		"∀s:set(set(A)). ⋃insert(∅, s) = ⋃s",
		BySets()),
})}

// UnionsDeleteEmpty — and the same bookkeeping run backwards: what was
// contributing nothing can be discarded at no cost to the union.
var UnionsDeleteEmpty = unionsDeleteEmptyThm{family.Add(registry.ProofEntry{
	Name: "UnionsDeleteEmpty",
	Key:  "prop_e71cd2463a77b80b",
	Build: family.Theorem(
		"∀s:set(set(A)). ⋃delete(s, ∅) = ⋃s",
		BySets()),
})}

// IntersEmpty — over the empty family there is no member to exclude a
// point, so every point qualifies vacuously and the intersection is
// everything. The exact mirror of UnionsEmpty, landing at the opposite
// end for the same reason.
var IntersEmpty = intersEmptyThm{family.Add(registry.ProofEntry{
	Name: "IntersEmpty",
	Key:  "prop_f59e844052c98511",
	Build: family.Theorem(
		"⋂∅ = 𝕌",
		BySets()),
})}

// IntersSing — one member imposes one condition, which is that member.
var IntersSing = intersSingThm{family.Add(registry.ProofEntry{
	Name: "IntersSing",
	Key:  "prop_35820b40a7db78bf",
	Build: family.Theorem(
		"∀s:set(A). ⋂{s} = s",
		BySets()),
})}

// IntersPair — two members impose both conditions at once, which is the
// binary intersection.
var IntersPair = intersPairThm{family.Add(registry.ProofEntry{
	Name: "IntersPair",
	Key:  "prop_159ac3ec2e9ba24f",
	Build: family.Theorem(
		"∀s t:set(A). ⋂{s, t} = s ∩ t",
		Chain(Simp(Fwd(IntersSing), Fwd(IntersInsert)), Basic())),
})}

// IntersInsert — the recursion for ⋂, mirroring ⋃'s: a new member
// imposes exactly its own condition, so the intersection is cut down by
// that set.
var IntersInsert = intersInsertThm{family.Add(registry.ProofEntry{
	Name: "IntersInsert",
	Key:  "prop_d51cd639bcc94ee0",
	Build: family.Theorem(
		"∀u:set(set(A)). ∀s:set(A). ⋂insert(s, u) = s ∩ ⋂u",
		BySets()),
})}

// IntersUnion — pooling two families conjoins their demands: a point
// surviving every member of the pool is one that survived each family
// separately. The ⋂ counterpart of UnionsUnion, and the harder of the
// pair — where "some member of the pool" splits into a choice between
// two sides for free, "every member" has to be applied at a member
// whose side is not known in advance.
var IntersUnion = intersUnionThm{family.Add(registry.ProofEntry{
	Name: "IntersUnion",
	Key:  "prop_6fc6873e822211fe",
	Build: family.Theorem(
		"∀s t:set(set(A)). big_intersection(s ∪ t) = ⋂s ∩ ⋂t",
		BySets()),
})}

// IntersEqUniv — when the intersection reaches the top. Mirror of the
// emptiness test for ⋃, and again a condition on every member: one
// member missing a point would keep that point out.
var IntersEqUniv = intersEqUnivThm{family.Add(registry.ProofEntry{
	Name: "IntersEqUniv",
	Key:  "prop_e16b7f548b29256",
	Build: family.Theorem(
		"∀f:set(set(A)). ⋂f = 𝕌 ⇔ ∀s:set(A). s ∈ f ⇒ s = 𝕌",
		BySets()),
})}
