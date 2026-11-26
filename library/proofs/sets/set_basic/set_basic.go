// set_basic.go — the chapter: the language of sets.
//
// Four parts, marked by banners:
//
// - Set equality is membership
// - Membership in a constructed set
// - Taking a set apart
// - Quantifiers over a constructed set

package set_basic

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Set equality is membership
// ---------------------------------------------------------------------------
//
// A set is its own membership predicate, so `x ∈ s` is `s` applied to
// `x` and nothing more. Extension makes that usable for equations: it
// is the bridge every set identity crosses to become a statement about
// elements, and the rest of the chapter says what those statements
// mean, constructor by constructor. Both members here cross that
// bridge — one for an equation between sets, one for its denial.

// Extension is set equality, stated in terms of members: `s = t` says
// no more and no less than that `s` and `t` have the same elements.
//
// One fact worth knowing lest the proof look too thin: the normalizer
// already dissolves an equation between functions into its pointwise
// form, so by the time `s = t` is a goal it reads `∀x. s(x) ⇔ t(x)` on
// its own, and what remains between the two sides is only that `s(x)`
// and `x ∈ s` are the same thing — the definition of `set_member`.
var Extension = extensionThm{family.Add(registry.ProofEntry{
	Name: "Extension",
	Key:  "prop_7c75462da1c74d4a",
	Build: family.Theorem(
		"∀s t:set(A). s = t ⇔ ∀x:A. x ∈ s ⇔ x ∈ t",
		BySets()),
})}

// NotEqualSets is Extension read backwards. If agreeing on every
// element is what makes two sets equal, then differing is exhibiting a
// single element the two disagree about — which is what a proof of
// inequality between sets actually produces.
var NotEqualSets = notEqualSetsThm{family.Add(registry.ProofEntry{
	Name: "NotEqualSets",
	Key:  "prop_ae08050b11769d61",
	Build: family.Theorem(
		"∀s t:set(A). ¬(s = t) ⇔ ∃x:A. ¬(x ∈ s ⇔ x ∈ t)",
		BySets()),
})}

// ---------------------------------------------------------------------------
// Membership in a constructed set
// ---------------------------------------------------------------------------
//
// One member per constructor, each answering the same question: given
// how the constructor is defined, what does it take to be in the set it
// builds? These are the facts the rest of set theory is written in —
// an inclusion or an identity between constructed sets becomes, via
// Extension, a statement about their elements, and it is these laws
// that say what those statements mean.
//
// Every proof is the same recorded move. Each constructor is
// introduced by a definition and the law IS that definition read
// through `∈`, so set_tac — definitional unfolding to a first-order
// residual, then a kernel-checked refute — is the whole argument, and
// there is nothing further to narrate.
//
// The file runs from the simplest set to the most structured: the two
// constants, then adding and removing a single element, then the
// binary operations, the image of a map, and the big operators.

// NotInEmpty — nothing is in the empty set (∅ is the predicate that
// rejects everything).
var NotInEmpty = notInEmptyThm{family.Add(registry.ProofEntry{
	Name: "NotInEmpty",
	Key:  "prop_7e122366a48bed73",
	Build: family.Theorem(
		"∀x:A. x ∉ ∅",
		BySets()),
})}

// InUniv — everything is in the universe (𝕌 is the predicate that
// accepts everything).
var InUniv = inUnivThm{family.Add(registry.ProofEntry{
	Name: "InUniv",
	Key:  "prop_b6bc791c11a07702",
	Build: family.Theorem(
		"∀x:A. x ∈ 𝕌",
		BySets()),
})}

// ExtensionWithin — two subsets of c are equal when they hold the same
// points of c: extensionality read inside a carrier, for sets a group
// on c builds from its subsets.
var ExtensionWithin = extensionWithinThm{family.Add(registry.ProofEntry{
	Name: "ExtensionWithin",
	Key:  "prop_4dc5773145215d1d",
	Build: family.Theorem(
		Statement{
			Binders: "∀c s t:set(A).",
			Hypotheses: []string{
				"s ⊆ c",
				"t ⊆ c",
				"∀x:A. x ∈ c ⇒ (x ∈ s ⇔ x ∈ t)",
			},
			Conclusion: "s = t",
		},
		BySets()),
})}

// InInsert — adding x to s admits exactly x and whatever s already
// admitted.
var InInsert = inInsertThm{family.Add(registry.ProofEntry{
	Name: "InInsert",
	Key:  "prop_b98966155120782c",
	Build: family.Theorem(
		"∀s:set(A). ∀x y:A. y ∈ insert(x, s) ⇔ y = x ∨ y ∈ s",
		BySets()),
})}

// InSing — a singleton admits its one element and nothing else. `{y}`
// is `insert(y, ∅)`, so this is InInsert's degenerate case, but it is
// the form downstream chapters reach for.
var InSing = inSingThm{family.Add(registry.ProofEntry{
	Name: "InSing",
	Key:  "prop_97ebe055ce788b84",
	Build: family.Theorem(
		"∀x y:A. x ∈ {y} ⇔ x = y",
		BySets()),
})}

// InDelete — removing y from s leaves everything s admitted except y.
var InDelete = inDeleteThm{family.Add(registry.ProofEntry{
	Name: "InDelete",
	Key:  "prop_1d7436ddf945c19b",
	Build: family.Theorem(
		"∀s:set(A). ∀x y:A. x ∈ delete(s, y) ⇔ x ∈ s ∧ ¬(x = y)",
		BySets()),
})}

// InUnion — a union admits what either side admits.
var InUnion = inUnionThm{family.Add(registry.ProofEntry{
	Name: "InUnion",
	Key:  "prop_ab178fdaf76801a3",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. x ∈ s ∪ t ⇔ x ∈ s ∨ x ∈ t",
		BySets()),
})}

// InInter — an intersection admits what both sides admit.
var InInter = inInterThm{family.Add(registry.ProofEntry{
	Name: "InInter",
	Key:  "prop_f5f7f62d4affb387",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. x ∈ s ∩ t ⇔ x ∈ s ∧ x ∈ t",
		BySets()),
})}

// InDiff — a difference admits what the left side admits and the right
// side does not.
var InDiff = inDiffThm{family.Add(registry.ProofEntry{
	Name: "InDiff",
	Key:  "prop_d5eb1bb56e147ca1",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. x ∈ s ∖ t ⇔ x ∈ s ∧ x ∉ t",
		BySets()),
})}

// InImage — the image of s under f admits exactly the values f takes on
// s. The one member whose statement needs a second element type: the
// map need not be an endofunction.
var InImage = inImageThm{family.Add(registry.ProofEntry{
	Name: "InImage",
	Key:  "prop_dd2ac3e90d700533",
	Build: family.Theorem(
		"∀f:(A → B). ∀s:set(A). ∀y:B. y ∈ image(f, s) ⇔ ∃x:A. y = f(x) ∧ x ∈ s",
		BySets()),
})}

// InUnions — the big union of a family admits what SOME member admits.
var InUnions = inUnionsThm{family.Add(registry.ProofEntry{
	Name: "InUnions",
	Key:  "prop_49737942ed9cc95a",
	Build: family.Theorem(
		"∀s:set(set(A)). ∀x:A. x ∈ ⋃s ⇔ ∃u:set(A). u ∈ s ∧ x ∈ u",
		BySets()),
})}

// InInters — the big intersection of a family admits what EVERY member
// admits. (Over the empty family that is everything, which is why 𝕌
// and not ∅ is ⋂'s unit.)
var InInters = inIntersThm{family.Add(registry.ProofEntry{
	Name: "InInters",
	Key:  "prop_79142e76e521241f",
	Build: family.Theorem(
		"∀s:set(set(A)). ∀x:A. x ∈ ⋂s ⇔ ∀u:set(A). u ∈ s ⇒ x ∈ u",
		BySets()),
})}

// ---------------------------------------------------------------------------
// Taking a set apart
// ---------------------------------------------------------------------------
//
// The laws above say what membership in a BUILT set
// amounts to; they say nothing about a set one has not built. The three
// facts here are what let a proof get hold of an arbitrary set: decide
// whether it is empty, and if it is not, split off one of its elements.
//
// This is where the chapter stops being purely definitional. The ⇒
// directions here have to EXHIBIT something — a member, or the rest of
// the set once a member is removed — and `delete(s, x)` is the witness
// that does it. So these carry the chapter's only proof structure, and
// its only dependencies.

// MemberNotEmpty — a set is non-empty exactly when it has a member.
//
// The two sides say the same thing in the two registers this chapter
// keeps apart: `¬(s = ∅)` is about the SET, `∃x. x ∈ s` is about its
// ELEMENTS. Crossing between them is what makes emptiness something a
// proof can act on, and it is why this law has the widest reach in the
// chapter. It is still definitional — ∅ rejects everything, so a set
// that is not ∅ must disagree with it somewhere, and disagreeing with
// ∅ is exactly having a member.
var MemberNotEmpty = memberNotEmptyThm{family.Add(registry.ProofEntry{
	Name: "MemberNotEmpty",
	Key:  "prop_62fcf5e9d55dbdde",
	Build: family.Theorem(
		"∀s:set(A). (∃x:A. x ∈ s) ⇔ ¬(s = ∅)",
		BySets()),
})}

// Decomposition — x is in s exactly when s can be built by inserting x
// into a set that does not already contain it.
//
// The ⇐ direction is definitional: if `s = insert(x, t)` then x is in
// s, whatever t is. The ⇒ direction is the one with content, and it is
// the first place in the chapter where a proof must PRODUCE a set
// rather than reason about one — the t it needs is what remains of s
// once x is taken out.
var Decomposition = decompositionThm{family.Add(registry.ProofEntry{
	Name: "Decomposition",
	Key:  "prop_a6479ac1f3810a4e",
	Build: family.Theorem(
		"∀x:A. ∀s:set(A). x ∈ s ⇔ ∃t:set(A). s = insert(x, t) ∧ x ∉ t",
		func(a *Argument, x, s Term) {
			a.Iff()
			a.Forward(
				"x₀ is in s₀, and what remains once it is removed is what it was inserted into",
				func(a *Argument, member Fact) { // member: x₀ ∈ s₀
					a.Take(deleteFrom(a.Ctx(), s, x))
					a.Do(BySets(member))
				})
			a.Backward(
				"s₀ is x₀ inserted into something, so x₀ is in it",
				func(a *Argument, ins Fact) { // ins: ∃t. s₀ = insert(x₀, t) ∧ x₀ ∉ t
					a.Do(BySets(ins))
				})
		}),
})}

// SetCases — every set is either empty or splits off one of its
// elements.
//
// The two facts above compose into the case analysis the rest of set
// theory runs on: MemberNotEmpty turns "not empty" into a member, and
// Decomposition turns that member into the split. Which disjunct holds
// is not decided here — the theorem says only that one of them does,
// which is exactly what a proof reasoning about an arbitrary set needs.
var SetCases = setCasesThm{family.Add(registry.ProofEntry{
	Name: "SetCases",
	Key:  "prop_e4bc945453986add",
	Build: family.Theorem(
		"∀s:set(A). s = ∅ ∨ (∃x:A. ∃t:set(A). s = insert(x, t) ∧ x ∉ t)",
		func(a *Argument, s *TermWrapper) {
			// The left disjunct settles the goal on its own, so the rest of
			// the argument runs with s₀ non-empty. (The goal keeps both
			// disjuncts throughout — Unless supplies the hypothesis, it does
			// not narrow what is to be proved.)
			nonempty := a.Unless(
				s.Eq(emptySet(a.Ctx())),
				"an empty s₀ is the left disjunct outright",
				Given(func(b *Argument, isEmpty Fact) {
					b.Show(
						"s₀ = ∅ is what that disjunct claims",
						By(Normalized, isEmpty))
				}))

			_, member := a.Obtain(
				"a non-empty s has a member x₀",
				"∃x:A. x ∈ s",
				By(nonempty, MemberNotEmpty))

			split := a.Have(
				"x splits s — what remains once x is removed is what it was inserted into",
				"∃t:set(A). s = insert(x, t) ∧ x ∉ t",
				By(member, Decomposition))

			a.Show(
				"that split IS the right disjunct, at x₀",
				By(split))
		}),
})}

// ---------------------------------------------------------------------------
// Quantifiers over a constructed set
// ---------------------------------------------------------------------------
//
// The constructor laws say what it takes for ONE element to be in a
// constructed set. These six say what happens when a whole quantifier
// ranges over one: the constructor is dissolved, and what is left
// quantifies over the pieces the set was built from. Adding an element
// splits that element off; a union splits into its two sides; a big
// union becomes two quantifiers, one choosing a member of the family
// and one ranging inside it.
//
// The file is read in pairs, because ∀ and ∃ are dual throughout. Over
// a set assembled from pieces, a universal claim is the CONJUNCTION of
// the claims about the pieces and an existential one is their
// DISJUNCTION — and that exchange is the only difference between each
// member below and the one after it.
//
// This is what makes quantification over a constructed set usable: a
// hypothesis about all of `s ∪ t` is consumed by taking the side one
// needs, and a goal about all of it is discharged by proving both.
//
// Each proof is the chapter's one move, a bare `BySets()` — a
// transfer law is a membership law read under a quantifier, so the same
// definitional unfolding settles it.

// ForallInInsert — a universal claim about an enlarged set separates
// into the element added and the set it was added to. It is the shape
// an induction over a finite set leaves behind at every step.
var ForallInInsert = forallInInsertThm{family.Add(registry.ProofEntry{
	Name: "ForallInInsert",
	Key:  "prop_e090f5bc3247274f",
	Build: family.Theorem(
		"∀P:(A → bool). ∀a:A. ∀s:set(A). (∀x:A. x ∈ insert(a, s) ⇒ P(x)) ⇔ P(a) ∧ (∀x:A. x ∈ s ⇒ P(x))",
		BySets()),
})}

// ExistsInInsert — dually, a witness in an enlarged set is either the
// element added or a witness already present in the set it was added
// to.
var ExistsInInsert = existsInInsertThm{family.Add(registry.ProofEntry{
	Name: "ExistsInInsert",
	Key:  "prop_7dba9c8fdc3c4403",
	Build: family.Theorem(
		"∀P:(A → bool). ∀a:A. ∀s:set(A). (∃x:A. x ∈ insert(a, s) ∧ P(x)) ⇔ P(a) ∨ (∃x:A. x ∈ s ∧ P(x))",
		BySets()),
})}

// ForallInUnion — a universal claim about a union is the two claims
// about its sides and nothing further: neither side constrains the
// other.
var ForallInUnion = forallInUnionThm{family.Add(registry.ProofEntry{
	Name: "ForallInUnion",
	Key:  "prop_6fe2bf44380a38fe",
	Build: family.Theorem(
		"∀P:(A → bool). ∀s t:set(A). "+
			"    (∀x:A. x ∈ s ∪ t ⇒ P(x)) ⇔ (∀x:A. x ∈ s ⇒ P(x)) ∧ (∀x:A. x ∈ t ⇒ P(x))",
		BySets()),
})}

// ExistsInUnion — a witness in a union is a witness in one of the two
// sides; which side it was found in is what the disjunction records.
var ExistsInUnion = existsInUnionThm{family.Add(registry.ProofEntry{
	Name: "ExistsInUnion",
	Key:  "prop_de4906295bfa60b3",
	Build: family.Theorem(
		"∀P:(A → bool). ∀s t:set(A). "+
			"    (∃x:A. x ∈ s ∪ t ∧ P(x)) ⇔ (∃x:A. x ∈ s ∧ P(x)) ∨ (∃x:A. x ∈ t ∧ P(x))",
		BySets()),
})}

// ForallInUnions — a universal claim about a big union is a universal
// claim about the family: it has to hold throughout every member, and
// the two quantifiers are the two choices that reach an element.
var ForallInUnions = forallInUnionsThm{family.Add(registry.ProofEntry{
	Name: "ForallInUnions",
	Key:  "prop_69b21e6c5d96eb35",
	Build: family.Theorem(
		"∀P:(A → bool). ∀s:set(set(A)). (∀x:A. x ∈ ⋃s ⇒ P(x)) ⇔ ∀t:set(A). t ∈ s ⇒ ∀x:A. x ∈ t ⇒ P(x)",
		BySets()),
})}

// ExistsInUnions — a witness in a big union arrives together with the
// member of the family it was found in, so one existential becomes two.
var ExistsInUnions = existsInUnionsThm{family.Add(registry.ProofEntry{
	Name: "ExistsInUnions",
	Key:  "prop_88343e5011f6a1ab",
	Build: family.Theorem(
		"∀P:(A → bool). ∀s:set(set(A)). (∃x:A. x ∈ ⋃s ∧ P(x)) ⇔ ∃t:set(A). t ∈ s ∧ (∃x:A. x ∈ t ∧ P(x))",
		BySets()),
})}
