// set_order.go — the chapter: inclusion.
//
// Six parts, marked by banners:
//
// - ⊆ as a partial order, and its bounds
// - ⊊, the strict part of the ordering
// - Where ∩, ∪, ⋂ and ⋃ sit in the ordering
// - Inclusion against the element-wise constructions
// - Inclusion recognised as an equation
// - A monotone map has a fixed point

package set_order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// ⊆ as a partial order, and its bounds
// ---------------------------------------------------------------------------
//
// The three laws that make inclusion an ordering rather than merely a
// relation, and then the two sets that bound it from below and above,
// each stated twice: as a bound, and as the LEAST or GREATEST one.

// SubsetRefl — inclusion is reflexive. Each element of s is required to
// be an element of s, which asks nothing.
var SubsetRefl = subsetReflThm{family.Add(registry.ProofEntry{
	Name: "SubsetRefl",
	Key:  "prop_a7a10fe9bd15bca5",
	Build: family.Theorem(
		"∀s:set(A). s ⊆ s",
		BySets()),
})}

// SubsetTrans — inclusion composes. An element of the smallest set is
// carried into the middle one, and from there into the largest.
var SubsetTrans = subsetTransThm{family.Add(registry.ProofEntry{
	Name: "SubsetTrans",
	Key:  "prop_81de800f45f9039c",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t u:set(A).",
			Hypotheses: []string{
				"s ⊆ t",
				"t ⊆ u",
			},
			Conclusion: "s ⊆ u",
		},
		BySets()),
})}

// SubsetAntisym — mutual inclusion is equality. Each set's elements are
// the other's, and a set is nothing but the elements it admits, so
// nothing is left to tell the two apart.
var SubsetAntisym = subsetAntisymThm{family.Add(registry.ProofEntry{
	Name: "SubsetAntisym",
	Key:  "prop_6f8f033495690248",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(A).",
			Hypotheses: []string{
				"s ⊆ t",
				"t ⊆ s",
			},
			Conclusion: "s = t",
		},
		BySets()),
})}

// SubsetAntisymEq — antisymmetry with its converse, which is immediate:
// equality of sets is exactly mutual inclusion. This is the form a set
// identity is usually proved in, since it splits the goal into the two
// inclusions.
var SubsetAntisymEq = subsetAntisymEqThm{family.Add(registry.ProofEntry{
	Name: "SubsetAntisymEq",
	Key:  "prop_2e28c1030dab38ea",
	Build: family.Theorem(
		"∀s t:set(A). s = t ⇔ s ⊆ t ∧ t ⊆ s",
		BySets()),
})}

// EmptySubset — ∅ is below everything. The inclusion is vacuous: there
// is no element to place.
var EmptySubset = emptySubsetThm{family.Add(registry.ProofEntry{
	Name: "EmptySubset",
	Key:  "prop_267ee82a1042fd1a",
	Build: family.Theorem(
		"∀s:set(A). ∅ ⊆ s",
		BySets()),
})}

// SubsetEmpty — and ∅ is the LEAST set, with nothing below it: a set
// included in ∅ has nowhere to keep an element, so it is ∅.
var SubsetEmpty = subsetEmptyThm{family.Add(registry.ProofEntry{
	Name: "SubsetEmpty",
	Key:  "prop_bf730de3bfcf2d35",
	Build: family.Theorem(
		"∀s:set(A). s ⊆ ∅ ⇔ s = ∅",
		BySets()),
})}

// SubsetUniv — 𝕌 is above everything. It admits every element of the
// type, so in particular every element of s.
var SubsetUniv = subsetUnivThm{family.Add(registry.ProofEntry{
	Name: "SubsetUniv",
	Key:  "prop_5cca12a94dfaf45f",
	Build: family.Theorem(
		"∀s:set(A). s ⊆ 𝕌",
		BySets()),
})}

// UnivSubset — and 𝕌 is the GREATEST set, with nothing above it: a set
// that includes 𝕌 already holds every element of the type.
var UnivSubset = univSubsetThm{family.Add(registry.ProofEntry{
	Name: "UnivSubset",
	Key:  "prop_80159c917416cf34",
	Build: family.Theorem(
		"∀s:set(A). 𝕌 ⊆ s ⇔ s = 𝕌",
		BySets()),
})}

// ---------------------------------------------------------------------------
// ⊊, the strict part of the ordering
// ---------------------------------------------------------------------------
//
// The strict order's own laws, and its bounds.

// NotProperSubsetEmpty — no set is a proper subset of ∅.
//
// ∅ is the bottom of the ordering, so the only set below it is itself,
// and "properly below" excludes that.
var NotProperSubsetEmpty = notProperSubsetEmptyThm{family.Add(registry.ProofEntry{
	Name: "NotProperSubsetEmpty",
	Key:  "prop_5b7f18d18fefab7a",
	Build: family.Theorem(
		"∀s:set(A). ¬(s ⊊ ∅)",
		BySets()),
})}

// ProperSubsetIrrefl — ⊊ is irreflexive: it asks for a difference, and
// a set does not differ from itself.
var ProperSubsetIrrefl = properSubsetIrreflThm{family.Add(registry.ProofEntry{
	Name: "ProperSubsetIrrefl",
	Key:  "prop_93a4539c36ad0717",
	Build: family.Theorem(
		"∀s:set(A). ¬(s ⊊ s)",
		BySets()),
})}

// ProperSubsetTrans — ⊊ is transitive. The inclusions compose, and the
// strictness survives: were the two ends equal, the middle set would be
// caught between a set and itself and would have to equal both.
var ProperSubsetTrans = properSubsetTransThm{family.Add(registry.ProofEntry{
	Name: "ProperSubsetTrans",
	Key:  "prop_804a483ab5098dd2",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t u:set(A).",
			Hypotheses: []string{
				"s ⊊ t",
				"t ⊊ u",
			},
			Conclusion: "s ⊊ u",
		},
		BySets()),
})}

// ProperSubsetWitness — proper inclusion exhibited by an element rather
// than asserted as an inequality.
//
// Read through their elements, the one element t holds and s does not is
// all the inequality of the two sets ever amounts to. It is also what
// makes ⊊ usable: an argument that has to break a proper inclusion open
// gets a concrete element out of it rather than a negated equation.
var ProperSubsetWitness = properSubsetWitnessThm{family.Add(registry.ProofEntry{
	Name: "ProperSubsetWitness",
	Key:  "prop_dabd343f244d528d",
	Build: family.Theorem(
		"∀s t:set(A). s ⊊ t ⇔ s ⊆ t ∧ (∃x:A. x ∈ t ∧ x ∉ s)",
		BySets()),
})}

// ProperSubsetSubsetTrans — a strict step followed by an inclusion is
// still strict: the element of t that s misses lies in u as well, so s
// falls short of u too.
var ProperSubsetSubsetTrans = properSubsetSubsetTransThm{family.Add(registry.ProofEntry{
	Name: "ProperSubsetSubsetTrans",
	Key:  "prop_a69cf29694636d2e",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t u:set(A).",
			Hypotheses: []string{
				"s ⊊ t",
				"t ⊆ u",
			},
			Conclusion: "s ⊊ u",
		},
		BySets()),
})}

// SubsetProperSubsetTrans — and the mirror: an inclusion followed by a
// strict step is strict. The element of u that t lacks is lacked by s
// too, since s lies inside t.
var SubsetProperSubsetTrans = subsetProperSubsetTransThm{family.Add(registry.ProofEntry{
	Name: "SubsetProperSubsetTrans",
	Key:  "prop_29a92d45aefe3914",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t u:set(A).",
			Hypotheses: []string{
				"s ⊆ t",
				"t ⊊ u",
			},
			Conclusion: "s ⊊ u",
		},
		BySets()),
})}

// NotUnivProperSubset — no set is a proper superset of 𝕌.
//
// 𝕌 is the top of the ordering, so the only set above it is itself, and
// "properly above" excludes that.
var NotUnivProperSubset = notUnivProperSubsetThm{family.Add(registry.ProofEntry{
	Name: "NotUnivProperSubset",
	Key:  "prop_bc6acd1c52c66555",
	Build: family.Theorem(
		"∀s:set(A). ¬(𝕌 ⊊ s)",
		BySets()),
})}

// ProperSubsetUniv — a set falls properly short of 𝕌 exactly when it
// misses something. Being inside 𝕌 costs nothing, so a witness to the
// difference is the whole of what proper inclusion asks for.
var ProperSubsetUniv = properSubsetUnivThm{family.Add(registry.ProofEntry{
	Name: "ProperSubsetUniv",
	Key:  "prop_61e912bd2f840806",
	Build: family.Theorem(
		"∀s:set(A). s ⊊ 𝕌 ⇔ ∃x:A. x ∉ s",
		BySets()),
})}

// ---------------------------------------------------------------------------
// Where ∩, ∪, ⋂ and ⋃ sit in the ordering
// ---------------------------------------------------------------------------
//
// Meeting sets moves DOWN the ordering and joining them moves UP: an
// intersection is below each set it is taken over, a union above each.
// But the sharp statements are the ones that characterize the two
// operations rather than merely locate them — `s ⊆ t ∩ u` exactly when s
// is below both, `s ∪ t ⊆ u` exactly when both are below u. Those say
// that ∩ is the greatest lower bound and ∪ the least upper bound, which
// is the whole content of calling this a lattice.
//
// The last seven repeat the story over a whole FAMILY of sets, where
// the same two characterizations hold at arbitrary arity, and where the
// two operations acquire a direction in the family itself: ⋃ rises with
// it and ⋂ falls. Each of those has a sharper form, in which the
// families are not compared by inclusion at all — only by whether each
// member of one is covered by a member of the other.

// SubsetInter — ∩ is the greatest lower bound: to sit below the meet is
// exactly to sit below both of its arguments.
var SubsetInter = subsetInterThm{family.Add(registry.ProofEntry{
	Name: "SubsetInter",
	Key:  "prop_fdbb1fb38c82bfc6",
	Build: family.Theorem(
		"∀s t u:set(A). s ⊆ t ∩ u ⇔ s ⊆ t ∧ s ⊆ u",
		BySets()),
})}

// UnionSubset — and dually ∪ is the least upper bound: to sit above the
// join is exactly to sit above both of its arguments.
var UnionSubset = unionSubsetThm{family.Add(registry.ProofEntry{
	Name: "UnionSubset",
	Key:  "prop_235c039e0bb08460",
	Build: family.Theorem(
		"∀s t u:set(A). s ∪ t ⊆ u ⇔ s ⊆ u ∧ t ⊆ u",
		BySets()),
})}

// InterSubset — an intersection is below each of the two sets it is
// taken over, whichever side that set is written on. It admits only
// what both admit, so in particular only what either one does.
var InterSubset = interSubsetThm{family.Add(registry.ProofEntry{
	Name: "InterSubset",
	Key:  "prop_adb5bf62d0f3160b",
	Build: family.Theorem(
		"∀s t:set(A). s ∩ t ⊆ s ∧ t ∩ s ⊆ s",
		BySets()),
})}

// SubsetUnion — and the mirror: a set is below any union it takes part
// in, on either side, since the union admits everything either side
// does.
var SubsetUnion = subsetUnionThm{family.Add(registry.ProofEntry{
	Name: "SubsetUnion",
	Key:  "prop_8622544d270fa641",
	Build: family.Theorem(
		"∀s t:set(A). s ⊆ s ∪ t ∧ s ⊆ t ∪ s",
		BySets()),
})}

// IntersSubset — bounding ⋂u from above needs only one member of u to
// do the bounding, but it does need u to HAVE a member: the second
// hypothesis says nothing at all when there are none, and ⋂∅ is 𝕌
// rather than anything small.
var IntersSubset = intersSubsetThm{family.Add(registry.ProofEntry{
	Name: "IntersSubset",
	Key:  "prop_ec28b7c2cf8f5406",
	Build: family.Theorem(
		Statement{
			Binders: "∀u:set(set(A)). ∀s:set(A).",
			Hypotheses: []string{
				"¬(u = ∅)",
				"∀t:set(A). t ∈ u ⇒ t ⊆ s",
			},
			Conclusion: "⋂u ⊆ s",
		},
		BySets()),
})}

// IntersSubsetStrong — the sharper form, and the one an argument
// usually wants: a single member of u that already sits inside s bounds
// the whole intersection, since ⋂u is inside that member. It implies
// IntersSubset, whose two hypotheses together produce such a member.
var IntersSubsetStrong = intersSubsetStrongThm{family.Add(registry.ProofEntry{
	Name: "IntersSubsetStrong",
	Key:  "prop_21fc05d8f317e80b",
	Build: family.Theorem(
		Statement{
			Binders: "∀u:set(set(A)). ∀s:set(A).",
			Hypotheses: []string{
				"∃t:set(A). t ∈ u ∧ t ⊆ s",
			},
			Conclusion: "⋂u ⊆ s",
		},
		BySets()),
})}

// SubsetInters — ⋂ is the greatest lower bound at arbitrary arity: to
// sit below the intersection of a family is exactly to sit below every
// one of its members. The empty family is no exception here — with
// nothing to be below, the condition is vacuous and ⋂∅ is 𝕌.
var SubsetInters = subsetIntersThm{family.Add(registry.ProofEntry{
	Name: "SubsetInters",
	Key:  "prop_256cb3c6968157de",
	Build: family.Theorem(
		"∀f:set(set(A)). ∀s:set(A). s ⊆ ⋂f ⇔ ∀t:set(A). t ∈ f ⇒ s ⊆ t",
		BySets()),
})}

// UnionsSubset — and dually ⋃ is the least upper bound: to sit above the
// union of a family is exactly to sit above every one of its members.
var UnionsSubset = unionsSubsetThm{family.Add(registry.ProofEntry{
	Name: "UnionsSubset",
	Key:  "prop_1ebcd8007e384fc4",
	Build: family.Theorem(
		"∀f:set(set(A)). ∀t:set(A). ⋃f ⊆ t ⇔ ∀s:set(A). s ∈ f ⇒ s ⊆ t",
		BySets()),
})}

// MemberSubsetUnions — ⋃ is an upper bound: each member of a family
// lies inside its union. The set closer does not find this on its own
// where the membership is only a hypothesis — the union's membership
// asks for a witness member, and nothing names it — so it is stated
// once and cited.
var MemberSubsetUnions = memberSubsetUnionsThm{family.Add(registry.ProofEntry{
	Name: "MemberSubsetUnions",
	Key:  "prop_51a349a9e4fd6d15",
	Build: family.Theorem(
		Statement{
			Binders: "∀f:set(set(A)). ∀t:set(A).",
			Hypotheses: []string{
				"t ∈ f",
			},
			Conclusion: "t ⊆ ⋃f",
		},
		BySets()),
})}

// SubsetUnions — ⋃ is monotone: a larger family has a larger union,
// since every set contributing to the smaller union already belongs to
// the larger family. Note the two ⊆ here are at different types — the
// hypothesis compares families, the conclusion compares sets.
var SubsetUnions = subsetUnionsThm{family.Add(registry.ProofEntry{
	Name: "SubsetUnions",
	Key:  "prop_3bd75db2583752ce",
	Build: family.Theorem(
		Statement{
			Binders: "∀f g:set(set(A)).",
			Hypotheses: []string{
				"f ⊆ g",
			},
			Conclusion: "⋃f ⊆ ⋃g",
		},
		BySets()),
})}

// IntersAntitone — and ⋂ is antitone, which is the mirror of
// SubsetUnions rather than an independent fact: a larger family imposes
// more conditions, and every condition it adds cuts the intersection
// down further. The two ⊆ are again at different types.
var IntersAntitone = intersAntitoneThm{family.Add(registry.ProofEntry{
	Name: "IntersAntitone",
	Key:  "prop_39188a0c79c11679",
	Build: family.Theorem(
		Statement{
			Binders: "∀f g:set(set(A)).",
			Hypotheses: []string{
				"g ⊆ f",
			},
			Conclusion: "⋂f ⊆ ⋂g",
		},
		BySets()),
})}

// UnionsMonotoneRefine — the sharp form of SubsetUnions, and the one
// that says what ⋃ really depends on. The families need not be
// comparable at all: it is enough that each member of the first sit
// inside SOME member of the second, which need not be that member
// itself. SubsetUnions is the special case where it is.
var UnionsMonotoneRefine = unionsMonotoneRefineThm{family.Add(registry.ProofEntry{
	Name: "UnionsMonotoneRefine",
	Key:  "prop_d9017adcb350f4be",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(set(A)).",
			Hypotheses: []string{
				"∀x:set(A). x ∈ s ⇒ ∃y:set(A). y ∈ t ∧ x ⊆ y",
			},
			Conclusion: "⋃s ⊆ ⋃t",
		},
		func(a *Argument, s, t Term, covering Fact) {
			// Alone in this chapter, the close needs a premise: the
			// driver unfolds ⋃-membership into an existential carrying
			// an equation, and discharges it against the covering
			// witness the premise supplies.
			a.Do(BySets(covering))
		}),
})}

// IntersAntitoneRefine — and the mirror, with the covering read the
// other way round: each member of the second family has to contain a
// member of the first. It stands to IntersAntitone exactly as
// UnionsMonotoneRefine stands to SubsetUnions.
var IntersAntitoneRefine = intersAntitoneRefineThm{family.Add(registry.ProofEntry{
	Name: "IntersAntitoneRefine",
	Key:  "prop_caf7567278d915eb",
	Build: family.Theorem(
		Statement{
			Binders: "∀s t:set(set(A)).",
			Hypotheses: []string{
				"∀y:set(A). y ∈ t ⇒ ∃x:set(A). x ∈ s ∧ x ⊆ y",
			},
			Conclusion: "⋂s ⊆ ⋂t",
		},
		BySets()),
})}

// ---------------------------------------------------------------------------
// Inclusion against the element-wise constructions
// ---------------------------------------------------------------------------
//
// Adding an element to a set, or removing one, changes it by a single
// explicit amount. So an inclusion involving one of them splits into a
// condition on that one element and an inclusion of what was already
// there — which is what most of the members below say. The two at the
// end are the degenerate cases of that: ∖ only ever removes, and a
// singleton's inclusion is its one element's membership.

// InsertSubset — a set grown by one element fits inside t exactly when
// the old set does and the new element is in t. The two conditions are
// independent because insert adds nothing else.
var InsertSubset = insertSubsetThm{family.Add(registry.ProofEntry{
	Name: "InsertSubset",
	Key:  "prop_8a514b18604e1fd0",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. insert(x, s) ⊆ t ⇔ x ∈ t ∧ s ⊆ t",
		BySets()),
})}

// DeleteSubset — removing an element can only shrink a set: what is
// left admits nothing it did not admit before.
var DeleteSubset = deleteSubsetThm{family.Add(registry.ProofEntry{
	Name: "DeleteSubset",
	Key:  "prop_38e0439d4bfc565e",
	Build: family.Theorem(
		"∀s:set(A). ∀x:A. delete(s, x) ⊆ s",
		BySets()),
})}

// SubsetDelete — and InsertSubset's mirror, one element taken away
// rather than added: to fit inside t with x removed is to fit inside t
// while avoiding x.
var SubsetDelete = subsetDeleteThm{family.Add(registry.ProofEntry{
	Name: "SubsetDelete",
	Key:  "prop_efca1254ff1c154f",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. s ⊆ delete(t, x) ⇔ x ∉ s ∧ s ⊆ t",
		BySets()),
})}

// SubsetInsertDelete — insertion and deletion are adjoint: granting x
// on the right of an inclusion is the same concession as forfeiting it
// on the left. Both sides say that everything in s except possibly x
// lies in t.
var SubsetInsertDelete = subsetInsertDeleteThm{family.Add(registry.ProofEntry{
	Name: "SubsetInsertDelete",
	Key:  "prop_6bd09c32b0a7d50e",
	Build: family.Theorem(
		"∀s t:set(A). ∀x:A. s ⊆ insert(x, t) ⇔ delete(s, x) ⊆ t",
		BySets()),
})}

// ForallSubsetInsert — quantifying over the subsets of insert(a, t) is
// quantifying over the subsets of t twice. A subset s of insert(a, t)
// has delete(s, a) ⊆ t, and is told apart by whether it holds a: it is
// insert(a, delete(s, a)) when it does and delete(s, a) itself when it
// does not, so it is one of the two sets the right-hand side speaks
// about. The converse needs no case: a subset of t, and that subset
// with a added, are both subsets of insert(a, t).
//
// The closer settles each inclusion and each set identity but not the
// whole at once: P is an arbitrary predicate on sets, so carrying P
// from the reassembled set to s is a rewrite by a set EQUATION, which
// each branch states and proves as its own fact.
var ForallSubsetInsert = forallSubsetInsertThm{family.Add(registry.ProofEntry{
	Name: "ForallSubsetInsert",
	Key:  "prop_59a27ff9dae5b12b",
	Build: family.Theorem(
		"∀P:(set(A) → bool). ∀t:set(A). ∀a:A. "+
			"    (∀s:set(A). s ⊆ insert(a, t) ⇒ P(s)) ⇔ (∀s:set(A). s ⊆ t ⇒ P(s) ∧ P(insert(a, s)))",
		func(arg *Argument, P, t, a Term) {
			arg.Iff()
			arg.Forward(
				"a subset of t, and that subset with a added, are both subsets of insert(a, t)",
				func(arg *Argument, all Fact) { // all: ∀s. s ⊆ insert(a, t) ⇒ P(s)
					arg.Show(
						"both are subsets of insert(a, t), so P holds of both",
						BySets(all))
				})
			arg.Backward(
				"a subset s of insert(a, t) has delete(s, a) ⊆ t, and is that set with a put back if s held a",
				func(arg *Argument, twice Fact) { // twice: ∀s. s ⊆ t ⇒ P(s) ∧ P(insert(a, s))
					arg.Fix()           // s, a subset of insert(a, t)
					sub := arg.Assume() // sub: s ⊆ insert(a, t)
					rest := arg.Term("delete(s, a)")
					below := arg.Have(
						"what is left of s once a is removed lies in t",
						"delete(s, a) ⊆ t",
						BySets(sub))
					arg.Cases(arg.Term("a ∈ s"))
					arg.When(
						"a ∈ s: s is delete(s, a) with a put back, and P holds of that set",
						func(arg *Argument, in Fact) {
							whole := arg.Have(
								"putting a back restores s",
								"insert(a, delete(s, a)) = s",
								BySets(in))
							// Normalized: whole rewrites P's argument to s — a
							// normalization, not a refutation.
							arg.Show(
								"P(insert(a, delete(s, a))) is P(s)",
								By(Normalized, twice.At(rest), below, whole))
						})
					arg.Otherwise(
						"a ∉ s: removing a changed nothing, and P holds of delete(s, a)",
						func(arg *Argument, out Fact) {
							same := arg.Have(
								"removing an absent element leaves s as it was",
								"delete(s, a) = s",
								BySets(out))
							// Normalized: same rewrites P's argument to s, as above.
							arg.Show(
								"P(delete(s, a)) is P(s)",
								By(Normalized, twice.At(rest), below, same))
						})
				})
		}),
})}

// SubsetDiff — taking a difference can only shrink a set, whatever is
// subtracted: `s ∖ t` admits only what s already did.
var SubsetDiff = subsetDiffThm{family.Add(registry.ProofEntry{
	Name: "SubsetDiff",
	Key:  "prop_f651454c7a06806c",
	Build: family.Theorem(
		"∀s t:set(A). s ∖ t ⊆ s",
		BySets()),
})}

// SingSubset — membership IS an inclusion, once the element is packaged
// as a singleton. This is the bridge between the two registers the
// chapter keeps apart, and the reason a fact about one element can be
// fed to a law stated about sets.
var SingSubset = singSubsetThm{family.Add(registry.ProofEntry{
	Name: "SingSubset",
	Key:  "prop_52a02a48ed77faf",
	Build: family.Theorem(
		"∀s:set(A). ∀x:A. {x} ⊆ s ⇔ x ∈ s",
		BySets()),
})}

// ---------------------------------------------------------------------------
// Inclusion recognised as an equation
// ---------------------------------------------------------------------------
//
// An inclusion between s and t can be read off either binary operation
// without mentioning ⊆ at all: s sits inside t exactly when meeting t
// costs s nothing, and exactly when joining s to t adds nothing. These
// are the absorption laws, and they are how a lattice recovers its
// order from its operations.

// SubsetInterAbsorption — meeting t leaves s unchanged exactly when s
// was already inside t. Nothing of s is lost to the meet precisely when
// there was nothing outside t to lose.
var SubsetInterAbsorption = subsetInterAbsorptionThm{family.Add(registry.ProofEntry{
	Name: "SubsetInterAbsorption",
	Key:  "prop_1f9b4980e1082e75",
	Build: family.Theorem(
		"∀s t:set(A). s ∩ t = s ⇔ s ⊆ t",
		BySets()),
})}

// SubsetUnionAbsorption — joining t to s leaves t unchanged exactly
// when s was already inside t. Adding s contributes nothing precisely
// when it had nothing to contribute.
//
// Unlike its sibling, this one is proved one direction at a time: the
// closure binds s and t so that the equivalence can be split, and each
// direction is then a plain consequence of what ∪ and ⊆ mean.
var SubsetUnionAbsorption = subsetUnionAbsorptionThm{family.Add(registry.ProofEntry{
	Name: "SubsetUnionAbsorption",
	Key:  "prop_8e616af577aa150d",
	Build: family.Theorem(
		"∀s t:set(A). s ⊆ t ⇔ s ∪ t = t",
		func(a *Argument, s, t Term) {
			a.Iff()
			a.Forward(
				"every element of s is already an element of t, so s ∪ t admits exactly what t does",
				func(a *Argument, sub Fact) { // sub: s₀ ⊆ t₀
					a.Do(BySets(sub))
				})
			a.Backward(
				"s lies inside s ∪ t, which the equation says is t",
				func(a *Argument, join Fact) { // join: s₀ ∪ t₀ = t₀
					a.Do(BySets(join))
				})
		}),
})}

// ---------------------------------------------------------------------------
// A monotone map has a fixed point
// ---------------------------------------------------------------------------
//
// Every family of sets has a greatest lower bound, its intersection, and
// that is all it takes to fix a map that respects the ordering: intersect
// everything the map shrinks.

// KnasterTarski — say F shrinks b when F(b) ⊆ b, and let L be the
// intersection of the sets F shrinks. F(L) lies inside every one of
// them, so F shrinks L; applying F to that inclusion, F shrinks F(L) as
// well, so F(L) is one of them and contains L. The two inclusions are
// the equation.
var KnasterTarski = knasterTarskiThm{family.Add(registry.ProofEntry{
	Name: "KnasterTarski",
	Key:  "prop_8184a04efc25baf5",
	Build: family.Theorem(
		Statement{
			Binders: "∀F:(set(A) → set(A)).",
			Hypotheses: []string{
				"∀s t:set(A). s ⊆ t ⇒ F(s) ⊆ F(t)",
			},
			Conclusion: "F(⋂{b:set(A) | F(b) ⊆ b}) = ⋂{b:set(A) | F(b) ⊆ b}",
		},
		func(a *Argument, F *Arrow[Set[A], Set[A]], monotone Fact) {
			L, lDef := a.LetAs[Set[A]]("L", "⋂{b:set(A) | F(b) ⊆ b}")
			FL := F.Apply(L)
			lower := a.Have(
				"L lies inside every set F shrinks, being their intersection",
				"∀c:set(A). F(c) ⊆ c ⇒ L ⊆ c",
				BySets(lDef))
			intoEach := a.Have(
				"so does F(L): a set c that F shrinks contains L, so F(L) ⊆ F(c) ⊆ c",
				"∀c:set(A). F(c) ⊆ c ⇒ F(L) ⊆ c",
				a.ForEach(func(c *Expr[Set[A]]) Action {
					return By(lower.At(c), monotone.At(L, c), SubsetTrans.At(FL, F.Apply(c), c))
				}))
			below := a.Have(
				"so F(L) lies inside their intersection",
				"F(L) ⊆ L",
				BySets(lDef, intoEach))
			above := a.Have(
				"F applied to that inclusion gives F(F(L)) ⊆ F(L): F(L) is a set F shrinks, so it contains L",
				"L ⊆ F(L)",
				By(monotone.At(FL, L), below, lower.At(FL)))
			a.Show(
				"the two inclusions are the equation",
				By(SubsetAntisym.At(FL, L), below, above))
		}),
})}
