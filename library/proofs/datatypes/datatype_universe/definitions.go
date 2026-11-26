// definitions.go — the chapter's definitional layer: the encodings,
// the universe, the type carved out of it, and its constructors,
// minted here in the order the universe is built.
//
// A tree is represented as a predicate on pairs (num, A). The two
// pairing functions on ℕ come first, then the projections that undo
// them — each a choice: the component of SOME pair encoding the
// number, which injectivity makes unique — then the four injections
// that encode a number, an atom, a countable family and a pair of
// encodings as such predicates. encoded_bottom and encoded_node are the empty tree
// and the node; is_recspace is the least predicate closed under them,
// minted by the inductive door from those two rules; the type recspace(A) is the subset it
// carves out, stamped against the empty tree (encodedBottomRep, the first
// conjunct of UniverseRules); recspace_bottom and recspace_node read the two
// constructors into the type; family_nil is the empty family. family_cons, the
// countable-family constructor, is defined beside its consumers in
// datatype_universe.go.

package datatype_universe

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The pairing functions on ℕ, and their projections
// ---------------------------------------------------------------------------

// numPairDef — num_pair(x, y) = 2^x · (2y + 1).
var numPairDef = numPairDefThm{family.Define(registry.DefEntry{
	Name:      "numPairDef",
	Key:       "prop_2395f650465f07ed",
	Const:     "num_pair",
	Type:      "num → num → num",
	Equations: []string{"∀x y:num. num_pair(x, y) = nat_pow(2, x) * (2 * y + 1)"},
})}

// numTagDef — num_tag(b, x): double x, plus one when b.
var numTagDef = numTagDefThm{family.Define(registry.DefEntry{
	Name:      "numTagDef",
	Key:       "prop_d81de288422f3a50",
	Const:     "num_tag",
	Type:      "bool → num → num",
	Equations: []string{"∀b:bool. ∀x:num. num_tag(b, x) = COND(b, suc(2 * x), 2 * x)"},
})}

// numPairFstDef · numPairSndDef — the projections of num_pair: the first
// (second) component of some pair encoding n.
var numPairFstDef = numPairFstDefThm{family.Define(registry.DefEntry{
	Name:      "numPairFstDef",
	Key:       "prop_4aec295a01e3ed00",
	Const:     "num_pair_fst",
	Type:      "num → num",
	Equations: []string{"∀n:num. num_pair_fst(n) = εx:num. ∃y:num. n = num_pair(x, y)"},
	Deps:      []registry.EntryLike{numPairDef},
})}

var numPairSndDef = numPairSndDefThm{family.Define(registry.DefEntry{
	Name:      "numPairSndDef",
	Key:       "prop_31d6e866f83d67a4",
	Const:     "num_pair_snd",
	Type:      "num → num",
	Equations: []string{"∀n:num. num_pair_snd(n) = εy:num. ∃x:num. n = num_pair(x, y)"},
	Deps:      []registry.EntryLike{numPairDef},
})}

// numTagBitDef · numTagValueDef — the projections of num_tag: the tag (the
// value) of some pair encoding n.
var numTagBitDef = numTagBitDefThm{family.Define(registry.DefEntry{
	Name:      "numTagBitDef",
	Key:       "prop_c15fb966c89a3761",
	Const:     "num_tag_bit",
	Type:      "num → bool",
	Equations: []string{"∀n:num. num_tag_bit(n) ⇔ εb:bool. ∃x:num. n = num_tag(b, x)"},
	Deps:      []registry.EntryLike{numTagDef},
})}

var numTagValueDef = numTagValueDefThm{family.Define(registry.DefEntry{
	Name:      "numTagValueDef",
	Key:       "prop_ca505d8ab596c4cd",
	Const:     "num_tag_value",
	Type:      "num → num",
	Equations: []string{"∀n:num. num_tag_value(n) = εx:num. ∃b:bool. n = num_tag(b, x)"},
	Deps:      []registry.EntryLike{numTagDef},
})}

// ---------------------------------------------------------------------------
// The injections into predicates on (num, A)
// ---------------------------------------------------------------------------

// injectNumDef — a number, as the predicate holding at exactly that number.
var injectNumDef = injectNumDefThm{family.Define(registry.DefEntry{
	Name:      "injectNumDef",
	Key:       "prop_f28a6d1cd1511757",
	Const:     "inject_num",
	Type:      "num → num → A → bool",
	Equations: []string{"∀m:num. inject_num(m) = λn:num. λa:A. n = m"},
})}

// injectAtomDef — an atom, as the predicate holding at exactly that atom.
var injectAtomDef = injectAtomDefThm{family.Define(registry.DefEntry{
	Name:      "injectAtomDef",
	Key:       "prop_da692383afc9486f",
	Const:     "inject_atom",
	Type:      "A → num → A → bool",
	Equations: []string{"∀a:A. inject_atom(a) = λn:num. λb:A. b = a"},
})}

// injectFamilyDef — a countable family of encodings, read at the two
// components of the number.
var injectFamilyDef = injectFamilyDefThm{family.Define(registry.DefEntry{
	Name:  "injectFamilyDef",
	Key:   "prop_427114df09728bb2",
	Const: "inject_family",
	Type:  "(num → num → A → bool) → num → A → bool",
	Equations: []string{
		"∀f:(num → num → A → bool). inject_family(f) = λn:num. f(num_pair_fst(n), num_pair_snd(n))",
	},
	Deps: []registry.EntryLike{numPairFstDef, numPairSndDef},
})}

// injectPairDef — a pair of encodings, the tag of the number selecting the
// component.
var injectPairDef = injectPairDefThm{family.Define(registry.DefEntry{
	Name:  "injectPairDef",
	Key:   "prop_2a77119440fcd61a",
	Const: "inject_pair",
	Type:  "(num → A → bool) → (num → A → bool) → num → A → bool",
	Equations: []string{
		"∀f₁ f₂:(num → A → bool). " +
			"    inject_pair(f₁, f₂) = " +
			"    λn:num. λa:A. COND(num_tag_bit(n), f₁(num_tag_value(n), a), f₂(num_tag_value(n), a))",
	},
	Deps: []registry.EntryLike{numTagBitDef, numTagValueDef},
})}

// ---------------------------------------------------------------------------
// The universe
// ---------------------------------------------------------------------------

// encodedBottomDef — the empty tree: tag 0, paired with an arbitrary encoding.
var encodedBottomDef = encodedBottomDefThm{family.Define(registry.DefEntry{
	Name:      "encodedBottomDef",
	Key:       "prop_7f525c52db5321a4",
	Const:     "encoded_bottom",
	Type:      "num → A → bool",
	Equations: []string{"encoded_bottom = inject_pair(inject_num(0), εz:(num → A → bool). ⊤)"},
	Deps:      []registry.EntryLike{injectPairDef, injectNumDef},
})}

// encodedNodeDef — a node: its tag (shifted past the empty tree's), its
// label, and its children, encoded as a pair of a pair.
var encodedNodeDef = encodedNodeDefThm{family.Define(registry.DefEntry{
	Name:  "encodedNodeDef",
	Key:   "prop_6e48c7119189a219",
	Const: "encoded_node",
	Type:  "num → A → (num → num → A → bool) → num → A → bool",
	Equations: []string{
		"∀c:num. ∀i:A. ∀r:(num → num → A → bool). " +
			"    encoded_node(c, i, r) = " +
			"    inject_pair(inject_num(suc(c)), inject_pair(inject_atom(i), inject_family(r)))",
	},
	Deps: []registry.EntryLike{injectPairDef, injectNumDef, injectAtomDef, injectFamilyDef},
})}

// universe — the well-formed trees: is_recspace is the least predicate
// closed under encoded_bottom and encoded_node, and the theorems those two rules come
// with are the faces at the top of datatype_universe.go. The node rule's premise
// ranges over every child — an infinitary premise, a premise under ∀.
var universe = family.DefineInductive(registry.InductiveEntry{
	Name: "Universe",
	Keys: registry.InductiveKeys{
		Rules:        "prop_ef2d23ce70f46fb5",
		Induct:       "prop_fc2a343209f99c24",
		Cases:        "prop_597714c565415d30",
		InductStrong: "prop_388dd41eacc5f6f0",
	},
	Const: "is_recspace",
	Type:  "(num → A → bool) → bool",
	Rules: []string{
		"is_recspace(encoded_bottom)",
		"∀c:num. ∀i:A. ∀r:(num → num → A → bool). (∀n:num. " +
			"is_recspace(r(n))) ⇒ is_recspace(encoded_node(c, i, r))",
	},
	Deps: []registry.EntryLike{encodedBottomDef, encodedNodeDef},
})

// RecspaceDef — the type recspace(A): the subset is_recspace carves out of
// the predicates on pairs, in bijection with it via mk_recspace /
// dest_recspace, stamped against the empty tree — encodedBottomRep, the inhabitant
// a type definition must be shown before it may be made. The two facts
// it comes with:
//
//   - RecspaceDef.Retraction: `mk_recspace(dest_recspace(x)) = x` — taking a
//     tree down to its representative and bringing it back is the
//     identity, so dest_recspace is injective (DestRecspaceInjective) and an
//     argument that dropped to representatives returns with its
//     conclusion (Induction).
//   - RecspaceDef.Membership: `is_recspace(r) ⇔ dest_recspace(mk_recspace(r)) = r`
//     — a predicate on pairs is a representative exactly when the round
//     trip up to recspace(A) and back returns it unchanged. Forwards, a
//     representative survives the round trip (MkRecspaceInjective's whole
//     argument); backwards, surviving is enough to BE one.
var RecspaceDef = family.DefineType(registry.TypeEntry{
	Name:      "Recspace",
	Type:      "recspace",
	Abs:       "mk_recspace",
	Rep:       "dest_recspace",
	Pred:      "is_recspace⟨A:A⟩",
	Existence: encodedBottomRep,
	Witness:   "encoded_bottom⟨A:A⟩",
	Deps:      []registry.EntryLike{UniverseRules},
})

// ---------------------------------------------------------------------------
// The constructors, read into the type
// ---------------------------------------------------------------------------

// recspaceBottomDef — the empty tree, brought up.
var recspaceBottomDef = recspaceBottomDefThm{family.Define(registry.DefEntry{
	Name:      "recspaceBottomDef",
	Key:       "prop_c2993c0996d13622",
	Const:     "recspace_bottom",
	Type:      "recspace(A)",
	Equations: []string{"recspace_bottom = mk_recspace(encoded_bottom⟨A:A⟩)"},
	Deps:      []registry.EntryLike{RecspaceDef.Retraction, encodedBottomDef},
})}

// recspaceNodeDef — a node, brought up from the node over its children's
// representatives.
var recspaceNodeDef = recspaceNodeDefThm{family.Define(registry.DefEntry{
	Name:  "recspaceNodeDef",
	Key:   "prop_4d45e92c7b1743b3",
	Const: "recspace_node",
	Type:  "num → A → (num → recspace(A)) → recspace(A)",
	Equations: []string{
		"∀c:num. ∀i:A. ∀r:(num → recspace(A)). " +
			"    recspace_node(c, i, r) = mk_recspace(encoded_node(c, i, λn:num. dest_recspace(r(n))))",
	},
	Deps: []registry.EntryLike{RecspaceDef.Retraction, encodedNodeDef},
})}

// family_cons, the countable-family constructor, is defined by recursion on
// the index in datatype_universe.go (FamilyCons), where the datatype kit reads it
// by name.

// FamilyNilDef — the empty family: an arbitrary element at every index.
var FamilyNilDef = familyNilDefThm{family.Define(registry.DefEntry{
	Name:      "FamilyNilDef",
	Key:       "prop_eda2c03b7e12e9b5",
	Const:     "family_nil",
	Type:      "num → A",
	Equations: []string{"∀n:num. family_nil(n) = εx:A. ⊤"},
})}
