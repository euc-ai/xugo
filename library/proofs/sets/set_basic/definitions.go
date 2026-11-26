// definitions.go — the chapter's definitional layer: the language of
// sets, minted here.
//
// A set is its own membership predicate, and every constructor is a
// comprehension over that — the two names the comprehension lowers to,
// set_comprehension and comprehension_spec, come first, then membership, the two constant
// sets, and the constructors in the order their equations mention one
// another. A name the DSL keeps for its own set surface (`∈`, `∅`,
// `{x | …}`, `∪`, and `insert`, which `{a, b}` lowers to) is spelled by
// a stand-in in its equation, since a definiendum cannot wear it; the
// rest (delete, disjoint, image) are written as themselves.

package set_basic

import (
	"github.com/euc-ai/xugo/library/registry"
)

// SetComprehensionDef · ComprehensionSpecDef — the two names a comprehension lowers to:
// `{x | φ}` is `set_comprehension(λv. ∃x. comprehension_spec(v, φ, x))`, set_comprehension the identity
// on predicates and comprehension_spec the pairing of the condition with the
// point.
var SetComprehensionDef = setComprehensionDefThm{family.Define(registry.DefEntry{
	Name:      "SetComprehensionDef",
	Key:       "prop_fc352ef0a02db2c4",
	Const:     "set_comprehension",
	Spelled:   "comprehension",
	Type:      "(A → bool) → set(A)",
	Equations: []string{"∀p:(A → bool). comprehension(p) = p"},
})}

var ComprehensionSpecDef = comprehensionSpecDefThm{family.Define(registry.DefEntry{
	Name:      "ComprehensionSpecDef",
	Key:       "prop_da98eebb3f9458d9",
	Const:     "comprehension_spec",
	Spelled:   "comprehension_point",
	Type:      "A → bool → A → bool",
	Equations: []string{"∀v:A. ∀p:bool. ∀t:A. comprehension_point(v, p, t) ⇔ p ∧ v = t"},
})}

// SetMemberDef — membership is application: x ∈ s is s at x.
var SetMemberDef = setMemberDefThm{family.Define(registry.DefEntry{
	Name:      "SetMemberDef",
	Key:       "prop_9da47ca4797fcc41",
	Const:     "set_member",
	Spelled:   "member",
	Type:      "A → set(A) → bool",
	Equations: []string{"∀x:A. ∀s:(A → bool). member(x, s) ⇔ s(x)"},
})}

// EmptySetDef · UniverseDef — the two constant sets: nothing, and everything.
var EmptySetDef = emptySetDefThm{family.Define(registry.DefEntry{
	Name:      "EmptySetDef",
	Key:       "prop_d26c4e771dff7bb0",
	Const:     "empty_set",
	Spelled:   "empty",
	Type:      "set(A)",
	Equations: []string{"empty = λx:A. ⊥"},
})}

var UniverseDef = universeDefThm{family.Define(registry.DefEntry{
	Name:      "UniverseDef",
	Key:       "prop_88d61b4075c0ea7b",
	Const:     "universe",
	Spelled:   "univ",
	Type:      "set(A)",
	Equations: []string{"univ = λx:A. ⊤"},
})}

// InsertDef — adding one element: a point is in insert(x, s) when it
// is in s or is x.
var InsertDef = insertDefThm{family.Define(registry.DefEntry{
	Name:      "InsertDef",
	Key:       "prop_fd78405ab1ad5130",
	Const:     "insert",
	Spelled:   "insertion",
	Type:      "A → set(A) → set(A)",
	Equations: []string{"∀x:A. ∀s:set(A). ∀y:A. insertion(x, s, y) ⇔ y ∈ s ∨ y = x"},
	Deps:      []registry.EntryLike{SetMemberDef},
})}

// DeleteDef — removing one element.
var DeleteDef = deleteDefThm{family.Define(registry.DefEntry{
	Name:      "DeleteDef",
	Key:       "prop_fce655c2aa22b555",
	Const:     "delete",
	Type:      "set(A) → A → set(A)",
	Equations: []string{"∀s:set(A). ∀x:A. delete(s, x) = {y:A | y ∈ s ∧ ¬(y = x)}"},
	Deps:      []registry.EntryLike{SetComprehensionDef, ComprehensionSpecDef, SetMemberDef},
})}

// UnionDef · IntersectionDef · SetDifferenceDef — the binary operations, each a
// comprehension over membership in the two arguments.
var UnionDef = unionDefThm{family.Define(registry.DefEntry{
	Name:      "UnionDef",
	Key:       "prop_fec3cbd77bd1db3",
	Const:     "union",
	Spelled:   "set_union",
	Type:      "set(A) → set(A) → set(A)",
	Equations: []string{"∀s t:set(A). set_union(s, t) = {x:A | x ∈ s ∨ x ∈ t}"},
	Deps:      []registry.EntryLike{SetComprehensionDef, ComprehensionSpecDef, SetMemberDef},
})}

var IntersectionDef = intersectionDefThm{family.Define(registry.DefEntry{
	Name:      "IntersectionDef",
	Key:       "prop_2de085ca42eb540f",
	Const:     "intersection",
	Spelled:   "inter",
	Type:      "set(A) → set(A) → set(A)",
	Equations: []string{"∀s t:set(A). inter(s, t) = {x:A | x ∈ s ∧ x ∈ t}"},
	Deps:      []registry.EntryLike{SetComprehensionDef, ComprehensionSpecDef, SetMemberDef},
})}

var SetDifferenceDef = setDifferenceDefThm{family.Define(registry.DefEntry{
	Name:      "SetDifferenceDef",
	Key:       "prop_25994ef016d73c3f",
	Const:     "set_difference",
	Spelled:   "diff",
	Type:      "set(A) → set(A) → set(A)",
	Equations: []string{"∀s t:set(A). diff(s, t) = {x:A | x ∈ s ∧ x ∉ t}"},
	Deps:      []registry.EntryLike{SetComprehensionDef, ComprehensionSpecDef, SetMemberDef},
})}

// SubsetDef · ProperSubsetDef — inclusion, and its strict part.
var SubsetDef = subsetDefThm{family.Define(registry.DefEntry{
	Name:      "SubsetDef",
	Key:       "prop_6f5de5f29afc2187",
	Const:     "subset",
	Spelled:   "is_subset",
	Type:      "set(A) → set(A) → bool",
	Equations: []string{"∀s t:set(A). is_subset(s, t) ⇔ ∀x:A. x ∈ s ⇒ x ∈ t"},
	Deps:      []registry.EntryLike{SetMemberDef},
})}

var ProperSubsetDef = properSubsetDefThm{family.Define(registry.DefEntry{
	Name:      "ProperSubsetDef",
	Key:       "prop_3fb99f7468235b26",
	Const:     "proper_subset",
	Spelled:   "psubset",
	Type:      "set(A) → set(A) → bool",
	Equations: []string{"∀s t:set(A). psubset(s, t) ⇔ s ⊆ t ∧ ¬(s = t)"},
	Deps:      []registry.EntryLike{SubsetDef},
})}

// DisjointDef — meeting in nothing.
var DisjointDef = disjointDefThm{family.Define(registry.DefEntry{
	Name:      "DisjointDef",
	Key:       "prop_fc9bf6393ca5a064",
	Const:     "disjoint",
	Type:      "set(A) → set(A) → bool",
	Equations: []string{"∀s t:set(A). disjoint(s, t) ⇔ s ∩ t = ∅"},
	Deps:      []registry.EntryLike{IntersectionDef, EmptySetDef},
})}

// BigUnionDef · BigIntersectionDef — the big operators, over a set of sets.
var BigUnionDef = bigUnionDefThm{family.Define(registry.DefEntry{
	Name:      "BigUnionDef",
	Key:       "prop_debb5bb070945b17",
	Const:     "big_union",
	Spelled:   "unions",
	Type:      "set(set(A)) → set(A)",
	Equations: []string{"∀u:set(set(A)). unions(u) = {x:A | ∃s:set(A). s ∈ u ∧ x ∈ s}"},
	Deps:      []registry.EntryLike{SetComprehensionDef, ComprehensionSpecDef, SetMemberDef},
})}

var BigIntersectionDef = bigIntersectionDefThm{family.Define(registry.DefEntry{
	Name:      "BigIntersectionDef",
	Key:       "prop_70abd41e907550cb",
	Const:     "big_intersection",
	Spelled:   "inters",
	Type:      "set(set(A)) → set(A)",
	Equations: []string{"∀u:set(set(A)). inters(u) = {x:A | ∀s:set(A). s ∈ u ⇒ x ∈ s}"},
	Deps:      []registry.EntryLike{SetComprehensionDef, ComprehensionSpecDef, SetMemberDef},
})}

// ImageDef — the image of a set under a map.
var ImageDef = imageDefThm{family.Define(registry.DefEntry{
	Name:      "ImageDef",
	Key:       "prop_e07d8cb98755fe6d",
	Const:     "image",
	Type:      "(A → B) → set(A) → set(B)",
	Equations: []string{"∀f:(A → B). ∀s:set(A). image(f, s) = {y:B | ∃x:A. x ∈ s ∧ y = f(x)}"},
	Deps:      []registry.EntryLike{SetComprehensionDef, ComprehensionSpecDef, SetMemberDef},
})}
