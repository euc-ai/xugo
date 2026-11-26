// definitions.go — the chapter's definitional layer: antisymmetry and
// the three order structures, the partial order a preorder with one
// axiom more and the total order a partial order with one more again;
// and what a set can be or have under a relation — a chain, bounds on
// either side, maximal, greatest and least points.
//
// The whole-type preorder and partial order read their laws through
// the corresponding structures on Universe. Sets also enter the notions
// built over a relation:
// `chain(R, c)`, `upper_bound(R, s, b)`, `maximal(R, s, m)`.

package order

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The order relations
// ---------------------------------------------------------------------------

// AntisymmetricDef — two points each related to the other are one
// point.
var AntisymmetricDef = antisymmetricDefThm{family.Define(registry.DefEntry{
	Name:      "AntisymmetricDef",
	Key:       "prop_d095e9c60ea2167f",
	Const:     "antisymmetric",
	Type:      "(A → A → bool) → bool",
	Equations: []string{"∀R:(A → A → bool). antisymmetric(R) ⇔ ∀x y:A. R(x, y) ∧ R(y, x) ⇒ x = y"},
})}

// Preorder — a preorder: reflexive and transitive. The structure's one
// component is the relation, so a law here is stated `preorder(R) ⇒
// body` and its proof receives the hypothesis. The two laws below read
// the carrier axioms at Universe through PreorderOnUniverse.
var Preorder = preorderThm{family.DefineStructure(registry.DefEntry{
	Name:      "Preorder",
	Key:       "prop_6a4089a15864cd46",
	Const:     "preorder",
	Subject:   "R",
	Type:      "(A → A → bool) → bool",
	Equations: []string{"∀R:(A → A → bool). preorder(R) ⇔ reflexive(R) ∧ transitive(R)"},
})}

// Reflexive — every point is below itself: ReflexiveOn on the whole
// type.
var Reflexive = reflexiveThm{family.Add(registry.ProofEntry{
	Name:  "Reflexive",
	Key:   "prop_b0f91b189ae2621f",
	Build: PreorderAtUniverse.Law("∀x:A. R(x, x)", ReflexiveOn),
})}

// Transitive — below a point that is below a third is below the third:
// TransitiveOn on the whole type.
var Transitive = transitiveThm{family.Add(registry.ProofEntry{
	Name: "Transitive",
	Key:  "prop_f16a5d1595957c57",
	Build: PreorderAtUniverse.Law(Statement{
		Binders: "∀x y z:A.",
		Hypotheses: []string{
			"R(x, y)",
			"R(y, z)",
		},
		Conclusion: "R(x, z)",
	}, TransitiveOn),
})}

// PartialOrder — a partial order: an antisymmetric preorder, the
// preorder being the definition's first conjunct.
var PartialOrder = partialOrderThm{family.DefineStructure(registry.DefEntry{
	Name:      "PartialOrder",
	Key:       "prop_fb47c3cc1acc3078",
	Const:     "partial_order",
	Subject:   "R",
	Type:      "(A → A → bool) → bool",
	Equations: []string{"∀R:(A → A → bool). partial_order(R) ⇔ preorder(R) ∧ antisymmetric(R)"},
	Deps:      []registry.EntryLike{Preorder, AntisymmetricDef},
})}

// PartialOrderPreorder — a partial order is a preorder: the
// sub-structure at which the laws of a preorder apply.
var PartialOrderPreorder = partialOrderPreorderThm{family.Add(registry.ProofEntry{
	Name:  "PartialOrderPreorder",
	Key:   "prop_747961933b8b7ed6",
	Build: PartialOrder.Axiom("preorder(R)"),
})}

// Antisymmetric — two points each below the other are equal:
// AntisymmetricOn on the whole type.
var Antisymmetric = antisymmetricThm{family.Add(registry.ProofEntry{
	Name: "Antisymmetric",
	Key:  "prop_c0b113d0c80d3c41",
	Build: PartialOrderAtUniverse.Law(Statement{
		Binders: "∀x y:A.",
		Hypotheses: []string{
			"R(x, y)",
			"R(y, x)",
		},
		Conclusion: "x = y",
	}, AntisymmetricOn),
})}

// TotalOrder — a total order: a partial order under which any two
// points are comparable, the partial order being the definition's
// first conjunct.
var TotalOrder = totalOrderThm{family.DefineStructure(registry.DefEntry{
	Name:    "TotalOrder",
	Key:     "prop_791aa48bce6b0bbd",
	Const:   "total_order",
	Subject: "R",
	Type:    "(A → A → bool) → bool",
	Equations: []string{
		"∀R:(A → A → bool). total_order(R) ⇔ partial_order(R) ∧ (∀x y:A. R(x, y) ∨ R(y, x))",
	},
	Deps: []registry.EntryLike{PartialOrder},
})}

// TotalOrderPartialOrder — a total order is a partial order: the
// sub-structure at which the laws of a partial order apply.
var TotalOrderPartialOrder = totalOrderPartialOrderThm{family.Add(registry.ProofEntry{
	Name:  "TotalOrderPartialOrder",
	Key:   "prop_b6bde9483b27217b",
	Build: TotalOrder.Axiom("partial_order(R)"),
})}

// Total — any two points are comparable: the axiom a total order adds.
var Total = totalThm{family.Add(registry.ProofEntry{
	Name:  "Total",
	Key:   "prop_985c6c6ef9a537a7",
	Build: TotalOrder.Axiom("∀x y:A. R(x, y) ∨ R(y, x)"),
})}

// ---------------------------------------------------------------------------
// Chains, bounds and extremal points
// ---------------------------------------------------------------------------

// ChainDef — `chain(R, c)`: any two points of c are comparable. A
// point is compared with itself too, so every point of a chain is
// below itself; under a preorder that asks nothing.
var ChainDef = chainDefThm{family.Define(registry.DefEntry{
	Name:  "ChainDef",
	Key:   "prop_4b3721a433278c9a",
	Const: "chain",
	Type:  "(A → A → bool) → set(A) → bool",
	Equations: []string{
		"∀R:(A → A → bool). ∀c:set(A). chain(R, c) ⇔ ∀x y:A. x ∈ c ∧ y ∈ c ⇒ R(x, y) ∨ R(y, x)",
	},
})}

// UpperBoundDef — `upper_bound(R, s, b)`: every point of s is below b.
// The bound need not lie in s.
var UpperBoundDef = upperBoundDefThm{family.Define(registry.DefEntry{
	Name:  "UpperBoundDef",
	Key:   "prop_58aff2e1d212a69c",
	Const: "upper_bound",
	Type:  "(A → A → bool) → set(A) → A → bool",
	Equations: []string{
		"∀R:(A → A → bool). ∀s:set(A). ∀b:A. upper_bound(R, s, b) ⇔ ∀x:A. x ∈ s ⇒ R(x, b)",
	},
})}

// MaximalDef — `maximal(R, s, m)`: m is a point of s, and whatever
// point of s it is below is below it in turn. That is the reading
// which is right for a preorder; under a partial order the two points
// are then equal (`MaximalIff`).
var MaximalDef = maximalDefThm{family.Define(registry.DefEntry{
	Name:  "MaximalDef",
	Key:   "prop_b1a73122aaa761c9",
	Const: "maximal",
	Type:  "(A → A → bool) → set(A) → A → bool",
	Equations: []string{
		"∀R:(A → A → bool). ∀s:set(A). ∀m:A. maximal(R, s, m) ⇔ m ∈ s ∧ (∀x:A. x ∈ s ∧ R(m, x) ⇒ R(x, m))",
	},
})}

// LowerBoundDef — `lower_bound(R, s, b)`: b is below every point of s.
// The bound need not lie in s.
var LowerBoundDef = lowerBoundDefThm{family.Define(registry.DefEntry{
	Name:  "LowerBoundDef",
	Key:   "prop_ea84c26768d4f2d5",
	Const: "lower_bound",
	Type:  "(A → A → bool) → set(A) → A → bool",
	Equations: []string{
		"∀R:(A → A → bool). ∀s:set(A). ∀b:A. lower_bound(R, s, b) ⇔ ∀x:A. x ∈ s ⇒ R(b, x)",
	},
})}

// GreatestDef — `greatest(R, s, m)`: m is a point of s that every
// point of s is below — an upper bound of s lying in s.
var GreatestDef = greatestDefThm{family.Define(registry.DefEntry{
	Name:  "GreatestDef",
	Key:   "prop_5b575143571e22e6",
	Const: "greatest",
	Type:  "(A → A → bool) → set(A) → A → bool",
	Equations: []string{
		"∀R:(A → A → bool). ∀s:set(A). ∀m:A. greatest(R, s, m) ⇔ m ∈ s ∧ upper_bound(R, s, m)",
	},
	Deps: []registry.EntryLike{UpperBoundDef},
})}

// LeastDef — `least(R, s, m)`: m is a point of s that is below every
// point of s — a lower bound of s lying in s.
var LeastDef = leastDefThm{family.Define(registry.DefEntry{
	Name:  "LeastDef",
	Key:   "prop_329a818ba021e737",
	Const: "least",
	Type:  "(A → A → bool) → set(A) → A → bool",
	Equations: []string{
		"∀R:(A → A → bool). ∀s:set(A). ∀m:A. least(R, s, m) ⇔ m ∈ s ∧ lower_bound(R, s, m)",
	},
	Deps: []registry.EntryLike{LowerBoundDef},
})}
