// definitions.go — separation in a directed acyclic graph, read on the
// moral graph of an ancestral set and with no path objects; the
// semigraphoid axioms a ternary relation on vertex sets may satisfy; and
// the back-door and front-door conditions, which are separation and
// ancestry statements in graphs with edges deleted.

package d_separation

import (
	"github.com/euc-ai/xugo/library/registry"
)

// MoralDef — on a set U, u and v are morally adjacent when they are
// distinct and joined by an edge in either direction or share a child
// in U.
var MoralDef = moralDefThm{family.Define(registry.DefEntry{
	Name:  "MoralDef",
	Key:   "prop_8f49dc49ad4490b3",
	Const: "dag_moral",
	Type:  "(A → A → bool) → set(A) → A → A → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀U:set(A). ∀u v:A. " +
			"    dag_moral(E, U, u, v) ⇔ u ≠ v ∧ (E(u, v) ∨ E(v, u) ∨ (∃w:A. w ∈ U ∧ E(u, w) ∧ E(v, w)))",
	},
})}

// DSeparatedDef — Z separates X from Y when moral adjacency on the
// ancestors U of X ∪ Y ∪ Z, restricted to U ∖ Z, has no positive-length
// walk from X to Y. The restriction excludes points of Z from every walk.
var DSeparatedDef = dSeparatedDefThm{family.Define(registry.DefEntry{
	Name:  "DSeparatedDef",
	Key:   "prop_1b461e1b63136ee",
	Const: "d_separated",
	Type:  "(A → A → bool) → set(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀X Y Z:set(A). " +
			"    d_separated(E, X, Y, Z) ⇔ " +
			"    ∀x y:A. " +
			"        x ∈ X ∧ y ∈ Y ⇒ " +
			"        ¬transitive_closure(relation_on(dag_ancestors(E, X ∪ Y ∪ Z) ∖ Z, " +
			"                dag_moral(E, dag_ancestors(E, X ∪ Y ∪ Z))), " +
			"            x, " +
			"            y)",
	},
	Deps: []registry.EntryLike{MoralDef},
})}

// SemigraphoidOn — a ternary relation R(X, Y, Z) on subsets of V, read
// "X and Y are independent given Z", is a semigraphoid when, for
// pairwise disjoint subsets of V, it is trivial (X is independent of ∅),
// symmetric, and closed under decomposition, weak union and contraction.
// Triviality is not redundant: without it the everywhere-false relation
// satisfies the other four and every local Markov condition on the empty
// vertex set.
var SemigraphoidOn = semigraphoidOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "SemigraphoidOn",
	Key:     "prop_7f81f644f3a86744",
	Const:   "semigraphoid_on",
	Subject: "V",
	Type:    "set(A) → (set(A) → set(A) → set(A) → bool) → bool",
	Equations: []string{
		"∀V:set(A). ∀R:(set(A) → set(A) → set(A) → bool). " +
			"    semigraphoid_on(V, R) ⇔ " +
			"    (∀X Z:set(A). X ⊆ V ∧ Z ⊆ V ∧ X ∩ Z = ∅ ⇒ R(X, ∅, Z)) ∧ " +
			"    (∀X Y Z:set(A). " +
			"        X ⊆ V ∧ Y ⊆ V ∧ Z ⊆ V ∧ X ∩ Y = ∅ ∧ X ∩ Z = ∅ ∧ Y ∩ Z = ∅ ∧ R(X, Y, Z) ⇒ R(Y, X, Z)) ∧ " +
			"    (∀X Y W Z:set(A). " +
			"        X ⊆ V ∧ " +
			"        Y ⊆ V ∧ " +
			"        W ⊆ V ∧ " +
			"        Z ⊆ V ∧ " +
			"        X ∩ Y = ∅ ∧ " +
			"        X ∩ W = ∅ ∧ " +
			"        X ∩ Z = ∅ ∧ " +
			"        Y ∩ W = ∅ ∧ " +
			"        Y ∩ Z = ∅ ∧ " +
			"        W ∩ Z = ∅ ∧ " +
			"        R(X, Y ∪ W, Z) ⇒ " +
			"        R(X, Y, Z)) ∧ " +
			"    (∀X Y W Z:set(A). " +
			"        X ⊆ V ∧ " +
			"        Y ⊆ V ∧ " +
			"        W ⊆ V ∧ " +
			"        Z ⊆ V ∧ " +
			"        X ∩ Y = ∅ ∧ " +
			"        X ∩ W = ∅ ∧ " +
			"        X ∩ Z = ∅ ∧ " +
			"        Y ∩ W = ∅ ∧ " +
			"        Y ∩ Z = ∅ ∧ " +
			"        W ∩ Z = ∅ ∧ " +
			"        R(X, Y ∪ W, Z) ⇒ " +
			"        R(X, Y, Z ∪ W)) ∧ " +
			"    (∀X Y W Z:set(A). " +
			"        X ⊆ V ∧ " +
			"        Y ⊆ V ∧ " +
			"        W ⊆ V ∧ " +
			"        Z ⊆ V ∧ " +
			"        X ∩ Y = ∅ ∧ " +
			"        X ∩ W = ∅ ∧ " +
			"        X ∩ Z = ∅ ∧ " +
			"        Y ∩ W = ∅ ∧ " +
			"        Y ∩ Z = ∅ ∧ " +
			"        W ∩ Z = ∅ ∧ " +
			"        R(X, Y, Z ∪ W) ∧ " +
			"        R(X, W, Z) ⇒ " +
			"        R(X, Y ∪ W, Z))",
	},
})}

// BackdoorCriterionDef — Z satisfies the back-door criterion for (X, Y)
// when it contains no descendant of X — no point of X is an ancestor of
// Z — and separates Y from X once the edges out of X are deleted.
var BackdoorCriterionDef = backdoorCriterionDefThm{family.Define(registry.DefEntry{
	Name:  "BackdoorCriterionDef",
	Key:   "prop_9bf5fea5e9ff7bf4",
	Const: "backdoor_criterion",
	Type:  "(A → A → bool) → set(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀X Y Z:set(A). " +
			"    backdoor_criterion(E, X, Y, Z) ⇔ " +
			"    dag_ancestors(E, Z) ∩ X = ∅ ∧ d_separated(dag_delete_out(E, X), Y, X, Z)",
	},
	Deps: []registry.EntryLike{DSeparatedDef},
})}

// FrontdoorCriterionDef — Z satisfies the front-door criterion for (X, Y)
// when it intercepts every directed path from X to Y (with the edges into
// Z deleted, no point of X is an ancestor of Y), X has no open back door
// to Z (∅ separates Z from X once the edges out of X are deleted), and X
// blocks every back door from Z to Y (X separates Y from Z once the
// edges out of Z are deleted).
var FrontdoorCriterionDef = frontdoorCriterionDefThm{family.Define(registry.DefEntry{
	Name:  "FrontdoorCriterionDef",
	Key:   "prop_c06ad91dd71fae25",
	Const: "frontdoor_criterion",
	Type:  "(A → A → bool) → set(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀X Y Z:set(A). " +
			"    frontdoor_criterion(E, X, Y, Z) ⇔ " +
			"    dag_ancestors(dag_delete_in(E, Z), Y) ∩ X = ∅ ∧ " +
			"    d_separated(dag_delete_out(E, X), Z, X, ∅) ∧ " +
			"    d_separated(dag_delete_out(E, Z), Y, Z, X)",
	},
	Deps: []registry.EntryLike{DSeparatedDef},
})}
