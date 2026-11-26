// definitions.go — a path of a DAG, read as a list of vertices, that is
// open given a set: Pearl's reading of separation by colliders.

package d_connection

import (
	"github.com/euc-ai/xugo/library/registry"
)

// OpenPathDef — `d_open_path(E, Z, p)`: p lists distinct vertices, each
// joined to the next by an edge in either direction, and every interior
// vertex b, between a and c, is open given Z — if both edges point into
// b (a collider) then b is an ancestor of Z, otherwise b is not in Z.
// Consecutive pairs and triples are read by splitting the list, as
// `list_ascending` reads its pairs.
var OpenPathDef = openPathDefThm{family.Define(registry.DefEntry{
	Name:  "OpenPathDef",
	Key:   "prop_94f1d01964c4abb3",
	Const: "d_open_path",
	Type:  "(A → A → bool) → set(A) → list(A) → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀Z:set(A). ∀p:list(A). " +
			"    d_open_path(E, Z, p) ⇔ " +
			"    list_distinct(p) ∧ " +
			"    (∀l₁ l₂:list(A). ∀a b:A. p = list_append(l₁, cons(a, cons(b, l₂))) ⇒ E(a, b) ∨ E(b, a)) ∧ " +
			"    (∀l₁ l₂:list(A). ∀a b c:A. " +
			"        p = list_append(l₁, cons(a, cons(b, cons(c, l₂)))) ⇒ " +
			"        (E(a, b) ∧ E(c, b) ⇒ b ∈ dag_ancestors(E, Z)) ∧ (¬(E(a, b) ∧ E(c, b)) ⇒ b ∉ Z))",
	},
})}
