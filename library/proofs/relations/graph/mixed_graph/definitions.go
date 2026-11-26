// definitions.go — acyclic directed mixed graphs, separation in a mixed
// graph read on an augmented ancestral graph with no paths, districts,
// and the C-forests and hedges of the identification criterion.

package mixed_graph

import (
	"github.com/euc-ai/xugo/library/registry"
)

// AdmgOn — `admg_on(V, D, B)`: an acyclic directed mixed graph on V, its
// directed edges D a DAG and its bidirected edges B symmetric, without
// loops, with both ends in V.
var AdmgOn = admgOnThm{family.Define(registry.DefEntry{
	Name:  "AdmgOn",
	Key:   "prop_dfafa74166692749",
	Const: "admg_on",
	Type:  "set(A) → (A → A → bool) → (A → A → bool) → bool",
	Equations: []string{
		"∀V:set(A). ∀D B:(A → A → bool). " +
			"    admg_on(V, D, B) ⇔ dag_on(V, D) ∧ (∀u v:A. B(u, v) ⇒ u ∈ V ∧ v ∈ V ∧ u ≠ v ∧ B(v, u))",
	},
})}

// AugmentedDef — on a set U of a mixed graph, u and v are adjacent in the
// augmented graph when they are distinct and joined by an edge of either
// kind, or collider-connected inside U: an edge from u with an arrowhead
// at c, a chain of bidirected edges in U from c to c′, and an edge from v
// with an arrowhead at c′.
var AugmentedDef = augmentedDefThm{family.Define(registry.DefEntry{
	Name:  "AugmentedDef",
	Key:   "prop_49dbf4d6fd1cbab1",
	Const: "mixed_graph_augmented",
	Type:  "(A → A → bool) → (A → A → bool) → set(A) → A → A → bool",
	Equations: []string{
		"∀D B:(A → A → bool). ∀U:set(A). ∀u v:A. " +
			"    mixed_graph_augmented(D, B, U, u, v) ⇔ " +
			"    u ≠ v ∧ " +
			"    (D(u, v) ∨ " +
			"        D(v, u) ∨ " +
			"        B(u, v) ∨ " +
			"        (∃c c':A. " +
			"            c ∈ U ∧ " +
			"            c' ∈ U ∧ " +
			"            (D(u, c) ∨ B(u, c)) ∧ " +
			"            reflexive_transitive_closure(relation_on(U, B), c, c') ∧ " +
			"            (D(v, c') ∨ B(v, c'))))",
	},
})}

// MSeparatedDef — Z m-separates X from Y in the mixed graph (D, B) when,
// on the ancestors U of X ∪ Y ∪ Z along D, augmented adjacency
// restricted to U ∖ Z connects no point of X to a point of Y: the
// augmented-graph criterion, the analogue of `d_separated`, with no path
// objects.
var MSeparatedDef = mSeparatedDefThm{family.Define(registry.DefEntry{
	Name:  "MSeparatedDef",
	Key:   "prop_494ca268766fecf0",
	Const: "m_separated",
	Type:  "(A → A → bool) → (A → A → bool) → set(A) → set(A) → set(A) → bool",
	Deps:  []registry.EntryLike{AugmentedDef},
	Equations: []string{
		"∀D B:(A → A → bool). ∀X Y Z:set(A). " +
			"    m_separated(D, B, X, Y, Z) ⇔ " +
			"    ∀x y:A. " +
			"        x ∈ X ∧ y ∈ Y ⇒ " +
			"        ¬transitive_closure(relation_on(dag_ancestors(D, X ∪ Y ∪ Z) ∖ Z, " +
			"                mixed_graph_augmented(D, B, dag_ancestors(D, X ∪ Y ∪ Z))), " +
			"            x, " +
			"            y)",
	},
})}

// DistrictDef — `mixed_graph_district(B, S, v)`: the vertices of S joined to v by
// a chain of bidirected edges inside S; empty when v is not in S.
var DistrictDef = districtDefThm{family.Define(registry.DefEntry{
	Name:  "DistrictDef",
	Key:   "prop_b7a3315aff60d928",
	Const: "mixed_graph_district",
	Type:  "(A → A → bool) → set(A) → A → set(A)",
	Equations: []string{
		"∀B:(A → A → bool). ∀S:set(A). ∀v:A. " +
			"    mixed_graph_district(B, S, v) = " +
			"    {u:A | u ∈ S ∧ reflexive_transitive_closure(relation_on(S, B), v, u)}",
	},
})}

// DistrictsDef — `mixed_graph_districts(B, S)`: the districts of S, one for each
// of its vertices.
var DistrictsDef = districtsDefThm{family.Define(registry.DefEntry{
	Name:  "DistrictsDef",
	Key:   "prop_9dcb85cf79d2bf3",
	Const: "mixed_graph_districts",
	Type:  "(A → A → bool) → set(A) → set(set(A))",
	Deps:  []registry.EntryLike{DistrictDef},
	Equations: []string{
		"∀B:(A → A → bool). ∀S:set(A). " +
			"    mixed_graph_districts(B, S) = {C:set(A) | ∃v:A. v ∈ S ∧ C = mixed_graph_district(B, S, v)}",
	},
})}

// CForestDef — `mixed_graph_c_forest(D, B, F, R)`: F with root set R is a
// C-forest of the mixed graph — R ⊆ F, F is one district of its own
// bidirected edges, and every vertex of F reaches R along directed edges
// inside F. A forest of directed edges with exactly the roots R and all
// the bidirected edges of F is then a subgraph; Shpitser and Pearl's
// C-forests are those subgraphs.
var CForestDef = cForestDefThm{family.Define(registry.DefEntry{
	Name:  "CForestDef",
	Key:   "prop_6fcd200eb6ff6d84",
	Const: "mixed_graph_c_forest",
	Type:  "(A → A → bool) → (A → A → bool) → set(A) → set(A) → bool",
	Equations: []string{
		"∀D B:(A → A → bool). ∀F R:set(A). " +
			"    mixed_graph_c_forest(D, B, F, R) ⇔ " +
			"    R ⊆ F ∧ " +
			"    (∀u v:A. u ∈ F ∧ v ∈ F ⇒ reflexive_transitive_closure(relation_on(F, B), u, v)) ∧ " +
			"    (∀u:A. u ∈ F ⇒ (∃r:A. r ∈ R ∧ reflexive_transitive_closure(relation_on(F, D), u, r)))",
	},
})}

// HedgeDef — `mixed_graph_hedge(D, B, X, Y, F, F′)`: F and F′ are C-forests with
// one root set R, F′ inside F, X meeting F and missing F′, and R among
// the ancestors of Y once the edges into X are deleted. A hedge for
// P(y | do(x)) is what makes the effect not identifiable.
var HedgeDef = hedgeDefThm{family.Define(registry.DefEntry{
	Name:  "HedgeDef",
	Key:   "prop_276755541597d70e",
	Const: "mixed_graph_hedge",
	Type:  "(A → A → bool) → (A → A → bool) → set(A) → set(A) → set(A) → set(A) → bool",
	Deps:  []registry.EntryLike{CForestDef},
	Equations: []string{
		"∀D B:(A → A → bool). ∀X Y F F':set(A). " +
			"    mixed_graph_hedge(D, B, X, Y, F, F') ⇔ " +
			"    (∃R:set(A). " +
			"        mixed_graph_c_forest(D, B, F, R) ∧ " +
			"        mixed_graph_c_forest(D, B, F', R) ∧ " +
			"        F' ⊆ F ∧ " +
			"        F ∩ X ≠ ∅ ∧ " +
			"        F' ∩ X = ∅ ∧ " +
			"        R ⊆ dag_ancestors(dag_delete_in(D, X), Y))",
	},
})}
