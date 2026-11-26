package simple_graph

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

// SimpleGraphOn says adjacency on V is symmetric on V and loopless.
var SimpleGraphOn = simpleGraphOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "SimpleGraphOn",
	Key:     "prop_1a89225a2d287d75",
	Const:   "simple_graph_on",
	Subject: "V",
	Type:    "set(A) → (A → A → bool) → bool",
	Equations: []string{
		"∀V:set(A). ∀R:(A → A → bool). " +
			"    simple_graph_on(V, R) ⇔ symmetric_on(V, R) ∧ (∀v:A. v ∈ V ⇒ ¬R(v, v))",
	},
})}

// Symmetric says adjacency reads the same backwards between vertices.
var Symmetric = symmetricThm{family.Add(registry.ProofEntry{
	Name:  "Symmetric",
	Key:   "prop_be17e60ced921b14",
	Build: SimpleGraphOn.Axiom("symmetric_on(V, R)"),
})}

// Loopless excludes adjacency of a vertex to itself.
var Loopless = looplessThm{family.Add(registry.ProofEntry{
	Name: "Loopless",
	Key:  "prop_6f6e871b973d88d3",
	Build: SimpleGraphOn.Axiom(Statement{
		Binders:    "∀v:A.",
		Hypotheses: []string{"v ∈ V"},
		Conclusion: "¬R(v, v)",
	}),
})}

// NeighboursDef restricts the neighbours of v to vertices of V.
var NeighboursDef = neighboursDefThm{family.Define(registry.DefEntry{
	Name:  "NeighboursDef",
	Key:   "prop_5ae9d53beba21692",
	Const: "graph_neighbours",
	Type:  "set(A) → (A → A → bool) → A → set(A)",
	Equations: []string{
		"∀V:set(A). ∀R:(A → A → bool). ∀v:A. graph_neighbours(V, R, v) = {w:A | w ∈ V ∧ R(v, w)}",
	},
})}

// DegreeDef counts the neighbours of a vertex.
var DegreeDef = degreeDefThm{family.Define(registry.DefEntry{
	Name:  "DegreeDef",
	Key:   "prop_be656e2f94eca96b",
	Const: "graph_degree",
	Type:  "set(A) → (A → A → bool) → A → num",
	Equations: []string{
		"∀V:set(A). ∀R:(A → A → bool). ∀v:A. graph_degree(V, R, v) = card(graph_neighbours(V, R, v))",
	},
	Deps: []registry.EntryLike{NeighboursDef},
})}

// EdgesDef represents an undirected edge by the set of its endpoints.
var EdgesDef = edgesDefThm{family.Define(registry.DefEntry{
	Name:  "EdgesDef",
	Key:   "prop_967cb3ac1405cbb3",
	Const: "graph_edges",
	Type:  "set(A) → (A → A → bool) → set(set(A))",
	Equations: []string{
		"∀V:set(A). ∀R:(A → A → bool). " +
			"    graph_edges(V, R) = {e:set(A) | ∃u v:A. u ∈ V ∧ v ∈ V ∧ R(u, v) ∧ e = {u, v}}",
	},
})}

// DeleteEdgeDef removes the edge e from adjacency: two vertices stay
// adjacent unless e is the pair of them.
var DeleteEdgeDef = deleteEdgeDefThm{family.Define(registry.DefEntry{
	Name:  "DeleteEdgeDef",
	Key:   "prop_6a25355e5e99180a",
	Const: "graph_delete_edge",
	Type:  "(A → A → bool) → set(A) → A → A → bool",
	Equations: []string{
		"∀R:(A → A → bool). ∀e:set(A). ∀x y:A. graph_delete_edge(R, e, x, y) ⇔ R(x, y) ∧ {x, y} ≠ e",
	},
})}

// ReachableDef says u reaches v by a walk in V: the reflexive–transitive
// closure of adjacency restricted to V, so the empty walk counts. Every
// point reaches itself by it, in V or not, which is why ComponentDef
// restricts reachability to V through relation_on and InComponent
// states u ∈ V ∧ z ∈ V.
var ReachableDef = reachableDefThm{family.Define(registry.DefEntry{
	Name:  "ReachableDef",
	Key:   "prop_dd5211b401e80be8",
	Const: "graph_reachable",
	Type:  "set(A) → (A → A → bool) → A → A → bool",
	Equations: []string{
		"∀V:set(A). ∀R:(A → A → bool). ∀u v:A. " +
			"    graph_reachable(V, R, u, v) ⇔ reflexive_transitive_closure(relation_on(V, R), u, v)",
	},
})}

// ConnectedDef says that every pair of vertices is reachable.
var ConnectedDef = connectedDefThm{family.Define(registry.DefEntry{
	Name:  "ConnectedDef",
	Key:   "prop_3e2fe2b8750c13d6",
	Const: "graph_connected",
	Type:  "set(A) → (A → A → bool) → bool",
	Equations: []string{
		"∀V:set(A). ∀R:(A → A → bool). " +
			"    graph_connected(V, R) ⇔ ∀u v:A. u ∈ V ∧ v ∈ V ⇒ graph_reachable(V, R, u, v)",
	},
	Deps: []registry.EntryLike{ReachableDef},
})}

// ComponentDef takes the component of u to be its class under
// reachability on V: the vertices u reaches.
var ComponentDef = componentDefThm{family.Define(registry.DefEntry{
	Name:  "ComponentDef",
	Key:   "prop_7315b92e4876683d",
	Const: "graph_component",
	Type:  "set(A) → (A → A → bool) → A → set(A)",
	Equations: []string{
		"∀V:set(A). ∀R:(A → A → bool). ∀u:A. " +
			"    graph_component(V, R, u) = equivalence_class(relation_on(V, graph_reachable(V, R)), u)",
	},
	Deps: []registry.EntryLike{ReachableDef},
})}

// ComponentsDef collects the components of the graph: the quotient of V
// by reachability.
var ComponentsDef = componentsDefThm{family.Define(registry.DefEntry{
	Name:  "ComponentsDef",
	Key:   "prop_e1f188154843952a",
	Const: "graph_components",
	Type:  "set(A) → (A → A → bool) → set(set(A))",
	Equations: []string{
		"∀V:set(A). ∀R:(A → A → bool). graph_components(V, R) = quotient_on(V, graph_reachable(V, R))",
	},
	Deps: []registry.EntryLike{ReachableDef},
})}
