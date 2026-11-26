package latent_projection

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/mixed_graph"
	"github.com/euc-ai/xugo/library/registry"
)

var LatentProjectionAdmg = latentProjectionAdmgThm{family.Add(registry.ProofEntry{
	Name: "LatentProjectionAdmg",
	Key:  "prop_aa8a258319eacb8a",
	Reading: "O ⊆ V keeps the projection's vertices inside the DAG's. A projected directed " +
		"cycle would be a directed cycle of the DAG through the latent paths it stands for.",
	Deps: []registry.EntryLike{dag.DagWellfounded, closure.TransitiveClosureRules},
	Build: family.Card(Statement{
		Binders:    "∀V:set(A). ∀E:(A → A → bool). ∀O:set(A).",
		Hypotheses: []string{"dag_on(V, E)", "O ⊆ V"},
		Conclusion: "admg_on(O, latent_proj_directed(E, O), latent_proj_bidirected(E, O))",
	},
		"The latent projection of a DAG onto observed vertices is an acyclic directed mixed "+
			"graph: a projected directed edge is a directed path of the DAG, so a projected cycle "+
			"is a cycle of the DAG; the bidirected edges are symmetric and loop-free by their "+
			"definition, and both kinds join observed vertices, O being finite as a subset of V."),
})}

var LatentProjectionSeparation = latentProjectionSeparationThm{family.Add(registry.ProofEntry{
	Name: "LatentProjectionSeparation",
	Key:  "prop_7bcb47065ad54e62",
	Reading: "The groups must be observed and pairwise disjoint; on latent vertices the " +
		"projection says nothing. This is what lets graph conditions stated on the projection " +
		"be read in the full DAG, where the derivation rules take their separations.",
	Deps: []registry.EntryLike{
		d_separation.DSeparatedDef,
		mixed_graph.MSeparatedDef,
		LatentProjectionAncestors,
		dag.AncestorsUpperBound,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(A). ∀E:(A → A → bool). ∀O X Y Z:set(A).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"X ⊆ O",
			"Y ⊆ O",
			"Z ⊆ O",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
		},
		Conclusion: "d_separated(E, X, Y, Z) ⇔ " +
			"m_separated(latent_proj_directed(E, O), latent_proj_bidirected(E, O), X, Y, Z)",
	},
		"Latent projection keeps separation among observed groups (Verma and Pearl; Richardson). The "+
			"ancestors of the three groups in the projection are their observed ancestors in the DAG "+
			"(LatentProjectionAncestors). A moral chain in the DAG avoiding Z passes between observed "+
			"vertices through stretches of latent ones, each a latent directed path, a latent fork or a "+
			"latent collider below observed parents, which the augmented graph of the projection records "+
			"as an edge or a collider connection; conversely each augmented adjacency unfolds into a "+
			"moral chain of the DAG through latent ancestors, which lie outside Z."),
})}

var LatentProjectionAncestors = latentProjectionAncestorsThm{family.Add(registry.ProofEntry{
	Name: "LatentProjectionAncestors",
	Key:  "prop_185192d00fcf2dd5",
	Reading: "X ⊆ O is load-bearing: a latent vertex of X is " +
		"its own DAG ancestor and is no vertex of the projection.",
	Deps: []registry.EntryLike{dag.AncestorsClosed, closure.ReflexiveTransitiveClosureTransitive},
	Build: family.Card(Statement{
		Binders:    "∀V:set(A). ∀E:(A → A → bool). ∀O X:set(A).",
		Hypotheses: []string{"dag_on(V, E)", "O ⊆ V", "X ⊆ O"},
		Conclusion: "dag_ancestors(latent_proj_directed(E, O), X) = dag_ancestors(E, X) ∩ O",
	},
		"Ancestry among observed vertices survives the projection: a projected directed path "+
			"is a DAG path, and a DAG path from an observed vertex to X, cut at its observed "+
			"vertices, is a chain of projected edges, its stretches between them latent."),
})}

var LatentProjectionAncestral = latentProjectionAncestralThm{family.Add(registry.ProofEntry{
	Name: "LatentProjectionAncestral",
	Key:  "prop_1e1ad3db6510ad6b",
	Reading: "The parent-closure of P is load-bearing: the latent paths and forks a " +
		"projected edge stands for run through ancestors of its observed ends, which stay in P.",
	Deps: []registry.EntryLike{LatentReachDef, dag.AncestorsUpperBound},
	Build: family.Card(Statement{
		Binders:    "∀E:(A → A → bool). ∀P O:set(A).",
		Hypotheses: []string{"dag_ancestral(E, P)"},
		Conclusion: "latent_proj_directed(relation_on(P, E), O ∩ P) = " +
			"relation_on(P, latent_proj_directed(E, O)) ∧ " +
			"latent_proj_bidirected(relation_on(P, E), O ∩ P) = relation_on(P, latent_proj_bidirected(E, O))",
	},
		"Projecting the restriction to a parent-closed set is restricting the "+
			"projection: every vertex of a latent path or fork into observed vertices of P "+
			"is an ancestor of them, so in P, and a vertex of P is outside O ∩ P exactly "+
			"when it is outside O. The second line of ID reads it at the ancestors of Y."),
})}

var LatentProjectionRemove = latentProjectionRemoveThm{family.Add(registry.ProofEntry{
	Name: "LatentProjectionRemove",
	Key:  "prop_16f3dd846ab3453e",
	Reading: "D ⊆ O is load-bearing: the paths a projected edge stands for have " +
		"latent interiors, so removing observed vertices removes no such path through them.",
	Deps: []registry.EntryLike{LatentReachDef},
	Build: family.Card(Statement{
		Binders:    "∀E:(A → A → bool). ∀O D:set(A).",
		Hypotheses: []string{"D ⊆ O"},
		Conclusion: "latent_proj_directed(relation_on(𝕌 ∖ D, E), O ∖ D) = " +
			"relation_on(𝕌 ∖ D, latent_proj_directed(E, O)) ∧ " +
			"latent_proj_bidirected(relation_on(𝕌 ∖ D, E), O ∖ D) = " +
			"relation_on(𝕌 ∖ D, latent_proj_bidirected(E, O))",
	},
		"Projecting the graph with observed vertices D removed is removing D from the projection: a "+
			"latent path or fork has no vertex of D inside it, and its observed ends are outside D exactly "+
			"when they are vertices of the smaller projection. The fourth and seventh lines of ID read it."),
})}

var DistrictPredecessorSeparation = districtPredecessorSeparationThm{family.Add(registry.ProofEntry{
	Name: "DistrictPredecessorSeparation",
	Key:  "prop_b61238f31a8401b2",
	Reading: "S must be a district of all of O, and P the observed vertices before v in " +
		"an order compatible with ancestry: closed under observed ancestors, and holding " +
		"v's. Both halves are load-bearing — with v → z and P = {z} the edge survives the " +
		"deletion. With the out-edges of P ∖ S deleted, a point of P ∖ S keeps only edges " +
		"into it, and any latent common cause it shares with S would put it in S's district.",
	Deps: []registry.EntryLike{
		LatentProjectionSeparation,
		mixed_graph.DistrictsPartition,
		d_separation.SeparationCertificate,
		dag.AncestorsUpperBound,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(A). ∀E:(A → A → bool). ∀O S P:set(A). ∀v:A.",
		Hypotheses: []string{
			"dag_on(V, E)",
			"O ⊆ V",
			"S ∈ mixed_graph_districts(latent_proj_bidirected(E, O), O)",
			"v ∈ S",
			"P ⊆ O",
			"v ∉ P",
			"dag_ancestors(E, P) ∩ O ⊆ P",
			"dag_ancestors(E, {v}) ∩ O ⊆ P ∪ {v}",
		},
		Conclusion: "d_separated(dag_delete_out(E, P ∖ S), {v}, P ∖ S, P ∩ S)",
	},
		"The graph half of Tian's factorization of a district: v is separated from its "+
			"predecessors outside its district by those inside, once the former's out-edges are "+
			"deleted, so Rule 2 turns P_{O ∖ S}(v | P ∩ S) into P(v | P). A certificate: take U the "+
			"ancestors of P ∪ {v}, observed ones in P ∪ {v}, and S* the part of U ∖ (P ∩ S) reached "+
			"from v by moral adjacency. A point z of P ∖ S has no child left; its moral neighbours "+
			"are its parents, and reaching it from v through latent vertices would give a bidirected "+
			"chain from v to z in the projection through observed vertices of S, so z ∈ S."),
})}
