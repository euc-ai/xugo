package intervention

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

var DoLegal = doLegalThm{family.Add(registry.ProofEntry{
	Name: "DoLegal",
	Reading: "x(i) ∈ M.states(i) on X ∩ M.nodes is load-bearing: the " +
		"sample is nonempty, so a constant mechanism's image must lie in the " +
		"states. An intervened node becomes a root. X ⊄ M.nodes is harmless.",
	Key:  "prop_dcc6080c4beb703c",
	Deps: []registry.EntryLike{dag.DagSubrelation, measurable_space.MeasurableMapDef},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀X:set(I). ∀x:(I → B).",
		Hypotheses: []string{"scm_on(M)", "∀i:I. i ∈ X ∧ i ∈ M.nodes ⇒ x(i) ∈ M.states(i)"},
		Conclusion: "scm_on(scm_do(M, X, x)) ∧ " +
			"(scm_noise_independent(M) ⇒ scm_noise_independent(scm_do(M, X, x)))",
	},
		"An intervention keeps a model legal: its graph is the graph with the edges into X "+
			"deleted, a DAG (DagSubrelation); a constant mechanism with a value in the states is "+
			"measurable for any σ-algebra, every preimage being empty or everything; the other "+
			"mechanisms, the noise and the background are unchanged, and so is noise independence."),
})}

var DoCompose = doComposeThm{family.Add(registry.ProofEntry{
	Name: "DoCompose",
	Key:  "prop_760e7f602379689e",
	Deps: []registry.EntryLike{functions.OverrideOnOverride},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀X Z:set(I). ∀x z:(I → B).",
		Conclusion: "scm_do(scm_do(M, X, x), Z, z) = scm_do(M, X ∪ Z, override_on(Z, z, x))",
	},
		"Two interventions are one on the union, the later one winning where they overlap: the "+
			"edges into X and then into Z are the edges into X ∪ Z, and the mechanisms compose by "+
			"OverrideOnOverride. The empty intervention, repeated interventions and the exchange "+
			"of disjoint ones are its instances; for disjoint X and Z it is M_{x,z} = (M_x)_z."),
})}

var DoCoordinate = doCoordinateThm{family.Add(registry.ProofEntry{
	Name: "DoCoordinate",
	Reading: "i ∈ M.nodes is load-bearing: off the nodes " +
		"the intervened solution is M.default(i), not x(i).",
	Key:  "prop_4a3a4783dd8d29da",
	Deps: []registry.EntryLike{structural_model.ScmSolution, dag.DagSubrelation},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀X:set(I). ∀x:(I → B). ∀u:A. ∀i:I.",
		Hypotheses: []string{"dag_on(M.nodes, M.edges)", "i ∈ X", "i ∈ M.nodes"},
		Conclusion: "scm_solve(scm_do(M, X, x), u, i) = x(i)",
	},
		"An intervened node takes its assigned value: its equation in the intervened model has "+
			"the constant mechanism, and the intervened graph is a DAG, so ScmSolution applies."),
})}

var DoNonDescendant = doNonDescendantThm{family.Add(registry.ProofEntry{
	Name:    "DoNonDescendant",
	Reading: "The descendants of X include X, so i ∉ X is implied; X need not lie in the nodes.",
	Key:     "prop_6aab9d86139b006",
	Deps:    []registry.EntryLike{structural_model.ScmSolution, dag.DagWellfounded, dag.DagSubrelation},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀X:set(I). ∀x:(I → B). ∀u:A. ∀i:I.",
		Hypotheses: []string{"dag_on(M.nodes, M.edges)", "i ∉ dag_descendants(M.edges, X)"},
		Conclusion: "scm_solve(scm_do(M, X, x), u, i) = scm_solve(M, u, i)",
	},
		"A node that descends from no point of X keeps its value at every sample: by "+
			"well-founded induction, its ancestors are not in X, so the two models have the same "+
			"mechanisms and the same parents along them. Off the nodes both are the fixed value."),
})}

var InterventionConsistency = interventionConsistencyThm{family.Add(registry.ProofEntry{
	Name: "InterventionConsistency",
	Reading: "agree_on is unrestricted, so off the nodes the hypothesis asks " +
		"M.default(i) = x(i); harmless, since both models force M.default there.",
	Key:  "prop_eb10b96a590fb4d",
	Deps: []registry.EntryLike{structural_model.ScmSolution, dag.DagSubrelation},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀X:set(I). ∀x:(I → B). ∀u:A.",
		Hypotheses: []string{"dag_on(M.nodes, M.edges)", "scm_solve(M, u) ∈ agree_on(X, x)"},
		Conclusion: "scm_solve(scm_do(M, X, x), u) = scm_solve(M, u)",
	},
		"Where the solution already takes the intervened values, the intervention changes nothing: "+
			"the solution of M solves the intervened equations — at a node of X its value is the "+
			"constant, elsewhere the equation is M's, the deleted edges into X being read by no equation "+
			"— so it is the intervened solution by uniqueness (ScmSolution). No measurability is used."),
})}

var InterventionConsistencyMeasure = interventionConsistencyMeasureThm{family.Add(registry.ProofEntry{
	Name: "InterventionConsistencyMeasure",
	Key:  "prop_c9d53c7373ce8d4e",
	Reading: "The singleton hypothesis is used twice: it gives x(i) ∈ M.states(i), which " +
		"DoLegal needs, and it makes {V_X = x} an event. E ∈ configSigma is load-bearing, " +
		"since monotonicity needs both sets measurable. X need not lie in the nodes: off " +
		"them the coordinate is the constant default, so the agree event stays measurable.",
	Deps: []registry.EntryLike{
		InterventionConsistency,
		DoLegal,
		structural_model.ScmSolutionMeasurable,
		measurable_space.AgreeOnMeasurable,
		measure_space.MeasureMono,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X:set(I). ∀x:(I → B). ∀E:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"∀i:I. i ∈ X ⇒ {x(i)} ∈ M.state_sigma(i)",
			"E ∈ indexed_product_sigma(M.nodes, M.default, M.states, M.state_sigma)",
		},
		Conclusion: "scm_distribution(M, E ∩ agree_on(X, x)) ≤ scm_distribution(scm_do(M, X, x), E)",
	},
		"By consistency the samples at which M's solution lies in E and takes the values x "+
			"on X are among those at which the intervened solution lies in E; both sets are "+
			"events (ScmSolutionMeasurable for the two legal models, AgreeOnMeasurable for the "+
			"finite X with measurable singletons), and the measure is monotone. Positivity of "+
			"an observational probability passes to the interventional one this way."),
})}

var RegimeFaces = regimeFacesThm{family.Add(registry.ProofEntry{
	Name: "RegimeFaces",
	Reading: "Only M.prob(∅) = 0 is used: E need not be measurable and Z, z are " +
		"unconstrained, because each face set's slices are ∅ and the model's preimage of E.",
	Key:  "prop_6f00809b11da0021",
	Deps: []registry.EntryLike{measure_space.PushforwardMeasureDef},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀Z:set(I). ∀z:(I → B). ∀E:set(I → B).",
		Hypotheses: []string{"measure_on(M.sample, M.events, M.prob)"},
		Conclusion: "bool_mixture_measure(M.prob, " +
			"    {p:prod(A, bool) | " +
			"        p ∈ set_cross(M.sample, 𝕌⟨A:bool⟩) ∧ snd(p) ∧ regime_solve(M, Z, z, p) ∈ E}) = " +
			"extended_of_real(&1 / &2) * scm_distribution(scm_do(M, Z, z), E) ∧ " +
			"bool_mixture_measure(M.prob, " +
			"    {p:prod(A, bool) | " +
			"        p ∈ set_cross(M.sample, 𝕌⟨A:bool⟩) ∧ ¬snd(p) ∧ regime_solve(M, Z, z, p) ∈ E}) = " +
			"extended_of_real(&1 / &2) * scm_distribution(M, E)",
	},
		"On each face of the coin the regime variables are one model's solution: the set has "+
			"one nonempty slice, the inverse image of E under that model's solution, and an empty "+
			"one of measure zero. So V' has the distribution of the intervened model given F = ⊤ "+
			"and that of M given F = ⊥, and the two distributions share one probability space."),
})}

var DoEmpty = doEmptyThm{family.Add(registry.ProofEntry{
	Name: "DoEmpty",
	Key:  "prop_641516dc294fd8f8",
	Deps: []registry.EntryLike{structural_model.ScmEq},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀x:(I → B).",
		Conclusion: "scm_do(M, ∅, x) = M",
	},
		"The empty intervention deletes no edge and replaces no mechanism: compare the records "+
			"field by field (ScmEq); the edge relation and the mechanism family agree pointwise."),
})}

var DoSolveJointMeasurable = doSolveJointMeasurableThm{family.Add(registry.ProofEntry{
	Name: "DoSolveJointMeasurable",
	Key:  "prop_279a6b14152cfe7",
	Reading: "The intervened values range over the configurations of Z, so each is legal and each " +
		"intervened model is a model (DoLegal); Z need not lie in the nodes, an intervention off them " +
		"changing no equation. Joint measurability in (u, z) is what the randomized regime reads.",
	Deps: []registry.EntryLike{
		structural_model.ScmSolutionMeasurable,
		DoLegal,
		measurable_space.IndexedProductMeasurableIff,
		measurable_space.PairedMeasurableIff,
		measurable_space.MeasurableCompose,
		dag.DagWellfounded,
	},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀Z:set(I).",
		Hypotheses: []string{"scm_on(M)"},
		Conclusion: "measurable_map(set_cross(M.sample, indexed_functions(Z, M.default, M.states)), " +
			"    product_sigma(M.sample, " +
			"        M.events, " +
			"        indexed_functions(Z, M.default, M.states), " +
			"        indexed_product_sigma(Z, M.default, M.states, M.state_sigma)), " +
			"    indexed_functions(M.nodes, M.default, M.states), " +
			"    indexed_product_sigma(M.nodes, M.default, M.states, M.state_sigma), " +
			"    λp:prod(A, I → B). scm_solve(scm_do(M, Z, snd(p)), fst(p)))",
	},
		"The solution of the intervened model is jointly measurable in the sample and the "+
			"intervened values. Coordinatewise (IndexedProductMeasurableIff), by well-founded induction "+
			"along the graph: a node of Z takes the value snd(p)(i), a coordinate of the second factor; "+
			"any other node is its mechanism applied to its parents' values, measurable in p by the "+
			"induction hypothesis, and to fst(p), whose pair is measurable for the product with the "+
			"noise (PairedMeasurableIff), the mechanism being jointly measurable (MeasurableCompose)."),
})}
