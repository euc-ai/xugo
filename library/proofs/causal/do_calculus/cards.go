package do_calculus

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/causal/graphical_markov"
	"github.com/euc-ai/xugo/library/proofs/causal/intervention"
	"github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	"github.com/euc-ai/xugo/library/proofs/probability/conditional_independence"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

var RegimeExchangeIndependence = regimeExchangeIndependenceThm{family.Add(registry.ProofEntry{
	Name: "RegimeExchangeIndependence",
	Reading: "z(i) ∈ M.states(i) on Z is load-bearing: otherwise a child of a node of " +
		"Z gets a parent configuration off its carrier on the face F = ⊤, its variable can " +
		"fail to be measurable, and the sub-σ-algebra condition inside the independence " +
		"fails. No singleton measurability is needed. Z = ∅ makes the coin idle (DoEmpty).",
	Key: "prop_7f35c5e84e830773",
	Deps: []registry.EntryLike{
		graphical_markov.RegimeStructuralFamily,
		graphical_markov.StructuralFamilyGlobalMarkov,
		d_separation.RegimeSeparationExchange,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀Y Z W:set(I). ∀z:(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ Z ⇒ z(i) ∈ M.states(i)",
			"d_separated(dag_delete_out(M.edges, Z), Y, Z, W)",
		},
		Conclusion: "cond_independent_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), " +
			"    bool_mixture_sigma(M.sample, M.events), " +
			"    bool_mixture_measure(M.prob), " +
			"    coordinate_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), regime_solve(M, Z, z), M.state_sigma, Y), " +
			"    «flag», " +
			"    coordinate_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), " +
			"        regime_solve(M, Z, z), " +
			"        M.state_sigma, " +
			"        Z ∪ W))",
	},
		"Rule 2 without an intervention group, in its independence form: on the regime family of "+
			"do(Z = z), Y is independent of the coin given Z and W. RegimeSeparationExchange turns the "+
			"separation with Z's out-edges deleted into separation of Y from the regime root by Z ∪ W; "+
			"StructuralFamilyGlobalMarkov on RegimeStructuralFamily reads it. On continuous values this "+
			"form carries no kernel statement: if V_Z = z is null and the singletons are measurable, "+
			"the two faces are mutually singular on V'_Z and the independence holds for any mechanism."),
})}

var RegimeDeleteIndependence = regimeDeleteIndependenceThm{family.Add(registry.ProofEntry{
	Name: "RegimeDeleteIndependence",
	Reading: "z(i) ∈ M.states(i) on Z is load-bearing: otherwise a child of a node of " +
		"Z gets a parent configuration off its carrier on the face F = ⊤, its variable can " +
		"fail to be measurable, and the sub-σ-algebra condition inside the independence " +
		"fails. No singleton measurability is needed. Z = ∅ makes the coin idle (DoEmpty).",
	Key: "prop_4bd53ab487ebaa91",
	Deps: []registry.EntryLike{
		graphical_markov.RegimeStructuralFamily,
		graphical_markov.StructuralFamilyGlobalMarkov,
		d_separation.RegimeSeparationDelete,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀Y Z W:set(I). ∀z:(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ Z ⇒ z(i) ∈ M.states(i)",
			"d_separated(dag_delete_in(M.edges, Z ∖ dag_ancestors(M.edges, W)), Y, Z, W)",
		},
		Conclusion: "cond_independent_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), " +
			"    bool_mixture_sigma(M.sample, M.events), " +
			"    bool_mixture_measure(M.prob), " +
			"    coordinate_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), regime_solve(M, Z, z), M.state_sigma, Y), " +
			"    «flag», " +
			"    coordinate_sigma(set_cross(M.sample, 𝕌⟨A:bool⟩), regime_solve(M, Z, z), M.state_sigma, W))",
	},
		"Rule 3 without an intervention group: on the regime family of do(Z = z), Y is "+
			"independent of the coin given W when W separates Y from Z with the edges into Z "+
			"∖ An(W) deleted. RegimeSeparationDelete gives separation of Y from the regime "+
			"root by W; StructuralFamilyGlobalMarkov on RegimeStructuralFamily reads it."),
})}

var DoObserve = doObserveThm{family.Add(registry.ProofEntry{
	Name: "DoObserve",
	Reading: "v(i) ∈ M.states(i) on X is load-bearing for the legality of M_x; the singletons " +
		"on W make the fibres events. E and F are any events of configurations determined by the " +
		"Y- and the Z-coordinates; neither side is conditioned on. X has no singleton hypothesis: " +
		"the condition X ∪ W is reduced to W before the point reading, V_X being the constant v.",
	Key: "prop_526054046733a20d",
	Deps: []registry.EntryLike{
		graphical_markov.SCMGlobalMarkov,
		intervention.DoLegal,
		intervention.DoCoordinate,
		structural_model.ScmSolutionStates,
		conditional_independence.CondIndepPointFiber,
		measurable_space.CoordinateSigmaPullback,
		measurable_space.CoordinateSigmaRestriction,
		measurable_space.AgreeOnMeasurable,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z W:set(I). ∀v:(I → B). ∀E F:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ W ⇒ {v(i)} ∈ M.state_sigma(i)",
			"E ∈ " +
				"coordinate_sigma(indexed_functions(M.nodes, M.default, M.states), " +
				"    λf:(I → B). f, " +
				"    M.state_sigma, " +
				"    Y)",
			"F ∈ " +
				"coordinate_sigma(indexed_functions(M.nodes, M.default, M.states), " +
				"    λf:(I → B). f, " +
				"    M.state_sigma, " +
				"    Z)",
			"d_separated(dag_delete_in(M.edges, X), Y, Z, X ∪ W)",
		},
		Conclusion: "«Px»(E ∩ F ∩ agree_on(W, v)) * «Px»(agree_on(W, v)) = " +
			"«Px»(E ∩ agree_on(W, v)) * «Px»(F ∩ agree_on(W, v))",
	},
		"Rule 1, inserting or deleting an observation: P_x(E, F, w) P_x(w) = P_x(E, w) P_x(F, w) for "+
			"an event E of the Y-coordinates and an event F of the Z-coordinates. SCMGlobalMarkov on the "+
			"legal intervened model (DoLegal) and its graph; the X-coordinates are the constants v "+
			"(DoCoordinate), so σ(V_{X ∪ W}) is σ(V_W) on the samples. The solution maps the samples "+
			"into the configurations (ScmSolutionStates), so E and F pull back to events of σ(V_Y) and "+
			"σ(V_Z) (CoordinateSigmaPullback), and CondIndepPointFiber reads the independence at the "+
			"point v_W, an event of σ(V_W) since the singletons are measurable. A null factor makes both "+
			"sides zero, so no support condition is stated; no state space need be finite or countable."),
})}

var DoExchange = doExchangeThm{family.Add(registry.ProofEntry{
	Name: "DoExchange",
	Reading: "Legal values on Z come from the singleton hypothesis, whose sets lie in the " +
		"states. E is any event of the Y-coordinates; Y is never conditioned on. The condition " +
		"Z ∪ X ∪ W is reduced to Z ∪ W before the point reading. The four regime masses cancel " +
		"to the identity; all are at most 1, so the cancellation is legal in extended arithmetic.",
	Key: "prop_96e3c273cd594b1e",
	Deps: []registry.EntryLike{
		RegimeExchangeIndependence,
		intervention.RegimeFaces,
		intervention.DoCompose,
		intervention.DoLegal,
		intervention.DoCoordinate,
		structural_model.ScmSolutionStates,
		conditional_independence.CondIndepPointFiber,
		measurable_space.CoordinateSigmaPullback,
		measurable_space.CoordinateSigmaRestriction,
		measurable_space.AgreeOnMeasurable,
		dag.AncestorsRootUnion,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z W:set(I). ∀v:(I → B). ∀E:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ Z ∪ W ⇒ {v(i)} ∈ M.state_sigma(i)",
			"E ∈ " +
				"coordinate_sigma(indexed_functions(M.nodes, M.default, M.states), " +
				"    λf:(I → B). f, " +
				"    M.state_sigma, " +
				"    Y)",
			"d_separated(dag_delete_out(dag_delete_in(M.edges, X), Z), Y, Z, X ∪ W)",
		},
		Conclusion: "«Pxz»(E ∩ agree_on(W, v)) * «Px»(agree_on(Z ∪ W, v)) = " +
			"«Px»(E ∩ agree_on(Z ∪ W, v)) * «Pxz»(agree_on(W, v))",
	},
		"Rule 2, exchanging an intervention and an observation: P_{x,z}(E, w) P_x(z, w) = P_x(E, z, w) "+
			"P_{x,z}(w) for an event E of the Y-coordinates. Read RegimeExchangeIndependence on the "+
			"intervened model M_x, whose graph has the edges into X deleted, with the condition X ∪ W "+
			"reduced to W because V_X is constant there; DoCompose identifies (M_x)_z with M_{x∪z} at v. E "+
			"pulls back to an event of σ(V'_Y) (CoordinateSigmaPullback, the regime variables lying in the "+
			"configurations), and CondIndepPointFiber at the point (v_Z, v_W) with the coin's event {F = ⊤} "+
			"gives the cross-multiplied identity on the regime family; RegimeFaces turns its four masses "+
			"into the two distributions, using that V'_Z = v_Z on the face F = ⊤. Checking separation in the "+
			"graph with X's in-edges deleted alone is not enough: deleting Z's out-edges is part of the rule."),
})}

var DoDelete = doDeleteThm{family.Add(registry.ProofEntry{
	Name: "DoDelete",
	Reading: "Z is never conditioned on, so it needs legal values and no singleton " +
		"hypothesis; only the points of W are read. E is any event of the Y-coordinates.",
	Key: "prop_3eb3bc5bc35f9487",
	Deps: []registry.EntryLike{
		RegimeDeleteIndependence,
		intervention.RegimeFaces,
		intervention.DoCompose,
		intervention.DoLegal,
		intervention.DoCoordinate,
		structural_model.ScmSolutionStates,
		conditional_independence.CondIndepPointFiber,
		measurable_space.CoordinateSigmaPullback,
		measurable_space.CoordinateSigmaRestriction,
		measurable_space.AgreeOnMeasurable,
		dag.AncestorsRootUnion,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z W:set(I). ∀v:(I → B). ∀E:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ∪ Z ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ W ⇒ {v(i)} ∈ M.state_sigma(i)",
			"E ∈ " +
				"coordinate_sigma(indexed_functions(M.nodes, M.default, M.states), " +
				"    λf:(I → B). f, " +
				"    M.state_sigma, " +
				"    Y)",
			"d_separated( " +
				"    dag_delete_in(dag_delete_in(M.edges, X), Z ∖ dag_ancestors(dag_delete_in(M.edges, X), W)), " +
				"    Y, " +
				"    Z, " +
				"    X ∪ W)",
		},
		Conclusion: "«Pxz»(E ∩ agree_on(W, v)) * «Px»(agree_on(W, v)) = " +
			"«Px»(E ∩ agree_on(W, v)) * «Pxz»(agree_on(W, v))",
	},
		"Rule 3, inserting or deleting an intervention: P_{x,z}(E, w) P_x(w) = P_x(E, w) P_{x,z}(w) "+
			"for an event E of the Y-coordinates. The ancestors are taken in the graph with X's in-edges "+
			"deleted, where X has no parents, so Z ∖ An(X ∪ W) is Z ∖ An(W) (AncestorsRootUnion); the "+
			"intervention still acts on all of Z, only Z ∖ An(W) loses its in-edges in the graph. Read "+
			"RegimeDeleteIndependence on M_x with the condition reduced to W, pull E back "+
			"(CoordinateSigmaPullback), apply CondIndepPointFiber at v_W with {F = ⊤}, and RegimeFaces."),
})}

var DoObserveRatio = doObserveRatioThm{family.Add(registry.ProofEntry{
	Name:    "DoObserveRatio",
	Reading: "Only P_x(z, w) ≠ 0 is stated; P_x(w) ≠ 0 follows by monotonicity.",
	Key:     "prop_52f7bb105fe697cd",
	Deps:    []registry.EntryLike{DoObserve, measurable_space.AgreeOnMeasurable},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z W:set(I). ∀v:(I → B). ∀E:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ Z ∪ W ⇒ {v(i)} ∈ M.state_sigma(i)",
			"E ∈ " +
				"coordinate_sigma(indexed_functions(M.nodes, M.default, M.states), " +
				"    λf:(I → B). f, " +
				"    M.state_sigma, " +
				"    Y)",
			"d_separated(dag_delete_in(M.edges, X), Y, Z, X ∪ W)",
			"«Px»(agree_on(Z ∪ W, v)) ≠ &0",
		},
		Conclusion: "cond_prob(«Px», E, agree_on(Z ∪ W, v)) = cond_prob(«Px», E, agree_on(W, v))",
	},
		"P_x(E | z, w) = P_x(E | w) where P_x(z, w) > 0: DoObserve with F the configurations "+
			"agreeing with v on Z, an event of the Z-coordinates (AgreeOnMeasurable), divided by "+
			"P_x(z, w) P_x(w), both finite and the second at least the first."),
})}

var DoExchangeRatio = doExchangeRatioThm{family.Add(registry.ProofEntry{
	Name: "DoExchangeRatio",
	Key:  "prop_f65de61575fb0d33",
	Deps: []registry.EntryLike{DoExchange},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z W:set(I). ∀v:(I → B). ∀E:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ Z ∪ W ⇒ {v(i)} ∈ M.state_sigma(i)",
			"E ∈ " +
				"coordinate_sigma(indexed_functions(M.nodes, M.default, M.states), " +
				"    λf:(I → B). f, " +
				"    M.state_sigma, " +
				"    Y)",
			"d_separated(dag_delete_out(dag_delete_in(M.edges, X), Z), Y, Z, X ∪ W)",
			"«Pxz»(agree_on(W, v)) ≠ &0",
			"«Px»(agree_on(Z ∪ W, v)) ≠ &0",
		},
		Conclusion: "cond_prob(«Pxz», E, agree_on(W, v)) = cond_prob(«Px», E, agree_on(Z ∪ W, v))",
	},
		"P_{x,z}(E | w) = P_x(E | z, w) where both denominators are positive: divide DoExchange."),
})}

var DoDeleteRatio = doDeleteRatioThm{family.Add(registry.ProofEntry{
	Name: "DoDeleteRatio",
	Key:  "prop_2f0865ce4ee8b42",
	Deps: []registry.EntryLike{DoDelete},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z W:set(I). ∀v:(I → B). ∀E:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"W ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"X ∩ W = ∅",
			"Y ∩ Z = ∅",
			"Y ∩ W = ∅",
			"Z ∩ W = ∅",
			"∀i:I. i ∈ X ∪ Z ⇒ v(i) ∈ M.states(i)",
			"∀i:I. i ∈ W ⇒ {v(i)} ∈ M.state_sigma(i)",
			"E ∈ " +
				"coordinate_sigma(indexed_functions(M.nodes, M.default, M.states), " +
				"    λf:(I → B). f, " +
				"    M.state_sigma, " +
				"    Y)",
			"d_separated( " +
				"    dag_delete_in(dag_delete_in(M.edges, X), Z ∖ dag_ancestors(dag_delete_in(M.edges, X), W)), " +
				"    Y, " +
				"    Z, " +
				"    X ∪ W)",
			"«Pxz»(agree_on(W, v)) ≠ &0",
			"«Px»(agree_on(W, v)) ≠ &0",
		},
		Conclusion: "cond_prob(«Pxz», E, agree_on(W, v)) = cond_prob(«Px», E, agree_on(W, v))",
	},
		"P_{x,z}(E | w) = P_x(E | w) where both denominators are positive: divide DoDelete."),
})}
