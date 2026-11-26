package adjustment

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/causal/do_calculus"
	"github.com/euc-ai/xugo/library/proofs/causal/intervention"
	"github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

var BackdoorAdjustment = backdoorAdjustmentThm{family.Add(registry.ProofEntry{
	Name: "BackdoorAdjustment",
	Reading: "The support condition is load-bearing: where P(z) > 0 but P(x, z) = 0 the " +
		"term is 0 while P_x(E, z) can be positive. E is any event of the Y-coordinates, so the " +
		"outcome need not be finite or discrete; only X is read at a point. Z = ∅ gives P_x(E) " +
		"= P(E | x), the support condition then forcing P(x) > 0; X = ∅ is total probability.",
	Key: "prop_9e6fb125fbf30879",
	Deps: []registry.EntryLike{
		do_calculus.DoDelete,
		do_calculus.DoExchangeRatio,
		intervention.DoEmpty,
		dag.DescendantsAncestorsDual,
		structural_model.ScmSolutionStates,
		indexed_functions.IndexedFunctionsFinite,
		measure_space.MeasureFiniteAdditive,
		measurable_space.AgreeOnMeasurable,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z:set(I). ∀v:(I → B). ∀E:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
			"backdoor_criterion(M.edges, X, Y, Z)",
			"∀i:I. i ∈ X ⇒ {v(i)} ∈ M.state_sigma(i)",
			"∀i:I. i ∈ Z ⇒ finite(M.states(i)) ∧ M.state_sigma(i) = {s:set(B) | s ⊆ M.states(i)}",
			"E ∈ " +
				"coordinate_sigma(indexed_functions(M.nodes, M.default, M.states), " +
				"    λf:(I → B). f, " +
				"    M.state_sigma, " +
				"    Y)",
			"∀w:(I → B). " +
				"    w ∈ indexed_functions(Z, v, M.states) ∧ scm_distribution(M)(agree_on(Z, w)) ≠ &0 ⇒ " +
				"    scm_distribution(M)(agree_on(X ∪ Z, w)) ≠ &0",
		},
		Conclusion: "extended_to_real(«Px»(E)) = " +
			"real_sum(indexed_functions(Z, v, M.states), " +
			"    λw:(I → B). " +
			"        cond_prob(scm_distribution(M), E, agree_on(X ∪ Z, w)) * " +
			"        extended_to_real(scm_distribution(M)(agree_on(Z, w))))",
	},
		"P_x(E) = Σ_z P(E | x, z) P(z) for an event E of the Y-coordinates. Split P_x(E) over "+
			"the finitely many configurations of Z (IndexedFunctionsFinite, ScmSolutionStates, "+
			"MeasureFiniteAdditive). No point of X is an ancestor of Z, so with X's in-edges "+
			"deleted ∅ separates Z from X and Rule 3 gives P_x(z) = P(z) (DoDelete at an empty "+
			"first group, the outcome event the Z-configurations agreeing with w, DoEmpty). Where "+
			"P(z) > 0 the support condition makes P(x, z) > 0, and the separation with X's "+
			"out-edges deleted gives P_x(E | z) = P(E | x, z) by Rule 2 (DoExchangeRatio); where "+
			"P(z) = 0 both terms vanish. Only the summed nodes need finite carriers."),
})}

var FrontdoorAdjustment = frontdoorAdjustmentThm{family.Add(registry.ProofEntry{
	Name: "FrontdoorAdjustment",
	Reading: "P(x) ≠ 0 is load-bearing: otherwise every P(z | x) is 0 and the right " +
		"side is 0. The support condition is used only where P(x, z) > 0; elsewhere " +
		"both sides' terms vanish. E is any event of the Y-coordinates. That no point " +
		"of Z is an ancestor of X is derived from the second criterion, not stated.",
	Key: "prop_6b0666b502cc36e9",
	Deps: []registry.EntryLike{
		BackdoorAdjustment,
		do_calculus.DoExchangeRatio,
		do_calculus.DoDeleteRatio,
		do_calculus.DoDelete,
		d_separation.DSeparatedEdgeMonotone,
		intervention.DoEmpty,
		intervention.DoCompose,
		indexed_functions.IndexedFunctionsFinite,
		measure_space.MeasureFiniteAdditive,
		measurable_space.AgreeOnMeasurable,
	},
	Build: family.Card(Statement{
		Binders: "∀M:scm_model(A, B, I). ∀X Y Z:set(I). ∀v:(I → B). ∀E:set(I → B).",
		Hypotheses: []string{
			"scm_on(M)",
			"scm_noise_independent(M)",
			"X ⊆ M.nodes",
			"Y ⊆ M.nodes",
			"Z ⊆ M.nodes",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
			"frontdoor_criterion(M.edges, X, Y, Z)",
			"∀i:I. i ∈ X ∪ Z ⇒ finite(M.states(i)) ∧ M.state_sigma(i) = {s:set(B) | s ⊆ M.states(i)}",
			"∀i:I. i ∈ X ⇒ v(i) ∈ M.states(i)",
			"E ∈ " +
				"coordinate_sigma(indexed_functions(M.nodes, M.default, M.states), " +
				"    λf:(I → B). f, " +
				"    M.state_sigma, " +
				"    Y)",
			"scm_distribution(M)(agree_on(X, v)) ≠ &0",
			"∀w w':(I → B). " +
				"    w ∈ indexed_functions(Z, v, M.states) ∧ " +
				"    w' ∈ indexed_functions(X, w, M.states) ∧ " +
				"    scm_distribution(M)(agree_on(X ∪ Z, w)) ≠ &0 ∧ " +
				"    scm_distribution(M)(agree_on(X, w')) ≠ &0 ⇒ " +
				"    scm_distribution(M)(agree_on(X ∪ Z, w')) ≠ &0",
		},
		Conclusion: "extended_to_real(«Px»(E)) = " +
			"real_sum(indexed_functions(Z, v, M.states), " +
			"    λw:(I → B). " +
			"        cond_prob(scm_distribution(M), agree_on(Z, w), agree_on(X, w)) * " +
			"        real_sum(indexed_functions(X, w, M.states), " +
			"            λw':(I → B). " +
			"                cond_prob(scm_distribution(M), E, agree_on(Z ∪ X, w')) * " +
			"                extended_to_real(scm_distribution(M)(agree_on(X, w')))))",
	},
		"P_x(E) = Σ_z P(z | x) Σ_{x'} P(E | z, x') P(x') for an event E of the Y-coordinates, with a "+
			"hidden common cause of X and Y allowed. The second condition gives P_x(z) = P(z | x) by "+
			"Rule 2; the third, with separation kept under edge deletion, gives P_x(E, z) = P_{x,z}(E) "+
			"P_x(z) by Rule 2; the first leaves X isolated in the ancestral graph with the in-edges of Z "+
			"and X deleted, so P_{x,z}(E) = P_z(E) by Rule 3. The second condition also makes X free of "+
			"descendants of Z, and with the third that is the back-door criterion of X for the effect of "+
			"Z on Y: the inner sum is BackdoorAdjustment. The support is P(x) > 0 and, for all z and x', "+
			"P(x, z) > 0 and P(x') > 0 giving P(x', z) > 0; the joint law need not be strictly positive."),
})}
