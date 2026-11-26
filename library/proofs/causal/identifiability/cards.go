package identifiability

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/causal/adjustment"
	"github.com/euc-ai/xugo/library/proofs/causal/intervention"
	"github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

var IdentifiedByFunctional = identifiedByFunctionalThm{family.Add(registry.ProofEntry{
	Name: "IdentifiedByFunctional",
	Key:  "prop_522bcce4c0ea7e2f",
	Build: family.Card(Statement{
		Binders: "∀C:(scm_model(A, B, I) → bool). ∀O:set(I). ∀Q:(scm_model(A, B, I) → real).",
		Hypotheses: []string{
			"∃Φ:(((I → B) → extended_nonneg_real) → real). ∀M:scm_model(A, B, I). " +
				"    C(M) ⇒ Q(M) = Φ(λv:(I → B). scm_distribution(M, agree_on(O, v)))",
		},
		Conclusion: "scm_identifiable(C, O, Q)",
	},
		"A query that is, on the class, a functional of the masses of the observed configurations "+
			"is identifiable: two models with the same masses give the functional the same argument."),
})}

var PositiveInterventional = positiveInterventionalThm{family.Add(registry.ProofEntry{
	Name: "PositiveInterventional",
	Key:  "prop_76fd9bb15631c666",
	Reading: "X and K may overlap: on X the intervened coordinates are the values " +
		"v. To use InterventionConsistencyMeasure take E as the configurations in " +
		"agree_on(K, v); agree_on itself is not in the product σ-algebra.",
	Deps: []registry.EntryLike{
		intervention.InterventionConsistencyMeasure,
		measurable_space.AgreeOnMeasurable,
		measure_space.MeasureMono,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀O:set(I). " +
			"∀D:(I → set(B)). " +
			"∀M:scm_model(A, B, I). " +
			"∀X K:set(I). " +
			"∀v:(I → B).",
		Hypotheses: []string{
			"positive_scm(V, E, O, D, M)",
			"X ⊆ O",
			"K ⊆ O",
			"∀i:I. i ∈ O ⇒ v(i) ∈ D(i)",
		},
		Conclusion: "scm_distribution(scm_do(M, X, v), agree_on(K, v)) ≠ &0",
	},
		"Positivity passes to interventions on observed nodes: by consistency P_x(V_K = "+
			"v_K) ≥ P(V_X = v_X, V_K = v_K) ≥ P(V_O = v_O) > 0 (InterventionConsistencyMeasure, "+
			"the events measurable by AgreeOnMeasurable). So every interventional conditional "+
			"probability on observed nodes has a positive denominator in the class."),
})}

var ObservedMarginal = observedMarginalThm{family.Add(registry.ProofEntry{
	Name: "ObservedMarginal",
	Reading: "When v leaves D on K both preimages are empty, " +
		"so both sides are 0 with no measurability argument.",
	Key: "prop_6153229721d99d4",
	Deps: []registry.EntryLike{
		structural_model.ScmSolutionStates,
		indexed_functions.IndexedFunctionsFinite,
		measure_space.MeasureFiniteAdditive,
		measurable_space.AgreeOnMeasurable,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀O:set(I). " +
			"∀D:(I → set(B)). " +
			"∀M:scm_model(A, B, I). " +
			"∀K:set(I). " +
			"∀v:(I → B).",
		Hypotheses: []string{"positive_scm(V, E, O, D, M)", "K ⊆ O"},
		Conclusion: "scm_distribution(M, agree_on(K, v)) = " +
			"Σ_{w∈indexed_functions(O ∖ K, v, D)} scm_distribution(M, agree_on(O, w))",
	},
		"The probability of a partial observed configuration is the sum of the masses of its "+
			"completions: the solution's observed coordinates lie in the finite carriers "+
			"(ScmSolutionStates), so the events {V_O = w}, w agreeing with v on K, partition {V_K = "+
			"v_K} into finitely many measurable pieces (IndexedFunctionsFinite, AgreeOnMeasurable, "+
			"MeasureFiniteAdditive). When v leaves the carriers on K both sides are zero."),
})}

var BackdoorIdentifiable = backdoorIdentifiableThm{family.Add(registry.ProofEntry{
	Name: "BackdoorIdentifiable",
	Key:  "prop_afd17039c7facab5",
	Reading: "Only legal values on X are needed, for the intervened model " +
		"to be legal; a value of v off the carrier on Y makes the effect 0 in " +
		"every model. The summation sets are indexed_functions over D, since " +
		"M.states = D on O, so the functional does not depend on the model.",
	Deps: []registry.EntryLike{
		adjustment.BackdoorAdjustment,
		IdentifiedByFunctional,
		ObservedMarginal,
		PositiveInterventional,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O:set(I). ∀D:(I → set(B)). ∀X Y Z:set(I). ∀v:(I → B).",
		Hypotheses: []string{
			"backdoor_criterion(E, X, Y, Z)",
			"X ⊆ O",
			"Y ⊆ O",
			"Z ⊆ O",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
			"∀i:I. i ∈ X ⇒ v(i) ∈ D(i)",
		},
		Conclusion: "scm_identifiable(«positiveClass», O, «effect»)",
	},
		"In the positive class the back-door formula's support condition always holds, and its "+
			"right side reads only probabilities of observed configurations, each a sum of observed "+
			"masses (ObservedMarginal): a functional of them, so IdentifiedByFunctional applies."),
})}

var FrontdoorIdentifiable = frontdoorIdentifiableThm{family.Add(registry.ProofEntry{
	Name: "FrontdoorIdentifiable",
	Key:  "prop_5a432b41612ce4fa",
	Reading: "Only legal values on X are needed, for the intervened model " +
		"to be legal; a value of v off the carrier on Y makes the effect 0 in " +
		"every model. The summation sets are indexed_functions over D, since " +
		"M.states = D on O, so the functional does not depend on the model.",
	Deps: []registry.EntryLike{
		adjustment.FrontdoorAdjustment,
		IdentifiedByFunctional,
		ObservedMarginal,
		PositiveInterventional,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). ∀E:(I → I → bool). ∀O:set(I). ∀D:(I → set(B)). ∀X Y Z:set(I). ∀v:(I → B).",
		Hypotheses: []string{
			"frontdoor_criterion(E, X, Y, Z)",
			"X ⊆ O",
			"Y ⊆ O",
			"Z ⊆ O",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
			"∀i:I. i ∈ X ⇒ v(i) ∈ D(i)",
		},
		Conclusion: "scm_identifiable(«positiveClass», O, «effect»)",
	},
		"As for the back door: the front-door formula's support conditions hold in the "+
			"positive class, and its right side is a functional of the observed masses. The "+
			"latent nodes, the hidden common cause of X and Y among them, are unobserved and free."),
})}

var BowNotIdentifiable = bowNotIdentifiableThm{family.Add(registry.ProofEntry{
	Name: "BowNotIdentifiable",
	Reading: "In the natural run bow_x copies bow_u, so c is never reached and " +
		"the solution maps of the two models coincide; the observed law is uniform.",
	Key: "prop_ff60131c30fc0157",
	Deps: []registry.EntryLike{
		BowModelDef,
		BowNodeDistinct,
		intervention.DoCoordinate,
		structural_model.ScmSolution,
	},
	Build: family.Card(Statement{
		Conclusion: "(∀c:bool. «bowClass»(bow_model(c))) ∧ " +
			"(∀v:(bow_node → bool). " +
			"    scm_distribution(bow_model(⊥), agree_on({bow_x, bow_y}, v)) = " +
			"    scm_distribution(bow_model(⊤), agree_on({bow_x, bow_y}, v))) ∧ " +
			"«bowEffect»(bow_model(⊥)) = &1 / &4 ∧ " +
			"«bowEffect»(bow_model(⊤)) = &3 / &4 ∧ " +
			"¬scm_identifiable(«bowClass», {bow_x, bow_y}, «bowEffect»)",
		Abbrev: Abbrev{
			{Name: "bowClass", Text: "λM:scm_model(prod(bool, bool), bool, bow_node). " +
				"    positive_scm({bow_u, bow_x, bow_y}, " +
				"        pair_relation({(bow_u, bow_x), (bow_u, bow_y), (bow_x, bow_y)}), " +
				"        {bow_x, bow_y}, " +
				"        λi:bow_node. 𝕌⟨A:bool⟩, " +
				"        M)"},
			{Name: "bowEffect", Text: "λM:scm_model(prod(bool, bool), bool, bow_node). " +
				"    extended_to_real( " +
				"        scm_distribution(scm_do(M, {bow_x}, λi:bow_node. ⊥), agree_on({bow_y}, λi:bow_node. ⊤)))"},
		},
	},
		"The bow graph U → X, U → Y, X → Y with U latent. Both models are legal with "+
			"independent noise: σ(fst), the trivial σ-algebra and σ(snd) under the uniform law on "+
			"bool × bool. In the natural run X = U, so Y is its noise and every observed "+
			"configuration has mass 1/4 in both. Under do(X = ⊥), Y = ⊤ when U = ⊥ and Y's coin "+
			"shows ⊤, or when U = ⊤ and c = ⊤: 1/4 for c = ⊥ and 3/4 for c = ⊤. The observed law is "+
			"strictly positive; what it does not fix is how the mechanism of Y behaves off X = U."),
})}

var FrontdoorExample = frontdoorExampleThm{family.Add(registry.ProofEntry{
	Name: "FrontdoorExample",
	Key:  "prop_cd817edf66367c64",
	Deps: []registry.EntryLike{
		d_separation.SeparationCertificate,
		dag.AncestorsUpperBound,
		FdNodeDistinct,
	},
	Build: family.Card(Statement{
		Conclusion: "frontdoor_criterion( " +
			"    pair_relation({(fd_u, fd_x), (fd_u, fd_y), (fd_x, fd_z), (fd_z, fd_y)}), " +
			"    {fd_x}, " +
			"    {fd_y}, " +
			"    {fd_z})",
	},
		"The graph U → X, U → Y, X → Z → Y meets the front-door criterion for X on Y through "+
			"Z. With Z's in-edges deleted the ancestors of Y are Y, U and Z (AncestorsUpperBound "+
			"at {fd_y, fd_u, fd_z}). With X's out-edges deleted, ∅ separates Z from X: U = {x, z, "+
			"u}, S = {z}. With Z's out-edges deleted, X separates Y from Z: U = {u, x, y, z}, S = "+
			"{y, u}. Each certificate's obligations are finite set facts on the literal, closed by "+
			"unfolding the bounded quantifiers, splitting the pairs and the vertices' distinctness "+
			"(FdNodeDistinct); this is the first instance of the concrete-graph spelling."),
})}

var FrontdoorExampleIdentifiable = frontdoorExampleIdentifiableThm{family.Add(registry.ProofEntry{
	Name: "FrontdoorExampleIdentifiable",
	Key:  "prop_dba713c1efe5b1af",
	Reading: "The pair of the bow graph: there X → Y is direct and the effect is not identifiable; " +
		"here it passes through the observed mediator Z. Only v's value on fd_x is constrained.",
	Deps: []registry.EntryLike{FrontdoorExample, FrontdoorIdentifiable, FdNodeDistinct},
	Build: family.Card(Statement{
		Binders:    "∀D:(fd_node → set(B)). ∀v:(fd_node → B).",
		Hypotheses: []string{"v(fd_x) ∈ D(fd_x)"},
		Conclusion: "scm_identifiable(«fdClass», " +
			"    {fd_x, fd_z, fd_y}, " +
			"    λM:scm_model(A, B, fd_node). " +
			"        extended_to_real(scm_distribution(scm_do(M, {fd_x}, v), agree_on({fd_y}, v))))",
		Abbrev: Abbrev{
			{Name: "fdClass", Text: "λM:scm_model(A, B, fd_node). " +
				"    positive_scm({fd_u, fd_x, fd_z, fd_y}, " +
				"        pair_relation({(fd_u, fd_x), (fd_u, fd_y), (fd_x, fd_z), (fd_z, fd_y)}), " +
				"        {fd_x, fd_z, fd_y}, " +
				"        D, " +
				"        M)"},
		},
	},
		"On the front-door graph with U unobserved, the effect of X on Y is identifiable on the "+
			"positive class, whatever the observed carriers and the latent space: FrontdoorIdentifiable at "+
			"the groups {fd_x}, {fd_y}, {fd_z}, its criterion FrontdoorExample, the three groups disjoint "+
			"and observed by FdNodeDistinct. With the bow graph it shows that a latent common cause of X "+
			"and Y blocks identification only when no observed mediator carries the whole effect."),
})}
