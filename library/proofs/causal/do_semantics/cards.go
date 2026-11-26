package do_semantics

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/causal/do_calculus"
	"github.com/euc-ai/xugo/library/proofs/causal/do_derivation"
	"github.com/euc-ai/xugo/library/proofs/causal/identifiability"
	"github.com/euc-ai/xugo/library/proofs/causal/intervention"
	"github.com/euc-ai/xugo/library/proofs/causal/structural_model"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

var EvalCoincidence = evalCoincidenceThm{family.Add(registry.ProofEntry{
	Name: "EvalCoincidence",
	Reading: "No hypothesis on M: the intervention reads v only on X through override_on, and the " +
		"sum case is the bijection u ↦ override_on(Z, u, w), which holds for infinite index sets too.",
	Key: "prop_6b5921382b2d5607",
	Deps: []registry.EntryLike{
		do_derivation.DoExprInduction,
		indexed_functions.IndexedFunctionsExtensional,
	},
	Build: family.Card(Statement{
		Binders:    "∀M:scm_model(A, B, I). ∀v w:(I → B). ∀e:do_expr(I).",
		Hypotheses: []string{"∀i:I. i ∈ do_expr_free(e) ⇒ v(i) = w(i)"},
		Conclusion: "do_expr_eval(M, v, e) = do_expr_eval(M, w, e)",
	},
		"The value reads the environment only at the free nodes. By induction on e: an "+
			"atom reads v on its three groups, the intervention only on X; a sum over Z ranges "+
			"over environments that override v on Z, and overriding the two environments on Z "+
			"with one configuration gives environments that agree on the free nodes of the "+
			"body, so the two sums run over sets in bijection with equal terms."),
})}

var EvalPositive = evalPositiveThm{family.Add(registry.ProofEntry{
	Name: "EvalPositive",
	Reading: "The observed environment is load-bearing: v itself lies in each sum's " +
		"index set, so every sum is nonempty; finite V and finite carriers make it finite.",
	Key: "prop_7548e2c768af7ea3",
	Deps: []registry.EntryLike{
		do_derivation.DoExprInduction,
		identifiability.PositiveInterventional,
		indexed_functions.IndexedFunctionsFinite,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀O:set(I). " +
			"∀D:(I → set(B)). " +
			"∀M:scm_model(A, B, I). " +
			"∀v:(I → B). " +
			"∀e:do_expr(I).",
		Hypotheses: []string{
			"positive_scm(V, E, O, D, M)",
			"do_expr_wf(O, e)",
			"∀i:I. i ∈ O ⇒ v(i) ∈ D(i)",
		},
		Conclusion: "&0 < do_expr_eval(M, v, e)",
	},
		"In the positive class a well-formed expression is positive at every observed "+
			"configuration, so the total division never meets a zero denominator. By induction: an "+
			"atom is a ratio of two positive interventional probabilities (PositiveInterventional); a "+
			"sum over Z runs over a finite nonempty set of observed configurations, the carriers being "+
			"finite and nonempty, of positive terms; products and quotients of positives are positive."),
})}

var ObservationalEvalAgrees = observationalEvalAgreesThm{family.Add(registry.ProofEntry{
	Name: "ObservationalEvalAgrees",
	Reading: "Holds at every environment, observed or not: ObservedMarginal " +
		"is stated for every v, and the two models share the carriers on O.",
	Key: "prop_2896caa9ebfe01c",
	Deps: []registry.EntryLike{
		do_derivation.DoExprInduction,
		intervention.DoEmpty,
		identifiability.ObservedMarginal,
		indexed_functions.IndexedFunctionsCongruence,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀O:set(I). " +
			"∀D:(I → set(B)). " +
			"∀M₁ M₂:scm_model(A, B, I). " +
			"∀v:(I → B). " +
			"∀e:do_expr(I).",
		Hypotheses: []string{
			"positive_scm(V, E, O, D, M₁)",
			"positive_scm(V, E, O, D, M₂)",
			"∀w:(I → B). scm_distribution(M₁, agree_on(O, w)) = scm_distribution(M₂, agree_on(O, w))",
			"do_expr_wf(O, e)",
			"do_expr_observational(e)",
		},
		Conclusion: "do_expr_eval(M₁, v, e) = do_expr_eval(M₂, v, e)",
	},
		"An observational expression depends on the model only through its observed "+
			"masses. By induction: an atom with no intervention is a conditional "+
			"probability of M itself (DoEmpty) between observed configurations, each a sum "+
			"of observed masses (ObservedMarginal); a sum ranges over configurations in "+
			"the observed carriers, which the class fixes (IndexedFunctionsCongruence). "+
			"The latent spaces of the two models may differ; they share the environment."),
})}

var DoDerivationSound = doDerivationSoundThm{family.Add(registry.ProofEntry{
	Name: "DoDerivationSound",
	Reading: "Rule by rule: conditioning needs no positivity (both inner denominators " +
		"are P_x(𝕌) = 1); marginalisation needs Y ∩ Z = ∅, else part of Y is summed; " +
		"nested sums need Z₁ ∩ Z₂ = ∅, else the overlap's carrier multiplies; the factor " +
		"rule needs free(a) ∩ Z = ∅; only a / a ~ 1 uses EvalPositive. The induction is " +
		"stated for every observed environment at once, since a sum moves the environment.",
	Key: "prop_52f1ac84ef7b6424",
	Deps: []registry.EntryLike{
		do_derivation.DoDerivableInduct,
		do_derivation.DerivableWellFormed,
		do_calculus.DoObserveRatio,
		do_calculus.DoExchangeRatio,
		do_calculus.DoDeleteRatio,
		identifiability.PositiveInterventional,
		EvalPositive,
		EvalCoincidence,
		indexed_functions.IndexedFunctionsFinite,
		structural_model.ScmSolutionStates,
		intervention.DoLegal,
		measurable_space.AgreeOnMeasurable,
		measure_space.MeasureFiniteAdditive,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀O:set(I). " +
			"∀D:(I → set(B)). " +
			"∀M:scm_model(A, B, I). " +
			"∀v:(I → B). " +
			"∀e₁ e₂:do_expr(I).",
		Hypotheses: []string{
			"do_derivable(E, O, e₁, e₂)",
			"positive_scm(V, E, O, D, M)",
			"∀i:I. i ∈ O ⇒ v(i) ∈ D(i)",
		},
		Conclusion: "do_expr_eval(M, v, e₁) = do_expr_eval(M, v, e₂)",
	},
		"Derivable expressions agree in every model of the positive class at every observed "+
			"configuration. By rule induction, for all configurations at once: the causal rules are "+
			"the ratio forms of the three rules, their denominators positive (PositiveInterventional); "+
			"conditioning, marginalisation and the empty event are measure identities, marginalisation "+
			"summing over the finite configurations of a group disjoint from the others; the algebraic "+
			"rules are laws of positive reals (EvalPositive), the factor rule reading EvalCoincidence. "+
			"Only the rule table couples this proof to the derivation side."),
})}

var DerivationIdentifies = derivationIdentifiesThm{family.Add(registry.ProofEntry{
	Name: "DerivationIdentifies",
	Reading: "Only legal values on X are asked: the observed carriers are nonempty in any " +
		"model of the class, so v is completed to an observed configuration off X ∪ Y, which " +
		"the query does not read; where v leaves a carrier on Y the effect is 0 in every " +
		"model. The query is the one BackdoorIdentifiable and FrontdoorIdentifiable state.",
	Key: "prop_35570e8a911b9a9c",
	Deps: []registry.EntryLike{
		DoDerivationSound,
		ObservationalEvalAgrees,
		EvalCoincidence,
		do_derivation.DerivableWellFormed,
		structural_model.ScmSolutionStates,
		intervention.DoLegal,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(I). " +
			"∀E:(I → I → bool). " +
			"∀O:set(I). " +
			"∀D:(I → set(B)). " +
			"∀X Y:set(I). " +
			"∀v:(I → B). " +
			"∀e:do_expr(I).",
		Hypotheses: []string{
			"do_derivable(E, O, do_prob(Y, X, ∅), e)",
			"do_expr_observational(e)",
			"∀i:I. i ∈ X ⇒ v(i) ∈ D(i)",
		},
		Conclusion: "scm_identifiable(λM:scm_model(A, B, I). positive_scm(V, E, O, D, M), " +
			"    O, " +
			"    λM:scm_model(A, B, I). extended_to_real(scm_distribution(scm_do(M, X, v), agree_on(Y, v))))",
	},
		"An interventional probability derived to an observational expression is identifiable on the "+
			"positive class. The atom do_prob(Y, X, ∅) reads P_x(V_Y = v_Y), the condition on ∅ being the "+
			"whole space of mass one. Given two models of the class with the same observed masses, their "+
			"observed carriers are nonempty (ScmSolutionStates), so v has a completion v′ to an observed "+
			"configuration agreeing with it on X ∪ Y, and the query is unchanged (EvalCoincidence); where "+
			"v leaves a carrier on Y both effects are 0. At v′ each model gives the query the value of e "+
			"(DoDerivationSound), and the two models give e the same value (ObservationalEvalAgrees)."),
})}
