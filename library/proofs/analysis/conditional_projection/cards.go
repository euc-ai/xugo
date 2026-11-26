package conditional_projection

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/analysis/l2_space"
	"github.com/euc-ai/xugo/library/proofs/analysis/lp_space"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/measure/complex_measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/registry"
)

var CondExpExistsL2 = condExpExistsL2Thm{family.Add(registry.ProofEntry{
	Name: "CondExpExistsL2",
	Reading: "Finiteness of μ is needed: for counting measure on ℕ, G = {∅, Ω} and X " +
		"the indicator of {0}, no G-measurable integrable Y matches the integral of X over Ω.",
	Deps: []registry.EntryLike{
		l2_space.L2Hilbert,
		lp_space.LpMeasurableClosed,
		lp_space.LpMeasurableRepresentative,
		lp_space.LpNested,
		hilbert_space.OrthogonalDecomposition,
		l2_space.L2InnerClasses,
		event_integral.EventIntegralCarrier,
		event_integral.EventIntegralEqOn,
		event_integral.EventIntegralRestrict,
		event_integral.EventIntegralSub,
	},
	Key: "prop_a2eaf9be2f38f0bb",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X:(A → real).",
		Hypotheses: []string{
			"finite_measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"real_measurable(Ω, S, X)",
			"real_integrable(Ω, S, μ, λx:A. X(x) * X(x))",
		},
		Conclusion: "∃Y:(A → real). " +
			"    is_cond_exp(Ω, S, μ, G, X, Y) ∧ real_integrable(Ω, S, μ, λx:A. Y(x) * Y(x))",
	},
		"Project the class of the complex embedding of X onto the closed G-measurable L2 "+
			"subspace. Choose a genuinely G-measurable representative and take its real part; "+
			"orthogonality to every event indicator gives the defining event-integral identity."),
})}

var CondExpIffProjection = condExpIffProjectionThm{family.Add(registry.ProofEntry{
	Name: "CondExpIffProjection",
	Deps: []registry.EntryLike{
		l2_space.L2Hilbert,
		lp_space.SimpleDenseInLp,
		lp_space.LpMeasurableClosed,
		hilbert_space.OrthogonalDecomposition,
		l2_space.L2InnerClasses,
		lp_space.LpMeasurableRepresentative,
		event_integral.EventIntegralCarrier,
		event_integral.EventIntegralEqOn,
		event_integral.EventIntegralRestrict,
		event_integral.EventIntegralSub,
	},
	Key: "prop_e0e1389fb706b4a4",
	Reading: "G-measurability of Y is required: equality of its ambient a.e. class with " +
		"a projected class would not force an arbitrary representative to be G-measurable " +
		"on an incomplete space. Finiteness of μ carries ⇐: in the counting-measure example " +
		"the projection of X is zero, yet zero is not its conditional expectation.",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y:(A → real).",
		Hypotheses: []string{
			"finite_measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"real_measurable(Ω, S, X)",
			"real_measurable(Ω, G, Y)",
			"real_integrable(Ω, S, μ, λx:A. X(x) * X(x))",
			"real_integrable(Ω, S, μ, λx:A. Y(x) * Y(x))",
		},
		Conclusion: "is_cond_exp(Ω, S, μ, G, X, Y) ⇔ " +
			"real_ae_class(Ω, S, μ, Y) = " +
			"hilbert_projection(lp_module(Ω, S, μ, &2), " +
			"    l2_inner(Ω, S, μ), " +
			"    lp_measurable_subspace(Ω, S, μ, G, &2), " +
			"    real_ae_class(Ω, S, μ, X))",
	},
		"The relation gives orthogonality to G-event indicators, then to simple "+
			"functions, and then to all of L2(G) by simple density. Conversely projection "+
			"orthogonality tested on indicators gives every event-integral identity."),
})}

var CondExpL2Bound = condExpL2BoundThm{family.Add(registry.ProofEntry{
	Name: "CondExpL2Bound",
	Deps: []registry.EntryLike{
		CondExpExistsL2,
		CondExpIffProjection,
		conditional_expectation.CondExpUnique,
		hilbert_space.ProjectionLinearContraction,
		measure_integral.IntegrableAE,
		l2_space.L2Hilbert,
		lp_space.LpMeasurableClosed,
	},
	Key: "prop_7746bffa27af4e8a",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y:(A → real).",
		Hypotheses: []string{
			"finite_measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"is_cond_exp(Ω, S, μ, G, X, Y)",
			"real_integrable(Ω, S, μ, λx:A. X(x) * X(x))",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. Y(x) * Y(x)) ∧ " +
			"measure_integral(Ω, S, μ, λx:A. Y(x) * Y(x)) ≤ measure_integral(Ω, S, μ, λx:A. X(x) * X(x))",
	},
		"The projected conditional expectation is square integrable and contractive. Relation "+
			"uniqueness makes Y agree a.e. with it, preserving square integrability and the bound."),
})}

var CondExpResidualOrthogonal = condExpResidualOrthogonalThm{family.Add(registry.ProofEntry{
	Name: "CondExpResidualOrthogonal",
	Key:  "prop_cc5df69499f5f06a",
	Reading: "Finiteness of μ is needed for the same reason as in " +
		"CondExpExistsL2: the projection characterization fails on counting measure.",
	Deps: []registry.EntryLike{
		CondExpIffProjection,
		CondExpL2Bound,
		hilbert_space.OrthogonalDecomposition,
		l2_space.L2Hilbert,
		l2_space.L2InnerClasses,
		lp_space.LpMeasurableClosed,
		lp_space.LpMeasurableRepresentative,
		complex_measure_integral.SquareProductIntegrable,
		complex_measure_integral.ComplexRealEmbedding,
		measure_integral.IntegrableDominated,
		complex_field.PartsOfReal,
		complex_field.ConjOfReal,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y Z:(A → real).",
		Hypotheses: []string{
			"finite_measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"is_cond_exp(Ω, S, μ, G, X, Y)",
			"real_integrable(Ω, S, μ, λx:A. X(x) * X(x))",
			"real_measurable(Ω, G, Z)",
			"real_integrable(Ω, S, μ, λx:A. Z(x) * Z(x))",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. (X(x) - Y(x)) * Z(x)) ∧ " +
			"measure_integral(Ω, S, μ, λx:A. (X(x) - Y(x)) * Z(x)) = &0",
	},
		"Y is square integrable (CondExpL2Bound), so the product of the residual with Z is "+
			"integrable (SquareProductIntegrable). By CondExpIffProjection the class of Y is the "+
			"projection of the class of X onto the closed subspace of G-measurable classes, which "+
			"contains the class of Z (LpMeasurableRepresentative); the residual is orthogonal to "+
			"that subspace (OrthogonalDecomposition), and L2InnerClasses reads the inner product "+
			"as the integral of (X − Y)·Z, real since all three are real (ComplexRealEmbedding)."),
})}

var CondExpExists = condExpExistsThm{family.Add(registry.ProofEntry{
	Name: "CondExpExists",
	Deps: []registry.EntryLike{
		CondExpExistsL2,
		integral_convergence.BoundedTruncationL1,
		lp_space.FastCauchyLimit,
		conditional_expectation.CondExpLinear,
		conditional_expectation.CondExpContraction,
		event_integral.EventIntegralL1Limit,
	},
	Key: "prop_57b1bdd9b49f0b4a",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X:(A → real).",
		Hypotheses: []string{
			"finite_measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"real_integrable(Ω, S, μ, X)",
		},
		Conclusion: "∃Y:(A → real). is_cond_exp(Ω, S, μ, G, X, Y)",
	},
		"Bounded truncations of X are square integrable and converge in L1. The relation "+
			"contraction makes their conditional expectations L1-Cauchy; FastCauchyLimit "+
			"supplies a genuinely G-measurable limit and event integrals pass to it."),
})}

var CondExpSpecification = condExpSpecificationThm{family.Add(registry.ProofEntry{
	Name: "CondExpSpecification",
	Reading: "Finiteness of μ and integrability of X make cond_exp " +
		"the relation's witness; otherwise it is an arbitrary function.",
	Deps: []registry.EntryLike{CondExpExists},
	Key:  "prop_e32e54c5cdf98141",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X:(A → real).",
		Hypotheses: []string{
			"finite_measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"real_integrable(Ω, S, μ, X)",
		},
		Conclusion: "is_cond_exp(Ω, S, μ, G, X, cond_exp(Ω, S, μ, G, X))",
	},
		"Apply choice to conditional-expectation existence; the definition itself assumes no existence."),
})}

var ConditionalClassOperator = conditionalClassOperatorThm{family.Add(registry.ProofEntry{
	Name: "ConditionalClassOperator",
	Deps: []registry.EntryLike{
		CondExpSpecification,
		conditional_expectation.CondExpUnique,
		conditional_expectation.CondExpLinear,
		conditional_expectation.CondExpContraction,
		module_homomorphism.QuotientRelationDescends,
		equivalence.InducedMapClass,
	},
	Key: "prop_fb3123513692f3c0",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G:set(set(A)).",
		Hypotheses: []string{"finite_measure_on(Ω, S, μ)", "sigma_algebra_on(Ω, G)", "G ⊆ S"},
		Conclusion: "bounded_operator(lp_module(Ω, S, μ, &1), " +
			"    lp_norm(Ω, S, μ, &1), " +
			"    lp_module(Ω, S, μ, &1), " +
			"    lp_norm(Ω, S, μ, &1), " +
			"    conditional_class(Ω, S, μ, G)) ∧ " +
			"image(conditional_class(Ω, S, μ, G), lp_module(Ω, S, μ, &1).carrier) ⊆ " +
			"lp_measurable_subspace(Ω, S, μ, G, &1)",
	},
		"Apply QuotientRelationDescends to the real and imaginary conditional-expectation "+
			"relations. Uniqueness identifies its coset values with the induced map in the "+
			"definition; the two real L1 bounds give a finite complex operator bound."),
})}

var ConditionalClassRealContraction = conditionalClassRealContractionThm{family.Add(registry.ProofEntry{
	Name: "ConditionalClassRealContraction",
	Deps: []registry.EntryLike{
		CondExpSpecification,
		conditional_expectation.CondExpContraction,
		conditional_expectation.CondExpUnique,
		equivalence.InducedMapClass,
	},
	Key: "prop_4624d674206a9dc9",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀Q:set(A → complex).",
		Hypotheses: []string{
			"finite_measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"Q ∈ lp_real_module(Ω, S, μ, &1).carrier",
		},
		Conclusion: "conditional_class(Ω, S, μ, G, Q) ∈ lp_real_module(Ω, S, μ, &1).carrier ∧ " +
			"lp_norm(Ω, S, μ, &1, conditional_class(Ω, S, μ, G, Q)) ≤ lp_norm(Ω, S, μ, &1, Q)",
	},
		"Choose a real representative and evaluate the induced map on its "+
			"coset. The relation contraction gives the class norm bound, and "+
			"the zero imaginary component has zero conditional expectation a.e."),
})}

var ConditionalClassProjection = conditionalClassProjectionThm{family.Add(registry.ProofEntry{
	Name: "ConditionalClassProjection",
	Deps: []registry.EntryLike{
		CondExpIffProjection,
		CondExpSpecification,
		CondExpL2Bound,
		lp_space.LpNested,
		hilbert_space.ProjectionLinearContraction,
		l2_space.L2Hilbert,
		lp_space.LpMeasurableClosed,
	},
	Key: "prop_48d2960fcfae936c",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀Q:set(A → complex).",
		Hypotheses: []string{
			"finite_measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"Q ∈ lp_module(Ω, S, μ, &2).carrier",
		},
		Conclusion: "conditional_class(Ω, S, μ, G, Q) = " +
			"hilbert_projection(lp_module(Ω, S, μ, &2), " +
			"    l2_inner(Ω, S, μ), " +
			"    lp_measurable_subspace(Ω, S, μ, G, &2), " +
			"    Q)",
	},
		"Apply the real projection characterization to both components and "+
			"use complex linearity of the projection. The L2-to-L1 embedding "+
			"makes the same ambient class admissible to the class operator."),
})}
