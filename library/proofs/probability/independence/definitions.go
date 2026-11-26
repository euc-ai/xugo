package independence

import (
	"github.com/euc-ai/xugo/library/registry"
)

var IndependentSigmaDef = independentSigmaDefThm{family.Define(registry.DefEntry{
	Name:  "IndependentSigmaDef",
	Key:   "prop_9aa98d7131382830",
	Const: "independent_sigma",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(set(A)) → " +
		"set(set(A)) → " +
		"bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H:set(set(A)). " +
			"    independent_sigma(Ω, S, μ, G, H) ⇔ " +
			"    probability_on(Ω, S, μ) ∧ " +
			"    sigma_algebra_on(Ω, G) ∧ " +
			"    sigma_algebra_on(Ω, H) ∧ " +
			"    G ⊆ S ∧ " +
			"    H ⊆ S ∧ " +
			"    (∀E D:set(A). E ∈ G ∧ D ∈ H ⇒ μ(E ∩ D) = μ(E) * μ(D))",
	},
})}

// IndependentVariablesDef — two real random variables are independent
// when they are measurable and the σ-algebras they generate are
// independent.
var IndependentVariablesDef = independentVariablesDefThm{family.Define(registry.DefEntry{
	Name:  "IndependentVariablesDef",
	Key:   "prop_490e5bffea0b786b",
	Const: "independent_variables",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(A → real) → " +
		"(A → real) → " +
		"bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀X Y:(A → real). " +
			"    independent_variables(Ω, S, μ, X, Y) ⇔ " +
			"    real_measurable(Ω, S, X) ∧ " +
			"    real_measurable(Ω, S, Y) ∧ " +
			"    independent_sigma(Ω, " +
			"        S, " +
			"        μ, " +
			"        pullback_sigma(Ω, X, borel_sets(real_topology)), " +
			"        pullback_sigma(Ω, Y, borel_sets(real_topology)))",
	},
	Deps: []registry.EntryLike{IndependentSigmaDef},
})}

var IndependentFamilyDef = independentFamilyDefThm{family.Define(registry.DefEntry{
	Name:  "IndependentFamilyDef",
	Key:   "prop_b6365672d0d8bd33",
	Const: "independent_sigma_family",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(I) → " +
		"(I → set(set(A))) → " +
		"bool",
	Reading: "The carrier intersects the finite intersection so that K empty denotes " +
		"Ω, not the whole host type. The empty product is one, matching total probability one.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀J:set(I). ∀F:(I → set(set(A))). " +
			"    independent_sigma_family(Ω, S, μ, J, F) ⇔ " +
			"    probability_on(Ω, S, μ) ∧ " +
			"    (∀i:I. i ∈ J ⇒ sigma_algebra_on(Ω, F(i)) ∧ F(i) ⊆ S) ∧ " +
			"    (∀K:set(I). ∀E:(I → set(A)). " +
			"        finite(K) ∧ K ⊆ J ∧ (∀i:I. i ∈ K ⇒ E(i) ∈ F(i)) ⇒ " +
			"        μ(Ω ∩ ⋂image(E, K)) = extended_of_real(real_product(K, λi:I. extended_to_real(μ(E(i))))))",
	},
})}

// BoolMixtureSigmaDef — `bool_mixture_sigma(Ω, S)` is the σ-algebra on Ω ×
// bool whose members are the sets with both slices in S: the sample space
// of a fair coin tossed beside Ω.
var BoolMixtureSigmaDef = boolMixtureSigmaDefThm{family.Define(registry.DefEntry{
	Name:  "BoolMixtureSigmaDef",
	Key:   "prop_872df9f4a3ce2ebc",
	Const: "bool_mixture_sigma",
	Type:  "set(A) → set(set(A)) → set(set(prod(A, bool)))",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). " +
			"    bool_mixture_sigma(Ω, S) = " +
			"    {E:set(prod(A, bool)) | " +
			"        E ⊆ set_cross(Ω, 𝕌⟨A:bool⟩) ∧ {u:A | (u, ⊤) ∈ E} ∈ S ∧ {u:A | (u, ⊥) ∈ E} ∈ S}",
	},
})}

// BoolMixtureMeasureDef — `bool_mixture_measure(μ)` gives a set on Ω ×
// bool the average of the measures of its two slices: μ under each face
// of a fair coin.
var BoolMixtureMeasureDef = boolMixtureMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "BoolMixtureMeasureDef",
	Key:   "prop_f0bfabd352ed2e0f",
	Const: "bool_mixture_measure",
	Type:  "(set(A) → extended_nonneg_real) → set(prod(A, bool)) → extended_nonneg_real",
	Equations: []string{
		"∀μ:(set(A) → extended_nonneg_real). ∀E:set(prod(A, bool)). " +
			"    bool_mixture_measure(μ, E) = " +
			"    extended_of_real(&1 / &2) * (μ({u:A | (u, ⊥) ∈ E}) + μ({u:A | (u, ⊤) ∈ E}))",
	},
})}

// IndependentVariableFamilyDef — a family of real random variables is
// independent when each is measurable and the σ-algebras they generate
// form an independent family.
var IndependentVariableFamilyDef = independentVariableFamilyDefThm{family.Define(registry.DefEntry{
	Name:  "IndependentVariableFamilyDef",
	Key:   "prop_732158da9d1b6c6a",
	Const: "independent_variable_family",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(I) → " +
		"(I → A → real) → " +
		"bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀J:set(I). ∀X:(I → A → real). " +
			"    independent_variable_family(Ω, S, μ, J, X) ⇔ " +
			"    (∀i:I. i ∈ J ⇒ real_measurable(Ω, S, X(i))) ∧ " +
			"    independent_sigma_family(Ω, " +
			"        S, " +
			"        μ, " +
			"        J, " +
			"        λi:I. pullback_sigma(Ω, X(i), borel_sets(real_topology)))",
	},
	Deps: []registry.EntryLike{IndependentFamilyDef},
})}
