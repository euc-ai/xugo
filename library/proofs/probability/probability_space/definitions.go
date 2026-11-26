package probability_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

var ProbabilityOnDef = probabilityOnDefThm{family.Define(registry.DefEntry{
	Name:  "ProbabilityOnDef",
	Key:   "prop_fc7591ce5379a3db",
	Const: "probability_on",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). " +
			"    probability_on(Ω, S, μ) ⇔ measure_on(Ω, S, μ) ∧ μ(Ω) = &1",
	},
})}

var ExpectationDef = expectationDefThm{family.Define(registry.DefEntry{
	Name:  "ExpectationDef",
	Key:   "prop_c4bb790fa6b7de0c",
	Const: "expectation",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → (A → real) → real",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀X:(A → real). " +
			"    expectation(Ω, S, μ, X) = measure_integral(Ω, S, μ, X)",
	},
})}

// CondProbDef — `cond_prob(μ, E, D)` is the probability of E given the
// event D, P(E ∩ D) / P(D), as a real number. Real division is total, so
// a null D gives 0; an identity between conditional probabilities still
// carries the positivity of its denominators as a hypothesis.
var CondProbDef = condProbDefThm{family.Define(registry.DefEntry{
	Name:  "CondProbDef",
	Key:   "prop_f7626273e73355d8",
	Const: "cond_prob",
	Type:  "(set(A) → extended_nonneg_real) → set(A) → set(A) → real",
	Equations: []string{
		"∀μ:(set(A) → extended_nonneg_real). ∀E D:set(A). " +
			"    cond_prob(μ, E, D) = extended_to_real(μ(E ∩ D)) / extended_to_real(μ(D))",
	},
})}

// VarianceDef — `variance(Ω, S, μ, X)` is the expectation of the squared
// distance of X from its expectation.
var VarianceDef = varianceDefThm{family.Define(registry.DefEntry{
	Name:  "VarianceDef",
	Key:   "prop_55047ed80d43a337",
	Const: "variance",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → (A → real) → real",
	Reading: "The integral is total: where the squared distance is not " +
		"integrable its nonnegative integral is infinite and the variance reads 0, so " +
		"a statement about a variance asks the square of the variable to be integrable.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀X:(A → real). " +
			"    variance(Ω, S, μ, X) = " +
			"    expectation(Ω, " +
			"        S, " +
			"        μ, " +
			"        λx:A. (X(x) - expectation(Ω, S, μ, X)) * (X(x) - expectation(Ω, S, μ, X)))",
	},
	Deps: []registry.EntryLike{ExpectationDef},
})}

// UniformMeasureDef — `uniform_measure(Ω)` is the discrete measure on Ω of constant
// weight 1/card(Ω): on a finite nonempty Ω, the uniform probability.
var UniformMeasureDef = uniformMeasureDefThm{family.Define(registry.DefEntry{
	Name:  "UniformMeasureDef",
	Key:   "prop_b771906b4ce895a4",
	Const: "uniform_measure",
	Type:  "set(A) → set(A) → extended_nonneg_real",
	Equations: []string{
		"∀Ω:set(A). uniform_measure(Ω) = discrete_measure(Ω, λu:A. extended_of_real(&1 / &(card(Ω))))",
	},
})}
