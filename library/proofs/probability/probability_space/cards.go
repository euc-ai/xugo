package probability_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/registry"
)

var FiniteWeightedProbability = finiteWeightedProbabilityThm{family.Add(registry.ProofEntry{
	Name: "FiniteWeightedProbability",
	Reading: "Nonnegative weights on Ω are load-bearing: " +
		"extended_of_real clamps a negative weight to zero.",
	Deps: []registry.EntryLike{
		measure_space.DiscreteMeasure,
		integral_convergence.FiniteDiscreteIntegral,
	},
	Key: "prop_28a5d1e5b5760134",
	Build: family.Card(Statement{Binders: "∀Ω:set(A). ∀w:(A → real).",
		Hypotheses: []string{"finite(Ω)", "∀x:A. x ∈ Ω ⇒ &0 ≤ w(x)", "real_sum(Ω, w) = &1"},
		Conclusion: "probability_on(Ω, " +
			"    {D:set(A) | D ⊆ Ω}, " +
			"    discrete_measure(Ω, λx:A. extended_of_real(w(x)))) ∧ " +
			"(∀X:(A → real). " +
			"    real_integrable(Ω, " +
			"        {D:set(A) | D ⊆ Ω}, " +
			"        discrete_measure(Ω, λx:A. extended_of_real(w(x))), " +
			"        X) ∧ " +
			"    expectation(Ω, {D:set(A) | D ⊆ Ω}, discrete_measure(Ω, λx:A. extended_of_real(w(x))), X) = " +
			"    real_sum(Ω, λx:A. w(x) * X(x)))"},
		"The discrete measure of the weights is a measure (DiscreteMeasure) "+
			"of mass Σ w = 1 on Ω, so a probability; FiniteDiscreteIntegral "+
			"gives the integrability and the integral, which is the expectation."),
})}

var UniformProbability = uniformProbabilityThm{family.Add(registry.ProofEntry{
	Name: "UniformProbability",
	Key:  "prop_b6ae3d47bea3316c",
	Reading: "Ω ≠ ∅ is load-bearing: on the empty set the mass is 0. So is finite(Ω): a constant " +
		"weight on an infinite set has mass 0 or ∞. Every subset of Ω is an event. E ⊆ Ω is " +
		"load-bearing in the value clause: the measure reads only Ω ∩ E, while card counts all of E.",
	Deps: []registry.EntryLike{UniformMeasureDef, ProbabilityOnDef, measure_space.DiscreteMeasure},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A).",
		Hypotheses: []string{
			"finite(Ω)",
			"Ω ≠ ∅",
		},
		Conclusion: "probability_on(Ω, {D:set(A) | D ⊆ Ω}, uniform_measure(Ω)) ∧ " +
			"(∀E:set(A). E ⊆ Ω ⇒ uniform_measure(Ω, E) = extended_of_real(&(card(E)) / &(card(Ω))))",
	},
		"The uniform law on a finite nonempty set. The discrete measure of constant weight 1/card(Ω) is "+
			"a measure on all subsets (DiscreteMeasure). On a subset E of the finite Ω the supremum of its "+
			"finite partial sums is attained at E itself, a sum of card(E) equal weights; at E = Ω it is 1."),
})}
