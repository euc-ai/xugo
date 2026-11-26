package measure_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var DiracMeasure = diracMeasureThm{family.Add(registry.ProofEntry{
	Name: "DiracMeasure",
	Key:  "prop_e023a614b32ac1fa",
	Reading: "a ∈ Ω is load-bearing: otherwise Ω has mass 0. No condition on S " +
		"beyond being a σ-algebra on Ω: every set has a definite mass, measurable or not.",
	Deps: []registry.EntryLike{MeasureOn, DiracMeasureDef},
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀a:A.",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)", "a ∈ Ω"},
		Conclusion: "measure_on(Ω, S, dirac_measure(a)) ∧ dirac_measure(a, Ω) = &1",
	},
		"The point mass at a point of Ω is a measure of total mass one, a probability: "+
			"the empty set misses a, a disjoint sequence holds a in at most one of its "+
			"sets, so the series has one term equal to one or none, and Ω holds a."),
})}
