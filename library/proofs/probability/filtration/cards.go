package filtration

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

var NaturalFiltration = naturalFiltrationThm{family.Add(registry.ProofEntry{
	Name: "NaturalFiltration",
	Deps: []registry.EntryLike{
		sigma_algebra.GeneratedSigmaAlgebra,
		sigma_algebra.GeneratedSigmaLeast,
		measurable_space.MeasurableGenerated,
	},
	Key: "prop_c3f4f48d5959775b",
	Build: family.Card(Statement{Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀X:(num → A → real).",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)", "∀n:num. real_measurable(Ω, S, X(n))"},
		Conclusion: "filtration_on(Ω, S, natural_filtration(Ω, X)) ∧ " +
			"adapted_process(Ω, natural_filtration(Ω, X), X)"},
		"The generators are ambient-measurable. Enlarging the time enlarges the "+
			"generating family, and the time-n inverse images are themselves generators."),
})}
