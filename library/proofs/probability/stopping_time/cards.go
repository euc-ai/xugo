package stopping_time

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

var FirstEntranceStopping = firstEntranceStoppingThm{family.Add(registry.ProofEntry{
	Name: "FirstEntranceStopping",
	Deps: []registry.EntryLike{filtration.FiltrationMono, sigma_algebra.SigmaFiniteOperations},
	Key:  "prop_906cd3b589d2404a",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀M:(num → A → real). ∀B:set(real).",
		Hypotheses: []string{
			"filtration_on(Ω, S, F)",
			"adapted_process(Ω, F, M)",
			"B ∈ borel_sets(real_topology)",
		},
		Conclusion: "stopping_time_on(Ω, F, first_entrance(B, M))",
	}, "The event of a visit by n is the finite union of the events M(k) in B for k ≤ n."),
})}

var StoppedSigmaMono = stoppedSigmaMonoThm{family.Add(registry.ProofEntry{
	Name: "StoppedSigmaMono",
	Deps: []registry.EntryLike{sigma_algebra.SigmaFiniteOperations},
	Key:  "prop_564a3790429c27c9",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀T U:(A → option(num)).",
		Hypotheses: []string{
			"filtration_on(Ω, S, F)",
			"stopping_time_on(Ω, F, T)",
			"stopping_time_on(Ω, F, U)",
			"∀x:A. x ∈ Ω ⇒ stopping_time_le(T(x), U(x))",
		},
		Conclusion: "stopped_sigma(Ω, S, F, T) ⊆ stopped_sigma(Ω, S, F, U)",
	}, "Intersect an event observable at T with {U ≤ n}, a subset of {T ≤ n}."),
})}
