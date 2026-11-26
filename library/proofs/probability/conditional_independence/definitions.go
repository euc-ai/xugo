// definitions.go — conditional independence of two σ-algebras given a
// third, in Doob's form: every version of the conditional expectation of
// an indicator given the condition is also a version given the
// condition joined with the other side.

package conditional_independence

import (
	"github.com/euc-ai/xugo/library/registry"
)

// CondIndependentSigmaDef — `cond_independent_sigma(Ω, S, μ, G, H, K)`,
// G and H independent given K: μ is a probability, G, H and K are
// sub-σ-algebras of S, and for every E ∈ G every version of the
// conditional expectation of the indicator of E given K is a version
// given σ(K ∪ H). The definition is an implication between two relation
// facts, so no choice of version enters; the structure hypotheses sit
// inside it, as in `independent_sigma`, since with an infinite measure
// the indicator need not be integrable and the implication would hold
// vacuously.
var CondIndependentSigmaDef = condIndependentSigmaDefThm{family.Define(registry.DefEntry{
	Name:  "CondIndependentSigmaDef",
	Key:   "prop_3b5f7dea6f9c48ff",
	Const: "cond_independent_sigma",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(set(A)) → " +
		"set(set(A)) → " +
		"set(set(A)) → " +
		"bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G H K:set(set(A)). " +
			"    cond_independent_sigma(Ω, S, μ, G, H, K) ⇔ " +
			"    probability_on(Ω, S, μ) ∧ " +
			"    sigma_algebra_on(Ω, G) ∧ " +
			"    sigma_algebra_on(Ω, H) ∧ " +
			"    sigma_algebra_on(Ω, K) ∧ " +
			"    G ⊆ S ∧ " +
			"    H ⊆ S ∧ " +
			"    K ⊆ S ∧ " +
			"    (∀E:set(A). ∀Y:(A → real). " +
			"        E ∈ G ∧ is_cond_exp(Ω, S, μ, K, λx:A. COND(x ∈ E, &1, &0), Y) ⇒ " +
			"        is_cond_exp(Ω, S, μ, generated_sigma(Ω, K ∪ H), λx:A. COND(x ∈ E, &1, &0), Y))",
	},
})}
