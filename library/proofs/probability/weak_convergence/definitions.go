// definitions.go — weak convergence of probability measures on the Borel
// sets of a topology.

package weak_convergence

import (
	"github.com/euc-ai/xugo/library/registry"
)

// WeaklyConvergesDef — `weakly_converges(T, ν, ρ)`: the ν(n) and ρ are
// probability measures on the Borel sets of T, and the integral of every
// bounded continuous real function against ν(n) tends to its integral
// against ρ.
var WeaklyConvergesDef = weaklyConvergesDefThm{family.Define(registry.DefEntry{
	Name:  "WeaklyConvergesDef",
	Key:   "prop_37c39fb2b49c491e",
	Const: "weakly_converges",
	Type: "set(set(A)) → " +
		"(num → set(A) → extended_nonneg_real) → " +
		"(set(A) → extended_nonneg_real) → " +
		"bool",
	Reading: "T is not asked to be a topology: the Borel sets of any family " +
		"of sets are a σ-algebra on its union. A bounded continuous function is " +
		"Borel measurable and integrable against a probability, so no integral " +
		"here reads its default. The measures are read on the Borel sets only.",
	Equations: []string{
		"∀T:set(set(A)). ∀ν:(num → set(A) → extended_nonneg_real). ∀ρ:(set(A) → extended_nonneg_real). " +
			"    weakly_converges(T, ν, ρ) ⇔ " +
			"    (∀n:num. probability_on(⋃T, borel_sets(T), ν(n))) ∧ " +
			"    probability_on(⋃T, borel_sets(T), ρ) ∧ " +
			"    (∀f:(A → real). " +
			"        continuous_map(T, real_topology, f) ∧ (∃B:real. ∀x:A. x ∈ ⋃T ⇒ |f(x)| ≤ B) ⇒ " +
			"        (λn:num. measure_integral(⋃T, borel_sets(T), ν(n), f)) ⟶ " +
			"        measure_integral(⋃T, borel_sets(T), ρ, f))",
	},
})}
