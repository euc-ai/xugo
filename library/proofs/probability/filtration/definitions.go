package filtration

import (
	"github.com/euc-ai/xugo/library/registry"
)

var FiltrationDef = filtrationDefThm{family.Define(registry.DefEntry{
	Name:  "FiltrationDef",
	Key:   "prop_df9c46f30dad23e9",
	Const: "filtration_on",
	Type:  "set(A) → set(set(A)) → (num → set(set(A))) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). " +
			"    filtration_on(Ω, S, F) ⇔ " +
			"    sigma_algebra_on(Ω, S) ∧ (∀n:num. sigma_algebra_on(Ω, F(n)) ∧ F(n) ⊆ S ∧ F(n) ⊆ F(n + 1))",
	},
})}

var AdaptedDef = adaptedDefThm{family.Define(registry.DefEntry{
	Name:  "AdaptedDef",
	Key:   "prop_5f1a6104546fe514",
	Const: "adapted_process",
	Type:  "set(A) → (num → set(set(A))) → (num → A → real) → bool",
	Equations: []string{
		"∀Ω:set(A). ∀F:(num → set(set(A))). ∀X:(num → A → real). " +
			"    adapted_process(Ω, F, X) ⇔ ∀n:num. real_measurable(Ω, F(n), X(n))",
	},
})}

// NaturalFiltrationDef — the natural filtration of a process at time n
// is the σ-algebra its values up to n generate.
var NaturalFiltrationDef = naturalFiltrationDefThm{family.Define(registry.DefEntry{
	Name:  "NaturalFiltrationDef",
	Key:   "prop_1a46e9f9ec65a52c",
	Const: "natural_filtration",
	Type:  "set(A) → (num → A → real) → num → set(set(A))",
	Equations: []string{
		"∀Ω:set(A). ∀X:(num → A → real). ∀n:num. " +
			"    natural_filtration(Ω, X, n) = " +
			"    sigma_join(Ω, λk:num. pullback_sigma(Ω, X(k), borel_sets(real_topology)), {k:num | k ≤ n})",
	},
})}

var LimitSigmaDef = limitSigmaDefThm{family.Define(registry.DefEntry{
	Name:  "LimitSigmaDef",
	Key:   "prop_49c498afab3f92d5",
	Const: "filtration_limit_sigma",
	Type:  "set(A) → (num → set(set(A))) → set(set(A))",
	Equations: []string{
		"∀Ω:set(A). ∀F:(num → set(set(A))). " +
			"    filtration_limit_sigma(Ω, F) = generated_sigma(Ω, ⋃image(F, 𝕌))",
	},
})}
