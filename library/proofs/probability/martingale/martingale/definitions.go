package martingale

import (
	"github.com/euc-ai/xugo/library/registry"
)

var MartingaleDef = martingaleDefThm{family.Define(registry.DefEntry{
	Name: "MartingaleDef",
	Reading: "This definition permits arbitrary measure spaces. Its " +
		"conditional-expectation clauses supply measure structure, integrability and " +
		"adaptedness. The optional-stopping theorems hold on any measure space; finiteness " +
		"of the measure enters only where an L2 limit or a constant must be integrable.",
	Key:   "prop_93ba7b516311de44",
	Const: "martingale_on",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(num → set(set(A))) → " +
		"(num → A → real) → " +
		"bool",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"    martingale_on(Ω, S, μ, F, M) ⇔ " +
			"    filtration_on(Ω, S, F) ∧ (∀n:num. is_cond_exp(Ω, S, μ, F(n), M(n + 1), M(n)))",
	},
})}

var SupermartingaleDef = supermartingaleDefThm{family.Define(registry.DefEntry{
	Name:  "SupermartingaleDef",
	Key:   "prop_d115dabf844f5ddf",
	Const: "supermartingale_on",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(num → set(set(A))) → " +
		"(num → A → real) → " +
		"bool",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"    supermartingale_on(Ω, S, μ, F, M) ⇔ " +
			"    measure_on(Ω, S, μ) ∧ " +
			"    filtration_on(Ω, S, F) ∧ " +
			"    adapted_process(Ω, F, M) ∧ " +
			"    (∀n:num. real_integrable(Ω, S, μ, M(n))) ∧ " +
			"    (∀n:num. ∀E:set(A). " +
			"        E ∈ F(n) ⇒ event_integral(Ω, S, μ, E, M(n + 1)) ≤ event_integral(Ω, S, μ, E, M(n)))",
	},
})}

var MartingaleTransformDef = martingaleTransformDefThm{family.Define(registry.DefEntry{
	Name:  "MartingaleTransformDef",
	Key:   "prop_21d269cfd42cdc8e",
	Const: "martingale_transform",
	Type:  "(num → A → real) → (num → A → real) → num → A → real",
	Reading: "H(i) multiplies the increment from i to i+1 and is measurable " +
		"at time i. The half-open index set makes the time-zero sum empty.",
	Equations: []string{
		"∀M H:(num → A → real). ∀n:num. ∀x:A. " +
			"    martingale_transform(M, H, n, x) = " +
			"    M(0, x) + real_sum({i:num | i < n}, λi:num. H(i, x) * (M(i + 1, x) - M(i, x)))",
	},
})}

// MartingaleDifferenceRowDef — `martingale_difference_row(Ω, S, μ, F, n, ξ, v)`:
// ξ(0), …, ξ(n − 1) are martingale differences along the filtration F, ξ(k)
// known at time k + 1 and centred given time k, and v(k) is the conditional
// variance of ξ(k) given time k.
var MartingaleDifferenceRowDef = martingaleDifferenceRowDefThm{family.Define(registry.DefEntry{
	Name:  "MartingaleDifferenceRowDef",
	Key:   "prop_3e9aca522a779e03",
	Const: "martingale_difference_row",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(num → set(set(A))) → " +
		"num → " +
		"(num → A → real) → " +
		"(num → A → real) → " +
		"bool",
	Reading: "Nothing is asked of ξ(k) or v(k) for k ≥ n. The " +
		"conditional-expectation clauses carry the measure, the integrability " +
		"of ξ(k) and of its square, and the F(k)-measurability of v(k).",
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀n:num. " +
			"∀ξ v:(num → A → real). " +
			"    martingale_difference_row(Ω, S, μ, F, n, ξ, v) ⇔ " +
			"    filtration_on(Ω, S, F) ∧ " +
			"    (∀k:num. " +
			"        k < n ⇒ " +
			"        real_measurable(Ω, F(k + 1), ξ(k)) ∧ " +
			"        is_cond_exp(Ω, S, μ, F(k), ξ(k), λx:A. &0) ∧ " +
			"        is_cond_exp(Ω, S, μ, F(k), λx:A. ξ(k, x) * ξ(k, x), v(k)))",
	},
})}
