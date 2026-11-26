package central_limit

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/probability/lindeberg_bound"
	"github.com/euc-ai/xugo/library/proofs/probability/weak_convergence"
	"github.com/euc-ai/xugo/library/registry"
)

// MartingaleCentralLimitConditional — the martingale central limit theorem under the conditional
// Lindeberg condition: as MartingaleCentralLimit, with the row sums of the conditional
// Lindeberg terms tending to 0 in measure in place of the Lindeberg sums tending to 0.
var MartingaleCentralLimitConditional = martingaleCentralLimitConditionalThm{family.Add(registry.ProofEntry{
	Name: "MartingaleCentralLimitConditional",
	Key:  "prop_67d88be3afecde69",
	Reading: "w(ε, n, k) is a conditional expectation, given F(n, k), of ξ(n, k)² cut to the " +
		"event ε < |ξ(n, k)|, as v(n, k) is one of ξ(n, k)²; both are given as binders. This is " +
		"the Hall–Heyde and McLeish form. Its hypothesis is weaker than MartingaleCentralLimit's: " +
		"Lindeberg sums tending to 0 make these row sums tend to 0 in mean, and so in measure.",
	Deps: []registry.EntryLike{
		MartingaleCentralLimit,
		lindeberg_bound.LindebergSumDef,
		conditional_expectation.CondExpKnownFactor,
		conditional_expectation.CondExpIntegral,
		integral_convergence.ConvergesInMeasureDef,
		weak_convergence.WeaklyConvergesDef,
		weak_convergence.WeakConvergenceSmoothTests,
	},
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → num → set(set(A))). " +
			"∀K:(num → num). " +
			"∀ξ v:(num → num → A → real). " +
			"∀w:(real → num → num → A → real).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"∀n:num. martingale_difference_row(Ω, S, μ, F(n), K(n), ξ(n), v(n))",
			"converges_in_measure(Ω, " +
				"    μ, " +
				"    λn:num. λx:A. real_sum({k:num | k < K(n)}, λk:num. v(n, k, x)), " +
				"    λx:A. &1)",
			"∀ε:real. ∀n k:num. " +
				"    &0 < ε ∧ k < K(n) ⇒ " +
				"    is_cond_exp(Ω, " +
				"        S, " +
				"        μ, " +
				"        F(n, k), " +
				"        λx:A. COND(ε < |ξ(n, k, x)|, ξ(n, k, x) * ξ(n, k, x), &0), " +
				"        w(ε, n, k))",
			"∀ε:real. " +
				"    &0 < ε ⇒ " +
				"    converges_in_measure(Ω, " +
				"        μ, " +
				"        λn:num. λx:A. real_sum({k:num | k < K(n)}, λk:num. w(ε, n, k, x)), " +
				"        λx:A. &0)",
		},
		Conclusion: "weakly_converges(real_topology, " +
			"    λn:num. pushforward_measure(Ω, μ, λx:A. real_sum({k:num | k < K(n)}, λk:num. ξ(n, k, x))), " +
			"    normal_distribution(&0, &1))",
	},
		"MartingaleCentralLimit applied to the rows stopped predictably where the conditional Lindeberg "+
			"clock passes δ_n, with ε_n, δ_n → 0 slowly. The hypothesis at ε = 1/m for every m gives such "+
			"ε_n, δ_n with μ{Σ_k w(ε_n, n, k) > δ_n} → 0. Keep ξ(n, k) where Σ_{j ≤ k} w(ε_n, n, j) ≤ δ_n: "+
			"the event is in F(n, k), so the kept terms are again martingale differences, with the kept "+
			"v(n, k) as conditional variances (conditional_expectation.CondExpKnownFactor at the event's "+
			"indicator). For ε ≥ ε_n the kept rows' Lindeberg sum at ε is at most the one at ε_n, which is "+
			"the expectation of the kept w(ε_n, n, k) (conditional_expectation.CondExpIntegral, "+
			"lindeberg_bound.LindebergSumDef), at most δ_n; so the kept rows satisfy the Lindeberg "+
			"condition. Off the event where the clock passes δ_n the kept rows are the given ones, and that "+
			"event's measure tends to 0: the kept conditional variances still sum to 1 in measure "+
			"(integral_convergence.ConvergesInMeasureDef), and a test D(0) bounded by B moves the row sums' "+
			"expectations by at most 2B times that measure, so the given row sums have the kept ones' weak "+
			"limit (weak_convergence.WeaklyConvergesDef, WeakConvergenceSmoothTests)."),
})}
