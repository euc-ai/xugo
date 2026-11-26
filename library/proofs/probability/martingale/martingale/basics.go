// basics.go — what a martingale carries: an adapted integrable process on a
// measure space with a filtration.

package martingale

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/registry"
)

// MartingaleAdaptedIntegrable — a martingale is an adapted integrable process
// on a measure space: each consecutive conditional-expectation relation carries
// the measure, the measurability of M(n) at time n and the integrability of M(n).
var MartingaleAdaptedIntegrable = martingaleAdaptedIntegrableThm{family.Add(registry.ProofEntry{
	Name: "MartingaleAdaptedIntegrable",
	Key:  "prop_3c482442edc25272",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real).",
		Hypotheses: []string{"martingale_on(Ω, S, μ, F, M)"},
		Conclusion: "measure_on(Ω, S, μ) ∧ " +
			"filtration_on(Ω, S, F) ∧ " +
			"adapted_process(Ω, F, M) ∧ " +
			"(∀n:num. real_integrable(Ω, S, μ, M(n)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		F *Arrow2[Nat, Set[A], Bool],
		M *Arrow2[Nat, A, Real],
		h Fact,
	) {
		conditional := a.Unfolded(h, MartingaleDef)
		data := a.Unfolded(conditional, conditional_expectation.IsCondExpDef)
		a.Show(
			"the conditional expectation clauses give the measure, adaptedness and integrability",
			By(data, filtration.AdaptedDef.At(Ω, F, M)))
	}),
})}
