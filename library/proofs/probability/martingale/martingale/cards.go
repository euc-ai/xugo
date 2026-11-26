package martingale

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/probability/stopping_time"
	"github.com/euc-ai/xugo/library/registry"
)

var MartingaleConditional = martingaleConditionalThm{family.Add(registry.ProofEntry{
	Name: "MartingaleConditional",
	Deps: []registry.EntryLike{
		conditional_expectation.CondExpTower,
		conditional_expectation.CondExpIdentity,
		filtration.FiltrationMono,
	},
	Key: "prop_b40ccdb69661d53a",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"∀m n:num.",
		Hypotheses: []string{"martingale_on(Ω, S, μ, F, M)", "m ≤ n"},
		Conclusion: "is_cond_exp(Ω, S, μ, F(m), M(n), M(m))",
	},
		"Iterate the tower property across consecutive times; at "+
			"equal times use adaptedness and the identity relation."),
})}

var StoppedMartingale = stoppedMartingaleThm{family.Add(registry.ProofEntry{
	Name: "StoppedMartingale",
	Deps: []registry.EntryLike{MartingaleTransform, stopping_time.StoppedIncrement},
	Key:  "prop_ccd10cc356d20923",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"∀T:(A → option(num)).",
		Hypotheses: []string{"martingale_on(Ω, S, μ, F, M)", "stopping_time_on(Ω, F, T)"},
		Conclusion: "martingale_on(Ω, S, μ, F, stopped_process(M, T))",
	},
		"Apply the martingale transform with coefficient the "+
			"indicator of T>n and the stopped-increment identity."),
})}

var StoppedSupermartingale = stoppedSupermartingaleThm{family.Add(registry.ProofEntry{
	Name: "StoppedSupermartingale",
	Deps: []registry.EntryLike{
		stopping_time.StoppedIncrement,
		stopping_time.StoppedValueMeasurable,
		event_integral.EventIntegralUnion,
		event_integral.EventIntegralEqOn,
		event_integral.EventIntegralSub,
	},
	Key: "prop_c81a8acf26e83d7a",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"∀T:(A → option(num)).",
		Hypotheses: []string{"supermartingale_on(Ω, S, μ, F, M)", "stopping_time_on(Ω, F, T)"},
		Conclusion: "supermartingale_on(Ω, S, μ, F, stopped_process(M, T))",
	},
		"Split a time-n event into T≤n and T>n. The stopped increment vanishes on the "+
			"first part and the original supermartingale inequality applies on the second."),
})}
