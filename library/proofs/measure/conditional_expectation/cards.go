package conditional_expectation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var CondExpContraction = condExpContractionThm{family.Add(registry.ProofEntry{
	Name: "CondExpContraction",
	Deps: []registry.EntryLike{
		event_integral.EventIntegralCarrier,
		event_integral.EventIntegralUnion,
		event_integral.EventIntegralEqOn,
		event_integral.EventIntegralNeg,
		event_integral.EventIntegralMono,
	},
	Key: "prop_93b347dea73b9573",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y:(A → real).",
		Hypotheses: []string{"is_cond_exp(Ω, S, μ, G, X, Y)"},
		Conclusion: "measure_integral(Ω, S, μ, λx:A. |Y(x)|) ≤ measure_integral(Ω, S, μ, λx:A. |X(x)|)",
	},
		"Split into the G-measurable sets where Y is positive and nonpositive. Use the defining "+
			"event identities on each part and compare the signed X with its absolute value."),
})}

var CondExpTower = condExpTowerThm{family.Add(registry.ProofEntry{
	Name: "CondExpTower",
	Key:  "prop_76848e9e678a4477",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀H:set(set(A)). " +
			"∀X Y Z:(A → real).",
		Hypotheses: []string{"is_cond_exp(Ω, S, μ, G, X, Y)", "is_cond_exp(Ω, S, μ, H, Y, Z)", "H ⊆ G"},
		Conclusion: "is_cond_exp(Ω, S, μ, H, X, Z)",
	}, "Each H-event is a G-event, so the two event-integral identities compose."),
})}

var CondExpAE = condExpAEThm{family.Add(registry.ProofEntry{
	Name:    "CondExpAE",
	Reading: "The separate measurability hypotheses are needed because S is not complete.",
	Deps:    []registry.EntryLike{event_integral.EventIntegralAE, measure_integral.IntegrableAE},
	Key:     "prop_313d5e5bc507aa93",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y U V:(A → real).",
		Hypotheses: []string{
			"is_cond_exp(Ω, S, μ, G, X, Y)",
			"real_measurable(Ω, S, U)",
			"real_measurable(Ω, G, V)",
			"measure_ae_eq(Ω, S, μ, X, U)",
			"measure_ae_eq(Ω, S, μ, Y, V)",
		},
		Conclusion: "is_cond_exp(Ω, S, μ, G, U, V)",
	},
		"A.e. invariance preserves integrability and every event integral; "+
			"the replacement output is separately assumed G-measurable."),
})}
