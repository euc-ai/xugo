// cards.go — negation of the integral over an event.

package event_integral

import (
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var EventIntegralNeg = eventIntegralNegThm{family.Add(registry.ProofEntry{
	Name:    "EventIntegralNeg",
	Key:     "prop_1e74ffd7ba698c25",
	Reading: "No structure is asked of Ω, S or μ, and no integrability.",
	Deps:    []registry.EntryLike{measure_integral.IntegralNeg},
	Build: family.Card("∀Ω:set(A). "+
		"∀S:set(set(A)). "+
		"∀μ:(set(A) → extended_nonneg_real). "+
		"∀E:set(A). "+
		"∀f:(A → real). "+
		"    event_integral(Ω, S, μ, E, λx:A. -f(x)) = -event_integral(Ω, S, μ, E, f)",
		"The cut of −f to E is the negative of the cut of f, "+
			"since −0 = 0; negating a function negates its integral."),
})}
