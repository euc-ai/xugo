package caratheodory

import (
	"github.com/euc-ai/xugo/library/registry"
)

var CaratheodorySetsDef = caratheodorySetsDefThm{family.Define(registry.DefEntry{
	Name:  "CaratheodorySetsDef",
	Key:   "prop_d1465aec417cdd9b",
	Const: "caratheodory_sets",
	Type:  "set(A) → (set(A) → extended_nonneg_real) → set(set(A))",
	Equations: []string{
		"∀Ω:set(A). ∀μ:(set(A) → extended_nonneg_real). " +
			"    caratheodory_sets(Ω, μ) = {s:set(A) | s ⊆ Ω ∧ ∀t:set(A). t ⊆ Ω ⇒ μ(t) = μ(t ∩ s) + μ(t ∖ s)}",
	},
})}
