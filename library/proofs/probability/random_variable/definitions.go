package random_variable

import (
	"github.com/euc-ai/xugo/library/registry"
)

// IdenticallyDistributedDef — two real random variables on one space are
// identically distributed when their distributions give every Borel set
// the same mass.
var IdenticallyDistributedDef = identicallyDistributedDefThm{family.Define(registry.DefEntry{
	Name:  "IdenticallyDistributedDef",
	Key:   "prop_7607c27b89e40dd6",
	Const: "identically_distributed",
	Type:  "set(A) → (set(A) → extended_nonneg_real) → (A → real) → (A → real) → bool",
	Reading: "The two distributions are compared on the Borel sets only: as functions on every set " +
		"of reals they may differ where a preimage is not an event. No σ-algebra and no measurability is " +
		"asked here: a statement that uses it supplies that the variables are measurable.",
	Equations: []string{
		"∀Ω:set(A). ∀μ:(set(A) → extended_nonneg_real). ∀X Y:(A → real). " +
			"    identically_distributed(Ω, μ, X, Y) ⇔ " +
			"    (∀E:set(real). " +
			"        E ∈ borel_sets(real_topology) ⇒ " +
			"        pushforward_measure(Ω, μ, X, E) = pushforward_measure(Ω, μ, Y, E))",
	},
})}
