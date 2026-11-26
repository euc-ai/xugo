// definitions.go — the chapter's definitional layer: the exponential
// function and the logarithm.
//
// Both are choices. real_exp(x) is the sum of the series Σ xⁿ/n!, chosen
// through the relation `real_sums` because the series chapter mints no
// value for a sum; the series converges for every x (ExpSums), so
// real_exp(x) IS its sum.
// real_log(y) is the x with exp(x) = y; exp takes every positive value
// exactly once (ExpSurjective, ExpInjective), so on the positive reals
// the choice is the one such x, and what it is elsewhere no theorem
// says.
//
// Two idioms recur in the bodies. A property of a choice `εx. P x`
// follows from `∃x. P x`: ExpSums, LogExp and ExpLog unfold the
// constant on their own goal, state the existence, and close on it.
// And the constant is unfolded before any resident fact mentions it,
// because a goal-side Unfold also rewrites every resident fact that
// does (the manual's `Unfold`, "The goal and every hypothesis"); the
// ε-δ definitions (the derivative, the limit, continuity) are opened by
// `Simp(Fwd(<Def>))` instead, which rewrites the goal alone.

package real_exp_log

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealExpDef — `real_exp(x)`: the sum of the series Σ xⁿ/n!.
var RealExpDef = realExpDefThm{family.Define(registry.DefEntry{
	Name:     "RealExpDef",
	Key:      "prop_ea141c9d208553ac",
	Const:    "real_exp",
	Overload: "exp",
	Type:     "real → real",
	Equations: []string{
		"∀x:real. real_exp(x) = εs:real. real_sums(λn:num. real_pow(x, n) / &factorial(n), s)",
	},
	// The mints of the series relation, the power, the quotient, the
	// factorial and the embedding.
})}

// RealLogDef — `real_log(y)`: the x whose exponential is y.
var RealLogDef = realLogDefThm{family.Define(registry.DefEntry{
	Name:      "RealLogDef",
	Key:       "prop_6182343bb29c9e60",
	Const:     "real_log",
	Overload:  "log",
	Type:      "real → real",
	Equations: []string{"∀y:real. real_log(y) = εx:real. exp(x) = y"},
	Deps:      []registry.EntryLike{RealExpDef},
})}
