// definitions.go — the chapter's definitional layer: what it means for
// a function to tend to a number at a point. The definition is the ε-δ
// one and nothing more; README.md says why the relation is minted and
// no value operator beside it.
//
// Two engine facts shape every ε-δ body in the chapter. Unfolding the
// goal's `real_limit_at` (or `real_converges_to`) also unfolds every
// resident hypothesis that mentions it, and leaves the closure's
// hypothesis Fact without a successor, so whatever a proof needs from
// its hypothesis — its ε-δ statement, `a.Unfolded(h, RealLimitAtDef)`,
// a fact cited from it — is stated BEFORE the goal is unfolded (the
// manual's `Unfold`, "The goal and every hypothesis"). And a witness
// Obtained from an ∃w. A ∧ B — a radius with its positivity, an ε with
// the balls that fail it — arrives as one conjunction, so its ∀ half
// is restated on its own before it is applied at a point.

package real_function_limits

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealLimitAtDef — `f ⟶ l (at c)`: every positive distance around l is met
// by the values on some punctured ball around c.
var RealLimitAtDef = realLimitAtDefThm{family.Define(registry.DefEntry{
	Name:     "RealLimitAtDef",
	Key:      "prop_1d13849f6468653e",
	Const:    "real_limit_at",
	Type:     "(real → real) → real → real → bool",
	Notation: "f ⟶ l (at c)",
	Equations: []string{
		"∀f:(real → real). ∀c l:real. " +
			"    real_limit_at(f, c, l) ⇔ " +
			"    ∀ε:real. &0 < ε ⇒ ∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < ε",
	},
	// The mints of the four constants the definiens spells: `<`,
	// real_abs, `-` and the embedding `&`.
})}
