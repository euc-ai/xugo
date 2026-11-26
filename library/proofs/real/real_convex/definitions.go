// definitions.go — the chapter's definitional layer: what it means for a
// real function to be convex on a set.

package real_convex

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealConvexOnDef — `real_convex_on(s, f)`: between any two points of s
// the graph of f lies on or below the chord joining their values. The
// point t·x + (1 − t)·y need not lie in s; on an interval it always does.
var RealConvexOnDef = realConvexOnDefThm{family.Define(registry.DefEntry{
	Name:  "RealConvexOnDef",
	Key:   "prop_2fe4bfc98cbf8e9",
	Const: "real_convex_on",
	Type:  "set(real) → (real → real) → bool",
	Equations: []string{
		"∀s:set(real). ∀f:real → real. " +
			"    real_convex_on(s, f) ⇔ " +
			"    ∀x y t:real. " +
			"        x ∈ s ∧ y ∈ s ∧ &0 ≤ t ∧ t ≤ &1 ⇒ f(t * x + (&1 - t) * y) ≤ t * f(x) + (&1 - t) * f(y)",
	},
})}
