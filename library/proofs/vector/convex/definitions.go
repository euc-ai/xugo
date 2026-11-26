// definitions.go — the chapter's definitional layer: what it is for a
// set of vectors to be convex.
//
// A convex set contains, with any two of its points, every weighted
// average of them: the weights are nonnegative and total one, and the
// average is taken in the module. Nothing about a dimension appears —
// convexity reads no active range, so the subject is a set of sequences
// and not a set of n-vectors, and the chapter's theorems hold for every
// dimension at once.
//
// The two weights are written out rather than parameterized as `t` and
// `1 - t`: the symmetric form is what a fold's recursion step produces,
// where a new point's weight and the total weight of the rest arrive as
// two numbers with no subtraction between them. The one-parameter test
// is the equivalent form, and it is a theorem here (`Segment`).

package convex

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ConvexDef — convexity: every weighted average of two points of the
// set, at nonnegative weights totalling one, is again a point of the
// set.
//
// The equation writes the module's operations by their notation, as
// every theorem of the chapter does: under the family's instance
// binding `c • x` is `vec_scalar_mul(real_mul, c, x)` and the `+` between two
// such is `vec_add(real_add, …)`, which is why those two definitions are
// deps.
var ConvexDef = convexDefThm{family.Define(registry.DefEntry{
	Name:  "ConvexDef",
	Key:   "prop_a2533d64d7f255fe",
	Const: "convex",
	Type:  "set(num → real) → bool",
	Equations: []string{
		"∀s:set(num → real). " +
			"    convex(s) ⇔ " +
			"    (∀x y:(num → real). ∀c d:real. " +
			"        x ∈ s ∧ y ∈ s ∧ &0 ≤ c ∧ &0 ≤ d ∧ c + d = &1 ⇒ c • x + d • y ∈ s)",
	},
})}
