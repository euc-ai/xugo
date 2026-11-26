// definitions.go — the reduced label of a point of Kuhn's grid.
//
// A labelling assigns each point and each coordinate a truth value; Kuhn's
// 0 and 1 are ⊥ and ⊤.

package kuhn_labelling

import (
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// kuhnReducedDef — `kuhn_reduced(n, l, x)`: how many of the labels
// l(x, 0), l(x, 1), … are ⊥ before the first ⊤, at most n. It takes the
// n + 1 values 0, …, n, as many as an n-simplex has vertices.
var kuhnReducedDef = kuhnReducedDefThm{family.Define(registry.DefEntry{
	Name:  "kuhnReducedDef",
	Key:   "prop_55295dc674638ed1",
	Const: "kuhn_reduced",
	Type:  "num → ((num → num) → num → bool) → (num → num) → num",
	Equations: []string{
		"∀n:num. ∀l:((num → num) → num → bool). ∀x:(num → num). " +
			"    kuhn_reduced(n, l, x) = card({k:num | k < n ∧ ∀j:num. j ≤ k ⇒ ¬l(x, j)})",
	},
})}
