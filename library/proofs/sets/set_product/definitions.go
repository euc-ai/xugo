// definitions.go — the chapter's definitional layer: the product of two
// sets, the set of pairs with a component in each, and the diagonal of a
// set, the pairs of a point with itself. The pair type and its projections
// are cartesian/pairs'.

package set_product

import (
	"github.com/euc-ai/xugo/library/registry"
)

// SetCrossDef — `set_cross(s, t)`: the pairs whose first component lies in
// s and whose second lies in t.
var SetCrossDef = setCrossDefThm{family.Define(registry.DefEntry{
	Name:  "SetCrossDef",
	Key:   "prop_821ad0284884e6d8",
	Const: "set_cross",
	Type:  "set(A) → set(B) → set(prod(A, B))",
	Equations: []string{
		"∀s:set(A). ∀t:set(B). set_cross(s, t) = {(x, y) | x:A, y:B | x ∈ s ∧ y ∈ t}",
	},
})}

// SetDiagonalDef — `set_diagonal(s)`: the pairs (x, x) with x in s, a
// subset of set_cross(s, s) (DiagonalSubsetCross).
var SetDiagonalDef = setDiagonalDefThm{family.Define(registry.DefEntry{
	Name:  "SetDiagonalDef",
	Key:   "prop_b7e3478f7add5373",
	Const: "set_diagonal",
	Type:  "set(A) → set(prod(A, A))",
	Equations: []string{
		"∀s:set(A). set_diagonal(s) = {(x, x) | x:A | x ∈ s}",
	},
})}
