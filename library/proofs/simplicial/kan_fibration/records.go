// records.go — the fibre of a simplicial map as one simplicial set.

package kan_fibration

import "github.com/euc-ai/xugo/library/registry"

// SimplicialFiberDef — `simplicial_fiber(X, Y, p, y₀)`: the simplices of
// X over the base simplex at y₀, with the operators of X.
var SimplicialFiberDef = simplicialFiberDefThm{family.Define(registry.DefEntry{
	Name:     "SimplicialFiberDef",
	Key:      "prop_7614912ad75d951d",
	Const:    "simplicial_fiber",
	Type:     "simplicial_ops(A) → simplicial_ops(B) → (num → A → B) → B → simplicial_ops(A)",
	Implicit: []string{"X", "Y"},
	Equations: []string{
		"∀X:simplicial_ops(A). ∀Y:simplicial_ops(B). ∀p:(num → A → B). ∀y₀:B. " +
			"    simplicial_fiber(X, Y, p, y₀) = " +
			"    restrict_simplicial_set(X, simplicial_fiber_simplices(X, Y, p, y₀))",
	},
	Deps: []registry.EntryLike{simplicialFiberSimplicesDef},
})}
