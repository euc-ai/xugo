// records.go — the free simplicial module on a simplicial set, as one
// value.

package simplicial_module

import "github.com/euc-ai/xugo/library/registry"

// FreeSimplicialModuleDef — `free_simplicial_module(R, X)`: the finitely
// supported chains on the simplices of X, the faces and degeneracies
// pushed forward along those of X.
var FreeSimplicialModuleDef = freeSimplicialModuleDefThm{family.Define(registry.DefEntry{
	Name:  "FreeSimplicialModuleDef",
	Key:   "prop_44d7aa1ff50d86f1",
	Const: "free_simplicial_module",
	Type:  "ring_ops(A) → simplicial_ops(D) → simplicial_ops(D → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀X:simplicial_ops(D). " +
			"    free_simplicial_module(R, X) = " +
			"    mk_simplicial(simplicial_chains(R.zero, X, R.carrier), " +
			"        λn:num. λi:num. free_pushforward(R, X.d(n, i)), " +
			"        λn:num. λi:num. free_pushforward(R, X.s(n, i)))",
	},
})}
