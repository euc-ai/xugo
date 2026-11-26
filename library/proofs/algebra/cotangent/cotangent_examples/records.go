// records.go — the Koszul simplicial algebra as one simplicial set.

package cotangent_examples

import "github.com/euc-ai/xugo/library/registry"

// koszulSimplicialSetDef — `koszul_simplicial_set(R, g)`: the free
// algebras on the Koszul names, with the Koszul faces at g and the
// degeneracies.
var koszulSimplicialSetDef = koszulSimplicialSetDefThm{family.Define(registry.DefEntry{
	Name:  "koszulSimplicialSetDef",
	Key:   "prop_1572659956c685ca",
	Const: "koszul_simplicial_set",
	Type:  "ring_ops(A) → A → simplicial_ops(U)",
	Equations: []string{
		"∀R:ring_ops(A). ∀g:A. " +
			"    koszul_simplicial_set(R, g) = " +
			"    mk_simplicial(λn:num. universe_algebra(R, koszul_names(n)), " +
			"        koszul_face(R, g), " +
			"        λn:num. koszul_degeneracy(R))",
	},
	Deps: []registry.EntryLike{koszulNamesDef, koszulFaceDef, koszulDegeneracyDef},
})}
