// records.go — the nerve of a category as one simplicial set.

package nerve

import "github.com/euc-ai/xugo/library/registry"

// NerveDef — `nerve(C)`: the chains of C with their faces and
// degeneracies, one simplicial set.
var NerveDef = nerveDefThm{family.Define(registry.DefEntry{
	Name:  "NerveDef",
	Key:   "prop_dd8acc4bef70e2e8",
	Const: "nerve",
	Type:  "category_ops(A, M) → simplicial_ops(num → M)",
	Equations: []string{
		"∀C:category_ops(A, M). " +
			"    nerve(C) = mk_simplicial(nerve_simplices(C), nerve_face(C), λn:num. nerve_degeneracy(C))",
	},
	Deps: []registry.EntryLike{NerveSimplicesDef, NerveFaceDef, NerveDegeneracyDef},
})}
