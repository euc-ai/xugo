// records.go — the left mapping complex between two vertices as one
// simplicial set.

package mapping_complex

import "github.com/euc-ai/xugo/library/registry"

// MappingComplexDef — `mapping_complex(X, x, y)`: the mapping simplices
// from x to y with the operators of X past vertex 0.
var MappingComplexDef = mappingComplexDefThm{family.Define(registry.DefEntry{
	Name:  "MappingComplexDef",
	Key:   "prop_cd80646ef1d24650",
	Const: "mapping_complex",
	Type:  "simplicial_ops(A) → A → A → simplicial_ops(A)",
	Equations: []string{
		"∀X:simplicial_ops(A). ∀x y:A. " +
			"    mapping_complex(X, x, y) = " +
			"    mk_simplicial(mapping_complex_simplices(X, x, y), " +
			"        mapping_complex_face(X.d), " +
			"        mapping_complex_degeneracy(X.s))",
	},
	Deps: []registry.EntryLike{
		mappingComplexSimplicesDef,
		mappingComplexFaceDef,
		mappingComplexDegeneracyDef,
	},
})}
