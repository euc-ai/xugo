package field_norm

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_determinant"
	"github.com/euc-ai/xugo/library/registry"
)

var FieldNormDef = fieldNormDefThm{family.Define(registry.DefEntry{
	Name:  "FieldNormDef",
	Key:   "prop_6986a30933a06fff",
	Deps:  []registry.EntryLike{},
	Const: "field_norm",
	Type:  "ring_ops(A) → set(A) → A → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀K:set(A). ∀a:A. " +
			"    field_norm(R, K, a) = module_determinant(restrict_ring(R, K), regular_module(R), R.mul(a))",
	},
})}
