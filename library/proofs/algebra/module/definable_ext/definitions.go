package definable_ext

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/tor_ext"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	"github.com/euc-ai/xugo/library/registry"
)

// extTopologiesDef — The canonical resolution fixes the generator carrier; coefficients carry the discrete topology.
var extTopologiesDef = extTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "extTopologiesDef",
	Key:   "prop_49cfa3198a5df3e9",
	Const: "ext_topologies",
	Type: "ring_ops(A) → " +
		"module_ops(A, B) → " +
		"module_ops(A, C) → " +
		"num → " +
		"set(set(set(prod(num, prod(A, B))) → C))",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀N:module_ops(A, C). " +
			"    ext_topologies(R, M, N) = dual_pointwise_topologies(N, canonical_resolution_terms(R, M))",
	},
	Reading: "The canonical resolution fixes the generator " +
		"carrier; coefficients carry the discrete topology.",
})}
