package definable_andre_quillen

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/simplicial_ring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/registry"
)

// AQTopologiesDef — Discrete coefficient values on the standard resolution names in each degree.
var AQTopologiesDef = aQTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "AQTopologiesDef",
	Key:   "prop_7d3a1f55e28eadb",
	Const: "aq_topologies",
	Type:  "ring_ops(A) → ring_ops(B) → module_ops(B, C) → num → set(set(U → C))",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:ring_ops(B). ∀N:module_ops(B, C). " +
			"    aq_topologies(R, S, N) = dual_pointwise_topologies(N, standard_names⟨A:A, B:B, U:U⟩(R, S))",
	},
	Reading: "Discrete coefficient values on the standard resolution names in each degree.",
})}
