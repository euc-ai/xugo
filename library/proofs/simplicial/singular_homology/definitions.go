// definitions.go — the singular chain complex of a space with
// coefficients in a ring: the free modules on the singular simplices,
// with the alternating sum of the faces for boundary. It is the chain
// complex simplicial_chain builds on any simplicial set, read at the
// singular one, so its homology is the space's singular homology.

package singular_homology

import (
	"github.com/euc-ai/xugo/library/registry"
)

// SingularComplexDef — `singular_complex(R, T)`: the singular chains of the
// space with coefficients in R.
var SingularComplexDef = singularComplexDefThm{family.Define(registry.DefEntry{
	Name:  "SingularComplexDef",
	Key:   "prop_38b82497bd27e632",
	Const: "singular_complex",
	Type:  "ring_ops(A) → set(set(D)) → complex_ops(A, ((num → real) → D) → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀T:set(set(D)). " +
			"    singular_complex(R, T) = " +
			"    free_complex(R, " +
			"        singular_set(T).simplices, " +
			"        simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, singular_set(T).d))",
	},
})}
