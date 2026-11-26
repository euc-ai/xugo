// definitions.go — the chapter's definitional layer: the Euclidean norm
// and the distance it induces, at ℝ, and the operator norm of a map.
//
// Everything below the norm is the generic chapters read at the real
// ring: `dot⟨n⟩(real_add, real_mul, u, v)` is the fold of `u(i) · v(i)`
// over the active range. What ℝ adds is an order, and with it the
// square root: `vec_norm⟨n⟩(u)` is the root of the dot product of u with
// itself, which the chapter proves nonnegative.

package euclidean

import (
	"github.com/euc-ai/xugo/library/registry"
)

// VecNormDef — the Euclidean norm in dimension n.
var VecNormDef = vecNormDefThm{family.Define(registry.DefEntry{
	Name:     "VecNormDef",
	Key:      "prop_abfa09b4d33774d",
	Const:    "vec_norm",
	Type:     "num → (num → real) → real",
	Notation: "‖u‖_n",
	Dim:      "n",
	Equations: []string{
		"∀n:num. ∀u:(num → real). vec_norm⟨n⟩(u) = real_sqrt(dot⟨n⟩(real_add, real_mul, u, u))",
	},
})}

// VecDistDef — the Euclidean distance: the norm of the difference.
var VecDistDef = vecDistDefThm{family.Define(registry.DefEntry{
	Name:     "VecDistDef",
	Key:      "prop_e166b14c07d0fe1d",
	Const:    "vec_dist",
	Type:     "num → (num → real) → (num → real) → real",
	Overload: "dist",
	Dim:      "n",
	Equations: []string{
		"∀n:num. ∀u v:(num → real). vec_dist⟨n⟩(u, v) = vec_norm⟨n⟩(vec_sub(real_sub, u, v))",
	},
	Deps: []registry.EntryLike{VecNormDef},
})}

// VecOpNormDef — `vec_op_norm⟨n, m⟩(L)`, the operator norm: the supremum
// of the sizes in ℝᵐ of L's images of the n-vectors of norm at most 1.
// For a linear L that set holds ‖L(vec_zero)‖ and is bounded by the total
// size of L's images of the basis (LinearBasisEstimate), so the value is
// the least nonnegative B with ‖L(h)‖_m ≤ B·‖h‖_n on ℝⁿ
// (OpNormLessEqIff); for a map that stretches the unit ball unboundedly
// it is the supremum's unspecified value, and no law here speaks of it.
var VecOpNormDef = vecOpNormDefThm{family.Define(registry.DefEntry{
	Name:      "VecOpNormDef",
	Key:       "prop_ccd8e5e2042e2dd8",
	Const:     "vec_op_norm",
	Type:      "num → num → ((num → real) → (num → real)) → real",
	SourceDim: "n",
	TargetDim: "m",
	Equations: []string{
		"∀n m:num. ∀L:((num → real) → (num → real)). " +
			"    vec_op_norm⟨n, m⟩(L) = sup({‖L(u)‖_m | u:(num → real) | vec⟨n⟩(u) ∧ ‖u‖_n ≤ &1})",
	},
	Deps: []registry.EntryLike{VecNormDef},
})}
