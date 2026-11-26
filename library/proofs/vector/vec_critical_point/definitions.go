package vec_critical_point

import (
	_ "github.com/euc-ai/xugo/library/proofs/vector/matrix"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// CriticalPointDef — the Jacobian at an n-vector fails to map ℝⁿ onto ℝᵐ.
var CriticalPointDef = criticalPointDefThm{family.Define(registry.DefEntry{
	Name:      "CriticalPointDef",
	Key:       "prop_39bf4f142ccd6bde",
	Const:     "vec_critical_point",
	Type:      "num → num → ((num → real) → (num → real)) → (num → real) → bool",
	Dim:       "n",
	SourceDim: "n",
	TargetDim: "m",
	Equations: []string{
		"∀n m:num. ∀f:((num → real) → (num → real)). ∀x:(num → real). " +
			"    vec_critical_point⟨n, m⟩(f, x) ⇔ " +
			"    vec⟨n⟩(x) ∧ " +
			"    ∃y:(num → real). " +
			"        vec⟨m⟩(y) ∧ " +
			"        ∀v:(num → real). vec⟨n⟩(v) ⇒ matrix_act⟨n⟩(vec_jacobian_matrix⟨n, m⟩(f, x), v) ≠ y",
	},
	Reading: "This is non-surjectivity on the zero-padded carriers, not on the full sequence " +
		"type. The Jacobian uses chosen partial derivatives, so the differential interpretation " +
		"requires differentiability; SmoothSard supplies smoothness on an open domain. With m = 0 " +
		"the Jacobian is onto the one-point target and there are no critical points.",
})}
