// definitions.go — the derivative of a map from ℝⁿ to ℝᵐ at a point, its
// continuity there, and the partial derivative of a real function on ℝⁿ
// along a coordinate.

package vec_derivative

import (
	_ "github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/registry"
)

// VecDerivativeAtDef — `vec_derivative_at⟨n, m⟩(f, c, L)`: the map f has
// the linear map L as its derivative at the point c of ℝⁿ, the increment
// f(x) − f(c) lying within ε·‖x − c‖ of L(x − c) near c. L carries ℝⁿ
// into ℝᵐ; only the first m coordinates of f's values are read.
var VecDerivativeAtDef = vecDerivativeAtDefThm{family.Define(registry.DefEntry{
	Name:  "VecDerivativeAtDef",
	Key:   "prop_1fdb157d1dc2a730",
	Const: "vec_derivative_at",
	Type: "num → " +
		"num → " +
		"((num → real) → (num → real)) → " +
		"(num → real) → " +
		"((num → real) → (num → real)) → " +
		"bool",
	Dim:       "n",
	SourceDim: "n",
	TargetDim: "m",
	Equations: []string{
		"∀n m:num. ∀f:((num → real) → (num → real)). ∀c:(num → real). ∀L:((num → real) → (num → real)). " +
			"    vec_derivative_at⟨n, m⟩(f, c, L) ⇔ " +
			"    vec⟨n⟩(c) ∧ " +
			"    vec_linear(L) ∧ " +
			"    (∀u:(num → real). vec⟨n⟩(u) ⇒ vec⟨m⟩(L(u))) ∧ " +
			"    ∀ε:real. " +
			"        &0 < ε ⇒ " +
			"        ∃δ:real. " +
			"            &0 < δ ∧ " +
			"            ∀x:(num → real). " +
			"                vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ ‖f(x) - f(c) - L(x - c)‖_m ≤ ε * ‖x - c‖_n",
	},
})}

// VecContinuousAtDef — `vec_continuous_at⟨n, m⟩(f, c)`: the map f is
// continuous at the point c of ℝⁿ, its values at the n-vectors near c
// lying within ε of f(c) in ℝᵐ. Only the first m coordinates of f's
// values are read, as by the derivative.
var VecContinuousAtDef = vecContinuousAtDefThm{family.Define(registry.DefEntry{
	Name:      "VecContinuousAtDef",
	Key:       "prop_ad6281e325a761a9",
	Const:     "vec_continuous_at",
	Type:      "num → num → ((num → real) → (num → real)) → (num → real) → bool",
	Dim:       "n",
	SourceDim: "n",
	TargetDim: "m",
	Equations: []string{"∀n m:num. ∀f:((num → real) → (num → real)). ∀c:(num → real). " +
		"    vec_continuous_at⟨n, m⟩(f, c) ⇔ " +
		"    vec⟨n⟩(c) ∧ " +
		"    ∀ε:real. " +
		"        &0 < ε ⇒ " +
		"        ∃δ:real. &0 < δ ∧ ∀x:(num → real). vec⟨n⟩(x) ∧ ‖x - c‖_n < δ ⇒ ‖f(x) - f(c)‖_m < ε"},
})}

// PartialDerivativeAtDef — `partial_derivative_at(f, j, c, d)`: the real
// function f on ℝⁿ has partial derivative d at c along coordinate j, the
// derivative at 0 of t ↦ f(c + t·e_j).
var PartialDerivativeAtDef = partialDerivativeAtDefThm{family.Define(registry.DefEntry{
	Name:  "PartialDerivativeAtDef",
	Key:   "prop_292aa9c91ffd710c",
	Const: "partial_derivative_at",
	Type:  "((num → real) → real) → num → (num → real) → real → bool",
	Equations: []string{
		"∀f:((num → real) → real). ∀j:num. ∀c:(num → real). ∀d:real. " +
			"    partial_derivative_at(f, j, c, d) ⇔ " +
			"    real_derivative_at(λt:real. f(c + t • basis_vector(j)), &0, d)",
	},
})}

// VecInverseOnDef — `vec_inverse_on⟨n⟩(L, K)`: K is a linear map of ℝⁿ
// into itself that undoes L on ℝⁿ and is undone by it.
var VecInverseOnDef = vecInverseOnDefThm{family.Define(registry.DefEntry{
	Name:      "VecInverseOnDef",
	Key:       "prop_48a17dd6e4743866",
	Const:     "vec_inverse_on",
	Type:      "num → ((num → real) → (num → real)) → ((num → real) → (num → real)) → bool",
	SourceDim: "n",
	TargetDim: "n",
	Equations: []string{
		"∀n:num. ∀L K:((num → real) → (num → real)). " +
			"    vec_inverse_on⟨n⟩(L, K) ⇔ " +
			"    vec_linear(K) ∧ ∀h:(num → real). vec⟨n⟩(h) ⇒ vec⟨n⟩(K(h)) ∧ K(L(h)) = h ∧ L(K(h)) = h",
	},
})}
