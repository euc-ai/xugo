// definitions.go — the partial derivative as a function, the functions of
// class Cᵏ and the smooth functions on a set of ℝⁿ, smooth maps and
// diffeomorphisms, the Jacobian matrix and its determinant, and support
// in a compact set.

package vec_smooth

import (
	_ "github.com/euc-ai/xugo/library/proofs/real/real_topology"
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/continuous"
	_ "github.com/euc-ai/xugo/library/proofs/vector/determinant"
	_ "github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_derivative"
	"github.com/euc-ai/xugo/library/registry"
)

// PartialDerivativeDef — `partial_derivative(f, j, c)`: the partial
// derivative of the real function f on ℝⁿ at c along coordinate j, the d
// of `partial_derivative_at(f, j, c, d)`. Applied to f and j alone it is
// the partial derivative as a function, ∂ⱼf.
var PartialDerivativeDef = partialDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "PartialDerivativeDef",
	Key:   "prop_51ba02f2b3479e23",
	Const: "partial_derivative",
	Type:  "((num → real) → real) → num → (num → real) → real",
	Equations: []string{
		"∀f:((num → real) → real). ∀j:num. ∀c:(num → real). " +
			"    partial_derivative(f, j, c) = εd:real. partial_derivative_at(f, j, c, d)",
	},
	Reading: "Where f has no partial derivative at c along j the value is an unspecified " +
		"real; a statement that reads it asks for the derivative first, or for a class that has it.",
})}

// ContinuouslyDifferentiableOnDef — `vec_continuously_differentiable_on⟨n⟩(U, k, g)`:
// the real function g on ℝⁿ is of class Cᵏ on U. Class 0 is continuity at
// every point of U; class k + 1 is continuity, a partial derivative along
// every coordinate at every point of U, and each partial derivative of
// class k on U.
var ContinuouslyDifferentiableOnDef = continuouslyDifferentiableOnDefThm{family.Define(registry.DefEntry{
	Name:  "ContinuouslyDifferentiableOnDef",
	Key:   "prop_6938b2a5740cbd1d",
	Const: "vec_continuously_differentiable_on",
	Type:  "num → ((num → real) → bool) → num → ((num → real) → real) → bool",
	Dim:   "n",
	Equations: []string{
		"∀n:num. ∀U:set(num → real). ∀g:((num → real) → real). " +
			"    vec_continuously_differentiable_on⟨n⟩(U, 0, g) ⇔ " +
			"    ∀x:(num → real). x ∈ U ⇒ continuous_map_at(euclidean_topology(n), real_topology, g, x)",
		"∀n:num. ∀U:set(num → real). ∀k:num. ∀g:((num → real) → real). " +
			"    vec_continuously_differentiable_on⟨n⟩(U, suc(k), g) ⇔ " +
			"    (∀x:(num → real). x ∈ U ⇒ continuous_map_at(euclidean_topology(n), real_topology, g, x)) ∧ " +
			"    ∀j:num. " +
			"        j < n ⇒ " +
			"        (∀x:(num → real). x ∈ U ⇒ ∃d:real. partial_derivative_at(g, j, x, d)) ∧ " +
			"        vec_continuously_differentiable_on⟨n⟩(U, k, partial_derivative(g, j))",
	},
	Reading: "Continuity at x is asked of g on ℝⁿ, so every class makes U a " +
		"set of n-vectors. The partial derivatives are those of g on ℝⁿ, read on " +
		"lines through the points of U: on a set that is not open they see values of " +
		"g off U, and the statements of the chapter take U open where that matters.",
})}

// SmoothOnDef — `vec_smooth_on⟨n⟩(U, g)`: the real function g on ℝⁿ is
// smooth on U, of class Cᵏ there for every k.
var SmoothOnDef = smoothOnDefThm{family.Define(registry.DefEntry{
	Name:  "SmoothOnDef",
	Key:   "prop_9fec7bc5f6fe0c89",
	Const: "vec_smooth_on",
	Type:  "num → ((num → real) → bool) → ((num → real) → real) → bool",
	Dim:   "n",
	Equations: []string{
		"∀n:num. ∀U:((num → real) → bool). ∀g:((num → real) → real). " +
			"    vec_smooth_on⟨n⟩(U, g) ⇔ ∀k:num. vec_continuously_differentiable_on⟨n⟩(U, k, g)",
	},
})}

// SmoothMapOnDef — `vec_smooth_map_on⟨n, m⟩(U, f)`: the map f carries U
// into ℝᵐ and each of its m coordinates is smooth on U.
var SmoothMapOnDef = smoothMapOnDefThm{family.Define(registry.DefEntry{
	Name:      "SmoothMapOnDef",
	Key:       "prop_c8f66ff97dbfc5cb",
	Const:     "vec_smooth_map_on",
	Type:      "num → num → ((num → real) → bool) → ((num → real) → (num → real)) → bool",
	Dim:       "n",
	SourceDim: "n",
	TargetDim: "m",
	Equations: []string{"∀n m:num. ∀U:set(num → real). ∀f:((num → real) → (num → real)). " +
		"    vec_smooth_map_on⟨n, m⟩(U, f) ⇔ " +
		"    (∀x:(num → real). x ∈ U ⇒ vec⟨m⟩(f(x))) ∧ " +
		"    ∀i:num. i < m ⇒ vec_smooth_on⟨n⟩(U, λx:(num → real). f(x)(i))"},
})}

// DiffeomorphicMapDef — `vec_diffeomorphic_map⟨n⟩(U, V, f)`: f is a
// smooth bijection of U onto V whose inverse is smooth on V.
var DiffeomorphicMapDef = diffeomorphicMapDefThm{family.Define(registry.DefEntry{
	Name:  "DiffeomorphicMapDef",
	Key:   "prop_3907d14cd15ebc18",
	Const: "vec_diffeomorphic_map",
	Type: "num → " +
		"((num → real) → bool) → " +
		"((num → real) → bool) → " +
		"((num → real) → (num → real)) → " +
		"bool",
	Dim:       "n",
	SourceDim: "n",
	TargetDim: "n",
	Equations: []string{"∀n:num. ∀U V:set(num → real). ∀f:((num → real) → (num → real)). " +
		"    vec_diffeomorphic_map⟨n⟩(U, V, f) ⇔ " +
		"    vec_smooth_map_on⟨n, n⟩(U, f) ∧ " +
		"    (∀x:(num → real). x ∈ U ⇒ f(x) ∈ V) ∧ " +
		"    ∃g:((num → real) → (num → real)). " +
		"        vec_smooth_map_on⟨n, n⟩(V, g) ∧ " +
		"        (∀y:(num → real). y ∈ V ⇒ g(y) ∈ U ∧ f(g(y)) = y) ∧ " +
		"        ∀x:(num → real). x ∈ U ⇒ g(f(x)) = x"},
	Reading: "Said of open sets U and V; on others the smoothness " +
		"asked is that of the definition's class on a set that is not open.",
})}

// JacobianMatrixDef — `vec_jacobian_matrix⟨n, m⟩(f, x)`: the m × n
// matrix of the partial derivatives at x of f's coordinates, the entry
// (i, j) being ∂ⱼfᵢ(x), and 0 outside i < m, j < n.
var JacobianMatrixDef = jacobianMatrixDefThm{family.Define(registry.DefEntry{
	Name:      "JacobianMatrixDef",
	Key:       "prop_26bfd175b1f3defa",
	Const:     "vec_jacobian_matrix",
	Type:      "num → num → ((num → real) → (num → real)) → (num → real) → num → num → real",
	Dim:       "n",
	SourceDim: "n",
	TargetDim: "m",
	Equations: []string{"∀n m:num. ∀f:((num → real) → (num → real)). ∀x:(num → real). ∀i j:num. " +
		"    vec_jacobian_matrix⟨n, m⟩(f, x, i, j) = " +
		"    COND(i < m ∧ j < n, partial_derivative(λy:(num → real). f(y)(i), j, x), &0)"},
})}

// JacobianDeterminantDef — `vec_jacobian_determinant⟨n⟩(f, x)`: the
// determinant of the n × n Jacobian matrix of f at x.
var JacobianDeterminantDef = jacobianDeterminantDefThm{family.Define(registry.DefEntry{
	Name:      "JacobianDeterminantDef",
	Key:       "prop_b8ab1d667d1f2543",
	Const:     "vec_jacobian_determinant",
	Type:      "num → ((num → real) → (num → real)) → (num → real) → real",
	Dim:       "n",
	SourceDim: "n",
	TargetDim: "n",
	Equations: []string{"∀n:num. ∀f:((num → real) → (num → real)). ∀x:(num → real). " +
		"    vec_jacobian_determinant⟨n⟩(f, x) = " +
		"    determinant(real_ring, n, vec_jacobian_matrix⟨n, n⟩(f, x))"},
})}

// CompactlySupportedInDef — `vec_compactly_supported_in⟨n⟩(U, g)`: the
// real function g on ℝⁿ vanishes at every n-vector off some compact subset
// of U.
var CompactlySupportedInDef = compactlySupportedInDefThm{family.Define(registry.DefEntry{
	Name:  "CompactlySupportedInDef",
	Key:   "prop_5395e60f58e62290",
	Const: "vec_compactly_supported_in",
	Type:  "num → ((num → real) → bool) → ((num → real) → real) → bool",
	Dim:   "n",
	Equations: []string{"∀n:num. ∀U:set(num → real). ∀g:((num → real) → real). " +
		"    vec_compactly_supported_in⟨n⟩(U, g) ⇔ " +
		"    ∃K:set(num → real). " +
		"        compact_in(euclidean_topology(n), K) ∧ " +
		"        K ⊆ U ∧ " +
		"        ∀x:(num → real). vec⟨n⟩(x) ∧ x ∉ K ⇒ g(x) = &0"},
	Reading: "Values of g away from the n-vectors are not read. With U the whole of ℝⁿ it says " +
		"g has compact support; the zero function has it in every U, the empty set being compact.",
})}
