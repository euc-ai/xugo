// A tangent vector is a compatible family of chart components at a
// fixed base point, zero on every chart that is not active there.

package tangent

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/vector/matrix"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// TangentVectorDef — chart components with Jacobian compatibility.
var TangentVectorDef = tangentVectorDefThm{family.Define(registry.DefEntry{
	Name:  "TangentVectorDef",
	Key:   "prop_4ff493c5747c25d3",
	Const: "tangent_vector_on",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"A → " +
		"(prod(set(A), A → num → real) → num → real) → " +
		"bool",
	Dim: "n",
	Reading: "The base point must lie in the manifold carrier. Each component is a padded " +
		"n-vector; incompatible charts and compatible charts not containing the point have zero " +
		"component. Normalization makes equality literal equality of functions on all chart pairs.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real). " +
			"    tangent_vector_on⟨n⟩(T, 𝒜, x, v) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    x ∈ ⋃T ∧ " +
			"    (∀c:prod(set(A), A → num → real). vec⟨n⟩(v(c))) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ¬«active»(c) ⇒ v(c) = (λi:num. &0)) ∧ " +
			"    (∀c d:prod(set(A), A → num → real). " +
			"        «active»(c) ∧ «active»(d) ⇒ " +
			"        v(d) = matrix_act⟨n⟩(vec_jacobian_matrix⟨n, n⟩(«transition»(c, d), snd(c)(x)), v(c)))",
	},
})}

// TangentFromChartDef — propagate a vector from one chart using the
// transition Jacobians, with zero components on inactive charts.
var TangentFromChartDef = tangentFromChartDefThm{family.Define(registry.DefEntry{
	Name:  "TangentFromChartDef",
	Key:   "prop_453c217719c191bc",
	Const: "tangent_from_chart",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(set(A), A → num → real) → " +
		"A → " +
		"(num → real) → " +
		"prod(set(A), A → num → real) → " +
		"num → " +
		"real",
	Dim: "n",
	Reading: "The constructor is zero unless its source chart and the output chart both " +
		"contain x and are compatible, and u is a padded n-vector. Its fiber laws require a manifold " +
		"and an active source chart; no chosen inverse is used away from a chart image in those laws.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀u:(num → real). " +
			"∀d:prod(set(A), A → num → real). " +
			"    tangent_from_chart⟨n⟩(T, 𝒜, c, x, u, d) = " +
			"    COND(«active»(c) ∧ «active»(d) ∧ vec⟨n⟩(u), " +
			"        matrix_act⟨n⟩(vec_jacobian_matrix⟨n, n⟩(«transition»(c, d), snd(c)(x)), u), " +
			"        λi:num. &0)",
	},
})}

// TangentModuleDef — the fiber inside the module of all chart families.
var TangentModuleDef = tangentModuleDefThm{family.Define(registry.DefEntry{
	Name:  "TangentModuleDef",
	Key:   "prop_c3f7d7d0743ec1f0",
	Const: "tangent_module",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"A → " +
		"module_ops(real, prod(set(A), A → num → real) → num → real)",
	Dim:  "n",
	Deps: []registry.EntryLike{TangentVectorDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀x:A. " +
			"    tangent_module⟨n⟩(T, 𝒜, x) = " +
			"    restrict_module(function_module(«Euclidean module», 𝕌⟨A:prod(set(A), A → num → real)⟩), " +
			"        {v:(prod(set(A), A → num → real) → num → real) | tangent_vector_on⟨n⟩(T, 𝒜, x, v)})",
	},
})}

// TangentBundleDef — a point of TM retains both its base and its vector.
var TangentBundleDef = tangentBundleDefThm{family.Define(registry.DefEntry{
	Name:  "TangentBundleDef",
	Key:   "prop_d6efbeabbba1ae6c",
	Const: "tangent_bundle",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(A, prod(set(A), A → num → real) → num → real))",
	Dim:  "n",
	Deps: []registry.EntryLike{TangentVectorDef},
	Reading: "Zero tangent vectors at different base points are the same " +
		"component function, but the corresponding pairs in the total space " +
		"are distinct. No points lie over points outside the manifold carrier.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    tangent_bundle⟨n⟩(T, 𝒜) = " +
			"    {p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"        tangent_vector_on⟨n⟩(T, 𝒜, fst(p), snd(p))}",
	},
})}
