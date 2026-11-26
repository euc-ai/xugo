// jacobian.go — the Jacobian: the matrix of partial derivatives acts as
// the derivative, the Jacobian of a composite is the product of the
// Jacobians, and its determinant multiplies along composites. A
// diffeomorphism has an inverse that is one, composites of them are
// diffeomorphisms, and their Jacobian determinant has no zero; a smooth
// map whose Jacobian determinant is not zero at a point is a
// diffeomorphism near it, the inverse function theorem.

package vec_smooth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/inverse_function"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_derivative"
	"github.com/euc-ai/xugo/library/registry"
)

// JacobianDerivative — the Jacobian matrix of a map of class C¹ acts as its
// derivative.
var JacobianDerivative = jacobianDerivativeThm{family.Add(registry.ProofEntry{
	Name: "JacobianDerivative",
	Key:  "prop_add7d48a3a43984d",
	Reading: "Only the first m coordinates of f are read, by both sides; " +
		"U open gives the ball about x on which the partial derivatives exist.",
	Deps: []registry.EntryLike{
		JacobianMatrixDef,
		vec_derivative.ContinuousPartialsDerivative,
		PartialDerivativeValue,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. ∀U:((num → real) → bool). ∀f:((num → real) → num → real). ∀x:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"∀i:num. i < m ⇒ vec_continuously_differentiable_on⟨n⟩(U, 1, λy:(num → real). f(y)(i))",
			"x ∈ U",
		},
		Conclusion: "vec_derivative_at⟨n, m⟩(f, x, matrix_act⟨n⟩(vec_jacobian_matrix⟨n, m⟩(f, x)))",
	},
		"vec_derivative.ContinuousPartialsDerivative on a ball about x inside U, "+
			"with D(y)(i)(j) = ∂ⱼfᵢ(y) (PartialDerivativeValue); the map it builds, "+
			"u ↦ (⟪D(x)(i), u⟫_n for i < m, 0 after), is the Jacobian matrix acting"),
})}

// JacobianChain — the Jacobian matrix of a composite of smooth maps is the
// product of their Jacobian matrices.
var JacobianChain = jacobianChainThm{family.Add(registry.ProofEntry{
	Name: "JacobianChain",
	Key:  "prop_b83779250ca77923",
	Deps: []registry.EntryLike{
		JacobianMatrixDef,
		PartialDerivativeChain,
		PartialDerivativeValue,
		matrix.MatrixMulDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀U V:((num → real) → bool). " +
			"∀f h:((num → real) → num → real). " +
			"∀x:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(m)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀y:(num → real). y ∈ U ⇒ f(y) ∈ V",
			"vec_smooth_map_on⟨m, k⟩(V, h)",
			"x ∈ U",
		},
		Conclusion: "vec_jacobian_matrix⟨n, k⟩(h ∘ f, x) = " +
			"matrix_mul(m, vec_jacobian_matrix⟨m, k⟩(h, f(x)), vec_jacobian_matrix⟨n, m⟩(f, x))",
	},
		"entrywise: for l < k and j < n, PartialDerivativeChain at the coordinate hₗ gives "+
			"∂ⱼ(hₗ ∘ f)(x) = Σ_{i<m} ∂ᵢhₗ(f(x))·∂ⱼfᵢ(x), the dot product of row l and column j "+
			"(matrix.MatrixMulDef); outside that range both sides are 0, a zero row or a zero column"),
})}

// JacobianDeterminantChain — the Jacobian determinant of a composite is
// the product of the Jacobian determinants.
var JacobianDeterminantChain = jacobianDeterminantChainThm{family.Add(registry.ProofEntry{
	Name: "JacobianDeterminantChain",
	Key:  "prop_f293dd1deb22203a",
	Deps: []registry.EntryLike{
		JacobianDeterminantDef,
		JacobianChain,
		matrix.MatrixProductAgrees,
		determinant.DeterminantMultiplicative,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀U V:((num → real) → bool). " +
			"∀f h:((num → real) → num → real). " +
			"∀x:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(n)",
			"vec_smooth_map_on⟨n, n⟩(U, f)",
			"∀y:(num → real). y ∈ U ⇒ f(y) ∈ V",
			"vec_smooth_map_on⟨n, n⟩(V, h)",
			"x ∈ U",
		},
		Conclusion: "vec_jacobian_determinant⟨n⟩(h ∘ f, x) = " +
			"vec_jacobian_determinant⟨n⟩(h, f(x)) * vec_jacobian_determinant⟨n⟩(f, x)",
	},
		"JacobianChain, matrix_mul read as matrix_product at real_ring (matrix.MatrixProductAgrees, "+
			"whose carrier is all of ℝ), and determinant.DeterminantMultiplicative, the Jacobian "+
			"matrices being n × n matrices over real_ring"),
})}

// DiffeomorphismJacobianNonzero — the Jacobian determinant of a
// diffeomorphism has no zero.
var DiffeomorphismJacobianNonzero = diffeomorphismJacobianNonzeroThm{family.Add(registry.ProofEntry{
	Name: "DiffeomorphismJacobianNonzero",
	Key:  "prop_2d341a1d02982195",
	Deps: []registry.EntryLike{
		DiffeomorphicMapDef,
		JacobianDeterminantChain,
		LinearSmoothMap,
		PartialDerivativeLocal,
		determinant.DeterminantIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U V:((num → real) → bool). ∀f:((num → real) → num → real). ∀x:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(n)",
			"vec_diffeomorphic_map⟨n⟩(U, V, f)",
			"x ∈ U",
		},
		Conclusion: "vec_jacobian_determinant⟨n⟩(f, x) ≠ &0",
	},
		"with g the smooth inverse, g ∘ f is the identity on the open U, so its Jacobian at "+
			"x is the identity's (PartialDerivativeLocal, LinearSmoothMap at the identity map), "+
			"of determinant 1 (determinant.DeterminantIdentity); JacobianDeterminantChain "+
			"writes that 1 as a product with the Jacobian determinant of f at x as a factor"),
})}

// DiffeomorphismInverse — the inverse of a diffeomorphism is a
// diffeomorphism.
var DiffeomorphismInverse = diffeomorphismInverseThm{family.Add(registry.ProofEntry{
	Name: "DiffeomorphismInverse",
	Key:  "prop_79698e75216953cc",
	Deps: []registry.EntryLike{DiffeomorphicMapDef},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U V:((num → real) → bool). ∀f:((num → real) → num → real).",
		Hypotheses: []string{
			"vec_diffeomorphic_map⟨n⟩(U, V, f)",
		},
		Conclusion: "∃g:((num → real) → num → real). " +
			"    vec_diffeomorphic_map⟨n⟩(V, U, g) ∧ " +
			"    (∀x:(num → real). x ∈ U ⇒ g(f(x)) = x) ∧ " +
			"    ∀y:(num → real). y ∈ V ⇒ f(g(y)) = y",
	},
		"the inverse g the definition supplies, with f for its own inverse"),
})}

// SmoothInverseFunction — the inverse function theorem: a smooth map is a
// diffeomorphism near a point where its Jacobian determinant is not zero.
var SmoothInverseFunction = smoothInverseFunctionThm{family.Add(registry.ProofEntry{
	Name: "SmoothInverseFunction",
	Key:  "prop_6502d9680c09cad6",
	Deps: []registry.EntryLike{
		inverse_function.InverseFunction,
		JacobianDerivative,
		vec_derivative.PartialFromDerivative,
		determinant.DeterminantZeroIffDependent,
		SmoothReciprocal,
		ContinuouslyDifferentiableCompose,
		DiffeomorphicMapDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀f:((num → real) → num → real). ∀a:(num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_map_on⟨n, n⟩(U, f)",
			"a ∈ U",
			"vec_jacobian_determinant⟨n⟩(f, a) ≠ &0",
		},
		Conclusion: "∃V W:set(num → real). " +
			"    V ∈ euclidean_topology(n) ∧ " +
			"    W ∈ euclidean_topology(n) ∧ " +
			"    a ∈ V ∧ " +
			"    V ⊆ U ∧ " +
			"    vec_diffeomorphic_map⟨n⟩(V, W, f)",
	},
		"f's derivative near a is its Jacobian acting (JacobianDerivative), continuous in operator "+
			"norm since the partial derivatives are continuous; the determinant is continuous too, so it "+
			"has no zero on a ball B about a inside U, and there the derivative is invertible "+
			"(determinant.DeterminantZeroIffDependent; the inverse by cofactors over the determinant). "+
			"inverse_function.InverseFunction, applied to f altered outside B so as to carry ℝⁿ into ℝⁿ, "+
			"gives a local inverse g with a derivative at f(a), hence continuous there: take W a ball "+
			"about f(a) small enough that g carries it into B and into the theorem's σ-ball, and V = B ∩ "+
			"f⁻¹(W); its uniqueness clause gives g(f(x)) = x on V. InverseFunction gives a derivative at "+
			"f(a) only, so apply it again at each b = g(y), y ∈ W: its inverse there is continuous at y, "+
			"so near y takes values in the first σ-ball and solves the same equations, and is g; so g "+
			"has at y the inverse of f's derivative at b, and its partial derivatives there are the "+
			"entries of the inverse Jacobian (vec_derivative.PartialFromDerivative), cofactors of f's "+
			"Jacobian at g(y) divided by its determinant. So g of class Cᵏ on W makes them of class Cᵏ "+
			"(ContinuouslyDifferentiableCompose, SmoothReciprocal), and g of class Cᵏ⁺¹; induction on k"),
})}
