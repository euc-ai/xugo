// smooth.go — smooth functions: the constants and the coordinates are
// smooth, sums, products, quotients by a function without zeros, square
// roots of a positive function and composites are smooth, and smoothness
// passes to subsets, is decided near each point, and is kept by the
// partial derivatives. A linear map is smooth with its own matrix for its
// Jacobian.

package vec_smooth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/registry"
)

// SmoothConst — a constant is smooth.
var SmoothConst = smoothConstThm{family.Add(registry.ProofEntry{
	Name: "SmoothConst",
	Key:  "prop_b709dd066bc2aae8",
	Reading: "U a set of n-vectors is load-bearing: " +
		"every class asks continuity at the points of U in ℝⁿ.",
	Deps: []registry.EntryLike{
		SmoothOnDef,
		ContinuouslyDifferentiableOnDef,
		real_derivative.DerivativeConst,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀a:real.",
		Hypotheses: []string{
			"U ⊆ {u:num → real | vec⟨n⟩(u)}",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). a)",
	},
		"every partial derivative of a constant is 0 (real_derivative.DerivativeConst along "+
			"each line), a constant again; induction on the class for all constants at once"),
})}

// SmoothCoordinate — each coordinate is a smooth function.
var SmoothCoordinate = smoothCoordinateThm{family.Add(registry.ProofEntry{
	Name: "SmoothCoordinate",
	Key:  "prop_60ba124e1c768fa1",
	Reading: "Any i: for i ≥ n the coordinate is 0 on ℝⁿ, " +
		"and still its partial derivatives along every line are 0.",
	Deps: []registry.EntryLike{
		SmoothConst,
		ContinuouslyDifferentiableCongruence,
		euclidean_topology.CoordinateContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀i:num.",
		Hypotheses: []string{
			"U ⊆ {u:num → real | vec⟨n⟩(u)}",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). x(i))",
	},
		"t ↦ (c + t·e_j)(i) is c(i) + t for j = i and c(i) otherwise, so ∂ⱼ of the coordinate "+
			"is the constant 1 or 0 at every point (SmoothConst); a coordinate is continuous on "+
			"ℝⁿ (euclidean_topology.CoordinateContinuous, and the constant 0 for i ≥ n)"),
})}

// SmoothAdd — a sum of smooth functions is smooth.
var SmoothAdd = smoothAddThm{family.Add(registry.ProofEntry{
	Name: "SmoothAdd",
	Key:  "prop_e263c6e60ca2175f",
	Deps: []registry.EntryLike{SmoothOnDef, ContinuouslyDifferentiableAdd},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀g h:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_on⟨n⟩(U, g)",
			"vec_smooth_on⟨n⟩(U, h)",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). g(x) + h(x))",
	},
		"ContinuouslyDifferentiableAdd at every class"),
})}

// SmoothSub — a difference of smooth functions is smooth.
var SmoothSub = smoothSubThm{family.Add(registry.ProofEntry{
	Name: "SmoothSub",
	Key:  "prop_31916d76ed1b90a5",
	Deps: []registry.EntryLike{SmoothAdd, SmoothMul, SmoothConst, ContinuouslyDifferentiableCongruence},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀g h:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_on⟨n⟩(U, g)",
			"vec_smooth_on⟨n⟩(U, h)",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). g(x) - h(x))",
	},
		"g − h = g + (−1)·h: SmoothConst, SmoothMul, SmoothAdd"),
})}

// SmoothMul — a product of smooth functions is smooth.
var SmoothMul = smoothMulThm{family.Add(registry.ProofEntry{
	Name: "SmoothMul",
	Key:  "prop_29027bc0bf7c978f",
	Deps: []registry.EntryLike{SmoothOnDef, ContinuouslyDifferentiableMul},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀g h:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_on⟨n⟩(U, g)",
			"vec_smooth_on⟨n⟩(U, h)",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). g(x) * h(x))",
	},
		"ContinuouslyDifferentiableMul at every class"),
})}

// SmoothSum — a finite sum of smooth functions is smooth.
var SmoothSum = smoothSumThm{family.Add(registry.ProofEntry{
	Name: "SmoothSum",
	Key:  "prop_3df9cb4426958b75",
	Deps: []registry.EntryLike{SmoothOnDef, ContinuouslyDifferentiableSum},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀N:num. ∀h:(num → (num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"∀i:num. i < N ⇒ vec_smooth_on⟨n⟩(U, h(i))",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). Σ_{i<N} h(i)(x))",
	},
		"ContinuouslyDifferentiableSum at every class"),
})}

// SmoothCompose — a smooth function of a smooth map is smooth.
var SmoothCompose = smoothComposeThm{family.Add(registry.ProofEntry{
	Name: "SmoothCompose",
	Key:  "prop_3c84e2731247a4bb",
	Deps: []registry.EntryLike{SmoothOnDef, SmoothMapOnDef, ContinuouslyDifferentiableCompose},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀U V:((num → real) → bool). " +
			"∀f:((num → real) → num → real). " +
			"∀g:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(m)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_smooth_on⟨m⟩(V, g)",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). g(f(x)))",
	},
		"ContinuouslyDifferentiableCompose at every class"),
})}

// SmoothMapCompose — a composite of smooth maps is smooth.
var SmoothMapCompose = smoothMapComposeThm{family.Add(registry.ProofEntry{
	Name: "SmoothMapCompose",
	Key:  "prop_6355dc251c9a8ef7",
	Deps: []registry.EntryLike{SmoothMapOnDef, SmoothCompose},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. ∀U V:((num → real) → bool). ∀f h:((num → real) → num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(m)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_smooth_map_on⟨m, k⟩(V, h)",
		},
		Conclusion: "vec_smooth_map_on⟨n, k⟩(U, h ∘ f)",
	},
		"each coordinate of h ∘ f is a coordinate of h composed "+
			"with f (SmoothCompose), and h carries f(x) ∈ V into ℝᵏ"),
})}

// SmoothComposeReal — a function of one variable with derivatives of all
// orders, applied to a smooth function, gives a smooth function.
var SmoothComposeReal = smoothComposeRealThm{family.Add(registry.ProofEntry{
	Name: "SmoothComposeReal",
	Key:  "prop_111efa1f20d47b9d",
	Reading: "D is the one-variable function D(0) with its derivatives D(1), D(2), " +
		"… on s, the form the corpus states higher derivatives in (real_taylor). U " +
		"open is load-bearing through the congruence the induction uses.",
	Deps: []registry.EntryLike{
		SmoothOnDef,
		ContinuouslyDifferentiableOnDef,
		real_derivative.DerivativeChain,
		real_derivative.DerivativeContinuous,
		ContinuouslyDifferentiableMul,
		ContinuouslyDifferentiableCongruence,
		PartialDerivativeValue,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀U:((num → real) → bool). " +
			"∀s:(real → bool). " +
			"∀D:(num → real → real). " +
			"∀g:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"s ∈ real_topology",
			"∀k:num. ∀t:real. t ∈ s ⇒ real_derivative_at(D(k), t, D(k + 1)(t))",
			"vec_smooth_on⟨n⟩(U, g)",
			"∀x:(num → real). x ∈ U ⇒ g(x) ∈ s",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). D(0)(g(x)))",
	},
		"show D(k) ∘ g of class j on U for all k at once, by induction on j: D(k) is differentiable, "+
			"so continuous, on s (real_derivative.DerivativeContinuous), and along each line ∂ⱼ(D(k) ∘ g) "+
			"= (D(k + 1) ∘ g)·∂ⱼg on U by the one-variable chain rule (real_derivative.DerivativeChain), "+
			"a product of two functions of class j (ContinuouslyDifferentiableMul, Congruence)"),
})}

// SmoothReciprocal — the reciprocal of a smooth function without zeros is
// smooth.
var SmoothReciprocal = smoothReciprocalThm{family.Add(registry.ProofEntry{
	Name: "SmoothReciprocal",
	Key:  "prop_286d0c015544b694",
	Deps: []registry.EntryLike{
		SmoothComposeReal,
		real_derivative.DerivativeInv,
		real_derivative.DerivativeDiv,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀g:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_on⟨n⟩(U, g)",
			"∀x:(num → real). x ∈ U ⇒ g(x) ≠ &0",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). &1 / g(x))",
	},
		"SmoothComposeReal on the open set of nonzero reals with D(k)(t) = (−1)ᵏ·k!/tᵏ⁺¹, "+
			"whose derivative is D(k + 1) there (real_derivative.DerivativeInv, DerivativeDiv)"),
})}

// SmoothSqrt — the square root of a smooth positive function is smooth.
var SmoothSqrt = smoothSqrtThm{family.Add(registry.ProofEntry{
	Name: "SmoothSqrt",
	Key:  "prop_5dd1734ae09c101b",
	Deps: []registry.EntryLike{SmoothComposeReal, real_rpow.RpowDerivativeBase, real_rpow.RpowSqrt},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀g:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_on⟨n⟩(U, g)",
			"∀x:(num → real). x ∈ U ⇒ &0 < g(x)",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, λx:(num → real). real_sqrt(g(x)))",
	},
		"SmoothComposeReal on the positive reals with D(k)(t) = cₖ·t^(1/2 − k), c₀ = "+
			"1 and cₖ₊₁ = (1/2 − k)·cₖ: real_sqrt is t^(1/2) there (real_rpow.RpowSqrt) "+
			"and the power rule (RpowDerivativeBase) gives each derivative"),
})}

// SmoothSubset — a function smooth on U is smooth on every subset of U.
var SmoothSubset = smoothSubsetThm{family.Add(registry.ProofEntry{
	Name: "SmoothSubset",
	Key:  "prop_48f16ddf1e9078ac",
	Deps: []registry.EntryLike{SmoothOnDef, ContinuouslyDifferentiableSubset},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U V:((num → real) → bool). ∀g:((num → real) → real).",
		Hypotheses: []string{
			"V ⊆ U",
			"vec_smooth_on⟨n⟩(U, g)",
		},
		Conclusion: "vec_smooth_on⟨n⟩(V, g)",
	},
		"ContinuouslyDifferentiableSubset at every class"),
})}

// SmoothLocal — smoothness on an open set is decided near each of its
// points.
var SmoothLocal = smoothLocalThm{family.Add(registry.ProofEntry{
	Name: "SmoothLocal",
	Key:  "prop_e6dda2b41a634923",
	Deps: []registry.EntryLike{SmoothOnDef, ContinuouslyDifferentiableOnDef, SmoothPartial},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀g:((num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"∀x:(num → real). " +
				"    x ∈ U ⇒ " +
				"    ∃V:set(num → real). V ∈ euclidean_topology(n) ∧ x ∈ V ∧ V ⊆ U ∧ vec_smooth_on⟨n⟩(V, g)",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, g)",
	},
		"class k on U for all g at once, by induction on k: continuity at x and "+
			"the partial derivatives at x are those on the V about x, and each ∂ⱼg is "+
			"smooth on every such V (SmoothPartial), so the hypothesis holds for ∂ⱼg"),
})}

// SmoothPartial — the partial derivatives of a smooth function are smooth
// and are its derivatives at every point.
var SmoothPartial = smoothPartialThm{family.Add(registry.ProofEntry{
	Name: "SmoothPartial",
	Key:  "prop_60cf41d49c4d0070",
	Deps: []registry.EntryLike{SmoothOnDef, ContinuouslyDifferentiableOnDef, PartialDerivativeValue},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U:((num → real) → bool). ∀g:((num → real) → real). ∀j:num.",
		Hypotheses: []string{
			"vec_smooth_on⟨n⟩(U, g)",
			"j < n",
		},
		Conclusion: "vec_smooth_on⟨n⟩(U, partial_derivative(g, j)) ∧ " +
			"∀x:(num → real). x ∈ U ⇒ partial_derivative_at(g, j, x, partial_derivative(g, j, x))",
	},
		"class k + 1 of g gives class k of ∂ⱼg and the existence of the partial "+
			"derivative at each point of U, which PartialDerivativeValue names"),
})}

// LinearSmoothMap — a linear map of ℝⁿ into ℝᵐ is smooth, and its Jacobian
// matrix at every point is its matrix.
var LinearSmoothMap = linearSmoothMapThm{family.Add(registry.ProofEntry{
	Name: "LinearSmoothMap",
	Key:  "prop_2dff3a129ae7dd7",
	Reading: "vec_linear is linearity on all sequences, so along every " +
		"line L moves by a constant vector and no openness of U is needed.",
	Deps: []registry.EntryLike{
		SmoothMapOnDef,
		JacobianMatrixDef,
		SmoothConst,
		PartialDerivativeValue,
		matrix.MatrixOfDef,
		euclidean.LinearBasisEstimate,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. ∀U:((num → real) → bool). ∀L:((num → real) → num → real).",
		Hypotheses: []string{
			"U ⊆ {u:num → real | vec⟨n⟩(u)}",
			"vec_linear(L)",
			"∀u:(num → real). vec⟨n⟩(u) ⇒ vec⟨m⟩(L(u))",
		},
		Conclusion: "vec_smooth_map_on⟨n, m⟩(U, L) ∧ " +
			"∀x:(num → real). x ∈ U ⇒ vec_jacobian_matrix⟨n, m⟩(L, x) = matrix_of(n, L)",
	},
		"L(c + t·e_j)(i) = L(c)(i) + t·L(e_j)(i), so ∂ⱼ of the i-th coordinate is the constant "+
			"L(e_j)(i) (SmoothConst, PartialDerivativeValue), which is matrix_of's entry, both "+
			"being 0 for i ≥ m since L(e_j) is an m-vector; continuity from |L(y)(i) − L(x)(i)| = "+
			"|L(y − x)(i)| bounded by a multiple of ‖y − x‖_n (euclidean.LinearBasisEstimate)"),
})}
