package projection_geometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var LocalFrame = localFrameThm{family.Add(registry.ProofEntry{
	Name: "LocalFrame",
	Key:  "prop_2791c201b62d6679",
	Deps: []registry.EntryLike{
		module_dimension.IdempotentTraceIsRank,
		module_dimension.TraceFromBasis,
		free_module.DeltaAtBasis,
		linear_independence.BasisWithinSpanning,
		module_dimension.IndependentFullBasis,
		smooth_manifold.FunctionAdd,
		smooth_manifold.FunctionMul,
		smooth_manifold.FunctionFiniteSum,
		smooth_manifold.FunctionReciprocal,
		smooth_manifold.FunctionContinuous,
		smooth_manifold.FunctionRestrict,
		smooth_manifold.OpenSubmanifold,
		smooth_manifold.SmoothFunctionDef,
		vec_smooth.SmoothSqrt,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀x:A.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀y:A. y ∈ ⋃T ⇒ projection_rank(P, y) = r",
			"x ∈ ⋃T",
		},
		Conclusion: "∃U:set(A). ∃F:(A → num → num → complex). " +
			"    x ∈ U ∧ smooth_projection_frame(n, r, T, 𝒜, P, U, F)",
	},
		"On ℂ^N the trace of P(y) in the delta basis is Σ P_ii (TraceFromBasis, DeltaAtBasis) and "+
			"equals the dimension of its image (IdempotentTraceIsRank), so the ε in projection_rank is met "+
			"and every image has dimension r. Choose r columns P(x)e_j forming a basis of the image at x "+
			"(BasisWithinSpanning) and apply complex Gram–Schmidt to P(y)e_j, whose squared residuals stay "+
			"smooth and positive near x. The r orthonormal columns span an image of dimension r "+
			"(IndependentFullBasis), so FF* = P(y). The filler promotes smooth_manifold.FunctionSqrt, a "+
			"sibling of FunctionReciprocal, from vec_smooth.SmoothSqrt in charts."),
})}

var TotalManifold = totalManifoldThm{family.Add(registry.ProofEntry{
	Name: "TotalManifold",
	Key:  "prop_694858925321a2c2",
	Deps: []registry.EntryLike{LocalFrame},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
		},
		Conclusion: "smooth_manifold⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"    projection_total_atlas(n, r, T, 𝒜, P)) ∧ " +
			"smooth_manifold_map⟨n + 2 * r, n⟩(projection_total_topology(T, P), " +
			"    projection_total_atlas(n, r, T, 𝒜, P), " +
			"    T, " +
			"    𝒜, " +
			"    λp:prod(A, num → complex). fst(p))",
	},
		"Local unitary frames identify the projection image with the product of "+
			"a base chart and C^r. Frame transitions are smooth complex linear maps."),
})}

var TotalOrientation = totalOrientationThm{family.Add(registry.ProofEntry{
	Name: "TotalOrientation",
	Key:  "prop_4e8b232e8af7bf33",
	Deps: []registry.EntryLike{TotalManifold, smooth_projection_bundle.RealifiedDeterminant},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"oriented_manifold⟨n⟩(T, 𝒜)",
		},
		Conclusion: "oriented_manifold⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"    projection_oriented_atlas(n, r, T, 𝒜, P))",
	},
		"Base coordinates precede complex fibre coordinates. A complex linear "+
			"frame transition has positive real determinant, the squared modulus of "+
			"its complex determinant (smooth_projection_bundle.RealifiedDeterminant)."),
})}

var FiberIntegralExistsUnique = fiberIntegralExistsUniqueThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralExistsUnique",
	Key:  "prop_ed58f2a79b944c7e",
	Deps: []registry.EntryLike{LocalFrame, FiberIntegrandCompact},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀ω:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"manifold_form_on⟨n + 2 * r⟩(projection_total_topology(T, P), " +
				"    projection_total_atlas(n, r, T, 𝒜, P), " +
				"    k + 2 * r, " +
				"    ω)",
			"projection_fiber_proper(n, r, T, 𝒜, P, ω)",
		},
		Conclusion: "projection_has_fiber_integral(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    k, " +
			"    ω, " +
			"    projection_fiber_integral(n, r, T, 𝒜, P, k, ω)) ∧ " +
			"(∀β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    projection_has_fiber_integral(n, r, T, 𝒜, P, k, ω, β) ⇒ " +
			"    β = projection_fiber_integral(n, r, T, 𝒜, P, k, ω))",
	},
		"Differentiate compact fibre integrals in a local trivialization. On compact base "+
			"neighborhoods the support bound is uniform. Frame changes preserve the complex fibre "+
			"orientation; change of variables and horizontal insertion glue the local integrals."),
})}

var FiberIntegralCompact = fiberIntegralCompactThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralCompact",
	Key:  "prop_507cddfecbfade65",
	Deps: []registry.EntryLike{FiberIntegralExistsUnique},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀ω:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"manifold_form_on⟨n + 2 * r⟩(projection_total_topology(T, P), " +
				"    projection_total_atlas(n, r, T, 𝒜, P), " +
				"    k + 2 * r, " +
				"    ω)",
			"compact_in(projection_total_topology(T, P), " +
				"    manifold_form_support⟨n + 2 * r⟩(projection_total_topology(T, P), " +
				"        projection_total_atlas(n, r, T, 𝒜, P), " +
				"        ω))",
		},
		Conclusion: "compact_in(T, " +
			"    manifold_form_support⟨n⟩(T, 𝒜, projection_fiber_integral(n, r, T, 𝒜, P, k, ω)))",
	}, "The support of the integral lies in the projection of the compact total support."),
})}

var FiberIntegralDifferential = fiberIntegralDifferentialThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralDifferential",
	Key:  "prop_db3290592ce3cfb6",
	Deps: []registry.EntryLike{FiberIntegralExistsUnique, FiberIntegrandCompact},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀ω:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"manifold_form_on⟨n + 2 * r⟩(projection_total_topology(T, P), " +
				"    projection_total_atlas(n, r, T, 𝒜, P), " +
				"    k + 2 * r, " +
				"    ω)",
			"projection_fiber_proper(n, r, T, 𝒜, P, ω)",
		},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    k, " +
			"    projection_fiber_integral(n, r, T, 𝒜, P, k, ω)) = " +
			"projection_fiber_integral(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    suc(k), " +
			"    manifold_exterior_derivative⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"        projection_total_atlas(n, r, T, 𝒜, P), " +
			"        k + 2 * r, " +
			"        ω))",
	},
		"In each frame integrate the vertical derivative by compact-support "+
			"Stokes. The even fibre dimension leaves a positive sign."),
})}

var FiberIntegralStokes = fiberIntegralStokesThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralStokes",
	Key:  "prop_28b332a337a56279",
	Deps: []registry.EntryLike{FiberIntegralExistsUnique, FiberIntegrandCompact},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀η:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
			"manifold_form_on⟨n + 2 * r⟩(projection_total_topology(T, P), " +
				"    projection_total_atlas(n, r, T, 𝒜, P), " +
				"    2 * r - 1, " +
				"    η)",
			"projection_fiber_proper(n, r, T, 𝒜, P, η)",
		},
		Conclusion: "projection_fiber_integral(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    0, " +
			"    manifold_exterior_derivative⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"        projection_total_atlas(n, r, T, 𝒜, P), " +
			"        2 * r - 1, " +
			"        η)) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). &0",
	},
		"On the 2r vertical coordinate vectors of a framed chart, dη is a sum of fibre partial "+
			"derivatives of η's components, each compactly supported in the fibre; each integrates "+
			"to zero over the fibre, so the zero form satisfies the local formula and uniqueness "+
			"identifies it with the fibre integral. This is the degree FiberIntegralDifferential "+
			"does not reach: a degree-zero fibre integral of a coboundary."),
})}
