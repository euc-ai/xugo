package projective_bundle

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/manifold/chern_weil"
	"github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	"github.com/euc-ai/xugo/library/proofs/manifold/projection_geometry"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ProjectiveManifold = projectiveManifoldThm{family.Add(registry.ProofEntry{
	Name: "ProjectiveManifold",
	Key:  "prop_7eeb4c36816e6aaa",
	Deps: []registry.EntryLike{
		projection_geometry.LocalFrame,
		module_dimension.IdempotentTraceIsRank,
		smooth_manifold.CompatibleTransition,
		smooth_manifold.SmoothMapCompatibleCharts,
		smooth_manifold.CountableAtlas,
		smooth_manifold.FunctionContinuous,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothReciprocal,
		vec_smooth.SmoothCompose,
		complex_topology.ComplexHausdorff,
		complex_topology.ContinuousIffParts,
		complex_topology.CoordinateRealHomeomorphism,
		euclidean_topology.BoxCompact,
		euclidean_topology.EuclideanSecondCountable,
		continuous.ImageCompact,
		product_topology.Tychonoff,
		product_topology.IndexedHausdorff,
		product_topology.HausdorffProduct,
		product_topology.CompactProduct,
		compact.ClosedSubsetCompact,
		compact.CompactInSubtopology,
		countability.SecondCountableOpenCover,
		countability.SecondCountableImpLindelof,
		countability.SecondCountableSubtopology,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
		},
		Conclusion: "smooth_manifold⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
			"    projective_atlas(n, r, T, 𝒜, P)) ∧ " +
			"smooth_manifold_map⟨n + 2 * (r - 1), n⟩(projective_topology(T, P), " +
			"    projective_atlas(n, r, T, 𝒜, P), " +
			"    T, " +
			"    𝒜, " +
			"    λp:prod(A, num → num → complex). fst(p)) ∧ " +
			"kc_proper_map(projective_topology(T, P), T, λp:prod(A, num → num → complex). fst(p))",
	},
		"Frames F exist near every point (projection_geometry.LocalFrame). For Q in a fibre, R = F*QF "+
			"is a trace-one Hermitian idempotent, so R = uu* with |u| = 1 (IdempotentTraceIsRank): some "+
			"R_ll > 0 puts Q in a chart, Q = F ww* F*/|w|² with w_k = R_kl/R_ll inverts it, and transitions "+
			"are base transitions times smooth linear-fractional maps. Hausdorff comes from the product "+
			"laws and second countability from SecondCountableOpenCover over countably many chart domains; "+
			"over a compact K the preimage is closed in K times unit-bounded rows, each row set compact as "+
			"the image of a box under complex_topology.CoordinateRealHomeomorphism. The filler promotes the "+
			"product of compact subsets: compact K(i) in T(i) for i ∈ J give compact indexed_functions(J, "+
			"z, K) in indexed_product_topology(J, z, T), from Tychonoff and IndexedContinuousIff."),
})}

var TautologicalSplitting = tautologicalSplittingThm{family.Add(registry.ProofEntry{
	Name: "TautologicalSplitting",
	Key:  "prop_90955132d9b8b0d4",
	Deps: []registry.EntryLike{
		ProjectiveManifold,
		projection_bundle.RankTrace,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
		},
		Conclusion: "smooth_projection_bundle(n + 2 * (r - 1), " +
			"    fst(P), " +
			"    projective_topology(T, P), " +
			"    projective_atlas(n, r, T, 𝒜, P), " +
			"    snd(projective_tautological(T, P))) ∧ " +
			"smooth_projection_bundle(n + 2 * (r - 1), " +
			"    fst(P), " +
			"    projective_topology(T, P), " +
			"    projective_atlas(n, r, T, 𝒜, P), " +
			"    snd(projective_complement(T, P))) ∧ " +
			"projection_isomorphic(projective_topology(T, P), " +
			"    projection_pullback(projective_topology(T, P), λp:prod(A, num → num → complex). fst(p), P), " +
			"    projection_sum(projective_tautological(T, P), projective_complement(T, P))) ∧ " +
			"(∀p:prod(A, num → num → complex). " +
			"    p ∈ projective_space(T, P) ⇒ " +
			"    projection_rank(projective_tautological(T, P), p) = 1 ∧ " +
			"    projection_rank(projective_complement(T, P), p) = r - 1)",
	},
		"The matrices Q and P-Q are orthogonal smooth projections. Addition of "+
			"their image vectors identifies their external direct sum with im P. Each "+
			"rank is the trace of its projection at the point (RankTrace): Q has trace "+
			"one, the line being one-dimensional, and P − Q the trace of P less one."),
})}

var PullbackInjective = pullbackInjectiveThm{family.Add(registry.ProofEntry{
	Name: "PullbackInjective",
	Key:  "prop_1838938dcbc53c5d",
	Deps: []registry.EntryLike{ProjectiveLeftInverse},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a b:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
			"a ∈ (de_rham_cohomology_module⟨n⟩(T, 𝒜, k)).carrier",
			"b ∈ (de_rham_cohomology_module⟨n⟩(T, 𝒜, k)).carrier",
			"de_rham_pullback⟨n + 2 * (r - 1), n⟩(projective_topology(T, P), " +
				"    projective_atlas(n, r, T, 𝒜, P), " +
				"    T, " +
				"    𝒜, " +
				"    k, " +
				"    λp:prod(A, num → num → complex). fst(p), " +
				"    a) = " +
				"de_rham_pullback⟨n + 2 * (r - 1), n⟩(projective_topology(T, P), " +
				"    projective_atlas(n, r, T, 𝒜, P), " +
				"    T, " +
				"    𝒜, " +
				"    k, " +
				"    λp:prod(A, num → num → complex). fst(p), " +
				"    b)",
		},
		Conclusion: "a = b",
	},
		"Integrate along the compact projective fibres after wedging with "+
			"c1(S*)^(r-1). Affine polar coordinates give fibre integral one in the complex "+
			"orientation. The projection formula therefore supplies a left inverse."),
})}

var CompactPullbackInjective = compactPullbackInjectiveThm{family.Add(registry.ProofEntry{
	Name: "CompactPullbackInjective",
	Key:  "prop_ce9b55d1949dc15d",
	Deps: []registry.EntryLike{CompactProjectiveLeftInverse},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a b:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
			"a ∈ (compact_de_rham_module(n, T, 𝒜, k)).carrier",
			"b ∈ (compact_de_rham_module(n, T, 𝒜, k)).carrier",
			"compact_de_rham_pullback(n + 2 * (r - 1), " +
				"    projective_topology(T, P), " +
				"    projective_atlas(n, r, T, 𝒜, P), " +
				"    n, " +
				"    T, " +
				"    𝒜, " +
				"    λp:prod(A, num → num → complex). fst(p), " +
				"    k, " +
				"    a) = " +
				"compact_de_rham_pullback(n + 2 * (r - 1), " +
				"    projective_topology(T, P), " +
				"    projective_atlas(n, r, T, 𝒜, P), " +
				"    n, " +
				"    T, " +
				"    𝒜, " +
				"    λp:prod(A, num → num → complex). fst(p), " +
				"    k, " +
				"    b)",
		},
		Conclusion: "a = b",
	},
		"The same fibre integral left inverse preserves compact support; "+
			"properness makes the initial pullback compactly supported."),
})}

var ModelOrientation = modelOrientationThm{family.Add(registry.ProofEntry{
	Name: "ModelOrientation",
	Key:  "prop_4288462c1db39077",
	Deps: []registry.EntryLike{
		ProjectiveManifold,
		form_integral.OrientedZeroDimension,
		compact.FiniteCompact,
		smooth_manifold.FunctionConstant,
		smooth_manifold.AtlasMemberCompatible,
		smooth_manifold.CompatibleTransition,
		vec_smooth.DiffeomorphismJacobianNonzero,
		smooth_projection_bundle.RealifiedDeterminant,
	},
	Build: family.Card(Statement{
		Binders:    "∀r:num.",
		Hypotheses: []string{"0 < r"},
		Conclusion: "oriented_manifold⟨2 * (r - 1)⟩(projective_model_topology(r), " +
			"    projective_model_atlas(r)) ∧ " +
			"compact_in(projective_model_topology(r), ⋃projective_model_topology(r))",
	},
		"ProjectiveManifold at n = 0, over the point with the trivial rank-r bundle "+
			"(smooth_manifold.FunctionConstant, trace r), gives the smooth structure, and properness "+
			"of fst onto the compact point (compact.FiniteCompact) gives compactness. At r = 1 the "+
			"dimension is zero and form_integral.OrientedZeroDimension orients it; for r ≥ 2 a "+
			"transition is a linear-fractional map holomorphic in the interleaved coordinates, whose "+
			"real Jacobian determinant is |det_ℂ|² (smooth_projection_bundle.RealifiedDeterminant), "+
			"nonzero since the transition is a diffeomorphism (CompatibleTransition, "+
			"DiffeomorphismJacobianNonzero). The filler promotes the point as a 0-manifold: "+
			"smooth_manifold⟨0⟩({U:set(bool) | U ⊆ {⊤}}, {({⊤}, λb:bool. λi:num. &0)})."),
})}

var FiberIntegral = fiberIntegralThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegral",
	Key:  "prop_c99c86b58786ea8a",
	Deps: []registry.EntryLike{ModelOrientation, ProjectiveManifold},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀ω:(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
			"manifold_form_on⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
				"    projective_atlas(n, r, T, 𝒜, P), " +
				"    k + 2 * (r - 1), " +
				"    ω)",
		},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, k, projective_fiber_integral(n, r, T, 𝒜, P, k, ω)) ∧ " +
			"(∀U:set(A). ∀F:(A → num → num → complex). " +
			"    smooth_projection_frame(n, r, T, 𝒜, P, U, F) ⇒ " +
			"    manifold_form_restrict⟨n⟩(T, 𝒜, U, projective_fiber_integral(n, r, T, 𝒜, P, k, ω)) = " +
			"    manifold_fiber_integral⟨n, 2 * (r - 1)⟩(subtopology(T, U), " +
			"        open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"        projective_model_topology(r), " +
			"        projective_model_atlas(r), " +
			"        k, " +
			"        manifold_form_pullback⟨n + 2 * (r - 1), n + 2 * (r - 1)⟩( " +
			"            product_topology(subtopology(T, U), projective_model_topology(r)), " +
			"            smooth_product_atlas⟨n, 2 * (r - 1)⟩(open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
			"                projective_model_atlas(r)), " +
			"            projective_topology(T, P), " +
			"            projective_atlas(n, r, T, 𝒜, P), " +
			"            k + 2 * (r - 1), " +
			"            projective_frame_map(r, F), " +
			"            ω)))",
	},
		"The compact oriented projective fibre permits differentiation under the "+
			"integral. Unitary transition maps preserve fibre orientation; horizontal "+
			"insertion and change of variables make the local formulas agree."),
})}

var HyperplaneNormalization = hyperplaneNormalizationThm{family.Add(registry.ProofEntry{
	Name: "HyperplaneNormalization",
	Key:  "prop_518067426c7814ab",
	Deps: []registry.EntryLike{FiberIntegral, chern_weil.ChernClosed},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
		},
		Conclusion: "projective_fiber_integral(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    0, " +
			"    projective_hyperplane_power(n, r, T, 𝒜, P, r - 1)) = " +
			"manifold_form_unit⟨n⟩(T, 𝒜)",
	},
		"The dual tautological Chern form restricts to the positive hyperplane "+
			"form. Its top power integrates to one, computed in an affine chart by "+
			"polar coordinates and the normalized 2 pi curvature factor."),
})}

var ProjectiveLeftInverse = projectiveLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "ProjectiveLeftInverse",
	Key:  "prop_58dc9ab1847a912e",
	Deps: []registry.EntryLike{
		HyperplaneNormalization,
		FiberIntegralDifferential,
		FiberIntegralStokes,
		form_integral.FiberIntegralProjectionFormula,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
			"a ∈ (de_rham_cohomology_module⟨n⟩(T, 𝒜, k)).carrier",
		},
		Conclusion: "projective_fiber_class(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    k, " +
			"    de_rham_wedge⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
			"        projective_atlas(n, r, T, 𝒜, P), " +
			"        k, " +
			"        2 * (r - 1), " +
			"        de_rham_pullback⟨n + 2 * (r - 1), n⟩(projective_topology(T, P), " +
			"            projective_atlas(n, r, T, 𝒜, P), " +
			"            T, " +
			"            𝒜, " +
			"            k, " +
			"            λp:prod(A, num → num → complex). fst(p), " +
			"            a), " +
			"        de_rham_class⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
			"            projective_atlas(n, r, T, 𝒜, P), " +
			"            2 * (r - 1), " +
			"            projective_hyperplane_power(n, r, T, 𝒜, P, r - 1)))) = " +
			"a",
	},
		"The fibre projection formula and hyperplane normalization give a left inverse on "+
			"representatives. Fibre Stokes shows it descends to the actual de Rham quotient."),
})}

var FiberIntegralCompact = fiberIntegralCompactThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralCompact",
	Key:  "prop_150dd8c857ee7e96",
	Deps: []registry.EntryLike{FiberIntegral},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀ω:(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
			"manifold_form_on⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
				"    projective_atlas(n, r, T, 𝒜, P), " +
				"    k + 2 * (r - 1), " +
				"    ω)",
			"compact_in(projective_topology(T, P), " +
				"    manifold_form_support⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
				"        projective_atlas(n, r, T, 𝒜, P), " +
				"        ω))",
		},
		Conclusion: "compact_in(T, " +
			"    manifold_form_support⟨n⟩(T, 𝒜, projective_fiber_integral(n, r, T, 𝒜, P, k, ω)))",
	}, "The base support is contained in the image of the compact total support."),
})}

var FiberIntegralDifferential = fiberIntegralDifferentialThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralDifferential",
	Key:  "prop_76cb4f2ebc389913",
	Deps: []registry.EntryLike{FiberIntegral},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀ω:(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
			"manifold_form_on⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
				"    projective_atlas(n, r, T, 𝒜, P), " +
				"    k + 2 * (r - 1), " +
				"    ω)",
		},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    k, " +
			"    projective_fiber_integral(n, r, T, 𝒜, P, k, ω)) = " +
			"projective_fiber_integral(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    suc(k), " +
			"    manifold_exterior_derivative⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
			"        projective_atlas(n, r, T, 𝒜, P), " +
			"        k + 2 * (r - 1), " +
			"        ω))",
	},
		"Local product differentiation and Stokes on the compact projective fibre "+
			"remove the vertical derivative; its even dimension leaves positive sign."),
})}

var FiberIntegralStokes = fiberIntegralStokesThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralStokes",
	Key:  "prop_212995f5ac3450a2",
	Deps: []registry.EntryLike{FiberIntegral, ModelOrientation, form_integral.ManifoldStokes},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀η:(prod(set(prod(A, num → num → complex)), prod(A, num → num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"1 < r",
			"manifold_form_on⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
				"    projective_atlas(n, r, T, 𝒜, P), " +
				"    2 * (r - 1) - 1, " +
				"    η)",
		},
		Conclusion: "projective_fiber_integral(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    0, " +
			"    manifold_exterior_derivative⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
			"        projective_atlas(n, r, T, 𝒜, P), " +
			"        2 * (r - 1) - 1, " +
			"        η)) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). &0",
	},
		"In a local frame the degree-zero fibre integral of dη is, at each base point, the "+
			"integral over the compact model fibre of the exterior derivative of a top-minus-one "+
			"form; ManifoldStokes on the closed oriented model makes it zero. This is the degree "+
			"FiberIntegralDifferential does not reach: a degree-zero fibre integral of a coboundary."),
})}

var CompactProjectiveLeftInverse = compactProjectiveLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "CompactProjectiveLeftInverse",
	Key:  "prop_f3312db06cda1be8",
	Deps: []registry.EntryLike{
		HyperplaneNormalization,
		FiberIntegralCompact,
		FiberIntegralDifferential,
		FiberIntegralStokes,
		form_integral.FiberIntegralProjectionFormula,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"0 < r",
			"a ∈ (compact_de_rham_module(n, T, 𝒜, k)).carrier",
		},
		Conclusion: "projective_compact_fiber_class(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    k, " +
			"    compact_de_rham_product(n + 2 * (r - 1), " +
			"        projective_topology(T, P), " +
			"        projective_atlas(n, r, T, 𝒜, P), " +
			"        k, " +
			"        2 * (r - 1), " +
			"        compact_de_rham_pullback(n + 2 * (r - 1), " +
			"            projective_topology(T, P), " +
			"            projective_atlas(n, r, T, 𝒜, P), " +
			"            n, " +
			"            T, " +
			"            𝒜, " +
			"            λp:prod(A, num → num → complex). fst(p), " +
			"            k, " +
			"            a), " +
			"        de_rham_class⟨n + 2 * (r - 1)⟩(projective_topology(T, P), " +
			"            projective_atlas(n, r, T, 𝒜, P), " +
			"            2 * (r - 1), " +
			"            projective_hyperplane_power(n, r, T, 𝒜, P, r - 1)))) = " +
			"a",
	},
		"Proper projective pullback preserves compact support. The projection "+
			"formula and hyperplane normalization give the identity, and fibre Stokes "+
			"and compact support preservation make the compact quotient map well defined."),
})}
