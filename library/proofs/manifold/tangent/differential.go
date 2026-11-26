// The coordinate formula removes the source-chart choice from every
// use of the differential and gives its fiberwise linear chain rule.

package tangent

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var DifferentialCoordinate = differentialCoordinateThm{family.Add(registry.ProofEntry{
	Name: "DifferentialCoordinate",
	Key:  "prop_9b57a10e0e0ff800",
	Reading: "The target chart only needs to contain f(x), not the image of the " +
		"whole source chart. The coordinate map is smooth on its open chart-preimage " +
		"domain, which is a neighbourhood of the source coordinate of x.",
	Deps: []registry.EntryLike{
		DifferentialDef,
		TangentVectorDef,
		smooth_manifold.SmoothMapCompatibleCharts,
		smooth_manifold.CompatibleTransition,
		vec_smooth.JacobianChain,
		vec_smooth.PartialDerivativeLocal,
		matrix.MatrixActAssoc,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀d:prod(set(B), B → num → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"tangent_vector_on⟨n⟩(T, 𝒜, x, v)",
			"«active»(c)",
			"compatible_chart⟨m⟩(S, ℬ, d)",
			"f(x) ∈ fst(d)",
		},
		Conclusion: "manifold_differential⟨n, m⟩(T, 𝒜, S, ℬ, f, x, v, d) = " +
			"matrix_act⟨n⟩(vec_jacobian_matrix⟨n, m⟩(«coordinate map»(c, d, f), snd(c)(x)), v(c))",
	},
		"The chosen source chart and c both contain x. On an open neighbourhood their coordinate "+
			"expressions differ by the source transition; JacobianChain and the tangent "+
			"compatibility equation cancel that change of coordinates. Local derivative agreement "+
			"handles the restricted chosen inverses, giving the formula in every active source chart."),
})}

var DifferentialTangent = differentialTangentThm{family.Add(registry.ProofEntry{
	Name: "DifferentialTangent",
	Key:  "prop_42bdc3aa99499962",
	Deps: []registry.EntryLike{
		DifferentialDef,
		DifferentialCoordinate,
		smooth_manifold.SmoothMapCompatibleCharts,
		vec_smooth.JacobianChain,
		vec_smooth.PartialDerivativeLocal,
		matrix.MatrixActAssoc,
		matrix.MatrixActVec,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"tangent_vector_on⟨n⟩(T, 𝒜, x, v)",
		},
		Conclusion: "tangent_vector_on⟨m⟩(S, ℬ, f(x), manifold_differential⟨n, m⟩(T, 𝒜, S, ℬ, f, x, v))",
	},
		"The map sends the base point into the target carrier, and its Jacobian "+
			"sends padded n-vectors to padded m-vectors. Comparing two active target "+
			"charts in DifferentialCoordinate and applying the chain rule gives the "+
			"target transition equation. Inactive target components vanish by definition."),
})}

var DifferentialLinear = differentialLinearThm{family.Add(registry.ProofEntry{
	Name: "DifferentialLinear",
	Key:  "prop_508ce0e80fd2adf7",
	Reading: "The carrier-point hypothesis makes both fiber carriers " +
		"modules. The source-chart choice depends on the base point and " +
		"source atlas alone, so addition and scaling use the same Jacobian.",
	Deps: []registry.EntryLike{
		DifferentialTangent,
		DifferentialDef,
		TangentModule,
		TangentModuleDef,
		matrix.MatrixActLinear,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀x:A.",
		Hypotheses: []string{"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)", "x ∈ ⋃T"},
		Conclusion: "module_homomorphism(real_ring, " +
			"    tangent_module⟨n⟩(T, 𝒜, x), " +
			"    tangent_module⟨m⟩(S, ℬ, f(x)), " +
			"    manifold_differential⟨n, m⟩(T, 𝒜, S, ℬ, f, x))",
	},
		"DifferentialTangent supplies preservation of the fiber carriers. The source-chart "+
			"choice depends on x and the atlas, not on the tangent vector, so each active target "+
			"component is a fixed linear Jacobian action after evaluation; inactive components "+
			"are zero. The pointwise module operations therefore commute with the differential."),
})}

var DifferentialIdentity = differentialIdentityThm{family.Add(registry.ProofEntry{
	Name: "DifferentialIdentity",
	Key:  "prop_4ef4076c51f0edb5",
	Deps: []registry.EntryLike{
		DifferentialCoordinate,
		DifferentialTangent,
		TangentChartReconstruct,
		smooth_manifold.SmoothMapIdentity,
		vec_smooth.LinearSmoothMap,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{"tangent_vector_on⟨n⟩(T, 𝒜, x, v)"},
		Conclusion: "manifold_differential⟨n, n⟩(T, 𝒜, T, 𝒜, identity_map, x, v) = v",
	},
		"Use the same active chart on both sides of the identity map. Its coordinate "+
			"expression agrees locally with the Euclidean identity, whose Jacobian fixes "+
			"the chart component. Both sides are tangent vectors, so reconstruction from "+
			"that component gives equality of the full normalized families."),
})}

var DifferentialCompose = differentialComposeThm{family.Add(registry.ProofEntry{
	Name: "DifferentialCompose",
	Key:  "prop_91b8461f69a72188",
	Deps: []registry.EntryLike{
		DifferentialCoordinate,
		DifferentialTangent,
		TangentChartReconstruct,
		smooth_manifold.SmoothMapCompose,
		vec_smooth.JacobianChain,
		vec_smooth.PartialDerivativeLocal,
		matrix.MatrixActAssoc,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀R:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"smooth_manifold_map⟨m, k⟩(S, ℬ, R, 𝒞, g)",
			"tangent_vector_on⟨n⟩(T, 𝒜, x, v)",
		},
		Conclusion: "manifold_differential⟨n, k⟩(T, 𝒜, R, 𝒞, g ∘ f, x, v) = " +
			"manifold_differential⟨m, k⟩(S, " +
			"    ℬ, " +
			"    R, " +
			"    𝒞, " +
			"    g, " +
			"    f(x), " +
			"    manifold_differential⟨n, m⟩(T, 𝒜, S, ℬ, f, x, v))",
	},
		"Choose charts at x, f(x) and g(f(x)), restricting to the common open "+
			"chart-preimage neighbourhoods. DifferentialCoordinate expresses both sides "+
			"there, and the Euclidean Jacobian chain rule followed by MatrixActAssoc "+
			"identifies their final-chart components. DifferentialTangent and "+
			"TangentChartReconstruct give equality as normalized target tangent vectors."),
})}
