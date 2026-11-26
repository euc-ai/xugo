// Evaluation in one active chart identifies the tangent fiber with R^n.
// Compatible data on the original atlas extend to the normalized family.

package tangent

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var TangentModule = tangentModuleThm{family.Add(registry.ProofEntry{
	Name: "TangentModule",
	Key:  "prop_7631dfdfb2c1ea2f",
	Reading: "The hypothesis x∈⋃T is necessary: at a point outside the " +
		"carrier the defined fiber is empty and cannot be a module. Inside the " +
		"carrier its zero is the same component function at every base point.",
	Deps: []registry.EntryLike{
		TangentModuleDef,
		TangentVectorDef,
		function_module.FunctionModuleDef,
		matrix.MatrixActLinear,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀x:A.",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "x ∈ ⋃T"},
		Conclusion: "module_on(real_ring, tangent_module⟨n⟩(T, 𝒜, x))",
	},
		"Padded vectors form the inner function module, and chart families form its "+
			"function module. Each transition Jacobian acts linearly, so pointwise addition "+
			"and real scaling preserve the compatibility equations and the zero components "+
			"on inactive charts. The normalized tangent carrier is therefore a submodule."),
})}

var TangentFromChart = tangentFromChartThm{family.Add(registry.ProofEntry{
	Name: "TangentFromChart",
	Key:  "prop_36b7991b20428d34",
	Reading: "The padded-vector hypothesis is necessary for the source component " +
		"to equal u: the Jacobian action cannot preserve an arbitrary nonzero tail.",
	Deps: []registry.EntryLike{
		TangentFromChartDef,
		TangentVectorDef,
		smooth_manifold.CompatibleTransition,
		vec_smooth.JacobianChain,
		vec_smooth.PartialDerivativeLocal,
		vec_smooth.LinearSmoothMap,
		matrix.MatrixActAssoc,
		matrix.MatrixActVec,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀u:(num → real).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "«active»(c)", "vec⟨n⟩(u)"},
		Conclusion: "tangent_vector_on⟨n⟩(T, 𝒜, x, tangent_from_chart⟨n⟩(T, 𝒜, c, x, u)) ∧ " +
			"tangent_from_chart⟨n⟩(T, 𝒜, c, x, u, c) = u",
	},
		"The transition cocycle holds on open triple overlaps; JacobianChain and local agreement "+
			"turn it into the linear compatibility equation for the propagated components. The "+
			"self-transition agrees with the identity near the base coordinate, so its Jacobian acts "+
			"as the identity on padded n-vectors. All inactive components vanish by definition."),
})}

var TangentChartReconstruct = tangentChartReconstructThm{family.Add(registry.ProofEntry{
	Name: "TangentChartReconstruct",
	Key:  "prop_f2d2cd042562d3b0",
	Deps: []registry.EntryLike{TangentVectorDef, TangentFromChartDef},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{"tangent_vector_on⟨n⟩(T, 𝒜, x, v)", "«active»(c)"},
		Conclusion: "tangent_from_chart⟨n⟩(T, 𝒜, c, x, v(c)) = v",
	},
		"At every active output chart the equality is the tangent compatibility "+
			"equation with source c. At every inactive chart both component families "+
			"are zero. Function extensionality gives equality on all chart indices."),
})}

var TangentChartIsomorphism = tangentChartIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "TangentChartIsomorphism",
	Key:  "prop_2899710ea4fe0ddf",
	Deps: []registry.EntryLike{
		TangentModule,
		TangentFromChart,
		TangentChartReconstruct,
		TangentModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀x:A.",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "«active»(c)"},
		Conclusion: "module_isomorphism(real_ring, " +
			"    tangent_module⟨n⟩(T, 𝒜, x), " +
			"    «Euclidean module», " +
			"    λv:(prod(set(A), A → num → real) → num → real). v(c))",
	},
		"Evaluation respects the pointwise module operations. TangentFromChart supplies a preimage "+
			"of every padded n-vector, and TangentChartReconstruct makes evaluation injective on the "+
			"tangent carrier. These give the module isomorphism, including dimension zero."),
})}

var TangentAtlasExtension = tangentAtlasExtensionThm{family.Add(registry.ProofEntry{
	Name: "TangentAtlasExtension",
	Key:  "prop_ab5c2537986944d2",
	Reading: "Only components on original charts containing x are prescribed. " +
		"Values of h on other charts are arbitrary and need not be zero; the unique " +
		"extended tangent vector itself is normalized on every inactive chart.",
	Deps: []registry.EntryLike{
		TangentFromChart,
		TangentChartReconstruct,
		smooth_manifold.AtlasMemberCompatible,
		smooth_manifold.AtlasDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀x:A. " +
			"∀h:(prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"x ∈ ⋃T",
			"∀c:prod(set(A), A → num → real). c ∈ 𝒜 ∧ x ∈ fst(c) ⇒ vec⟨n⟩(h(c))",
			"∀c d:prod(set(A), A → num → real). " +
				"    c ∈ 𝒜 ∧ d ∈ 𝒜 ∧ x ∈ fst(c) ∧ x ∈ fst(d) ⇒ " +
				"    h(d) = matrix_act⟨n⟩(vec_jacobian_matrix⟨n, n⟩(«transition»(c, d), snd(c)(x)), h(c))",
		},
		Conclusion: "∃v:(prod(set(A), A → num → real) → num → real). " +
			"    tangent_vector_on⟨n⟩(T, 𝒜, x, v) ∧ " +
			"    (∀c:prod(set(A), A → num → real). c ∈ 𝒜 ∧ x ∈ fst(c) ⇒ v(c) = h(c)) ∧ " +
			"    (∀w:(prod(set(A), A → num → real) → num → real). " +
			"        tangent_vector_on⟨n⟩(T, 𝒜, x, w) ∧ " +
			"        (∀c:prod(set(A), A → num → real). c ∈ 𝒜 ∧ x ∈ fst(c) ⇒ w(c) = h(c)) ⇒ " +
			"        w = v)",
	},
		"Choose one original chart containing x and propagate h's component there by "+
			"TangentFromChart. The supplied transition equations recover every other prescribed "+
			"component. Any other tangent vector with the same prescribed components agrees at "+
			"the chosen chart and hence agrees everywhere by TangentChartReconstruct."),
})}
