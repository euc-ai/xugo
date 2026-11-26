// Fiber integration is linear and commutes with exterior differentiation.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_riemann"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var FiberIntegralAdd = fiberIntegralAddThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralAdd",
	Key:  "prop_93ace7f47fa746c6",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		FiberSliceForm,
		IntegralAdd,
		differential_form.SupportClosed,
		compact.ClosedSubsetCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω η:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, η)",
		},
		Conclusion: "manifold_fiber_integral⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    k, " +
			"    λc:prod(set(prod(A, B)), prod(A, B) → num → real). λy:(num → real). λP:(num → num → real). " +
			"        ω(c, y, P) + η(c, y, P)) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω)(c, y, P) + " +
			"    manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, η)(c, y, P)",
	},
		"Slicing commutes with pointwise addition. Each slice has compact support "+
			"because the fiber is compact, so IntegralAdd applies pointwise in every "+
			"valid base chart; normalization handles the remaining arguments."),
})}

var FiberIntegralScale = fiberIntegralScaleThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralScale",
	Key:  "prop_b46dff115a68db87",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		FiberSliceForm,
		IntegralScale,
		differential_form.SupportClosed,
		compact.ClosedSubsetCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real). " +
			"∀a:real.",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
		},
		Conclusion: "manifold_fiber_integral⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    k, " +
			"    λc:prod(set(prod(A, B)), prod(A, B) → num → real). λy:(num → real). λP:(num → num → real). " +
			"        a * ω(c, y, P)) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    a * manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω)(c, y, P)",
	},
		"Pull the constant real scalar through each fiber slice and apply IntegralScale "+
			"on the compact fiber. Both sides vanish at invalid base chart data."),
})}

var FiberIntegralFiniteSum = fiberIntegralFiniteSumThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralFiniteSum",
	Key:  "prop_6a240264423d60ee",
	Reading: "The base-manifold and compact oriented-fiber " +
		"hypotheses remain explicit even for an empty index set.",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		FiberSliceForm,
		IntegralFiniteSum,
		differential_form.SupportClosed,
		compact.ClosedSubsetCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀N:num. " +
			"∀ω:(num → " +
			"        prod(set(prod(A, B)), prod(A, B) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"∀i:num. " +
				"    i < N ⇒ " +
				"    manifold_form_on⟨n + m⟩(product_topology(T, S), " +
				"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
				"        k + m, " +
				"        ω(i))",
		},
		Conclusion: "manifold_fiber_integral⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    k, " +
			"    λc:prod(set(prod(A, B)), prod(A, B) → num → real). λy:(num → real). λP:(num → num → real). " +
			"        Σ_{i<N} ω(i, c, y, P)) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    Σ_{i<N} manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω(i))(c, y, P)",
	},
		"The slice of a finite sum is the finite sum of its slices, and their "+
			"supports are compact in the compact fiber. Apply IntegralFiniteSum; "+
			"its empty-sum case gives the same result when N is zero."),
})}

var FiberIntegralExteriorDerivative = fiberIntegralExteriorDerivativeThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralExteriorDerivative",
	Key:  "prop_9c96221c14886813",
	Reading: "With horizontal slots before vertical slots, d commutes with fiber integration without " +
		"a sign. The fiber is compact and has no boundary. The vertical terms are integrated as whole " +
		"exact fiber forms, so derivatives of localization weights are not dropped. For positive m, the " +
		"vertical remainder is (-1)^(k+1) times the fiber derivative of the global (m-1)-form obtained " +
		"by inserting k+1 horizontal vectors; compactness of the fiber supplies its compact support.",
	Deps: []registry.EntryLike{
		FiberIntegralForm,
		FiberIntegralCoordinate,
		ManifoldStokes,
		differential_form.ExteriorDerivativeDef,
		differential_form.ExteriorDerivativeForm,
		differential_form.FormOnDef,
		vec_form.ExteriorDerivativeDef,
		vec_smooth.PartialDerivativeUnderIntegral,
		lebesgue_riemann.LebesgueIntegralInterval,
		vec_integral.IntegralSplit,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
		},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    k, " +
			"    manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω)) = " +
			"manifold_fiber_integral⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    k + 1, " +
			"    manifold_exterior_derivative⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        k + m, " +
			"        ω))",
	},
		"In a base chart separate the exterior derivative into horizontal differentiation and the "+
			"vertical exterior derivative of the components with k+1 horizontal slots. Differentiate the "+
			"fixed-partition integral under the integral sign; horizontal terms have exactly the base "+
			"exterior-derivative signs. For positive fiber dimension the remaining global fiber forms are "+
			"exact top forms and vanish by ManifoldStokes; in dimension zero there are no vertical terms."),
})}
