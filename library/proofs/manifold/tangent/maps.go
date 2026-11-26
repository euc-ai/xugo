// The differential varies smoothly with the base point, yielding a
// smooth map of tangent bundles with the identity and composition laws.

package tangent

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var TangentMapSmooth = tangentMapSmoothThm{family.Add(registry.ProofEntry{
	Name: "TangentMapSmooth",
	Key:  "prop_aa3005876b1c2907",
	Reading: "DifferentialCoordinate removes the potentially discontinuous source-chart " +
		"choice on each open coordinate cylinder. Agreement on these open cylinders makes " +
		"arbitrary inverse values and off-carrier values irrelevant to ambient smoothness.",
	Deps: []registry.EntryLike{
		TangentMapDef,
		TangentManifold,
		TangentChartInverse,
		DifferentialCoordinate,
		DifferentialTangent,
		smooth_manifold.SmoothMapCompatibleCharts,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothCompose,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothSum,
		vec_smooth.LinearSmoothMap,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)"},
		Conclusion: "smooth_manifold_map⟨2 * n, 2 * m⟩(tangent_topology⟨n⟩(T, 𝒜), " +
			"    tangent_atlas⟨n⟩(T, 𝒜), " +
			"    tangent_topology⟨m⟩(S, ℬ), " +
			"    tangent_atlas⟨m⟩(S, ℬ), " +
			"    tangent_map⟨n, m⟩(T, 𝒜, S, ℬ, f))",
	},
		"DifferentialTangent ensures that the paired map lands in the target tangent carrier. In "+
			"induced coordinates it is (y,u)↦(F(y),D F(y)u) on the open cylinder over the original "+
			"chart-preimage domain; the derivative entries are smooth, so products and finite sums make "+
			"the full expression smooth. These local chart formulas also give continuity of the bundle map."),
})}

var TangentMapIdentity = tangentMapIdentityThm{family.Add(registry.ProofEntry{
	Name: "TangentMapIdentity",
	Key:  "prop_9a305d9abf209987",
	Reading: "The identity law is stated on the tangent carrier. An " +
		"arbitrary pair with an unnormalized component function is not a tangent " +
		"vector, and the differential does not preserve such off-carrier data.",
	Deps: []registry.EntryLike{TangentMapDef, TangentBundleDef, DifferentialIdentity},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀p:prod(A, prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{"p ∈ tangent_bundle⟨n⟩(T, 𝒜)"},
		Conclusion: "tangent_map⟨n, n⟩(T, 𝒜, T, 𝒜, identity_map, p) = p",
	},
		"The first component is the original base point, and DifferentialIdentity fixes the tangent "+
			"vector in the second component. Pair extensionality gives equality on the tangent carrier."),
})}

var TangentMapCompose = tangentMapComposeThm{family.Add(registry.ProofEntry{
	Name: "TangentMapCompose",
	Key:  "prop_8d250b45da73bce3",
	Deps: []registry.EntryLike{TangentMapDef, TangentBundleDef, DifferentialCompose},
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
			"∀p:prod(A, prod(set(A), A → num → real) → num → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"smooth_manifold_map⟨m, k⟩(S, ℬ, R, 𝒞, g)",
			"p ∈ tangent_bundle⟨n⟩(T, 𝒜)",
		},
		Conclusion: "tangent_map⟨n, k⟩(T, 𝒜, R, 𝒞, g ∘ f, p) = " +
			"tangent_map⟨m, k⟩(S, ℬ, R, 𝒞, g, tangent_map⟨n, m⟩(T, 𝒜, S, ℬ, f, p))",
	},
		"The base components agree by composition of f and g. Apply "+
			"DifferentialCompose to the tangent vector over fst(p) to identify the second "+
			"components; pair extensionality gives the law on the total-space carrier."),
})}
