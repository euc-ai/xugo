// Chartwise immersion is exactly injectivity of every tangent differential.

package tangent

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

var ImmersionDifferentialIff = immersionDifferentialIffThm{family.Add(registry.ProofEntry{
	Name: "ImmersionDifferentialIff",
	Key:  "prop_e3f786ba7dfc4dec",
	Reading: "Injectivity is on the tangent carrier, not on all " +
		"chart-indexed functions. Empty carriers make both derivative criteria " +
		"vacuous, and zero-dimensional tangent carriers are singletons.",
	Deps: []registry.EntryLike{
		smooth_manifold.ImmersionDef,
		TangentChartIsomorphism,
		DifferentialCoordinate,
		DifferentialTangent,
		TangentChartReconstruct,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
		},
		Conclusion: "smooth_manifold_immersion⟨n, m⟩(T, 𝒜, S, ℬ, f) ⇔ " +
			"(∀x:A. " +
			"    x ∈ ⋃T ⇒ " +
			"    injective_on(tangent_module⟨n⟩(T, 𝒜, x).carrier, " +
			"        manifold_differential⟨n, m⟩(T, 𝒜, S, ℬ, f, x)))",
	},
		"At a source point and its image, TangentChartIsomorphism identifies tangent vectors with "+
			"normalized coordinate vectors. DifferentialCoordinate identifies the conjugated map with "+
			"the coordinate Jacobian, so its injectivity is equivalent in the two descriptions."),
})}
