// Base pullback commutes with fiber integration and the fiber orientation controls its sign.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var FiberIntegralNaturality = fiberIntegralNaturalityThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralNaturality",
	Key:  "prop_afad911f9f667f65",
	Reading: "The base map may be nonproper and its source dimension may " +
		"differ from the target dimension. Only the common fiber is integrated and " +
		"compact; the target base chart is fixed locally while taking the Jacobian.",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		FiberIntegralForm,
		smooth_manifold.SmoothProductPair,
		smooth_manifold.SmoothProductProjections,
		smooth_manifold.SmoothMapCompose,
		smooth_manifold.ProductCompatibleChart,
		differential_form.PullbackCoordinate,
		differential_form.PullbackForm,
		vec_form.PullbackDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real). " +
			"∀l:num. " +
			"∀R:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀f:(C → A).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
			"smooth_manifold_map⟨l, n⟩(R, 𝒞, T, 𝒜, f)",
		},
		Conclusion: "manifold_fiber_integral⟨l, m⟩(R, " +
			"    𝒞, " +
			"    S, " +
			"    ℬ, " +
			"    k, " +
			"    manifold_form_pullback⟨l + m, n + m⟩(product_topology(R, S), " +
			"        smooth_product_atlas⟨l, m⟩(𝒞, ℬ), " +
			"        product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        k + m, " +
			"        λp:prod(C, B). (f(fst(p)), snd(p)), " +
			"        ω)) = " +
			"manifold_form_pullback⟨l, n⟩(R, 𝒞, T, 𝒜, k, f, manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω))",
	},
		"Fix a source base point and a target base chart containing its image. On a base "+
			"neighbourhood, PullbackCoordinate expresses f times the fiber identity in paired charts with "+
			"a block Jacobian. The vertical slice is the target slice with the horizontal vectors pushed "+
			"forward by Df, so its integral is precisely the coordinate expression of the base pullback."),
})}

var FiberIntegralAtlasInvariant = fiberIntegralAtlasInvariantThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralAtlasInvariant",
	Key:  "prop_f71326a891173d29",
	Reading: "The product form keeps its whole compatible-chart family. Changing the positive " +
		"fiber covering atlas changes neither those smooth components nor the integration orientation.",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		FiberSliceForm,
		OrientedAtlasChange,
		IntegralAtlasInvariant,
		differential_form.SupportClosed,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀ω:(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real). " +
			"∀𝒟:set(prod(set(B), B → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"oriented_manifold⟨m⟩(S, ℬ)",
			"compact_in(S, ⋃S)",
			"manifold_form_on⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k + m, ω)",
			"oriented_manifold⟨m⟩(S, 𝒟)",
			"∀d:prod(set(B), B → num → real). d ∈ 𝒟 ⇒ positive_manifold_chart⟨m⟩(S, ℬ, d)",
		},
		Conclusion: "manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω) = " +
			"manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, 𝒟, k, ω)",
	},
		"The positive covering atlas has the same compatible fiber charts, so the normalized "+
			"slice is literally the same family for both atlases. Apply IntegralAtlasInvariant "+
			"to each compactly supported fiber slice. The invalid-base-data guards agree as well."),
})}

var FiberIntegralReverseOrientation = fiberIntegralReverseOrientationThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegralReverseOrientation",
	Key:  "prop_7d3df85ead3148a9",
	Reading: "The positivity guard is on the fiber dimension m. In dimension zero the atlas " +
		"convention makes every point positive, so this sign-reversal formula is not asserted there.",
	Deps: []registry.EntryLike{
		FiberIntegralDef,
		fiberSliceDef,
		FiberSliceForm,
		ReflectedAtlas,
		IntegralReverseOrientation,
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
			"0 < m",
		},
		Conclusion: "manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, reflected_manifold_atlas(ℬ), k, ω) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    -manifold_fiber_integral⟨n, m⟩(T, 𝒜, S, ℬ, k, ω)(c, y, P)",
	},
		"Reflection preserves all smoothly compatible fiber charts, hence it preserves each normalized "+
			"slice. The top-form integral on the reflected fiber is its negative by "+
			"IntegralReverseOrientation. Normalization gives the same equality outside the base chart domain."),
})}
