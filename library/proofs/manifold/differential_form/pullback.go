// The local coordinate formula removes the pointwise target-chart
// choice and gives contravariance, linearity and naturality.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var PullbackCoordinate = pullbackCoordinateThm{family.Add(registry.ProofEntry{
	Name: "PullbackCoordinate",
	Key:  "prop_3d984dd2b46e7b9e",
	Reading: "Only the chosen open coordinate region V must map into the fixed target " +
		"chart. There is no requirement that the image of the entire source chart fit into " +
		"one target chart. At each point, continuity gives an open source neighbourhood " +
		"mapping into the intersection of the selected and fixed target charts; coordinate " +
		"agreement there gives Jacobian agreement at that point. Both sides are normalized " +
		"outside V, so the equality is between total Euclidean form functions.",
	Deps: []registry.EntryLike{
		PullbackDef,
		FormOnDef,
		smooth_manifold.SmoothMapCompatibleCharts,
		smooth_manifold.CompatibleTransition,
		vec_form.PullbackCompose,
		vec_form.FormRestrict,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀d:prod(set(B), B → num → real). " +
			"∀V:set(num → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"manifold_form_on⟨m⟩(S, ℬ, k, ω)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"compatible_chart⟨m⟩(S, ℬ, d)",
			"V ∈ euclidean_topology(n)",
			"V ⊆ «chart image»(c)",
			"∀y:(num → real). y ∈ V ⇒ f(inverse_on(fst(c), snd(c), y)) ∈ fst(d)",
		},
		Conclusion: "normalize_on(V, " +
			"    λP:(num → num → real). &0, " +
			"    manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω, c)) = " +
			"vec_form_pullback⟨n, m⟩(V, k, «coordinate map»(c, d, f), ω(d))",
	},
		"At any y in V the definition's target chart and d both contain the image point. On "+
			"an open neighbourhood their coordinate expressions differ by a target transition; "+
			"the target form's compatibility equation and Euclidean PullbackCompose identify "+
			"their pullback values, using local derivative agreement for the coordinate maps. "+
			"This proves equality at every point of V, and normalization proves it elsewhere."),
})}

var PullbackForm = pullbackFormThm{family.Add(registry.ProofEntry{
	Name: "PullbackForm",
	Key:  "prop_2d72d61329b50d5f",
	Deps: []registry.EntryLike{
		PullbackCoordinate,
		PullbackDef,
		FormOnDef,
		smooth_manifold.SmoothMapCompatibleCharts,
		vec_form.FormLocal,
		vec_form.PullbackForm,
		vec_form.PullbackCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"manifold_form_on⟨m⟩(S, ℬ, k, ω)",
		},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, k, manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω))",
	},
		"Continuity and the target chart cover give an open source-coordinate neighbourhood mapping "+
			"into one target chart at each point. PullbackCoordinate and Euclidean PullbackForm give a "+
			"local form there; FormLocal and the defining normalization give a form on the whole source "+
			"image. On source-chart overlaps, choose a common target chart locally and use PullbackCompose "+
			"to obtain compatibility pointwise; incompatible source charts are already zero."),
})}

var PullbackLinear = pullbackLinearThm{family.Add(registry.ProofEntry{
	Name: "PullbackLinear",
	Key:  "prop_d8002f6c62e5cca1",
	Reading: "The selected target chart is independent of the input form and its degree. Addition " +
		"and scalar multiplication therefore evaluate through exactly the same chart and Jacobian.",
	Deps: []registry.EntryLike{PullbackForm, FormModule, PullbackDef, vec_form.PullbackDef},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)"},
		Conclusion: "module_homomorphism(real_ring, " +
			"    manifold_form_module⟨m⟩(S, ℬ, k), " +
			"    manifold_form_module⟨n⟩(T, 𝒜, k), " +
			"    manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f))",
	},
		"The selected target chart depends on f, the source chart and the point, but not on the input "+
			"form. Evaluation after the same Jacobian action therefore respects pointwise addition and real "+
			"scaling. PullbackForm supplies the carrier condition and FormModule supplies both modules."),
})}

var PullbackIdentity = pullbackIdentityThm{family.Add(registry.ProofEntry{
	Name: "PullbackIdentity",
	Key:  "prop_a11fb403c655c06e",
	Deps: []registry.EntryLike{
		PullbackCoordinate,
		PullbackDef,
		FormOnDef,
		smooth_manifold.SmoothMapIdentity,
		vec_form.PullbackIdentity,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, k, ω)"},
		Conclusion: "manifold_form_pullback⟨n, n⟩(T, 𝒜, T, 𝒜, k, identity_map, ω) = ω",
	},
		"For each compatible source chart choose that same chart as the fixed target in "+
			"PullbackCoordinate on the full coordinate image. The coordinate expression agrees "+
			"locally with the identity, so Euclidean PullbackIdentity recovers the component. "+
			"Both families vanish on incompatible charts and outside the coordinate images."),
})}

var PullbackCompose = pullbackComposeThm{family.Add(registry.ProofEntry{
	Name: "PullbackCompose",
	Key:  "prop_4ffbc6d63e610891",
	Deps: []registry.EntryLike{
		PullbackCoordinate,
		PullbackForm,
		PullbackDef,
		smooth_manifold.SmoothMapCompose,
		vec_form.PullbackCompose,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n m l k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀R:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀ω:(prod(set(C), C → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"smooth_manifold_map⟨m, l⟩(S, ℬ, R, 𝒞, g)",
			"manifold_form_on⟨l⟩(R, 𝒞, k, ω)",
		},
		Conclusion: "manifold_form_pullback⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    k, " +
			"    f, " +
			"    manifold_form_pullback⟨m, l⟩(S, ℬ, R, 𝒞, k, g, ω)) = " +
			"manifold_form_pullback⟨n, l⟩(T, 𝒜, R, 𝒞, k, g ∘ f, ω)",
	},
		"Choose charts around a source point and its two successive images, then restrict to open "+
			"chart-preimage neighbourhoods on which both coordinate maps compose. PullbackCoordinate "+
			"turns both sides into Euclidean pullbacks there; Euclidean PullbackCompose and local "+
			"coordinate agreement identify them. Since this holds at every source coordinate point "+
			"and both sides have the same zero normalization, it gives global contravariance."),
})}

var PullbackWedge = pullbackWedgeThm{family.Add(registry.ProofEntry{
	Name: "PullbackWedge",
	Key:  "prop_6b2547453014383c",
	Deps: []registry.EntryLike{
		PullbackCoordinate,
		PullbackForm,
		WedgeForm,
		WedgeDef,
		vec_form.PullbackWedge,
	},
	Build: family.Card(Statement{
		Binders: "∀n m p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀α β:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"manifold_form_on⟨m⟩(S, ℬ, p, α)",
			"manifold_form_on⟨m⟩(S, ℬ, q, β)",
		},
		Conclusion: "manifold_form_pullback⟨n, m⟩(T, " +
			"    𝒜, " +
			"    S, " +
			"    ℬ, " +
			"    p + q, " +
			"    f, " +
			"    manifold_form_wedge⟨m⟩(S, ℬ, p, q, α, β)) = " +
			"manifold_form_wedge⟨n⟩(T, " +
			"    𝒜, " +
			"    p, " +
			"    q, " +
			"    manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, p, f, α), " +
			"    manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, q, f, β))",
	},
		"Near each source coordinate point use the same fixed target chart for both "+
			"factors and their product. PullbackCoordinate reduces the equation to Euclidean "+
			"PullbackWedge on that open region. The wedge and pullback normalizations agree "+
			"everywhere outside those coordinate domains and on incompatible charts."),
})}

var PullbackExteriorDerivative = pullbackExteriorDerivativeThm{family.Add(registry.ProofEntry{
	Name: "PullbackExteriorDerivative",
	Key:  "prop_ac806658aaa4f521",
	Reading: "The target-chart choice is replaced by a fixed chart on an open neighbourhood before " +
		"differentiating. Differentiating the epsilon choice itself is neither required nor justified.",
	Deps: []registry.EntryLike{
		PullbackCoordinate,
		PullbackForm,
		ExteriorDerivativeForm,
		ExteriorDerivativeDef,
		vec_form.PullbackExteriorDerivative,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"manifold_form_on⟨m⟩(S, ℬ, k, ω)",
		},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, " +
			"    𝒜, " +
			"    k, " +
			"    manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω)) = " +
			"manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k + 1, f, manifold_exterior_derivative⟨m⟩(S, ℬ, k, ω))",
	},
		"Choose a fixed target chart on an open source-coordinate neighbourhood and use "+
			"PullbackCoordinate for the form and its derivative. Derivative locality permits differentiation "+
			"of this fixed-chart formula, and Euclidean PullbackExteriorDerivative gives the equality there. "+
			"All coordinate points are covered, and zero normalization finishes the equality of families."),
})}
