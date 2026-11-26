// Normalized functions correspond to zero-forms and act by scalar weights.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var FunctionForm = functionFormThm{family.Add(registry.ProofEntry{
	Name: "FunctionForm",
	Key:  "prop_31ba35c8ff118d99",
	Deps: []registry.EntryLike{
		FunctionFormDef,
		FormOnDef,
		smooth_manifold.SmoothFunctionDef,
		vec_form.FormZeroDegree,
		vec_form.PullbackDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → real).",
		Hypotheses: []string{"smooth_manifold_function⟨n⟩(T, 𝒜, f)"},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, 0, manifold_function_form⟨n⟩(T, 𝒜, f))",
	},
		"In each compatible chart the scalar coordinate function is smooth and matrix-independent, "+
			"so FormZeroDegree makes it a zero-form. On overlaps the inverse-chart identities give "+
			"exactly the same base value; degree-zero pullback has no vector columns."),
})}

var FormZeroDegree = formZeroDegreeThm{family.Add(registry.ProofEntry{
	Name: "FormZeroDegree",
	Key:  "prop_2e7034f114b5b2b4",
	Reading: "The unique scalar function is normalized off the base carrier. Without " +
		"that normalization zero-forms would not determine the unused exterior scalar " +
		"values. On an empty manifold every component is zero, including compatible " +
		"empty-domain components, and the unique scalar is the everywhere-zero function.",
	Deps: []registry.EntryLike{
		FunctionFormDef,
		FormOnDef,
		smooth_manifold.SmoothFunctionDef,
		smooth_manifold.AtlasDef,
		vec_form.FormZeroDegree,
		vec_form.PullbackDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"manifold_form_on⟨n⟩(T, 𝒜, 0, ω)"},
		Conclusion: "∃f:(A → real). " +
			"    smooth_manifold_function⟨n⟩(T, 𝒜, f) ∧ " +
			"    ω = manifold_function_form⟨n⟩(T, 𝒜, f) ∧ " +
			"    (∀g:(A → real). " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, g) ∧ ω = manifold_function_form⟨n⟩(T, 𝒜, g) ⇒ g = f)",
	},
		"At each carrier point read the matrix-independent zero-form value in any active chart "+
			"and put zero off the carrier. The overlap equation makes the value independent of the "+
			"chart, and the chart coefficients give scalar smoothness. The atlas cover determines "+
			"every carrier value, while scalar normalization gives uniqueness outside it."),
})}

var WeightAsWedge = weightAsWedgeThm{family.Add(registry.ProofEntry{
	Name: "WeightAsWedge",
	Key:  "prop_11477f4764e5f8d6",
	Reading: "The sole (0,k) shuffle replaces the matrix by its padded active " +
		"block. Literal equality uses the input form's independence of all matrix tails.",
	Deps: []registry.EntryLike{
		WeightDef,
		FunctionFormDef,
		WedgeDef,
		vec_form.WedgeDef,
		vec_form.FormZeroDegree,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → real). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_function⟨n⟩(T, 𝒜, f)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
		},
		Conclusion: "manifold_form_weight⟨n⟩(T, 𝒜, f, ω) = " +
			"manifold_form_wedge⟨n⟩(T, 𝒜, 0, k, manifold_function_form⟨n⟩(T, 𝒜, f), ω)",
	},
		"For degrees zero and k the shuffle sum has one split, with the empty first block. "+
			"Its zero-form factor is the base scalar value, so the wedge equals pointwise "+
			"weighting; both definitions have the same inactive-chart and exterior normalization."),
})}

var WeightForm = weightFormThm{family.Add(registry.ProofEntry{
	Name: "WeightForm",
	Key:  "prop_83bcbaabab5dce76",
	Deps: []registry.EntryLike{WeightAsWedge, FunctionForm, WedgeForm},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → real). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_function⟨n⟩(T, 𝒜, f)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
		},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, k, manifold_form_weight⟨n⟩(T, 𝒜, f, ω))",
	},
		"WeightAsWedge identifies weighting with the wedge of the corresponding "+
			"zero-form and ω. FunctionForm and WedgeForm supply the degree-k carrier."),
})}
