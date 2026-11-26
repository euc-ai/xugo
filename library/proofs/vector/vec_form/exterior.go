// The exterior derivative raises degree, is linear, squares to zero,
// and is a derivation of the shuffle product with the degree sign.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ExteriorDerivativeForm = exteriorDerivativeFormThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeForm",
	Key:  "prop_3053fcf25286031d",
	Deps: []registry.EntryLike{
		ExteriorDerivativeDef,
		FormOnDef,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothAdd,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, k, ω)"},
		Conclusion: "vec_form_on⟨n⟩(U, k + 1, vec_exterior_derivative⟨n⟩(U, k, ω))",
	},
		"Differentiate the finite coordinate expansion. The new coefficients are alternating sums "+
			"of first partials of the old ones, hence smooth by SmoothPartial; the column formula is "+
			"their increasing-minor expansion. The outer guard supplies zero normalization."),
})}

var ExteriorDerivativeLinear = exteriorDerivativeLinearThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeLinear",
	Key:  "prop_3ca997452f9fc62c",
	Deps: []registry.EntryLike{
		ExteriorDerivativeForm,
		FormModule,
		vec_smooth.PartialDerivativeAdd,
		vec_smooth.PartialDerivativeMul,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U:set(num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)"},
		Conclusion: "module_homomorphism(real_ring, " +
			"    vec_form_module⟨n⟩(U, k), " +
			"    vec_form_module⟨n⟩(U, k + 1), " +
			"    vec_exterior_derivative⟨n⟩(U, k))",
	},
		"PartialDerivativeAdd and the constant-scalar case of PartialDerivativeMul "+
			"pass through the finite signed sums in the definition. ExteriorDerivativeForm "+
			"supplies closure and FormModule supplies the source and target modules."),
})}

var ExteriorDerivativeSquareZero = exteriorDerivativeSquareZeroThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeSquareZero",
	Key:  "prop_fec99a8eef0aad62",
	Reading: "Both derivatives are normalized on the same open U. Smoothness is used for equality of " +
		"mixed partials inside U, while the outer guard gives equality with zero at every point outside U.",
	Deps: []registry.EntryLike{
		ExteriorDerivativeForm,
		ExteriorDerivativeDef,
		vec_smooth.PartialDerivativeSymmetric,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, k, ω)"},
		Conclusion: "vec_exterior_derivative⟨n⟩(U, k + 1, vec_exterior_derivative⟨n⟩(U, k, ω)) = «zero»",
	},
		"In each coordinate coefficient, the terms deleting two distinct positions come in pairs "+
			"with opposite signs. Their mixed second partials agree by PartialDerivativeSymmetric, so "+
			"the coefficient vanishes; the normalized coordinate expansion gives equality everywhere."),
})}

var ExteriorDerivativeLeibniz = exteriorDerivativeLeibnizThm{family.Add(registry.ProofEntry{
	Name: "ExteriorDerivativeLeibniz",
	Key:  "prop_d083a47b890b848a",
	Deps: []registry.EntryLike{
		WedgeForm,
		ExteriorDerivativeForm,
		WedgeDef,
		ExteriorDerivativeDef,
		vec_smooth.PartialDerivativeMul,
	},
	Build: family.Card(Statement{
		Binders:    "∀n p q:num. ∀U:set(num → real). ∀α β:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, p, α)", "vec_form_on⟨n⟩(U, q, β)"},
		Conclusion: "vec_exterior_derivative⟨n⟩(U, p + q, vec_form_wedge⟨n⟩(U, p, q, α, β)) = " +
			"(λx:(num → real). λP:(num → num → real). " +
			"    vec_form_wedge⟨n⟩(U, p + 1, q, vec_exterior_derivative⟨n⟩(U, p, α), β, x, P) + " +
			"    (-&1)^p * vec_form_wedge⟨n⟩(U, p, q + 1, α, vec_exterior_derivative⟨n⟩(U, q, β), x, P))",
	},
		"Differentiate each shuffle summand with PartialDerivativeMul. Terms "+
			"differentiating α form dα∧β; moving the differentiating slot past the p slots of "+
			"α gives (-1)^p for the terms forming α∧dβ. All three expressions vanish off U."),
})}
