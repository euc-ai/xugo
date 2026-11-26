// Pullback is contravariant, linear, and preserves the wedge product
// and exterior derivative on Euclidean open sets.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var PullbackForm = pullbackFormThm{family.Add(registry.ProofEntry{
	Name: "PullbackForm",
	Key:  "prop_fde4d8e760795cfe",
	Deps: []registry.EntryLike{
		PullbackDef,
		FormOnDef,
		vec_smooth.SmoothCompose,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothAdd,
		vec_smooth.SmoothMul,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀U V:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_form_on⟨m⟩(V, k, ω)",
		},
		Conclusion: "vec_form_on⟨n⟩(U, k, vec_form_pullback⟨n, m⟩(U, k, f, ω))",
	},
		"Substitute the Jacobian action into the finite coordinate expansion and "+
			"expand its minors; the resulting coefficients are sums of products of "+
			"coefficients composed with f and partial derivatives of f. SmoothCompose and "+
			"SmoothPartial give smoothness, and the source guard gives normalization on U."),
})}

var PullbackLinear = pullbackLinearThm{family.Add(registry.ProofEntry{
	Name: "PullbackLinear",
	Key:  "prop_ebabccd56a7b28cf",
	Deps: []registry.EntryLike{PullbackForm, FormModule, PullbackDef},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. ∀U V:set(num → real). ∀f:((num → real) → num → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)", "V ∈ euclidean_topology(m)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
		},
		Conclusion: "module_homomorphism(real_ring, " +
			"    vec_form_module⟨m⟩(V, k), " +
			"    vec_form_module⟨n⟩(U, k), " +
			"    vec_form_pullback⟨n, m⟩(U, k, f))",
	},
		"Evaluation after a fixed Jacobian action commutes with pointwise "+
			"addition and scalar multiplication. PullbackForm gives the "+
			"target carrier and FormModule gives the two module structures."),
})}

var PullbackIdentity = pullbackIdentityThm{family.Add(registry.ProofEntry{
	Name: "PullbackIdentity",
	Key:  "prop_f80639affd38c74c",
	Deps: []registry.EntryLike{
		PullbackDef,
		FormOnDef,
		vec_smooth.LinearSmoothMap,
		vec_smooth.JacobianDerivative,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U:set(num → real). ∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_on⟨n⟩(U, k, ω)"},
		Conclusion: "vec_form_pullback⟨n, n⟩(U, k, λx:(num → real). x, ω) = ω",
	},
		"The identity map has identity Jacobian on the n-vectors, so the column "+
			"action gives exactly the active n×k block of the input. FormOnDef ignores "+
			"the matrix tails and makes ω zero off U, matching the pullback guard."),
})}

var PullbackCompose = pullbackComposeThm{family.Add(registry.ProofEntry{
	Name: "PullbackCompose",
	Key:  "prop_775d2be3347a31ee",
	Reading: "Both maps have explicit source open sets and image-in-domain guards. These make the " +
		"intermediate pullback's zero extension invisible near every point where its derivative is read.",
	Deps: []registry.EntryLike{
		PullbackForm,
		PullbackDef,
		vec_smooth.SmoothMapCompose,
		vec_smooth.JacobianChain,
	},
	Build: family.Card(Statement{
		Binders: "∀n m l k:num. " +
			"∀U V W:set(num → real). " +
			"∀f g:((num → real) → num → real). " +
			"∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)", "V ∈ euclidean_topology(m)",
			"vec_smooth_map_on⟨n, m⟩(U, f)", "vec_smooth_map_on⟨m, l⟩(V, g)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"∀y:(num → real). y ∈ V ⇒ g(y) ∈ W",
			"vec_form_on⟨l⟩(W, k, ω)",
		},
		Conclusion: "vec_form_pullback⟨n, m⟩(U, k, f, vec_form_pullback⟨m, l⟩(V, k, g, ω)) = " +
			"vec_form_pullback⟨n, l⟩(U, k, g ∘ f, ω)",
	},
		"At x in U the intermediate guard holds because f(x) lies in V. JacobianChain "+
			"identifies the two successive column actions with the composite Jacobian; zero "+
			"padding makes the rectangular contractions agree. Outside U both expressions are zero."),
})}

var PullbackWedge = pullbackWedgeThm{family.Add(registry.ProofEntry{
	Name: "PullbackWedge",
	Key:  "prop_b93a1dbb2f22b410",
	Deps: []registry.EntryLike{PullbackForm, WedgeForm, PullbackDef, WedgeDef},
	Build: family.Card(Statement{
		Binders: "∀n m p q:num. " +
			"∀U V:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀α β:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)", "vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_form_on⟨m⟩(V, p, α)", "vec_form_on⟨m⟩(V, q, β)",
		},
		Conclusion: "vec_form_pullback⟨n, m⟩(U, p + q, f, vec_form_wedge⟨m⟩(V, p, q, α, β)) = " +
			"vec_form_wedge⟨n⟩(U, " +
			"    p, " +
			"    q, " +
			"    vec_form_pullback⟨n, m⟩(U, p, f, α), " +
			"    vec_form_pullback⟨n, m⟩(U, q, f, β))",
	},
		"Applying a fixed linear map to the columns commutes with selecting the "+
			"two shuffle blocks. Thus the finite signed sums agree term by term inside "+
			"U; the image guard supplies f(x) in V and both sides vanish outside U."),
})}

var PullbackExteriorDerivative = pullbackExteriorDerivativeThm{family.Add(registry.ProofEntry{
	Name: "PullbackExteriorDerivative",
	Key:  "prop_7b2106aebab1e77c",
	Deps: []registry.EntryLike{
		PullbackForm,
		ExteriorDerivativeForm,
		PullbackDef,
		ExteriorDerivativeDef,
		vec_smooth.PartialDerivativeChain,
		vec_smooth.PartialDerivativeSymmetric,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀U V:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)", "vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_form_on⟨m⟩(V, k, ω)",
		},
		Conclusion: "vec_form_pullback⟨n, m⟩(U, k + 1, f, vec_exterior_derivative⟨m⟩(V, k, ω)) = " +
			"vec_exterior_derivative⟨n⟩(U, k, vec_form_pullback⟨n, m⟩(U, k, f, ω))",
	},
		"Differentiate the coordinate formula for pullback. Chain-rule terms differentiating "+
			"the coefficients give f*(dω), while terms differentiating the Jacobian cancel in "+
			"opposite-sign pairs by equality of mixed partials of f. The open-domain image "+
			"guards justify the local formulas, and the normalized expressions agree off U."),
})}
