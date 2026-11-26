// Integration of the time contraction gives the cochain homotopy between endpoint pullbacks.

package de_rham

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var EndpointSmooth = endpointSmoothThm{family.Add(registry.ProofEntry{
	Name: "EndpointSmooth",
	Key:  "prop_37b8bdbc127f7dad",
	Deps: []registry.EntryLike{
		smooth_manifold.EuclideanManifold,
		smooth_manifold.SmoothMapIdentity,
		smooth_manifold.SmoothMapConstant,
		smooth_manifold.SmoothProductPair,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀J:set(num → real). " +
			"∀t:real.",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"J ∈ euclidean_topology(1)",
			"«time point»(t) ∈ J",
		},
		Conclusion: "smooth_manifold_map⟨n, n + 1⟩(T, " +
			"    𝒜, " +
			"    «cylinder topology», " +
			"    «cylinder atlas», " +
			"    «endpoint»(t))",
	},
		"The time point is a point of the Euclidean open time manifold. Pair the identity "+
			"map of the base with the constant map to that point, using SmoothProductPair."),
})}

var HomotopyForm = homotopyFormThm{family.Add(registry.ProofEntry{
	Name: "HomotopyForm",
	Key:  "prop_25ba43265fe2f2ad",
	Reading: "The time set is open and contains the whole unit interval in normalized " +
		"one-dimensional coordinates. Neither compact support nor compactness or orientation of " +
		"the base is required. ProductCompatibleChart applies to every compatible base chart, " +
		"including those outside the original atlas, as required for the whole normalized family.",
	Deps: []registry.EntryLike{
		HomotopyDef,
		smooth_manifold.ProductCompatibleChart, smooth_manifold.AtlasMemberCompatible,
		smooth_manifold.EuclideanManifold,
		differential_form.FormOnDef,
		vec_form.HomotopyForm,
		vec_form.HomotopyDef,
		vec_form.PullbackDef,
		real_integral.HasIntegralAdd,
		real_integral.HasIntegralScale,
		real_integral.HasIntegralValue,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀J:set(num → real). " +
			"∀ω:(prod(set(prod(A, num → real)), prod(A, num → real) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"J ∈ euclidean_topology(1)",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ «time point»(t) ∈ J",
			"manifold_form_on⟨n + 1⟩(«cylinder topology», «cylinder atlas», k + 1, ω)",
		},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, k, manifold_form_homotopy⟨n⟩(T, 𝒜, J, k, ω))",
	},
		"On every paired cylinder chart the Euclidean HomotopyForm theorem supplies a smooth "+
			"degree-k form. A base transition paired with the time identity has block Jacobian with "+
			"no time dependence in the base block: first-slot time contraction commutes with it, and "+
			"the resulting finite horizontal coefficients pass through the integral. This proves the "+
			"overlap equations; the outer guard supplies incompatible-chart normalization."),
})}

var HomotopyLinear = homotopyLinearThm{family.Add(registry.ProofEntry{
	Name: "HomotopyLinear",
	Key:  "prop_8c09bff084dcf5f6",
	Deps: []registry.EntryLike{
		HomotopyForm,
		HomotopyDef,
		differential_form.FormModule,
		vec_form.HomotopyLinear,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀J:set(num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"J ∈ euclidean_topology(1)",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ «time point»(t) ∈ J",
		},
		Conclusion: "module_homomorphism(real_ring, " +
			"    manifold_form_module⟨n + 1⟩(«cylinder topology», «cylinder atlas», k + 1), " +
			"    manifold_form_module⟨n⟩(T, 𝒜, k), " +
			"    manifold_form_homotopy⟨n⟩(T, 𝒜, J, k))",
	},
		"In each compatible base chart use the linearity of the Euclidean time-contraction "+
			"integral. The chart choice is independent of the input form, and HomotopyForm supplies "+
			"the output carrier, so these pointwise identities give the module homomorphism."),
})}

var HomotopyOperator = homotopyOperatorThm{family.Add(registry.ProofEntry{
	Name: "HomotopyOperator",
	Key:  "prop_37de48d704b66060",
	Reading: "Input degree is k+1, so dK and Kd both return that degree. Time occupies the " +
		"last coordinate but the first contraction slot, fixing the endpoint order j1 minus j0.",
	Deps: []registry.EntryLike{
		HomotopyDef,
		HomotopyForm,
		EndpointSmooth,
		differential_form.ExteriorDerivativeDef,
		differential_form.PullbackCoordinate,
		smooth_manifold.ProductCompatibleChart, smooth_manifold.AtlasMemberCompatible,
		vec_form.HomotopyOperator,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀J:set(num → real). " +
			"∀ω:(prod(set(prod(A, num → real)), prod(A, num → real) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"J ∈ euclidean_topology(1)",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ «time point»(t) ∈ J",
			"manifold_form_on⟨n + 1⟩(«cylinder topology», «cylinder atlas», k + 1, ω)",
		},
		Conclusion: "(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k, manifold_form_homotopy⟨n⟩(T, 𝒜, J, k, ω))(c, " +
			"        y, " +
			"        P) + " +
			"    manifold_form_homotopy⟨n⟩(T, " +
			"        𝒜, " +
			"        J, " +
			"        k + 1, " +
			"        manifold_exterior_derivative⟨n + 1⟩(«cylinder topology», «cylinder atlas», k + 1, ω))( " +
			"        c, y, P)) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    manifold_form_pullback⟨n, n + 1⟩(T, " +
			"        𝒜, " +
			"        «cylinder topology», " +
			"        «cylinder atlas», " +
			"        k + 1, " +
			"        «endpoint»(&1))(ω, c, y, P) - " +
			"    manifold_form_pullback⟨n, n + 1⟩(T, " +
			"        𝒜, " +
			"        «cylinder topology», " +
			"        «cylinder atlas», " +
			"        k + 1, " +
			"        «endpoint»(&0))(ω, c, y, P)",
	},
		"Work on a compatible base chart paired with the identity time chart. Apply "+
			"the Euclidean dK+Kd formula there; PullbackCoordinate identifies its two "+
			"endpoint pullbacks with the manifold endpoint maps. Both sides have the "+
			"same zero normalization at all other chart and coordinate arguments."),
})}

var HomotopyOperatorZeroDegree = homotopyOperatorZeroDegreeThm{family.Add(registry.ProofEntry{
	Name: "HomotopyOperatorZeroDegree",
	Key:  "prop_6d615bc3cf1e866a",
	Reading: "There is no dK term on a degree-zero input and no negative degree. This " +
		"is the separate bottom-degree equation required by a nonnegative cochain homotopy.",
	Deps: []registry.EntryLike{
		HomotopyDef,
		EndpointSmooth,
		differential_form.ExteriorDerivativeDef,
		differential_form.PullbackCoordinate,
		smooth_manifold.ProductCompatibleChart, smooth_manifold.AtlasMemberCompatible,
		vec_form.HomotopyOperatorZeroDegree,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀J:set(num → real). " +
			"∀ω:(prod(set(prod(A, num → real)), prod(A, num → real) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"J ∈ euclidean_topology(1)",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ «time point»(t) ∈ J",
			"manifold_form_on⟨n + 1⟩(«cylinder topology», «cylinder atlas», 0, ω)",
		},
		Conclusion: "manifold_form_homotopy⟨n⟩(T, " +
			"    𝒜, " +
			"    J, " +
			"    0, " +
			"    manifold_exterior_derivative⟨n + 1⟩(«cylinder topology», «cylinder atlas», 0, ω)) = " +
			"λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    manifold_form_pullback⟨n, n + 1⟩(T, " +
			"        𝒜, " +
			"        «cylinder topology», " +
			"        «cylinder atlas», " +
			"        0, " +
			"        «endpoint»(&1))(ω, c, y, P) - " +
			"    manifold_form_pullback⟨n, n + 1⟩(T, " +
			"        𝒜, " +
			"        «cylinder topology», " +
			"        «cylinder atlas», " +
			"        0, " +
			"        «endpoint»(&0))(ω, c, y, P)",
	},
		"Apply the degree-zero Euclidean formula in every paired chart and identify the endpoint "+
			"restrictions by PullbackCoordinate. The normalized chart families then agree everywhere."),
})}

var EndpointCochainHomotopy = endpointCochainHomotopyThm{family.Add(registry.ProofEntry{
	Name: "EndpointCochainHomotopy",
	Key:  "prop_dbec979f2f72abda",
	Reading: "The generic homotopy is between endpoint-one pullback and endpoint-zero " +
		"pullback. Its h(0) is not used by cochain_homotopy, and the conditional prevents " +
		"truncated subtraction from being interpreted as a negative-degree operator.",
	Deps: []registry.EntryLike{
		Complex,
		HomotopyLinear,
		HomotopyOperator,
		HomotopyOperatorZeroDegree,
		chain_complex.CochainHomotopyDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀J:set(num → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"J ∈ euclidean_topology(1)",
			"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ «time point»(t) ∈ J",
		},
		Conclusion: "cochain_homotopy(real_ring, " +
			"    de_rham_complex⟨n + 1⟩(«cylinder topology», «cylinder atlas»), " +
			"    de_rham_complex⟨n⟩(T, 𝒜), " +
			"    λq:num. " +
			"        manifold_form_pullback⟨n, n + 1⟩(T, " +
			"            𝒜, " +
			"            «cylinder topology», " +
			"            «cylinder atlas», " +
			"            q, " +
			"            «endpoint»(&1)), " +
			"    λq:num. " +
			"        manifold_form_pullback⟨n, n + 1⟩(T, " +
			"            𝒜, " +
			"            «cylinder topology», " +
			"            «cylinder atlas», " +
			"            q, " +
			"            «endpoint»(&0)), " +
			"    λq:num. " +
			"        COND(q = 0, " +
			"            λω:(prod(set(prod(A, num → real)), prod(A, num → real) → num → real) → " +
			"                    (num → real) → " +
			"                    (num → num → real) → " +
			"                    real). " +
			"                «zero family», " +
			"            manifold_form_homotopy⟨n⟩(T, 𝒜, J, q - 1)))",
	},
		"The generic cochain homotopy reads h(q) as a map from degree q to q-1 for q>0, so use K with "+
			"output degree q-1. HomotopyLinear gives its homomorphisms and the two homotopy-operator cards "+
			"give the successor and zero-degree equations. The unused h(0) is explicitly the zero operator."),
})}
