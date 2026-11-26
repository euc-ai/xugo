// Positive-chart Euler data determine one global normalized form, including its degenerate cases.

package riemannian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var EulerRepresentativeExistsUnique = eulerRepresentativeExistsUniqueThm{family.Add(registry.ProofEntry{
	Name: "EulerRepresentativeExistsUnique",
	Key:  "prop_7bb55b3fc814afb1",
	Deps: []registry.EntryLike{
		eulerRepresentativeDef,
		PositiveFrameExists,
		LocalEulerForm,
		LocalEulerFrameIndependent,
		LocalEulerOverlap,
		form_integral.AtlasMemberPositive,
		differential_form.FormAtlasExtension,
		differential_form.FormExt,
		differential_form.FormOnDef,
	},
	Reading: "The original oriented atlas covers the manifold and supplies positive " +
		"charts. Extension assigns components on all compatible charts, including " +
		"orientation-reversing or disconnected charts; only incompatible charts are " +
		"zeroed. Empty chart domains and the empty manifold require no separate choice data.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "riemannian_metric⟨n⟩(T, 𝒜, g)"},
		Conclusion: "∃ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    riemannian_euler_representative⟨n⟩(T, 𝒜, g, ω) ∧ " +
			"    (∀η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        riemannian_euler_representative⟨n⟩(T, 𝒜, g, η) ⇒ η = ω)",
	},
		"Choose a positive frame on each original atlas chart; local form "+
			"membership and positive-overlap equality supply FormAtlasExtension. Cover "+
			"each additional positive chart by overlaps with the original atlas to "+
			"recover its local Pfaffian for every frame, while FormExt gives uniqueness."),
})}

var EulerForm = eulerFormThm{family.Add(registry.ProofEntry{
	Name: "EulerForm",
	Key:  "prop_359535cd81f94f5a",
	Deps: []registry.EntryLike{EulerFormDef, eulerRepresentativeDef, EulerRepresentativeExistsUnique},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "riemannian_metric⟨n⟩(T, 𝒜, g)"},
		Conclusion: "manifold_form_on⟨n⟩(T, 𝒜, n, riemannian_euler_form⟨n⟩(T, 𝒜, g))",
	},
		"The guarded choice in EulerFormDef selects an Euler representative by existence "+
			"and uniqueness. Its defining form conjunct gives the normalized global n-form."),
})}

var EulerPositiveChart = eulerPositiveChartThm{family.Add(registry.ProofEntry{
	Name: "EulerPositiveChart",
	Key:  "prop_fa7a4cb0d2fab3c9",
	Deps: []registry.EntryLike{EulerFormDef, eulerRepresentativeDef, EulerRepresentativeExistsUnique},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
		},
		Conclusion: "riemannian_euler_form⟨n⟩(T, 𝒜, g)(c) = riemannian_local_euler_form⟨n⟩(g, c, E)",
	},
		"The chosen representative satisfies its chart equation for every positive chart and every "+
			"positive frame there. PositiveFrameDef supplies the metric premise needed for the choice guard."),
})}

var EulerClosed = eulerClosedThm{family.Add(registry.ProofEntry{
	Name: "EulerClosed",
	Key:  "prop_1e5c058cc09cb01",
	Reading: "A dimension count: an n-form on an n-manifold has an exterior " +
		"derivative of degree above the dimension. Nothing of the curvature is read.",
	Deps: []registry.EntryLike{
		EulerForm,
		differential_form.ExteriorDerivativeForm,
		differential_form.FormAboveDimension,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "riemannian_metric⟨n⟩(T, 𝒜, g)"},
		Conclusion: "manifold_exterior_derivative⟨n⟩(T, 𝒜, n, riemannian_euler_form⟨n⟩(T, 𝒜, g)) = " +
			"(λc:prod(set(A), A → num → real). «zero»)",
	},
		"EulerForm makes the Euler form a manifold n-form. Its exterior derivative is an "+
			"(n+1)-form by ExteriorDerivativeForm, hence the zero family by FormAboveDimension."),
})}

var EulerOdd = eulerOddThm{family.Add(registry.ProofEntry{
	Name: "EulerOdd",
	Key:  "prop_a2dbd8c89dfd0cdf",
	Deps: []registry.EntryLike{
		EulerForm,
		EulerPositiveChart,
		localEulerDef,
		PositiveFrameExists,
		form_integral.AtlasMemberPositive,
		vec_form.PfaffianOdd,
		differential_form.FormExt,
		differential_form.FormModule,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "riemannian_metric⟨n⟩(T, 𝒜, g)", "¬nat_even(n)"},
		Conclusion: "riemannian_euler_form⟨n⟩(T, 𝒜, g) = (λc:prod(set(A), A → num → real). «zero»)",
	},
		"On each original positive chart the odd-order Pfaffian is zero, regardless of the "+
			"chosen frame. FormExt then identifies the global Euler form with the zero family."),
})}

var EulerZeroDimension = eulerZeroDimensionThm{family.Add(registry.ProofEntry{
	Name: "EulerZeroDimension",
	Key:  "prop_f611b3b7d8da9ab9",
	Deps: []registry.EntryLike{
		MetricDef,
		EulerForm,
		EulerPositiveChart,
		localEulerDef,
		PositiveFrameExists,
		form_integral.OrientedZeroDimension,
		vec_form.PfaffianEmpty,
		differential_form.UnitDef,
		differential_form.WedgeUnit,
		differential_form.FormExt,
	},
	Reading: "This uses the canonical positive orientation encoded by zero-dimensional " +
		"atlases. On an empty manifold the normalized unit is itself the zero family.",
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real).",
		Hypotheses: []string{"riemannian_metric⟨0⟩(T, 𝒜, g)"},
		Conclusion: "riemannian_euler_form⟨0⟩(T, 𝒜, g) = manifold_form_unit⟨0⟩(T, 𝒜)",
	},
		"Every zero-dimensional smooth atlas is oriented and every compatible chart "+
			"is positive. The empty Pfaffian is the normalized unit, independent of "+
			"curvature entries, so the global form equals the manifold zero-form unit."),
})}
