// The wedge of closed forms descends to a unital graded-commutative product on cohomology.

package de_rham_product

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/registry"
)

var WedgeClassCongruence = wedgeClassCongruenceThm{family.Add(registry.ProofEntry{
	Name: "WedgeClassCongruence",
	Key:  "prop_67f1f5396737dd65",
	Reading: "Both factors must be closed. A class equality in degree zero is literal equality of " +
		"its closed form representatives; truncating a primitive degree would give the wrong argument.",
	Deps: []registry.EntryLike{
		de_rham.ClassEqualSucc,
		de_rham.ClassEqualZero,
		differential_form.WedgeForm,
		differential_form.WedgeBilinear,
		differential_form.ExteriorDerivativeLeibniz,
		differential_form.ExteriorDerivativeLinear,
	},
	Build: family.Card(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α α' β β':(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, p, α)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, p, α) = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"manifold_form_on⟨n⟩(T, 𝒜, p, α')",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, p, α') = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"manifold_form_on⟨n⟩(T, 𝒜, q, β)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, q, β) = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"manifold_form_on⟨n⟩(T, 𝒜, q, β')",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, q, β') = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"de_rham_class⟨n⟩(T, 𝒜, p, α) = de_rham_class⟨n⟩(T, 𝒜, p, α')",
			"de_rham_class⟨n⟩(T, 𝒜, q, β) = de_rham_class⟨n⟩(T, 𝒜, q, β')",
		},
		Conclusion: "de_rham_class⟨n⟩(T, 𝒜, p + q, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β)) = " +
			"de_rham_class⟨n⟩(T, 𝒜, p + q, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α', β'))",
	},
		"Change one representative at a time. In positive first degree write α−α'=dη and use "+
			"d(η∧β)=dη∧β; in positive second degree use the primitive (-1)^p α'∧θ for α'∧dθ. In "+
			"degree zero equal classes give equal forms, so no negative-degree primitive is used."),
})}

var WedgeClass = wedgeClassThm{family.Add(registry.ProofEntry{
	Name: "WedgeClass",
	Key:  "prop_e4b864e30f50fcd4",
	Deps: []registry.EntryLike{
		WedgeDef,
		WedgeClassCongruence,
		de_rham.ClassMember,
		de_rham.ClassRepresentative,
	},
	Build: family.Card(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, p, α)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, p, α) = de_rham_complex⟨n⟩(T, 𝒜).zero",
			"manifold_form_on⟨n⟩(T, 𝒜, q, β)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, q, β) = de_rham_complex⟨n⟩(T, 𝒜).zero",
		},
		Conclusion: "de_rham_wedge⟨n⟩(T, " +
			"    𝒜, " +
			"    p, " +
			"    q, " +
			"    de_rham_class⟨n⟩(T, 𝒜, p, α), " +
			"    de_rham_class⟨n⟩(T, 𝒜, q, β)) = " +
			"de_rham_class⟨n⟩(T, 𝒜, p + q, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β))",
	},
		"The given closed forms and the definition’s chosen forms represent the same "+
			"classes. WedgeClassCongruence replaces both choices by the given representatives. "+
			"The resulting formula is independent of every representative selection."),
})}

var WedgeBilinear = wedgeBilinearThm{family.Add(registry.ProofEntry{
	Name: "WedgeBilinear",
	Key:  "prop_fef59a4a0079e3f5",
	Reading: "Bilinearity is on the two degree carriers, with target " +
		"degree p+q. In particular multiplication by either zero class " +
		"vanishes, including empty manifolds and degrees above dimension.",
	Deps: []registry.EntryLike{
		WedgeClass,
		de_rham.ClassRepresentative,
		de_rham.ClassMember,
		de_rham.ClassAdd,
		de_rham.ClassScale,
		de_rham.CohomologyModule,
		differential_form.WedgeBilinear,
		differential_form.ExteriorDerivativeLeibniz,
		module_homomorphism.BilinearMapOfClauses,
	},
	Build: family.Card(Statement{
		Binders:    "∀n p q:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "bilinear_map(real_ring, " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, p), " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, q), " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, p + q), " +
			"    de_rham_wedge⟨n⟩(T, 𝒜, p, q))",
	},
		"Choose closed representatives. The Leibniz rule makes their wedge closed; pointwise "+
			"wedge bilinearity and the class addition/scaling laws descend to the quotient. "+
			"BilinearMapOfClauses packages carrier preservation and linearity in both arguments."),
})}

var WedgeAssociative = wedgeAssociativeThm{family.Add(registry.ProofEntry{
	Name: "WedgeAssociative",
	Key:  "prop_a608431722d3d32f",
	Deps: []registry.EntryLike{
		WedgeClass,
		de_rham.ClassRepresentative,
		differential_form.WedgeAssociative,
		differential_form.WedgeForm,
		differential_form.ExteriorDerivativeLeibniz,
	},
	Build: family.Card(Statement{
		Binders: "∀n p q r:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀s t u:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier",
			"t ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, q).carrier",
			"u ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, r).carrier",
		},
		Conclusion: "de_rham_wedge⟨n⟩(T, 𝒜, p + q, r, de_rham_wedge⟨n⟩(T, 𝒜, p, q, s, t), u) = " +
			"de_rham_wedge⟨n⟩(T, 𝒜, p, q + r, s, de_rham_wedge⟨n⟩(T, 𝒜, q, r, t, u))",
	},
		"Choose closed representatives of all three classes. Their intermediate "+
			"wedges are closed forms, so WedgeClass applies twice on either side. "+
			"Form-level associativity and equality of the total degrees give the result."),
})}

var WedgeGradedCommutative = wedgeGradedCommutativeThm{family.Add(registry.ProofEntry{
	Name:    "WedgeGradedCommutative",
	Key:     "prop_a3a29ec9f1dde88c",
	Reading: "The sign depends on the form degrees, not the manifold dimension or an orientation.",
	Deps: []registry.EntryLike{
		WedgeClass,
		de_rham.ClassRepresentative,
		de_rham.ClassScale,
		differential_form.WedgeGradedCommutative,
		differential_form.WedgeForm,
		differential_form.ExteriorDerivativeLeibniz,
	},
	Build: family.Card(Statement{
		Binders: "∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀s t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier",
			"t ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, q).carrier",
		},
		Conclusion: "de_rham_wedge⟨n⟩(T, 𝒜, p, q, s, t) = " +
			"de_rham_cohomology_module⟨n⟩(T, 𝒜, p + q).smul((-&1)^(p * q), de_rham_wedge⟨n⟩(T, 𝒜, q, p, t, s))",
	},
		"Apply the shuffle sign (-1)^(pq) to closed representatives and pass scalar "+
			"multiplication through ClassScale. Degree addition identifies the two target modules."),
})}

var WedgeUnit = wedgeUnitThm{family.Add(registry.ProofEntry{
	Name: "WedgeUnit",
	Key:  "prop_68457aa77eef4b69",
	Reading: "On an empty manifold the unit form is zero and its cohomology " +
		"unit equals the zero class. The statement does not assert a nonzero unit.",
	Deps: []registry.EntryLike{
		WedgeClass,
		de_rham.ClassRepresentative,
		de_rham.ClassMember,
		differential_form.FormModule,
		differential_form.WedgeUnit,
		differential_form.ExteriorDerivativeForm,
		differential_form.ExteriorDerivativeLeibniz,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier",
		},
		Conclusion: "de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)) ∈ " +
			"de_rham_cohomology_module⟨n⟩(T, 𝒜, 0).carrier ∧ " +
			"de_rham_wedge⟨n⟩(T, 𝒜, 0, k, de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)), s) = s ∧ " +
			"de_rham_wedge⟨n⟩(T, 𝒜, k, 0, s, de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜))) = s",
	},
		"The normalized form unit is a zero-form. Differentiating 1∧1=1 with Leibniz "+
			"and the two unit laws gives d1=d1+d1, hence d1=0. Its class is therefore "+
			"defined in degree zero, and the form unit laws descend by WedgeClass."),
})}

var PullbackWedge = pullbackWedgeThm{family.Add(registry.ProofEntry{
	Name: "PullbackWedge",
	Key:  "prop_5fd249621665fdf0",
	Deps: []registry.EntryLike{
		WedgeClass,
		de_rham.ClassRepresentative,
		de_rham.PullbackClass,
		differential_form.PullbackWedge,
		differential_form.PullbackForm,
		differential_form.PullbackExteriorDerivative,
	},
	Build: family.Card(Statement{
		Binders: "∀n m p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀s t:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"s ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, p).carrier",
			"t ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, q).carrier",
		},
		Conclusion: "de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, p + q, f)(de_rham_wedge⟨m⟩(S, ℬ, p, q, s, t)) = " +
			"de_rham_wedge⟨n⟩(T, " +
			"    𝒜, " +
			"    p, " +
			"    q, " +
			"    de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, p, f)(s), " +
			"    de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, q, f)(t))",
	},
		"Choose closed target representatives. Smooth pullback preserves their form degrees and "+
			"closedness, so PullbackClass and WedgeClass reduce the equation to form-level PullbackWedge."),
})}

var PullbackUnit = pullbackUnitThm{family.Add(registry.ProofEntry{
	Name: "PullbackUnit",
	Key:  "prop_ffb15320dc5e2b72",
	Reading: "Source and target may have different dimensions or be empty. The " +
		"smooth-map condition includes both manifold structures and carrier containment.",
	Deps: []registry.EntryLike{
		WedgeUnit,
		de_rham.CohomologyModule,
		de_rham.PullbackClass,
		differential_form.PullbackCoordinate,
		differential_form.UnitDef,
		differential_form.ExteriorDerivativeLeibniz,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)"},
		Conclusion: "de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, 0, f)( " +
			"    de_rham_class⟨m⟩(S, ℬ, 0, manifold_form_unit⟨m⟩(S, ℬ))) = " +
			"de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜))",
	},
		"The unit is closed by the Leibniz and unit identities. In each compatible "+
			"source chart its degree-zero pullback has coefficient one on the coordinate "+
			"domain, since the smooth map lands in the target carrier; normalization "+
			"gives zero elsewhere. PullbackClass gives the asserted equality."),
})}
