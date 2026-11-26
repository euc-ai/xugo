// Convex Euclidean factors contract smoothly, and their cohomology reduces to constants in degree zero.

package de_rham

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/registry"
)

var ConvexProductCohomology = convexProductCohomologyThm{family.Add(registry.ProofEntry{
	Name: "ConvexProductCohomology",
	Key:  "prop_f01b0a9018d56503",
	Reading: "No compactness or orientation is needed for either factor. The base may be empty; " +
		"U is nonempty because a is specified. The product cohomology classes live on the product " +
		"point type, so the identification is an isomorphism, not literal equality of the two modules.",
	Deps: []registry.EntryLike{
		HomotopyInvariance,
		PullbackHom,
		PullbackCompose,
		PullbackIdentity,
		PullbackCongruence,
		smooth_manifold.ConvexOpenContraction,
		smooth_manifold.SmoothProductPair,
		smooth_manifold.SmoothProductProjections,
		smooth_manifold.SmoothMapConstant,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀U:set(num → real). " +
			"∀a:(num → real). " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)", "convex(U)", "a ∈ U", "smooth_manifold⟨m⟩(T, 𝒜)"},
		Conclusion: "module_isomorphism(real_ring, " +
			"    de_rham_cohomology_module⟨m⟩(T, 𝒜, k), " +
			"    de_rham_cohomology_module⟨n + m⟩(«euclidean product topology», " +
			"        «euclidean product atlas», " +
			"        k), " +
			"    de_rham_pullback⟨n + m, m⟩(«euclidean product topology», " +
			"        «euclidean product atlas», " +
			"        T, " +
			"        𝒜, " +
			"        k, " +
			"        snd)) ∧ " +
			"(∀s:set(prod(set(prod(num → real, A)), prod(num → real, A) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"    s ∈ " +
			"    de_rham_cohomology_module⟨n + m⟩(«euclidean product topology», " +
			"        «euclidean product atlas», " +
			"        k).carrier ⇒ " +
			"    de_rham_pullback⟨n + m, m⟩(«euclidean product topology», " +
			"        «euclidean product atlas», " +
			"        T, " +
			"        𝒜, " +
			"        k, " +
			"        snd)(de_rham_pullback⟨m, n + m⟩(T, " +
			"            𝒜, " +
			"            «euclidean product topology», " +
			"            «euclidean product atlas», " +
			"            k, " +
			"            «convex section»)(s)) = " +
			"    s) ∧ " +
			"(∀t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    t ∈ de_rham_cohomology_module⟨m⟩(T, 𝒜, k).carrier ⇒ " +
			"    de_rham_pullback⟨m, n + m⟩(T, " +
			"        𝒜, " +
			"        «euclidean product topology», " +
			"        «euclidean product atlas», " +
			"        k, " +
			"        «convex section»)(de_rham_pullback⟨n + m, m⟩(«euclidean product topology», " +
			"            «euclidean product atlas», " +
			"            T, " +
			"            𝒜, " +
			"            k, " +
			"            snd)(t)) = " +
			"    t)",
	},
		"Pair the convex contraction with the identity of the second factor and rearrange the "+
			"product/time coordinates using smooth product projections and pairing. This gives a "+
			"smooth homotopy from section-after-projection to the identity on U×M, while "+
			"projection-after-section is already the identity on M. Homotopy invariance and "+
			"contravariant composition make the two displayed pullbacks inverse on their carriers."),
})}

var EmptyCohomology = emptyCohomologyThm{family.Add(registry.ProofEntry{
	Name: "EmptyCohomology",
	Key:  "prop_35b6387dbe8c5cf4",
	Reading: "The zero class is the singleton containing the zero form, not the empty set. " +
		"This handles the empty family of boxes before any nonempty convex contraction is invoked.",
	Deps: []registry.EntryLike{
		CohomologyModule,
		ClassRepresentative,
		differential_form.FormOnDef,
		vec_form.FormOnDef,
		module_dimension.FiniteCarrierFiniteDimensional,
		module_dimension.DimZero,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "⋃T = ∅"},
		Conclusion: "de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier = " +
			"{de_rham_cohomology_module⟨n⟩(T, 𝒜, k).zero} ∧ " +
			"finite_dimensional(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k)) ∧ " +
			"module_dim(real_ring, de_rham_cohomology_module⟨n⟩(T, 𝒜, k)) = 0",
	}, "Every compatible chart has empty domain, and every Euclidean component is "+
		"zero by coordinate normalization; incompatible chart components are zero too. "+
		"Thus every form is zero in every degree, giving the singleton quotient carrier. "+
		"The finite-carrier dimension theorem and the zero-dimension criterion finish."),
})}

var ConvexOpenCohomology = convexOpenCohomologyThm{family.Add(registry.ProofEntry{
	Name: "ConvexOpenCohomology",
	Key:  "prop_a8386dc88e3ef03e",
	Reading: "Positive-degree vanishing is about cohomology, not about all " +
		"forms. The empty open has dimension zero in every degree; the nonempty " +
		"zero-dimensional open has one-dimensional degree-zero cohomology.",
	Deps: []registry.EntryLike{
		EmptyCohomology,
		HomotopyInvariance,
		PullbackClass,
		PullbackIdentity,
		ClassEqualZero,
		ClassRepresentative,
		ClassScale,
		CohomologyModule,
		smooth_manifold.ConvexOpenContraction,
		smooth_manifold.EuclideanManifold,
		differential_form.FormZeroDegree,
		differential_form.WedgeUnit,
		differential_form.PullbackCoordinate,
		module_dimension.LineDim,
		module_dimension.DimZero,
		module_dimension.FiniteCarrierFiniteDimensional,
	},
	Build: family.Card(Statement{
		Binders:    "∀n k:num. ∀U:set(num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)", "convex(U)"},
		Conclusion: "finite_dimensional(real_ring, «euclidean cohomology»(U, k)) ∧ " +
			"module_dim(real_ring, «euclidean cohomology»(U, k)) = COND(U = ∅, 0, COND(k = 0, 1, 0))",
	},
		"For a nonempty U contract to a chosen point. In positive degree, pullback by the "+
			"constant map is zero because its Jacobian kills every active form column, so "+
			"every closed form is exact. In degree zero, homotopy invariance and equality of "+
			"zero-degree classes make each closed form a constant multiple of the unit, which "+
			"is nonzero on U; LineDim gives dimension one. EmptyCohomology handles U empty."),
})}
