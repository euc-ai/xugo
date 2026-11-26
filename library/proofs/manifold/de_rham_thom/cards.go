package de_rham_thom

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/projection_geometry"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var ThomForm = thomFormThm{family.Add(registry.ProofEntry{
	Name: "ThomForm",
	Key:  "prop_84d62507196cad0a",
	Deps: []registry.EntryLike{projection_geometry.FiberIntegralExistsUnique},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
		},
		Conclusion: "manifold_form_on⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"    projection_total_atlas(n, r, T, 𝒜, P), " +
			"    2 * r, " +
			"    projection_thom_form(n, r, T, 𝒜, P)) ∧ " +
			"projection_fiber_proper(n, r, T, 𝒜, P, projection_thom_form(n, r, T, 𝒜, P)) ∧ " +
			"manifold_exterior_derivative⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"    projection_total_atlas(n, r, T, 𝒜, P), " +
			"    2 * r, " +
			"    projection_thom_form(n, r, T, 𝒜, P)) = " +
			"(λc:prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real). " +
			"λy:(num → real). " +
			"λV:(num → num → real). " +
			"    &0) ∧ " +
			"projection_fiber_integral(n, r, T, 𝒜, P, 0, projection_thom_form(n, r, T, 𝒜, P)) = " +
			"manifold_form_unit⟨n⟩(T, 𝒜)",
	},
		"Choose normalized radial compact forms in local unitary frames. The relative de Rham "+
			"gluing construction corrects their differences by compact fibre primitives and gives "+
			"a closed global form; proper support is controlled over each compact base subset."),
})}

var ThomHomomorphism = thomHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "ThomHomomorphism",
	Key:  "prop_4a6958b5f0d47435",
	Deps: []registry.EntryLike{ThomForm},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
		},
		Conclusion: "module_homomorphism(real_ring, " +
			"    compact_de_rham_module(n, T, 𝒜, k), " +
			"    compact_de_rham_module(n + 2 * r, " +
			"        projection_total_topology(T, P), " +
			"        projection_total_atlas(n, r, T, 𝒜, P), " +
			"        k + 2 * r), " +
			"    compact_de_rham_thom(n, r, T, 𝒜, P, k))",
	},
		"The wedge has support in the fibre-proper Thom support over a compact base "+
			"support. Closedness and Leibniz make the map descend through compact coboundaries."),
})}

var FiberHomomorphism = fiberHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "FiberHomomorphism",
	Key:  "prop_a24699e71423813e",
	Deps: []registry.EntryLike{
		projection_geometry.FiberIntegralCompact,
		projection_geometry.FiberIntegralDifferential,
		projection_geometry.FiberIntegralStokes,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
		},
		Conclusion: "module_homomorphism(real_ring, " +
			"    compact_de_rham_module(n + 2 * r, " +
			"        projection_total_topology(T, P), " +
			"        projection_total_atlas(n, r, T, 𝒜, P), " +
			"        k + 2 * r), " +
			"    compact_de_rham_module(n, T, 𝒜, k), " +
			"    compact_de_rham_fiber(n, r, T, 𝒜, P, k))",
	},
		"Fibre integration commutes with d in even fibre dimension and sends compact support "+
			"to compact support. At degree zero a coboundary has a primitive of degree one below "+
			"the fibre dimension, whose fibre integral vanishes by FiberIntegralStokes."),
})}

var ThomLeftInverse = thomLeftInverseThm{family.Add(registry.ProofEntry{
	Name: "ThomLeftInverse",
	Key:  "prop_f8d615b76bea23a9",
	Deps: []registry.EntryLike{ThomHomomorphism, FiberHomomorphism, FiberProjectionFormula},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"a ∈ (compact_de_rham_module(n, T, 𝒜, k)).carrier",
		},
		Conclusion: "compact_de_rham_fiber(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    k, " +
			"    compact_de_rham_thom(n, r, T, 𝒜, P, k, a)) = " +
			"a",
	},
		"The projection formula reduces the integral to the "+
			"original form multiplied by the fibre integral one."),
})}

var ThomRightInverse = thomRightInverseThm{family.Add(registry.ProofEntry{
	Name: "ThomRightInverse",
	Key:  "prop_5c26ebe7942e79c2",
	Deps: []registry.EntryLike{ThomHomomorphism, FiberHomomorphism},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a:set(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"a ∈ " +
				"(compact_de_rham_module(n + 2 * r, " +
				"        projection_total_topology(T, P), " +
				"        projection_total_atlas(n, r, T, 𝒜, P), " +
				"        k + 2 * r)).carrier",
		},
		Conclusion: "compact_de_rham_thom(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    k, " +
			"    compact_de_rham_fiber(n, r, T, 𝒜, P, k, a)) = " +
			"a",
	},
		"On a trivialization, the compact Poincare homotopy leaves only the top fibre integral. "+
			"Glue the relative homotopies over a finite cover of the projected compact support."),
})}

var LowerDegreeZero = lowerDegreeZeroThm{family.Add(registry.ProofEntry{
	Name: "LowerDegreeZero",
	Key:  "prop_b61104c42140d88e",
	Deps: []registry.EntryLike{ThomRightInverse},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a:set(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"k < 2 * r",
			"a ∈ " +
				"(compact_de_rham_module(n + 2 * r, " +
				"        projection_total_topology(T, P), " +
				"        projection_total_atlas(n, r, T, 𝒜, P), " +
				"        k)).carrier",
		},
		Conclusion: "a = " +
			"(compact_de_rham_module(n + 2 * r, " +
			"        projection_total_topology(T, P), " +
			"        projection_total_atlas(n, r, T, 𝒜, P), " +
			"        k)).zero",
	}, "The same compact fibre homotopy has no top-fibre component below the fibre dimension."),
})}

var ThomFormIndependent = thomFormIndependentThm{family.Add(registry.ProofEntry{
	Name: "ThomFormIndependent",
	Key:  "prop_6edd92ca368b55c1",
	Deps: []registry.EntryLike{ThomRightInverse, ThomLeftInverse, FiberProjectionFormula},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀τ:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"manifold_form_on⟨n + 2 * r⟩(projection_total_topology(T, P), " +
				"    projection_total_atlas(n, r, T, 𝒜, P), " +
				"    2 * r, " +
				"    τ) ∧ " +
				"projection_fiber_proper(n, r, T, 𝒜, P, τ) ∧ " +
				"manifold_exterior_derivative⟨n + 2 * r⟩(projection_total_topology(T, P), " +
				"    projection_total_atlas(n, r, T, 𝒜, P), " +
				"    2 * r, " +
				"    τ) = " +
				"(λc:prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real). " +
				"λy:(num → real). " +
				"λV:(num → num → real). " +
				"    &0) ∧ " +
				"projection_fiber_integral(n, r, T, 𝒜, P, 0, τ) = manifold_form_unit⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω) = " +
				"(λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). &0)",
		},
		Conclusion: "compact_de_rham_class(n + 2 * r, " +
			"    projection_total_topology(T, P), " +
			"    projection_total_atlas(n, r, T, 𝒜, P), " +
			"    k + 2 * r, " +
			"    manifold_form_wedge⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"        projection_total_atlas(n, r, T, 𝒜, P), " +
			"        k, " +
			"        2 * r, " +
			"        manifold_form_pullback⟨n + 2 * r, n⟩(projection_total_topology(T, P), " +
			"            projection_total_atlas(n, r, T, 𝒜, P), " +
			"            T, " +
			"            𝒜, " +
			"            k, " +
			"            λp:prod(A, num → complex). fst(p), " +
			"            ω), " +
			"        τ)) = " +
			"compact_de_rham_thom(n, r, T, 𝒜, P, k, compact_de_rham_class(n, T, 𝒜, k, ω))",
	},
		"Both compact classes have the same fibre integral by the projection formula "+
			"and normalization. The two-sided Thom inverse therefore identifies them."),
})}

var FiberProjectionFormula = fiberProjectionFormulaThm{family.Add(registry.ProofEntry{
	Name: "FiberProjectionFormula",
	Key:  "prop_ee1864bb9bf6bc6",
	Deps: []registry.EntryLike{
		projection_geometry.FiberIntegralExistsUnique,
		projection_geometry.FiberIntegrandCompact,
		projection_geometry.TotalManifold,
		differential_form.PullbackForm,
		differential_form.PullbackCoordinate,
		differential_form.WedgeForm,
		differential_form.WedgeSupport,
		differential_form.SupportClosed,
		compact.CompactInterClosed,
		smooth_manifold.AtlasMemberCompatible,
		vec_integral.CcRapid,
		vec_integral.IntegralSum,
		vec_integral.IntegralScale,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k l:num. " +
			"∀α:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀ω:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"manifold_form_on⟨n⟩(T, 𝒜, k, α)",
			"manifold_form_on⟨n + 2 * r⟩(projection_total_topology(T, P), " +
				"    projection_total_atlas(n, r, T, 𝒜, P), " +
				"    l + 2 * r, " +
				"    ω)",
			"projection_fiber_proper(n, r, T, 𝒜, P, ω)",
		},
		Conclusion: "projection_fiber_integral(n, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    k + l, " +
			"    manifold_form_wedge⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"        projection_total_atlas(n, r, T, 𝒜, P), " +
			"        k, " +
			"        l + 2 * r, " +
			"        manifold_form_pullback⟨n + 2 * r, n⟩(projection_total_topology(T, P), " +
			"            projection_total_atlas(n, r, T, 𝒜, P), " +
			"            T, " +
			"            𝒜, " +
			"            k, " +
			"            λp:prod(A, num → complex). fst(p), " +
			"            α), " +
			"        ω)) = " +
			"manifold_form_wedge⟨n⟩(T, 𝒜, k, l, α, projection_fiber_integral(n, r, T, 𝒜, P, l, ω))",
	},
		"The wedge ξ of the pulled-back α with ω is a form of degree k + l + 2r (TotalManifold, "+
			"PullbackForm, WedgeForm), fibre-proper since its support lies in ω's (WedgeSupport, "+
			"SupportClosed, CompactInterClosed); by the uniqueness half of FiberIntegralExistsUnique "+
			"it suffices that α wedged with the fibre integral of ω satisfies ξ's local formula in "+
			"each framed chart. There the pulled-back α reads the base coordinates only and vanishes "+
			"on a vertical column (PullbackCoordinate), so only the shuffles giving α base columns "+
			"survive, and the 2r vertical columns stay last in ω's block, so each sign is the (k, "+
			"l)-shuffle's. The integrands are «Cc» by FiberIntegrandCompact, hence rapid (CcRapid), "+
			"and IntegralSum and IntegralScale move the fibre integral inside the finite sum and "+
			"past α's factor, which is constant along the fibre."),
})}
