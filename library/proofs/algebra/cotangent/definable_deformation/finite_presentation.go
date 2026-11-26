package definable_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/definable_andre_quillen"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	"github.com/euc-ai/xugo/library/registry"
)

var finiteConormalCodesDef = finiteConormalCodesDefThm{family.Define(registry.DefEntry{
	Name:  "finiteConormalCodesDef",
	Key:   "prop_87ea2f0e5bed718c",
	Const: "finite_conormal_codes",
	Type:  "ring_ops(A) → set(U) → ring_ops(B) → (U → B) → module_ops(B, D) → set(U) → set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀X:set(U). ∀S:ring_ops(B). ∀ε:(U → B). ∀N:module_ops(B, D). ∀Y:set(U). " +
			"    finite_conormal_codes(R, X, S, ε, N, Y) = " +
			"    image(λh:(U → D). λy:U. COND(y ∈ Y, h(y), N.zero), " +
			"        {h:(U → D) | conormal_hom(universe_algebra_ring(R, X), S, ε, N, h)})",
	},
	Deps: []registry.EntryLike{},
	Reading: "Conormal maps recorded only on the specified " +
		"relation generators, normalized outside them."})}

var finiteConormalBoundariesDef = finiteConormalBoundariesDefThm{family.Define(registry.DefEntry{
	Name:  "finiteConormalBoundariesDef",
	Key:   "prop_84d6d2d85802871e",
	Const: "finite_conormal_boundaries",
	Type:  "ring_ops(A) → set(U) → ring_ops(B) → (U → B) → module_ops(B, D) → set(U) → set(U → D)",
	Equations: []string{
		"∀R:ring_ops(A). ∀X:set(U). ∀S:ring_ops(B). ∀ε:(U → B). ∀N:module_ops(B, D). ∀Y:set(U). " +
			"    finite_conormal_boundaries(R, X, S, ε, N, Y) = " +
			"    image(λa:(U → D). λy:U. " +
			"            COND(y ∈ Y, " +
			"                free_algebra_derivation(universe_embedding(R), R, X, ε, N, a)(y), " +
			"                N.zero), " +
			"        function_module(N, X).carrier)",
	},
	Deps: []registry.EntryLike{},
	Reading: "The image of the finite generator-value space " +
		"N^X under relation evaluation of the free derivation."})}

var FinitePresentationExalModel = finitePresentationExalModelThm{family.Add(registry.ProofEntry{
	Name: "FinitePresentationExalModel",
	Key:  "prop_cd8ae1b24e1fad6d",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀X:set(U). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀ε:(U → B). " +
				"∀N:module_ops(B, D). " +
				"∀Y:set(U).",
			Hypotheses: []string{
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
				"ring_homomorphism(R, S, f)",
				"ring_homomorphism(universe_algebra_ring(R, X), S, ε)",
				"image(ε, universe_algebra_ring(R, X).carrier) = S.carrier",
				"∀a:A. a ∈ R.carrier ⇒ ε(universe_algebra_const(R, a)) = f(a)",
				"module_on(S, N)",
				"finite(X)",
				"finite(Y)",
				"Y ⊆ ring_kernel(S.zero, universe_algebra_ring(R, X).carrier, ε)",
				"ideal_span(universe_algebra_ring(R, X), Y) = " +
					"ring_kernel(S.zero, universe_algebra_ring(R, X).carrier, ε)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
			},
			Conclusion: "polish_cover_on(restrict_group(module_additive_group(function_module(N, Y)), " +
				"        finite_conormal_codes(R, X, S, ε, N, Y)), " +
				"    subtopology(indexed_discrete_topology(Y, λy:U. N.zero, λy:U. N.carrier), " +
				"        finite_conormal_codes(R, X, S, ε, N, Y)), " +
				"    finite_conormal_boundaries(R, X, S, ε, N, Y)) ∧ " +
				"(∀z:(U → D). " +
				"    z ∈ finite_conormal_codes(R, X, S, ε, N, Y) ⇒ " +
				"    {z} ∈ " +
				"    subtopology(indexed_discrete_topology(Y, λy:U. N.zero, λy:U. N.carrier), " +
				"        finite_conormal_codes(R, X, S, ε, N, Y))) ∧ " +
				"borel_cover_iso(restrict_group(module_additive_group(function_module(N, Y)), " +
				"        finite_conormal_codes(R, X, S, ε, N, Y)), " +
				"    subtopology(indexed_discrete_topology(Y, λy:U. N.zero, λy:U. N.carrier), " +
				"        finite_conormal_codes(R, X, S, ε, N, Y)), " +
				"    finite_conormal_boundaries(R, X, S, ε, N, Y), " +
				"    cocycle_group(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1), " +
				"    cocycle_topology(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), " +
				"        aq_topologies(R, S, N), " +
				"        1), " +
				"    coboundaries(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1), " +
				"    induced_map(λc:(U → D). " +
				"            square_zero_class⟨U:U⟩(R, " +
				"                S, " +
				"                f, " +
				"                N, " +
				"                square_zero_graph(universe_algebra_ring(R, X), " +
				"                    universe_algebra_const(R), " +
				"                    S, " +
				"                    ε, " +
				"                    N, " +
				"                    inverse_on( " +
				"                        {h:(U → D) | conormal_hom(universe_algebra_ring(R, X), S, ε, N, h)}, " +
				"                        λh:(U → D). λy:U. COND(y ∈ Y, h(y), N.zero), " +
				"                        c))))) ∧ " +
				"countable(cohomology(cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N), 1))",
		},
		"Conormal maps are determined by the finite ideal generators. Their relation-value "+
			"space is a subgroup of the finite discrete product N^Y; free derivations are "+
			"determined by N^X. Polynomial presentation classification identifies the quotient "+
			"with D1. The source is countable discrete, and finite relation evaluation plus "+
			"the reduced standard conormal comparison supplies Borel lifts in both directions."),
	Deps: []registry.EntryLike{
		finiteConormalCodesDef,
		finiteConormalBoundariesDef,
		FactorSetAQDefinableIso,
		definable_andre_quillen.ResolutionComparisonDefinableIso,
		square_zero_classification.ExtensionIsoIffSameClass,
	},
	Reading: "The relation generators need not be independent and the quotient need " +
		"not be finitely generated. Finite presentation with countable coefficients makes " +
		"the classification countable, even though standard name spaces are infinite.",
})}
