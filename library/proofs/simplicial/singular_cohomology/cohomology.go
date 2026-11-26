package singular_cohomology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/simplicial/singular_homology"
	"github.com/euc-ai/xugo/library/proofs/simplicial/singular_set"
	"github.com/euc-ai/xugo/library/registry"
)

var CochainComplex = cochainComplexThm{family.Add(registry.ProofEntry{
	Name: "CochainComplex",
	Key:  "prop_5db9ebbb1ecbe222",
	Deps: []registry.EntryLike{ComplexOfDef},
	Build: family.Card(
		Statement{
			Binders:    "∀K:simplicial_ops((num → real) → A).",
			Hypotheses: []string{"simplicial_set(K)"},
			Conclusion: "cochain_complex(real_ring, singular_cochain_complex_of(K))",
		},
		"The alternating coface sum squares to zero by the simplicial "+
			"face identities; normalization preserves the degree carriers."),
})}

var UniversalCoefficient = universalCoefficientThm{family.Add(registry.ProofEntry{
	Name: "UniversalCoefficient",
	Key:  "prop_493c7309e9c81e79",
	Deps: []registry.EntryLike{CochainComplex, EvaluationDef},
	Reading: "No finite-dimensionality assumption is needed for real " +
		"coefficients. Surjectivity uses algebraic extension of linear functionals, " +
		"not a topological dual or a finite-dimensional duality theorem.",
	Build: family.Card(
		Statement{
			Binders:    "∀K:simplicial_ops((num → real) → A). ∀k:num.",
			Hypotheses: []string{"simplicial_set(K)"},
			Conclusion: "module_isomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex_of(K), k), " +
				"    hom_module(real_ring, " +
				"        homology_module(free_complex(real_ring, " +
				"                K.simplices, " +
				"                simplicial_boundary(real_ring.add, " +
				"                    real_ring.zero, " +
				"                    real_ring.one, " +
				"                    real_ring.neg, " +
				"                    real_ring.mul, " +
				"                    K.d)), " +
				"            k), " +
				"        regular_module(real_ring)), " +
				"    singular_cohomology_evaluation(K, k))",
		},
		"A functional on homology extends from cycles to all chains by a vector "+
			"- space complement. Conversely, a cocycle vanishing on cycles factors "+
			"through boundaries and extends one degree lower, hence is a coboundary."),
})}

var PullbackCochain = pullbackCochainThm{family.Add(registry.ProofEntry{
	Name: "PullbackCochain",
	Key:  "prop_241aa9cfd00b19da",
	Deps: []registry.EntryLike{CochainComplex, PullbackOfDef},
	Build: family.Card(
		Statement{
			Binders:    "∀K:simplicial_ops((num → real) → A). ∀L:simplicial_ops((num → real) → B). ∀f:(A → B).",
			Hypotheses: []string{"simplicial_map(K, L, singular_map(f))"},
			Conclusion: "cochain_map(real_ring, " +
				"    singular_cochain_complex_of(L), " +
				"    singular_cochain_complex_of(K), " +
				"    singular_cochain_pullback_of(K, f))",
		},
		"Postcomposition commutes with faces, so its dual commutes with the "+
			"alternating coboundary. The source carrier guard normalizes the pullback."),
})}

var SmallCochainsQuasiIsomorphism = smallCochainsQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SmallCochainsQuasiIsomorphism",
	Key:  "prop_d7d3fbc2a3ea375d",
	Deps: []registry.EntryLike{UniversalCoefficient, singular_homology.SmallChainsQuasiIsomorphism},
	Build: family.Card(
		Statement{
			Binders:    "∀T:set(set(A)). ∀𝒰:set(set(A)). ∀k:num.",
			Hypotheses: []string{"is_topology(T)", "𝒰 ⊆ T", "⋃T ⊆ ⋃𝒰"},
			Conclusion: "module_isomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex(T), k), " +
				"    cohomology_module(singular_cochain_complex_of(singular_small_set(singular_set(T), 𝒰)), k), " +
				"    singular_cohomology_restriction(singular_small_set(singular_set(T), 𝒰), k))",
		},
		"Small chains are a homology equivalence. Over the reals evaluation identifies "+
			"cohomology with the homology dual, so restriction to small cochains is an isomorphism."),
})}

var SubspaceSingularSet = subspaceSingularSetThm{family.Add(registry.ProofEntry{
	Name: "SubspaceSingularSet",
	Key:  "prop_8a143dee3de79a39",
	Deps: []registry.EntryLike{
		RestrictedSetDef,
		singular_set.SingularSetDef,
		singular_set.SubspaceSingularSimplices,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀T:set(set(A)). ∀U:set(A).",
			Hypotheses: []string{"U ⊆ ⋃T"},
			Conclusion: "singular_set(subtopology(T, U)) = singular_restricted_set(singular_set(T), U)",
		},
		"Both records carry the same face and degeneracy maps, which do not read the "+
			"space. Their simplices agree in each degree by SubspaceSingularSimplices."),
})}

var CoverLongExact = coverLongExactThm{family.Add(registry.ProofEntry{
	Name: "CoverLongExact",
	Key:  "prop_6390897f99b25e26",
	Deps: []registry.EntryLike{CochainComplex, ConnectingDef, CoverComplexDef},
	Build: family.Card(
		Statement{
			Binders: "∀K:simplicial_ops((num → real) → A). ∀U V:set(A). ∀k:num.",
			Hypotheses: []string{
				"simplicial_set(K)",
				"simplicial_map(singular_restricted_set(K, U), K, (λk:num. λσ:((num → real) → A). σ))",
				"simplicial_map(singular_restricted_set(K, V), K, (λk:num. λσ:((num → real) → A). σ))",
				"simplicial_map(singular_restricted_set(K, U ∩ V), K, (λk:num. λσ:((num → real) → A). σ))",
				"simplicial_map(singular_small_set(K, {U, V}), K, (λk:num. λσ:((num → real) → A). σ))",
				"∀j:num. " +
					"    module_isomorphism(real_ring, " +
					"        cohomology_module(singular_cochain_complex_of(K), j), " +
					"        cohomology_module(singular_cochain_complex_of(singular_small_set(K, {U, V})), j), " +
					"        singular_cohomology_restriction(singular_small_set(K, {U, V}), j))",
			},
			Conclusion: "module_homomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex_of(singular_restricted_set(K, U ∩ V)), k), " +
				"    cohomology_module(singular_cochain_complex_of(K), k + 1), " +
				"    singular_cohomology_connecting(K, U, V, k)) ∧ " +
				"exact_at( " +
				"    cohomology_module(singular_cochain_complex_of(singular_restricted_set(K, U ∩ V)), k).zero, " +
				"    cohomology_module(singular_cochain_complex_of(K), k).carrier, " +
				"    cohomology_module(singular_cover_complex(K, U, V), k).carrier, " +
				"    cohomology_map(singular_cover_complex(K, U, V), singular_cover_restriction(K, U, V), k), " +
				"    cohomology_map(singular_cochain_complex_of(singular_restricted_set(K, U ∩ V)), " +
				"        singular_cover_difference(K, U, V), " +
				"        k)) ∧ " +
				"exact_at(cohomology_module(singular_cochain_complex_of(K), k + 1).zero, " +
				"    cohomology_module(singular_cover_complex(K, U, V), k).carrier, " +
				"    cohomology_module(singular_cochain_complex_of(singular_restricted_set(K, U ∩ V)), " +
				"        k).carrier, " +
				"    cohomology_map(singular_cochain_complex_of(singular_restricted_set(K, U ∩ V)), " +
				"        singular_cover_difference(K, U, V), " +
				"        k), " +
				"    singular_cohomology_connecting(K, U, V, k)) ∧ " +
				"exact_at(cohomology_module(singular_cover_complex(K, U, V), k + 1).zero, " +
				"    cohomology_module(singular_cochain_complex_of(singular_restricted_set(K, U ∩ V)), " +
				"        k).carrier, " +
				"    cohomology_module(singular_cochain_complex_of(K), k + 1).carrier, " +
				"    singular_cohomology_connecting(K, U, V, k), " +
				"    cohomology_map(singular_cover_complex(K, U, V), singular_cover_restriction(K, U, V), k + 1))",
		},
		"The small cochains inject into the pair of local cochains, whose difference "+
			"maps onto intersection cochains by extension by zero. Apply the cochain "+
			"long exact sequence and transport through the small-restriction isomorphism."),
})}

var MayerVietoris = mayerVietorisThm{family.Add(registry.ProofEntry{
	Name: "MayerVietoris",
	Key:  "prop_8dfbe11b09b4b2a9",
	Deps: []registry.EntryLike{CoverLongExact, SmallCochainsQuasiIsomorphism},
	Build: family.Card(
		Statement{
			Binders:    "∀T:set(set(A)). ∀U V:set(A). ∀k:num.",
			Hypotheses: []string{"is_topology(T)", "U ∈ T", "V ∈ T", "U ∪ V = ⋃T"},
			Conclusion: "module_homomorphism(real_ring, " +
				"    cohomology_module( " +
				"        singular_cochain_complex_of(singular_restricted_set(singular_set(T), U ∩ V)), k), " +
				"    cohomology_module(singular_cochain_complex_of(singular_set(T)), k + 1), " +
				"    singular_cohomology_connecting(singular_set(T), U, V, k)) ∧ " +
				"exact_at(cohomology_module( " +
				"        singular_cochain_complex_of(singular_restricted_set(singular_set(T), U ∩ V)), k).zero, " +
				"    cohomology_module(singular_cochain_complex_of(singular_set(T)), k).carrier, " +
				"    cohomology_module(singular_cover_complex(singular_set(T), U, V), k).carrier, " +
				"    cohomology_map(singular_cover_complex(singular_set(T), U, V), " +
				"        singular_cover_restriction(singular_set(T), U, V), " +
				"        k), " +
				"    cohomology_map( " +
				"        singular_cochain_complex_of(singular_restricted_set(singular_set(T), U ∩ V)), " +
				"        singular_cover_difference(singular_set(T), U, V), " +
				"        k)) ∧ " +
				"exact_at(cohomology_module(singular_cochain_complex_of(singular_set(T)), k + 1).zero, " +
				"    cohomology_module(singular_cover_complex(singular_set(T), U, V), k).carrier, " +
				"    cohomology_module( " +
				"        singular_cochain_complex_of(singular_restricted_set(singular_set(T), U ∩ V)), " +
				"        k).carrier, " +
				"    cohomology_map( " +
				"        singular_cochain_complex_of(singular_restricted_set(singular_set(T), U ∩ V)), " +
				"        singular_cover_difference(singular_set(T), U, V), " +
				"        k), " +
				"    singular_cohomology_connecting(singular_set(T), U, V, k)) ∧ " +
				"exact_at(cohomology_module(singular_cover_complex(singular_set(T), U, V), k + 1).zero, " +
				"    cohomology_module( " +
				"        singular_cochain_complex_of(singular_restricted_set(singular_set(T), U ∩ V)), " +
				"        k).carrier, " +
				"    cohomology_module(singular_cochain_complex_of(singular_set(T)), k + 1).carrier, " +
				"    singular_cohomology_connecting(singular_set(T), U, V, k), " +
				"    cohomology_map(singular_cover_complex(singular_set(T), U, V), " +
				"        singular_cover_restriction(singular_set(T), U, V), " +
				"        k + 1))",
		},
		"Use the two-open small-cochain comparison and the generic cover long exact sequence. Subspace "+
			"singular simplices are exactly the normalized simplices with image in the specified open set."),
})}
