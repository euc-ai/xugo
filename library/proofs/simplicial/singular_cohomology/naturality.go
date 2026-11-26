package singular_cohomology

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var ConnectingNaturality = connectingNaturalityThm{family.Add(registry.ProofEntry{
	Name: "ConnectingNaturality",
	Key:  "prop_6f8e8f44d5696b30",
	Deps: []registry.EntryLike{MayerVietoris, SmallCochainsQuasiIsomorphism, SubspaceSingularSet},
	Build: family.Card(
		Statement{
			Binders: "∀T:set(set(A)). " +
				"∀S:set(set(B)). " +
				"∀f:(A → B). " +
				"∀k:num. " +
				"∀U V:set(A). " +
				"∀U' V':set(B). " +
				"∀s:set(((num → real) → B) → real).",
			Hypotheses: []string{
				"continuous_map(T, S, f)",
				"is_topology(T)",
				"is_topology(S)",
				"U ∈ T",
				"V ∈ T",
				"U ∪ V = ⋃T",
				"U' ∈ S",
				"V' ∈ S",
				"U' ∪ V' = ⋃S",
				"image(f, U) ⊆ U'",
				"image(f, V) ⊆ V'",
				"s ∈ " +
					"cohomology_module(singular_cochain_complex_of(singular_set(subtopology(S, U' ∩ V'))), k).carrier",
			},
			Conclusion: "cohomology_map(singular_cochain_complex_of(singular_set(T)), " +
				"    singular_cochain_pullback_of(singular_set(T), f), " +
				"    k + 1)(singular_cohomology_connecting(singular_set(S), U', V', k, s)) = " +
				"singular_cohomology_connecting(singular_set(T), " +
				"    U, " +
				"    V, " +
				"    k, " +
				"    cohomology_map(singular_cochain_complex_of(singular_set(subtopology(T, U ∩ V))), " +
				"        singular_cochain_pullback_of(singular_set(subtopology(T, U ∩ V)), f), " +
				"        k)(s))",
		},
		"Postcomposition preserves the assigned cover pieces. The induced map of short exact "+
			"small-cochain sequences commutes with the difference maps; generic connecting "+
			"naturality and the inverse small-restriction comparisons give the result."),
})}

var MayerVietorisInitial = mayerVietorisInitialThm{family.Add(registry.ProofEntry{
	Name: "MayerVietorisInitial",
	Key:  "prop_55a0fb0660ded055",
	Deps: []registry.EntryLike{MayerVietoris, SmallCochainsQuasiIsomorphism},
	Build: family.Card(
		Statement{
			Binders:    "∀T:set(set(A)). ∀U V:set(A).",
			Hypotheses: []string{"is_topology(T)", "U ∈ T", "V ∈ T", "U ∪ V = ⋃T"},
			Conclusion: "injective_on( " +
				"    cohomology_module(singular_cochain_complex_of(singular_set(T)), 0).carrier, " +
				"    cohomology_map(singular_cover_complex(singular_set(T), U, V), " +
				"        singular_cover_restriction(singular_set(T), U, V), " +
				"        0))",
		},
		"The cochain cover sequence is short exact and degree-zero coboundaries "+
			"are zero. The induced degree-zero restriction is therefore injective."),
})}
