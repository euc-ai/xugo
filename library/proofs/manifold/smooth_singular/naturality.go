package smooth_singular

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var ConnectingNaturality = connectingNaturalityThm{family.Add(registry.ProofEntry{
	Name: "ConnectingNaturality",
	Key:  "prop_4dd27ce1ed2dd003",
	Deps: []registry.EntryLike{
		MayerVietoris,
		SmallCochainsQuasiIsomorphism,
		OpenSubmanifoldSingularSet,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀m:num. " +
				"∀S:set(set(B)). " +
				"∀ℬ:set(prod(set(B), B → num → real)). " +
				"∀f:(A → B). " +
				"∀k:num. " +
				"∀U V:set(A). " +
				"∀U' V':set(B). " +
				"∀s:set(((num → real) → B) → real).",
			Hypotheses: []string{
				"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
				"U ∈ T",
				"V ∈ T",
				"U ∪ V = ⋃T",
				"U' ∈ S",
				"V' ∈ S",
				"U' ∪ V' = ⋃S",
				"image(f, U) ⊆ U'",
				"image(f, V) ⊆ V'",
				"s ∈ " +
					"smooth_singular_cohomology_module⟨m⟩(subtopology(S, U' ∩ V'), " +
					"    open_submanifold_atlas⟨m⟩(S, ℬ, U' ∩ V'), " +
					"    k).carrier",
			},
			Conclusion: "smooth_singular_cohomology_pullback⟨n⟩(T, 𝒜, f, k + 1)( " +
				"    singular_cohomology_connecting(smooth_singular_set⟨m⟩(S, ℬ), U', V', k, s)) = " +
				"singular_cohomology_connecting(smooth_singular_set⟨n⟩(T, 𝒜), " +
				"    U, " +
				"    V, " +
				"    k, " +
				"    smooth_singular_cohomology_pullback⟨n⟩(subtopology(T, U ∩ V), " +
				"        open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
				"        f, " +
				"        k)(s))",
		},
		"Postcomposition preserves the assigned cover pieces. The induced map of short exact "+
			"small-cochain sequences commutes with the difference maps; generic connecting "+
			"naturality and the inverse small-restriction comparisons give the result."),
})}

var MayerVietorisInitial = mayerVietorisInitialThm{family.Add(registry.ProofEntry{
	Name: "MayerVietorisInitial",
	Key:  "prop_411ac02c0522c44f",
	Deps: []registry.EntryLike{MayerVietoris, SmallCochainsQuasiIsomorphism},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A).",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T", "V ∈ T", "U ∪ V = ⋃T"},
			Conclusion: "injective_on(smooth_singular_cohomology_module⟨n⟩(T, 𝒜, 0).carrier, " +
				"    cohomology_map(singular_cover_complex(smooth_singular_set⟨n⟩(T, 𝒜), U, V), " +
				"        singular_cover_restriction(smooth_singular_set⟨n⟩(T, 𝒜), U, V), " +
				"        0))",
		},
		"The cochain cover sequence is short exact and degree-zero coboundaries "+
			"are zero. The induced degree-zero restriction is therefore injective."),
})}
