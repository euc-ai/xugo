package de_rham_comparison

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_embedding"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_singular"
	"github.com/euc-ai/xugo/library/proofs/manifold/thom_form"
	"github.com/euc-ai/xugo/library/proofs/simplicial/singular_cohomology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var RestrictionCochain = restrictionCochainThm{family.Add(registry.ProofEntry{
	Name: "RestrictionCochain",
	Key:  "prop_8e8d402a667223e6",
	Deps: []registry.EntryLike{smooth_singular.SmoothSingularSet, singular_cohomology.RestrictionDef},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
			Conclusion: "cochain_map(real_ring, " +
				"    singular_cochain_complex(T), " +
				"    singular_cochain_complex_of(smooth_singular_set⟨n⟩(T, 𝒜)), " +
				"    singular_cochain_restriction(smooth_singular_set⟨n⟩(T, 𝒜)))",
		},
		"The inclusion of smooth simplices commutes with faces, and restriction is its dual cochain map."),
})}

var ComparisonHomomorphisms = comparisonHomomorphismsThm{family.Add(registry.ProofEntry{
	Name: "ComparisonHomomorphisms",
	Key:  "prop_a70a7693fc349c86",
	Deps: []registry.EntryLike{smooth_singular.IntegrationCochain, RestrictionCochain},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
			Conclusion: "module_homomorphism(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    de_rham_integration_class⟨n⟩(T, 𝒜, k)) ∧ " +
				"module_homomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex(T), k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    singular_cohomology_restriction(smooth_singular_set⟨n⟩(T, 𝒜), k))",
		},
		"The integration and restriction cochain maps induce linear maps on cohomology."),
})}

var RestrictionNaturality = restrictionNaturalityThm{family.Add(registry.ProofEntry{
	Name: "RestrictionNaturality",
	Key:  "prop_f273ef28cce0c331",
	Deps: []registry.EntryLike{smooth_singular.SmoothSingularMap, RestrictionCochain},
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
				"∀s:set(((num → real) → B) → real).",
			Hypotheses: []string{
				"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
				"s ∈ cohomology_module(singular_cochain_complex(S), k).carrier",
			},
			Conclusion: "singular_cohomology_restriction(smooth_singular_set⟨n⟩(T, 𝒜), k)( " +
				"    singular_cohomology_pullback(T, f, k, s)) = " +
				"smooth_singular_cohomology_pullback⟨n⟩(T, 𝒜, f, k)( " +
				"    singular_cohomology_restriction(smooth_singular_set⟨m⟩(S, ℬ), k)(s))",
		},
		"Postcomposition by a smooth map preserves smooth singular simplices, so "+
			"the restriction square commutes already on cochains and hence on classes."),
})}

var IntegrationClassNaturality = integrationClassNaturalityThm{family.Add(registry.ProofEntry{
	Name: "IntegrationClassNaturality",
	Key:  "prop_541a225329cdef51",
	Deps: []registry.EntryLike{
		smooth_singular.IntegrationNaturality,
		smooth_singular.IntegrationCochain,
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
				"∀s:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{
				"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
				"s ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, k).carrier",
			},
			Conclusion: "de_rham_integration_class⟨n⟩(T, 𝒜, k)( " +
				"    de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)(s)) = " +
				"smooth_singular_cohomology_pullback⟨n⟩(T, 𝒜, f, k)(de_rham_integration_class⟨m⟩(S, ℬ, k)(s))",
		},
		"The naturality identity for integration cochains descends to genuine quotient classes."),
})}

var IntegrationConnecting = integrationConnectingThm{family.Add(registry.ProofEntry{
	Name: "IntegrationConnecting",
	Key:  "prop_63ae5a6e210d3738",
	Deps: []registry.EntryLike{
		chain_complex.CoconnectingNaturality,
		smooth_singular.IntegrationNaturality,
		smooth_singular.MayerVietoris,
		smooth_singular.OpenSubmanifoldSingularSet,
		de_rham_cover.MayerVietoris,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀U V:set(A). " +
				"∀k:num. " +
				"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{
				"«cover exact»",
				"smooth_manifold⟨n⟩(T, 𝒜)",
				"U ∈ T",
				"V ∈ T",
				"U ∪ V = ⋃T",
				"s ∈ " +
					"de_rham_cohomology_module⟨n⟩(subtopology(T, U ∩ V), " +
					"    open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
					"    k).carrier",
			},
			Conclusion: "de_rham_integration_class⟨n⟩(T, 𝒜, k + 1)( " +
				"    de_rham_connecting⟨n⟩(T, 𝒜, U, V, k, s)) = " +
				"singular_cohomology_connecting(smooth_singular_set⟨n⟩(T, 𝒜), U, V, k)( " +
				"    de_rham_integration_class⟨n⟩(subtopology(T, U ∩ V), " +
				"        open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
				"        k)(s))",
		},
		"Use the supplied short exact de Rham cover sequence and restrict integration "+
			"to the smooth small-cochain cover sequence. Integration commutes with "+
			"restriction and the U-minus-V difference, so CoconnectingNaturality gives "+
			"the connecting square; invert the small restriction afterwards."),
})}

var RestrictionConnecting = restrictionConnectingThm{family.Add(registry.ProofEntry{
	Name: "RestrictionConnecting",
	Key:  "prop_3ce1f25493931ace",
	Deps: []registry.EntryLike{
		RestrictionNaturality,
		singular_cohomology.MayerVietoris,
		singular_cohomology.SubspaceSingularSet,
		smooth_singular.MayerVietoris,
		smooth_singular.OpenSubmanifoldSingularSet,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀U V:set(A). " +
				"∀k:num. " +
				"∀s:set(((num → real) → A) → real).",
			Hypotheses: []string{
				"smooth_manifold⟨n⟩(T, 𝒜)",
				"U ∈ T",
				"V ∈ T",
				"U ∪ V = ⋃T",
				"s ∈ cohomology_module(singular_cochain_complex(subtopology(T, U ∩ V)), k).carrier",
			},
			Conclusion: "singular_cohomology_restriction(smooth_singular_set⟨n⟩(T, 𝒜), k + 1)( " +
				"    singular_cohomology_connecting(singular_set(T), U, V, k)(s)) = " +
				"singular_cohomology_connecting(smooth_singular_set⟨n⟩(T, 𝒜), U, V, k)( " +
				"    singular_cohomology_restriction( " +
				"        smooth_singular_set⟨n⟩(subtopology(T, U ∩ V), open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V)), " +
				"        k)(s))",
		},
		"Inclusion of smooth small simplices gives a map of the continuous "+
			"and smooth short-exact cover sequences. Connecting naturality and "+
			"the two small-cochain isomorphisms identify the transported maps."),
})}

var EmptyComparison = emptyComparisonThm{family.Add(registry.ProofEntry{
	Name: "EmptyComparison",
	Key:  "prop_70eefd1f7bacac3",
	Deps: []registry.EntryLike{ComparisonHomomorphisms},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "⋃T = ∅"},
			Conclusion: "module_isomorphism(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    de_rham_integration_class⟨n⟩(T, 𝒜, k)) ∧ " +
				"module_isomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex(T), k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    singular_cohomology_restriction(smooth_singular_set⟨n⟩(T, 𝒜), k))",
		},
		"All three complexes have the zero module in every degree. The "+
			"normalized maps between them therefore induce the unique isomorphisms."),
})}

var ConvexComparison = convexComparisonThm{family.Add(registry.ProofEntry{
	Name: "ConvexComparison",
	Key:  "prop_831d0ab21b7c40f5",
	Deps: []registry.EntryLike{
		smooth_manifold.ConvexOpenContraction,
		EmptyComparison,
		smooth_singular.HomotopyInvariance,
		smooth_singular.SimplexIntegralExtension,
		de_rham.HomotopyInvariance,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n k:num. ∀U:set(num → real).",
			Hypotheses: []string{"U ∈ euclidean_topology(n)", "convex(U)"},
			Conclusion: "module_isomorphism(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(subtopology(euclidean_topology(n), U), euclidean_atlas(U), k), " +
				"    smooth_singular_cohomology_module⟨n⟩(subtopology(euclidean_topology(n), U), " +
				"        euclidean_atlas(U), " +
				"        k), " +
				"    de_rham_integration_class⟨n⟩(subtopology(euclidean_topology(n), U), " +
				"        euclidean_atlas(U), " +
				"        k)) ∧ " +
				"module_isomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex(subtopology(euclidean_topology(n), U)), k), " +
				"    smooth_singular_cohomology_module⟨n⟩(subtopology(euclidean_topology(n), U), " +
				"        euclidean_atlas(U), " +
				"        k), " +
				"    singular_cohomology_restriction( " +
				"        smooth_singular_set⟨n⟩(subtopology(euclidean_topology(n), U), euclidean_atlas(U)), k))",
		},
		"For a nonempty convex open, straight-line contraction reduces all three "+
			"theories to a point, where degree-zero integration sends constants to the same "+
			"vertex values. Positive degrees vanish; the empty open uses EmptyComparison."),
})}

var MayerVietorisComparison = mayerVietorisComparisonThm{family.Add(registry.ProofEntry{
	Name: "MayerVietorisComparison",
	Key:  "prop_821f9b6a79d497d7",
	Deps: []registry.EntryLike{
		de_rham_cover.MayerVietorisMaps,
		de_rham_cover.MayerVietorisExact,
		de_rham_cover.MayerVietorisStart,
		singular_cohomology.MayerVietoris,
		singular_cohomology.MayerVietorisInitial,
		smooth_singular.MayerVietoris,
		smooth_singular.MayerVietorisInitial,
		singular_cohomology.SubspaceSingularSet,
		smooth_singular.OpenSubmanifoldSingularSet,
		IntegrationConnecting,
		RestrictionConnecting,
		ComparisonHomomorphisms,
		module_homomorphism.FiveLemma,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A). ∀k:num.",
			Hypotheses: []string{
				"«cover exact»",
				"smooth_manifold⟨n⟩(T, 𝒜)",
				"U ∈ T",
				"V ∈ T",
				"U ∪ V = ⋃T",
				"∀j:num. " +
					"    module_isomorphism(real_ring, " +
					"        de_rham_cohomology_module⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), j), " +
					"        smooth_singular_cohomology_module⟨n⟩(subtopology(T, U), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
					"            j), " +
					"        de_rham_integration_class⟨n⟩(subtopology(T, U), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
					"            j)) ∧ " +
					"    module_isomorphism(real_ring, " +
					"        cohomology_module(singular_cochain_complex(subtopology(T, U)), j), " +
					"        smooth_singular_cohomology_module⟨n⟩(subtopology(T, U), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, U), " +
					"            j), " +
					"        singular_cohomology_restriction( " +
					"            smooth_singular_set⟨n⟩(subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U)), j))",
				"∀j:num. " +
					"    module_isomorphism(real_ring, " +
					"        de_rham_cohomology_module⟨n⟩(subtopology(T, V), open_submanifold_atlas⟨n⟩(T, 𝒜, V), j), " +
					"        smooth_singular_cohomology_module⟨n⟩(subtopology(T, V), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, V), " +
					"            j), " +
					"        de_rham_integration_class⟨n⟩(subtopology(T, V), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, V), " +
					"            j)) ∧ " +
					"    module_isomorphism(real_ring, " +
					"        cohomology_module(singular_cochain_complex(subtopology(T, V)), j), " +
					"        smooth_singular_cohomology_module⟨n⟩(subtopology(T, V), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, V), " +
					"            j), " +
					"        singular_cohomology_restriction( " +
					"            smooth_singular_set⟨n⟩(subtopology(T, V), open_submanifold_atlas⟨n⟩(T, 𝒜, V)), j))",
				"∀j:num. " +
					"    module_isomorphism(real_ring, " +
					"        de_rham_cohomology_module⟨n⟩(subtopology(T, U ∩ V), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
					"            j), " +
					"        smooth_singular_cohomology_module⟨n⟩(subtopology(T, U ∩ V), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
					"            j), " +
					"        de_rham_integration_class⟨n⟩(subtopology(T, U ∩ V), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
					"            j)) ∧ " +
					"    module_isomorphism(real_ring, " +
					"        cohomology_module(singular_cochain_complex(subtopology(T, U ∩ V)), j), " +
					"        smooth_singular_cohomology_module⟨n⟩(subtopology(T, U ∩ V), " +
					"            open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V), " +
					"            j), " +
					"        singular_cohomology_restriction(smooth_singular_set⟨n⟩(subtopology(T, U ∩ V), " +
					"                open_submanifold_atlas⟨n⟩(T, 𝒜, U ∩ V)), " +
					"            j))",
			},
			Conclusion: "module_isomorphism(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    de_rham_integration_class⟨n⟩(T, 𝒜, k)) ∧ " +
				"module_isomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex(T), k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    singular_cohomology_restriction(smooth_singular_set⟨n⟩(T, 𝒜), k))",
		},
		"The supplied short exact de Rham sequence gives its exact cohomology ladder "+
			"through MayerVietorisMaps, MayerVietorisExact and MayerVietorisStart. Compare it "+
			"to the two singular ladders using the connecting squares and the heterogeneous "+
			"FiveLemma; degree zero uses the initial injections and the same kernel argument."),
})}

var FiniteBoxUnionComparison = finiteBoxUnionComparisonThm{family.Add(registry.ProofEntry{
	Name: "FiniteBoxUnionComparison",
	Key:  "prop_9ebe991ad5f08ea7",
	Deps: []registry.EntryLike{
		vec_smooth.SmoothPartitionOfUnityOpen,
		de_rham_cover.MayerVietoris, ConvexComparison, MayerVietorisComparison, EmptyComparison},
	Build: family.Card(
		Statement{
			Binders: "∀n k:num. ∀𝒰:set(set(num → real)).",
			Hypotheses: []string{
				"finite(𝒰)",
				"∀U:set(num → real). U ∈ 𝒰 ⇒ ∃a b:(num → real). U = euclidean_open_box⟨n⟩(a, b)",
			},
			Conclusion: "module_isomorphism(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(subtopology(euclidean_topology(n), ⋃𝒰), " +
				"        euclidean_atlas(⋃𝒰), " +
				"        k), " +
				"    smooth_singular_cohomology_module⟨n⟩(subtopology(euclidean_topology(n), ⋃𝒰), " +
				"        euclidean_atlas(⋃𝒰), " +
				"        k), " +
				"    de_rham_integration_class⟨n⟩(subtopology(euclidean_topology(n), ⋃𝒰), " +
				"        euclidean_atlas(⋃𝒰), " +
				"        k)) ∧ " +
				"module_isomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex(subtopology(euclidean_topology(n), ⋃𝒰)), k), " +
				"    smooth_singular_cohomology_module⟨n⟩(subtopology(euclidean_topology(n), ⋃𝒰), " +
				"        euclidean_atlas(⋃𝒰), " +
				"        k), " +
				"    singular_cohomology_restriction( " +
				"        smooth_singular_set⟨n⟩(subtopology(euclidean_topology(n), ⋃𝒰), euclidean_atlas(⋃𝒰)), k))",
		},
		"Induct on the finite family of boxes; intersecting the new box with the old union "+
			"produces a smaller finite family of boxes. At each Euclidean union choose two "+
			"subordinate smooth weights by SmoothPartitionOfUnityOpen, normalize them outside the "+
			"union, and apply de_rham_cover.MayerVietoris. Identify the canonical and restricted "+
			"Euclidean atlases, then use ConvexComparison and the guarded MayerVietorisComparison."),
})}

var RetractComparison = retractComparisonThm{family.Add(registry.ProofEntry{
	Name: "RetractComparison",
	Key:  "prop_2dbd36533f86378e",
	Deps: []registry.EntryLike{IntegrationClassNaturality, RestrictionNaturality},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀m:num. " +
				"∀S:set(set(B)). " +
				"∀ℬ:set(prod(set(B), B → num → real)). " +
				"∀i:(A → B). " +
				"∀r:(B → A). " +
				"∀k:num.",
			Hypotheses: []string{
				"smooth_manifold⟨n⟩(T, 𝒜)",
				"smooth_manifold⟨m⟩(S, ℬ)",
				"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, i)",
				"smooth_manifold_map⟨m, n⟩(S, ℬ, T, 𝒜, r)",
				"∀x:A. x ∈ ⋃T ⇒ r(i(x)) = x",
				"module_isomorphism(real_ring, " +
					"    de_rham_cohomology_module⟨m⟩(S, ℬ, k), " +
					"    smooth_singular_cohomology_module⟨m⟩(S, ℬ, k), " +
					"    de_rham_integration_class⟨m⟩(S, ℬ, k)) ∧ " +
					"module_isomorphism(real_ring, " +
					"    cohomology_module(singular_cochain_complex(S), k), " +
					"    smooth_singular_cohomology_module⟨m⟩(S, ℬ, k), " +
					"    singular_cohomology_restriction(smooth_singular_set⟨m⟩(S, ℬ), k))",
			},
			Conclusion: "module_isomorphism(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    de_rham_integration_class⟨n⟩(T, 𝒜, k)) ∧ " +
				"module_isomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex(T), k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    singular_cohomology_restriction(smooth_singular_set⟨n⟩(T, 𝒜), k))",
		},
		"For either natural comparison η, an inverse on the retract is i* ∘ η_S^(-1) ∘ r*. "+
			"Naturality and r∘i=id verify both inverse equations on the cohomology carriers."),
})}

var CompactComparison = compactComparisonThm{family.Add(registry.ProofEntry{
	Name: "CompactComparison",
	Key:  "prop_6f10747dc9761ad3",
	Deps: []registry.EntryLike{
		manifold_embedding.CompactEuclideanRetract,
		FiniteBoxUnionComparison,
		RetractComparison,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
			Conclusion: "module_isomorphism(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    de_rham_integration_class⟨n⟩(T, 𝒜, k)) ∧ " +
				"module_isomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex(T), k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    singular_cohomology_restriction(smooth_singular_set⟨n⟩(T, 𝒜), k))",
		},
		"Choose the smooth retraction of a finite union of open Euclidean boxes onto the compact "+
			"manifold. FiniteBoxUnionComparison and RetractComparison give both arrows as isomorphisms."),
})}

var DeRhamTheorem = deRhamTheoremThm{family.Add(registry.ProofEntry{
	Name: "DeRhamTheorem",
	Key:  "prop_b59a66e944ce471f",
	Deps: []registry.EntryLike{CompactComparison, ComparisonDef},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
			Conclusion: "module_isomorphism(real_ring, " +
				"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    cohomology_module(singular_cochain_complex(T), k), " +
				"    de_rham_comparison⟨n⟩(T, 𝒜, k))",
		},
		"Compose the integration isomorphism with the inverse of continuous-to-smooth "+
			"restriction. This gives the natural real singular comparison map."),
})}

var ComparisonNaturality = comparisonNaturalityThm{family.Add(registry.ProofEntry{
	Name: "ComparisonNaturality",
	Key:  "prop_db84d72424b9877d",
	Deps: []registry.EntryLike{CompactComparison, IntegrationClassNaturality, RestrictionNaturality},
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
				"∀s:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{
				"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
				"compact_in(T, ⋃T)",
				"compact_in(S, ⋃S)",
				"s ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, k).carrier",
			},
			Conclusion: "de_rham_comparison⟨n⟩(T, 𝒜, k)(de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)(s)) = " +
				"singular_cohomology_pullback(T, f, k, de_rham_comparison⟨m⟩(S, ℬ, k)(s))",
		},
		"The integration and restriction squares commute, and both restrictions are bijective on their "+
			"cohomology carriers. Invert those vertical arrows to obtain naturality of the final comparison."),
})}

var SingularHomologyFinite = singularHomologyFiniteThm{family.Add(registry.ProofEntry{
	Name: "SingularHomologyFinite",
	Key:  "prop_32385b4ef7475c4a",
	Deps: []registry.EntryLike{
		DeRhamTheorem,
		singular_cohomology.UniversalCoefficient,
		de_rham_cover.CompactManifoldFiniteCohomology,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
			Conclusion: "finite_dimensional(real_ring, homology_module(singular_complex(real_ring, T), k))",
		},
		"Comparison makes singular cohomology finite dimensional. Universal coefficient identifies "+
			"it with the full algebraic dual of homology; an infinite independent family in homology "+
			"would give arbitrarily many independent coordinate functionals, a contradiction."),
})}

var SingularHomologyAboveDimension = singularHomologyAboveDimensionThm{family.Add(registry.ProofEntry{
	Name: "SingularHomologyAboveDimension",
	Key:  "prop_646c95ab069144cc",
	Deps: []registry.EntryLike{DeRhamTheorem, singular_cohomology.UniversalCoefficient},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)", "n < k"},
			Conclusion: "homology_module(singular_complex(real_ring, T), k).carrier = " +
				"{homology_module(singular_complex(real_ring, T), k).zero}",
		},
		"Forms vanish above dimension n, so comparison makes singular cohomology zero there. A nonzero "+
			"homology vector would admit a nonzero real functional, contradicting universal coefficient."),
})}

var BettiComparison = bettiComparisonThm{family.Add(registry.ProofEntry{
	Name: "BettiComparison",
	Key:  "prop_2555daf6797a81b",
	Deps: []registry.EntryLike{
		DeRhamTheorem,
		SingularHomologyFinite,
		singular_cohomology.UniversalCoefficient,
		module_dimension.DualDim,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num.",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
			Conclusion: "de_rham_betti⟨n⟩(T, 𝒜, k) = singular_betti(T, k)",
		},
		"Use the de Rham comparison and universal coefficient, then "+
			"DualDim for the finite-dimensional real singular homology module."),
})}

var EulerComparison = eulerComparisonThm{family.Add(registry.ProofEntry{
	Name: "EulerComparison",
	Key:  "prop_f296255f30b4f68d",
	Deps: []registry.EntryLike{BettiComparison, SingularHomologyAboveDimension},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
			Conclusion: "de_rham_euler⟨n⟩(T, 𝒜) = singular_euler(T, n)",
		},
		"Sum BettiComparison with alternating signs through degree n. SingularHomologyAboveDimension "+
			"shows this truncation includes every nonzero homology degree."),
})}

var TopologicalGaussBonnetChern = topologicalGaussBonnetChernThm{family.Add(registry.ProofEntry{
	Name: "TopologicalGaussBonnetChern",
	Key:  "prop_df5cffe6e0a54b47",
	Deps: []registry.EntryLike{thom_form.GaussBonnetChern, EulerComparison},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
				"∀m:num.",
			Hypotheses: []string{
				"oriented_manifold⟨n⟩(T, 𝒜)",
				"compact_in(T, ⋃T)",
				"riemannian_metric⟨n⟩(T, 𝒜, g)",
				"n = 2 * m",
			},
			Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, riemannian_euler_form⟨n⟩(T, 𝒜, g)) = " +
				"singular_euler(T, n)",
		},
		"Combine Gauss–Bonnet–Chern with EulerComparison. The metric is arbitrary, "+
			"and the zero-dimensional branch is already included in the geometric theorem."),
})}
