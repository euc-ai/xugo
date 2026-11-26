package smooth_singular

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/simplicial/singular_cohomology"
	"github.com/euc-ai/xugo/library/proofs/simplicial/singular_set"
	"github.com/euc-ai/xugo/library/registry"
)

var SmoothSingularSet = smoothSingularSetThm{family.Add(registry.ProofEntry{
	Name: "SmoothSingularSet",
	Key:  "prop_148ffb6e457a8aee",
	Deps: []registry.EntryLike{SingularSetDef, simplicesDef},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
			Conclusion: "simplicial_set(smooth_singular_set⟨n⟩(T, 𝒜)) ∧ " +
				"simplicial_map(smooth_singular_set⟨n⟩(T, 𝒜), singular_set(T), (λk:num. λσ:((num → real) → A). σ))",
		},
		"Affine face and degeneracy maps carry simplices to simplices and extend smoothly on "+
			"neighbourhoods. Compose the local extension and then normalize on the new simplex."),
})}

var OpenSubmanifoldSingularSet = openSubmanifoldSingularSetThm{family.Add(registry.ProofEntry{
	Name: "OpenSubmanifoldSingularSet",
	Key:  "prop_f11b959c6c97a4c9",
	Deps: []registry.EntryLike{
		SingularSetDef,
		simplicesDef,
		simplexExtensionDef,
		singular_cohomology.RestrictedSetDef,
		singular_set.SubspaceSingularSimplices,
		smooth_manifold.SmoothOpenInclusion,
		smooth_manifold.SmoothMapCompose,
		smooth_manifold.SmoothMapRestrict,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀W:set(A).",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "W ∈ T"},
			Conclusion: "smooth_singular_set⟨n⟩(subtopology(T, W), open_submanifold_atlas⟨n⟩(T, 𝒜, W)) = " +
				"singular_restricted_set(smooth_singular_set⟨n⟩(T, 𝒜), W)",
		},
		"The face and degeneracy maps do not read the space. A smooth extension into W is one into "+
			"the manifold through the smooth open inclusion. Conversely, shrink an extension's open "+
			"domain to the preimage of W: it is open, still contains the simplex, and maps into W."),
})}

var SmoothSingularMap = smoothSingularMapThm{family.Add(registry.ProofEntry{
	Name: "SmoothSingularMap",
	Key:  "prop_77ffbcd90f800802",
	Deps: []registry.EntryLike{SmoothSingularSet},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀m:num. " +
				"∀S:set(set(B)). " +
				"∀ℬ:set(prod(set(B), B → num → real)). " +
				"∀f:(A → B).",
			Hypotheses: []string{"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)"},
			Conclusion: "simplicial_map(smooth_singular_set⟨n⟩(T, 𝒜), " +
				"    smooth_singular_set⟨m⟩(S, ℬ), " +
				"    singular_map(f))",
		},
		"Compose a simplex extension with the smooth map. Normalization changes only values "+
			"outside the simplex, and postcomposition commutes with its faces and degeneracies."),
})}

var SimplexIntegralExtension = simplexIntegralExtensionThm{family.Add(registry.ProofEntry{
	Name: "SimplexIntegralExtension",
	Key:  "prop_676525f64eabac45",
	Deps: []registry.EntryLike{simplexIntegralDef},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀k:num. " +
				"∀σ:((num → real) → A). " +
				"∀e:prod(set(num → real), (num → real) → A). " +
				"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{
				"smooth_manifold⟨n⟩(T, 𝒜)",
				"σ ∈ smooth_singular_simplices⟨n⟩(T, 𝒜, k)",
				"smooth_simplex_extension⟨n⟩(T, 𝒜, k, σ, e)",
				"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			},
			Conclusion: "smooth_simplex_integral⟨n⟩(T, 𝒜, k, ω, σ) = " +
				"vec_integral⟨k⟩(λx:(num → real). " +
				"        COND(vec⟨k⟩(x) ∧ simplex_affine_coordinates(k, x) ∈ euclidean_simplex(k), " +
				"            manifold_form_pullback⟨k + 1, n⟩(subtopology(euclidean_topology(k + 1), fst(e)), " +
				"                euclidean_atlas(fst(e)), " +
				"                T, " +
				"                𝒜, " +
				"                k, " +
				"                snd(e), " +
				"                ω)((fst(e), λy:(num → real). y), " +
				"                simplex_affine_coordinates(k, x), " +
				"                (λi:num. λj:num. COND(j < k, COND(i = 0, -&1, COND(i = j + 1, &1, &0)), &0))), " +
				"            &0))",
		},
		"Two smooth extensions agree on the affine simplex interior, hence their tangential derivatives "+
			"agree there. Continuity extends the pullback equality to the faces; degree zero is evaluation."),
})}

var SimplexStokes = simplexStokesThm{family.Add(registry.ProofEntry{
	Name: "SimplexStokes",
	Key:  "prop_26377f0abd4af77b",
	Deps: []registry.EntryLike{
		SimplexIntegralExtension,
		differential_form.PullbackExteriorDerivative,
	},
	Reading: "This is Stokes for Euclidean simplices, not the no-boundary manifold Stokes theorem. " +
		"The simplex is closed and has corners, but its extension is smooth on an open neighbourhood.",
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀k:num. " +
				"∀σ:((num → real) → A). " +
				"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{
				"smooth_manifold⟨n⟩(T, 𝒜)",
				"σ ∈ smooth_singular_simplices⟨n⟩(T, 𝒜, k + 1)",
				"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			},
			Conclusion: "smooth_simplex_integral⟨n⟩(T, " +
				"    𝒜, " +
				"    k + 1, " +
				"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω), " +
				"    σ) = " +
				"real_sum({i:num | i ≤ k + 1}, " +
				"    λi:num. " +
				"        (-&1)^i * " +
				"        smooth_simplex_integral⟨n⟩(T, 𝒜, k, ω, smooth_singular_set⟨n⟩(T, 𝒜).d(k + 1, i, σ)))",
		},
		"Pull back to an extension neighbourhood and use coordinate fundamental "+
			"theorems on the reduced affine simplex. The induced boundary orientation "+
			"is the alternating coface sign, including the edge endpoint case."),
})}

var IntegrationCochain = integrationCochainThm{family.Add(registry.ProofEntry{
	Name: "IntegrationCochain",
	Key:  "prop_51cc2e45a2e832fb",
	Deps: []registry.EntryLike{SimplexStokes, singular_cohomology.CochainComplex},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
			Conclusion: "cochain_map(real_ring, " +
				"    de_rham_complex⟨n⟩(T, 𝒜), " +
				"    singular_cochain_complex_of(smooth_singular_set⟨n⟩(T, 𝒜)), " +
				"    de_rham_integration_cochain⟨n⟩(T, 𝒜))",
		},
		"Linearity of integration gives degreewise linearity and simplex Stokes is exactly "+
			"the coboundary identity. The cochain is normalized to zero on nonsmooth simplices."),
})}

var IntegrationNaturality = integrationNaturalityThm{family.Add(registry.ProofEntry{
	Name: "IntegrationNaturality",
	Key:  "prop_33259f4702a2fc88",
	Deps: []registry.EntryLike{
		SimplexIntegralExtension,
		SmoothSingularMap,
		differential_form.PullbackCompose,
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
				"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
			Hypotheses: []string{"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)", "manifold_form_on⟨m⟩(S, ℬ, k, ω)"},
			Conclusion: "de_rham_integration_cochain⟨n⟩(T, " +
				"    𝒜, " +
				"    k, " +
				"    manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω)) = " +
				"singular_cochain_pullback_of(smooth_singular_set⟨n⟩(T, 𝒜), " +
				"    f, " +
				"    k, " +
				"    de_rham_integration_cochain⟨m⟩(S, ℬ, k, ω))",
		},
		"Use the composed smooth simplex extension and functoriality of differential "+
			"- form pullback. Both sides vanish on simplices outside the source carrier."),
})}

var SmallChainsQuasiIsomorphism = smallChainsQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SmallChainsQuasiIsomorphism",
	Key:  "prop_a4ea91b5cdaa26f1",
	Deps: []registry.EntryLike{SmoothSingularSet, ChainComplexDef},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀𝒰:set(set(A)).",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "𝒰 ⊆ T", "⋃T ⊆ ⋃𝒰"},
			Conclusion: "quasi_isomorphism(real_ring, " +
				"    free_complex(real_ring, " +
				"        singular_small_set(smooth_singular_set⟨n⟩(T, 𝒜), 𝒰).simplices, " +
				"        simplicial_boundary(real_ring.add, " +
				"            real_ring.zero, " +
				"            real_ring.one, " +
				"            real_ring.neg, " +
				"            real_ring.mul, " +
				"            singular_small_set(smooth_singular_set⟨n⟩(T, 𝒜), 𝒰).d)), " +
				"    smooth_singular_complex⟨n⟩(T, 𝒜), " +
				"    (λk:num. λz:(((num → real) → A) → real). z))",
		},
		"Barycentric subdivision and its prism homotopy precompose only with affine "+
			"maps, preserving smooth extensions. Compactness of each simplex supplies "+
			"the subdivision depth making its image subordinate to the open cover."),
})}

var SmallCochainsQuasiIsomorphism = smallCochainsQuasiIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SmallCochainsQuasiIsomorphism",
	Key:  "prop_c90fefaf97f814",
	Deps: []registry.EntryLike{SmallChainsQuasiIsomorphism, singular_cohomology.UniversalCoefficient},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀𝒰:set(set(A)). ∀k:num.",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "𝒰 ⊆ T", "⋃T ⊆ ⋃𝒰"},
			Conclusion: "module_isomorphism(real_ring, " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k), " +
				"    cohomology_module( " +
				"        singular_cochain_complex_of(singular_small_set(smooth_singular_set⟨n⟩(T, 𝒜), 𝒰)), k), " +
				"    singular_cohomology_restriction(singular_small_set(smooth_singular_set⟨n⟩(T, 𝒜), 𝒰), k))",
		},
		"Dualize the small-chain homology equivalence over the reals using "+
			"evaluation on homology. No finite-dimensionality hypothesis is used."),
})}

var MayerVietoris = mayerVietorisThm{family.Add(registry.ProofEntry{
	Name: "MayerVietoris",
	Key:  "prop_f197f0568eee1475",
	Deps: []registry.EntryLike{SmallCochainsQuasiIsomorphism, singular_cohomology.CoverLongExact},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U V:set(A). ∀k:num.",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T", "V ∈ T", "U ∪ V = ⋃T"},
			Conclusion: "module_homomorphism(real_ring, " +
				"    cohomology_module(singular_cochain_complex_of( " +
				"            singular_restricted_set(smooth_singular_set⟨n⟩(T, 𝒜), U ∩ V)), " +
				"        k), " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k + 1), " +
				"    singular_cohomology_connecting(smooth_singular_set⟨n⟩(T, 𝒜), U, V, k)) ∧ " +
				"exact_at(cohomology_module(singular_cochain_complex_of( " +
				"            singular_restricted_set(smooth_singular_set⟨n⟩(T, 𝒜), U ∩ V)), " +
				"        k).zero, " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k).carrier, " +
				"    cohomology_module(singular_cover_complex(smooth_singular_set⟨n⟩(T, 𝒜), U, V), k).carrier, " +
				"    cohomology_map(singular_cover_complex(smooth_singular_set⟨n⟩(T, 𝒜), U, V), " +
				"        singular_cover_restriction(smooth_singular_set⟨n⟩(T, 𝒜), U, V), " +
				"        k), " +
				"    cohomology_map(singular_cochain_complex_of( " +
				"            singular_restricted_set(smooth_singular_set⟨n⟩(T, 𝒜), U ∩ V)), " +
				"        singular_cover_difference(smooth_singular_set⟨n⟩(T, 𝒜), U, V), " +
				"        k)) ∧ " +
				"exact_at(smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k + 1).zero, " +
				"    cohomology_module(singular_cover_complex(smooth_singular_set⟨n⟩(T, 𝒜), U, V), k).carrier, " +
				"    cohomology_module(singular_cochain_complex_of( " +
				"            singular_restricted_set(smooth_singular_set⟨n⟩(T, 𝒜), U ∩ V)), " +
				"        k).carrier, " +
				"    cohomology_map(singular_cochain_complex_of( " +
				"            singular_restricted_set(smooth_singular_set⟨n⟩(T, 𝒜), U ∩ V)), " +
				"        singular_cover_difference(smooth_singular_set⟨n⟩(T, 𝒜), U, V), " +
				"        k), " +
				"    singular_cohomology_connecting(smooth_singular_set⟨n⟩(T, 𝒜), U, V, k)) ∧ " +
				"exact_at( " +
				"    cohomology_module(singular_cover_complex(smooth_singular_set⟨n⟩(T, 𝒜), U, V), k + 1).zero, " +
				"    cohomology_module(singular_cochain_complex_of( " +
				"            singular_restricted_set(smooth_singular_set⟨n⟩(T, 𝒜), U ∩ V)), " +
				"        k).carrier, " +
				"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k + 1).carrier, " +
				"    singular_cohomology_connecting(smooth_singular_set⟨n⟩(T, 𝒜), U, V, k), " +
				"    cohomology_map(singular_cover_complex(smooth_singular_set⟨n⟩(T, 𝒜), U, V), " +
				"        singular_cover_restriction(smooth_singular_set⟨n⟩(T, 𝒜), U, V), " +
				"        k + 1))",
		},
		"Smooth extensions restrict to target open sets after shrinking their source "+
			"neighbourhood around the simplex. Small cochains give the comparison, and "+
			"CoverLongExact provides all three recurring exactness positions."),
})}
