package smooth_singular

import (
	"github.com/euc-ai/xugo/library/registry"
)

var simplexExtensionDef = simplexExtensionDefThm{family.Define(registry.DefEntry{
	Name:  "simplexExtensionDef",
	Key:   "prop_402f1752cbafe67f",
	Const: "smooth_simplex_extension",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"((num → real) → A) → " +
		"prod(set(num → real), (num → real) → A) → " +
		"bool",
	Dimensions: []string{"n"},
	Reading: "The extension is on an open neighbourhood in R^(k + 1), and " +
		"agreement is required only on the simplex. This is equivalent to smooth " +
		"extension in its affine hyperplane by composing with an affine retraction.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀σ:((num → real) → A). " +
			"∀e:prod(set(num → real), (num → real) → A). " +
			"    smooth_simplex_extension⟨n⟩(T, 𝒜, k, σ, e) ⇔ " +
			"    fst(e) ∈ euclidean_topology(k + 1) ∧ " +
			"    euclidean_simplex(k) ⊆ fst(e) ∧ " +
			"    smooth_manifold_map⟨k + 1, n⟩(subtopology(euclidean_topology(k + 1), fst(e)), " +
			"        euclidean_atlas(fst(e)), " +
			"        T, " +
			"        𝒜, " +
			"        snd(e)) ∧ " +
			"    (∀y:(num → real). y ∈ euclidean_simplex(k) ⇒ snd(e)(y) = σ(y))",
	},
})}

var simplicesDef = simplicesDefThm{family.Define(registry.DefEntry{
	Name:       "simplicesDef",
	Key:        "prop_1448a68f9461a44d",
	Const:      "smooth_singular_simplices",
	Type:       "num → set(set(A)) → set(prod(set(A), A → num → real)) → num → set((num → real) → A)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{simplexExtensionDef},
	Reading: "Normalization to junk outside the simplex is inherited from singular_simplices. " +
		"Smoothness is asserted of an extension, not of that discontinuously normalized total map.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num. " +
			"    smooth_singular_simplices⟨n⟩(T, 𝒜, k) = " +
			"    {σ:((num → real) → A) | " +
			"        σ ∈ singular_simplices(T, k) ∧ " +
			"        (∃e:prod(set(num → real), (num → real) → A). smooth_simplex_extension⟨n⟩(T, 𝒜, k, σ, e))}",
	},
})}

var SingularSetDef = singularSetDefThm{family.Define(registry.DefEntry{
	Name:  "SingularSetDef",
	Key:   "prop_8b3896e095684669",
	Const: "smooth_singular_set",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"simplicial_ops((num → real) → A)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{simplicesDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    smooth_singular_set⟨n⟩(T, 𝒜) = " +
			"    mk_simplicial(smooth_singular_simplices⟨n⟩(T, 𝒜), singular_set(T).d, singular_set(T).s)",
	},
})}

var ChainComplexDef = chainComplexDefThm{family.Define(registry.DefEntry{
	Name:  "ChainComplexDef",
	Key:   "prop_e4b06fe859d40984",
	Const: "smooth_singular_complex",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"complex_ops(real, ((num → real) → A) → real)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{SingularSetDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    smooth_singular_complex⟨n⟩(T, 𝒜) = " +
			"    free_complex(real_ring, " +
			"        smooth_singular_set⟨n⟩(T, 𝒜).simplices, " +
			"        simplicial_boundary(real_ring.add, " +
			"            real_ring.zero, " +
			"            real_ring.one, " +
			"            real_ring.neg, " +
			"            real_ring.mul, " +
			"            smooth_singular_set⟨n⟩(T, 𝒜).d))",
	},
})}

var CohomologyModuleDef = cohomologyModuleDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyModuleDef",
	Key:   "prop_9a226f71f67950e4",
	Const: "smooth_singular_cohomology_module",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"module_ops(real, set(((num → real) → A) → real))",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{SingularSetDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num. " +
			"    smooth_singular_cohomology_module⟨n⟩(T, 𝒜, k) = " +
			"    cohomology_module(singular_cochain_complex_of(smooth_singular_set⟨n⟩(T, 𝒜)), k)",
	},
})}

var CohomologyPullbackDef = cohomologyPullbackDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyPullbackDef",
	Key:   "prop_3a29cee1c1aa062b",
	Const: "smooth_singular_cohomology_pullback",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → B) → " +
		"num → " +
		"set(((num → real) → B) → real) → " +
		"set(((num → real) → A) → real)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{SingularSetDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → B). " +
			"    smooth_singular_cohomology_pullback⟨n⟩(T, 𝒜, f) = " +
			"    cohomology_map(singular_cochain_complex_of(smooth_singular_set⟨n⟩(T, 𝒜)), " +
			"        singular_cochain_pullback_of(smooth_singular_set⟨n⟩(T, 𝒜), f))",
	},
})}

var affineCoordinatesDef = affineCoordinatesDefThm{family.Define(registry.DefEntry{
	Name:  "affineCoordinatesDef",
	Key:   "prop_bd2fc2158f8e4e99",
	Const: "simplex_affine_coordinates",
	Type:  "num → (num → real) → num → real",
	Reading: "These coordinates map the reduced k-simplex to " +
		"barycentric coordinates in R^(k + 1). The tangent columns are e_(j + " +
		"1)−e_0, so the boundary is the alternating sum of the ordered faces.",
	Equations: []string{
		"∀k:num. ∀x:(num → real). ∀i:num. " +
			"    simplex_affine_coordinates(k, x, i) = " +
			"    COND(i = 0, &1 - real_sum({j:num | j < k}, λj:num. x(j)), COND(i ≤ k, x(i - 1), &0))",
	},
})}

var simplexIntegralDef = simplexIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "simplexIntegralDef",
	Key:   "prop_f0e8d38f40b7031d",
	Const: "smooth_simplex_integral",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"((num → real) → A) → " +
		"real",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{simplicesDef, affineCoordinatesDef},
	Reading: "The integrand is the coefficient of the pullback in the oriented affine simplex " +
		"chart, extended by zero outside the closed simplex. Its discontinuity at the boundary is " +
		"harmless for the iterated Lebesgue integral. Degree zero evaluates the form at the single vertex.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀σ:((num → real) → A). " +
			"    smooth_simplex_integral⟨n⟩(T, 𝒜, k, ω, σ) = " +
			"    COND(σ ∈ smooth_singular_simplices⟨n⟩(T, 𝒜, k), " +
			"        vec_integral⟨k⟩(λx:(num → real). " +
			"                COND(vec⟨k⟩(x) ∧ simplex_affine_coordinates(k, x) ∈ euclidean_simplex(k), " +
			"                    manifold_form_pullback⟨k + 1, n⟩(subtopology(euclidean_topology(k + 1), " +
			"                            fst((εe:prod(set(num → real), (num → real) → A). " +
			"                                    smooth_simplex_extension⟨n⟩(T, 𝒜, k, σ, e)))), " +
			"                        euclidean_atlas(fst((εe:prod(set(num → real), (num → real) → A). " +
			"                                    smooth_simplex_extension⟨n⟩(T, 𝒜, k, σ, e)))), " +
			"                        T, " +
			"                        𝒜, " +
			"                        k, " +
			"                        snd((εe:prod(set(num → real), (num → real) → A). " +
			"                                smooth_simplex_extension⟨n⟩(T, 𝒜, k, σ, e))), " +
			"                        ω)((fst((εe:prod(set(num → real), (num → real) → A). " +
			"                                    smooth_simplex_extension⟨n⟩(T, 𝒜, k, σ, e))), " +
			"                            λy:(num → real). y), " +
			"                        simplex_affine_coordinates(k, x), " +
			"                        (λi:num. λj:num. " +
			"                            COND(j < k, COND(i = 0, -&1, COND(i = j + 1, &1, &0)), &0))), " +
			"                    &0)), " +
			"        &0)",
	},
})}

var IntegrationDef = integrationDefThm{family.Define(registry.DefEntry{
	Name:  "IntegrationDef",
	Key:   "prop_48a48da7c1ae7f5f",
	Const: "de_rham_integration_cochain",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"((num → real) → A) → " +
		"real",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{simplexIntegralDef},
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_integration_cochain⟨n⟩(T, 𝒜, k, ω) = smooth_simplex_integral⟨n⟩(T, 𝒜, k, ω)",
	},
})}

var IntegrationClassDef = integrationClassDefThm{family.Define(registry.DefEntry{
	Name:  "IntegrationClassDef",
	Key:   "prop_a45d5f19ff92c236",
	Const: "de_rham_integration_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(((num → real) → A) → real)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{IntegrationDef, SingularSetDef},
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    de_rham_integration_class⟨n⟩(T, 𝒜) = " +
			"    cohomology_map(singular_cochain_complex_of(smooth_singular_set⟨n⟩(T, 𝒜)), " +
			"        de_rham_integration_cochain⟨n⟩(T, 𝒜))",
	},
})}
