package cohomological_index

import (
	"github.com/euc-ai/xugo/library/registry"
)

var symplecticAtlasDef = symplecticAtlasDefThm{family.Define(registry.DefEntry{
	Name:  "symplecticAtlasDef",
	Key:   "prop_857b1b4bc473dbf8",
	Const: "cotangent_symplectic_atlas",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"        prod(A, prod(set(A), A → num → real) → num → real) → num → real))",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    cotangent_symplectic_atlas(n, T, 𝒜) = " +
			"    image(λc:prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → real). " +
			"            (fst(c), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). λi:num. " +
			"                    COND(i < 2 * n, " +
			"                        snd(c)(p, COND(nat_mod(i, 2) = 0, nat_div(i, 2), n + nat_div(i, 2))), " +
			"                        &0)), " +
			"        cotangent_atlas(n, T, 𝒜))",
	},
})}

var TangentToddDef = tangentToddDefThm{family.Define(registry.DefEntry{
	Name:  "TangentToddDef",
	Key:   "prop_3c246818a2cc1a5b",
	Const: "tangent_todd_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num. " +
			"    tangent_todd_class(n, T, 𝒜, k) = " +
			"    εa:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    ∃N:num. " +
			"    ∃f:(A → num → real). " +
			"        smooth_manifold_embedding⟨n, N⟩(T, " +
			"            𝒜, " +
			"            euclidean_topology(N), " +
			"            euclidean_atlas({x:(num → real) | vec⟨N⟩(&0, x)}), " +
			"            f) ∧ " +
			"        a = todd_class(n, T, 𝒜, embedding_complex_tangent(n, N, T, 𝒜, f), k)",
	},
})}

var IntegrandDef = integrandDefThm{family.Define(registry.DefEntry{
	Name:  "IntegrandDef",
	Key:   "prop_b089209235077d4e",
	Deps:  []registry.EntryLike{TangentToddDef},
	Const: "index_character_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"        prod(prod(num, " +
		"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"            prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))) → " +
		"set(prod(set(prod(A, prod(set(A), A → num → real) → num → real)), " +
		"        prod(A, prod(set(A), A → num → real) → num → real) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))). " +
			"    index_character_class(n, T, 𝒜, a) = " +
			"    module_sum((compact_de_rham_module(2 * n, " +
			"                cotangent_topology(n, T, 𝒜), " +
			"                cotangent_atlas(n, T, 𝒜), " +
			"                2 * n)).add, " +
			"        (compact_de_rham_module(2 * n, " +
			"                cotangent_topology(n, T, 𝒜), " +
			"                cotangent_atlas(n, T, 𝒜), " +
			"                2 * n)).zero, " +
			"        {j:num | j ≤ n}, " +
			"        λj:num. " +
			"            compact_de_rham_product(2 * n, " +
			"                cotangent_topology(n, T, 𝒜), " +
			"                cotangent_atlas(n, T, 𝒜), " +
			"                2 * j, " +
			"                2 * (n - j), " +
			"                compact_chern_class(2 * n, " +
			"                    cotangent_topology(n, T, 𝒜), " +
			"                    cotangent_atlas(n, T, 𝒜), " +
			"                    a, " +
			"                    j), " +
			"                de_rham_pullback⟨2 * n, n⟩(cotangent_topology(n, T, 𝒜), " +
			"                    cotangent_atlas(n, T, 𝒜), " +
			"                    T, " +
			"                    𝒜, " +
			"                    2 * (n - j), " +
			"                    λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                    tangent_todd_class(n, T, 𝒜, n - j))))",
	},
})}

var CohomologicalIndexDef = cohomologicalIndexDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologicalIndexDef",
	Key:   "prop_29a5104660d170aa",
	Deps:  []registry.EntryLike{symplecticAtlasDef, IntegrandDef},
	Const: "cohomological_index",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"        prod(prod(num, " +
		"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"            prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))) → " +
		"real",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))). " +
			"    cohomological_index(n, T, 𝒜, a) = " +
			"    real_pow(-&1, n) * " +
			"    compact_de_rham_integral(2 * n, " +
			"        cotangent_topology(n, T, 𝒜), " +
			"        cotangent_symplectic_atlas(n, T, 𝒜), " +
			"        index_character_class(n, T, 𝒜, a))",
	},
})}
