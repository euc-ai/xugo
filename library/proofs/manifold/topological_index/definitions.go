package topological_index

import (
	"github.com/euc-ai/xugo/library/registry"
)

var TangentNormalDef = tangentNormalDefThm{family.Define(registry.DefEntry{
	Name:  "TangentNormalDef",
	Key:   "prop_f01b1bc3ce1c09ce",
	Const: "index_tangent_normal",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex)",
	Equations: []string{
		"∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → num → real). " +
			"    index_tangent_normal(n, N, T, 𝒜, f) = " +
			"    projection_pullback(tangent_topology⟨n⟩(T, 𝒜), " +
			"        λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"        embedding_normal_bundle(n, N, T, 𝒜, f))",
	},
})}

var tangentEmbeddingDef = tangentEmbeddingDefThm{family.Define(registry.DefEntry{
	Name:  "tangentEmbeddingDef",
	Key:   "prop_85dc30ad134c922",
	Const: "index_tangent_embedding",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"prod(A, prod(set(A), A → num → real) → num → real) → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"∀i:num. " +
			"    index_tangent_embedding(n, N, T, 𝒜, f, p, i) = " +
			"    COND(i < N, " +
			"        complex_of_real(f(fst(p), i)) + " +
			"        complex_i * " +
			"        complex_of_real(manifold_euclidean_differential⟨n, N⟩(T, 𝒜, f, fst(p), snd(p), i)), " +
			"        complex_of_real(&0))",
	},
})}

var normalDerivativeDef = normalDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "normalDerivativeDef",
	Key:   "prop_63b0a2d98dc5f0e5",
	Const: "index_normal_derivative",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"prod(A, prod(set(A), A → num → real) → num → real) → " +
		"num → " +
		"num → " +
		"real",
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"∀i j:num. " +
			"    index_normal_derivative(n, N, T, 𝒜, f, p, i, j) = " +
			"    manifold_euclidean_differential⟨n, 1⟩(T, " +
			"        𝒜, " +
			"        λx:A. λk:num. COND(k = 0, embedding_normal_projection(n, N, T, 𝒜, f)(x, i, j), &0), " +
			"        fst(p), " +
			"        snd(p), " +
			"        0)",
	},
})}

var tangentGermDef = tangentGermDefThm{family.Define(registry.DefEntry{
	Name:  "tangentGermDef",
	Key:   "prop_638471c270a02104",
	Deps:  []registry.EntryLike{normalDerivativeDef},
	Const: "index_tubular_germ",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex) → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀z:prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex). " +
			"∀i:num. " +
			"    index_tubular_germ(n, N, T, 𝒜, f, z, i) = " +
			"    COND(i < N, " +
			"        complex_of_real(f(fst(fst(z)), i) + re(snd(z)(i))) + " +
			"        complex_i * " +
			"        complex_of_real(manifold_euclidean_differential⟨n, N⟩(T, " +
			"                𝒜, " +
			"                f, " +
			"                fst(fst(z)), " +
			"                snd(fst(z)), " +
			"                i) + " +
			"            im(snd(z)(i)) + " +
			"            real_sum({j:num | j < N}, " +
			"                λj:num. index_normal_derivative(n, N, T, 𝒜, f, fst(z), i, j) * re(snd(z)(j)))), " +
			"        complex_of_real(&0))",
	},
})}

var TangentTubeDef = tangentTubeDefThm{family.Define(registry.DefEntry{
	Name:  "TangentTubeDef",
	Key:   "prop_87d961768d4ae7af",
	Deps:  []registry.EntryLike{TangentNormalDef, tangentEmbeddingDef, tangentGermDef},
	Const: "index_tangent_tube",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"(prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex) → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀h:(prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex) → num → complex). " +
			"    index_tangent_tube(n, N, T, 𝒜, f, h) ⇔ " +
			"    k_tubular_presentation(tangent_topology⟨n⟩(T, 𝒜), " +
			"        complex_coordinate_topology(N), " +
			"        index_tangent_normal(n, N, T, 𝒜, f), " +
			"        index_tangent_embedding(n, N, T, 𝒜, f), " +
			"        h) ∧ " +
			"    ∃ε:real. " +
			"        &0 < ε ∧ " +
			"        (∀z:prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex). " +
			"            z ∈ " +
			"            projection_total_space(tangent_topology⟨n⟩(T, 𝒜), " +
			"                index_tangent_normal(n, N, T, 𝒜, f)) ∧ " +
			"            real_sum({j:num | j < N}, λj:num. real_pow(|snd(z)(j)|, 2)) < real_pow(ε, 2) ⇒ " +
			"            h(z) = index_tubular_germ(n, N, T, 𝒜, f, z))",
	},
})}

var EuclideanBottTripleDef = euclideanBottTripleDefThm{family.Define(registry.DefEntry{
	Name:  "EuclideanBottTripleDef",
	Key:   "prop_e938cb9139569d6e",
	Const: "index_bott_triple",
	Type: "num → " +
		"prod(prod(num, (num → complex) → num → num → complex), " +
		"    prod(prod(num, (num → complex) → num → num → complex), " +
		"        (num → complex) → num → num → complex))",
	Equations: []string{
		"∀N:num. " +
			"    index_bott_triple(N) = " +
			"    ((nat_pow(2, N), " +
			"            λz:(num → complex). λa:num. λb:num. " +
			"                COND(z ∈ ⋃complex_coordinate_topology(N) ∧ " +
			"                    a < nat_pow(2, N) ∧ " +
			"                    a = b ∧ " +
			"                    nat_mod(card(exterior_mask(N, a)), 2) = 0, " +
			"                    complex_of_real(&1), " +
			"                    complex_of_real(&0))), " +
			"        ((nat_pow(2, N), " +
			"                λz:(num → complex). λa:num. λb:num. " +
			"                    COND(z ∈ ⋃complex_coordinate_topology(N) ∧ " +
			"                        a < nat_pow(2, N) ∧ " +
			"                        a = b ∧ " +
			"                        nat_mod(card(exterior_mask(N, a)), 2) = 1, " +
			"                        complex_of_real(&1), " +
			"                        complex_of_real(&0))), " +
			"            λz:(num → complex). λa:num. λb:num. " +
			"                COND(z ∈ ⋃complex_coordinate_topology(N) ∧ " +
			"                    nat_mod(card(exterior_mask(N, b)), 2) = 0, " +
			"                    koszul_ambient_matrix(N, z, a, b), " +
			"                    complex_of_real(&0))))",
	},
})}

var bottMultipleDef = bottMultipleDefThm{family.Define(registry.DefEntry{
	Name:  "bottMultipleDef",
	Key:   "prop_29aa4068df49dc2a",
	Deps:  []registry.EntryLike{EuclideanBottTripleDef},
	Const: "index_bott_multiple",
	Type: "num → " +
		"int → " +
		"set(prod(prod(num, (num → complex) → num → num → complex), " +
		"        prod(prod(num, (num → complex) → num → num → complex), " +
		"            (num → complex) → num → num → complex)))",
	Equations: []string{
		"∀N:num. ∀k:int. " +
			"    index_bott_multiple(N, k) = " +
			"    COND(int_of_num(0) ≤ k, " +
			"        monoid_pow(kc_add(complex_coordinate_topology(N)), " +
			"            (kc_group(complex_coordinate_topology(N))).one, " +
			"            kc_class(complex_coordinate_topology(N), index_bott_triple(N)), " +
			"            num_of_int(k)), " +
			"        kc_negate(complex_coordinate_topology(N), " +
			"            monoid_pow(kc_add(complex_coordinate_topology(N)), " +
			"                (kc_group(complex_coordinate_topology(N))).one, " +
			"                kc_class(complex_coordinate_topology(N), index_bott_triple(N)), " +
			"                num_of_int(-k))))",
	},
})}

var EmbeddingIndexDef = embeddingIndexDefThm{family.Define(registry.DefEntry{
	Name:  "EmbeddingIndexDef",
	Key:   "prop_6534e4703f114fc4",
	Deps:  []registry.EntryLike{TangentNormalDef, bottMultipleDef},
	Const: "embedding_topological_index",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"(prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex) → num → complex) → " +
		"set(prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"        prod(prod(num, " +
		"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"            prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))) → " +
		"int",
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀h:(prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex) → num → complex). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))). " +
			"    embedding_topological_index(n, N, T, 𝒜, f, h, a) = " +
			"    εk:int. " +
			"        index_bott_multiple(N, k) = " +
			"        kc_tubular_pushforward(tangent_topology⟨n⟩(T, 𝒜), " +
			"            complex_coordinate_topology(N), " +
			"            index_tangent_normal(n, N, T, 𝒜, f), " +
			"            h, " +
			"            a)",
	},
})}

var IndexDef = indexDefThm{family.Define(registry.DefEntry{
	Name:  "IndexDef",
	Key:   "prop_8fd0f1d5eafe6ea",
	Deps:  []registry.EntryLike{TangentTubeDef, EmbeddingIndexDef},
	Const: "topological_index",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"        prod(prod(num, " +
		"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"            prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))) → " +
		"int",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))). " +
			"    topological_index(n, T, 𝒜, a) = " +
			"    εk:int. " +
			"    ∃N:num. " +
			"    ∃f:(A → num → real). " +
			"    ∃g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"    ∃h:(prod(prod(A, prod(set(A), A → num → real) → num → real), num → complex) → " +
			"            num → " +
			"            complex). " +
			"        smooth_manifold_embedding⟨n, N⟩(T, " +
			"            𝒜, " +
			"            euclidean_topology(N), " +
			"            euclidean_atlas({y:(num → real) | vec⟨N⟩(&0, y)}), " +
			"            f) ∧ " +
			"        riemannian_metric⟨n⟩(T, 𝒜, g) ∧ " +
			"        index_tangent_tube(n, N, T, 𝒜, f, h) ∧ " +
			"        k = " +
			"        embedding_topological_index(n, " +
			"            N, " +
			"            T, " +
			"            𝒜, " +
			"            f, " +
			"            h, " +
			"            kc_pullback(tangent_topology⟨n⟩(T, 𝒜), cotangent_metric_flat(n, T, 𝒜, g), a))",
	},
})}
