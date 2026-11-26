package embedding_normal

import (
	"github.com/euc-ai/xugo/library/registry"
)

var NormalProjectionDef = normalProjectionDefThm{family.Define(registry.DefEntry{
	Name:  "NormalProjectionDef",
	Key:   "prop_7c4361d1454f4bf2",
	Const: "embedding_normal_projection",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"A → " +
		"num → " +
		"num → " +
		"real",
	Equations: []string{
		"∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → num → real). ∀x:A. " +
			"    embedding_normal_projection(n, N, T, 𝒜, f, x) = " +
			"    COND(x ∈ ⋃T, " +
			"        εR:(num → num → real). " +
			"            (∀i j:num. N ≤ i ∨ N ≤ j ⇒ R(i, j) = &0) ∧ " +
			"            (∀i j:num. R(i, j) = R(j, i)) ∧ " +
			"            (∀i j:num. " +
			"                i < N ∧ j < N ⇒ " +
			"                real_sum({k:num | k < N}, λk:num. R(i, k) * R(k, j)) = R(i, j)) ∧ " +
			"            image(λu:(num → real). λi:num. " +
			"                    COND(i < N, real_sum({j:num | j < N}, λj:num. R(i, j) * u(j)), &0), " +
			"                {u:(num → real) | vec⟨N⟩(&0, u)}) = " +
			"            {u:(num → real) | " +
			"                vec⟨N⟩(&0, u) ∧ " +
			"                (∀v:(prod(set(A), A → num → real) → num → real). " +
			"                    tangent_vector_on⟨n⟩(T, 𝒜, x, v) ⇒ " +
			"                    real_sum({i:num | i < N}, " +
			"                        λi:num. " +
			"                            u(i) * manifold_euclidean_differential⟨n, N⟩(T, 𝒜, f, x, v, i)) = " +
			"                    &0)}, " +
			"        λi:num. λj:num. &0)",
	},
})}

var NormalBundleDef = normalBundleDefThm{family.Define(registry.DefEntry{
	Name:  "NormalBundleDef",
	Key:   "prop_ea96145e647bb0db",
	Deps:  []registry.EntryLike{NormalProjectionDef},
	Const: "embedding_normal_bundle",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"prod(num, A → num → num → complex)",
	Equations: []string{
		"∀n N:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → num → real). " +
			"    embedding_normal_bundle(n, N, T, 𝒜, f) = " +
			"    (N, " +
			"        λx:A. λi:num. λj:num. " +
			"            complex_of_real(embedding_normal_projection(n, N, T, 𝒜, f)(x, i, j)))",
	},
})}

var ComplexTangentDef = complexTangentDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexTangentDef",
	Key:   "prop_f3d3a216c274fda4",
	Deps:  []registry.EntryLike{NormalBundleDef},
	Const: "embedding_complex_tangent",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"prod(num, A → num → num → complex)",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀N:num. ∀f:(A → num → real). " +
			"    embedding_complex_tangent(n, N, T, 𝒜, f) = " +
			"    (N, " +
			"        λx:A. λi:num. λj:num. " +
			"            COND(x ∈ ⋃T ∧ i < N ∧ j < N, " +
			"                COND(i = j, complex_of_real(&1), complex_of_real(&0)) - " +
			"                snd(embedding_normal_bundle(n, N, T, 𝒜, f))(x, i, j), " +
			"                complex_of_real(&0)))",
	},
})}
