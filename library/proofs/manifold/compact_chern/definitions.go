package compact_chern

import (
	"github.com/euc-ai/xugo/library/registry"
)

var smoothTripleDef = smoothTripleDefThm{family.Define(registry.DefEntry{
	Name:  "smoothTripleDef",
	Key:   "prop_8a25bbf67ef7ea96",
	Const: "smooth_kc_triple",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"bool",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀t:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    smooth_kc_triple(n, T, 𝒜, t) ⇔ " +
			"    kc_triple(T, t) ∧ " +
			"    smooth_projection_bundle(n, fst(fst(t)), T, 𝒜, snd(fst(t))) ∧ " +
			"    smooth_projection_bundle(n, fst(fst(snd(t))), T, 𝒜, snd(fst(snd(t)))) ∧ " +
			"    (∀i j:num. " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. re(snd(snd(t))(x, i, j))) ∧ " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. im(snd(snd(t))(x, i, j))))",
	},
})}

var covariantMapDerivativeDef = covariantMapDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "covariantMapDerivativeDef",
	Key:   "prop_6c3fdfac0ab7f8df",
	Const: "relative_map_derivative",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"num → " +
		"num → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"complex",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀t:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∀Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀i j:num. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    relative_map_derivative(n, T, 𝒜, t, Γ, Δ, i, j, c, y, V) = " +
			"    module_sum(complex_add, " +
			"        complex_of_real(&0), " +
			"        {l:num | l < fst(fst(snd(t)))}, " +
			"        λl:num. " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {h:num | h < fst(fst(t))}, " +
			"                λh:num. " +
			"                    complex_form_wedge(n, " +
			"                        T, " +
			"                        𝒜, " +
			"                        0, " +
			"                        1, " +
			"                        chern_matrix_function(n, T, 𝒜, snd(fst(snd(t))))(i, l), " +
			"                        complex_form_wedge(n, " +
			"                            T, " +
			"                            𝒜, " +
			"                            1, " +
			"                            0, " +
			"                            complex_form_derivative(n, " +
			"                                T, " +
			"                                𝒜, " +
			"                                0, " +
			"                                chern_matrix_function(n, T, 𝒜, snd(snd(t)))(l, h)), " +
			"                            chern_matrix_function(n, T, 𝒜, snd(fst(t)))(h, j)))(c, y, V))) + " +
			"    module_sum(complex_add, " +
			"        complex_of_real(&0), " +
			"        {l:num | l < fst(fst(snd(t)))}, " +
			"        λl:num. " +
			"            complex_form_wedge(n, " +
			"                T, " +
			"                𝒜, " +
			"                1, " +
			"                0, " +
			"                Δ(i, l), " +
			"                chern_matrix_function(n, T, 𝒜, snd(snd(t)))(l, j))(c, y, V)) - " +
			"    module_sum(complex_add, " +
			"        complex_of_real(&0), " +
			"        {l:num | l < fst(fst(t))}, " +
			"        λl:num. " +
			"            complex_form_wedge(n, " +
			"                T, " +
			"                𝒜, " +
			"                0, " +
			"                1, " +
			"                chern_matrix_function(n, T, 𝒜, snd(snd(t)))(i, l), " +
			"                Γ(l, j))(c, y, V))",
	},
})}

var adaptedConnectionsDef = adaptedConnectionsDefThm{family.Define(registry.DefEntry{
	Name:  "adaptedConnectionsDef",
	Key:   "prop_83ebf075b1e65bca",
	Deps:  []registry.EntryLike{smoothTripleDef, covariantMapDerivativeDef},
	Const: "relative_chern_connections",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(prod(num, A → num → num → complex), " +
		"    prod(prod(num, A → num → num → complex), A → num → num → complex)) → " +
		"set(A) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"bool",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀t:prod(prod(num, A → num → num → complex), " +
			"        prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"∀K:set(A). " +
			"∀Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"    relative_chern_connections(n, T, 𝒜, t, K, Γ, Δ) ⇔ " +
			"    smooth_kc_triple(n, T, 𝒜, t) ∧ " +
			"    kc_supported_in(T, K, t) ∧ " +
			"    projection_connection(n, T, 𝒜, fst(t), Γ) ∧ " +
			"    projection_connection(n, T, 𝒜, fst(snd(t)), Δ) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀y:(num → real). ∀V:(num → num → real). ∀i j:num. " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"        y ∈ image(snd(c), fst(c)) ∧ " +
			"        inverse_on(fst(c), snd(c), y) ∉ K ⇒ " +
			"        relative_map_derivative(n, T, 𝒜, t, Γ, Δ, i, j, c, y, V) = complex_of_real(&0))",
	},
})}

var CharacterDef = characterDefThm{family.Define(registry.DefEntry{
	Name:  "CharacterDef",
	Key:   "prop_d1408128582b8b4a",
	Deps:  []registry.EntryLike{adaptedConnectionsDef},
	Const: "compact_chern_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"∀k:num. " +
			"    compact_chern_class(n, T, 𝒜, a, k) = " +
			"    εb:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    ∃t:prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"    ∃K:set(A). " +
			"    ∃Γ Δ:(num → " +
			"            num → " +
			"            prod(set(A), A → num → real) → " +
			"            (num → real) → " +
			"            (num → num → real) → " +
			"            complex). " +
			"        relative_chern_connections(n, T, 𝒜, t, K, Γ, Δ) ∧ " +
			"        a = kc_class(T, t) ∧ " +
			"        b = " +
			"        compact_de_rham_class(n, " +
			"            T, " +
			"            𝒜, " +
			"            2 * k, " +
			"            (λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). " +
			"                chern_form(n, T, 𝒜, fst(t), Γ, k, c, y, V) - " +
			"                chern_form(n, T, 𝒜, fst(snd(t)), Δ, k, c, y, V)))",
	},
})}
