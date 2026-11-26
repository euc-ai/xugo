package spin_geometry

import (
	"github.com/euc-ai/xugo/library/registry"
)

var SpinAtlasDef = spinAtlasDefThm{family.Define(registry.DefEntry{
	Name:  "SpinAtlasDef",
	Key:   "prop_3bf46060c9c8eff1",
	Const: "spin_atlas",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"num → " +
		"(num → set(A)) → " +
		"(num → A → num → num → real) → " +
		"(num → num → A → num → real) → " +
		"bool",
	Equations: []string{
		"∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"    spin_atlas(m, N, T, 𝒜, f, L, U, F, g) ⇔ " +
			"    oriented_manifold⟨2 * m⟩(T, 𝒜) ∧ " +
			"    smooth_manifold_embedding⟨2 * m, N⟩(T, " +
			"        𝒜, " +
			"        euclidean_topology(N), " +
			"        euclidean_atlas({x:(num → real) | vec⟨N⟩(&0, x)}), " +
			"        f) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ ∃i:num. i < L ∧ x ∈ U(i)) ∧ " +
			"    (∀i:num. " +
			"        i < L ⇒ " +
			"        smooth_projection_frame(2 * m, " +
			"            2 * m, " +
			"            T, " +
			"            𝒜, " +
			"            embedding_complex_tangent(2 * m, N, T, 𝒜, f), " +
			"            U(i), " +
			"            λx:A. λa:num. λb:num. complex_of_real(F(i, x, a, b))) ∧ " +
			"        (∀c:prod(set(A), A → num → real). ∀x:A. " +
			"            positive_manifold_chart⟨2 * m⟩(T, 𝒜, c) ∧ x ∈ fst(c) ∩ U(i) ⇒ " +
			"            &0 < " +
			"            determinant(real_ring, " +
			"                2 * m, " +
			"                λa:num. λb:num. " +
			"                    COND(a < 2 * m ∧ b < 2 * m, " +
			"                        real_sum({h:num | h < N}, " +
			"                            λh:num. " +
			"                                F(i, x, h, a) * " +
			"                                vec_jacobian_matrix⟨2 * m, N⟩(f ∘ inverse_on(fst(c), snd(c)), " +
			"                                    snd(c)(x), " +
			"                                    h, " +
			"                                    b)), " +
			"                        &0)))) ∧ " +
			"    (∀i j:num. " +
			"        i < L ∧ j < L ⇒ " +
			"        (∀a:num. " +
			"            smooth_manifold_function⟨2 * m⟩(subtopology(T, U(i) ∩ U(j)), " +
			"                open_submanifold_atlas⟨2 * m⟩(T, 𝒜, U(i) ∩ U(j)), " +
			"                λx:A. g(i, j, x, a))) ∧ " +
			"        (∀x:A. " +
			"            x ∈ U(i) ∩ U(j) ⇒ " +
			"            spin_element(2 * m, g(i, j, x)) ∧ " +
			"            (∀a b:num. " +
			"                spin_vector_action(2 * m, g(i, j, x), a, b) = " +
			"                COND(a < 2 * m ∧ b < 2 * m, " +
			"                    real_sum({h:num | h < N}, λh:num. F(i, x, h, a) * F(j, x, h, b)), " +
			"                    &0)))) ∧ " +
			"    (∀i j k:num. ∀x:A. " +
			"        i < L ∧ j < L ∧ k < L ∧ x ∈ U(i) ∩ U(j) ∩ U(k) ⇒ " +
			"        clifford_product(2 * m, g(i, j, x), g(j, k, x)) = g(i, k, x))",
	},
})}

var spinorRealizationDef = spinorRealizationDefThm{family.Define(registry.DefEntry{
	Name:  "spinorRealizationDef",
	Key:   "prop_c9ca072a14fe8b9b",
	Deps:  []registry.EntryLike{SpinAtlasDef},
	Const: "spinor_realization",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"num → " +
		"(num → set(A)) → " +
		"(num → A → num → num → real) → " +
		"(num → num → A → num → real) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → A → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"∀S:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex). " +
			"    spinor_realization(m, N, T, 𝒜, f, L, U, F, g, S, W) ⇔ " +
			"    spin_atlas(m, N, T, 𝒜, f, L, U, F, g) ∧ " +
			"    smooth_projection_bundle(2 * m, fst(S), T, 𝒜, snd(S)) ∧ " +
			"    (∀i:num. i < L ⇒ smooth_projection_frame(2 * m, nat_pow(2, m), T, 𝒜, S, U(i), W(i))) ∧ " +
			"    (∀i j:num. ∀x:A. ∀a b:num. " +
			"        i < L ∧ j < L ∧ x ∈ U(i) ∩ U(j) ⇒ " +
			"        W(j, x, a, b) = " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {h:num | h < nat_pow(2, m)}, " +
			"            λh:num. W(i, x, a, h) * spinor_representation(m, g(i, j, x), h, b)))",
	},
})}

var ParityDef = parityDefThm{family.Define(registry.DefEntry{
	Name:  "ParityDef",
	Key:   "prop_359c1365a3e57426",
	Const: "spinor_parity",
	Type: "num → " +
		"set(set(A)) → " +
		"num → " +
		"(num → set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → A → num → num → complex) → " +
		"num → " +
		"prod(num, A → num → num → complex)",
	Equations: []string{
		"∀m L e:num. " +
			"∀T:set(set(A)). " +
			"∀U:(num → set(A)). " +
			"∀S:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex). " +
			"    spinor_parity(m, T, L, U, S, W, e) = " +
			"    (fst(S), " +
			"        λx:A. λa:num. λc:num. " +
			"            COND(x ∈ ⋃T, " +
			"                module_sum(complex_add, " +
			"                    complex_of_real(&0), " +
			"                    {b:num | b < nat_pow(2, m) ∧ nat_mod(card(exterior_mask(m, b)), 2) = e}, " +
			"                    λb:num. " +
			"                        W((εi:num. i < L ∧ x ∈ U(i)), x, a, b) * " +
			"                        complex_conj(W((εi:num. i < L ∧ x ∈ U(i)), x, c, b))), " +
			"                complex_of_real(&0)))",
	},
})}

var localSpinConnectionDef = localSpinConnectionDefThm{family.Define(registry.DefEntry{
	Name:  "localSpinConnectionDef",
	Key:   "prop_b99725c4c47563a4",
	Const: "spin_local_connection",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(num → A → num → num → real) → " +
		"num → " +
		"num → " +
		"num → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"complex",
	Equations: []string{
		"∀m N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀F:(num → A → num → num → real). " +
			"∀i p q:num. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    spin_local_connection(m, N, T, 𝒜, F, i, p, q, c, y, V) = " +
			"    module_sum(complex_add, " +
			"        complex_of_real(&0), " +
			"        {a:num | a < 2 * m}, " +
			"        λa:num. " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                {b:num | b < 2 * m}, " +
			"                λb:num. " +
			"                    complex_of_real(-(real_sum({h:num | h < N}, " +
			"                                λh:num. " +
			"                                    manifold_form_wedge⟨2 * m⟩(T, " +
			"                                        𝒜, " +
			"                                        0, " +
			"                                        1, " +
			"                                        manifold_function_form⟨2 * m⟩(T, " +
			"                                            𝒜, " +
			"                                            λx:A. F(i, x, h, a)), " +
			"                                        manifold_exterior_derivative⟨2 * m⟩(T, " +
			"                                            𝒜, " +
			"                                            0, " +
			"                                            manifold_function_form⟨2 * m⟩(T, " +
			"                                                𝒜, " +
			"                                                λx:A. F(i, x, h, b))))(c, y, V))) / " +
			"                        &4) * " +
			"                    matrix_mul(complex_add, " +
			"                        complex_mul, " +
			"                        nat_pow(2, m), " +
			"                        spinor_generator(m, a), " +
			"                        spinor_generator(m, b), " +
			"                        p, " +
			"                        q)))",
	},
})}

var SpinConnectionDef = spinConnectionDefThm{family.Define(registry.DefEntry{
	Name:  "SpinConnectionDef",
	Key:   "prop_19f874fd26e83963",
	Deps:  []registry.EntryLike{spinorRealizationDef, localSpinConnectionDef},
	Const: "spinor_connection",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"num → " +
		"(num → set(A)) → " +
		"(num → A → num → num → real) → " +
		"(num → num → A → num → real) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → A → num → num → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"bool",
	Equations: []string{
		"∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"∀S:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"    spinor_connection(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ) ⇔ " +
			"    spinor_realization(m, N, T, 𝒜, f, L, U, F, g, S, W) ∧ " +
			"    projection_connection(2 * m, T, 𝒜, S, Γ) ∧ " +
			"    (∀i p q:num. ∀c:prod(set(A), A → num → real). ∀y:(num → real). ∀V:(num → num → real). " +
			"        i < L ∧ compatible_chart⟨2 * m⟩(T, 𝒜, c) ∧ fst(c) ⊆ U(i) ∧ y ∈ image(snd(c), fst(c)) ⇒ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {a:num | a < fst(S)}, " +
			"            λa:num. " +
			"                complex_form_wedge(2 * m, " +
			"                    T, " +
			"                    𝒜, " +
			"                    0, " +
			"                    1, " +
			"                    chern_matrix_function(2 * m, " +
			"                        T, " +
			"                        𝒜, " +
			"                        (λx:A. λa:num. λb:num. complex_conj(W(i, x, b, a))))(p, a), " +
			"                    complex_form_derivative(2 * m, " +
			"                        T, " +
			"                        𝒜, " +
			"                        0, " +
			"                        chern_matrix_function(2 * m, T, 𝒜, W(i))(a, q)))(c, y, V) + " +
			"                module_sum(complex_add, " +
			"                    complex_of_real(&0), " +
			"                    {b:num | b < fst(S)}, " +
			"                    λb:num. " +
			"                        complex_form_wedge(2 * m, " +
			"                            T, " +
			"                            𝒜, " +
			"                            0, " +
			"                            1, " +
			"                            chern_matrix_function(2 * m, " +
			"                                T, " +
			"                                𝒜, " +
			"                                (λx:A. λa:num. λb:num. complex_conj(W(i, x, b, a))))(p, a), " +
			"                            complex_form_wedge(2 * m, " +
			"                                T, " +
			"                                𝒜, " +
			"                                1, " +
			"                                0, " +
			"                                Γ(a, b), " +
			"                                chern_matrix_function(2 * m, T, 𝒜, W(i))(b, q)))(c, y, V))) = " +
			"        spin_local_connection(m, N, T, 𝒜, F, i, p, q, c, y, V))",
	},
})}

var FrameVectorDef = frameVectorDefThm{family.Define(registry.DefEntry{
	Name:  "FrameVectorDef",
	Key:   "prop_afc8cad005ec7fc",
	Const: "spin_frame_vector",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → real) → " +
		"(A → num → num → real) → " +
		"A → " +
		"num → " +
		"prod(set(A), A → num → real) → " +
		"num → " +
		"real",
	Equations: []string{
		"∀n N:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀F:(A → num → num → real). " +
			"∀x:A. " +
			"∀j:num. " +
			"    spin_frame_vector(n, N, T, 𝒜, f, F, x, j) = " +
			"    εv:(prod(set(A), A → num → real) → num → real). " +
			"        tangent_vector_on⟨n⟩(T, 𝒜, x, v) ∧ " +
			"        manifold_euclidean_differential⟨n, N⟩(T, 𝒜, f, x, v) = (λi:num. F(x, i, j))",
	},
})}
