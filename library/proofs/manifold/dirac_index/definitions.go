package dirac_index

import (
	"github.com/euc-ai/xugo/library/registry"
)

var directionalDerivativeDef = directionalDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "directionalDerivativeDef",
	Key:   "prop_528059179946d036",
	Const: "complex_directional_derivative",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → complex) → " +
		"A → " +
		"(prod(set(A), A → num → real) → num → real) → " +
		"complex",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀h:(A → complex). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real). " +
			"    complex_directional_derivative(n, T, 𝒜, h, x, v) = " +
			"    complex_of_real(manifold_euclidean_differential⟨n, 1⟩(T, " +
			"            𝒜, " +
			"            λy:A. λj:num. COND(j = 0, re(h(y)), &0), " +
			"            x, " +
			"            v, " +
			"            0)) + " +
			"    complex_i * " +
			"    complex_of_real(manifold_euclidean_differential⟨n, 1⟩(T, " +
			"            𝒜, " +
			"            λy:A. λj:num. COND(j = 0, im(h(y)), &0), " +
			"            x, " +
			"            v, " +
			"            0))",
	},
})}

var oneFormPairingDef = oneFormPairingDefThm{family.Define(registry.DefEntry{
	Name:  "oneFormPairingDef",
	Key:   "prop_773e9d1c5be8bff7",
	Const: "complex_form_pairing",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"A → " +
		"(prod(set(A), A → num → real) → num → real) → " +
		"complex",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real). " +
			"    complex_form_pairing(n, T, 𝒜, ω, x, v) = " +
			"    COND(x ∈ ⋃T, " +
			"        ω((εc:prod(set(A), A → num → real). compatible_chart⟨n⟩(T, 𝒜, c) ∧ x ∈ fst(c)), " +
			"            snd((εc:prod(set(A), A → num → real). compatible_chart⟨n⟩(T, 𝒜, c) ∧ x ∈ fst(c)))( " +
			"                x), " +
			"            (λi:num. λj:num. " +
			"                COND(j = 0, " +
			"                    v((εc:prod(set(A), A → num → real). " +
			"                            compatible_chart⟨n⟩(T, 𝒜, c) ∧ x ∈ fst(c)), " +
			"                        i), " +
			"                    &0))), " +
			"        complex_of_real(&0))",
	},
})}

var covariantDerivativeDef = covariantDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "covariantDerivativeDef",
	Key:   "prop_fd0500c35bdf3910",
	Deps:  []registry.EntryLike{directionalDerivativeDef, oneFormPairingDef},
	Const: "projected_covariant_derivative",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"(A → num → complex) → " +
		"A → " +
		"(prod(set(A), A → num → real) → num → real) → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀s:(A → num → complex). " +
			"∀x:A. " +
			"∀v:(prod(set(A), A → num → real) → num → real). " +
			"∀i:num. " +
			"    projected_covariant_derivative(n, T, 𝒜, P, Γ, s, x, v, i) = " +
			"    COND(x ∈ ⋃T ∧ i < fst(P), " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {j:num | j < fst(P)}, " +
			"            λj:num. " +
			"                snd(P)(x, i, j) * " +
			"                complex_directional_derivative(n, T, 𝒜, λy:A. s(y, j), x, v) + " +
			"                complex_form_pairing(n, T, 𝒜, Γ(i, j), x, v) * s(x, j)), " +
			"        complex_of_real(&0))",
	},
})}

var tensorConnectionDef = tensorConnectionDefThm{family.Define(registry.DefEntry{
	Name:  "tensorConnectionDef",
	Key:   "prop_9f6bf770b064257c",
	Const: "tensor_projection_connection",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"prod(num, A → num → num → complex) → " +
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
			"∀S E:prod(num, A → num → num → complex). " +
			"∀Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀i j:num. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    tensor_projection_connection(n, T, 𝒜, S, Γ, E, Δ, i, j, c, y, V) = " +
			"    COND(i < fst(S) * fst(E) ∧ j < fst(S) * fst(E), " +
			"        complex_form_wedge(n, " +
			"            T, " +
			"            𝒜, " +
			"            1, " +
			"            0, " +
			"            Γ(nat_div(i, fst(E)), nat_div(j, fst(E))), " +
			"            chern_matrix_function(n, T, 𝒜, snd(E))(nat_mod(i, fst(E)), nat_mod(j, fst(E))), " +
			"            c, " +
			"            y, " +
			"            V) + " +
			"        complex_form_wedge(n, " +
			"            T, " +
			"            𝒜, " +
			"            0, " +
			"            1, " +
			"            chern_matrix_function(n, T, 𝒜, snd(S))(nat_div(i, fst(E)), nat_div(j, fst(E))), " +
			"            Δ(nat_mod(i, fst(E)), nat_mod(j, fst(E))), " +
			"            c, " +
			"            y, " +
			"            V), " +
			"        complex_of_real(&0))",
	},
})}

var cliffordMatrixDef = cliffordMatrixDefThm{family.Define(registry.DefEntry{
	Name:  "cliffordMatrixDef",
	Key:   "prop_73049327f4faeacd",
	Const: "spinor_clifford_matrix",
	Type: "num → " +
		"set(set(A)) → " +
		"num → " +
		"(num → set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → A → num → num → complex) → " +
		"A → " +
		"(num → real) → " +
		"num → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀m L:num. " +
			"∀T:set(set(A)). " +
			"∀U:(num → set(A)). " +
			"∀S:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex). " +
			"∀x:A. " +
			"∀v:(num → real). " +
			"∀i j:num. " +
			"    spinor_clifford_matrix(m, T, L, U, S, W, x, v, i, j) = " +
			"    COND(x ∈ ⋃T ∧ i < fst(S) ∧ j < fst(S), " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {a:num | a < nat_pow(2, m)}, " +
			"            λa:num. " +
			"                module_sum(complex_add, " +
			"                    complex_of_real(&0), " +
			"                    {b:num | b < nat_pow(2, m)}, " +
			"                    λb:num. " +
			"                        W((εi:num. i < L ∧ x ∈ U(i)), x, i, a) * " +
			"                        module_sum(complex_add, " +
			"                            complex_of_real(&0), " +
			"                            {l:num | l < 2 * m}, " +
			"                            λl:num. complex_of_real(v(l)) * spinor_generator(m, l, a, b)) * " +
			"                        complex_conj(W((εi:num. i < L ∧ x ∈ U(i)), x, j, b)))), " +
			"        complex_of_real(&0))",
	},
})}

var OperatorDef = operatorDefThm{family.Define(registry.DefEntry{
	Name:  "OperatorDef",
	Key:   "prop_3bb33e89dfeee55a",
	Deps:  []registry.EntryLike{covariantDerivativeDef, tensorConnectionDef, cliffordMatrixDef},
	Const: "spin_dirac_operator",
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
		"prod(num, A → num → num → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"(A → num → complex) → " +
		"A → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"∀S E:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex). " +
			"∀Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀s:(A → num → complex). " +
			"∀x:A. " +
			"∀i:num. " +
			"    spin_dirac_operator(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ, E, Δ, s, x, i) = " +
			"    COND(x ∈ ⋃T ∧ i < fst(S) * fst(E), " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {l:num | l < 2 * m}, " +
			"            λl:num. " +
			"                module_sum(complex_add, " +
			"                    complex_of_real(&0), " +
			"                    {h:num | h < fst(S) * fst(E)}, " +
			"                    λh:num. " +
			"                        spinor_clifford_matrix(m, " +
			"                            T, " +
			"                            L, " +
			"                            U, " +
			"                            S, " +
			"                            W, " +
			"                            x, " +
			"                            (λj:num. COND(j = l, &1, &0)), " +
			"                            nat_div(i, fst(E)), " +
			"                            nat_div(h, fst(E))) * " +
			"                        snd(E)(x, nat_mod(i, fst(E)), nat_mod(h, fst(E))) * " +
			"                        projected_covariant_derivative(2 * m, " +
			"                            T, " +
			"                            𝒜, " +
			"                            projection_tensor(S, E), " +
			"                            tensor_projection_connection(2 * m, T, 𝒜, S, Γ, E, Δ), " +
			"                            s, " +
			"                            x, " +
			"                            spin_frame_vector(2 * m, " +
			"                                N, " +
			"                                T, " +
			"                                𝒜, " +
			"                                f, " +
			"                                F((εi:num. i < L ∧ x ∈ U(i))), " +
			"                                x, " +
			"                                l), " +
			"                            h))), " +
			"        complex_of_real(&0))",
	},
})}

var SymbolDef = symbolDefThm{family.Define(registry.DefEntry{
	Name:  "SymbolDef",
	Key:   "prop_9a6f335a2e713b08",
	Deps:  []registry.EntryLike{cliffordMatrixDef},
	Const: "spin_dirac_symbol",
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
		"prod(num, A → num → num → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"prod(A, prod(set(A), A → num → real) → num → real) → " +
		"num → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀m N L:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀f:(A → num → real). " +
			"∀U:(num → set(A)). " +
			"∀F:(num → A → num → num → real). " +
			"∀g:(num → num → A → num → real). " +
			"∀S E:prod(num, A → num → num → complex). " +
			"∀W:(num → A → num → num → complex). " +
			"∀Γ Δ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"∀i j:num. " +
			"    spin_dirac_symbol(m, N, T, 𝒜, f, L, U, F, g, S, W, Γ, E, Δ, p, i, j) = " +
			"    COND(p ∈ cotangent_punctured(2 * m, T, 𝒜) ∧ i < fst(S) * fst(E) ∧ j < fst(S) * fst(E), " +
			"        complex_i * " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {a:num | a < fst(S)}, " +
			"            λa:num. " +
			"                spinor_clifford_matrix(m, " +
			"                    T, " +
			"                    L, " +
			"                    U, " +
			"                    S, " +
			"                    W, " +
			"                    fst(p), " +
			"                    (λl:num. " +
			"                        real_sum({h:num | h < 2 * m}, " +
			"                            λh:num. " +
			"                                snd(p)((εc:prod(set(A), A → num → real). " +
			"                                        compatible_chart⟨2 * m⟩(T, 𝒜, c) ∧ fst(p) ∈ fst(c)), " +
			"                                    h) * " +
			"                                spin_frame_vector(2 * m, " +
			"                                    N, " +
			"                                    T, " +
			"                                    𝒜, " +
			"                                    f, " +
			"                                    F((εu:num. u < L ∧ fst(p) ∈ U(u))), " +
			"                                    fst(p), " +
			"                                    l)((εc:prod(set(A), A → num → real). " +
			"                                        compatible_chart⟨2 * m⟩(T, 𝒜, c) ∧ fst(p) ∈ fst(c)), " +
			"                                    h))), " +
			"                    nat_div(i, fst(E)), " +
			"                    a) * " +
			"                snd(spinor_parity(m, T, L, U, S, W, 0))(fst(p), a, nat_div(j, fst(E)))) * " +
			"        snd(E)(fst(p), nat_mod(i, fst(E)), nat_mod(j, fst(E))), " +
			"        complex_of_real(&0))",
	},
})}

var AHatDef = aHatDefThm{family.Define(registry.DefEntry{
	Name:  "AHatDef",
	Key:   "prop_15994d85013d3b64",
	Const: "a_hat_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    a_hat_class(n, T, 𝒜) = " +
			"    εb:(num → set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)). " +
			"        b(0) = de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)) ∧ " +
			"        (∀k:num. b(k) ∈ (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).carrier) ∧ " +
			"        (∀k:num. " +
			"            module_sum((de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).add, " +
			"                (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).zero, " +
			"                {j:num | j ≤ k}, " +
			"                λj:num. de_rham_wedge⟨n⟩(T, 𝒜, 2 * j, 2 * (k - j), b(j), b(k - j))) = " +
			"            tangent_todd_class(n, T, 𝒜, k))",
	},
})}

var IntegrandDef = integrandDefThm{family.Define(registry.DefEntry{
	Name:  "IntegrandDef",
	Key:   "prop_7976995c85554608",
	Deps:  []registry.EntryLike{AHatDef},
	Const: "twisted_dirac_character",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀E:prod(num, A → num → num → complex). " +
			"    twisted_dirac_character(m, T, 𝒜, E) = " +
			"    module_sum((de_rham_cohomology_module⟨2 * m⟩(T, 𝒜, 2 * m)).add, " +
			"        (de_rham_cohomology_module⟨2 * m⟩(T, 𝒜, 2 * m)).zero, " +
			"        {j:num | j ≤ m}, " +
			"        λj:num. " +
			"            de_rham_wedge⟨2 * m⟩(T, " +
			"                𝒜, " +
			"                2 * j, " +
			"                2 * (m - j), " +
			"                a_hat_class(2 * m, T, 𝒜, j), " +
			"                chern_class(2 * m, T, 𝒜, E, m - j)))",
	},
})}
