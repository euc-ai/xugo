package pseudo_differential

import (
	"github.com/euc-ai/xugo/library/registry"
)

var smoothModuleDef = smoothModuleDefThm{family.Define(registry.DefEntry{
	Name:  "smoothModuleDef",
	Key:   "prop_51a8103e387ba0ec",
	Const: "ps_smooth_module",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"module_ops(complex, A → num → complex)",
	Equations: []string{
		"∀n r:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀P:(A → num → num → complex). " +
			"    ps_smooth_module(n, r, T, 𝒜, P) = " +
			"    mk_module(λf:(A → num → complex). λg:(A → num → complex). λx:A. λi:num. f(x, i) + g(x, i), " +
			"        λx:A. λi:num. complex_of_real(&0), " +
			"        λf:(A → num → complex). λx:A. λi:num. -f(x, i), " +
			"        λz:complex. λf:(A → num → complex). λx:A. λi:num. z * f(x, i), " +
			"        {f:(A → num → complex) | smooth_projected_section(n, r, T, 𝒜, P, f)})",
	},
})}

var PuncturedDef = puncturedDefThm{family.Define(registry.DefEntry{
	Name:  "PuncturedDef",
	Key:   "prop_413fa3dbd504dbe6",
	Const: "cotangent_punctured",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(A, prod(set(A), A → num → real) → num → real))",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    cotangent_punctured(n, T, 𝒜) = " +
			"    {p:prod(A, prod(set(A), A → num → real) → num → real) | " +
			"        p ∈ cotangent_bundle(n, T, 𝒜) ∧ snd(p) ≠ (λc:prod(set(A), A → num → real). λi:num. &0)}",
	},
})}

var PrincipalSymbolDef = principalSymbolDefThm{family.Define(registry.DefEntry{
	Name:  "PrincipalSymbolDef",
	Key:   "prop_2ebf80af1576c22e",
	Deps:  []registry.EntryLike{PuncturedDef},
	Const: "ps_principal_symbol",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"int → " +
		"(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀m:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"    ps_principal_symbol(n, r, q, T, 𝒜, P, Q, m, σ) ⇔ " +
			"    smooth_projection_bundle(n, r, T, 𝒜, P) ∧ " +
			"    smooth_projection_bundle(n, q, T, 𝒜, Q) ∧ " +
			"    (∀p:prod(A, prod(set(A), A → num → real) → num → real). ∀i j:num. " +
			"        p ∉ cotangent_punctured(n, T, 𝒜) ∨ q ≤ i ∨ r ≤ j ⇒ σ(p, i, j) = complex_of_real(&0)) ∧ " +
			"    (∀p:prod(A, prod(set(A), A → num → real) → num → real). ∀i j:num. " +
			"        p ∈ cotangent_punctured(n, T, 𝒜) ∧ i < q ∧ j < r ⇒ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < q}, " +
			"            λk:num. Q(fst(p), i, k) * σ(p, k, j)) = " +
			"        σ(p, i, j) ∧ " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < r}, " +
			"            λk:num. σ(p, i, k) * P(fst(p), k, j)) = " +
			"        σ(p, i, j)) ∧ " +
			"    (∀p:prod(A, prod(set(A), A → num → real) → num → real). ∀t:real. ∀i j:num. " +
			"        p ∈ cotangent_punctured(n, T, 𝒜) ∧ &0 < t ⇒ " +
			"        σ(cotangent_scale(t, p), i, j) = complex_of_real(real_zpow(t, m)) * σ(p, i, j)) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ∀i j:num. " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ∧ i < q ∧ j < r ⇒ " +
			"        vec_smooth_on⟨2 * n⟩({z:(num → real) | " +
			"                vec⟨2 * n⟩(&0, z) ∧ " +
			"                ps_base(n, z) ∈ image(snd(c), fst(c)) ∧ " +
			"                ps_frequency(n, z) ≠ (λi:num. &0)}, " +
			"            λz:(num → real). " +
			"                re(σ((inverse_on(fst(c), snd(c), ps_base(n, z)), " +
			"                            cotangent_from_chart(n, " +
			"                                T, " +
			"                                𝒜, " +
			"                                c, " +
			"                                inverse_on(fst(c), snd(c), ps_base(n, z)), " +
			"                                ps_frequency(n, z))), " +
			"                        i, " +
			"                        j))) ∧ " +
			"        vec_smooth_on⟨2 * n⟩({z:(num → real) | " +
			"                vec⟨2 * n⟩(&0, z) ∧ " +
			"                ps_base(n, z) ∈ image(snd(c), fst(c)) ∧ " +
			"                ps_frequency(n, z) ≠ (λi:num. &0)}, " +
			"            λz:(num → real). " +
			"                im(σ((inverse_on(fst(c), snd(c), ps_base(n, z)), " +
			"                            cotangent_from_chart(n, " +
			"                                T, " +
			"                                𝒜, " +
			"                                c, " +
			"                                inverse_on(fst(c), snd(c), ps_base(n, z)), " +
			"                                ps_frequency(n, z))), " +
			"                        i, " +
			"                        j))))",
	},
})}

var EllipticDef = ellipticDefThm{family.Define(registry.DefEntry{
	Name:  "EllipticDef",
	Key:   "prop_8b606af796a96b5d",
	Deps:  []registry.EntryLike{PuncturedDef, PrincipalSymbolDef},
	Const: "ps_elliptic_symbol",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"int → " +
		"(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀m:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"    ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ) ⇔ " +
			"    ps_principal_symbol(n, r, q, T, 𝒜, P, Q, m, σ) ∧ " +
			"    (∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"        p ∈ cotangent_punctured(n, T, 𝒜) ⇒ " +
			"        projection_invertible_at(projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                (r, P)), " +
			"            projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                (q, Q)), " +
			"            σ, " +
			"            p))",
	},
})}

var SmoothingDef = smoothingDefThm{family.Define(registry.DefEntry{
	Name:  "SmoothingDef",
	Key:   "prop_dd82e9fbe31947fc",
	Deps:  []registry.EntryLike{smoothModuleDef},
	Const: "ps_smoothing",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"sobolev_localization(A) → " +
		"((A → num → complex) → A → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀R:((A → num → complex) → A → num → complex). " +
			"    ps_smoothing(n, r, q, T, 𝒜, P, Q, L, R) ⇔ " +
			"    module_homomorphism(complex_ring, " +
			"        ps_smooth_module(n, r, T, 𝒜, P), " +
			"        ps_smooth_module(n, q, T, 𝒜, Q), " +
			"        R) ∧ " +
			"    (∀s t:int. ∃C:real. " +
			"        &0 ≤ C ∧ " +
			"        ∀f:(A → num → complex). " +
			"            smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
			"            localization_sequence_norm(n, q, L.count, t)(localize_section(n, q, L, R(f))) ≤ " +
			"            C * localization_sequence_norm(n, r, L.count, s)(localize_section(n, r, L, f)))",
	},
})}

var cutoffsDef = cutoffsDefThm{family.Define(registry.DefEntry{
	Name:  "cutoffsDef",
	Key:   "prop_ca71def2c8246715",
	Const: "ps_chart_cutoffs",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"sobolev_localization(A) → " +
		"(num → A → real) → " +
		"bool",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀L:sobolev_localization(A). " +
			"∀ψ:(num → A → real). " +
			"    ps_chart_cutoffs(n, T, 𝒜, L, ψ) ⇔ " +
			"    sobolev_localization_on(n, T, 𝒜, L) ∧ " +
			"    (∀i:num. " +
			"        i < L.count ⇒ " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, ψ(i)) ∧ " +
			"        compact_in(T, function_support(T, &0, ψ(i))) ∧ " +
			"        function_support(T, &0, ψ(i)) ⊆ fst(L.charts(i)) ∧ " +
			"        (∀x:A. x ∈ function_support(T, &0, L.partition(i)) ⇒ ψ(i, x) = &1))",
	},
})}

var localSectionDef = localSectionDefThm{family.Define(registry.DefEntry{
	Name:  "localSectionDef",
	Key:   "prop_a940b102102c37d",
	Const: "ps_local_section",
	Type: "num → " +
		"prod(set(A), A → num → real) → " +
		"(A → real) → " +
		"(A → num → complex) → " +
		"num → " +
		"(num → real) → " +
		"complex",
	Equations: []string{
		"∀n:num. ∀c:prod(set(A), A → num → real). ∀ψ:(A → real). ∀f:(A → num → complex). ∀j:num. " +
			"    ps_local_section(n, c, ψ, f, j) = " +
			"    torus_periodize(n, " +
			"        λy:(num → real). " +
			"            COND(y ∈ image(snd(c), fst(c)), " +
			"                complex_of_real(ψ(inverse_on(fst(c), snd(c), y))) * " +
			"                f(inverse_on(fst(c), snd(c), y), j), " +
			"                complex_of_real(&0)))",
	},
})}

var localPrincipalDef = localPrincipalDefThm{family.Define(registry.DefEntry{
	Name:  "localPrincipalDef",
	Key:   "prop_477a984e40839fff",
	Const: "ps_local_principal",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(set(A), A → num → real) → " +
		"(A → real) → " +
		"(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex) → " +
		"num → " +
		"num → " +
		"(num → real) → " +
		"complex",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀ψ:(A → real). " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀i j:num. " +
			"∀z:(num → real). " +
			"    ps_local_principal(n, T, 𝒜, c, ψ, σ, i, j, z) = " +
			"    COND(vec⟨2 * n⟩(&0, z), " +
			"        torus_periodize(n, " +
			"            λy:(num → real). " +
			"                COND(y ∈ image(snd(c), fst(c)), " +
			"                    complex_of_real(ψ(inverse_on(fst(c), snd(c), y))) * " +
			"                    σ((inverse_on(fst(c), snd(c), y), " +
			"                            cotangent_from_chart(n, " +
			"                                T, " +
			"                                𝒜, " +
			"                                c, " +
			"                                inverse_on(fst(c), snd(c), y), " +
			"                                ps_frequency(n, z))), " +
			"                        i, " +
			"                        j), " +
			"                    complex_of_real(&0)), " +
			"            ps_base(n, z)), " +
			"        complex_of_real(&0))",
	},
})}

var quantizationDef = quantizationDefThm{family.Define(registry.DefEntry{
	Name:  "quantizationDef",
	Key:   "prop_cdd77ccaf47be004",
	Deps:  []registry.EntryLike{localSectionDef},
	Const: "ps_quantization_seed",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"sobolev_localization(A) → " +
		"(num → A → real) → " +
		"(num → (num → real) → num → num → complex) → " +
		"(A → num → complex) → " +
		"A → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀ψ:(num → A → real). " +
			"∀a:(num → (num → real) → num → num → complex). " +
			"∀f:(A → num → complex). " +
			"∀x:A. " +
			"∀i:num. " +
			"    ps_quantization_seed(n, r, q, T, 𝒜, P, Q, L, ψ, a, f, x, i) = " +
			"    COND(x ∈ ⋃T ∧ i < q, " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {l:num | l < L.count}, " +
			"            λl:num. " +
			"                COND(x ∈ fst(L.charts(l)), " +
			"                    complex_of_real(L.partition(l, x)) * " +
			"                    module_sum(complex_add, " +
			"                        complex_of_real(&0), " +
			"                        {j:num | j < q}, " +
			"                        λj:num. " +
			"                            Q(x, i, j) * " +
			"                            module_sum(complex_add, " +
			"                                complex_of_real(&0), " +
			"                                {k:num | k < r}, " +
			"                                λk:num. " +
			"                                    torus_quantize(n, " +
			"                                        λz:(num → real). a(l, z, j, k), " +
			"                                        torus_coefficients(n, " +
			"                                            ps_local_section(n, L.charts(l), ψ(l), f, k)), " +
			"                                        snd(L.charts(l))(x)))), " +
			"                    complex_of_real(&0))), " +
			"        complex_of_real(&0))",
	},
})}

var OperatorDef = operatorDefThm{family.Define(registry.DefEntry{
	Name: "OperatorDef",
	Key:  "prop_418f4441960f80c9",
	Deps: []registry.EntryLike{
		PrincipalSymbolDef,
		SmoothingDef,
		cutoffsDef,
		localPrincipalDef,
		quantizationDef,
	},
	Const: "pseudo_differential_operator",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"int → " +
		"(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex) → " +
		"((A → num → complex) → A → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀m:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex). " +
			"    pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D) ⇔ " +
			"    compact_in(T, ⋃T) ∧ " +
			"    ps_principal_symbol(n, r, q, T, 𝒜, P, Q, m, σ) ∧ " +
			"    ∃L:sobolev_localization(A). " +
			"    ∃ψ:(num → A → real). " +
			"    ∃a:(num → (num → real) → num → num → complex). " +
			"    ∃R:((A → num → complex) → A → num → complex). " +
			"        ps_chart_cutoffs(n, T, 𝒜, L, ψ) ∧ " +
			"        (∀l i j:num. " +
			"            l < L.count ∧ i < q ∧ j < r ⇒ " +
			"            torus_principal_pair(n, " +
			"                m, " +
			"                λz:(num → real). a(l, z, i, j), " +
			"                ps_local_principal(n, T, 𝒜, L.charts(l), ψ(l), σ, i, j))) ∧ " +
			"        ps_smoothing(n, r, q, T, 𝒜, P, Q, L, R) ∧ " +
			"        (∀f:(A → num → complex). " +
			"            smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
			"            D(f) = " +
			"            (λx:A. λi:num. " +
			"                ps_quantization_seed(n, r, q, T, 𝒜, P, Q, L, ψ, a, f, x, i) + R(f, x, i)))",
	},
})}

var RealizationDef = realizationDefThm{family.Define(registry.DefEntry{
	Name:  "RealizationDef",
	Key:   "prop_c64dd813ee82c62d",
	Const: "ps_realization",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"sobolev_localization(A) → " +
		"int → " +
		"int → " +
		"((A → num → complex) → A → num → complex) → " +
		"(prod(num, prod(num, num → int)) → complex) → " +
		"prod(num, prod(num, num → int)) → " +
		"complex",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀m s:int. " +
			"∀D:((A → num → complex) → A → num → complex). " +
			"    ps_realization(n, r, q, T, 𝒜, P, Q, L, m, s, D) = " +
			"    εF:((prod(num, prod(num, num → int)) → complex) → " +
			"            prod(num, prod(num, num → int)) → " +
			"            complex). " +
			"        F ∈ " +
			"        (operator_module(section_sobolev_module(n, r, T, 𝒜, P, L, s), " +
			"                localization_sequence_norm(n, r, L.count, s), " +
			"                section_sobolev_module(n, q, T, 𝒜, Q, L, s - m), " +
			"                localization_sequence_norm(n, q, L.count, s - m))).carrier ∧ " +
			"        (∀f:(A → num → complex). " +
			"            smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
			"            F(localize_section(n, r, L, f)) = localize_section(n, q, L, D(f)))",
	},
})}

var AdjointDef = adjointDefThm{family.Define(registry.DefEntry{
	Name:  "AdjointDef",
	Key:   "prop_d84c3641d6b867b1",
	Deps:  []registry.EntryLike{smoothModuleDef},
	Const: "ps_formal_adjoint",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"sobolev_localization(A) → " +
		"((A → num → complex) → A → num → complex) → " +
		"(A → num → complex) → " +
		"A → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀D:((A → num → complex) → A → num → complex). " +
			"    ps_formal_adjoint(n, r, q, T, 𝒜, P, Q, L, D) = " +
			"    εE:((A → num → complex) → A → num → complex). " +
			"        module_homomorphism(complex_ring, " +
			"            ps_smooth_module(n, q, T, 𝒜, Q), " +
			"            ps_smooth_module(n, r, T, 𝒜, P), " +
			"            E) ∧ " +
			"        (∀f g:(A → num → complex). " +
			"            smooth_projected_section(n, r, T, 𝒜, P, f) ∧ " +
			"            smooth_projected_section(n, q, T, 𝒜, Q, g) ⇒ " +
			"            localization_sequence_inner(n, " +
			"                q, " +
			"                L.count, " +
			"                int_of_num(0), " +
			"                localize_section(n, q, L, D(f)), " +
			"                localize_section(n, q, L, g)) = " +
			"            localization_sequence_inner(n, " +
			"                r, " +
			"                L.count, " +
			"                int_of_num(0), " +
			"                localize_section(n, r, L, f), " +
			"                localize_section(n, r, L, E(g))))",
	},
})}
