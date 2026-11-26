package torus_pseudo_differential

import (
	"github.com/euc-ai/xugo/library/registry"
)

var BaseDef = baseDefThm{family.Define(registry.DefEntry{
	Name:      "BaseDef",
	Key:       "prop_bfeb08b4b225fc7f",
	Const:     "ps_base",
	Type:      "num → (num → real) → num → real",
	Equations: []string{"∀n:num. ∀z:(num → real). ∀i:num. ps_base(n, z, i) = COND(i < n, z(i), &0)"},
})}

var FrequencyDef = frequencyDefThm{family.Define(registry.DefEntry{
	Name:  "FrequencyDef",
	Key:   "prop_d638cbbb798300bd",
	Const: "ps_frequency",
	Type:  "num → (num → real) → num → real",
	Equations: []string{
		"∀n:num. ∀z:(num → real). ∀i:num. ps_frequency(n, z, i) = COND(i < n, z(n + i), &0)",
	},
})}

var joinDef = joinDefThm{family.Define(registry.DefEntry{
	Name:  "joinDef",
	Key:   "prop_698573782799c616",
	Const: "ps_join",
	Type:  "num → (num → real) → (num → real) → num → real",
	Equations: []string{
		"∀n:num. ∀x ξ:(num → real). ∀i:num. " +
			"    ps_join(n, x, ξ, i) = COND(i < n, x(i), COND(i < 2 * n, ξ(i - n), &0))",
	},
})}

var DerivativeDef = derivativeDefThm{family.Define(registry.DefEntry{
	Name:  "DerivativeDef",
	Key:   "prop_bdd3083b8b3ba4c3",
	Const: "ps_derivative_word",
	Type:  "num → (num → num) → ((num → real) → real) → (num → real) → real",
	Equations: []string{
		"∀j:(num → num). ∀f:((num → real) → real). ps_derivative_word(0, j, f) = f",
		"∀r:num. ∀j:(num → num). ∀f:((num → real) → real). " +
			"    ps_derivative_word(suc(r), j, f) = partial_derivative(ps_derivative_word(r, j, f), j(r))",
	},
})}

var derivativeBoundDef = derivativeBoundDefThm{family.Define(registry.DefEntry{
	Name:  "derivativeBoundDef",
	Key:   "prop_1d27d5d300a7cc01",
	Deps:  []registry.EntryLike{DerivativeDef},
	Const: "ps_derivative_bound",
	Type:  "num → int → ((num → real) → complex) → num → real → bool",
	Equations: []string{
		"∀n:num. ∀m:int. ∀a:((num → real) → complex). ∀N:num. ∀C:real. " +
			"    ps_derivative_bound(n, m, a, N, C) ⇔ " +
			"    &0 ≤ C ∧ " +
			"    ∀r:num. ∀j:(num → num). ∀z:(num → real). " +
			"        r ≤ N ∧ (∀l:num. l < r ⇒ j(l) < 2 * n) ∧ vec⟨2 * n⟩(&0, z) ⇒ " +
			"        real_pow(ps_derivative_word(r, j, λw:(num → real). re(a(w)), z), 2) + " +
			"        real_pow(ps_derivative_word(r, j, λw:(num → real). im(a(w)), z), 2) ≤ " +
			"        C * " +
			"        real_zpow(&1 + real_sum({i:num | i < n}, λi:num. real_pow(z(n + i), 2)), " +
			"            m - int_of_num(card({l:num | l < r ∧ n ≤ j(l)})))",
	},
})}

var SymbolDef = symbolDefThm{family.Define(registry.DefEntry{
	Name:  "SymbolDef",
	Key:   "prop_4bccd1dd99488f96",
	Deps:  []registry.EntryLike{joinDef, derivativeBoundDef},
	Const: "torus_symbol",
	Type:  "num → int → ((num → real) → complex) → bool",
	Equations: []string{
		"∀n:num. ∀m:int. ∀a:((num → real) → complex). " +
			"    torus_symbol(n, m, a) ⇔ " +
			"    (∀z:(num → real). ¬vec⟨2 * n⟩(&0, z) ⇒ a(z) = complex_of_real(&0)) ∧ " +
			"    vec_smooth_on⟨2 * n⟩({z:(num → real) | vec⟨2 * n⟩(&0, z)}, λz:(num → real). re(a(z))) ∧ " +
			"    vec_smooth_on⟨2 * n⟩({z:(num → real) | vec⟨2 * n⟩(&0, z)}, λz:(num → real). im(a(z))) ∧ " +
			"    (∀x ξ:(num → real). ∀k:(num → int). " +
			"        vec⟨n⟩(&0, x) ∧ vec⟨n⟩(&0, ξ) ∧ k ∈ fourier_lattice(n) ⇒ " +
			"        a(ps_join(n, torus_period_shift(n, k, x), ξ)) = a(ps_join(n, x, ξ))) ∧ " +
			"    (∀N:num. ∃C:real. ps_derivative_bound(n, m, a, N, C))",
	},
})}

var homogeneousDef = homogeneousDefThm{family.Define(registry.DefEntry{
	Name:  "homogeneousDef",
	Key:   "prop_915e16951b770192",
	Deps:  []registry.EntryLike{FrequencyDef, joinDef},
	Const: "torus_homogeneous_symbol",
	Type:  "num → int → ((num → real) → complex) → bool",
	Equations: []string{
		"∀n:num. ∀m:int. ∀h:((num → real) → complex). " +
			"    torus_homogeneous_symbol(n, m, h) ⇔ " +
			"    (∀z:(num → real). " +
			"        ¬vec⟨2 * n⟩(&0, z) ∨ ps_frequency(n, z) = (λi:num. &0) ⇒ h(z) = complex_of_real(&0)) ∧ " +
			"    vec_smooth_on⟨2 * n⟩( " +
			"        {z:(num → real) | vec⟨2 * n⟩(&0, z) ∧ ps_frequency(n, z) ≠ (λi:num. &0)}, " +
			"        λz:(num → real). re(h(z))) ∧ " +
			"    vec_smooth_on⟨2 * n⟩( " +
			"        {z:(num → real) | vec⟨2 * n⟩(&0, z) ∧ ps_frequency(n, z) ≠ (λi:num. &0)}, " +
			"        λz:(num → real). im(h(z))) ∧ " +
			"    (∀x ξ:(num → real). ∀k:(num → int). " +
			"        vec⟨n⟩(&0, x) ∧ vec⟨n⟩(&0, ξ) ∧ k ∈ fourier_lattice(n) ⇒ " +
			"        h(ps_join(n, torus_period_shift(n, k, x), ξ)) = h(ps_join(n, x, ξ))) ∧ " +
			"    (∀x ξ:(num → real). ∀t:real. " +
			"        vec⟨n⟩(&0, x) ∧ vec⟨n⟩(&0, ξ) ∧ &0 < t ⇒ " +
			"        h(ps_join(n, x, λi:num. t * ξ(i))) = " +
			"        complex_of_real(real_zpow(t, m)) * h(ps_join(n, x, ξ)))",
	},
})}

var radialCutoffDef = radialCutoffDefThm{family.Define(registry.DefEntry{
	Name:  "radialCutoffDef",
	Key:   "prop_e41ae0756ca62ad9",
	Const: "ps_radial_cutoff",
	Type:  "num → ((num → real) → real) → bool",
	Equations: []string{
		"∀n:num. ∀χ:((num → real) → real). " +
			"    ps_radial_cutoff(n, χ) ⇔ " +
			"    vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, χ) ∧ " +
			"    (∀x:(num → real). " +
			"        vec⟨n⟩(&0, x) ⇒ " +
			"        (real_sum({i:num | i < n}, λi:num. real_pow(x(i), 2)) ≤ &1 ⇒ χ(x) = &0) ∧ " +
			"        (&4 ≤ real_sum({i:num | i < n}, λi:num. real_pow(x(i), 2)) ⇒ χ(x) = &1))",
	},
})}

var PrincipalPairDef = principalPairDefThm{family.Define(registry.DefEntry{
	Name:  "PrincipalPairDef",
	Key:   "prop_827a1cda7986a977",
	Deps:  []registry.EntryLike{FrequencyDef, SymbolDef, homogeneousDef, radialCutoffDef},
	Const: "torus_principal_pair",
	Type:  "num → int → ((num → real) → complex) → ((num → real) → complex) → bool",
	Equations: []string{
		"∀n:num. ∀m:int. ∀a h:((num → real) → complex). " +
			"    torus_principal_pair(n, m, a, h) ⇔ " +
			"    torus_symbol(n, m, a) ∧ " +
			"    torus_homogeneous_symbol(n, m, h) ∧ " +
			"    ∃χ:((num → real) → real). " +
			"        ps_radial_cutoff(n, χ) ∧ " +
			"        torus_symbol(n, " +
			"            m - int_of_num(1), " +
			"            λz:(num → real). a(z) - complex_of_real(χ(ps_frequency(n, z))) * h(z))",
	},
})}

var QuantizationDef = quantizationDefThm{family.Define(registry.DefEntry{
	Name:  "QuantizationDef",
	Key:   "prop_da21b62b372b4a49",
	Deps:  []registry.EntryLike{joinDef},
	Const: "torus_quantize",
	Type:  "num → ((num → real) → complex) → ((num → int) → complex) → (num → real) → complex",
	Equations: []string{
		"∀n:num. ∀a:((num → real) → complex). ∀u:((num → int) → complex). ∀x:(num → real). " +
			"    torus_quantize(n, a, u, x) = " +
			"    COND(vec⟨n⟩(&0, x), " +
			"        unordered_complex_sum(fourier_lattice(n), " +
			"            λk:(num → int). " +
			"                torus_character(n, k, x) * a(ps_join(n, x, λi:num. real_of_int(k(i)))) * u(k)), " +
			"        complex_of_real(&0))",
	},
})}

var realizationDef = realizationDefThm{family.Define(registry.DefEntry{
	Name:  "realizationDef",
	Key:   "prop_737083fcbaf2a36a",
	Deps:  []registry.EntryLike{QuantizationDef},
	Const: "torus_ps_realization",
	Type: "num → " +
		"int → " +
		"int → " +
		"((num → real) → complex) → " +
		"((num → int) → complex) → " +
		"(num → int) → " +
		"complex",
	Equations: []string{
		"∀n:num. ∀m s:int. ∀a:((num → real) → complex). " +
			"    torus_ps_realization(n, m, s, a) = " +
			"    εD:(((num → int) → complex) → (num → int) → complex). " +
			"        bounded_operator(sobolev_module(n, s), " +
			"            sobolev_norm(n, s), " +
			"            sobolev_module(n, s - m), " +
			"            sobolev_norm(n, s - m), " +
			"            D) ∧ " +
			"        (∀u:((num → int) → complex). " +
			"            u ∉ (sobolev_module(n, s)).carrier ⇒ " +
			"            D(u) = (λk:(num → int). complex_of_real(&0))) ∧ " +
			"        (∀f:((num → real) → complex). " +
			"            torus_smooth(n, f) ⇒ " +
			"            D(torus_coefficients(n, f)) = " +
			"            torus_coefficients(n, torus_quantize(n, a, torus_coefficients(n, f))))",
	},
})}
