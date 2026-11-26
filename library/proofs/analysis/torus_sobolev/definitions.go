package torus_sobolev

import "github.com/euc-ai/xugo/library/registry"

var SobolevWeightDef = sobolevWeightDefThm{family.Define(registry.DefEntry{
	Name:  "SobolevWeightDef",
	Key:   "prop_59fe20d4951282d5",
	Const: "sobolev_weight",
	Type:  "num → int → (num → int) → real",
	Equations: []string{
		"∀n:num. ∀s:int. ∀k:(num → int). " +
			"    sobolev_weight(n, s, k) = real_zpow(&1 + frequency_length_squared(n, k), s)",
	},
})}

var SobolevModuleDef = sobolevModuleDefThm{family.Define(registry.DefEntry{
	Name:  "SobolevModuleDef",
	Key:   "prop_8981e5bb1c1e92ff",
	Const: "sobolev_module",
	Type:  "num → int → module_ops(complex, (num → int) → complex)",
	Deps:  []registry.EntryLike{SobolevWeightDef},
	Equations: []string{
		"∀n:num. ∀s:int. " +
			"    sobolev_module(n, s) = weighted_sequence_module(fourier_lattice(n), sobolev_weight(n, s))",
	},
})}

var SobolevInnerDef = sobolevInnerDefThm{family.Define(registry.DefEntry{
	Name:  "SobolevInnerDef",
	Key:   "prop_b6184dace138b220",
	Const: "sobolev_inner",
	Type:  "num → int → ((num → int) → complex) → ((num → int) → complex) → complex",
	Deps:  []registry.EntryLike{SobolevWeightDef},
	Equations: []string{
		"∀n:num. ∀s:int. " +
			"    sobolev_inner(n, s) = weighted_sequence_inner(fourier_lattice(n), sobolev_weight(n, s))",
	},
})}

var SobolevNormDef = sobolevNormDefThm{family.Define(registry.DefEntry{
	Name:      "SobolevNormDef",
	Key:       "prop_d72af89d05a9ec15",
	Const:     "sobolev_norm",
	Type:      "num → int → ((num → int) → complex) → real",
	Deps:      []registry.EntryLike{SobolevInnerDef},
	Equations: []string{"∀n:num. ∀s:int. sobolev_norm(n, s) = hilbert_norm(sobolev_inner(n, s))"},
})}

var frequencyDerivativeDef = frequencyDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "frequencyDerivativeDef",
	Key:   "prop_8e557793fbedaf27",
	Const: "frequency_derivative",
	Type:  "num → num → ((num → int) → complex) → (num → int) → complex",
	Equations: []string{
		"∀n j:num. ∀u:((num → int) → complex). ∀k:(num → int). " +
			"    frequency_derivative(n, j, u, k) = " +
			"    COND(k ∈ fourier_lattice(n), " +
			"        complex_i * complex_of_real(real_of_int(k(j))) * u(k), " +
			"        complex_of_real(&0))",
	},
})}

var sobolevMultiplyDef = sobolevMultiplyDefThm{family.Define(registry.DefEntry{
	Name:  "sobolevMultiplyDef",
	Key:   "prop_2d69657a388dce1b",
	Const: "sobolev_multiply",
	Type:  "num → ((num → real) → complex) → ((num → int) → complex) → (num → int) → complex",
	Equations: []string{
		"∀n:num. ∀a:((num → real) → complex). ∀u:((num → int) → complex). ∀k:(num → int). " +
			"    sobolev_multiply(n, a, u, k) = " +
			"    COND(k ∈ fourier_lattice(n), " +
			"        unordered_complex_sum(fourier_lattice(n), " +
			"            λl:(num → int). torus_coefficients(n, a, l) * u(λj:num. k(j) - l(j))), " +
			"        complex_of_real(&0))",
	},
})}

var multiplierBoundDef = multiplierBoundDefThm{family.Define(registry.DefEntry{
	Name:  "multiplierBoundDef",
	Key:   "prop_ee5a2400273451eb",
	Const: "sobolev_multiplier_bound",
	Type:  "num → int → ((num → real) → complex) → real",
	Equations: []string{
		"∀n:num. ∀s:int. ∀a:((num → real) → complex). " +
			"    sobolev_multiplier_bound(n, s, a) = " +
			"    real_sup({r:real | " +
			"            ∃F:set(num → int). " +
			"                finite(F) ∧ " +
			"                F ⊆ fourier_lattice(n) ∧ " +
			"                r = " +
			"                real_sum(F, " +
			"                    λk:(num → int). " +
			"                        real_zpow(&2 * (&1 + frequency_length_squared(n, k)), int_abs(s)) * " +
			"                        |torus_coefficients(n, a, k)|)})",
	},
})}

var SmallBoxDef = smallBoxDefThm{family.Define(registry.DefEntry{
	Name:  "SmallBoxDef",
	Key:   "prop_35a7dc1a07081ae3",
	Const: "torus_small_box",
	Type:  "num → set(num → real)",
	Equations: []string{
		"∀n:num. " +
			"    torus_small_box(n) = " +
			"    {x:(num → real) | vec⟨n⟩(&0, x) ∧ ∀j:num. j < n ⇒ -pi / &2 < x(j) ∧ x(j) < pi / &2}",
	},
})}

var PeriodizeDef = periodizeDefThm{family.Define(registry.DefEntry{
	Name:  "PeriodizeDef",
	Key:   "prop_a78a7953bcd78bac",
	Const: "torus_periodize",
	Type:  "num → ((num → real) → complex) → (num → real) → complex",
	Equations: []string{
		"∀n:num. ∀g:((num → real) → complex). ∀x:(num → real). " +
			"    torus_periodize(n, g, x) = " +
			"    COND(vec⟨n⟩(&0, x), " +
			"        unordered_complex_sum(fourier_lattice(n), " +
			"            λk:(num → int). g(torus_period_shift(n, k, x))), " +
			"        complex_of_real(&0))",
	},
})}

var LocalPullbackSeedDef = localPullbackSeedDefThm{family.Define(registry.DefEntry{
	Name:  "LocalPullbackSeedDef",
	Key:   "prop_41758609b593903f",
	Const: "local_pullback_seed",
	Type: "num → " +
		"set(num → real) → " +
		"((num → real) → (num → real)) → " +
		"((num → real) → real) → " +
		"((num → real) → complex) → " +
		"(num → real) → " +
		"complex",
	Deps: []registry.EntryLike{PeriodizeDef},
	Equations: []string{
		"∀n:num. " +
			"∀U:set(num → real). " +
			"∀φ:((num → real) → num → real). " +
			"∀χ:((num → real) → real). " +
			"∀f:((num → real) → complex). " +
			"    local_pullback_seed(n, U, φ, χ, f) = " +
			"    torus_periodize(n, " +
			"        λx:(num → real). COND(x ∈ U, complex_of_real(χ(x)) * f(φ(x)), complex_of_real(&0)))",
	},
})}

var localPullbackDef = localPullbackDefThm{family.Define(registry.DefEntry{
	Name:  "localPullbackDef",
	Key:   "prop_a7c714f1de62bf5b",
	Const: "sobolev_local_pullback",
	Type: "num → " +
		"int → " +
		"set(num → real) → " +
		"((num → real) → (num → real)) → " +
		"((num → real) → real) → " +
		"((num → int) → complex) → " +
		"((num → int) → complex)",
	Deps: []registry.EntryLike{SobolevModuleDef, SobolevNormDef, LocalPullbackSeedDef},
	Equations: []string{
		"∀n:num. ∀s:int. ∀U:set(num → real). ∀φ:((num → real) → num → real). ∀χ:((num → real) → real). " +
			"    sobolev_local_pullback(n, s, U, φ, χ) = " +
			"    εT:(((num → int) → complex) → (num → int) → complex). " +
			"        T ∈ " +
			"        (operator_module(sobolev_module(n, s), " +
			"                sobolev_norm(n, s), " +
			"                sobolev_module(n, s), " +
			"                sobolev_norm(n, s))).carrier ∧ " +
			"        ∀f:((num → real) → complex). " +
			"            torus_smooth(n, f) ⇒ " +
			"            T(torus_coefficients(n, f)) = " +
			"            torus_coefficients(n, local_pullback_seed(n, U, φ, χ, f))",
	},
})}

var derivativeWordDef = derivativeWordDefThm{family.Define(registry.DefEntry{
	Name:  "derivativeWordDef",
	Key:   "prop_d3eb8ed717a1e139",
	Const: "frequency_derivative_word",
	Type:  "num → num → (num → num) → ((num → int) → complex) → (num → int) → complex",
	Deps:  []registry.EntryLike{frequencyDerivativeDef},
	Equations: []string{
		"∀n:num. ∀j:(num → num). ∀u:((num → int) → complex). frequency_derivative_word(n, 0, j, u) = u",
		"∀n r:num. ∀j:(num → num). ∀u:((num → int) → complex). " +
			"    frequency_derivative_word(n, suc(r), j, u) = " +
			"    frequency_derivative(n, j(r), frequency_derivative_word(n, r, j, u))",
	},
})}

var differentialOperatorDef = differentialOperatorDefThm{family.Define(registry.DefEntry{
	Name:  "differentialOperatorDef",
	Key:   "prop_a605354dca04c2cd",
	Const: "sobolev_differential_operator",
	Type: "num → " +
		"num → " +
		"(num → num) → " +
		"(num → num → num) → " +
		"(num → ((num → real) → complex)) → " +
		"((num → int) → complex) → " +
		"(num → int) → " +
		"complex",
	Deps: []registry.EntryLike{sobolevMultiplyDef, derivativeWordDef},
	Equations: []string{
		"∀n N:num. " +
			"∀r:(num → num). " +
			"∀j:(num → num → num). " +
			"∀a:(num → (num → real) → complex). " +
			"∀u:((num → int) → complex). " +
			"∀k:(num → int). " +
			"    sobolev_differential_operator(n, N, r, j, a, u, k) = " +
			"    module_sum(complex_add, " +
			"        complex_of_real(&0), " +
			"        {i:num | i < N}, " +
			"        λi:num. sobolev_multiply(n, a(i), frequency_derivative_word(n, r(i), j(i), u), k))",
	},
})}

var localSobolevCarrierDef = localSobolevCarrierDefThm{family.Define(registry.DefEntry{
	Name:  "localSobolevCarrierDef",
	Key:   "prop_17c707e3fa76c884",
	Const: "local_sobolev_carrier",
	Type:  "num → int → set(num → real) → set((num → int) → complex)",
	Deps:  []registry.EntryLike{SobolevModuleDef, SobolevNormDef, PeriodizeDef},
	Equations: []string{
		"∀n:num. ∀s:int. ∀U:set(num → real). " +
			"    local_sobolev_carrier(n, s, U) = " +
			"    closure(norm_topology(sobolev_module(n, s), sobolev_norm(n, s)), " +
			"        {u:((num → int) → complex) | " +
			"            ∃g:((num → real) → complex). " +
			"                vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, λx:(num → real). re(g(x))) ∧ " +
			"                vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, λx:(num → real). im(g(x))) ∧ " +
			"                compact_in(euclidean_topology(n), " +
			"                    function_support(euclidean_topology(n), complex_of_real(&0), g)) ∧ " +
			"                function_support(euclidean_topology(n), complex_of_real(&0), g) ⊆ U ∧ " +
			"                u = torus_coefficients(n, torus_periodize(n, g))})",
	},
})}
