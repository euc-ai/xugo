package torus_fourier

import "github.com/euc-ai/xugo/library/registry"

var FrequencyLatticeDef = frequencyLatticeDefThm{family.Define(registry.DefEntry{
	Name:  "FrequencyLatticeDef",
	Key:   "prop_c3aeb1d6baf68ac4",
	Const: "fourier_lattice",
	Type:  "num → set(num → int)",
	Equations: []string{
		"∀n:num. fourier_lattice(n) = {k:(num → int) | ∀j:num. n ≤ j ⇒ k(j) = int_of_num(0)}",
	},
})}

var FrequencyLengthDef = frequencyLengthDefThm{family.Define(registry.DefEntry{
	Name:  "FrequencyLengthDef",
	Key:   "prop_22d4081e18ece404",
	Const: "frequency_length_squared",
	Type:  "num → (num → int) → real",
	Equations: []string{
		"∀n:num. ∀k:(num → int). " +
			"    frequency_length_squared(n, k) = " +
			"    real_sum({j:num | j < n}, λj:num. real_pow(real_of_int(k(j)), 2))",
	},
})}

var FrequencyBlockDef = frequencyBlockDefThm{family.Define(registry.DefEntry{
	Name:  "FrequencyBlockDef",
	Key:   "prop_4aaf2ad8c6504ff",
	Const: "fourier_block",
	Type:  "num → real → set(num → int)",
	Deps:  []registry.EntryLike{FrequencyLatticeDef, FrequencyLengthDef},
	Equations: []string{
		"∀n:num. ∀R:real. " +
			"    fourier_block(n, R) = " +
			"    {k:(num → int) | k ∈ fourier_lattice(n) ∧ frequency_length_squared(n, k) ≤ real_pow(R, 2)}",
	},
})}

var PeriodShiftDef = periodShiftDefThm{family.Define(registry.DefEntry{
	Name:  "PeriodShiftDef",
	Key:   "prop_939f7a80ecb28830",
	Const: "torus_period_shift",
	Type:  "num → (num → int) → (num → real) → num → real",
	Equations: []string{
		"∀n:num. ∀k:(num → int). ∀x:(num → real). ∀j:num. " +
			"    torus_period_shift(n, k, x, j) = COND(j < n, x(j) + &2 * pi * real_of_int(k(j)), &0)",
	},
})}

var periodicFunctionDef = periodicFunctionDefThm{family.Define(registry.DefEntry{
	Name:  "periodicFunctionDef",
	Key:   "prop_896065899350b059",
	Const: "torus_periodic",
	Type:  "num → ((num → real) → complex) → bool",
	Deps:  []registry.EntryLike{FrequencyLatticeDef, PeriodShiftDef},
	Equations: []string{
		"∀n:num. ∀f:((num → real) → complex). " +
			"    torus_periodic(n, f) ⇔ " +
			"    (∀x:(num → real). ¬vec⟨n⟩(&0, x) ⇒ f(x) = complex_of_real(&0)) ∧ " +
			"    (∀x:(num → real). ∀k:(num → int). " +
			"        vec⟨n⟩(&0, x) ∧ k ∈ fourier_lattice(n) ⇒ f(torus_period_shift(n, k, x)) = f(x))",
	},
})}

var TorusClassDef = torusClassDefThm{family.Define(registry.DefEntry{
	Name:  "TorusClassDef",
	Key:   "prop_851545f891c16870",
	Const: "torus_class",
	Type:  "num → num → ((num → real) → complex) → bool",
	Deps:  []registry.EntryLike{periodicFunctionDef},
	Equations: []string{
		"∀n r:num. ∀f:((num → real) → complex). " +
			"    torus_class(n, r, f) ⇔ " +
			"    torus_periodic(n, f) ∧ " +
			"    vec_continuously_differentiable_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, " +
			"        r, " +
			"        λx:(num → real). re(f(x))) ∧ " +
			"    vec_continuously_differentiable_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, " +
			"        r, " +
			"        λx:(num → real). im(f(x)))",
	},
})}

var SmoothPeriodicDef = smoothPeriodicDefThm{family.Define(registry.DefEntry{
	Name:  "SmoothPeriodicDef",
	Key:   "prop_2cade1fe53a77104",
	Const: "torus_smooth",
	Type:  "num → ((num → real) → complex) → bool",
	Deps:  []registry.EntryLike{TorusClassDef},
	Equations: []string{
		"∀n:num. ∀f:((num → real) → complex). torus_smooth(n, f) ⇔ ∀r:num. torus_class(n, r, f)",
	},
})}

var TorusIntegralDef = torusIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "TorusIntegralDef",
	Key:   "prop_7176678d3cd23b96",
	Const: "torus_integral",
	Type:  "num → ((num → real) → complex) → complex",
	Equations: []string{
		"∀f:((num → real) → complex). torus_integral(0, f) = f(λj:num. &0)",
		"∀n:num. ∀f:((num → real) → complex). " +
			"    torus_integral(suc(n), f) = " +
			"    complex_integral(λt:real. " +
			"            torus_integral(n, " +
			"                λx:(num → real). f(λj:num. COND(j < n, x(j), COND(j = n, t, &0)))), " +
			"        &0, " +
			"        &2 * pi) / " +
			"    complex_of_real(&2 * pi)",
	},
})}

var CharacterDef = characterDefThm{family.Define(registry.DefEntry{
	Name:  "CharacterDef",
	Key:   "prop_1d5c374c416c36dc",
	Const: "torus_character",
	Type:  "num → (num → int) → (num → real) → complex",
	Equations: []string{
		"∀n:num. ∀k:(num → int). ∀x:(num → real). " +
			"    torus_character(n, k, x) = " +
			"    COND(vec⟨n⟩(&0, x), " +
			"        complex_exp(complex_i * " +
			"            complex_of_real(real_sum({j:num | j < n}, λj:num. real_of_int(k(j)) * x(j)))), " +
			"        complex_of_real(&0))",
	},
})}

var CoefficientsDef = coefficientsDefThm{family.Define(registry.DefEntry{
	Name:  "CoefficientsDef",
	Key:   "prop_223fc872b0f6af10",
	Const: "torus_coefficients",
	Type:  "num → ((num → real) → complex) → (num → int) → complex",
	Deps:  []registry.EntryLike{FrequencyLatticeDef, TorusIntegralDef, CharacterDef},
	Equations: []string{
		"∀n:num. ∀f:((num → real) → complex). ∀k:(num → int). " +
			"    torus_coefficients(n, f, k) = " +
			"    COND(k ∈ fourier_lattice(n), " +
			"        torus_integral(n, λx:(num → real). f(x) * complex_conj(torus_character(n, k, x))), " +
			"        complex_of_real(&0))",
	},
})}

var RapidSequenceDef = rapidSequenceDefThm{family.Define(registry.DefEntry{
	Name:  "RapidSequenceDef",
	Key:   "prop_55affb5228b93890",
	Const: "rapid_sequence",
	Type:  "num → ((num → int) → complex) → bool",
	Deps:  []registry.EntryLike{FrequencyLatticeDef, FrequencyLengthDef},
	Equations: []string{
		"∀n:num. ∀u:((num → int) → complex). " +
			"    rapid_sequence(n, u) ⇔ " +
			"    (∀k:(num → int). k ∉ fourier_lattice(n) ⇒ u(k) = complex_of_real(&0)) ∧ " +
			"    ∀m:num. ∃C:real. " +
			"        &0 ≤ C ∧ " +
			"        ∀k:(num → int). " +
			"            k ∈ fourier_lattice(n) ⇒ " +
			"            real_pow(&1 + frequency_length_squared(n, k), m) * |u(k)| ≤ C",
	},
})}

var SynthesisDef = synthesisDefThm{family.Define(registry.DefEntry{
	Name:  "SynthesisDef",
	Key:   "prop_569f4b800dd6b720",
	Const: "torus_synthesis",
	Type:  "num → ((num → int) → complex) → (num → real) → complex",
	Deps:  []registry.EntryLike{FrequencyLatticeDef, CharacterDef},
	Equations: []string{
		"∀n:num. ∀u:((num → int) → complex). ∀x:(num → real). " +
			"    torus_synthesis(n, u, x) = " +
			"    COND(vec⟨n⟩(&0, x), " +
			"        unordered_complex_sum(fourier_lattice(n), " +
			"            λk:(num → int). u(k) * torus_character(n, k, x)), " +
			"        complex_of_real(&0))",
	},
})}

var TrigonometricPolynomialDef = trigonometricPolynomialDefThm{family.Define(registry.DefEntry{
	Name:  "TrigonometricPolynomialDef",
	Key:   "prop_f5c301331c82b5da",
	Const: "torus_polynomial",
	Type:  "num → ((num → real) → complex) → bool",
	Deps:  []registry.EntryLike{FrequencyLatticeDef, SynthesisDef},
	Equations: []string{
		"∀n:num. ∀f:((num → real) → complex). " +
			"    torus_polynomial(n, f) ⇔ " +
			"    ∃F:set(num → int). ∃u:((num → int) → complex). " +
			"        finite(F) ∧ F ⊆ fourier_lattice(n) ∧ f = torus_synthesis(n, sequence_truncate(F, u))",
	},
})}

var TorusPartialDef = torusPartialDefThm{family.Define(registry.DefEntry{
	Name:  "TorusPartialDef",
	Key:   "prop_852b8af98a40ab43",
	Const: "torus_partial",
	Type:  "num → num → ((num → real) → complex) → (num → real) → complex",
	Equations: []string{
		"∀n j:num. ∀f:((num → real) → complex). ∀x:(num → real). " +
			"    torus_partial(n, j, f, x) = " +
			"    COND(vec⟨n⟩(&0, x), " +
			"        complex(partial_derivative(λy:(num → real). re(f(y)), j, x), " +
			"            partial_derivative(λy:(num → real). im(f(y)), j, x)), " +
			"        complex_of_real(&0))",
	},
})}
