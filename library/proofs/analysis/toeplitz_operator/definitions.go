package toeplitz_operator

import "github.com/euc-ai/xugo/library/registry"

var CircleSymbolDef = circleSymbolDefThm{family.Define(registry.DefEntry{
	Name:  "CircleSymbolDef",
	Key:   "prop_f1dc3e28c3c4b329",
	Const: "circle_symbol",
	Type:  "(real → complex) → bool",
	Equations: []string{
		"∀f:(real → complex). " +
			"    circle_symbol(f) ⇔ " +
			"    real_continuous_on(𝕌, λt:real. re(f(t))) ∧ " +
			"    real_continuous_on(𝕌, λt:real. im(f(t))) ∧ " +
			"    ∀t:real. f(t + &2 * pi) = f(t)",
	},
})}

var circleCoefficientDef = circleCoefficientDefThm{family.Define(registry.DefEntry{
	Name:  "circleCoefficientDef",
	Key:   "prop_f893b529ceac2b73",
	Const: "circle_coefficient",
	Type:  "(real → complex) → int → complex",
	Equations: []string{
		"∀f:(real → complex). ∀k:int. " +
			"    circle_coefficient(f, k) = " +
			"    complex_integral( " +
			"        λt:real. f(t) * complex_exp(-(complex_i * complex_of_real(real_of_int(k) * t))), " +
			"        &0, " +
			"        &2 * pi) / " +
			"    complex_of_real(&2 * pi)",
	},
})}

var symbolNormDef = symbolNormDefThm{family.Define(registry.DefEntry{
	Name:  "symbolNormDef",
	Key:   "prop_a757ba343c59e413",
	Const: "circle_symbol_norm",
	Type:  "(real → complex) → real",
	Equations: []string{
		"∀f:(real → complex). " +
			"    circle_symbol_norm(f) = real_sup({r:real | ∃t:real. &0 ≤ t ∧ t ≤ &2 * pi ∧ r = |f(t)|})",
	},
})}

var HardyModuleDef = hardyModuleDefThm{family.Define(registry.DefEntry{
	Name:      "HardyModuleDef",
	Key:       "prop_cb2aa254a593ed55",
	Const:     "hardy_sequence_module",
	Type:      "module_ops(complex, num → complex)",
	Equations: []string{"hardy_sequence_module = weighted_sequence_module(𝕌, λj:num. &1)"},
})}

var HardyInnerDef = hardyInnerDefThm{family.Define(registry.DefEntry{
	Name:      "HardyInnerDef",
	Key:       "prop_299e0a1a77be28af",
	Const:     "hardy_sequence_inner",
	Type:      "(num → complex) → (num → complex) → complex",
	Equations: []string{"hardy_sequence_inner = weighted_sequence_inner(𝕌, λj:num. &1)"},
})}

var HardyNormDef = hardyNormDefThm{family.Define(registry.DefEntry{
	Name:      "HardyNormDef",
	Key:       "prop_bd7c2ec81cf2fbc",
	Const:     "hardy_sequence_norm",
	Type:      "(num → complex) → real",
	Deps:      []registry.EntryLike{HardyInnerDef},
	Equations: []string{"hardy_sequence_norm = hilbert_norm(hardy_sequence_inner)"},
})}

var ToeplitzDef = toeplitzDefThm{family.Define(registry.DefEntry{
	Name:  "ToeplitzDef",
	Key:   "prop_da61a3e9a87014d8",
	Const: "toeplitz_operator",
	Type:  "(real → complex) → (num → complex) → num → complex",
	Deps:  []registry.EntryLike{HardyModuleDef, HardyNormDef, circleCoefficientDef},
	Equations: []string{
		"∀f:(real → complex). " +
			"    toeplitz_operator(f) = " +
			"    εT:((num → complex) → num → complex). " +
			"        T ∈ " +
			"        (operator_module(hardy_sequence_module, " +
			"                hardy_sequence_norm, " +
			"                hardy_sequence_module, " +
			"                hardy_sequence_norm)).carrier ∧ " +
			"        ∀u:(num → complex). " +
			"            finite({j:num | u(j) ≠ complex_of_real(&0)}) ⇒ " +
			"            ∀m:num. " +
			"                T(u, m) = " +
			"                module_sum(complex_add, " +
			"                    complex_of_real(&0), " +
			"                    {j:num | u(j) ≠ complex_of_real(&0)}, " +
			"                    λj:num. circle_coefficient(f, int_of_num(m) - int_of_num(j)) * u(j))",
	},
})}

var circlePolynomialDef = circlePolynomialDefThm{family.Define(registry.DefEntry{
	Name:  "circlePolynomialDef",
	Key:   "prop_b83e7a548829eb24",
	Const: "circle_polynomial",
	Type:  "(real → complex) → bool",
	Equations: []string{
		"∀f:(real → complex). " +
			"    circle_polynomial(f) ⇔ " +
			"    ∃F:set(int). ∃a:(int → complex). " +
			"        finite(F) ∧ " +
			"        ∀t:real. " +
			"            f(t) = " +
			"            module_sum(complex_add, " +
			"                complex_of_real(&0), " +
			"                F, " +
			"                λk:int. a(k) * complex_exp(complex_i * complex_of_real(real_of_int(k) * t)))",
	},
})}

var CircleWindingDef = circleWindingDefThm{family.Define(registry.DefEntry{
	Name:  "CircleWindingDef",
	Key:   "prop_646a118fcb6b74a9",
	Const: "circle_winding_number",
	Type:  "(real → complex) → (real → complex) → int",
	Reading: "The integer choice is used only for a nonvanishing periodic " +
		"symbol whose supplied d is its piecewise smooth velocity on the whole period.",
	Equations: []string{
		"∀f d:(real → complex). " +
			"    circle_winding_number(f, d) = " +
			"    εk:int. " +
			"        complex_of_real(real_of_int(k)) = winding_index(f, d, &0, &2 * pi, complex_of_real(&0))",
	},
})}

var UnilateralShiftDef = unilateralShiftDefThm{family.Define(registry.DefEntry{
	Name:  "UnilateralShiftDef",
	Key:   "prop_ddd43a5d16dca9de",
	Const: "unilateral_shift",
	Type:  "(num → complex) → num → complex",
	Equations: []string{
		"∀u:(num → complex). ∀m:num. unilateral_shift(u, m) = COND(m = 0, complex_of_real(&0), u(m - 1))",
	},
})}

var symbolHomotopyDef = symbolHomotopyDefThm{family.Define(registry.DefEntry{
	Name:  "symbolHomotopyDef",
	Key:   "prop_e66d26a3f1f77173",
	Const: "circle_symbol_homotopy",
	Type:  "(real → real → complex) → bool",
	Deps:  []registry.EntryLike{CircleSymbolDef, symbolNormDef},
	Equations: []string{
		"∀F:(real → real → complex). " +
			"    circle_symbol_homotopy(F) ⇔ " +
			"    (∀t:real. " +
			"        &0 ≤ t ∧ t ≤ &1 ⇒ circle_symbol(F(t)) ∧ (∀θ:real. F(t, θ) ≠ complex_of_real(&0))) ∧ " +
			"    ∀t:real. " +
			"        &0 ≤ t ∧ t ≤ &1 ⇒ " +
			"        ∀ε:real. " +
			"            &0 < ε ⇒ " +
			"            ∃δ:real. " +
			"                &0 < δ ∧ " +
			"                ∀u:real. " +
			"                    &0 ≤ u ∧ u ≤ &1 ∧ |u - t| < δ ⇒ " +
			"                    circle_symbol_norm(λθ:real. F(u, θ) - F(t, θ)) < ε",
	},
})}
