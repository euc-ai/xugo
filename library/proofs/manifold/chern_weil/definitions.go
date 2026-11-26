package chern_weil

import (
	"github.com/euc-ai/xugo/library/registry"
)

var realPartDef = realPartDefThm{family.Define(registry.DefEntry{
	Name:  "realPartDef",
	Key:   "prop_cfb2d69aeb74428f",
	Const: "complex_form_real",
	Type: "(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Equations: []string{
		"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    complex_form_real(ω, c, y, V) = re(ω(c, y, V))",
	},
})}

var imaginaryPartDef = imaginaryPartDefThm{family.Define(registry.DefEntry{
	Name:  "imaginaryPartDef",
	Key:   "prop_48acf01dcae1ced9",
	Const: "complex_form_imag",
	Type: "(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Equations: []string{
		"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    complex_form_imag(ω, c, y, V) = im(ω(c, y, V))",
	},
})}

var complexFormDef = complexFormDefThm{family.Define(registry.DefEntry{
	Name:  "complexFormDef",
	Key:   "prop_e76c0f2fe63c07a1",
	Deps:  []registry.EntryLike{realPartDef, imaginaryPartDef},
	Const: "complex_form_on",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"bool",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"    complex_form_on(n, T, 𝒜, k, ω) ⇔ " +
			"    manifold_form_on⟨n⟩(T, 𝒜, k, complex_form_real(ω)) ∧ " +
			"    manifold_form_on⟨n⟩(T, 𝒜, k, complex_form_imag(ω))",
	},
})}

var ComplexWedgeDef = complexWedgeDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexWedgeDef",
	Key:   "prop_4a9ec49625806f9e",
	Deps:  []registry.EntryLike{realPartDef, imaginaryPartDef},
	Const: "complex_form_wedge",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"complex",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀p q:num. " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    complex_form_wedge(n, T, 𝒜, p, q, α, β, c, y, V) = " +
			"    complex_of_real(manifold_form_wedge⟨n⟩(T, " +
			"            𝒜, " +
			"            p, " +
			"            q, " +
			"            complex_form_real(α), " +
			"            complex_form_real(β))(c, y, V) - " +
			"        manifold_form_wedge⟨n⟩(T, 𝒜, p, q, complex_form_imag(α), complex_form_imag(β))(c, " +
			"            y, " +
			"            V)) + " +
			"    complex_i * " +
			"    complex_of_real(manifold_form_wedge⟨n⟩(T, " +
			"            𝒜, " +
			"            p, " +
			"            q, " +
			"            complex_form_real(α), " +
			"            complex_form_imag(β))(c, y, V) + " +
			"        manifold_form_wedge⟨n⟩(T, 𝒜, p, q, complex_form_imag(α), complex_form_real(β))(c, y, V))",
	},
})}

var ComplexDerivativeDef = complexDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexDerivativeDef",
	Key:   "prop_66d2720dc6b0c249",
	Deps:  []registry.EntryLike{realPartDef, imaginaryPartDef},
	Const: "complex_form_derivative",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"complex",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    complex_form_derivative(n, T, 𝒜, k, ω, c, y, V) = " +
			"    complex_of_real(manifold_exterior_derivative⟨n⟩(T, 𝒜, k, complex_form_real(ω))(c, y, V)) + " +
			"    complex_i * " +
			"    complex_of_real(manifold_exterior_derivative⟨n⟩(T, 𝒜, k, complex_form_imag(ω))(c, y, V))",
	},
})}

var MatrixFunctionDef = matrixFunctionDefThm{family.Define(registry.DefEntry{
	Name:  "MatrixFunctionDef",
	Key:   "prop_a95b8f2b78a69ea7",
	Const: "chern_matrix_function",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
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
			"∀U:(A → num → num → complex). " +
			"∀i j:num. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    chern_matrix_function(n, T, 𝒜, U, i, j, c, y, V) = " +
			"    complex_of_real(manifold_function_form⟨n⟩(T, 𝒜, λx:A. re(U(x, i, j)), c, y, V)) + " +
			"    complex_i * complex_of_real(manifold_function_form⟨n⟩(T, 𝒜, λx:A. im(U(x, i, j)), c, y, V))",
	},
})}

var matrixProductDef = matrixProductDefThm{family.Define(registry.DefEntry{
	Name:  "matrixProductDef",
	Key:   "prop_8507f97fd85d9571",
	Deps:  []registry.EntryLike{ComplexWedgeDef},
	Const: "chern_matrix_product",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"num → " +
		"num → " +
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
			"∀r p q:num. " +
			"∀U W:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀i j:num. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    chern_matrix_product(n, T, 𝒜, r, p, q, U, W, i, j, c, y, V) = " +
			"    COND(i < r ∧ j < r, " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {l:num | l < r}, " +
			"            λl:num. complex_form_wedge(n, T, 𝒜, p, q, U(i, l), W(l, j))(c, y, V)), " +
			"        complex_of_real(&0))",
	},
})}

var ConnectionDef = connectionDefThm{family.Define(registry.DefEntry{
	Name:  "ConnectionDef",
	Key:   "prop_24c40cf0e9537553",
	Deps:  []registry.EntryLike{complexFormDef, MatrixFunctionDef, matrixProductDef},
	Const: "projection_connection",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"bool",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"    projection_connection(n, T, 𝒜, P, Γ) ⇔ " +
			"    smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P)) ∧ " +
			"    (∀i j:num. complex_form_on(n, T, 𝒜, 1, Γ(i, j))) ∧ " +
			"    Γ = " +
			"    chern_matrix_product(n, " +
			"        T, " +
			"        𝒜, " +
			"        fst(P), " +
			"        0, " +
			"        1, " +
			"        chern_matrix_function(n, T, 𝒜, snd(P)), " +
			"        chern_matrix_product(n, T, 𝒜, fst(P), 1, 0, Γ, chern_matrix_function(n, T, 𝒜, snd(P))))",
	},
})}

var curvatureDef = curvatureDefThm{family.Define(registry.DefEntry{
	Name:  "curvatureDef",
	Key:   "prop_3701fd67b45da60e",
	Deps:  []registry.EntryLike{ComplexDerivativeDef, MatrixFunctionDef, matrixProductDef},
	Const: "projection_curvature",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
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
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀i j:num. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    projection_curvature(n, T, 𝒜, P, Γ, i, j, c, y, V) = " +
			"    chern_matrix_product(n, " +
			"        T, " +
			"        𝒜, " +
			"        fst(P), " +
			"        0, " +
			"        2, " +
			"        chern_matrix_function(n, T, 𝒜, snd(P)), " +
			"        chern_matrix_product(n, " +
			"            T, " +
			"            𝒜, " +
			"            fst(P), " +
			"            2, " +
			"            0, " +
			"            chern_matrix_product(n, " +
			"                T, " +
			"                𝒜, " +
			"                fst(P), " +
			"                1, " +
			"                1, " +
			"                (λi:num. λj:num. " +
			"                    complex_form_derivative(n, " +
			"                        T, " +
			"                        𝒜, " +
			"                        0, " +
			"                        chern_matrix_function(n, T, 𝒜, snd(P))(i, j))), " +
			"                (λi:num. λj:num. " +
			"                    complex_form_derivative(n, " +
			"                        T, " +
			"                        𝒜, " +
			"                        0, " +
			"                        chern_matrix_function(n, T, 𝒜, snd(P))(i, j)))), " +
			"            chern_matrix_function(n, T, 𝒜, snd(P))))(i, j, c, y, V) + " +
			"    chern_matrix_product(n, " +
			"        T, " +
			"        𝒜, " +
			"        fst(P), " +
			"        0, " +
			"        2, " +
			"        chern_matrix_function(n, T, 𝒜, snd(P)), " +
			"        chern_matrix_product(n, " +
			"            T, " +
			"            𝒜, " +
			"            fst(P), " +
			"            2, " +
			"            0, " +
			"            (λi:num. λj:num. complex_form_derivative(n, T, 𝒜, 1, Γ(i, j))), " +
			"            chern_matrix_function(n, T, 𝒜, snd(P))))(i, j, c, y, V) + " +
			"    chern_matrix_product(n, T, 𝒜, fst(P), 1, 1, Γ, Γ)(i, j, c, y, V)",
	},
})}

var curvaturePowerDef = curvaturePowerDefThm{family.Define(registry.DefEntry{
	Name:  "curvaturePowerDef",
	Key:   "prop_b615fd087a80645c",
	Deps:  []registry.EntryLike{MatrixFunctionDef, matrixProductDef, curvatureDef},
	Const: "chern_curvature_power",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"num → " +
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
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"    chern_curvature_power(n, T, 𝒜, P, Γ, 0) = chern_matrix_function(n, T, 𝒜, snd(P))",
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀k:num. " +
			"    chern_curvature_power(n, T, 𝒜, P, Γ, suc(k)) = " +
			"    chern_matrix_product(n, " +
			"        T, " +
			"        𝒜, " +
			"        fst(P), " +
			"        2 * k, " +
			"        2, " +
			"        chern_curvature_power(n, T, 𝒜, P, Γ, k), " +
			"        (λi:num. " +
			"        λj:num. " +
			"        λc:prod(set(A), A → num → real). " +
			"        λy:(num → real). " +
			"        λV:(num → num → real). " +
			"            (-projection_curvature(n, T, 𝒜, P, Γ, i, j, c, y, V)) / " +
			"            (complex_of_real(&2 * pi) * complex_i)))",
	},
})}

var ChernFormDef = chernFormDefThm{family.Define(registry.DefEntry{
	Name:  "ChernFormDef",
	Key:   "prop_41bdcc9d6f7a5085",
	Deps:  []registry.EntryLike{curvaturePowerDef},
	Const: "chern_form",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"num → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"∀k:num. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real). " +
			"    chern_form(n, T, 𝒜, P, Γ, k, c, y, V) = " +
			"    re(module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {i:num | i < fst(P)}, " +
			"            λi:num. chern_curvature_power(n, T, 𝒜, P, Γ, k, i, i, c, y, V))) / " +
			"    real_of_num(factorial(k))",
	},
})}

var ChernClassDef = chernClassDefThm{family.Define(registry.DefEntry{
	Name:  "ChernClassDef",
	Key:   "prop_b2586261ee7f7f6a",
	Deps:  []registry.EntryLike{ChernFormDef},
	Const: "chern_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"    chern_class(n, T, 𝒜, P, k) = " +
			"    de_rham_class⟨n⟩(T, " +
			"        𝒜, " +
			"        2 * k, " +
			"        chern_form(n, " +
			"            T, " +
			"            𝒜, " +
			"            P, " +
			"            (λi:num. " +
			"            λj:num. " +
			"            λc:prod(set(A), A → num → real). " +
			"            λy:(num → real). " +
			"            λV:(num → num → real). " +
			"                complex_of_real(&0)), " +
			"            k))",
	},
})}

var ToddCoefficientsDef = toddCoefficientsDefThm{family.Define(registry.DefEntry{
	Name:  "ToddCoefficientsDef",
	Key:   "prop_d9095b214bb251e4",
	Const: "todd_coefficient",
	Type:  "num → real",
	Equations: []string{
		"todd_coefficient = " +
			"εb:(num → real). ∀k:num. " +
			"    real_sum({j:num | j ≤ k}, " +
			"        λj:num. b(j) * real_pow(-&1, k - j) / real_of_num(factorial(suc(k - j)))) = " +
			"    COND(k = 0, &1, &0)",
	},
})}

var toddLogarithmDef = toddLogarithmDefThm{family.Define(registry.DefEntry{
	Name:  "toddLogarithmDef",
	Key:   "prop_c19f1f982f9aa3a5",
	Deps:  []registry.EntryLike{ToddCoefficientsDef},
	Const: "todd_log_coefficient",
	Type:  "num → real",
	Equations: []string{
		"todd_log_coefficient = " +
			"εl:(num → real). l(0) = &0 ∧ formal_exp_zero(real_ring, l) = todd_coefficient",
	},
})}

var ToddFormDef = toddFormDefThm{family.Define(registry.DefEntry{
	Name:  "ToddFormDef",
	Key:   "prop_eef62e533d4613d1",
	Deps:  []registry.EntryLike{ChernFormDef, toddLogarithmDef},
	Const: "todd_form",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex) → " +
		"num → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀Γ:(num → num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → complex). " +
			"    todd_form(n, T, 𝒜, P, Γ) = " +
			"    ετ:(num → prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        τ(0) = manifold_form_unit⟨n⟩(T, 𝒜) ∧ " +
			"        (∀k:num. " +
			"            τ(suc(k)) = " +
			"            (manifold_form_module⟨n⟩(T, 𝒜, 0)).smul(&1 / real_of_num(suc(k)), " +
			"                module_sum((manifold_form_module⟨n⟩(T, 𝒜, 0)).add, " +
			"                    (manifold_form_module⟨n⟩(T, 𝒜, 0)).zero, " +
			"                    {j:num | j ≤ k}, " +
			"                    λj:num. " +
			"                        (manifold_form_module⟨n⟩(T, 𝒜, 0)).smul(real_of_num(suc(j)) * " +
			"                            todd_log_coefficient(suc(j)) * " +
			"                            real_of_num(factorial(suc(j))), " +
			"                            manifold_form_wedge⟨n⟩(T, " +
			"                                𝒜, " +
			"                                2 * suc(j), " +
			"                                2 * (k - j), " +
			"                                chern_form(n, T, 𝒜, P, Γ, suc(j)), " +
			"                                τ(k - j))))))",
	},
})}

var ToddClassDef = toddClassDefThm{family.Define(registry.DefEntry{
	Name:  "ToddClassDef",
	Key:   "prop_d402856cab26f26e",
	Deps:  []registry.EntryLike{ToddFormDef},
	Const: "todd_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"    todd_class(n, T, 𝒜, P, k) = " +
			"    de_rham_class⟨n⟩(T, " +
			"        𝒜, " +
			"        2 * k, " +
			"        todd_form(n, " +
			"            T, " +
			"            𝒜, " +
			"            P, " +
			"            (λi:num. " +
			"            λj:num. " +
			"            λc:prod(set(A), A → num → real). " +
			"            λy:(num → real). " +
			"            λV:(num → num → real). " +
			"                complex_of_real(&0)), " +
			"            k))",
	},
})}
