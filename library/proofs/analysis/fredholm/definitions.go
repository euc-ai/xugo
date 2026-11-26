package fredholm

import "github.com/euc-ai/xugo/library/registry"

var KernelDef = kernelDefThm{family.Define(registry.DefEntry{
	Name:  "KernelDef",
	Key:   "prop_9a4188a445182b0",
	Const: "hilbert_kernel",
	Type:  "module_ops(complex, A) → module_ops(complex, B) → (A → B) → set(A)",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀N:module_ops(complex, B). ∀T:(A → B). " +
			"    hilbert_kernel(M, N, T) = {x:A | x ∈ M.carrier ∧ T(x) = N.zero}",
	},
})}

var CokernelDef = cokernelDefThm{family.Define(registry.DefEntry{
	Name:  "CokernelDef",
	Key:   "prop_c711cf93924370f5",
	Const: "hilbert_cokernel",
	Type:  "module_ops(complex, A) → module_ops(complex, B) → (B → B → complex) → (A → B) → set(B)",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀N:module_ops(complex, B). ∀q:(B → B → complex). ∀T:(A → B). " +
			"    hilbert_cokernel(M, N, q, T) = hilbert_complement(N, q, image(T, M.carrier))",
	},
})}

var FredholmDef = fredholmDefThm{family.Define(registry.DefEntry{
	Name:  "FredholmDef",
	Key:   "prop_42796d8f6a2a16f5",
	Const: "fredholm_operator",
	Type: "module_ops(complex, A) → " +
		"(A → A → complex) → " +
		"module_ops(complex, B) → " +
		"(B → B → complex) → " +
		"(A → B) → " +
		"bool",
	Deps: []registry.EntryLike{KernelDef, CokernelDef},
	Equations: []string{
		"∀M:module_ops(complex, A). " +
			"∀p:(A → A → complex). " +
			"∀N:module_ops(complex, B). " +
			"∀q:(B → B → complex). " +
			"∀T:(A → B). " +
			"    fredholm_operator(M, p, N, q, T) ⇔ " +
			"    complex_hilbert_space(M, p) ∧ " +
			"    complex_hilbert_space(N, q) ∧ " +
			"    bounded_operator(M, hilbert_norm(p), N, hilbert_norm(q), T) ∧ " +
			"    closed_in(norm_topology(N, hilbert_norm(q)), image(T, M.carrier)) ∧ " +
			"    finite_dimensional(complex_ring, restrict_module(M, hilbert_kernel(M, N, T))) ∧ " +
			"    finite_dimensional(complex_ring, restrict_module(N, hilbert_cokernel(M, N, q, T)))",
	},
})}

var IndexDef = indexDefThm{family.Define(registry.DefEntry{
	Name:  "IndexDef",
	Key:   "prop_1e12738067e51a3b",
	Const: "fredholm_index",
	Type:  "module_ops(complex, A) → module_ops(complex, B) → (B → B → complex) → (A → B) → int",
	Deps:  []registry.EntryLike{KernelDef, CokernelDef},
	Equations: []string{
		"∀M:module_ops(complex, A). ∀N:module_ops(complex, B). ∀q:(B → B → complex). ∀T:(A → B). " +
			"    fredholm_index(M, N, q, T) = " +
			"    int_of_num(module_dim(complex_ring, restrict_module(M, hilbert_kernel(M, N, T)))) - " +
			"    int_of_num(module_dim(complex_ring, restrict_module(N, hilbert_cokernel(M, N, q, T))))",
	},
})}

var ParametrixDef = parametrixDefThm{family.Define(registry.DefEntry{
	Name:  "ParametrixDef",
	Key:   "prop_a5383760f2b5d5a5",
	Const: "fredholm_parametrix",
	Type: "module_ops(complex, A) → " +
		"(A → A → complex) → " +
		"module_ops(complex, B) → " +
		"(B → B → complex) → " +
		"(A → B) → " +
		"(B → A) → " +
		"bool",
	Equations: []string{
		"∀M:module_ops(complex, A). " +
			"∀p:(A → A → complex). " +
			"∀N:module_ops(complex, B). " +
			"∀q:(B → B → complex). " +
			"∀T:(A → B). " +
			"∀S:(B → A). " +
			"    fredholm_parametrix(M, p, N, q, T, S) ⇔ " +
			"    bounded_operator(N, hilbert_norm(q), M, hilbert_norm(p), S) ∧ " +
			"    compact_operator(M, hilbert_norm(p), M, hilbert_norm(p), λx:A. M.add(S(T(x)), M.neg(x))) ∧ " +
			"    compact_operator(N, hilbert_norm(q), N, hilbert_norm(q), λy:B. N.add(T(S(y)), N.neg(y)))",
	},
})}
