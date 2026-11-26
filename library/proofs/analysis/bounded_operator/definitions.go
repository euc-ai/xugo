package bounded_operator

import "github.com/euc-ai/xugo/library/registry"

var BoundedOperatorDef = boundedOperatorDefThm{family.Define(registry.DefEntry{
	Name:  "BoundedOperatorDef",
	Key:   "prop_1ec4a5a8c5437286",
	Const: "bounded_operator",
	Type: "module_ops(complex, A) → " +
		"(A → real) → " +
		"module_ops(complex, B) → " +
		"(B → real) → " +
		"(A → B) → " +
		"bool",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀N:module_ops(complex, B). ∀v:(A → real). ∀w:(B → real). ∀T:(A → B). " +
			"    bounded_operator(M, v, N, w, T) ⇔ " +
			"    module_homomorphism(complex_ring, M, N, T) ∧ " +
			"    ∃C:real. &0 ≤ C ∧ ∀x:A. x ∈ M.carrier ⇒ w(T(x)) ≤ C * v(x)",
	},
})}

var OperatorNormDef = operatorNormDefThm{family.Define(registry.DefEntry{
	Name:  "OperatorNormDef",
	Key:   "prop_ec218ca4817c1979",
	Const: "bounded_op_norm",
	Type:  "module_ops(complex, A) → (A → real) → (B → real) → (A → B) → real",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀v:(A → real). ∀w:(B → real). ∀T:(A → B). " +
			"    bounded_op_norm(M, v, w, T) = " +
			"    real_sup({r:real | ∃x:A. x ∈ M.carrier ∧ v(x) ≤ &1 ∧ r = w(T(x))})",
	},
})}

var OperatorModuleDef = operatorModuleDefThm{family.Define(registry.DefEntry{
	Name:  "OperatorModuleDef",
	Key:   "prop_1a535d9940733720",
	Const: "operator_module",
	Type: "module_ops(complex, A) → " +
		"(A → real) → " +
		"module_ops(complex, B) → " +
		"(B → real) → " +
		"module_ops(complex, A → B)",
	Deps: []registry.EntryLike{BoundedOperatorDef},
	Equations: []string{
		"∀M:module_ops(complex, A). ∀N:module_ops(complex, B). ∀v:(A → real). ∀w:(B → real). " +
			"    operator_module(M, v, N, w) = " +
			"    mk_module(λS:(A → B). λT:(A → B). λx:A. N.add(S(x), T(x)), " +
			"        λx:A. N.zero, " +
			"        λT:(A → B). λx:A. N.neg(T(x)), " +
			"        λc:complex. λT:(A → B). λx:A. N.smul(c, T(x)), " +
			"        {T:(A → B) | bounded_operator(M, v, N, w, T) ∧ ∀x:A. x ∉ M.carrier ⇒ T(x) = N.zero})",
	},
})}

var FiniteRankDef = finiteRankDefThm{family.Define(registry.DefEntry{
	Name:  "FiniteRankDef",
	Key:   "prop_9fbfeaf18ef7007a",
	Const: "finite_rank_operator",
	Type:  "module_ops(complex, A) → module_ops(complex, B) → (A → B) → bool",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀N:module_ops(complex, B). ∀T:(A → B). " +
			"    finite_rank_operator(M, N, T) ⇔ " +
			"    module_homomorphism(complex_ring, M, N, T) ∧ " +
			"    finite_dimensional(complex_ring, restrict_module(N, image(T, M.carrier)))",
	},
})}

var CompactOperatorDef = compactOperatorDefThm{family.Define(registry.DefEntry{
	Name:  "CompactOperatorDef",
	Key:   "prop_122bd8b9f05a8881",
	Const: "compact_operator",
	Type: "module_ops(complex, A) → " +
		"(A → real) → " +
		"module_ops(complex, B) → " +
		"(B → real) → " +
		"(A → B) → " +
		"bool",
	Deps: []registry.EntryLike{BoundedOperatorDef},
	Equations: []string{
		"∀M:module_ops(complex, A). ∀N:module_ops(complex, B). ∀v:(A → real). ∀w:(B → real). ∀T:(A → B). " +
			"    compact_operator(M, v, N, w, T) ⇔ " +
			"    bounded_operator(M, v, N, w, T) ∧ " +
			"    compact_in(norm_topology(N, w), " +
			"        closure(norm_topology(N, w), image(T, {x:A | x ∈ M.carrier ∧ v(x) ≤ &1})))",
	},
})}

var AdjointDef = adjointDefThm{family.Define(registry.DefEntry{
	Name:  "AdjointDef",
	Key:   "prop_ede44ac2a211ecaf",
	Const: "hilbert_adjoint",
	Type: "module_ops(complex, A) → " +
		"(A → A → complex) → " +
		"module_ops(complex, B) → " +
		"(B → B → complex) → " +
		"(A → B) → " +
		"B → " +
		"A",
	Equations: []string{
		"∀M:module_ops(complex, A). " +
			"∀p:(A → A → complex). " +
			"∀N:module_ops(complex, B). " +
			"∀q:(B → B → complex). " +
			"∀T:(A → B). " +
			"∀y:B. " +
			"    hilbert_adjoint(M, p, N, q, T, y) = " +
			"    COND(y ∈ N.carrier, εx:A. x ∈ M.carrier ∧ ∀z:A. z ∈ M.carrier ⇒ q(T(z), y) = p(z, x), M.zero)",
	},
})}
