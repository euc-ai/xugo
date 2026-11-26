package analytic_index

import (
	"github.com/euc-ai/xugo/library/registry"
)

var extensionDef = extensionDefThm{family.Define(registry.DefEntry{
	Name:  "extensionDef",
	Key:   "prop_7bf36e925b754892",
	Const: "ps_symbol_extension",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex) → " +
		"(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex) → " +
		"bool",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀σ τ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"    ps_symbol_extension(n, r, q, T, 𝒜, P, Q, σ, τ) ⇔ " +
			"    continuous_projection_map(cotangent_topology(n, T, 𝒜), " +
			"        projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"            λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"            (r, P)), " +
			"        projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"            λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"            (q, Q)), " +
			"        τ) ∧ " +
			"    ∃K:set(prod(A, prod(set(A), A → num → real) → num → real)). " +
			"        compact_in(cotangent_topology(n, T, 𝒜), K) ∧ " +
			"        (∀p:prod(A, prod(set(A), A → num → real) → num → real). ∀i j:num. " +
			"            p ∈ cotangent_bundle(n, T, 𝒜) ∧ p ∉ K ⇒ τ(p, i, j) = σ(p, i, j))",
	},
})}

var tripleDef = tripleDefThm{family.Define(registry.DefEntry{
	Name:  "tripleDef",
	Key:   "prop_74a0a332a491c8e8",
	Deps:  []registry.EntryLike{extensionDef},
	Const: "ps_symbol_triple",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex) → " +
		"prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"    prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"        prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"    ps_symbol_triple(n, r, q, T, 𝒜, P, Q, σ) = " +
			"    (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"            λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"            (r, P)), " +
			"        (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                (q, Q)), " +
			"            ετ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"                ps_symbol_extension(n, r, q, T, 𝒜, P, Q, σ, τ)))",
	},
})}

var classDef = classDefThm{family.Define(registry.DefEntry{
	Name:  "classDef",
	Key:   "prop_f71aa4eee2c016ee",
	Deps:  []registry.EntryLike{tripleDef},
	Const: "ps_symbol_class",
	Type: "num → " +
		"num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(A → num → num → complex) → " +
		"(A → num → num → complex) → " +
		"(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex) → " +
		"set(prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"        prod(prod(num, " +
		"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"            prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex)))",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"    ps_symbol_class(n, r, q, T, 𝒜, P, Q, σ) = " +
			"    kc_class(cotangent_topology(n, T, 𝒜), ps_symbol_triple(n, r, q, T, 𝒜, P, Q, σ))",
	},
})}

var OperatorIndexDef = operatorIndexDefThm{family.Define(registry.DefEntry{
	Name:  "OperatorIndexDef",
	Key:   "prop_e7123e53e64663e7",
	Const: "ps_operator_index",
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
		"int",
	Equations: []string{
		"∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀m s:int. " +
			"∀D:((A → num → complex) → A → num → complex). " +
			"    ps_operator_index(n, r, q, T, 𝒜, P, Q, L, m, s, D) = " +
			"    fredholm_index(section_sobolev_module(n, r, T, 𝒜, P, L, s), " +
			"        section_sobolev_module(n, q, T, 𝒜, Q, L, s - m), " +
			"        localization_sequence_inner(n, q, L.count, s - m), " +
			"        ps_realization(n, r, q, T, 𝒜, P, Q, L, m, s, D))",
	},
})}

var AnalyticIndexDef = analyticIndexDefThm{family.Define(registry.DefEntry{
	Name: "AnalyticIndexDef",
	Key:  "prop_4cc917cd20122ef1",
	Reading: "The choice ranges over concrete zero-order elliptic realizations. " +
		"Its value is justified by SymbolClassRealization and IndexClassIndependent.",
	Deps:  []registry.EntryLike{classDef, OperatorIndexDef},
	Const: "analytic_index",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(prod(num, prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"        prod(prod(num, " +
		"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
		"            prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))) → " +
		"int",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))). " +
			"    analytic_index(n, T, 𝒜, a) = " +
			"    εz:int. " +
			"    ∃r q:num. " +
			"    ∃P Q:(A → num → num → complex). " +
			"    ∃L:sobolev_localization(A). " +
			"    ∃σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"    ∃D:((A → num → complex) → A → num → complex). " +
			"        sobolev_localization_on(n, T, 𝒜, L) ∧ " +
			"        pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, int_of_num(0), σ, D) ∧ " +
			"        ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, int_of_num(0), σ) ∧ " +
			"        ps_symbol_class(n, r, q, T, 𝒜, P, Q, σ) = a ∧ " +
			"        ps_operator_index(n, r, q, T, 𝒜, P, Q, L, int_of_num(0), int_of_num(0), D) = z",
	},
})}
