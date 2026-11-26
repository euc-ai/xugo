package k_thom

import (
	"github.com/euc-ai/xugo/library/registry"
)

var exteriorDef = exteriorDefThm{family.Define(registry.DefEntry{
	Name:  "exteriorDef",
	Key:   "prop_b06ca066635ad256",
	Const: "projection_exterior",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"prod(num, A → num → num → complex)",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). ∀e:num. " +
			"    projection_exterior(T, P, e) = " +
			"    (nat_pow(2, fst(P)), " +
			"        λx:A. λa:num. λb:num. " +
			"            COND(x ∈ ⋃T ∧ nat_mod(card(exterior_mask(fst(P), a)), 2) = e, " +
			"                exterior_power(complex_ring, fst(P), snd(P)(x), a, b), " +
			"                complex_of_real(&0)))",
	},
})}

var koszulMapDef = koszulMapDefThm{family.Define(registry.DefEntry{
	Name:  "koszulMapDef",
	Key:   "prop_906daf537cd75d6",
	Deps:  []registry.EntryLike{exteriorDef},
	Const: "koszul_projection_map",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(A, num → complex) → " +
		"num → " +
		"num → " +
		"complex",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). ∀p:prod(A, num → complex). ∀a b:num. " +
			"    koszul_projection_map(T, P, p, a, b) = " +
			"    COND(p ∈ projection_total_space(T, P), " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < nat_pow(2, fst(P))}, " +
			"            λk:num. " +
			"                koszul_ambient_matrix(fst(P), snd(p), a, k) * " +
			"                snd(projection_exterior(T, P, 0))(fst(p), k, b)), " +
			"        complex_of_real(&0))",
	},
})}

var koszulTripleDef = koszulTripleDefThm{family.Define(registry.DefEntry{
	Name:  "koszulTripleDef",
	Key:   "prop_a316c6f289db8ed4",
	Deps:  []registry.EntryLike{exteriorDef, koszulMapDef},
	Const: "koszul_triple",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(prod(num, prod(A, num → complex) → num → num → complex), " +
		"    prod(prod(num, prod(A, num → complex) → num → num → complex), " +
		"        prod(A, num → complex) → num → num → complex))",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). " +
			"    koszul_triple(T, P) = " +
			"    (projection_pullback(projection_total_topology(T, P), " +
			"            λp:prod(A, num → complex). fst(p), " +
			"            projection_exterior(T, P, 0)), " +
			"        (projection_pullback(projection_total_topology(T, P), " +
			"                λp:prod(A, num → complex). fst(p), " +
			"                projection_exterior(T, P, 1)), " +
			"            koszul_projection_map(T, P)))",
	},
})}

var CompactThomMapDef = compactThomMapDefThm{family.Define(registry.DefEntry{
	Name:  "CompactThomMapDef",
	Key:   "prop_35bca92e1a399562",
	Deps:  []registry.EntryLike{koszulTripleDef},
	Const: "k_thom_map",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))) → " +
		"set(prod(prod(num, prod(A, num → complex) → num → num → complex), " +
		"        prod(prod(num, prod(A, num → complex) → num → num → complex), " +
		"            prod(A, num → complex) → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀a:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"    k_thom_map(T, P, a) = " +
			"    induced_map(λv:prod(prod(num, A → num → num → complex), " +
			"                prod(num, A → num → num → complex)). " +
			"            kc_class(projection_total_topology(T, P), " +
			"                kc_triple_product(kc_triple_pullback(projection_total_topology(T, P), " +
			"                        λp:prod(A, num → complex). fst(p), " +
			"                        (fst(v), (snd(v), λx:A. λi:num. λj:num. complex_of_real(&0)))), " +
			"                    koszul_triple(T, P))), " +
			"        a)",
	},
})}

var ThomMapDef = thomMapDefThm{family.Define(registry.DefEntry{
	Name:  "ThomMapDef",
	Key:   "prop_760b7ca06b059bbd",
	Deps:  []registry.EntryLike{koszulTripleDef},
	Const: "kc_thom_map",
	Type: "set(set(A)) → " +
		"prod(num, A → num → num → complex) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"set(prod(prod(num, prod(A, num → complex) → num → num → complex), " +
		"        prod(prod(num, prod(A, num → complex) → num → num → complex), " +
		"            prod(A, num → complex) → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"    kc_thom_map(T, P, a) = " +
			"    induced_map(λb:prod(prod(num, A → num → num → complex), " +
			"                prod(prod(num, A → num → num → complex), A → num → num → complex)). " +
			"            kc_class(projection_total_topology(T, P), " +
			"                kc_triple_product(kc_triple_pullback(projection_total_topology(T, P), " +
			"                        λp:prod(A, num → complex). fst(p), " +
			"                        b), " +
			"                    koszul_triple(T, P))), " +
			"        a)",
	},
})}

var IsomorphismPredicateDef = isomorphismPredicateDefThm{family.Define(registry.DefEntry{
	Name:  "IsomorphismPredicateDef",
	Key:   "prop_e529ab1271ac0d3c",
	Deps:  []registry.EntryLike{ThomMapDef},
	Const: "kc_thom_isomorphism",
	Type:  "set(set(A)) → prod(num, A → num → num → complex) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀P:prod(num, A → num → num → complex). " +
			"    kc_thom_isomorphism(T, P) ⇔ " +
			"    group_isomorphism(kc_group(T), kc_group(projection_total_topology(T, P)), kc_thom_map(T, P))",
	},
})}
