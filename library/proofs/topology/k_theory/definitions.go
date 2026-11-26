package k_theory

import (
	"github.com/euc-ai/xugo/library/registry"
)

var virtualDef = virtualDefThm{family.Define(registry.DefEntry{
	Name:  "virtualDef",
	Key:   "prop_e940e3ed6fcf67e6",
	Const: "k_virtual_bundle",
	Type: "set(set(A)) → " +
		"prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀v:prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)). " +
			"    k_virtual_bundle(T, v) ⇔ " +
			"    continuous_projection_bundle(T, fst(v)) ∧ continuous_projection_bundle(T, snd(v))",
	},
})}

var StableDef = stableDefThm{family.Define(registry.DefEntry{
	Name:  "StableDef",
	Key:   "prop_1b2bcc6664b7cdfb",
	Deps:  []registry.EntryLike{virtualDef},
	Const: "k_stable_equivalent",
	Type: "set(set(A)) → " +
		"prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)) → " +
		"bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀u v:prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)). " +
			"    k_stable_equivalent(T, u, v) ⇔ " +
			"    k_virtual_bundle(T, u) ∧ " +
			"    k_virtual_bundle(T, v) ∧ " +
			"    ∃R:prod(num, A → num → num → complex). " +
			"        continuous_projection_bundle(T, R) ∧ " +
			"        projection_isomorphic(T, " +
			"            projection_sum(projection_sum(fst(u), snd(v)), R), " +
			"            projection_sum(projection_sum(fst(v), snd(u)), R))",
	},
})}

var ClassDef = classDefThm{family.Define(registry.DefEntry{
	Name:  "ClassDef",
	Key:   "prop_4e66447b78e5c100",
	Deps:  []registry.EntryLike{StableDef},
	Const: "k_class",
	Type: "set(set(A)) → " +
		"prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀v:prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)). " +
			"    k_class(T, v) = " +
			"    {u:prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)) | " +
			"        k_stable_equivalent(T, v, u)}",
	},
})}

var addRepresentativeDef = addRepresentativeDefThm{family.Define(registry.DefEntry{
	Name:  "addRepresentativeDef",
	Key:   "prop_852e85ec18c69700",
	Const: "k_virtual_add",
	Type: "prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))",
	Equations: []string{
		"∀u v:prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)). " +
			"    k_virtual_add(u, v) = (projection_sum(fst(u), fst(v)), projection_sum(snd(u), snd(v)))",
	},
})}

var multiplyRepresentativeDef = multiplyRepresentativeDefThm{family.Define(registry.DefEntry{
	Name:  "multiplyRepresentativeDef",
	Key:   "prop_aa733c43656f4071",
	Const: "k_virtual_multiply",
	Type: "prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)) → " +
		"prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))",
	Equations: []string{
		"∀u v:prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)). " +
			"    k_virtual_multiply(u, v) = " +
			"    (projection_sum(projection_tensor(fst(u), fst(v)), projection_tensor(snd(u), snd(v))), " +
			"        projection_sum(projection_tensor(fst(u), snd(v)), projection_tensor(snd(u), fst(v))))",
	},
})}

var AddDef = addDefThm{family.Define(registry.DefEntry{
	Name:  "AddDef",
	Key:   "prop_9e67ef3fba645e82",
	Deps:  []registry.EntryLike{ClassDef, addRepresentativeDef},
	Const: "k_add",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀C D:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"    k_add(T, C, D) = " +
			"    induced_map(λu:prod(prod(num, A → num → num → complex), " +
			"                prod(num, A → num → num → complex)). " +
			"            induced_map(λv:prod(prod(num, A → num → num → complex), " +
			"                        prod(num, A → num → num → complex)). " +
			"                    k_class(T, k_virtual_add(u, v)), " +
			"                D), " +
			"        C)",
	},
})}

var NegateDef = negateDefThm{family.Define(registry.DefEntry{
	Name:  "NegateDef",
	Key:   "prop_61bcffa8d194430b",
	Deps:  []registry.EntryLike{ClassDef},
	Const: "k_negate",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀C:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"    k_negate(T, C) = " +
			"    induced_map(λu:prod(prod(num, A → num → num → complex), " +
			"                prod(num, A → num → num → complex)). " +
			"            k_class(T, (snd(u), fst(u))), " +
			"        C)",
	},
})}

var MultiplyDef = multiplyDefThm{family.Define(registry.DefEntry{
	Name:  "MultiplyDef",
	Key:   "prop_14fe1a8f8593ff55",
	Deps:  []registry.EntryLike{ClassDef, multiplyRepresentativeDef},
	Const: "k_multiply",
	Type: "set(set(A)) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀C D:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"    k_multiply(T, C, D) = " +
			"    induced_map(λu:prod(prod(num, A → num → num → complex), " +
			"                prod(num, A → num → num → complex)). " +
			"            induced_map(λv:prod(prod(num, A → num → num → complex), " +
			"                        prod(num, A → num → num → complex)). " +
			"                    k_class(T, k_virtual_multiply(u, v)), " +
			"                D), " +
			"        C)",
	},
})}

var RingDef = ringDefThm{family.Define(registry.DefEntry{
	Name:  "RingDef",
	Key:   "prop_21dba08a1f295cd4",
	Deps:  []registry.EntryLike{virtualDef, StableDef, ClassDef, AddDef, NegateDef, MultiplyDef},
	Const: "k_ring",
	Type: "set(set(A)) → " +
		"ring_ops(set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    k_ring(T) = " +
			"    mk_ring(k_add(T), " +
			"        k_class(T, (projection_trivial(T, 0), projection_trivial(T, 0))), " +
			"        k_negate(T), " +
			"        k_multiply(T), " +
			"        k_class(T, (projection_trivial(T, 1), projection_trivial(T, 0))), " +
			"        λC:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"        λD:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). " +
			"            k_add(T, C, k_negate(T, D)), " +
			"        quotient_on({v:prod(prod(num, A → num → num → complex), " +
			"                    prod(num, A → num → num → complex)) | " +
			"                k_virtual_bundle(T, v)}, " +
			"            k_stable_equivalent(T)))",
	},
})}

var PullbackDef = pullbackDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackDef",
	Key:   "prop_90c036b9b9900b90",
	Deps:  []registry.EntryLike{ClassDef},
	Const: "k_pullback",
	Type: "set(set(A)) → " +
		"(A → B) → " +
		"set(prod(prod(num, B → num → num → complex), prod(num, B → num → num → complex))) → " +
		"set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex)))",
	Equations: []string{
		"∀T:set(set(A)). " +
			"∀f:(A → B). " +
			"∀C:set(prod(prod(num, B → num → num → complex), prod(num, B → num → num → complex))). " +
			"    k_pullback(T, f, C) = " +
			"    induced_map(λv:prod(prod(num, B → num → num → complex), " +
			"                prod(num, B → num → num → complex)). " +
			"            k_class(T, (projection_pullback(T, f, fst(v)), projection_pullback(T, f, snd(v)))), " +
			"        C)",
	},
})}

var RankDef = rankDefThm{family.Define(registry.DefEntry{
	Name:  "RankDef",
	Key:   "prop_9a6334ebcf7bd7af",
	Const: "k_rank",
	Type: "set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))) → " +
		"A → " +
		"int",
	Equations: []string{
		"∀C:set(prod(prod(num, A → num → num → complex), prod(num, A → num → num → complex))). ∀x:A. " +
			"    k_rank(C, x) = " +
			"    induced_map(λv:prod(prod(num, A → num → num → complex), " +
			"                prod(num, A → num → num → complex)). " +
			"            int_of_num(projection_rank(fst(v), x)) - int_of_num(projection_rank(snd(v), x)), " +
			"        C)",
	},
})}
