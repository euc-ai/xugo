package polish_group

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/abelian_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	_ "github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	_ "github.com/euc-ai/xugo/library/proofs/sets/functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolishAbelianGroupDef — The topology has exactly the group carrier, with continuous multiplication and inverse.
var PolishAbelianGroupDef = polishAbelianGroupDefThm{family.Define(registry.DefEntry{
	Name:  "PolishAbelianGroupDef",
	Key:   "prop_e4a67977418b9d2a",
	Const: "polish_abelian_group",
	Type:  "group_ops(A) → set(set(A)) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀T:set(set(A)). " +
			"    polish_abelian_group(G, T) ⇔ " +
			"    abelian_group_on(G) ∧ " +
			"    polish_space(T) ∧ " +
			"    ⋃T = G.carrier ∧ " +
			"    continuous_map(product_topology(T, T), T, λp:prod(A, A). G.mul(fst(p), snd(p))) ∧ " +
			"    continuous_map(T, T, G.inv)",
	},
	Reading: "The topology has exactly the group " +
		"carrier, with continuous multiplication and inverse.",
})}

// PolishableSubgroupDef — The subgroup admits a Polish group topology with the ambient trace Borel sets.
var PolishableSubgroupDef = polishableSubgroupDefThm{family.Define(registry.DefEntry{
	Name:  "PolishableSubgroupDef",
	Key:   "prop_e716915c97a4b993",
	Const: "polishable_subgroup",
	Type:  "group_ops(A) → set(set(A)) → set(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A). " +
			"    polishable_subgroup(G, T, N) ⇔ " +
			"    subgroup(G, N) ∧ " +
			"    (∃U:set(set(A)). " +
			"        polish_abelian_group(restrict_group(G, N), U) ∧ " +
			"        borel_sets(U) = image(λs:set(A). s ∩ N, borel_sets(T)))",
	},
	Deps:    []registry.EntryLike{PolishAbelianGroupDef},
	Reading: "The subgroup admits a Polish group topology with the ambient trace Borel sets.",
})}

// PolishCoverOnDef — The covered quotient has underlying carrier left_cosets(G.mul, G.carrier, N).
var PolishCoverOnDef = polishCoverOnDefThm{family.Define(registry.DefEntry{
	Name:  "PolishCoverOnDef",
	Key:   "prop_9868ffe0c0ca067",
	Const: "polish_cover_on",
	Type:  "group_ops(A) → set(set(A)) → set(A) → bool",
	Equations: []string{
		"∀G:group_ops(A). ∀T:set(set(A)). ∀N:set(A). " +
			"    polish_cover_on(G, T, N) ⇔ polish_abelian_group(G, T) ∧ polishable_subgroup(G, T, N)",
	},
	Deps:    []registry.EntryLike{PolishAbelianGroupDef, PolishableSubgroupDef},
	Reading: "The covered quotient has underlying carrier left_cosets(G.mul, G.carrier, N).",
})}

// BorelCoverMapDef — A quotient homomorphism with a Borel lift; the lift may be additive only modulo the target subgroup.
var BorelCoverMapDef = borelCoverMapDefThm{family.Define(registry.DefEntry{
	Name:  "BorelCoverMapDef",
	Key:   "prop_c32373dff48b6282",
	Const: "borel_cover_map",
	Type: "group_ops(A) → " +
		"set(set(A)) → " +
		"set(A) → " +
		"group_ops(B) → " +
		"set(set(B)) → " +
		"set(B) → " +
		"(set(A) → set(B)) → " +
		"bool",
	Equations: []string{
		"∀G:group_ops(A). " +
			"∀T:set(set(A)). " +
			"∀N:set(A). " +
			"∀H:group_ops(B). " +
			"∀U:set(set(B)). " +
			"∀M:set(B). " +
			"∀h:(set(A) → set(B)). " +
			"    borel_cover_map(G, T, N, H, U, M, h) ⇔ " +
			"    polish_cover_on(G, T, N) ∧ " +
			"    polish_cover_on(H, U, M) ∧ " +
			"    group_homomorphism(quotient_group(G, N), quotient_group(H, M), h) ∧ " +
			"    (∃f:(A → B). " +
			"        borel_map(T, U, f) ∧ " +
			"        (∀x:A. x ∈ G.carrier ⇒ h(left_coset(G.mul, x, N)) = left_coset(H.mul, f(x), M)))",
	},
	Deps: []registry.EntryLike{PolishCoverOnDef},
	Reading: "A quotient homomorphism with a Borel lift; " +
		"the lift may be additive only modulo the target subgroup.",
})}

// BorelCoverIsoDef — Both directions have Borel lifts; their inverse equations are guarded by quotient membership.
var BorelCoverIsoDef = borelCoverIsoDefThm{family.Define(registry.DefEntry{
	Name:  "BorelCoverIsoDef",
	Key:   "prop_950f952acd11755f",
	Const: "borel_cover_iso",
	Type: "group_ops(A) → " +
		"set(set(A)) → " +
		"set(A) → " +
		"group_ops(B) → " +
		"set(set(B)) → " +
		"set(B) → " +
		"(set(A) → set(B)) → " +
		"bool",
	Equations: []string{
		"∀G:group_ops(A). " +
			"∀T:set(set(A)). " +
			"∀N:set(A). " +
			"∀H:group_ops(B). " +
			"∀U:set(set(B)). " +
			"∀M:set(B). " +
			"∀h:(set(A) → set(B)). " +
			"    borel_cover_iso(G, T, N, H, U, M, h) ⇔ " +
			"    borel_cover_map(G, T, N, H, U, M, h) ∧ " +
			"    (∃k:(set(B) → set(A)). " +
			"        borel_cover_map(H, U, M, G, T, N, k) ∧ " +
			"        (∀s:set(A). s ∈ left_cosets(G.mul, G.carrier, N) ⇒ k(h(s)) = s) ∧ " +
			"        (∀s:set(B). s ∈ left_cosets(H.mul, H.carrier, M) ⇒ h(k(s)) = s))",
	},
	Deps: []registry.EntryLike{BorelCoverMapDef},
	Reading: "Both directions have Borel lifts; their " +
		"inverse equations are guarded by quotient membership.",
})}
