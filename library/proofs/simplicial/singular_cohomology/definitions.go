package singular_cohomology

import (
	"github.com/euc-ai/xugo/library/registry"
)

var ComplexOfDef = complexOfDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexOfDef",
	Key:   "prop_cd5027febe8ac1f7",
	Const: "singular_cochain_complex_of",
	Type:  "simplicial_ops((num → real) → A) → complex_ops(real, ((num → real) → A) → real)",
	Reading: "A cochain is a function on the basis of a free chain " +
		"module, extended by zero off that basis. The differential reads " +
		"the faces of a (k + 1) - simplex; no predecessor at zero occurs.",
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). " +
			"    singular_cochain_complex_of(K) = " +
			"    pack_complex((λc:(((num → real) → A) → real). " +
			"        λe:(((num → real) → A) → real). " +
			"        λσ:((num → real) → A). " +
			"            c(σ) + e(σ)), " +
			"        (λσ:((num → real) → A). &0), " +
			"        (λc:(((num → real) → A) → real). λσ:((num → real) → A). -c(σ)), " +
			"        (λr:real. λc:(((num → real) → A) → real). λσ:((num → real) → A). r * c(σ)), " +
			"        (λk:num. " +
			"            {c:(((num → real) → A) → real) | " +
			"                ∀σ:((num → real) → A). σ ∉ K.simplices(k) ⇒ c(σ) = &0}), " +
			"        (λk:num. λc:(((num → real) → A) → real). λσ:((num → real) → A). " +
			"            COND(σ ∈ K.simplices(k + 1), " +
			"                real_sum({i:num | i ≤ k + 1}, λi:num. (-&1)^i * c(K.d(k + 1, i, σ))), " +
			"                &0)))",
	},
})}

var ComplexDef = complexDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexDef",
	Key:   "prop_1942b3df6fa444e2",
	Const: "singular_cochain_complex",
	Type:  "set(set(A)) → complex_ops(real, ((num → real) → A) → real)",
	Deps:  []registry.EntryLike{ComplexOfDef},
	Equations: []string{
		"∀T:set(set(A)). singular_cochain_complex(T) = singular_cochain_complex_of(singular_set(T))",
	},
})}

var PullbackOfDef = pullbackOfDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackOfDef",
	Key:   "prop_cdfa9523bd7a409c",
	Const: "singular_cochain_pullback_of",
	Type: "simplicial_ops((num → real) → A) → " +
		"(A → B) → " +
		"num → " +
		"(((num → real) → B) → real) → " +
		"((num → real) → A) → " +
		"real",
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). " +
			"∀f:(A → B). " +
			"∀k:num. " +
			"∀c:(((num → real) → B) → real). " +
			"∀σ:((num → real) → A). " +
			"    singular_cochain_pullback_of(K, f, k, c, σ) = " +
			"    COND(σ ∈ K.simplices(k), c(singular_map(f, k, σ)), &0)",
	},
})}

var PullbackDef = pullbackDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackDef",
	Key:   "prop_8851257fd726a0d6",
	Const: "singular_cohomology_pullback",
	Type: "set(set(A)) → " +
		"(A → B) → " +
		"num → " +
		"set(((num → real) → B) → real) → " +
		"set(((num → real) → A) → real)",
	Deps: []registry.EntryLike{ComplexDef, PullbackOfDef},
	Equations: []string{
		"∀T:set(set(A)). ∀f:(A → B). " +
			"    singular_cohomology_pullback(T, f) = " +
			"    cohomology_map(singular_cochain_complex(T), singular_cochain_pullback_of(singular_set(T), f))",
	},
})}

var RestrictedSetDef = restrictedSetDefThm{family.Define(registry.DefEntry{
	Name:  "RestrictedSetDef",
	Key:   "prop_b7063083b74c42b3",
	Const: "singular_restricted_set",
	Type:  "simplicial_ops((num → real) → A) → set(A) → simplicial_ops((num → real) → A)",
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). ∀U:set(A). " +
			"    singular_restricted_set(K, U) = " +
			"    mk_simplicial((λk:num. " +
			"            {σ:((num → real) → A) | σ ∈ K.simplices(k) ∧ image(σ, euclidean_simplex(k)) ⊆ U}), " +
			"        K.d, " +
			"        K.s)",
	},
})}

var SmallSetDef = smallSetDefThm{family.Define(registry.DefEntry{
	Name:  "SmallSetDef",
	Key:   "prop_dbcd1e2e795665d7",
	Const: "singular_small_set",
	Type:  "simplicial_ops((num → real) → A) → set(set(A)) → simplicial_ops((num → real) → A)",
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). ∀𝒰:set(set(A)). " +
			"    singular_small_set(K, 𝒰) = " +
			"    mk_simplicial((λk:num. " +
			"            {σ:((num → real) → A) | " +
			"                σ ∈ K.simplices(k) ∧ (∃U:set(A). U ∈ 𝒰 ∧ image(σ, euclidean_simplex(k)) ⊆ U)}), " +
			"        K.d, " +
			"        K.s)",
	},
})}

var RestrictionDef = restrictionDefThm{family.Define(registry.DefEntry{
	Name:  "RestrictionDef",
	Key:   "prop_b21623ea4408bdec",
	Const: "singular_cochain_restriction",
	Type: "simplicial_ops((num → real) → A) → " +
		"num → " +
		"(((num → real) → A) → real) → " +
		"((num → real) → A) → " +
		"real",
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). ∀k:num. ∀c:(((num → real) → A) → real). " +
			"    singular_cochain_restriction(K, k, c) = normalize_on(K.simplices(k), &0, c)",
	},
})}

var CohomologyRestrictionDef = cohomologyRestrictionDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyRestrictionDef",
	Key:   "prop_7841147ff6645712",
	Const: "singular_cohomology_restriction",
	Type: "simplicial_ops((num → real) → A) → " +
		"num → " +
		"set(((num → real) → A) → real) → " +
		"set(((num → real) → A) → real)",
	Deps: []registry.EntryLike{ComplexOfDef, RestrictionDef},
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). " +
			"    singular_cohomology_restriction(K) = " +
			"    cohomology_map(singular_cochain_complex_of(K), singular_cochain_restriction(K))",
	},
})}

var CoverComplexDef = coverComplexDefThm{family.Define(registry.DefEntry{
	Name:  "CoverComplexDef",
	Key:   "prop_da1220ddca32c5f4",
	Const: "singular_cover_complex",
	Type: "simplicial_ops((num → real) → A) → " +
		"set(A) → " +
		"set(A) → " +
		"complex_ops(real, prod(((num → real) → A) → real, ((num → real) → A) → real))",
	Deps: []registry.EntryLike{ComplexOfDef, RestrictedSetDef},
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). ∀U V:set(A). " +
			"    singular_cover_complex(K, U, V) = " +
			"    pack_complex((λz:prod(((num → real) → A) → real, ((num → real) → A) → real). " +
			"        λw:prod(((num → real) → A) → real, ((num → real) → A) → real). " +
			"            (singular_cochain_complex_of(singular_restricted_set(K, U)).add(fst(z), fst(w)), " +
			"                singular_cochain_complex_of(singular_restricted_set(K, V)).add(snd(z), " +
			"                    snd(w)))), " +
			"        (singular_cochain_complex_of(singular_restricted_set(K, U)).zero, " +
			"            singular_cochain_complex_of(singular_restricted_set(K, V)).zero), " +
			"        (λz:prod(((num → real) → A) → real, ((num → real) → A) → real). " +
			"            (singular_cochain_complex_of(singular_restricted_set(K, U)).neg(fst(z)), " +
			"                singular_cochain_complex_of(singular_restricted_set(K, V)).neg(snd(z)))), " +
			"        (λr:real. λz:prod(((num → real) → A) → real, ((num → real) → A) → real). " +
			"            (singular_cochain_complex_of(singular_restricted_set(K, U)).smul(r, fst(z)), " +
			"                singular_cochain_complex_of(singular_restricted_set(K, V)).smul(r, snd(z)))), " +
			"        (λk:num. " +
			"            set_cross(singular_cochain_complex_of(singular_restricted_set(K, U)).terms(k), " +
			"                singular_cochain_complex_of(singular_restricted_set(K, V)).terms(k))), " +
			"        (λk:num. λz:prod(((num → real) → A) → real, ((num → real) → A) → real). " +
			"            (singular_cochain_complex_of(singular_restricted_set(K, U)).d(k, fst(z)), " +
			"                singular_cochain_complex_of(singular_restricted_set(K, V)).d(k, snd(z)))))",
	},
})}

var CoverRestrictionDef = coverRestrictionDefThm{family.Define(registry.DefEntry{
	Name:  "CoverRestrictionDef",
	Key:   "prop_f971c3edb4700205",
	Const: "singular_cover_restriction",
	Type: "simplicial_ops((num → real) → A) → " +
		"set(A) → " +
		"set(A) → " +
		"num → " +
		"(((num → real) → A) → real) → " +
		"prod(((num → real) → A) → real, ((num → real) → A) → real)",
	Deps: []registry.EntryLike{RestrictionDef, RestrictedSetDef},
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). ∀U V:set(A). ∀k:num. ∀c:(((num → real) → A) → real). " +
			"    singular_cover_restriction(K, U, V)(k, c) = " +
			"    (singular_cochain_restriction(singular_restricted_set(K, U), k, c), " +
			"        singular_cochain_restriction(singular_restricted_set(K, V), k, c))",
	},
})}

var CoverDifferenceDef = coverDifferenceDefThm{family.Define(registry.DefEntry{
	Name:  "CoverDifferenceDef",
	Key:   "prop_7c4cf0179f4f6c0b",
	Const: "singular_cover_difference",
	Type: "simplicial_ops((num → real) → A) → " +
		"set(A) → " +
		"set(A) → " +
		"num → " +
		"prod(((num → real) → A) → real, ((num → real) → A) → real) → " +
		"((num → real) → A) → " +
		"real",
	Deps: []registry.EntryLike{RestrictionDef, RestrictedSetDef},
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). " +
			"∀U V:set(A). " +
			"∀k:num. " +
			"∀z:prod(((num → real) → A) → real, ((num → real) → A) → real). " +
			"    singular_cover_difference(K, U, V)(k, z) = " +
			"    singular_cochain_restriction(singular_restricted_set(K, U ∩ V), " +
			"        k, " +
			"        (λσ:((num → real) → A). fst(z)(σ) - snd(z)(σ)))",
	},
})}

var ConnectingDef = connectingDefThm{family.Define(registry.DefEntry{
	Name:  "ConnectingDef",
	Key:   "prop_bfd090c6c95c7c4b",
	Const: "singular_cohomology_connecting",
	Type: "simplicial_ops((num → real) → A) → " +
		"set(A) → " +
		"set(A) → " +
		"num → " +
		"set(((num → real) → A) → real) → " +
		"set(((num → real) → A) → real)",
	Deps: []registry.EntryLike{
		SmallSetDef,
		CohomologyRestrictionDef,
		CoverComplexDef,
		CoverRestrictionDef,
		CoverDifferenceDef,
	},
	Reading: "The sign convention is restriction to U minus restriction to " +
		"V. Lift, differentiate and glue first gives a small-cochain class; invert " +
		"the small restriction only when its cohomology map is an isomorphism.",
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). ∀U V:set(A). ∀k:num. ∀s:set(((num → real) → A) → real). " +
			"    singular_cohomology_connecting(K, U, V, k)(s) = " +
			"    inverse_on(cohomology_module(singular_cochain_complex_of(K), k + 1).carrier, " +
			"        singular_cohomology_restriction(singular_small_set(K, {U, V}), k + 1), " +
			"        coconnecting_hom(singular_cochain_complex_of(singular_small_set(K, {U, V})), " +
			"            singular_cover_complex(K, U, V), " +
			"            singular_cover_restriction(K, U, V), " +
			"            singular_cover_difference(K, U, V), " +
			"            k, " +
			"            s))",
	},
})}

var EvaluationDef = evaluationDefThm{family.Define(registry.DefEntry{
	Name:  "EvaluationDef",
	Key:   "prop_faa62edf6bd5dfc8",
	Const: "singular_cohomology_evaluation",
	Type: "simplicial_ops((num → real) → A) → " +
		"num → " +
		"set(((num → real) → A) → real) → " +
		"set(((num → real) → A) → real) → " +
		"real",
	Deps: []registry.EntryLike{ComplexOfDef},
	Reading: "Cycles have finite support. The two choices are respectively a " +
		"cocycle and a cycle; evaluation descends because cocycles kill boundaries " +
		"and coboundaries kill cycles. Off either quotient carrier the value is zero.",
	Equations: []string{
		"∀K:simplicial_ops((num → real) → A). " +
			"∀k:num. " +
			"∀s:set(((num → real) → A) → real). " +
			"∀t:set(((num → real) → A) → real). " +
			"    singular_cohomology_evaluation(K, k, s, t) = " +
			"    COND(s ∈ cohomology_module(singular_cochain_complex_of(K), k).carrier ∧ " +
			"        t ∈ " +
			"        homology_module(free_complex(real_ring, " +
			"                K.simplices, " +
			"                simplicial_boundary(real_ring.add, " +
			"                    real_ring.zero, " +
			"                    real_ring.one, " +
			"                    real_ring.neg, " +
			"                    real_ring.mul, " +
			"                    K.d)), " +
			"            k).carrier, " +
			"        real_sum({σ:((num → real) → A) | " +
			"                (εz:(((num → real) → A) → real). " +
			"                    z ∈ t ∧ " +
			"                    z ∈ " +
			"                    cycles(free_complex(real_ring, " +
			"                            K.simplices, " +
			"                            simplicial_boundary(real_ring.add, " +
			"                                real_ring.zero, " +
			"                                real_ring.one, " +
			"                                real_ring.neg, " +
			"                                real_ring.mul, " +
			"                                K.d)), " +
			"                        k))(σ) ≠ " +
			"                &0}, " +
			"            λσ:((num → real) → A). " +
			"                (εz:(((num → real) → A) → real). " +
			"                    z ∈ t ∧ " +
			"                    z ∈ " +
			"                    cycles(free_complex(real_ring, " +
			"                            K.simplices, " +
			"                            simplicial_boundary(real_ring.add, " +
			"                                real_ring.zero, " +
			"                                real_ring.one, " +
			"                                real_ring.neg, " +
			"                                real_ring.mul, " +
			"                                K.d)), " +
			"                        k))(σ) * " +
			"                (εc:(((num → real) → A) → real). " +
			"                    c ∈ s ∧ c ∈ cocycles(singular_cochain_complex_of(K), k))(σ)), " +
			"        &0)",
	},
})}

var BettiDef = bettiDefThm{family.Define(registry.DefEntry{
	Name:  "BettiDef",
	Key:   "prop_2e1d7299e473153a",
	Const: "singular_betti",
	Type:  "set(set(A)) → num → num",
	Equations: []string{
		"∀T:set(set(A)). ∀k:num. " +
			"    singular_betti(T, k) = " +
			"    module_dim(real_ring, homology_module(singular_complex(real_ring, T), k))",
	},
})}

var EulerDef = eulerDefThm{family.Define(registry.DefEntry{
	Name:  "EulerDef",
	Key:   "prop_5a17e41550f2d7cf",
	Const: "singular_euler",
	Type:  "set(set(A)) → num → real",
	Deps:  []registry.EntryLike{BettiDef},
	Reading: "The dimension bound is explicit. This is the topological " +
		"Euler characteristic when homology is finite dimensional and vanishes " +
		"above n; comparison supplies those hypotheses for compact n-manifolds.",
	Equations: []string{
		"∀T:set(set(A)). ∀n:num. " +
			"    singular_euler(T, n) = real_sum({k:num | k ≤ n}, λk:num. (-&1)^k * &singular_betti(T, k))",
	},
})}
